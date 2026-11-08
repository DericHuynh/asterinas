// SPDX-License-Identifier: MPL-2.0

//! Locates the actual internal journal in an EA-enabled immutable source.
//! Validation uses the raw EA header and journal inode. Partially checkpointed allocation bitmaps are deliberately not
//! consumed here. This bounded locator conveys no write or mount authority.
//! See Linux ext4_get_journal_inode and __ext4_get_inode_loc at sources.json.

use alloc::vec::Vec;

use vstd::prelude::*;
pub use crate::bootstrap::*;
pub use crate::bootstrap_frame::*;
use crate::{block_claims, bootstrap_identity::{self, *}, bytes, crc, ea_source, group, layout::{self, JournalLayout, LayoutView}, recovery_io::{self, Recovery},
    scan_trace::Source, snapshot::Snapshot, super_state, superblock};

verus! {

pub open spec fn admissible(source: Seq<u8>) -> bool { valid(projection(source)) }

/// Raw recovery preparation for this exact source and journal layout. This
/// condition contains no full repaired-filesystem validation premise.
pub open spec fn source_can_prepare(v: BootstrapView, layout: &JournalLayout) -> bool {
    &&& valid(v) && layout.wf() && layout.view() == v.layout
    &&& recovery_io::can_prepare_ea(journal_bytes(v), journal_identity(v), layout,
        v.source.subrange(0, 4096), v.source.len() as u64)
}

#[verifier::opaque]
pub open spec fn valid(v: BootstrapView) -> bool {
    &&& 8192 <= v.source.len() <= 18446744073709551615
    &&& ea_source::header_accepted(v.source.subrange(1024, 2048), v.source.len() as u64)
    &&& 2 < v.blocks <= block_claims::MAX_BLOCKS && v.blocks as nat * 4096 <= v.source.len()
    &&& v.blocks as nat == bytes::le32(v.source, 1028) && v.inodes as nat == bytes::le32(v.source, 1024)
    &&& v.ipg as nat == bytes::le32(v.source, 1064) && 0 < v.ipg <= 32768 && v.ipg % 16 == 0 && v.inodes >= 11
    &&& v.seed == crc::fold(0xffffffff, journal_identity(v))
    &&& v.metadata_seed == superblock::metadata_seed(v.source.subrange(1024, 2048))
    &&& group::accepted_with_features(v.source.subrange(4096, 4096 + superblock::descriptor_bytes(v.source.subrange(1024, 2048)) as int), 0, v.blocks, v.ipg, v.metadata_seed, superblock::flex_bg(v.source.subrange(1024, 2048)))
    &&& v.table as nat == bytes::le32(v.source, 4104) && 0 < v.table < v.blocks
    &&& layout::admitted(journal_inode(v), v.inodes, v.blocks, v.metadata_seed)
    &&& v.layout.start > 1 && 1024 <= v.layout.journal_blocks <= 32768
    &&& v.layout.start as nat + v.layout.journal_blocks <= v.blocks && v.layout.fs_blocks == v.blocks
    &&& v.layout.start as nat == bytes::le32(journal_inode(v), 60)
    &&& v.layout.journal_blocks as nat == bytes::le32(journal_inode(v), 4) / 4096
}

pub proof fn every_valid_bootstrap_is_the_unique_source_projection(v: BootstrapView)
    requires valid(v),
    ensures v == projection(v.source), admissible(v.source),
{
    hide(crc::fold);
    reveal(valid);
}

pub(crate) proof fn a_valid_bootstrap_uses_its_actual_journal_identity_seed(v: BootstrapView)
    requires valid(v),
    ensures v.seed == crc::fold(0xffffffff, journal_identity(v)),
{ hide(crc::fold); reveal(valid); }

pub proof fn valid_bootstraps_of_identical_bytes_have_identical_fields(before: BootstrapView, after: BootstrapView)
    requires valid(before), valid(after), before.source == after.source,
    ensures before == after,
{
    every_valid_bootstrap_is_the_unique_source_projection(before);
    every_valid_bootstrap_is_the_unique_source_projection(after);
}

proof fn an_admitted_source_supplies_the_locator_inputs(source: Seq<u8>)
    ensures admissible(source) ==> 8192 <= source.len() <= 18446744073709551615
        && ea_source::header_accepted(source.subrange(1024, 2048), source.len() as u64)
        && 2 < bytes::le32(source, 1028) <= block_claims::MAX_BLOCKS
        && bytes::le32(source, 1028) * 4096 <= source.len()
        && 0 < bytes::le32(source, 4104) < bytes::le32(source, 1028)
        && group::accepted_with_features(source.subrange(4096, 4096 + superblock::descriptor_bytes(source.subrange(1024, 2048)) as int),
            0, bytes::le32(source, 1028) as u32, bytes::le32(source, 1064) as u32,
            superblock::metadata_seed(source.subrange(1024, 2048)), superblock::flex_bg(source.subrange(1024, 2048)))
        && layout::admitted(source.subrange(bytes::le32(source, 4104) as int * 4096 + 1792, bytes::le32(source, 4104) as int * 4096 + 2048),
            bytes::le32(source, 1024) as u32, bytes::le32(source, 1028) as u32, superblock::metadata_seed(source.subrange(1024, 2048))),
{
    hide(crc::fold);
    if admissible(source) { reveal(valid); }
}

pub struct Bootstrap<'s, 'a> {
    source: &'s Snapshot<'a>, layout: JournalLayout, table: u32,
    blocks: u32, inodes: u32, ipg: u32, seed: u32, metadata_seed: u32,
}

impl<'s, 'a> Bootstrap<'s, 'a> {
    pub closed spec fn view(&self) -> BootstrapView {
        BootstrapView { source: self.source.view(), layout: self.layout.view(), table: self.table,
            blocks: self.blocks, inodes: self.inodes, ipg: self.ipg, seed: self.seed, metadata_seed: self.metadata_seed }
    }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    pub closed spec fn can_prepare_recovery(&self) -> bool {
        recovery_io::can_prepare_ea(journal_bytes(self.view()), journal_identity(self.view()), &self.layout,
            self.view().source.subrange(0, 4096), self.view().source.len() as u64)
    }

    pub proof fn recovery_profile_is_exact(&self, layout: &JournalLayout)
        requires self.wf(), layout.wf(), layout.view() == self.view().layout,
        ensures self.can_prepare_recovery() == source_can_prepare(self.view(), layout),
    {
        hide(crc::fold);
        hide(ea_source::header_accepted);
        hide(group::accepted_with_features);
        hide(layout::admitted);
        assert(self.layout.wf()) by { reveal(valid); }
        recovery_io::ea_recovery_profiles_depend_only_on_layout_views(journal_bytes(self.view()),
            journal_identity(self.view()), &self.layout, layout, self.view().source.subrange(0, 4096),
            self.view().source.len() as u64);
    }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn source(&self) -> (r: &'s Snapshot<'a>) ensures self.wf(), r.view() == self.view().source {
        proof { use_type_invariant(self); }
        self.source
    }

    pub fn layout(&self) -> (r: &JournalLayout) ensures self.wf(), r.wf(), r.view() == self.view().layout {
        proof { use_type_invariant(self); reveal(valid); }
        &self.layout
    }

    pub fn group_count(&self) -> (r: u32)
        ensures self.wf(), 0 < r <= 32, r as nat == (self.view().blocks as nat + 32767) / 32768,
    {
        proof { use_type_invariant(self); reveal(valid); }
        (self.blocks + 32767) / 32768
    }

    pub fn descriptor_size(&self) -> (r: usize)
        ensures self.wf(), r as nat == superblock::descriptor_bytes(self.view().source.subrange(1024, 2048)),
            r == 32 || r == 64,
    {
        let primary = self.primary();
        proof {
            reveal(valid);
            assert(primary@.subrange(1024, 2048) =~= self.view().source.subrange(1024, 2048));
        }
        superblock::descriptor_length(&primary[1024..2048]).unwrap()
    }

    pub fn journal_inode_block(&self) -> (r: u32) ensures self.wf(), r == self.view().table {
        proof { use_type_invariant(self); }
        self.table
    }

    pub fn primary(&self) -> (r: &'a [u8])
        ensures self.wf(), r@ == self.view().source.subrange(0, 4096), r.len() == 4096,
    {
        proof { use_type_invariant(self); reveal(valid); }
        self.source.block(0).unwrap().as_slice()
    }

    pub fn uuid(&self) -> (r: &'a [u8])
        ensures self.wf(), r@ == self.view().source.subrange(1128, 1144), r.len() == 16,
    {
        proof { use_type_invariant(self); reveal(valid); }
        self.source.block(0).unwrap().range(1128, 16).unwrap()
    }

    pub fn journal_uuid(&self) -> (r: &'a [u8])
        ensures self.wf(), r@ == journal_identity(self.view()), r.len() == 16,
    {
        proof { use_type_invariant(self); reveal(valid); }
        self.source.block(self.layout.physical_start()).unwrap().range(48, 16).unwrap()
    }

    pub fn raw_journal_inode(&self) -> (r: &'a [u8])
        ensures self.wf(), r@ == journal_inode(self.view()), r.len() == 256,
    {
        proof { use_type_invariant(self); reveal(valid); }
        self.source.block(self.table).unwrap().range(1792, 256).unwrap()
    }

    pub fn capture_journal(&self) -> (r: Vec<u8>)
        ensures self.wf(), r@ == self.view().source.subrange(self.view().layout.start as int * 4096,
            (self.view().layout.start as int + self.view().layout.journal_blocks) * 4096),
    {
        proof { use_type_invariant(self); reveal(valid); }
        self.source.capture(self.layout.physical_start(), self.layout.blocks()).unwrap()
    }

    pub fn prepare_recovery(&self) -> (r: Option<Recovery>)
        ensures self.wf(), match r {
            Some(engine) => engine.plan().refines() && engine.plan().layout().view() == self.view().layout
                && engine.primary() == self.view().source.subrange(0, 4096)
                && engine.partition_bytes() as nat == self.view().source.len()
                && engine.scan_result().certificate(scan_source(self.view()))
                && engine.scan_result().maximal(scan_source(self.view()))
                && crate::write_recovery::returned(engine.scan_result(), scan_source(self.view()))
                && engine.state().cursor == 0 && engine.state().request == 0
                && !engine.state().pending && !engine.state().faulted
                && (forall|i: int| 0 <= i < engine.plan().log().len() ==>
                    (#[trigger] engine.plan().log()[i]).block != 0),
            None => !self.can_prepare_recovery(),
        },
    {
        hide(crc::fold);
        hide(layout::admitted);
        hide(crate::inode::accepted);
        hide(ea_source::header_accepted);
        let _ = self.layout();
        let raw = self.raw_journal_inode();
        assert(layout::admitted(raw@, self.inodes, self.blocks, self.metadata_seed)) by { reveal(valid); }
        let layout = layout::from_inode(raw, self.inodes, self.blocks, self.metadata_seed).unwrap();
        assert(layout.view() == self.view().layout) by { reveal(valid); }
        assert(self.seed == crc::fold(0xffffffff, journal_identity(self.view()))) by { reveal(valid); }
        let journal = self.capture_journal();
        proof { self.recovery_profile_is_exact(&layout); }
        recovery_io::prepare_ea_no_primary(journal.as_slice(), self.journal_uuid(), layout, self.primary(), self.source.partition_bytes())
    }
}

#[verifier::rlimit(30)]
pub fn locate<'s, 'a>(source: &'s Snapshot<'a>) -> (r: Option<Bootstrap<'s, 'a>>)
    ensures match r {
        Some(found) => found.wf() && found.view().source == source.view() && found.view() == projection(source.view())
            && admissible(source.view()),
        None => !admissible(source.view()),
    },
{
    hide(crc::fold);
    hide(ea_source::header_accepted);
    hide(group::accepted_with_features);
    hide(layout::admitted);
    hide(crate::inode::accepted);
    proof { an_admitted_source_supplies_the_locator_inputs(source.view()); }
    let primary = match source.block(0) { Some(block) => block, None => { return None; } };
    let raw = primary.range(1024, 1024).unwrap();
    if !ea_source::validate_header(raw, source.partition_bytes()) { return None; }
    let blocks = bytes::read_le32(raw, 4).unwrap();
    if blocks > block_claims::MAX_BLOCKS { return None; }
    let inodes = bytes::read_le32(raw, 0).unwrap();
    let ipg = bytes::read_le32(raw, 40).unwrap();
    let metadata_seed = superblock::metadata_checksum_seed(raw).unwrap();
    let descriptor = match source.block(1) { Some(block) => block, None => { return None; } };
    let length = superblock::descriptor_length(raw).unwrap();
    let desc = descriptor.range(0, length).unwrap();
    let flex = superblock::flex_enabled(raw).unwrap();
    let group = match group::parse_with_features(desc, 0, blocks, ipg, metadata_seed, flex) { Some(group) => group, None => { return None; } };
    let table = group.inode_table;
    if table == 0 { return None; }
    let itable = match source.block(table) { Some(block) => block, None => { return None; } };
    let journal = itable.range(1792, 256).unwrap();
    let layout = match layout::from_inode(journal, inodes, blocks, metadata_seed) { Some(layout) => layout, None => { return None; } };
    assert(blocks as nat * 4096 <= source.view().len()) by { reveal(ea_source::header_accepted); }
    assert(table < blocks) by { reveal(group::accepted_with_features); }
    let journal_header = source.block(layout.physical_start()).unwrap();
    let uuid_bytes = journal_header.range(48, 16).unwrap();
    let seed = crc::crc32c(0xffffffff, uuid_bytes);
    let ghost assembled = BootstrapView { source: source.view(), layout: layout.view(), table, blocks, inodes, ipg, seed, metadata_seed };
    assert(journal_identity(assembled) =~= uuid_bytes@);
    assert(valid(assembled)) by { reveal(valid); reveal(ea_source::header_accepted); }
    proof { every_valid_bootstrap_is_the_unique_source_projection(assembled); }
    Some(Bootstrap { source, layout, table, blocks, inodes, ipg, seed, metadata_seed })
}

pub open spec fn identity_preserved(before: BootstrapView, after: Seq<u8>) -> bool {
    bootstrap_identity::preserved(before, after)
}

fn check_primary(before: &[u8], after: &[u8]) -> (r: bool)
    ensures r == primary_fixed(before@, after@),
{
    if before.len() != 4096 || after.len() != 4096 { return false; }
    if bytes::read_le32(before, 1116).unwrap() & !8u32 != bytes::read_le32(after, 1116).unwrap() & !8u32 { return false; }
    if (bytes::read_le32(before, 1120).unwrap() & 0xfffffffbu32)
        != (bytes::read_le32(after, 1120).unwrap() & 0xfffffffbu32) { return false; }
    let mut index = 0usize;
    while index < 4096
        invariant index <= 4096, before.len() == 4096, after.len() == 4096,
            forall|i: int| 0 <= i < index && !super_state::replay_mutable(i) ==> #[trigger] after@[i] == before@[i],
        decreases 4096 - index,
    {
        let mutable = (1032 <= index && index < 1044) || (1068 <= index && index < 1100)
            || (1116 <= index && index < 1120) || (1120 <= index && index < 1124) || (1144 <= index && index < 1224)
            || (1288 <= index && index < 1292) || (2044 <= index && index < 2048);
        if !mutable && after[index] != before[index] { return false; }
        index += 1;
    }
    true
}

fn check_addresses(before: &[u8], after: &[u8], groups: u32, width: usize) -> (r: bool)
    ensures r == addresses_fixed(before@, after@, groups as nat, width as nat),
{
    if before.len() != 4096 || after.len() != 4096 || groups == 0 || groups > 32 || (width != 32 && width != 64) { return false; }
    let mut group = 0u32;
    while group < groups
        invariant group <= groups <= 32, groups > 0, before.len() == 4096, after.len() == 4096, width == 32 || width == 64,
            forall|g: int| 0 <= g < group ==>
                #[trigger] after@.subrange(g * width, g * width + 12) == before@.subrange(g * width, g * width + 12)
                && (width == 64 ==> after@.subrange(g * width + 32, g * width + 44) == before@.subrange(g * width + 32, g * width + 44)),
        decreases groups - group,
    {
        let old = &before[group as usize * width..group as usize * width + 12];
        let new = &after[group as usize * width..group as usize * width + 12];
        if !bytes::equal(old, new) {
            assert(!addresses_fixed(before@, after@, groups as nat, width as nat));
            return false;
        }
        if width == 64 && !bytes::equal(&before[group as usize * width + 32..group as usize * width + 44],
            &after[group as usize * width + 32..group as usize * width + 44]) { return false; }
        group += 1;
    }
    true
}

pub fn check_identity(before: &Bootstrap<'_, '_>, after: &Snapshot<'_>) -> (r: bool)
    ensures before.wf(), r == preserved(before.view(), after.view()),
{
    let source = before.source();
    if source.partition_bytes() != after.partition_bytes() { return false; }
    assert(after.view().len() >= 8192) by { reveal(valid); }
    if !check_primary(before.primary(), after.block(0).unwrap().as_slice()) { return false; }
    if !check_addresses(source.block(1).unwrap().as_slice(), after.block(1).unwrap().as_slice(), before.group_count(), before.descriptor_size()) { return false; }
    let table = before.journal_inode_block();
    assert((table as nat + 1) * 4096 <= after.view().len()) by { reveal(valid); }
    let new_inode = after.block(table).unwrap().range(1792, 256).unwrap();
    bytes::equal(before.raw_journal_inode(), new_inode)
}

pub(crate) proof fn the_same_locator_inputs_give_an_admissible_source(before: BootstrapView, source: Seq<u8>)
    requires valid(before), source.len() == before.source.len(),
        ea_source::header_accepted(source.subrange(1024, 2048), source.len() as u64),
        bytes::le32(source, 1024) == before.inodes, bytes::le32(source, 1028) == before.blocks,
        bytes::le32(source, 1064) == before.ipg, bytes::le32(source, 4104) == before.table,
        superblock::metadata_seed(source.subrange(1024, 2048)) == before.metadata_seed,
        group::accepted_with_features(source.subrange(4096, 4096 + superblock::descriptor_bytes(source.subrange(1024, 2048)) as int),
            0, before.blocks, before.ipg, before.metadata_seed, superblock::flex_bg(source.subrange(1024, 2048))),
        source.subrange(before.table as int * 4096 + 1792, before.table as int * 4096 + 2048) == journal_inode(before),
    ensures admissible(source), same_locator_geometry(before, projection(source)),
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    hide(group::accepted_with_features);
    hide(layout::admitted);
    let tentative = BootstrapView { source, ..before };
    let candidate = BootstrapView { seed: crate::crc::fold(0xffffffff, journal_identity(tentative)), ..tentative };
    assert(valid(candidate)) by { reveal(valid); }
    every_valid_bootstrap_is_the_unique_source_projection(candidate);
}

pub(crate) proof fn primary_source_projection(before: BootstrapView, source: Seq<u8>)
    requires valid(before), source.len() == before.source.len(),
        bootstrap_identity::primary_fixed(before.source.subrange(0, 4096), source.subrange(0, 4096)),
    ensures bytes::le32(source, 1024) == before.inodes, bytes::le32(source, 1028) == before.blocks,
        bytes::le32(source, 1064) == before.ipg,
        superblock::metadata_seed(source.subrange(1024, 2048)) == before.metadata_seed,
        superblock::descriptor_bytes(source.subrange(1024, 2048)) == superblock::descriptor_bytes(before.source.subrange(1024, 2048)),
        superblock::flex_bg(source.subrange(1024, 2048)) == superblock::flex_bg(before.source.subrange(1024, 2048)),
{
    hide(crate::crc::fold);
    reveal(valid);
    bootstrap_identity::fixed_primary_identity_keeps_bootstrap_geometry_and_checksum_domain(before.source.subrange(0, 4096), source.subrange(0, 4096));
    assert(before.source.subrange(0, 4096).subrange(1024, 2048) =~= before.source.subrange(1024, 2048));
    assert(source.subrange(0, 4096).subrange(1024, 2048) =~= source.subrange(1024, 2048));
}

#[verifier::rlimit(30)]
proof fn mixed_primary_keeps_the_admitted_locator_inputs(before: BootstrapView, after: BootstrapView, source: Seq<u8>)
    requires valid(before), valid(after), same_locator_geometry(before, after),
        bootstrap_identity::primary_fixed(before.source.subrange(0, 4096), after.source.subrange(0, 4096)),
        source.len() == before.source.len(),
        source.subrange(0, 4096) == before.source.subrange(0, 4096) || source.subrange(0, 4096) == after.source.subrange(0, 4096),
    ensures source.len() >= 8192,
        ea_source::header_accepted(source.subrange(1024, 2048), source.len() as u64),
        bytes::le32(source, 1024) == before.inodes, bytes::le32(source, 1028) == before.blocks, bytes::le32(source, 1064) == before.ipg,
        superblock::metadata_seed(source.subrange(1024, 2048)) == before.metadata_seed,
        superblock::descriptor_bytes(source.subrange(1024, 2048)) == superblock::descriptor_bytes(before.source.subrange(1024, 2048)),
        superblock::flex_bg(source.subrange(1024, 2048)) == superblock::flex_bg(before.source.subrange(1024, 2048)),
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    hide(group::accepted_with_features);
    hide(layout::admitted);
    assert(bootstrap_identity::primary_fixed(before.source.subrange(0, 4096), source.subrange(0, 4096)));
    primary_source_projection(before, source);
    assert(source.len() >= 8192) by { reveal(valid); }
    assert(ea_source::header_accepted(source.subrange(1024, 2048), source.len() as u64)) by {
        reveal(valid);
        assert(source.subrange(1024, 2048) == source.subrange(0, 4096).subrange(1024, 2048));
        assert(before.source.subrange(1024, 2048) == before.source.subrange(0, 4096).subrange(1024, 2048));
        assert(after.source.subrange(1024, 2048) == after.source.subrange(0, 4096).subrange(1024, 2048));
    }
}

#[verifier::rlimit(30)]
proof fn mixed_descriptors_keep_the_admitted_locator_inputs(before: BootstrapView, after: BootstrapView, source: Seq<u8>)
    requires valid(before), valid(after), same_locator_geometry(before, after),
        bootstrap_identity::primary_fixed(before.source.subrange(0, 4096), after.source.subrange(0, 4096)),
        source.len() == before.source.len(),
        superblock::descriptor_bytes(source.subrange(1024, 2048)) == superblock::descriptor_bytes(before.source.subrange(1024, 2048)),
        superblock::flex_bg(source.subrange(1024, 2048)) == superblock::flex_bg(before.source.subrange(1024, 2048)),
        source.subrange(4096, 8192) == before.source.subrange(4096, 8192) || source.subrange(4096, 8192) == after.source.subrange(4096, 8192),
    ensures bytes::le32(source, 4104) == before.table,
        group::accepted_with_features(source.subrange(4096, 4096 + superblock::descriptor_bytes(source.subrange(1024, 2048)) as int),
            0, before.blocks, before.ipg, before.metadata_seed, superblock::flex_bg(source.subrange(1024, 2048))),
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    hide(group::accepted_with_features);
    hide(layout::admitted);
    primary_source_projection(before, after.source);
    assert(source.len() >= 8192 && before.source.len() >= 8192 && after.source.len() >= 8192) by { reveal(valid); }
    let width = superblock::descriptor_bytes(before.source.subrange(1024, 2048)) as int;
    assert(width == 32 || width == 64);
    assert(source.subrange(4096, 4096 + width) == source.subrange(4096, 8192).subrange(0, width));
    assert(before.source.subrange(4096, 4096 + width) == before.source.subrange(4096, 8192).subrange(0, width));
    assert(after.source.subrange(4096, 4096 + width) == after.source.subrange(4096, 8192).subrange(0, width));
    assert(bytes::le32(source, 4104) == before.table) by {
        reveal(valid);
        assert(bytes::le32(source.subrange(4096, 8192), 8) == bytes::le32(source, 4104));
        assert(bytes::le32(before.source.subrange(4096, 8192), 8) == bytes::le32(before.source, 4104));
        assert(bytes::le32(after.source.subrange(4096, 8192), 8) == bytes::le32(after.source, 4104));
    }
    assert(group::accepted_with_features(source.subrange(4096, 4096 + width), 0, before.blocks, before.ipg, before.metadata_seed,
        superblock::flex_bg(source.subrange(1024, 2048)))) by { reveal(valid); }
}

pub proof fn complete_bootstrap_block_mixtures_keep_the_same_admitted_locator(before: BootstrapView, after: BootstrapView, source: Seq<u8>)
    requires valid(before), valid(after), same_locator_geometry(before, after),
        bootstrap_identity::primary_fixed(before.source.subrange(0, 4096), after.source.subrange(0, 4096)),
        source.len() == before.source.len(),
        source.subrange(0, 4096) == before.source.subrange(0, 4096) || source.subrange(0, 4096) == after.source.subrange(0, 4096),
        source.subrange(4096, 8192) == before.source.subrange(4096, 8192) || source.subrange(4096, 8192) == after.source.subrange(4096, 8192),
        source.subrange(before.table as int * 4096 + 1792, before.table as int * 4096 + 2048) == journal_inode(before),
    ensures admissible(source), same_locator_geometry(before, projection(source)),
{
    mixed_primary_keeps_the_admitted_locator_inputs(before, after, source);
    mixed_descriptors_keep_the_admitted_locator_inputs(before, after, source);
    the_same_locator_inputs_give_an_admissible_source(before, source);
}


}
