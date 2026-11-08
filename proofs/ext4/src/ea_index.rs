// SPDX-License-Identifier: MPL-2.0

//! Complete group metadata for the isolated EA_INODE source profile.
//! This retains actual source features and logical lazy bitmap semantics;
//! inode-table block ranges are pairwise disjoint. This is not ordinary
//! filesystem admission or a complete physical ownership census.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{backup_layout, bitmap::{self, Bitmap, BitmapView}, block_bitmap, bytes, crc,
    ea_source::{self, Header, HeaderView, Node, NodeView}, group, group_fields, snapshot::Snapshot};

verus! {

pub struct GroupView {
    pub header: HeaderView, pub number: u32, pub descriptor: Seq<u8>,
    pub block_bitmap: u32, pub inode_bitmap: u32, pub inode_table: u32, pub table_blocks: u32,
    pub allocation: BitmapView, pub inodes: BitmapView,
}
pub open spec fn valid_bits(h: HeaderView, number: u32) -> nat {
    (group::end(h.blocks, number) - number as nat * 32768) as nat
}
pub open spec fn logical_blocks(h: HeaderView, number: u32, descriptor: Seq<u8>) -> Seq<u8> {
    if group::block_uninitialized(descriptor) {
        block_bitmap::canonical(block_bitmap::context_with_backup(descriptor, number, h.blocks, h.ipg,
            backup_layout::present(h.source.subrange(1024, 2048), number)))
    } else { h.source.subrange(bytes::le32(descriptor, 0) as int * 4096,
        (bytes::le32(descriptor, 0) as int + 1) * 4096) }
}
pub open spec fn logical_inodes(h: HeaderView, descriptor: Seq<u8>) -> Seq<u8> {
    if group::inode_uninitialized(descriptor) { bitmap::empty_inode_bytes(h.ipg as nat) }
    else { h.source.subrange(bytes::le32(descriptor, 4) as int * 4096,
        (bytes::le32(descriptor, 4) as int + 1) * 4096) }
}
#[verifier::opaque]
pub open spec fn group_valid(v: GroupView) -> bool {
    let h = v.header; let d = v.descriptor;
    &&& ea_source::header_valid(h) && v.number < h.groups && v.number < 32
    &&& d == h.source.subrange(4096 + v.number as int * h.width, 4096 + (v.number as int + 1) * h.width)
    &&& group::accepted_with_features(d, v.number, h.blocks, h.ipg, h.seed, h.flex)
    &&& v.block_bitmap as nat == bytes::le32(d, 0) && v.inode_bitmap as nat == bytes::le32(d, 4)
    &&& v.inode_table as nat == bytes::le32(d, 8) && v.table_blocks == h.ipg / 16
    &&& v.allocation.raw == logical_blocks(h, v.number, d)
    &&& v.allocation.valid as nat == valid_bits(h, v.number) && v.allocation.meaningful == 32768
    &&& v.allocation.free as nat == bytes::le16(d, 12) && v.allocation.seed == h.seed
    &&& v.allocation.checksum == if group::block_uninitialized(d) {
        (crc::fold(h.seed, logical_blocks(h, v.number, d)) & 0xffffu32) as u16
    } else { bytes::le16(d, 24) as u16 }
    &&& bitmap::accepted(v.allocation.raw, v.allocation.valid, v.allocation.meaningful,
        v.allocation.free, v.allocation.checksum, h.seed)
    &&& (h.width == 64 && !group::block_uninitialized(d) ==>
        crc::fold(h.seed, v.allocation.raw) == group_fields::counter(d, 24, 56, true))
    &&& v.inodes.raw == logical_inodes(h, d) && v.inodes.valid == h.ipg && v.inodes.meaningful == h.ipg
    &&& v.inodes.free as nat == bytes::le16(d, 14) && v.inodes.seed == h.seed
    &&& v.inodes.checksum == if group::inode_uninitialized(d) {
        (crc::fold(h.seed, bitmap::empty_inode_bytes(h.ipg as nat).take(h.ipg as int / 8)) & 0xffffu32) as u16
    } else { bytes::le16(d, 26) as u16 }
    &&& bitmap::accepted(v.inodes.raw, v.inodes.valid, v.inodes.meaningful, v.inodes.free, v.inodes.checksum, h.seed)
    &&& (h.width == 64 && !group::inode_uninitialized(d) ==>
        crc::fold(h.seed, v.inodes.raw.take(h.ipg as int / 8)) == group_fields::counter(d, 26, 58, true))
}

/// The unique group metadata projection of the actual source bytes.
/// Lazy groups use the logical Linux bitmap, independently of stale media.
pub open spec fn source_group(h: HeaderView, number: u32) -> GroupView {
    let d = h.source.subrange(4096 + number as int * h.width,
        4096 + (number as int + 1) * h.width);
    let blocks = logical_blocks(h, number, d);
    let inodes = logical_inodes(h, d);
    GroupView {
        header: h, number, descriptor: d,
        block_bitmap: bytes::le32(d, 0) as u32,
        inode_bitmap: bytes::le32(d, 4) as u32,
        inode_table: bytes::le32(d, 8) as u32, table_blocks: h.ipg / 16,
        allocation: BitmapView { raw: blocks, valid: valid_bits(h, number) as u32,
            meaningful: 32768, free: bytes::le16(d, 12) as u32, seed: h.seed,
            checksum: if group::block_uninitialized(d) {
                (crc::fold(h.seed, blocks) & 0xffffu32) as u16
            } else { bytes::le16(d, 24) as u16 } },
        inodes: BitmapView { raw: inodes, valid: h.ipg, meaningful: h.ipg,
            free: bytes::le16(d, 14) as u32, seed: h.seed,
            checksum: if group::inode_uninitialized(d) {
                (crc::fold(h.seed, bitmap::empty_inode_bytes(h.ipg as nat).take(h.ipg as int / 8)) & 0xffffu32) as u16
            } else { bytes::le16(d, 26) as u16 } },
    }
}

#[verifier::opaque]
pub open spec fn group_admissible(h: HeaderView, number: u32) -> bool {
    group_valid(source_group(h, number))
}

pub proof fn a_valid_group_is_the_unique_exact_source_projection(v: GroupView)
    requires group_valid(v),
    ensures v == source_group(v.header, v.number),
{
    hide(crc::fold);
    reveal(group_valid);
    assert(v.allocation == source_group(v.header, v.number).allocation);
    assert(v.inodes == source_group(v.header, v.number).inodes);
}

pub proof fn every_declaratively_valid_group_is_admissible(v: GroupView)
    requires group_valid(v),
    ensures group_admissible(v.header, v.number),
{
    a_valid_group_is_the_unique_exact_source_projection(v);
    reveal(group_admissible);
}

pub struct Group {
    descriptor: Vec<u8>, fields: group::Group, allocation: Bitmap, inodes: Bitmap,
    checked: Ghost<GroupView>,
}
impl Group {
    pub closed spec fn view(&self) -> GroupView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        group_valid(self.view()) && self.descriptor@ == self.view().descriptor
            && self.fields.number == self.view().number && self.fields.block_bitmap == self.view().block_bitmap
            && self.fields.inode_bitmap == self.view().inode_bitmap && self.fields.inode_table == self.view().inode_table
            && self.fields.inode_table_blocks == self.view().table_blocks
            && self.allocation.view() == self.view().allocation && self.inodes.view() == self.view().inodes
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn descriptor(&self) -> (r: &[u8])
        ensures self.wf(), group_valid(self.view()), r@ == self.view().descriptor,
    { proof { use_type_invariant(self); } &self.descriptor }
    pub fn bitmaps(&self) -> (r: (&Bitmap, &Bitmap))
        ensures self.wf(), group_valid(self.view()), r.0.view() == self.view().allocation && r.1.view() == self.view().inodes,
    { proof { use_type_invariant(self); } (&self.allocation, &self.inodes) }
    pub fn info(&self) -> (r: &group::Group)
        ensures self.wf(), group_valid(self.view()), r.number == self.view().number
            && r.block_bitmap == self.view().block_bitmap && r.inode_bitmap == self.view().inode_bitmap
            && r.inode_table == self.view().inode_table && r.inode_table_blocks == self.view().table_blocks,
    { proof { use_type_invariant(self); } &self.fields }
}
fn copy(raw: &[u8]) -> (r: Vec<u8>) ensures r@ == raw@ {
    let mut result = Vec::new(); let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len(), result@ == raw@.take(i as int),
        decreases raw.len() - i,
    { result.push(raw[i]); assert(result@ =~= raw@.take(i as int + 1)); i += 1; }
    result
}
fn read_group(header: &Header<'_, '_>, number: u32) -> (r: Option<Group>)
    ensures header.wf(), ea_source::header_valid(header.view()), match r {
        Some(g) => g.wf() && group_valid(g.view()) && g.view().header == header.view() && g.view().number == number
            && g.view() == source_group(header.view(), number) && group_admissible(header.view(), number),
        None => !group_admissible(header.view(), number) },
{
    hide(crc::fold);
    reveal(group_admissible);
    let ghost expected = source_group(header.view(), number);
    proof {
        if group_admissible(header.view(), number) {
            reveal(group_valid);
        }
    }
    let (blocks, _, ipg, seed) = header.parameters();
    let width = header.descriptor_width(); let source = header.source();
    if width != 32 && width != 64 { return None; }
    proof { reveal(ea_source::header_valid); }
    let count = ((blocks as u64 + 32767) / 32768) as u32;
    if number >= count || number >= 32 { return None; }
    let primary = match source.block(0) { Some(block) => block, None => { return None; } };
    let boot = primary.range(1024, 1024).unwrap();
    let backup = backup_layout::has_backup(boot, number).unwrap();
    let flex = crate::superblock::flex_enabled(boot).unwrap();
    let gdt = match source.block(1) { Some(block) => block, None => { return None; } };
    assert(number as nat * width as nat <= 2048) by (nonlinear_arith)
        requires number < 32, width <= 64;
    let offset = number as usize * width;
    let raw = match gdt.range(offset, width) { Some(raw) => raw, None => { return None; } };
    assert(source.view() == header.view().source);
    assert(raw@ == source.view().subrange(4096 + offset as int, 4096 + offset as int + width));
    assert(number as int * width as int + width as int == (number as int + 1) * width as int) by (nonlinear_arith);
    assert(raw@ == header.view().source.subrange(4096 + number as int * width, 4096 + (number as int + 1) * width));
    assert(raw@ == expected.descriptor);
    let fields = match group::parse_with_features(raw, number, blocks, ipg, seed, flex) { Some(fields) => fields, None => { return None; } };
    let block_bytes = match source.block(fields.block_bitmap) { Some(block) => block, None => { return None; } };
    let inode_bytes = match source.block(fields.inode_bitmap) { Some(block) => block, None => { return None; } };
    let physical_blocks = block_bytes.as_slice(); let physical_inodes = inode_bytes.as_slice();
    let flags = bytes::read_le16(raw, 18).unwrap();
    let lazy_inodes = flags & 1 != 0; let lazy_blocks = flags & 2 != 0;
    let free_blocks = bytes::read_le16(raw, 12).unwrap() as u32;
    let free_inodes = bytes::read_le16(raw, 14).unwrap() as u32;
    assert(number as nat * 32768 < blocks) by { reveal(group::accepted_with_features); }
    let available = blocks - number * 32768;
    let meaningful_blocks = if available < 32768 { available } else { 32768u32 };
    assert(meaningful_blocks as nat == valid_bits(header.view(), number));
    if width == 64 {
        let block_checksum = group_fields::read_counter(raw, 24, 56, true).unwrap();
        let inode_checksum = group_fields::read_counter(raw, 26, 58, true).unwrap();
        if !lazy_blocks && crc::crc32c(seed, physical_blocks) != block_checksum { return None; }
        if !lazy_inodes && crc::crc32c(seed, &physical_inodes[..(ipg / 8) as usize]) != inode_checksum { return None; }
    }
    let allocation = if lazy_blocks {
        proof {
            if group_admissible(header.view(), number) {
                reveal(block_bitmap::admitted_with_backup);
                assert(block_bitmap::admitted_with_backup(raw@, number, blocks, ipg, seed, flex, backup));
            }
        }
        match block_bitmap::synthesize_with_backup(raw, number, blocks, ipg, seed, flex, backup) {
            Some(bitmap) => bitmap, None => { return None; }
        }
    } else {
        match bitmap::parse(physical_blocks, meaningful_blocks, 32768, free_blocks, bytes::read_le16(raw, 24).unwrap(), seed) {
            Some(bitmap) => bitmap, None => { return None; }
        }
    };
    let inodes = if lazy_inodes {
        assert(free_inodes == ipg) by { reveal(group::accepted_with_features); }
        match bitmap::synthesize_free_inodes(ipg, seed) { Some(bitmap) => bitmap, None => { return None; } }
    } else {
        match bitmap::parse(physical_inodes, ipg, ipg, free_inodes, bytes::read_le16(raw, 26).unwrap(), seed) {
            Some(bitmap) => bitmap, None => { return None; }
        }
    };
    let descriptor = copy(raw);
    let ghost view = GroupView { header: header.view(), number, descriptor: descriptor@,
        block_bitmap: fields.block_bitmap, inode_bitmap: fields.inode_bitmap, inode_table: fields.inode_table,
        table_blocks: fields.inode_table_blocks, allocation: allocation.view(), inodes: inodes.view() };
    assert(group_valid(view)) by { reveal(group_valid); }
    proof { a_valid_group_is_the_unique_exact_source_projection(view); }
    Some(Group { descriptor, fields, allocation, inodes, checked: Ghost(view) })
}

pub open spec fn views(groups: Seq<Group>) -> Seq<GroupView> {
    Seq::new(groups.len(), |i: int| groups[i].view())
}
#[verifier::opaque]
pub open spec fn free_block_count(groups: Seq<GroupView>) -> nat
    decreases groups.len(),
{ if groups.len() == 0 { 0nat } else { free_block_count(groups.drop_last()) + groups.last().allocation.free as nat } }
#[verifier::opaque]
pub open spec fn free_inode_count(groups: Seq<GroupView>) -> nat
    decreases groups.len(),
{ if groups.len() == 0 { 0nat } else { free_inode_count(groups.drop_last()) + groups.last().inodes.free as nat } }

pub struct IndexView { pub header: HeaderView, pub groups: Seq<GroupView> }
pub open spec fn separate_tables(a: GroupView, b: GroupView) -> bool {
    a.inode_table as nat + a.table_blocks <= b.inode_table
        || b.inode_table as nat + b.table_blocks <= a.inode_table
}
pub open spec fn tables_separated(groups: Seq<GroupView>) -> bool {
    forall|a: int, b: int| 0 <= a < b < groups.len() ==> #[trigger] separate_tables(groups[a], groups[b])
}
pub open spec fn inode_tables_disjoint(v: IndexView) -> bool { tables_separated(v.groups) }
pub open spec fn table_contains(g: GroupView, block: u32) -> bool {
    g.inode_table <= block < g.inode_table as nat + g.table_blocks
}
pub open spec fn table_member(v: IndexView, block: u32) -> bool {
    exists|i: int| 0 <= i < v.groups.len() && #[trigger] table_contains(v.groups[i], block)
}
fn check_inode_tables(groups: &[Group]) -> (r: bool)
    ensures r == tables_separated(views(groups@)),
{
    let mut i = 0usize;
    while i < groups.len()
        invariant i <= groups.len(),
            forall|a: int, b: int| 0 <= a < b < i ==> #[trigger] separate_tables(views(groups@)[a], views(groups@)[b]),
        decreases groups.len() - i,
    {
        let mut j = 0usize;
        while j < i
            invariant j <= i < groups.len(),
                forall|a: int, b: int| 0 <= a < b < i ==> #[trigger] separate_tables(views(groups@)[a], views(groups@)[b]),
                forall|a: int| 0 <= a < j ==> #[trigger] separate_tables(views(groups@)[a], views(groups@)[i as int]),
            decreases i - j,
        {
            let a = groups[j].info(); let b = groups[i].info();
            if !(a.inode_table as u64 + a.inode_table_blocks as u64 <= b.inode_table as u64
                || b.inode_table as u64 + b.inode_table_blocks as u64 <= a.inode_table as u64)
            {
                assert(!separate_tables(views(groups@)[j as int], views(groups@)[i as int]));
                assert(!tables_separated(views(groups@)));
                return false;
            }
            assert(separate_tables(views(groups@)[j as int], views(groups@)[i as int]));
            j += 1;
        }
        i += 1;
    }
    true
}
proof fn header_bounds(h: HeaderView)
    requires ea_source::header_valid(h),
    ensures 2 < h.blocks <= 1048576, 11 <= h.inodes <= 1048576,
        0 < h.ipg <= 32768, h.ipg % 16 == 0, 0 < h.groups <= 32,
        h.inodes as nat == h.groups as nat * h.ipg as nat,
{
    reveal(ea_source::header_valid);
    assert(h.inodes as nat == h.groups as nat * h.ipg as nat);
    assert(h.groups as nat * h.ipg as nat <= 1048576) by (nonlinear_arith)
        requires h.groups <= 32, h.ipg <= 32768;
}
#[verifier::opaque]
pub open spec fn ordered(groups: Seq<GroupView>, header: HeaderView) -> bool {
    forall|i: int| 0 <= i < groups.len() ==> #[trigger] group_valid(groups[i])
        && groups[i].header == header && groups[i].number as int == i
}
#[verifier::opaque]
pub open spec fn valid(v: IndexView) -> bool {
    &&& ea_source::header_valid(v.header) && v.groups.len() == v.header.groups
    &&& 2 < v.header.blocks <= 1048576 && 11 <= v.header.inodes <= 1048576
    &&& 0 < v.header.ipg <= 32768 && v.header.ipg % 16 == 0 && 0 < v.header.groups <= 32
    &&& ordered(v.groups, v.header)
    &&& inode_tables_disjoint(v)
    &&& free_block_count(v.groups) == bytes::le32(v.header.source, 1036)
    &&& free_inode_count(v.groups) == bytes::le32(v.header.source, 1040)
}

/// Canonical complete index of actual source group descriptors and bitmaps.
pub open spec fn source_groups(header: HeaderView) -> Seq<GroupView> {
    Seq::new(header.groups as nat, |i: int| source_group(header, i as u32))
}
pub open spec fn source_index(header: HeaderView) -> IndexView {
    IndexView { header, groups: source_groups(header) }
}
#[verifier::opaque]
pub open spec fn admissible(header: HeaderView) -> bool { valid(source_index(header)) }

pub proof fn a_valid_index_is_the_unique_exact_source_projection(v: IndexView)
    requires valid(v),
    ensures v == source_index(v.header),
{
    reveal(valid);
    reveal(ordered);
    assert(v.groups =~= source_groups(v.header)) by {
        assert forall|i: int| 0 <= i < v.groups.len()
            implies #[trigger] v.groups[i] == source_groups(v.header)[i] by {
            every_index_group_retains_its_exact_source_header_and_order(v, i);
            assert(v.groups[i].header == v.header && v.groups[i].number as int == i);
            assert(0 <= i < v.header.groups <= 32);
            assert(v.groups[i].number == i as u32);
            assert(source_groups(v.header)[i] == source_group(v.header, i as u32));
            a_valid_group_is_the_unique_exact_source_projection(v.groups[i]);
        }
    }
}

pub proof fn every_declaratively_valid_index_is_admissible(v: IndexView)
    requires valid(v),
    ensures admissible(v.header),
{
    a_valid_index_is_the_unique_exact_source_projection(v);
    reveal(admissible);
}

pub open spec fn inode_allocated(v: IndexView, number: u32) -> bool {
    0 < number <= v.header.inodes && bitmap::set(
        v.groups[(number as int - 1) / v.header.ipg as int].inodes.raw,
        (number as int - 1) % v.header.ipg as int)
}

/// Allocation alone does not validate an inode-table slot: the exact source
/// slot must also pass the initialized-table and bitmap provenance checks.
pub open spec fn node_admissible(v: IndexView, number: u32) -> bool {
    inode_allocated(v, number) && ea_source::node_admissible(v.header, number)
}

proof fn append_ordered(groups: Seq<GroupView>, header: HeaderView, next: GroupView)
    requires ordered(groups, header), group_valid(next), next.header == header && next.number as nat == groups.len(),
    ensures ordered(groups.push(next), header),
{
    reveal(ordered);
    assert forall|i: int| 0 <= i < groups.push(next).len() implies #[trigger] group_valid(groups.push(next)[i])
        && groups.push(next)[i].header == header && groups.push(next)[i].number as int == i by {
        if i < groups.len() { assert(groups.push(next)[i] == groups[i]); }
        else { assert(groups.push(next)[i] == next); }
    }
}
proof fn group_inode_limit(g: GroupView)
    requires group_valid(g),
    ensures g.inodes.valid == g.header.ipg,
{ reveal(group_valid); }
proof fn inode_coordinates(v: IndexView, number: u32)
    requires valid(v), 0 < number <= v.header.inodes,
    ensures 0 <= ((number as int - 1) / (v.header.ipg as int)) < v.groups.len(),
        0 <= ((number as int - 1) % (v.header.ipg as int)) < v.header.ipg,
        v.groups[(number as int - 1) / v.header.ipg as int].inodes.valid == v.header.ipg,
{
    reveal(valid);
    header_bounds(v.header);
    assert(v.header.inodes as nat == v.groups.len() * v.header.ipg as nat);
    vstd::arithmetic::mul::lemma_mul_is_commutative(v.header.ipg as int, v.groups.len() as int);
    vstd::arithmetic::div_mod::lemma_multiply_divide_lt(number as int - 1, v.header.ipg as int, v.groups.len() as int);
    let g = (number as int - 1) / v.header.ipg as int;
    every_index_group_retains_its_exact_source_header_and_order(v, g);
    group_inode_limit(v.groups[g]);
}

pub struct Index<'s, 'a> { header: Header<'s, 'a>, groups: Vec<Group>, checked: Ghost<IndexView> }
impl<'s, 'a> Index<'s, 'a> {
    pub closed spec fn view(&self) -> IndexView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        valid(self.view()) && self.header.view() == self.view().header && views(self.groups@) == self.view().groups
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn header(&self) -> (r: &Header<'s, 'a>)
        ensures self.wf(), valid(self.view()), r.wf(), ea_source::header_valid(r.view()), r.view() == self.view().header,
    {
        proof { use_type_invariant(self); reveal(valid); }
        let _ = self.header.parameters(); &self.header
    }
    pub fn source(&self) -> (r: &'s Snapshot<'a>)
        ensures self.wf(), valid(self.view()), r.view() == self.view().header.source,
    { proof { use_type_invariant(self); } self.header.source() }
    pub fn parameters(&self) -> (r: (u32, u32, u32, u32))
        ensures self.wf(), valid(self.view()), r == (self.view().header.blocks, self.view().header.inodes, self.view().header.ipg, self.view().header.seed),
            2 < r.0 <= 1048576, 11 <= r.1 <= 1048576, 0 < r.2 <= 32768, r.2 % 16 == 0,
    { proof { use_type_invariant(self); reveal(valid); } self.header.parameters() }
    pub fn group_count(&self) -> (r: usize)
        ensures self.wf(), valid(self.view()), r == self.view().groups.len(), 0 < r <= 32,
    {
        proof { use_type_invariant(self); reveal(valid); reveal(ea_source::header_valid); }
        self.groups.len()
    }
    pub fn group(&self, number: u32) -> (r: Option<&Group>)
        ensures self.wf(), valid(self.view()), match r {
            Some(group) => group.wf() && group_valid(group.view()) && number < self.view().groups.len()
                && group.view() == self.view().groups[number as int],
            None => number >= self.view().groups.len(),
        },
    {
        proof { use_type_invariant(self); }
        if number as usize >= self.groups.len() { return None; }
        let result = &self.groups[number as usize];
        let _ = result.info();
        proof { reveal(valid); reveal(ordered); }
        Some(result)
    }
    pub fn allocated(&self, number: u32) -> (r: Option<bool>)
        ensures self.wf(), valid(self.view()), match r {
            Some(set) => 0 < number <= self.view().header.inodes && set == inode_allocated(self.view(), number),
            None => number == 0 || number > self.view().header.inodes,
        },
    {
        proof { use_type_invariant(self); }
        let (_, inodes, ipg, _) = self.parameters();
        if number == 0 || number > inodes { return None; }
        let group_number = (number - 1) / ipg; let slot = (number - 1) % ipg;
        proof { inode_coordinates(self.view(), number); }
        let group = self.group(group_number).unwrap();
        let (_, bitmap) = group.bitmaps();
        let set = bitmap.is_set(slot).unwrap();
        Some(set)
    }
    pub fn node(&self, number: u32) -> (r: Option<Node<'a>>)
        ensures self.wf(), valid(self.view()), match r {
            Some(node) => node.wf() && ea_source::node_valid(node.view()) && node.view().header == self.view().header
                && node.view().number == number && inode_allocated(self.view(), number)
                && node.view() == ea_source::node_projection(self.view().header, number)
                && node_admissible(self.view(), number),
            None => !node_admissible(self.view(), number),
        },
    {
        proof { use_type_invariant(self); }
        let set = match self.allocated(number) { Some(set) => set, None => { return None; } };
        if !set { return None; }
        self.header.get(number)
    }
    pub fn is_inode_table_block(&self, block: u32) -> (r: bool)
        ensures self.wf(), valid(self.view()), r == table_member(self.view(), block),
    {
        proof { use_type_invariant(self); }
        let count = self.group_count(); let mut i = 0usize;
        while i < count
            invariant self.wf(), valid(self.view()), count == self.view().groups.len(), count <= 32, i <= count,
                forall|a: int| 0 <= a < i ==> !#[trigger] table_contains(self.view().groups[a], block),
            decreases count - i,
        {
            let group = self.group(i as u32).unwrap(); let fields = group.info();
            if fields.inode_table <= block && (block as u64) < fields.inode_table as u64 + fields.inode_table_blocks as u64 {
                assert(table_contains(self.view().groups[i as int], block));
                assert(table_member(self.view(), block));
                return true;
            }
            assert(!table_contains(self.view().groups[i as int], block));
            i += 1;
        }
        assert(!table_member(self.view(), block));
        false
    }
}

pub fn parse<'s, 'a>(header: Header<'s, 'a>) -> (r: Option<Index<'s, 'a>>)
    ensures header.wf(), ea_source::header_valid(header.view()), match r {
        Some(index) => index.wf() && valid(index.view()) && index.view().header == header.view()
            && index.view() == source_index(header.view()) && admissible(header.view()),
        None => !admissible(header.view()),
    },
{
    reveal(admissible);
    let (blocks, inodes, ipg, seed) = header.parameters();
    proof { header_bounds(header.view()); reveal(ea_source::header_valid); }
    let source = header.source(); let primary = match source.block(0) { Some(block) => block, None => { return None; } };
    let boot = primary.range(1024, 1024).unwrap();
    let count = ((blocks as u64 + 32767) / 32768) as u32;
    proof { header_bounds(header.view()); reveal(ea_source::header_valid); }
    if count == 0 || count > 32 { return None; }
    let mut groups: Vec<Group> = Vec::new(); let mut number = 0u32;
    let mut block_free = 0u64; let mut inode_free = 0u64;
    assert(views(groups@) =~= Seq::<GroupView>::empty());
    assert(ordered(views(groups@), header.view())) by { reveal(ordered); }
    assert(free_block_count(views(groups@)) == 0 && free_inode_count(views(groups@)) == 0) by {
        reveal(free_block_count); reveal(free_inode_count);
    }
    while number < count
        invariant header.wf(), ea_source::header_valid(header.view()),
            8192 <= header.view().source.len(),
            boot.len() == 1024, boot@ == header.view().source.subrange(1024, 2048),
            blocks == header.view().blocks, inodes == header.view().inodes, ipg == header.view().ipg, seed == header.view().seed,
            2 < header.view().blocks <= 1048576, 11 <= header.view().inodes <= 1048576,
            0 < header.view().ipg <= 32768, header.view().ipg % 16 == 0, 0 < header.view().groups <= 32,
            groups.len() == number, number <= count <= 32, count == header.view().groups,
            block_free as nat == free_block_count(views(groups@)), inode_free as nat == free_inode_count(views(groups@)),
            block_free as nat <= number as nat * 32768, inode_free as nat <= number as nat * 32768,
            ordered(views(groups@), header.view()),
            views(groups@) == source_groups(header.view()).take(number as int),
        decreases count - number,
    {
        proof {
            if admissible(header.view()) {
                reveal(admissible);
                every_index_group_retains_its_exact_source_header_and_order(source_index(header.view()), number as int);
                assert(group_admissible(header.view(), number)) by { reveal(group_admissible); }
            }
        }
        let group = match read_group(&header, number) { Some(group) => group, None => { return None; } };
        let (allocation, inodes) = group.bitmaps();
        block_free += allocation.free_count() as u64; inode_free += inodes.free_count() as u64;
        let ghost previous = views(groups@); let ghost next = group.view();
        proof { append_ordered(previous, header.view(), next); }
        groups.push(group);
        proof {
            assert(views(groups@) =~= previous.push(next));
            assert(views(groups@).drop_last() =~= previous);
            assert(views(groups@).last() == next);
            assert(views(groups@) =~= source_groups(header.view()).take(number as int + 1));
            assert(free_block_count(views(groups@)) == free_block_count(previous) + next.allocation.free as nat) by { reveal(free_block_count); }
            assert(free_inode_count(views(groups@)) == free_inode_count(previous) + next.inodes.free as nat) by { reveal(free_inode_count); }
        }
        number += 1;
    }
    assert(views(groups@) =~= source_groups(header.view()));
    proof {
        if admissible(header.view()) {
            reveal(admissible);
            reveal(valid);
        }
    }
    if block_free != bytes::read_le32(boot, 12).unwrap() as u64 || inode_free != bytes::read_le32(boot, 16).unwrap() as u64 { return None; }
    if !check_inode_tables(&groups) { return None; }
    let ghost view = IndexView { header: header.view(), groups: views(groups@) };
    assert(valid(view)) by { reveal(valid); }
    assert(view == source_index(header.view()));
    Some(Index { header, groups, checked: Ghost(view) })
}

pub proof fn every_index_group_retains_its_exact_source_header_and_order(v: IndexView, number: int)
    requires valid(v), 0 <= number < v.groups.len(),
    ensures group_valid(v.groups[number]), v.groups[number].header == v.header, v.groups[number].number as int == number,
{ reveal(valid); reveal(ordered); }
pub proof fn every_ea_index_has_exact_primary_free_counters(v: IndexView)
    requires valid(v),
    ensures free_block_count(v.groups) == bytes::le32(v.header.source, 1036),
        free_inode_count(v.groups) == bytes::le32(v.header.source, 1040),
{ reveal(valid); }
pub proof fn distinct_group_inode_tables_have_disjoint_block_ranges(v: IndexView, a: int, b: int)
    requires valid(v), 0 <= a < b < v.groups.len(),
    ensures separate_tables(v.groups[a], v.groups[b]),
{ reveal(valid); }
pub proof fn a_block_cannot_belong_to_two_distinct_inode_tables(v: IndexView, a: int, b: int, block: u32)
    requires valid(v), 0 <= a < b < v.groups.len(), table_contains(v.groups[a], block),
    ensures !table_contains(v.groups[b], block),
{
    distinct_group_inode_tables_have_disjoint_block_ranges(v, a, b);
}
proof fn group_table_geometry(g: GroupView)
    requires group_valid(g),
    ensures g.descriptor == g.header.source.subrange(4096 + g.number as int * g.header.width,
            4096 + (g.number as int + 1) * g.header.width),
        g.inode_table as nat == bytes::le32(g.descriptor, 8),
        g.table_blocks == g.header.ipg / 16,
        g.inode_table as nat + g.table_blocks <= g.header.blocks,
{
    reveal(group_valid);
    reveal(group::accepted_with_features);
}
proof fn source_inode_coordinates(v: IndexView, node: NodeView)
    requires valid(v), ea_source::node_valid(node), node.header == v.header,
    ensures 0 <= (node.group as int) < v.groups.len(), node.slot < v.header.ipg,
        node.number as nat == node.group as nat * v.header.ipg as nat + node.slot as nat + 1,
        v.groups[node.group as int].descriptor == node.descriptor,
        node.position as nat == v.groups[node.group as int].inode_table as nat * 4096 + node.slot as nat * 256,
        v.groups[node.group as int].inode_table as nat * 4096 <= node.position,
        node.position as nat + 256 <= (v.groups[node.group as int].inode_table as nat + v.groups[node.group as int].table_blocks) * 4096,
        node.position as nat / 4096 < v.header.blocks,
        table_contains(v.groups[node.group as int], (node.position / 4096) as u32),
{
    reveal(valid); reveal(ea_source::node_valid);
    let g = node.group as int;
    every_index_group_retains_its_exact_source_header_and_order(v, g);
    group_table_geometry(v.groups[g]);
    assert(v.groups[g].descriptor == node.descriptor);
    let base = v.groups[g].inode_table as int;
    let count = v.groups[g].table_blocks as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(node.number as int - 1, v.header.ipg as int);
    assert(node.number as nat == node.group as nat * v.header.ipg as nat + node.slot as nat + 1);
    assert(node.position as int == base * 4096 + node.slot as int * 256);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(v.header.ipg as int, 16);
    assert(count * 16 == v.header.ipg);
    assert(node.position as nat + 256 <= (base + count) * 4096);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(node.slot as int, 16);
    vstd::arithmetic::div_mod::lemma_multiply_divide_lt(node.slot as int, 16, count);
    assert(node.position as int == (base + node.slot as int / 16) * 4096 + (node.slot as int % 16) * 256);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(node.position as int, 4096,
        base + node.slot as int / 16, (node.slot as int % 16) * 256);
    assert(node.position as nat / 4096 < v.header.blocks);
    assert((node.position / 4096) as u32 as nat == node.position as nat / 4096);
    assert(table_contains(v.groups[g], (node.position / 4096) as u32));
}
pub proof fn source_inode_block_belongs_to_one_checked_inode_table(v: IndexView, node: NodeView)
    requires valid(v), ea_source::node_valid(node), node.header == v.header,
    ensures table_member(v, (node.position / 4096) as u32),
{
    source_inode_coordinates(v, node);
    assert(table_contains(v.groups[node.group as int], (node.position / 4096) as u32));
}
pub proof fn distinct_source_inode_slots_have_disjoint_byte_ranges(v: IndexView, a: NodeView, b: NodeView)
    requires valid(v), ea_source::node_valid(a), ea_source::node_valid(b),
        a.header == v.header, b.header == v.header, a.number != b.number,
    ensures a.position as nat + 256 <= b.position || b.position as nat + 256 <= a.position,
{
    source_inode_coordinates(v, a); source_inode_coordinates(v, b);
    let ga = a.group as int; let gb = b.group as int;
    if ga == gb {
        assert(a.slot != b.slot);
        if a.slot < b.slot { assert(a.position as nat + 256 <= b.position); }
        else { assert(b.position as nat + 256 <= a.position); }
    } else {
        if ga < gb { distinct_group_inode_tables_have_disjoint_block_ranges(v, ga, gb); }
        else {
            distinct_group_inode_tables_have_disjoint_block_ranges(v, gb, ga);
            assert(separate_tables(v.groups[ga], v.groups[gb]));
        }
        if v.groups[ga].inode_table as nat + v.groups[ga].table_blocks <= v.groups[gb].inode_table {
            assert(a.position as nat + 256 <= b.position);
        } else { assert(b.position as nat + 256 <= a.position); }
    }
}
pub proof fn stale_inode_bitmap_bytes_in_uninitialized_groups_grant_no_inode(v: IndexView, number: u32)
    requires valid(v), 0 < number <= v.header.inodes,
        group::inode_uninitialized(v.groups[(number as int - 1) / v.header.ipg as int].descriptor),
    ensures !inode_allocated(v, number),
{
    reveal(valid); reveal(ordered);
    let g = (number as int - 1) / v.header.ipg as int; let slot = (number as int - 1) % v.header.ipg as int;
    assert(0 <= g < v.groups.len()) by {
        reveal(ea_source::header_valid);
        vstd::arithmetic::mul::lemma_mul_is_commutative(v.header.ipg as int, v.groups.len() as int);
        vstd::arithmetic::div_mod::lemma_multiply_divide_lt(number as int - 1, v.header.ipg as int, v.groups.len() as int);
    }
    assert(group_valid(v.groups[g])); reveal(group_valid);
    bitmap::empty_inode_bitmap_has_only_allocated_padding(v.header.ipg, slot);
}
pub proof fn ea_indices_do_not_enable_ordinary_feature_admission(v: IndexView)
    requires valid(v),
    ensures !crate::feature_policy::incompat_allowed(bytes::le32(v.header.source, 1120) as u32),
{
    reveal(valid);
    ea_source::ea_read_headers_do_not_satisfy_ordinary_feature_admission(v.header);
}

}
