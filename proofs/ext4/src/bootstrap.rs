// SPDX-License-Identifier: MPL-2.0

//! Locates the internal journal from one immutable source before whole-image
//! validation. Partially checkpointed allocation bitmaps are deliberately not
//! consumed here. This bounded locator conveys no write or mount authority.
//! See Linux ext4_get_journal_inode and __ext4_get_inode_loc at sources.json.

use vstd::prelude::*;
use crate::{block_claims, bytes, crc, group, layout::{self, JournalLayout, LayoutView}, recovery_io::{self, Recovery},
    scan_trace::Source, snapshot::Snapshot, superblock};

verus! {

pub struct BootstrapView {
    pub source: Seq<u8>, pub layout: LayoutView, pub table: u32,
    pub blocks: u32, pub inodes: u32, pub ipg: u32, pub seed: u32, pub metadata_seed: u32,
}

pub open spec fn journal_inode(v: BootstrapView) -> Seq<u8> {
    v.source.subrange(v.table as int * 4096 + 1792, v.table as int * 4096 + 2048)
}

pub open spec fn journal_bytes(v: BootstrapView) -> Seq<u8> {
    v.source.subrange(v.layout.start as int * 4096, (v.layout.start as int + v.layout.journal_blocks) * 4096)
}

pub open spec fn journal_identity(v: BootstrapView) -> Seq<u8> { journal_bytes(v).subrange(48, 64) }

pub open spec fn scan_source(v: BootstrapView) -> Source {
    let journal = journal_bytes(v);
    Source { journal, blocks: v.layout.journal_blocks, start: bytes::be32(journal, 28) as u32,
        first: bytes::be32(journal, 24) as u32, uuid: journal_identity(v), seed: v.seed, layout: v.layout }
}

#[verifier::opaque]
pub open spec fn valid(v: BootstrapView) -> bool {
    &&& 8192 <= v.source.len() <= 18446744073709551615
    &&& superblock::accepted(v.source.subrange(1024, 2048), v.source.len() as u64)
    &&& 2 < v.blocks <= block_claims::MAX_BLOCKS && v.blocks as nat * 4096 <= v.source.len()
    &&& v.blocks as nat == bytes::le32(v.source, 1028) && v.inodes as nat == bytes::le32(v.source, 1024)
    &&& v.ipg as nat == bytes::le32(v.source, 1064) && 0 < v.ipg <= 32768 && v.ipg % 16 == 0 && v.inodes >= 11
    &&& v.seed == crc::fold(0xffffffff, journal_identity(v))
    &&& v.metadata_seed == superblock::metadata_seed(v.source.subrange(1024, 2048))
    &&& group::accepted(v.source.subrange(4096, 4128), 0, v.blocks, v.ipg, v.metadata_seed)
    &&& v.table as nat == bytes::le32(v.source, 4104) && v.table < v.blocks
    &&& layout::admitted(journal_inode(v), v.inodes, v.blocks, v.metadata_seed)
    &&& v.layout.start > 1 && 1024 <= v.layout.journal_blocks <= 32768
    &&& v.layout.start as nat + v.layout.journal_blocks <= v.blocks && v.layout.fs_blocks == v.blocks
    &&& v.layout.start as nat == bytes::le32(journal_inode(v), 60)
    &&& v.layout.journal_blocks as nat == bytes::le32(journal_inode(v), 4) / 4096
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
                && engine.state().cursor == 0 && engine.state().request == 0
                && !engine.state().pending && !engine.state().faulted,
            None => true,
        },
    {
        hide(crc::fold);
        hide(layout::admitted);
        hide(crate::inode::accepted);
        hide(superblock::accepted);
        let _ = self.layout();
        let raw = self.raw_journal_inode();
        assert(layout::admitted(raw@, self.inodes, self.blocks, self.metadata_seed)) by { reveal(valid); }
        let layout = layout::from_inode(raw, self.inodes, self.blocks, self.metadata_seed).unwrap();
        assert(layout.view() == self.view().layout) by { reveal(valid); }
        assert(self.seed == crc::fold(0xffffffff, journal_identity(self.view()))) by { reveal(valid); }
        let journal = self.capture_journal();
        recovery_io::prepare(journal.as_slice(), self.journal_uuid(), layout, self.primary(), self.source.partition_bytes())
    }
}

pub fn locate<'s, 'a>(source: &'s Snapshot<'a>) -> (r: Option<Bootstrap<'s, 'a>>)
    ensures match r { Some(found) => found.wf() && found.view().source == source.view(), None => true },
{
    hide(crc::fold);
    hide(superblock::accepted);
    hide(group::accepted);
    hide(layout::admitted);
    hide(crate::inode::accepted);
    let primary = match source.block(0) { Some(block) => block, None => { return None; } };
    let raw = primary.range(1024, 1024).unwrap();
    let sb = match superblock::parse(raw, source.partition_bytes()) { Some(sb) => sb, None => { return None; } };
    let blocks = sb.blocks();
    if blocks > block_claims::MAX_BLOCKS { return None; }
    let inodes = sb.inodes();
    let ipg = bytes::read_le32(raw, 40).unwrap();
    let metadata_seed = superblock::metadata_checksum_seed(raw).unwrap();
    let descriptor = match source.block(1) { Some(block) => block, None => { return None; } };
    let desc = descriptor.range(0, 32).unwrap();
    let group = match group::parse(desc, 0, blocks, ipg, metadata_seed) { Some(group) => group, None => { return None; } };
    let table = group.inode_table;
    let itable = match source.block(table) { Some(block) => block, None => { return None; } };
    let journal = itable.range(1792, 256).unwrap();
    let layout = match layout::from_inode(journal, inodes, blocks, metadata_seed) { Some(layout) => layout, None => { return None; } };
    assert(blocks as nat * 4096 <= source.view().len()) by { reveal(superblock::accepted); }
    assert(table < blocks) by { reveal(group::accepted); }
    let journal_header = source.block(layout.physical_start()).unwrap();
    let uuid_bytes = journal_header.range(48, 16).unwrap();
    let seed = crc::crc32c(0xffffffff, uuid_bytes);
    let ghost assembled = BootstrapView { source: source.view(), layout: layout.view(), table, blocks, inodes, ipg, seed, metadata_seed };
    assert(journal_identity(assembled) =~= uuid_bytes@);
    assert(valid(assembled)) by { reveal(valid); }
    Some(Bootstrap { source, layout, table, blocks, inodes, ipg, seed, metadata_seed })
}

}
