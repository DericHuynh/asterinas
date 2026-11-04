// SPDX-License-Identifier: MPL-2.0

//! Locates the internal journal from one immutable source before whole-image
//! validation. Partially checkpointed allocation bitmaps are deliberately not
//! consumed here. This bounded locator conveys no write or mount authority.
//! See Linux ext4_get_journal_inode and __ext4_get_inode_loc at sources.json.

use vstd::prelude::*;
use crate::{block_claims, bytes, crc, group, layout::{self, JournalLayout, LayoutView}, snapshot::Snapshot, superblock};

verus! {

pub struct BootstrapView {
    pub source: Seq<u8>, pub layout: LayoutView, pub table: u32,
    pub blocks: u32, pub inodes: u32, pub ipg: u32, pub seed: u32,
}

pub open spec fn journal_inode(v: BootstrapView) -> Seq<u8> {
    v.source.subrange(v.table as int * 4096 + 1792, v.table as int * 4096 + 2048)
}

#[verifier::opaque]
pub open spec fn valid(v: BootstrapView) -> bool {
    &&& 8192 <= v.source.len() <= 18446744073709551615
    &&& superblock::accepted(v.source.subrange(1024, 2048), v.source.len() as u64)
    &&& 2 < v.blocks <= block_claims::MAX_BLOCKS && v.blocks as nat * 4096 <= v.source.len()
    &&& v.blocks as nat == bytes::le32(v.source, 1028) && v.inodes as nat == bytes::le32(v.source, 1024)
    &&& v.ipg as nat == bytes::le32(v.source, 1064) && 0 < v.ipg <= 32768 && v.ipg % 16 == 0 && v.inodes >= 11
    &&& v.seed == crc::fold(0xffffffff, v.source.subrange(1128, 1144))
    &&& group::accepted(v.source.subrange(4096, 4128), 0, v.blocks, v.ipg, v.seed)
    &&& v.table as nat == bytes::le32(v.source, 4104) && v.table < v.blocks
    &&& layout::admitted(journal_inode(v), v.inodes, v.blocks, v.seed)
    &&& v.layout.start > 1 && 1024 <= v.layout.journal_blocks <= 32768
    &&& v.layout.start as nat + v.layout.journal_blocks <= v.blocks && v.layout.fs_blocks == v.blocks
    &&& v.layout.start as nat == bytes::le32(journal_inode(v), 60)
    &&& v.layout.journal_blocks as nat == bytes::le32(journal_inode(v), 4) / 4096
}

pub struct Bootstrap<'s, 'a> {
    source: &'s Snapshot<'a>, layout: JournalLayout, table: u32,
    blocks: u32, inodes: u32, ipg: u32, seed: u32,
}

impl<'s, 'a> Bootstrap<'s, 'a> {
    pub closed spec fn view(&self) -> BootstrapView {
        BootstrapView { source: self.source.view(), layout: self.layout.view(), table: self.table,
            blocks: self.blocks, inodes: self.inodes, ipg: self.ipg, seed: self.seed }
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
    let seed = crc::crc32c(0xffffffff, primary.range(1128, 16).unwrap());
    let descriptor = match source.block(1) { Some(block) => block, None => { return None; } };
    let desc = descriptor.range(0, 32).unwrap();
    let group = match group::parse(desc, 0, blocks, ipg, seed) { Some(group) => group, None => { return None; } };
    let table = group.inode_table;
    let itable = match source.block(table) { Some(block) => block, None => { return None; } };
    let journal = itable.range(1792, 256).unwrap();
    let layout = match layout::from_inode(journal, inodes, blocks, seed) { Some(layout) => layout, None => { return None; } };
    assert(blocks as nat * 4096 <= source.view().len()) by { reveal(superblock::accepted); }
    assert(table < blocks) by { reveal(group::accepted); }
    let ghost assembled = BootstrapView { source: source.view(), layout: layout.view(), table, blocks, inodes, ipg, seed };
    assert(valid(assembled)) by { reveal(valid); }
    Some(Bootstrap { source, layout, table, blocks, inodes, ipg, seed })
}

}
