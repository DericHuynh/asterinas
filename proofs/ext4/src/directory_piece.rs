// SPDX-License-Identifier: MPL-2.0

//! Canonical namespace records for a source-selected linear or indexed block.
//! HTree roots contribute dot entries; internal routing nodes contribute none.
//! Complete reachability and hash ranges are checked by the directory layer.

use vstd::prelude::*;
use crate::{bytes, directory::Entry, directory_block::{self, BlockView}, htree};

verus! {

pub open spec fn root_records(raw: Seq<u8>) -> Seq<Entry> {
    seq![Entry { inode: bytes::le32(raw, 0) as u32, next: 12, name_offset: 8, name_length: 1, file_type: 2 },
        Entry { inode: bytes::le32(raw, 12) as u32, next: 4096, name_offset: 20, name_length: 2, file_type: 2 }]
}
pub open spec fn canonical_records(raw: Seq<u8>, inodes: u32, indexed: bool, logical: u32) -> Seq<Entry> {
    if indexed && logical == 0 { root_records(raw) }
    else if indexed && htree::node_header(raw) { Seq::empty() }
    else { directory_block::canonical_records(raw, inodes) }
}
pub struct PieceView { pub block: BlockView, pub indexed: bool, pub logical: u32, pub blocks: u32, pub large: bool }
#[verifier::opaque]
pub open spec fn valid(v: PieceView) -> bool {
    let b = v.block;
    &&& b.raw.len() == 4096 && v.logical < v.blocks
    &&& b.records == canonical_records(b.raw, b.inodes, v.indexed, v.logical)
    &&& if v.indexed && v.logical == 0 {
        htree::root_header(b.raw, b.inodes, v.large)
            && htree::valid(htree::IndexView { raw: b.raw, first: 32, blocks: v.blocks, seed: b.seed, checksummed: true })
    } else if v.indexed && htree::node_header(b.raw) {
        htree::valid(htree::IndexView { raw: b.raw, first: 8, blocks: v.blocks, seed: b.seed, checksummed: true })
    } else { directory_block::valid(b) }
}
pub open spec fn name_bounds(raw: Seq<u8>, e: Entry) -> bool {
    raw.len() == 4096 && e.name_length <= 255 && e.name_offset as nat + e.name_length as nat <= 4096
}

pub struct Piece<'a> { raw: &'a [u8], records: Vec<Entry>, inodes: u32, seed: u32, indexed: bool, logical: u32, blocks: u32, large: bool }
impl<'a> Piece<'a> {
    pub closed spec fn view(&self) -> PieceView { PieceView { block: BlockView { raw: self.raw@, records: self.records@, inodes: self.inodes, seed: self.seed },
        indexed: self.indexed, logical: self.logical, blocks: self.blocks, large: self.large } }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn len(&self) -> (r: usize) ensures self.wf(), r == self.view().block.records.len(), r <= 510 {
        proof { use_type_invariant(self); reveal(valid); reveal(directory_block::valid); } self.records.len()
    }
    pub fn get(&self, i: usize) -> (r: Option<&Entry>)
        ensures self.wf(), match r { Some(e) => i < self.view().block.records.len() && *e == self.view().block.records[i as int]
            && name_bounds(self.view().block.raw, *e), None => i >= self.view().block.records.len() },
    {
        proof { use_type_invariant(self); reveal(valid); reveal(directory_block::valid); reveal(directory_block::chain); }
        if i >= self.records.len() { return None; }
        proof {
            if self.indexed && self.logical == 0 {
                if i == 0 { assert(self.records@[i as int] == root_records(self.raw@)[0]); }
                else { assert(i == 1); }
            } else if self.indexed && htree::node_header(self.raw@) { assert(false); }
            else { assert(directory_block::record(self.raw@, self.inodes, self.records@[i as int])); }
        }
        Some(&self.records[i])
    }
    pub fn name(&self, i: usize) -> (r: Option<&'a [u8]>)
        ensures self.wf(), match r { Some(name) => i < self.view().block.records.len() && name.len() <= 255
            && name@ == self.view().block.raw.subrange(self.view().block.records[i as int].name_offset as int,
                self.view().block.records[i as int].name_offset as int + self.view().block.records[i as int].name_length as int),
            None => i >= self.view().block.records.len() },
    {
        let e = match self.get(i) { Some(e) => e, None => { return None; } };
        Some(&self.raw[e.name_offset..e.name_offset + e.name_length as usize])
    }
}

pub fn parse(raw: &[u8], inodes: u32, seed: u32, indexed: bool, logical: u32, blocks: u32, large: bool) -> (r: Option<Piece<'_>>)
    ensures match r { Some(piece) => piece.wf() && piece.view() == (PieceView { block: BlockView { raw: raw@,
        records: canonical_records(raw@, inodes, indexed, logical), inodes, seed }, indexed, logical, blocks, large }), None => true },
{
    if raw.len() != 4096 || logical >= blocks { return None; }
    let mut records = Vec::<Entry>::new();
    if indexed && logical == 0 {
        let root = match htree::parse_root(raw, blocks, inodes, seed, true, large) { Some(root) => root, None => { return None; } };
        let _ = root.routing_index();
        records.push(Entry { inode: bytes::read_le32(raw, 0).unwrap(), next: 12, name_offset: 8, name_length: 1, file_type: 2 });
        records.push(Entry { inode: bytes::read_le32(raw, 12).unwrap(), next: 4096, name_offset: 20, name_length: 2, file_type: 2 });
        assert(records@ =~= root_records(raw@));
    } else if indexed && bytes::read_le32(raw, 0).unwrap() == 0 && bytes::read_le16(raw, 4).unwrap() == 4096 && raw[6] == 0 && raw[7] == 0 {
        let node = match htree::parse_node(raw, blocks, seed, true) { Some(node) => node, None => { return None; } };
        let _ = node.child_count();
        assert(records@ =~= Seq::<Entry>::empty());
    } else {
        assert(!indexed || !htree::node_header(raw@));
        let block = match directory_block::parse(raw, inodes, seed) { Some(block) => block, None => { return None; } };
        proof { directory_block::checked_block_has_canonical_records(block.view()); }
        let count = block.len();
        let mut i = 0usize;
        while i < count
            invariant block.wf(), count == block.view().records.len(), i <= count <= 510, records@ == block.view().records.take(i as int),
            decreases count - i,
        {
            let e = block.get(i).unwrap();
            records.push(Entry { inode: e.inode, next: e.next, name_offset: e.name_offset, name_length: e.name_length, file_type: e.file_type });
            assert(records@ =~= block.view().records.take(i as int + 1));
            i += 1;
        }
        assert(records@ =~= block.view().records);
    }
    assert(valid(PieceView { block: BlockView { raw: raw@, records: records@, inodes, seed }, indexed, logical, blocks, large })) by { reveal(valid); }
    Some(Piece { raw, records, inodes, seed, indexed, logical, blocks, large })
}

}
