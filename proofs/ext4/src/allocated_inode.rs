// SPDX-License-Identifier: MPL-2.0

//! Read-only metadata for an allocated ordinary inode in a checked image.
//! This binds inode identity and physical claims to the retained source. It is
//! structural validation, not a POSIX open handle or a credential capability.

use vstd::prelude::*;
use crate::{allocation::{self, Allocation, AllocationView}, bitmap, bytes, group_index::{self, IndexView},
    inode::{self, Inode}, inode_size, extent_claims, inode_group, inode_table};

verus! {

pub open spec fn live(v: IndexView, n: u32) -> bool {
    &&& (n == 2 || n >= 11) && 0 < n <= v.inodes
    &&& bitmap::set(v.groups[(n as int - 1) / v.ipg as int].inodes.raw, (n as int - 1) % v.ipg as int)
}

pub proof fn every_live_inode_has_source_bound_claims(v: AllocationView, n: u32)
    requires allocation::valid(v), live(v.index, n),
    ensures inode_group::ordinary_checked(v.index, v.census.roles, n),
{
    reveal(allocation::valid);
    reveal(group_index::valid);
    vstd::arithmetic::mul::lemma_mul_is_commutative(v.index.ipg as int, v.index.groups.len() as int);
    vstd::arithmetic::div_mod::lemma_multiply_divide_lt(n as int - 1, v.index.ipg as int, v.index.groups.len() as int);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int - 1, v.index.ipg as int);
    let g = ((n as int - 1) / v.index.ipg as int) as u32;
    let slot = ((n as int - 1) % v.index.ipg as int) as nat;
    assert(g as int == (n as int - 1) / v.index.ipg as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(v.index.ipg as int, g as int);
    assert(inode_group::number(v.index, g, slot) == n);
    reveal(allocation::checked_groups);
    assert(inode_group::checked_prefix(v.index, v.census.roles, g, v.index.ipg as nat));
    reveal(inode_group::checked_prefix);
    assert(inode_group::node_checked(v.index, v.census.roles, g, slot));
    reveal(inode_group::node_checked);
}

pub struct NodeView {
    pub volume: AllocationView, pub number: u32, pub mode: u16, pub uid: u32, pub gid: u32,
    pub size: u64, pub generation: u32, pub links: u16,
}

pub open spec fn source_view(volume: AllocationView, n: u32) -> NodeView {
    let raw = inode_table::raw(volume.index, n);
    NodeView { volume, number: n, mode: bytes::le16(raw, 0) as u16, size: inode_size::value(raw, false) as u64,
        generation: bytes::le32(raw, 100) as u32, links: bytes::le16(raw, 26) as u16,
        uid: (bytes::le16(raw, 2) + 65536 * bytes::le16(raw, 120)) as u32,
        gid: (bytes::le16(raw, 24) + 65536 * bytes::le16(raw, 122)) as u32 }
}

#[verifier::opaque]
pub open spec fn valid(v: NodeView) -> bool {
    let raw = inode_table::raw(v.volume.index, v.number);
    &&& allocation::valid(v.volume) && live(v.volume.index, v.number)
    &&& inode_group::ordinary_checked(v.volume.index, v.volume.census.roles, v.number)
    &&& inode::metadata_accepted(raw, v.number, v.volume.index.inodes, v.volume.index.seed)
    &&& v.mode as nat == bytes::le16(raw, 0) && v.size as nat == inode_size::value(raw, false)
    &&& v.generation as nat == bytes::le32(raw, 100) && v.links as nat == bytes::le16(raw, 26)
    &&& v.uid as nat == bytes::le16(raw, 2) + 65536 * bytes::le16(raw, 120)
    &&& v.gid as nat == bytes::le16(raw, 24) + 65536 * bytes::le16(raw, 122)
}

pub proof fn checked_view_is_the_source_projection(v: NodeView)
    requires valid(v),
    ensures v == source_view(v.volume, v.number),
{
    reveal(valid);
}

pub struct AllocatedInode<'v, 'a> { volume: &'v Allocation<'a>, number: u32, info: Inode }

impl<'v, 'a> AllocatedInode<'v, 'a> {
    pub closed spec fn view(&self) -> NodeView {
        NodeView { volume: self.volume.view(), number: self.number, mode: self.info.mode,
            uid: self.info.uid, gid: self.info.gid, size: self.info.size, generation: self.info.generation, links: self.info.links }
    }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn volume(&self) -> (r: &'v Allocation<'a>) ensures self.wf(), r.view() == self.view().volume {
        proof { use_type_invariant(self); }
        self.volume
    }

    pub fn number(&self) -> (r: u32) ensures self.wf(), r == self.view().number {
        proof { use_type_invariant(self); }
        self.number
    }

    pub fn info(&self) -> (r: &Inode)
        ensures self.wf(), r.mode == self.view().mode, r.uid == self.view().uid, r.gid == self.view().gid,
            r.size == self.view().size, r.size <= inode_size::linux_max(4096, false), r.generation == self.view().generation, r.links == self.view().links,
    {
        proof { use_type_invariant(self); }
        proof { reveal(valid); }
        &self.info
    }

    pub fn raw(&self) -> (r: &'a [u8])
        ensures self.wf(), r.len() == 256, r@ == inode_table::raw(self.view().volume.index, self.view().number),
    {
        proof { use_type_invariant(self); reveal(valid); }
        inode_table::read(self.volume.index(), self.number).unwrap()
    }
}

pub fn get<'v, 'a>(volume: &'v Allocation<'a>, n: u32) -> (r: Option<AllocatedInode<'v, 'a>>)
    ensures volume.wf(), match r {
        Some(node) => node.wf() && node.view().volume == volume.view() && node.view().number == n,
        None => !live(volume.view().index, n),
    },
{
    let index = volume.index();
    let (blocks, inodes, ipg, seed) = index.parameters();
    if (n != 2 && n < 11) || n == 0 || n > inodes { return None; }
    assert(ipg > 0) by { reveal(group_index::valid); }
    let g = (n - 1) / ipg;
    let slot = (n - 1) % ipg;
    assert(g < index.view().groups.len()) by {
        reveal(group_index::valid);
        vstd::arithmetic::mul::lemma_mul_is_commutative(ipg as int, index.view().groups.len() as int);
        vstd::arithmetic::div_mod::lemma_multiply_divide_lt(n as int - 1, ipg as int, index.view().groups.len() as int);
    }
    let group = index.get(g).unwrap();
    let (_, bitmap) = group.bitmaps();
    assert(bitmap.view().valid == ipg) by {
        reveal(group_index::valid); reveal(group_index::records_match); reveal(crate::group_metadata::valid);
    }
    if !bitmap.is_set(slot).unwrap() { return None; }
    proof { every_live_inode_has_source_bound_claims(volume.view(), n); }
    let raw = inode_table::read(index, n).unwrap();
    assert(inode::metadata_accepted(raw@, n, inodes, seed)) by { reveal(inode_group::ordinary_checked); reveal(extent_claims::accepted); }
    let info = inode::parse_metadata(raw, n, inodes, seed).unwrap();
    let ghost assembled = NodeView { volume: volume.view(), number: n, mode: info.mode, uid: info.uid,
        gid: info.gid, size: info.size, generation: info.generation, links: info.links };
    assert(valid(assembled)) by { reveal(valid); }
    Some(AllocatedInode { volume, number: n, info })
}

}
