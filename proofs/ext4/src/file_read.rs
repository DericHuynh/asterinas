// SPDX-License-Identifier: MPL-2.0

//! Structural reads from a checked immutable host image. Data results are tied
//! to initialized ownership and the file size; holes never read storage. This
//! is not a VFS entry point and does not confer POSIX credential/handle rights.

use vstd::prelude::*;
use crate::{allocated_inode::{self, AllocatedInode, NodeView}, allocation, block_claims, bytes, extent, group_index,
    inode, inode_claims, inode_group, inode_table};

verus! {

pub open spec fn logical_covers(c: block_claims::Claim, logical: u32) -> bool {
    c.logical <= logical < c.logical as nat + c.length
}

pub open spec fn maps(v: NodeView, logical: u32, physical: u32) -> bool {
    let claims = inode_claims::claims(inode_table::raw(v.volume.index, v.number), v.number);
    exists|i: int| 0 <= i < claims.len() && (#[trigger] claims[i]).initialized && logical_covers(claims[i], logical)
        && physical as int == claims[i].start as int + logical as int - claims[i].logical as int
}

pub open spec fn owned(v: NodeView, logical: u32, physical: u32) -> bool {
    &&& physical < v.volume.index.blocks && physical < v.volume.census.roles.len()
    &&& v.volume.census.roles[physical as int].kind == if v.mode & 0xf000 == 0x4000 { 5u8 } else { 4u8 }
    &&& v.volume.census.roles[physical as int].inode == v.number
    &&& v.volume.census.roles[physical as int].generation == v.generation
    &&& v.volume.census.roles[physical as int].logical == logical
    &&& v.volume.census.roles[physical as int].initialized
}

pub proof fn an_initialized_mapping_has_exact_ownership(v: NodeView, logical: u32, physical: u32)
    requires allocated_inode::valid(v), maps(v, logical, physical),
    ensures owned(v, logical, physical),
{
    reveal(allocated_inode::valid);
    reveal(inode_group::ordinary_checked);
    reveal(block_claims::mapped_claims);
    let claims = inode_claims::claims(inode_table::raw(v.volume.index, v.number), v.number);
    let i = choose|i: int| 0 <= i < claims.len() && (#[trigger] claims[i]).initialized && logical_covers(claims[i], logical)
        && physical as int == claims[i].start as int + logical as int - claims[i].logical as int;
    assert(block_claims::valid_claim(claims[i], v.volume.census.roles.len()));
    assert(block_claims::covers(claims[i], physical as int));
    assert(v.volume.census.roles[physical as int] == block_claims::at(claims[i], physical as int));
    reveal(allocation::valid);
}

pub proof fn initialized_mapping_is_unique(v: NodeView, logical: u32, a: u32, b: u32)
    requires allocated_inode::valid(v), maps(v, logical, a), maps(v, logical, b),
    ensures a == b,
{
    reveal(allocated_inode::valid);
    reveal(inode::accepted);
    let raw = inode_table::raw(v.volume.index, v.number);
    let claims = inode_claims::claims(raw, v.number);
    let i = choose|i: int| 0 <= i < claims.len() && (#[trigger] claims[i]).initialized && logical_covers(claims[i], logical)
        && a as int == claims[i].start as int + logical as int - claims[i].logical as int;
    let j = choose|j: int| 0 <= j < claims.len() && (#[trigger] claims[j]).initialized && logical_covers(claims[j], logical)
        && b as int == claims[j].start as int + logical as int - claims[j].logical as int;
    if i < j { extent::disjoint_logical_ranges(raw.subrange(40, 100), claims.len(), v.volume.index.blocks, i, j); }
    if j < i { extent::disjoint_logical_ranges(raw.subrange(40, 100), claims.len(), v.volume.index.blocks, j, i); }
    assert(i == j);
}

pub enum Resolution { Zero, Data(u32) }

proof fn checked_leaf_entry(root: Seq<u8>, count: nat, blocks: u32, index: int)
    requires extent::leaf_entries(root, count, blocks), 0 <= index < count,
    ensures extent::accepted(root, 12 + 12 * index, blocks),
{
    assert(extent::accepted(root, extent::entry_offset(index), blocks));
}

pub fn resolve(node: &AllocatedInode<'_, '_>, logical: u32) -> (r: Resolution)
    ensures node.wf(), match r {
        Resolution::Data(physical) => maps(node.view(), logical, physical) && owned(node.view(), logical, physical),
        Resolution::Zero => !exists|physical: u32| #[trigger] maps(node.view(), logical, physical),
    },
{
    hide(inode::accepted);
    let raw = node.raw();
    let index = node.volume().index();
    let (blocks, _, _, _) = index.parameters();
    let count = bytes::read_le16(raw, 42).unwrap();
    let root = &raw[40..100];
    let ghost claims = inode_claims::claims(raw@, node.view().number);
    assert(count <= 4) by { reveal(allocated_inode::valid); reveal(inode::accepted); }
    assert(extent::leaf_entries(root@, count as nat, blocks)) by { reveal(allocated_inode::valid); reveal(inode::accepted); }
    let mut i = 0usize;
    while i < count as usize
        invariant node.wf(), raw@ == inode_table::raw(node.view().volume.index, node.view().number), raw.len() == 256,
            root@ == raw@.subrange(40, 100), blocks == node.view().volume.index.blocks,
            extent::leaf_entries(root@, count as nat, blocks),
            i <= count <= 4, count as nat == bytes::le16(raw@, 42),
            claims == inode_claims::claims(raw@, node.view().number), claims.len() == count,
            forall|j: int| 0 <= j < i ==> !(#[trigger] claims[j]).initialized || !logical_covers(claims[j], logical),
        decreases count as usize - i,
    {
        proof { checked_leaf_entry(root@, count as nat, blocks, i as int); }
        let e = extent::parse(root, 12 + 12 * i, blocks).unwrap();
        assert(e.logical == claims[i as int].logical && e.physical == claims[i as int].start
            && e.length == claims[i as int].length && e.initialized == claims[i as int].initialized);
        if e.initialized && e.logical <= logical && (logical as u64) < e.logical as u64 + e.length as u64 {
            let physical = e.physical + (logical - e.logical);
            assert(maps(node.view(), logical, physical)) by { assert(claims[i as int].initialized && logical_covers(claims[i as int], logical)); }
            proof { an_initialized_mapping_has_exact_ownership(node.view(), logical, physical); }
            return Resolution::Data(physical);
        }
        i += 1;
    }
    assert(!exists|physical: u32| #[trigger] maps(node.view(), logical, physical));
    Resolution::Zero
}

pub open spec fn chunk_length(v: NodeView, offset: u64, wanted: usize) -> nat {
    if wanted == 0 || offset >= v.size { 0nat }
    else {
        let remaining = (v.size as nat - offset as nat) as nat;
        let boundary = (4096 - offset as nat % 4096) as nat;
        let limit = if remaining < boundary { remaining } else { boundary };
        if (wanted as nat) < limit { wanted as nat } else { limit }
    }
}

pub enum Chunk<'a> { End, Zero(usize), Data(&'a [u8]) }

pub fn chunk<'a>(node: &AllocatedInode<'_, 'a>, offset: u64, wanted: usize) -> (r: Chunk<'a>)
    ensures node.wf(), match r {
        Chunk::End => wanted == 0 || offset >= node.view().size,
        Chunk::Zero(length) => wanted > 0 && offset < node.view().size && 0 < length
            && length as nat == chunk_length(node.view(), offset, wanted) && length <= wanted
            && offset as nat + length <= node.view().size
            && !exists|physical: u32| #[trigger] maps(node.view(), (offset / 4096) as u32, physical),
        Chunk::Data(bytes) => wanted > 0 && offset < node.view().size && bytes.len() > 0
            && bytes.len() == chunk_length(node.view(), offset, wanted) && bytes.len() <= wanted
            && offset as nat + bytes.len() <= node.view().size
            && exists|physical: u32| #[trigger] maps(node.view(), (offset / 4096) as u32, physical)
                && owned(node.view(), (offset / 4096) as u32, physical)
                && bytes@ == node.view().volume.index.source.subrange(physical as int * 4096 + offset as int % 4096,
                    physical as int * 4096 + offset as int % 4096 + bytes.len()),
    },
{
    let info = node.info();
    if wanted == 0 || offset >= info.size as u64 { return Chunk::End; }
    let logical = (offset / 4096) as u32;
    let within = (offset % 4096) as usize;
    let remaining = info.size as u64 - offset;
    let mut length = 4096 - within;
    if remaining < length as u64 { length = remaining as usize; }
    if wanted < length { length = wanted; }
    match resolve(node, logical) {
        Resolution::Zero => Chunk::Zero(length),
        Resolution::Data(physical) => {
            let source = node.volume().index().source();
            assert((physical as nat + 1) * 4096 <= source.view().len()) by {
                reveal(allocated_inode::valid); reveal(allocation::valid); reveal(group_index::valid);
            }
            let block = source.block(physical).unwrap();
            let bytes = block.range(within, length).unwrap();
            Chunk::Data(bytes)
        }
    }
}

}
