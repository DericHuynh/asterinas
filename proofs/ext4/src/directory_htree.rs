// SPDX-License-Identifier: MPL-2.0

//! Bind complete HTree validation to initialized, physically owned source
//! mappings and superblock-selected seeds/signedness. This is host admission;
//! OSTD, CortenMM and device authority are separate obligations.

use vstd::prelude::*;
use crate::{allocated_inode::{self, AllocatedInode}, allocation::AllocationView, bytes, dir_hash::State,
    directory_source as source, file_read::{self, Chunk}, htree_names::{self, DirectoryView}, htree_topology};

verus! {

pub const MAX_BLOCKS: u32 = 4096;
pub open spec fn blocks(v: AllocationView, n: u32) -> Seq<Seq<u8>> {
    Seq::new((allocated_inode::source_view(v, n).size / 4096) as nat, |i: int| source::raw(v, n, i as u32))
}
pub open spec fn hash_seed(v: AllocationView) -> State {
    State { a: bytes::le32(v.index.source, 1260) as u32, b: bytes::le32(v.index.source, 1264) as u32,
        c: bytes::le32(v.index.source, 1268) as u32, d: bytes::le32(v.index.source, 1272) as u32 }
}
pub open spec fn unsigned(v: AllocationView) -> bool { bytes::le32(v.index.source, 1376) as u32 & 2 != 0 }
#[verifier::opaque]
pub open spec fn bound(v: AllocationView, n: u32, tree: DirectoryView) -> bool {
    htree_names::valid(tree)
        && tree.graph.context == (htree_topology::Context { source: blocks(v, n), inodes: v.index.inodes, seed: source::seed(v, n), large: source::large(v) })
        && tree.hash_seed == hash_seed(v) && tree.version as nat == blocks(v, n)[0][28] as nat + if unsigned(v) { 3nat } else { 0nat }
        && htree_names::owner(htree_names::parameters(tree)) == n
}
#[verifier::opaque]
pub open spec fn admitted(v: AllocationView, n: u32) -> bool {
    !source::indexed(v, n) || (exists|tree: DirectoryView| #[trigger] bound(v, n, tree))
}

fn read_block<'a>(node: &AllocatedInode<'_, 'a>, logical: u32) -> (r: Option<&'a [u8]>)
    ensures node.wf(), match r { Some(raw) => raw.len() == 4096 && raw@ == source::raw(node.view().volume, node.view().number, logical), None => true },
{
    let raw = match file_read::chunk(node, logical as u64 * 4096, 4096) { Chunk::Data(raw) => raw, _ => { return None; } };
    if raw.len() != 4096 { return None; }
    proof { source::checked_mapping_is_the_canonical_source(node.view(), logical, raw@); }
    Some(raw)
}

fn capture_blocks<'a>(node: &AllocatedInode<'_, 'a>, count: u32) -> (r: Option<Vec<&'a [u8]>>)
    requires 2 <= count <= MAX_BLOCKS, node.view().size / 4096 == count,
    ensures node.wf(), match r { Some(raw) => raw.len() == count && htree_topology::source_views(raw@) == blocks(node.view().volume, node.view().number)
        && (forall|i: int| 0 <= i < raw.len() ==> (#[trigger] raw@[i]).len() == 4096), None => true },
{
    hide(source::raw);
    let volume = node.volume();
    let number = node.number();
    proof { allocated_inode::checked_view_is_the_source_projection(node.view()); }
    let mut raw_blocks: Vec<&[u8]> = Vec::new();
    let mut logical = 0u32;
    while logical < count
        invariant node.wf(), node.view().volume == volume.view(), node.view().number == number,
            node.view() == allocated_inode::source_view(volume.view(), number),
            2 <= count <= MAX_BLOCKS, node.view().size / 4096 == count, logical <= count, raw_blocks.len() == logical,
            forall|i: int| 0 <= i < raw_blocks.len() ==> (#[trigger] raw_blocks@[i]).len() == 4096,
            htree_topology::source_views(raw_blocks@) == blocks(volume.view(), number).take(logical as int),
        decreases count - logical,
    {
        let raw = match read_block(node, logical) { Some(raw) => raw, None => { return None; } };
        assert(blocks(volume.view(), number)[logical as int] == raw@);
        let ghost before = raw_blocks@;
        raw_blocks.push(raw);
        assert forall|j: int| 0 <= j < raw_blocks.len() implies (#[trigger] raw_blocks@[j]).len() == 4096 by {
            if j < before.len() { assert(raw_blocks@[j] == before[j]); }
        }
        assert(htree_topology::source_views(raw_blocks@) =~= blocks(volume.view(), number).take(logical as int + 1));
        logical += 1;
    }
    assert(htree_topology::source_views(raw_blocks@) =~= blocks(volume.view(), number));
    Some(raw_blocks)
}

#[verifier::rlimit(20)]
pub fn validate(node: &AllocatedInode<'_, '_>) -> (r: bool)
    ensures node.wf(), r ==> admitted(node.view().volume, node.view().number),
{
    hide(crate::crc::fold);
    hide(source::raw);
    let volume = node.volume();
    let number = node.number();
    proof { allocated_inode::checked_view_is_the_source_projection(node.view()); }
    if bytes::read_le32(node.raw(), 32).unwrap() & 0x1000 == 0 {
        proof { reveal(admitted); }
        return true;
    }
    let info = node.info();
    if info.mode & 0xf000 != 0x4000 || info.size % 4096 != 0 || info.size / 4096 < 2 || info.size / 4096 > MAX_BLOCKS as u64 { return false; }
    let count = (info.size / 4096) as u32;
    let raw_blocks = match capture_blocks(node, count) { Some(raw) => raw, None => { return false; } };
    let primary = match volume.index().source().block(0) { Some(primary) => primary, None => { return false; } };
    let raw = primary.as_slice();
    let hash_seed = State { a: bytes::read_le32(raw, 1260).unwrap(), b: bytes::read_le32(raw, 1264).unwrap(),
        c: bytes::read_le32(raw, 1268).unwrap(), d: bytes::read_le32(raw, 1272).unwrap() };
    let unsigned = bytes::read_le32(raw, 1376).unwrap() & 2 != 0;
    let large = bytes::read_le32(raw, 1120).unwrap() & 0x4000 != 0;
    let (_, inodes, _, uuid_seed) = volume.index().parameters();
    let seed = crate::inode::inode_seed(uuid_seed, number, info.generation);
    let directory = match htree_names::build(raw_blocks.as_slice(), inodes, seed, hash_seed, unsigned, large) { Some(tree) => tree, None => { return false; } };
    if bytes::read_le32(raw_blocks[0], 0).unwrap() != number { return false; }
    proof {
        assert(bound(volume.view(), number, directory.view())) by { reveal(bound); }
        assert(exists|tree: DirectoryView| #[trigger] bound(volume.view(), number, tree));
        reveal(admitted);
    }
    true
}

pub proof fn a_namespace_indexed_directory_has_a_complete_source_tree(v: crate::namespace::NamespaceView, number: u32)
    requires crate::namespace::valid(v), crate::namespace_model::is_directory(v.index.volume, number), source::indexed(v.index.volume, number),
    ensures exists|tree: DirectoryView| #[trigger] bound(v.index.volume, number, tree),
{
    reveal(crate::namespace::valid); reveal(crate::directory_index::valid); reveal(crate::namespace_model::directories_valid);
    assert(crate::namespace_model::directory_valid(v.index.volume, number));
    reveal(admitted);
}

pub proof fn every_bound_tree_block_has_initialized_physical_source_ownership(v: AllocationView, number: u32, tree: DirectoryView, logical: u32)
    requires crate::allocation::valid(v), allocated_inode::live(v.index, number), bound(v, number, tree), logical < blocks(v, number).len(),
    ensures source::initialized(v, number, logical),
        file_read::maps(allocated_inode::source_view(v, number), logical, source::physical(v, number, logical)),
        file_read::owned(allocated_inode::source_view(v, number), logical, source::physical(v, number, logical)),
        tree.graph.context.source[logical as int] == v.index.source.subrange(source::physical(v, number, logical) as int * 4096,
            (source::physical(v, number, logical) as int + 1) * 4096),
{
    reveal(bound); reveal(htree_names::valid); reveal(htree_topology::valid);
    assert(tree.graph.context.source[logical as int].len() == 4096);
    assert(source::initialized(v, number, logical));
    allocated_inode::a_live_source_projection_is_a_valid_inode(v, number);
    file_read::an_initialized_mapping_has_exact_ownership(allocated_inode::source_view(v, number), logical, source::physical(v, number, logical));
}

pub proof fn the_source_largedir_feature_controls_admitted_index_depth(v: AllocationView, number: u32, tree: DirectoryView)
    requires bound(v, number, tree),
    ensures tree.graph.depth <= if source::large(v) { 2u8 } else { 1u8 },
        tree.graph.context.large == source::large(v),
{
    reveal(bound); reveal(htree_names::valid); reveal(htree_topology::valid);
    htree_topology::a_checked_subtree_retains_its_source_header(tree.graph.context, 0, tree.graph.depth);
    reveal(htree_topology::local);
}

pub proof fn distinct_logical_tree_blocks_have_distinct_physical_ownership(v: AllocationView, number: u32, tree: DirectoryView, a: u32, b: u32)
    requires crate::allocation::valid(v), allocated_inode::live(v.index, number), bound(v, number, tree),
        a < blocks(v, number).len(), b < blocks(v, number).len(), a != b,
    ensures source::physical(v, number, a) != source::physical(v, number, b),
{
    every_bound_tree_block_has_initialized_physical_source_ownership(v, number, tree, a);
    every_bound_tree_block_has_initialized_physical_source_ownership(v, number, tree, b);
}

}
