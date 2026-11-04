// SPDX-License-Identifier: MPL-2.0

//! Structural reads from a checked immutable host image. All extent-tree
//! mappings inherit complete source-bound allocation claims. Holes and
//! unwritten extents return zeros. VFS/credential and OSTD refinement is separate.

use vstd::prelude::*;
use crate::{allocated_inode::{self, AllocatedInode, NodeView}, allocation, block_claims, bytes,
    extent, extent_claims, extent_ownership, extent_span::{self, SpanView}, extent_tree::{self, Mapping},
    extent_tree_model, group_index, inode_group, inode_size};

verus! {

pub open spec fn logical_covers(c: block_claims::Claim, logical: u32) -> bool {
    c.logical <= logical < c.logical as nat + c.length
}

pub open spec fn maps(v: NodeView, logical: u32, physical: u32) -> bool {
    let c = extent_claims::context(v.volume.index, v.number);
    exists|span: SpanView| #[trigger] extent_tree_model::stored_mapping(c, extent_tree::root_node(c),
        extent_claims::depth(v.volume.index, v.number), logical, span)
        && span.initialized && extent_span::mapping(span, logical) == Some(physical as u64)
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
    reveal(extent_claims::accepted);
    reveal(block_claims::mapped_claims);
    let c = extent_claims::context(v.volume.index, v.number);
    let d = extent_claims::depth(v.volume.index, v.number);
    let owner = extent_claims::owner(v.volume.index, v.number);
    let claims = extent_claims::claims(v.volume.index, v.number);
    let span = choose|span: SpanView| #[trigger] extent_tree_model::stored_mapping(c, extent_tree::root_node(c), d, logical, span)
        && span.initialized && extent_span::mapping(span, logical) == Some(physical as u64);
    extent_tree_model::every_stored_mapping_respects_the_subtree_interval(c, extent_tree::root_node(c), None, d, None, extent::MAX_LOGICAL_END, logical, span);
    extent_ownership::a_stored_mapping_has_its_source_bound_claim(c, extent_tree::root_node(c), None, d, None, extent::MAX_LOGICAL_END, owner, logical, span);
    let claim = extent_ownership::span_claim(span, owner);
    let i = choose|i: int| 0 <= i < claims.len() && claims[i] == claim;
    assert(block_claims::valid_claim(claims[i], v.volume.census.roles.len()));
    assert(span.physical < v.volume.index.blocks);
    assert(block_claims::covers(claims[i], physical as int));
    assert(v.volume.census.roles[physical as int] == block_claims::at(claims[i], physical as int));
    reveal(allocation::valid);
}

pub proof fn initialized_mapping_is_unique(v: NodeView, logical: u32, a: u32, b: u32)
    requires allocated_inode::valid(v), maps(v, logical, a), maps(v, logical, b),
    ensures a == b,
{
    reveal(allocated_inode::valid);
    reveal(inode_group::ordinary_checked);
    reveal(extent_claims::accepted);
    let c = extent_claims::context(v.volume.index, v.number);
    let d = extent_claims::depth(v.volume.index, v.number);
    let x = choose|span: SpanView| #[trigger] extent_tree_model::stored_mapping(c, extent_tree::root_node(c), d, logical, span)
        && span.initialized && extent_span::mapping(span, logical) == Some(a as u64);
    let y = choose|span: SpanView| #[trigger] extent_tree_model::stored_mapping(c, extent_tree::root_node(c), d, logical, span)
        && span.initialized && extent_span::mapping(span, logical) == Some(b as u64);
    extent_tree_model::complete_tree_has_unique_covering_extent(c, extent_tree::root_node(c), None, d, None, extent::MAX_LOGICAL_END, logical, x, y);
}

pub enum Resolution { Zero, Data(u32) }

pub fn resolve(node: &AllocatedInode<'_, '_>, logical: u32) -> (r: Resolution)
    ensures node.wf(), match r {
        Resolution::Data(physical) => maps(node.view(), logical, physical) && owned(node.view(), logical, physical),
        Resolution::Zero => !exists|physical: u32| #[trigger] maps(node.view(), logical, physical),
    },
{
    let path = match extent_tree::lookup_allocated(node, logical) {
        Some(path) => path, None => { return Resolution::Zero; },
    };
    match path.resolved() {
        Mapping::Written(block) => {
            proof {
                reveal(allocated_inode::valid); reveal(inode_group::ordinary_checked); reveal(extent_claims::accepted);
                let span = path.result()->Some_0;
                assert(span.initialized && extent_span::mapping(span, logical) == Some(block));
                extent_tree_model::every_stored_mapping_respects_the_subtree_interval(path.source(), extent_tree::root_node(path.source()), None,
                    extent_claims::depth(node.view().volume.index, node.view().number), None, extent::MAX_LOGICAL_END, logical, span);
                assert(block < span.blocks <= 1048576) by { reveal(group_index::valid); }
            }
            let physical = block as u32;
            assert(maps(node.view(), logical, physical)) by {
                let span = path.result()->Some_0;
                assert(exists|s: SpanView| #[trigger] extent_tree_model::stored_mapping(path.source(), extent_tree::root_node(path.source()),
                    extent_claims::depth(node.view().volume.index, node.view().number), logical, s)
                    && s.initialized && extent_span::mapping(s, logical) == Some(physical as u64));
            }
            proof { an_initialized_mapping_has_exact_ownership(node.view(), logical, physical); }
            Resolution::Data(physical)
        },
        _ => {
            assert(!exists|physical: u32| #[trigger] maps(node.view(), logical, physical)) by {
                if exists|physical: u32| #[trigger] maps(node.view(), logical, physical) {
                    let p = choose|physical: u32| #[trigger] maps(node.view(), logical, physical);
                    let c = path.source();
                    let d = extent_claims::depth(node.view().volume.index, node.view().number);
                    let span = choose|span: SpanView| #[trigger] extent_tree_model::stored_mapping(c, extent_tree::root_node(c), d, logical, span)
                        && span.initialized && extent_span::mapping(span, logical) == Some(p as u64);
                    assert(path.result() == Some(span));
                }
            }
            Resolution::Zero
        },
    }
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
    proof { inode_size::offsets_never_truncate_to_a_different_logical_block(4096, false, info.size, offset); }
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
