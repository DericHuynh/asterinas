// SPDX-License-Identifier: MPL-2.0

//! Relate a checked lookup path to the complete tree, independently of the
//! binary search: enumerate all children and all covering leaf records.

use vstd::prelude::*;
use crate::{bytes, extent_node::{self, NodeView}, extent_span::SpanView,
    extent_tree::{self, *}};

verus! {

pub open spec fn stored_mapping(c: Context, node: NodeView, depth: u16, logical: u32, span: SpanView) -> bool
    decreases depth, 0nat, 0nat,
{
    if depth == 0 { extent_node::leaf_result(node, logical, Some(span)) }
    else { prefix_mapping(c, node, bytes::le16(node.raw, 2), (depth - 1) as u16, logical, span) }
}

pub open spec fn prefix_mapping(c: Context, node: NodeView, count: nat, depth: u16, logical: u32, span: SpanView) -> bool
    decreases depth, 1nat, count,
{
    count > 0 && (prefix_mapping(c, node, (count - 1) as nat, depth, logical, span)
        || stored_mapping(c, external_node(c, extent_node::child(node.raw, count as int - 1) as u64), depth, logical, span))
}

proof fn prefix_has_child(c: Context, node: NodeView, count: nat, depth: u16, logical: u32, span: SpanView)
    requires prefix_mapping(c, node, count, depth, logical, span),
    ensures exists|i: int| 0 <= i < count && #[trigger] stored_mapping(c,
        external_node(c, extent_node::child(node.raw, i) as u64), depth, logical, span),
    decreases count,
{
    reveal(prefix_mapping);
    if stored_mapping(c, external_node(c, extent_node::child(node.raw, count as int - 1) as u64), depth, logical, span) {
        assert(exists|i: int| 0 <= i < count && #[trigger] stored_mapping(c,
            external_node(c, extent_node::child(node.raw, i) as u64), depth, logical, span));
    } else {
        prefix_has_child(c, node, (count - 1) as nat, depth, logical, span);
        let i = choose|i: int| 0 <= i < count - 1 && #[trigger] stored_mapping(c,
            external_node(c, extent_node::child(node.raw, i) as u64), depth, logical, span);
        assert(exists|i: int| 0 <= i < count && #[trigger] stored_mapping(c,
            external_node(c, extent_node::child(node.raw, i) as u64), depth, logical, span));
    }
}

proof fn prefix_from_child(c: Context, node: NodeView, count: nat, depth: u16, index: int, logical: u32, span: SpanView)
    requires 0 <= index < count, stored_mapping(c, external_node(c, extent_node::child(node.raw, index) as u64), depth, logical, span),
    ensures prefix_mapping(c, node, count, depth, logical, span),
    decreases count,
{
    if index < count - 1 { prefix_from_child(c, node, (count - 1) as nat, depth, index, logical, span); }
    reveal(prefix_mapping);
}

proof fn valid_node(c: Context, node: NodeView, address: Option<u64>, depth: u16, first: Option<u32>, upper: u64)
    requires subtree_valid(c, node, address, depth, first, upper),
    ensures extent_node::valid(node), extent_tree::node_source(c, node, address), extent_node::branch_bounds(node, depth, first, upper),
{
    reveal(subtree_valid);
}

proof fn at_leaf(c: Context, node: NodeView, logical: u32, span: SpanView)
    ensures stored_mapping(c, node, 0, logical, span) == extent_node::leaf_result(node, logical, Some(span)),
{
    reveal(stored_mapping);
}

pub proof fn stored_mapping_has_child(c: Context, node: NodeView, depth: u16, logical: u32, span: SpanView)
    requires depth > 0, stored_mapping(c, node, depth, logical, span),
    ensures exists|i: int| 0 <= i < bytes::le16(node.raw, 2) && #[trigger] stored_mapping(c,
        external_node(c, extent_node::child(node.raw, i) as u64), (depth - 1) as u16, logical, span),
{
    reveal(stored_mapping);
    prefix_has_child(c, node, bytes::le16(node.raw, 2), (depth - 1) as u16, logical, span);
}

pub proof fn stored_mapping_from_child(c: Context, node: NodeView, depth: u16, index: usize, logical: u32, span: SpanView)
    requires depth > 0, index < bytes::le16(node.raw, 2), stored_mapping(c,
        external_node(c, extent_node::child(node.raw, index as int) as u64), (depth - 1) as u16, logical, span),
    ensures stored_mapping(c, node, depth, logical, span),
{
    prefix_from_child(c, node, bytes::le16(node.raw, 2), (depth - 1) as u16, index as int, logical, span);
    reveal(stored_mapping);
}

pub proof fn every_stored_mapping_respects_the_subtree_interval(c: Context, node: NodeView, address: Option<u64>, depth: u16, first: Option<u32>, upper: u64, logical: u32, span: SpanView)
    requires subtree_valid(c, node, address, depth, first, upper), stored_mapping(c, node, depth, logical, span),
    ensures logical < upper, match first { Some(low) => low <= logical, None => true },
        crate::extent_span::valid(span), span.blocks == c.blocks,
    decreases depth,
{
    valid_node(c, node, address, depth, first, upper);
    if depth == 0 {
        at_leaf(c, node, logical, span);
        let index = choose|i: int| 0 <= i < bytes::le16(node.raw, 2) && #[trigger] extent_node::covers(node, i, logical)
            && crate::extent_span::represents(span, node.raw, extent_node::offset(i));
        extent_node::every_record_respects_branch_bounds(node, depth, first, upper, index);
    } else {
        stored_mapping_has_child(c, node, depth, logical, span);
        let index = choose|i: int| 0 <= i < bytes::le16(node.raw, 2) && #[trigger] stored_mapping(c,
            external_node(c, extent_node::child(node.raw, i as int) as u64), (depth - 1) as u16, logical, span);
        let link = extent_node::branch_link(node, index as usize, upper);
        extent_tree::complete_tree_includes_each_child(c, node, address, depth, first, upper, index as usize);
        extent_node::child_intervals_stay_within_parent(node, depth, first, upper, index as usize);
        every_stored_mapping_respects_the_subtree_interval(c, external_node(c, link.number), Some(link.number), (depth - 1) as u16, Some(link.first), link.upper, logical, span);
    }
}

pub proof fn audited_route_equals_complete_tree_mapping(c: Context, path: Seq<Visit>, logical: u32, depth: u16, first: Option<u32>, upper: u64, result: Option<SpanView>)
    requires path.len() > 0, route(c, path, logical, depth, first, upper),
        subtree_valid(c, path[0].node, path[0].address, depth, first, upper),
        extent_node::leaf_result(path.last().node, logical, result),
    ensures forall|span: SpanView| #[trigger] stored_mapping(c, path[0].node, depth, logical, span) == (result == Some(span)),
    decreases depth,
{
    reveal(route);
    let node = path[0].node;
    valid_node(c, node, path[0].address, depth, first, upper);
    if depth == 0 {
        assert(path.last() == path[0]);
        assert forall|span: SpanView| #[trigger] stored_mapping(c, node, depth, logical, span) == (result == Some(span)) by {
            at_leaf(c, node, logical, span);
            if stored_mapping(c, node, depth, logical, span) {
                extent_node::leaf_result_is_unique(node, logical, result, Some(span));
            }
        }
    } else {
        let selected = extent_node::branch_link(node, path[0].choice, upper);
        extent_tree::complete_tree_includes_each_child(c, node, path[0].address, depth, first, upper, selected.index);
        extent_tree::successful_route_has_exact_depths_and_sources(c, path, logical, depth, first, upper);
        assert(extent_tree::node_source(c, path[1].node, path[1].address));
        assert(tail(path)[0].node == external_node(c, selected.number));
        extent_node::child_intervals_stay_within_parent(node, depth, first, upper, selected.index);
        assert(tail(path).last() == path.last());
        assert(selected.depth == depth - 1);
        audited_route_equals_complete_tree_mapping(c, tail(path), logical, selected.depth, Some(selected.first), selected.upper, result);
        assert forall|span: SpanView| #[trigger] stored_mapping(c, node, depth, logical, span) == (result == Some(span)) by {
            if stored_mapping(c, node, depth, logical, span) {
                stored_mapping_has_child(c, node, depth, logical, span);
                let index = choose|i: int| 0 <= i < bytes::le16(node.raw, 2) && #[trigger] stored_mapping(c,
                    external_node(c, extent_node::child(node.raw, i as int) as u64), (depth - 1) as u16, logical, span);
                let other = extent_node::branch_link(node, index as usize, upper);
                extent_node::child_intervals_stay_within_parent(node, depth, first, upper, index as usize);
                extent_tree::complete_tree_includes_each_child(c, node, path[0].address, depth, first, upper, index as usize);
                every_stored_mapping_respects_the_subtree_interval(c, external_node(c, other.number), Some(other.number), (depth - 1) as u16, Some(other.first), other.upper, logical, span);
                if index < selected.index {
                    assert(index + 1 <= selected.index < bytes::le16(node.raw, 2));
                    if index + 1 < selected.index { extent_node::record_keys_are_strictly_increasing(node, index as int + 1, selected.index as int); }
                    assert(other.upper <= extent_node::key(node.raw, selected.index as int));
                } else if selected.index < index {
                    assert(logical < extent_node::key(node.raw, index as int));
                }
                assert(index == selected.index);
                assert(stored_mapping(c, external_node(c, selected.number), selected.depth, logical, span));
            }
            if result == Some(span) {
                assert(stored_mapping(c, external_node(c, selected.number), selected.depth, logical, span));
                stored_mapping_from_child(c, node, depth, selected.index, logical, span);
            }
        }
    }
}

pub proof fn complete_tree_has_unique_covering_extent(c: Context, node: NodeView, address: Option<u64>, depth: u16, first: Option<u32>, upper: u64, logical: u32, a: SpanView, b: SpanView)
    requires subtree_valid(c, node, address, depth, first, upper),
        stored_mapping(c, node, depth, logical, a), stored_mapping(c, node, depth, logical, b),
    ensures a == b,
    decreases depth,
{
    valid_node(c, node, address, depth, first, upper);
    if depth == 0 {
        at_leaf(c, node, logical, a);
        at_leaf(c, node, logical, b);
        extent_node::leaf_result_is_unique(node, logical, Some(a), Some(b));
    } else {
        stored_mapping_has_child(c, node, depth, logical, a);
        stored_mapping_has_child(c, node, depth, logical, b);
        let i = choose|i: int| 0 <= i < bytes::le16(node.raw, 2) && #[trigger] stored_mapping(c,
            external_node(c, extent_node::child(node.raw, i) as u64), (depth - 1) as u16, logical, a);
        let j = choose|i: int| 0 <= i < bytes::le16(node.raw, 2) && #[trigger] stored_mapping(c,
            external_node(c, extent_node::child(node.raw, i) as u64), (depth - 1) as u16, logical, b);
        let left = extent_node::branch_link(node, i as usize, upper);
        let right = extent_node::branch_link(node, j as usize, upper);
        extent_tree::complete_tree_includes_each_child(c, node, address, depth, first, upper, i as usize);
        extent_tree::complete_tree_includes_each_child(c, node, address, depth, first, upper, j as usize);
        extent_node::child_intervals_stay_within_parent(node, depth, first, upper, i as usize);
        extent_node::child_intervals_stay_within_parent(node, depth, first, upper, j as usize);
        every_stored_mapping_respects_the_subtree_interval(c, external_node(c, left.number), Some(left.number), (depth - 1) as u16, Some(left.first), left.upper, logical, a);
        every_stored_mapping_respects_the_subtree_interval(c, external_node(c, right.number), Some(right.number), (depth - 1) as u16, Some(right.first), right.upper, logical, b);
        if i < j {
            if i + 1 < j { extent_node::record_keys_are_strictly_increasing(node, i + 1, j); }
            assert(left.upper <= right.first);
        } else if j < i {
            if j + 1 < i { extent_node::record_keys_are_strictly_increasing(node, j + 1, i); }
            assert(right.upper <= left.first);
        }
        assert(i == j);
        complete_tree_has_unique_covering_extent(c, external_node(c, left.number), Some(left.number), (depth - 1) as u16, Some(left.first), left.upper, logical, a, b);
    }
}

}
