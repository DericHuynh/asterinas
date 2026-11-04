// SPDX-License-Identifier: MPL-2.0

//! Source framing for complete extent trees. Changes to data and unrelated
//! metadata cannot change a tree whose root and owned metadata bytes survive.
//! This is a byte/source theorem, not a cache or mapping-epoch capability.

use vstd::prelude::*;
use crate::{block_claims::Claim, bytes, extent_claims::{self, Owner}, extent_node::{self, NodeView},
    extent_span::SpanView, extent_tree::{self, Context}, extent_tree_model};

verus! {

pub open spec fn same_geometry(before: Context, after: Context) -> bool {
    before.root == after.root && before.blocks == after.blocks && before.size == after.size
        && before.checksum == after.checksum && before.source.len() == after.source.len()
}

pub open spec fn metadata_unchanged(before: Context, after: Context, claims: Seq<Claim>) -> bool {
    forall|claim: Claim| #[trigger] claims.contains(claim) && claim.kind == 6 ==>
        after.source.subrange(claim.start as int * before.size as int, (claim.start as int + 1) * before.size as int)
            == before.source.subrange(claim.start as int * before.size as int, (claim.start as int + 1) * before.size as int)
}

proof fn metadata_frame_restricts_to_each_concatenated_part(before: Context, after: Context, left: Seq<Claim>, right: Seq<Claim>)
    requires metadata_unchanged(before, after, left + right),
    ensures metadata_unchanged(before, after, left), metadata_unchanged(before, after, right),
{
    assert forall|claim: Claim| #[trigger] left.contains(claim) && claim.kind == 6 implies
        after.source.subrange(claim.start as int * before.size as int, (claim.start as int + 1) * before.size as int)
            == before.source.subrange(claim.start as int * before.size as int, (claim.start as int + 1) * before.size as int) by {
        let i = choose|i: int| 0 <= i < left.len() && left[i] == claim;
        assert((left + right)[i] == claim);
        assert((left + right).contains(claim));
    }
    assert forall|claim: Claim| #[trigger] right.contains(claim) && claim.kind == 6 implies
        after.source.subrange(claim.start as int * before.size as int, (claim.start as int + 1) * before.size as int)
            == before.source.subrange(claim.start as int * before.size as int, (claim.start as int + 1) * before.size as int) by {
        let i = choose|i: int| 0 <= i < right.len() && right[i] == claim;
        assert((left + right)[left.len() as int + i] == claim);
        assert((left + right).contains(claim));
    }
}

proof fn framed_children(before: Context, after: Context, node: NodeView, count: nat, depth: u16, upper: u64,
    owner: Owner, logical: u32, span: SpanView)
    requires same_geometry(before, after), before.blocks <= 4294967296,
        extent_tree::children_valid(before, node, count, depth, upper), count <= bytes::le16(node.raw, 2),
        metadata_unchanged(before, after, extent_claims::children_claims(before, node, count, depth, owner)),
    ensures extent_tree::children_valid(after, node, count, depth, upper),
        extent_claims::children_claims(before, node, count, depth, owner) == extent_claims::children_claims(after, node, count, depth, owner),
        extent_tree_model::prefix_mapping(before, node, count, depth, logical, span)
            == extent_tree_model::prefix_mapping(after, node, count, depth, logical, span),
    decreases depth, 1nat, count,
{
    reveal(extent_tree::children_valid);
    reveal(extent_claims::children_claims);
    reveal(extent_tree_model::prefix_mapping);
    if count > 0 {
        assert(count <= 65535);
        assert((count - 1) as usize as int == count - 1);
        let link = extent_node::branch_link(node, (count - 1) as usize, upper);
        let child = extent_tree::external_node(before, link.number);
        assert(extent_tree::subtree_valid(before, child, Some(link.number), depth, Some(link.first), link.upper));
        let prefix = extent_claims::children_claims(before, node, (count - 1) as nat, depth, owner);
        let suffix = extent_claims::node_claims(before, child, Some(link.number), depth, owner);
        metadata_frame_restricts_to_each_concatenated_part(before, after, prefix, suffix);
        let own = extent_claims::metadata_claim(link.number, owner);
        assert(suffix.contains(own)) by {
            reveal(extent_claims::node_claims);
            assert(suffix[0] == own);
        }
        assert(extent_tree::node_source(before, child, Some(link.number))) by { reveal(extent_tree::subtree_valid); }
        assert(0 < link.number < before.blocks <= 18446744073709551615);
        assert(link.number == own.start as u64);
        assert(child == extent_tree::external_node(after, link.number));
        framed_subtree(before, after, child, Some(link.number), depth, Some(link.first), link.upper, owner, logical, span);
        framed_children(before, after, node, (count - 1) as nat, depth, upper, owner, logical, span);
    }
}

proof fn framed_subtree(before: Context, after: Context, node: NodeView, address: Option<u64>, depth: u16,
    first: Option<u32>, upper: u64, owner: Owner, logical: u32, span: SpanView)
    requires same_geometry(before, after), before.blocks <= 4294967296,
        extent_tree::subtree_valid(before, node, address, depth, first, upper),
        extent_tree::node_source(after, node, address),
        metadata_unchanged(before, after, extent_claims::node_claims(before, node, address, depth, owner)),
    ensures extent_tree::subtree_valid(after, node, address, depth, first, upper),
        extent_claims::node_claims(before, node, address, depth, owner) == extent_claims::node_claims(after, node, address, depth, owner),
        extent_tree_model::stored_mapping(before, node, depth, logical, span)
            == extent_tree_model::stored_mapping(after, node, depth, logical, span),
    decreases depth, 0nat, 0nat,
{
    reveal(extent_tree::subtree_valid);
    reveal(extent_claims::node_claims);
    reveal(extent_tree_model::stored_mapping);
    let own = match address { Some(number) => seq![extent_claims::metadata_claim(number, owner)], None => Seq::empty() };
    if depth > 0 {
        let children = extent_claims::children_claims(before, node, bytes::le16(node.raw, 2), (depth - 1) as u16, owner);
        metadata_frame_restricts_to_each_concatenated_part(before, after, own, children);
        framed_children(before, after, node, bytes::le16(node.raw, 2), (depth - 1) as u16, upper, owner, logical, span);
    }
}

pub proof fn preserving_the_root_and_owned_metadata_preserves_the_complete_tree(before: Context, after: Context,
    depth: u16, owner: Owner, logical: u32, span: SpanView)
    requires extent_tree::context_valid(before), same_geometry(before, after), before.blocks <= 4294967296,
        extent_tree::subtree_valid(before, extent_tree::root_node(before), None, depth, None, crate::extent::MAX_LOGICAL_END),
        extent_tree::root_node(before) == extent_tree::root_node(after),
        metadata_unchanged(before, after, extent_claims::node_claims(before, extent_tree::root_node(before), None, depth, owner)),
    ensures extent_tree::context_valid(after),
        extent_tree::subtree_valid(after, extent_tree::root_node(after), None, depth, None, crate::extent::MAX_LOGICAL_END),
        extent_claims::node_claims(before, extent_tree::root_node(before), None, depth, owner)
            == extent_claims::node_claims(after, extent_tree::root_node(after), None, depth, owner),
        extent_tree_model::stored_mapping(before, extent_tree::root_node(before), depth, logical, span)
            == extent_tree_model::stored_mapping(after, extent_tree::root_node(after), depth, logical, span),
{
    framed_subtree(before, after, extent_tree::root_node(before), None, depth, None, crate::extent::MAX_LOGICAL_END, owner, logical, span);
}

}
