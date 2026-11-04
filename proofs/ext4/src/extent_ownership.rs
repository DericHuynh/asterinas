// SPDX-License-Identifier: MPL-2.0

//! Relate complete-tree mappings to the actual source-derived ownership
//! claims. Byte provenance and the no-alias census remain separate premises;
//! a checksum is never treated as inode or physical-block identity.

use vstd::prelude::*;
use crate::{block_claims::Claim, bytes, extent_claims::{self, Owner}, extent_node::{self, NodeView},
    extent_span::{self, SpanView}, extent_tree::{self, Context}, extent_tree_model};

verus! {

pub open spec fn span_claim(span: SpanView, owner: Owner) -> Claim {
    Claim { start: span.physical as u32, length: span.length, kind: owner.kind,
        inode: owner.number, generation: owner.generation, logical: span.logical, initialized: span.initialized }
}

proof fn concatenation_keeps_membership(a: Seq<Claim>, b: Seq<Claim>, claim: Claim)
    requires a.contains(claim) || b.contains(claim),
    ensures (a + b).contains(claim),
{
    if a.contains(claim) {
        let i = choose|i: int| 0 <= i < a.len() && a[i] == claim;
        assert((a + b)[i] == claim);
    } else {
        let i = choose|i: int| 0 <= i < b.len() && b[i] == claim;
        assert((a + b)[a.len() as int + i] == claim);
    }
}

proof fn leaf_prefix_includes_entry(raw: Seq<u8>, count: nat, owner: Owner, index: int)
    requires 0 <= index < count,
    ensures extent_claims::leaf_claims(raw, count, owner).contains(extent_claims::leaf_claim(raw, index, owner)),
    decreases count,
{
    let claim = extent_claims::leaf_claim(raw, index, owner);
    let prefix = extent_claims::leaf_claims(raw, (count - 1) as nat, owner);
    reveal(extent_claims::leaf_claims);
    let all = extent_claims::leaf_claims(raw, count, owner);
    if index < count - 1 {
        leaf_prefix_includes_entry(raw, (count - 1) as nat, owner, index);
        let i = choose|i: int| 0 <= i < prefix.len() && prefix[i] == claim;
        assert(all[i] == claim);
    } else {
        assert(all[prefix.len() as int] == claim);
    }
}

proof fn child_prefix_includes_claim(c: Context, node: NodeView, count: nat, depth: u16, owner: Owner, index: int, claim: Claim)
    requires 0 <= index < count, {
        let number = extent_node::child(node.raw, index) as u64;
        extent_claims::node_claims(c, extent_tree::external_node(c, number), Some(number), depth, owner).contains(claim)
    },
    ensures extent_claims::children_claims(c, node, count, depth, owner).contains(claim),
    decreases count,
{
    if index < count - 1 { child_prefix_includes_claim(c, node, (count - 1) as nat, depth, owner, index, claim); }
    let number = extent_node::child(node.raw, count as int - 1) as u64;
    let prefix = extent_claims::children_claims(c, node, (count - 1) as nat, depth, owner);
    let suffix = extent_claims::node_claims(c, extent_tree::external_node(c, number), Some(number), depth, owner);
    concatenation_keeps_membership(prefix, suffix, claim);
    reveal(extent_claims::children_claims);
}

pub proof fn a_stored_mapping_has_its_source_bound_claim(c: Context, node: NodeView, address: Option<u64>, depth: u16, first: Option<u32>, upper: u64, owner: Owner, logical: u32, span: SpanView)
    requires extent_tree::subtree_valid(c, node, address, depth, first, upper),
        extent_tree_model::stored_mapping(c, node, depth, logical, span),
    ensures extent_claims::node_claims(c, node, address, depth, owner).contains(span_claim(span, owner)),
    decreases depth,
{
    let own = match address { Some(number) => seq![extent_claims::metadata_claim(number, owner)], None => Seq::empty() };
    if depth == 0 {
        let index = choose|i: int| 0 <= i < bytes::le16(node.raw, 2) && #[trigger] extent_node::covers(node, i, logical)
            && extent_span::represents(span, node.raw, extent_node::offset(i));
        assert(span_claim(span, owner) == extent_claims::leaf_claim(node.raw, index, owner));
        leaf_prefix_includes_entry(node.raw, bytes::le16(node.raw, 2), owner, index);
        concatenation_keeps_membership(own, extent_claims::leaf_claims(node.raw, bytes::le16(node.raw, 2), owner), span_claim(span, owner));
    } else {
        extent_tree_model::stored_mapping_has_child(c, node, depth, logical, span);
        let index = choose|i: int| 0 <= i < bytes::le16(node.raw, 2) && #[trigger] extent_tree_model::stored_mapping(c,
            extent_tree::external_node(c, extent_node::child(node.raw, i) as u64), (depth - 1) as u16, logical, span);
        let link = extent_node::branch_link(node, index as usize, upper);
        extent_tree::complete_tree_includes_each_child(c, node, address, depth, first, upper, index as usize);
        a_stored_mapping_has_its_source_bound_claim(c, extent_tree::external_node(c, link.number), Some(link.number), (depth - 1) as u16, Some(link.first), link.upper, owner, logical, span);
        child_prefix_includes_claim(c, node, bytes::le16(node.raw, 2), (depth - 1) as u16, owner, index, span_claim(span, owner));
        concatenation_keeps_membership(own, extent_claims::children_claims(c, node, bytes::le16(node.raw, 2), (depth - 1) as u16, owner), span_claim(span, owner));
    }
    reveal(extent_claims::node_claims);
}

}
