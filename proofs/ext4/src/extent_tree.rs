// SPDX-License-Identifier: MPL-2.0

//! Source-bound read-only extent-tree paths and complete bounded audits.
//! A path checks only visited nodes; an audit checks every reachable branch.
//! Neither grants allocation, initialized-data, credential or I/O authority.

use vstd::prelude::*;
use crate::{block_size, bytes, extent, extent_node::{self, BlockChecksum, Node, NodeView}, extent_span::{self, ExtentSpan, SpanView}, snapshot::Snapshot, source_block};

verus! {

pub struct Context { pub source: Seq<u8>, pub root: u64, pub blocks: u64, pub size: u32, pub checksum: BlockChecksum }
pub struct Visit { pub address: Option<u64>, pub node: NodeView, pub choice: usize }
pub enum LookupError { Geometry, Corrupt }
pub enum AuditError { Geometry, Corrupt, Budget }
pub enum Mapping { Hole, Written(u64), Unwritten(u64) }

pub open spec fn context_valid(c: Context) -> bool {
    &&& block_size::accepted(c.size as nat) && c.blocks > 0
    &&& c.blocks as nat * c.size <= c.source.len()
    &&& c.root as nat + 60 <= c.blocks as nat * c.size
}

pub open spec fn node_source(c: Context, node: NodeView, address: Option<u64>) -> bool {
    &&& node.blocks == c.blocks
    &&& match address {
        None => node.kind is Inline && node.raw == c.source.subrange(c.root as int, c.root as int + 60),
        Some(number) => 0 < number < c.blocks && node.kind == extent_node::block_kind(c.checksum)
            && node.raw == c.source.subrange(number as int * c.size as int, (number as int + 1) * c.size as int),
    }
}

pub open spec fn root_node(c: Context) -> NodeView {
    NodeView { raw: c.source.subrange(c.root as int, c.root as int + 60), blocks: c.blocks, kind: extent_node::NodeKind::Inline }
}

pub open spec fn external_node(c: Context, number: u64) -> NodeView {
    NodeView { raw: c.source.subrange(number as int * c.size as int, (number as int + 1) * c.size as int),
        blocks: c.blocks, kind: extent_node::block_kind(c.checksum) }
}

pub open spec fn subtree_valid(c: Context, node: NodeView, address: Option<u64>, depth: u16, first: Option<u32>, upper: u64) -> bool
    decreases depth, 0nat, 0nat,
{
    &&& node_source(c, node, address) && extent_node::valid(node)
    &&& extent_node::branch_bounds(node, depth, first, upper)
    &&& if depth == 0 { true } else {
        children_valid(c, node, bytes::le16(node.raw, 2), (depth - 1) as u16, upper)
    }
}

// Finite conjunction in disk order, with a separate rank for child depth.
pub open spec fn children_valid(c: Context, node: NodeView, count: nat, depth: u16, upper: u64) -> bool
    decreases depth, 1nat, count,
{
    if count == 0 { true } else {
        let link = extent_node::branch_link(node, (count - 1) as usize, upper);
        children_valid(c, node, (count - 1) as nat, depth, upper)
            && subtree_valid(c, external_node(c, link.number), Some(link.number), depth, Some(link.first), link.upper)
    }
}

// Visits, including any repeated address. Physical ownership is separate.
pub open spec fn tree_visits(c: Context, node: NodeView, depth: u16) -> nat
    decreases depth, 0nat, 0nat,
{
    1 + if depth == 0 { 0nat } else { prefix_visits(c, node, bytes::le16(node.raw, 2), (depth - 1) as u16) }
}

pub open spec fn prefix_visits(c: Context, node: NodeView, count: nat, depth: u16) -> nat
    decreases depth, 1nat, count,
{
    if count == 0 { 0nat } else {
        prefix_visits(c, node, (count - 1) as nat, depth)
            + tree_visits(c, external_node(c, extent_node::child(node.raw, count as int - 1) as u64), depth)
    }
}

proof fn append_visit_count(c: Context, node: NodeView, count: nat, depth: u16)
    ensures prefix_visits(c, node, count + 1, depth) == prefix_visits(c, node, count, depth)
        + tree_visits(c, external_node(c, extent_node::child(node.raw, count as int) as u64), depth),
{
    reveal(prefix_visits);
}

proof fn visit_prefix_is_monotonic(c: Context, node: NodeView, small: nat, large: nat, depth: u16)
    requires small <= large,
    ensures prefix_visits(c, node, small, depth) <= prefix_visits(c, node, large, depth),
    decreases large - small,
{
    if small < large { visit_prefix_is_monotonic(c, node, small, (large - 1) as nat, depth); }
    reveal(prefix_visits);
}

proof fn checked_children_have_each_child(c: Context, node: NodeView, count: nat, depth: u16, upper: u64, index: usize)
    requires children_valid(c, node, count, depth, upper), index < count,
    ensures {
        let link = extent_node::branch_link(node, index, upper);
        subtree_valid(c, external_node(c, link.number), Some(link.number), depth, Some(link.first), link.upper)
    },
    decreases count,
{
    reveal(children_valid);
    if index < count - 1 { checked_children_have_each_child(c, node, (count - 1) as nat, depth, upper, index); }
}

pub proof fn complete_tree_includes_each_child(c: Context, node: NodeView, address: Option<u64>, depth: u16, first: Option<u32>, upper: u64, index: usize)
    requires subtree_valid(c, node, address, depth, first, upper), depth > 0, index < bytes::le16(node.raw, 2),
    ensures {
        let link = extent_node::branch_link(node, index, upper);
        subtree_valid(c, external_node(c, link.number), Some(link.number), (depth - 1) as u16, Some(link.first), link.upper)
    },
{
    reveal(subtree_valid);
    checked_children_have_each_child(c, node, bytes::le16(node.raw, 2), (depth - 1) as u16, upper, index);
}

proof fn append_checked_child(c: Context, node: NodeView, count: usize, depth: u16, upper: u64)
    requires children_valid(c, node, count as nat, depth, upper), {
        let link = extent_node::branch_link(node, count, upper);
        subtree_valid(c, external_node(c, link.number), Some(link.number), depth, Some(link.first), link.upper)
    },
    ensures children_valid(c, node, count as nat + 1, depth, upper),
{
    reveal(children_valid);
}

pub open spec fn tail(path: Seq<Visit>) -> Seq<Visit> { path.subrange(1, path.len() as int) }

#[verifier::opaque]
pub open spec fn route(c: Context, path: Seq<Visit>, logical: u32, depth: u16, first: Option<u32>, upper: u64) -> bool
    decreases path.len(),
{
    &&& path.len() > 0
    &&& node_source(c, path[0].node, path[0].address) && extent_node::valid(path[0].node)
    &&& extent_node::branch_bounds(path[0].node, depth, first, upper)
    &&& if depth == 0 { path.len() == 1 } else {
        let link = extent_node::branch_link(path[0].node, path[0].choice, upper);
        &&& extent_node::chosen_link(path[0].node, logical, upper, link)
        &&& path.len() > 1 && path[1].address == Some(link.number)
        &&& route(c, tail(path), logical, link.depth, Some(link.first), link.upper)
    }
}

pub open spec fn span_view(span: Option<ExtentSpan>) -> Option<SpanView> {
    match span { Some(value) => Some(value.view()), None => None }
}

pub open spec fn mapping(span: Option<SpanView>, logical: u32) -> Mapping {
    match span {
        None => Mapping::Hole,
        Some(value) => match extent_span::mapping(value, logical) {
            Some(block) => if value.initialized { Mapping::Written(block) } else { Mapping::Unwritten(block) },
            None => Mapping::Hole,
        },
    }
}

pub proof fn successful_route_has_exact_depths_and_sources(c: Context, path: Seq<Visit>, logical: u32, depth: u16, first: Option<u32>, upper: u64)
    requires route(c, path, logical, depth, first, upper),
    ensures path.len() == depth as nat + 1,
        forall|i: int| 0 <= i < path.len() ==> #[trigger] node_source(c, path[i].node, path[i].address)
            && extent_node::valid(path[i].node) && bytes::le16(path[i].node.raw, 6) == depth as int - i,
    decreases path.len(),
{
    reveal(route);
    if depth > 0 {
        let link = extent_node::branch_link(path[0].node, path[0].choice, upper);
        successful_route_has_exact_depths_and_sources(c, tail(path), logical, link.depth, Some(link.first), link.upper);
        assert(link.depth as nat + 1 == depth);
        assert forall|i: int| 0 <= i < path.len() implies #[trigger] node_source(c, path[i].node, path[i].address)
            && extent_node::valid(path[i].node) && bytes::le16(path[i].node.raw, 6) == depth as int - i by {
            if i > 0 {
                assert(path[i] == tail(path)[i - 1]);
                assert(node_source(c, tail(path)[i - 1].node, tail(path)[i - 1].address));
                assert(bytes::le16(tail(path)[i - 1].node.raw, 6) == link.depth as int - (i - 1));
            } else { assert(extent_node::branch_bounds(path[0].node, depth, first, upper)); }
        }
    }
}

pub proof fn successful_route_never_revisits_an_external_block(c: Context, path: Seq<Visit>, logical: u32, depth: u16, first: Option<u32>, upper: u64, i: int, j: int)
    requires route(c, path, logical, depth, first, upper), 0 <= i < j < path.len(), path[i].address is Some,
    ensures path[i].address != path[j].address,
{
    successful_route_has_exact_depths_and_sources(c, path, logical, depth, first, upper);
    assert(node_source(c, path[i].node, path[i].address));
    assert(node_source(c, path[j].node, path[j].address));
}

struct Geometry { root: u64, blocks: u64, size: u32, checksum: BlockChecksum }
impl Geometry {
    spec fn context(&self, source: Seq<u8>) -> Context { Context { source, root: self.root, blocks: self.blocks, size: self.size, checksum: self.checksum } }
}

fn duplicate_checksum(checksum: &BlockChecksum) -> (r: BlockChecksum) ensures r == *checksum {
    match checksum { BlockChecksum::Legacy => BlockChecksum::Legacy, BlockChecksum::Crc32c(seed) => BlockChecksum::Crc32c(*seed) }
}

fn make_geometry(source: &Snapshot<'_>, root: u64, blocks: u64, size: u32, checksum: BlockChecksum) -> (r: Option<Geometry>)
    ensures match r {
        Some(g) => context_valid(g.context(source.view())) && g.context(source.view()) == (Context { source: source.view(), root, blocks, size, checksum }),
        None => !context_valid(Context { source: source.view(), root, blocks, size, checksum }),
    },
{
    if !block_size::valid(size as usize) || blocks == 0 { return None; }
    let length = source.partition_bytes();
    proof { source_block::whole_blocks_fit_exactly_below_the_partition_quotient(length, size, blocks as nat); }
    if blocks > length / size as u64 { return None; }
    let filesystem_bytes = blocks * size as u64;
    if root > filesystem_bytes || filesystem_bytes - root < 60 { return None; }
    Some(Geometry { root, blocks, size, checksum })
}

struct Walk { span: Option<ExtentSpan>, nodes: u16, path: Ghost<Seq<Visit>> }

fn walk(source: &Snapshot<'_>, geometry: &Geometry, node: Node<'_>, address: Option<u64>, logical: u32, depth: u16, first: Option<u32>, upper: u64) -> (r: Result<Walk, LookupError>)
    requires context_valid(geometry.context(source.view())), depth <= 5, node.wf(), node_source(geometry.context(source.view()), node.view(), address),
    ensures match r {
        Ok(w) => route(geometry.context(source.view()), w.path@, logical, depth, first, upper)
            && w.path@.len() == w.nodes && w.nodes == depth as nat + 1
            && w.path@[0].node == node.view() && w.path@[0].address == address
            && extent_node::leaf_result(w.path@.last().node, logical, span_view(w.span)),
        Err(error) => error is Corrupt && !subtree_valid(geometry.context(source.view()), node.view(), address, depth, first, upper),
    },
    decreases depth,
{
    if !node.fits_branch(depth, first, upper) { return Err(LookupError::Corrupt); }
    let ghost complete = subtree_valid(geometry.context(source.view()), node.view(), address, depth, first, upper);
    if depth == 0 {
        let span = node.find_leaf(logical);
        let ghost path = seq![Visit { address, node: node.view(), choice: 0 }];
        assert(route(geometry.context(source.view()), path, logical, depth, first, upper)) by { reveal(route); }
        return Ok(Walk { span, nodes: 1, path: Ghost(path) });
    }
    let link = node.find_child(logical, upper).unwrap();
    proof { if complete { complete_tree_includes_each_child(geometry.context(source.view()), node.view(), address, depth, first, upper, link.index); } }
    proof { vstd::arithmetic::mul::lemma_mul_inequality(link.number as int + 1, geometry.blocks as int, geometry.size as int); }
    let block = source_block::capture(source, link.number, geometry.size).unwrap();
    let child = match block.parse_extent_node(geometry.blocks, duplicate_checksum(&geometry.checksum)) {
        Some(child) => child, None => { assert(!complete); return Err(LookupError::Corrupt); },
    };
    let below = match walk(source, geometry, child, Some(link.number), logical, link.depth, Some(link.first), link.upper) {
        Ok(below) => below, Err(error) => { assert(!complete); return Err(error); },
    };
    let ghost head = Visit { address, node: node.view(), choice: link.index };
    let ghost path = seq![head] + below.path@;
    proof {
        assert(tail(path) =~= below.path@);
        assert(route(geometry.context(source.view()), path, logical, depth, first, upper)) by { reveal(route); }
        assert(path.last() == below.path@.last());
    }
    Ok(Walk { span: below.span, nodes: below.nodes + 1, path: Ghost(path) })
}

pub struct CheckedPath { span: Option<ExtentSpan>, nodes: u16, logical: u32, context: Ghost<Context>, path: Ghost<Seq<Visit>> }

impl CheckedPath {
    pub closed spec fn source(&self) -> Context { self.context@ }
    pub closed spec fn visits(&self) -> Seq<Visit> { self.path@ }
    pub closed spec fn query(&self) -> u32 { self.logical }
    pub closed spec fn result(&self) -> Option<SpanView> { span_view(self.span) }
    pub open spec fn wf(&self) -> bool {
        &&& context_valid(self.source()) && self.query() < extent::MAX_LOGICAL_END
        &&& self.visits().len() > 0 && self.visits()[0].address is None
        &&& route(self.source(), self.visits(), self.query(), bytes::le16(self.visits()[0].node.raw, 6) as u16, None, extent::MAX_LOGICAL_END)
        &&& extent_node::leaf_result(self.visits().last().node, self.query(), self.result())
    }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() && self.nodes == self.path@.len() && 1 <= self.nodes <= 6 }

    pub fn resolved(&self) -> (r: Mapping) ensures self.wf(), r == mapping(self.result(), self.query()) {
        proof { use_type_invariant(self); }
        match &self.span {
            None => Mapping::Hole,
            Some(span) => {
                let info = span.info();
                let block = span.physical_block(self.logical).unwrap();
                if info.initialized { Mapping::Written(block) } else { Mapping::Unwritten(block) }
            },
        }
    }

    pub fn visited_nodes(&self) -> (r: u16) ensures self.wf(), r == self.visits().len(), 1 <= r <= 6 {
        proof { use_type_invariant(self); }
        self.nodes
    }
}

pub fn lookup(source: &Snapshot<'_>, root: u64, blocks: u64, size: u32, checksum: BlockChecksum, logical: u32) -> (r: Result<CheckedPath, LookupError>)
    ensures match r {
        Ok(path) => path.wf() && path.source() == (Context { source: source.view(), root, blocks, size, checksum }) && path.query() == logical,
        Err(LookupError::Geometry) => !context_valid(Context { source: source.view(), root, blocks, size, checksum }) || logical >= extent::MAX_LOGICAL_END,
        Err(LookupError::Corrupt) => {
            let c = Context { source: source.view(), root, blocks, size, checksum };
            !subtree_valid(c, root_node(c), None, bytes::le16(root_node(c).raw, 6) as u16, None, extent::MAX_LOGICAL_END)
        },
    },
{
    if logical as u64 >= extent::MAX_LOGICAL_END { return Err(LookupError::Geometry); }
    let geometry = match make_geometry(source, root, blocks, size, checksum) {
        Some(geometry) => geometry, None => { return Err(LookupError::Geometry); },
    };
    let raw = source.capture_bytes(root, 60).unwrap();
    let node = match extent_node::parse_inline_root(raw.as_slice(), blocks) {
        Some(node) => node, None => { return Err(LookupError::Corrupt); },
    };
    let depth = node.header_fields().2;
    proof { reveal(extent_node::valid); }
    let walked = match walk(source, &geometry, node, None, logical, depth, None, extent::MAX_LOGICAL_END) {
        Ok(walked) => walked, Err(error) => { return Err(error); },
    };
    Ok(CheckedPath { span: walked.span, nodes: walked.nodes, logical, context: Ghost(geometry.context(source.view())), path: walked.path })
}

fn audit_subtree(source: &Snapshot<'_>, geometry: &Geometry, node: Node<'_>, address: Option<u64>, depth: u16, first: Option<u32>, upper: u64, budget: u64) -> (r: Result<u64, AuditError>)
    requires context_valid(geometry.context(source.view())), node.wf(), node_source(geometry.context(source.view()), node.view(), address), depth <= 5,
    ensures match r {
        Ok(count) => 1 <= count <= budget && count as nat == tree_visits(geometry.context(source.view()), node.view(), depth)
            && subtree_valid(geometry.context(source.view()), node.view(), address, depth, first, upper),
        Err(AuditError::Budget) => budget < tree_visits(geometry.context(source.view()), node.view(), depth),
        Err(AuditError::Corrupt) => !subtree_valid(geometry.context(source.view()), node.view(), address, depth, first, upper),
        Err(AuditError::Geometry) => false,
    },
    decreases depth,
{
    if budget == 0 { return Err(AuditError::Budget); }
    if !node.fits_branch(depth, first, upper) { return Err(AuditError::Corrupt); }
    let ghost c = geometry.context(source.view());
    let ghost v = node.view();
    let ghost complete = subtree_valid(c, v, address, depth, first, upper);
    if depth == 0 {
        assert(subtree_valid(c, v, address, depth, first, upper)) by { reveal(subtree_valid); }
        return Ok(1);
    }
    let count = node.header_fields().0;
    proof { reveal(extent_node::valid); }
    let mut index = 0usize;
    let mut used = 1u64;
    assert(children_valid(c, v, 0, (depth - 1) as u16, upper)) by { reveal(children_valid); }
    while index < count as usize
        invariant context_valid(c), c == geometry.context(source.view()), node.wf(), v == node.view(),
            complete == subtree_valid(c, v, address, depth, first, upper),
            node_source(c, v, address), extent_node::branch_bounds(v, depth, first, upper), 0 < depth <= 5,
            count as nat == bytes::le16(v.raw, 2), index <= count <= 5460, 1 <= used <= budget,
            used as nat == 1 + prefix_visits(c, v, index as nat, (depth - 1) as u16),
            children_valid(c, v, index as nat, (depth - 1) as u16, upper),
        decreases count as usize - index,
    {
        if used == budget {
            proof {
                append_visit_count(c, v, index as nat, (depth - 1) as u16);
                visit_prefix_is_monotonic(c, v, index as nat + 1, count as nat, (depth - 1) as u16);
            }
            return Err(AuditError::Budget);
        }
        let entry = node.index_entry(index).unwrap();
        let high = if index + 1 < count as usize { node.key_at(index + 1).unwrap() as u64 } else { upper };
        proof { vstd::arithmetic::mul::lemma_mul_inequality(entry.child as int + 1, geometry.blocks as int, geometry.size as int); }
        let block = source_block::capture(source, entry.child, geometry.size).unwrap();
        proof { if complete { complete_tree_includes_each_child(c, v, address, depth, first, upper, index); } }
        let child = match block.parse_extent_node(geometry.blocks, duplicate_checksum(&geometry.checksum)) {
            Some(child) => child, None => { assert(!complete); return Err(AuditError::Corrupt); },
        };
        let consumed = match audit_subtree(source, geometry, child, Some(entry.child), depth - 1, Some(entry.logical), high, budget - used) {
            Ok(consumed) => consumed, Err(error) => {
                proof {
                    if error is Budget {
                        append_visit_count(c, v, index as nat, (depth - 1) as u16);
                        visit_prefix_is_monotonic(c, v, index as nat + 1, count as nat, (depth - 1) as u16);
                    } else { assert(!complete); }
                }
                return Err(error);
            },
        };
        let ghost checked = extent_node::branch_link(v, index, upper);
        assert(subtree_valid(c, external_node(c, checked.number), Some(checked.number), (depth - 1) as u16, Some(checked.first), checked.upper));
        proof { append_checked_child(c, v, index, (depth - 1) as u16, upper); }
        proof { append_visit_count(c, v, index as nat, (depth - 1) as u16); }
        used += consumed;
        index += 1;
    }
    assert(subtree_valid(c, v, address, depth, first, upper)) by { reveal(subtree_valid); }
    Ok(used)
}

pub struct CheckedTree<'s, 'image> { source: &'s Snapshot<'image>, geometry: Geometry, nodes: u64 }

impl<'s, 'image> CheckedTree<'s, 'image> {
    pub closed spec fn context(&self) -> Context { self.geometry.context(self.source.view()) }
    pub closed spec fn count(&self) -> u64 { self.nodes }
    pub open spec fn maps(&self, logical: u32, span: SpanView) -> bool {
        crate::extent_tree_model::stored_mapping(self.context(), root_node(self.context()), bytes::le16(root_node(self.context()).raw, 6) as u16, logical, span)
    }
    pub open spec fn wf(&self) -> bool {
        context_valid(self.context()) && subtree_valid(self.context(), root_node(self.context()), None,
            bytes::le16(root_node(self.context()).raw, 6) as u16, None, extent::MAX_LOGICAL_END)
            && self.count() as nat == tree_visits(self.context(), root_node(self.context()), bytes::le16(root_node(self.context()).raw, 6) as u16)
    }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() && self.nodes > 0 }

    pub fn checked_nodes(&self) -> (r: u64) ensures self.wf(), r == self.count(), r > 0 {
        proof { use_type_invariant(self); }
        self.nodes
    }

    pub fn find(&self, logical: u32) -> (r: Option<CheckedPath>)
        ensures self.wf(), match r {
            Some(path) => path.wf() && path.source() == self.context() && path.query() == logical
                && forall|span: SpanView| #[trigger] self.maps(logical, span) == (path.result() == Some(span)),
            None => logical >= extent::MAX_LOGICAL_END,
        },
    {
        proof { use_type_invariant(self); }
        if logical as u64 >= extent::MAX_LOGICAL_END { return None; }
        let path = match lookup(self.source, self.geometry.root, self.geometry.blocks, self.geometry.size, duplicate_checksum(&self.geometry.checksum), logical) {
            Ok(path) => path, Err(_) => { assert(false); return None; },
        };
        proof {
            let c = self.context();
            let visits = path.visits();
            let depth = bytes::le16(visits[0].node.raw, 6) as u16;
            successful_route_has_exact_depths_and_sources(c, visits, logical, depth, None, extent::MAX_LOGICAL_END);
            assert(node_source(c, visits[0].node, visits[0].address));
            assert(visits[0].node == root_node(c));
            crate::extent_tree_model::audited_route_equals_complete_tree_mapping(c, visits, logical, depth, None, extent::MAX_LOGICAL_END, path.result());
        }
        Some(path)
    }
}

pub fn audit<'s, 'image>(source: &'s Snapshot<'image>, root: u64, blocks: u64, size: u32, checksum: BlockChecksum, budget: u64) -> (r: Result<CheckedTree<'s, 'image>, AuditError>)
    ensures match r {
        Ok(tree) => tree.wf() && tree.context() == (Context { source: source.view(), root, blocks, size, checksum }) && tree.count() <= budget,
        Err(AuditError::Geometry) => !context_valid(Context { source: source.view(), root, blocks, size, checksum }),
        Err(AuditError::Corrupt) => {
            let c = Context { source: source.view(), root, blocks, size, checksum };
            !subtree_valid(c, root_node(c), None, bytes::le16(root_node(c).raw, 6) as u16, None, extent::MAX_LOGICAL_END)
        },
        Err(AuditError::Budget) => {
            let c = Context { source: source.view(), root, blocks, size, checksum };
            context_valid(c) && budget < tree_visits(c, root_node(c), bytes::le16(root_node(c).raw, 6) as u16)
        },
    },
{
    let geometry = match make_geometry(source, root, blocks, size, checksum) {
        Some(geometry) => geometry, None => { return Err(AuditError::Geometry); },
    };
    if budget == 0 { return Err(AuditError::Budget); }
    let raw = source.capture_bytes(root, 60).unwrap();
    let node = match extent_node::parse_inline_root(raw.as_slice(), blocks) {
        Some(node) => node, None => { return Err(AuditError::Corrupt); },
    };
    let depth = node.header_fields().2;
    proof { reveal(extent_node::valid); }
    let nodes = match audit_subtree(source, &geometry, node, None, depth, None, extent::MAX_LOGICAL_END, budget) {
        Ok(nodes) => nodes, Err(error) => { return Err(error); },
    };
    Ok(CheckedTree { source, geometry, nodes })
}

// Restore lookup from the sealed whole-image certificate. Its allocation
// validator already checked every branch; reads need only a bounded path.
pub fn lookup_allocated(inode: &crate::allocated_inode::AllocatedInode<'_, '_>, logical: u32) -> (r: Option<CheckedPath>)
    ensures inode.wf(), match r {
        Some(path) => path.wf() && path.query() == logical
            && path.source() == crate::extent_claims::context(inode.view().volume.index, inode.view().number)
            && forall|span: SpanView| #[trigger] crate::extent_tree_model::stored_mapping(path.source(), root_node(path.source()),
                crate::extent_claims::depth(inode.view().volume.index, inode.view().number), logical, span) == (path.result() == Some(span)),
        None => logical >= extent::MAX_LOGICAL_END
            && !exists|span: SpanView| #[trigger] crate::extent_tree_model::stored_mapping(crate::extent_claims::context(inode.view().volume.index, inode.view().number),
                root_node(crate::extent_claims::context(inode.view().volume.index, inode.view().number)),
                crate::extent_claims::depth(inode.view().volume.index, inode.view().number), logical, span),
    },
{
    hide(crate::crc::fold);
    let index = inode.volume().index();
    let (blocks, _, _, seed) = index.parameters();
    let number = inode.number();
    let info = inode.info();
    proof {
        reveal(crate::allocated_inode::valid);
        reveal(crate::inode_group::ordinary_checked);
        reveal(crate::extent_claims::accepted);
    }
    let ghost c = crate::extent_claims::context(index.view(), number);
    let ghost depth = crate::extent_claims::depth(index.view(), number);
    if logical as u64 >= extent::MAX_LOGICAL_END {
        assert(!exists|span: SpanView| #[trigger] crate::extent_tree_model::stored_mapping(c, root_node(c), depth, logical, span)) by {
            if exists|span: SpanView| #[trigger] crate::extent_tree_model::stored_mapping(c, root_node(c), depth, logical, span) {
                let span = choose|span: SpanView| #[trigger] crate::extent_tree_model::stored_mapping(c, root_node(c), depth, logical, span);
                crate::extent_tree_model::every_stored_mapping_respects_the_subtree_interval(c, root_node(c), None, depth, None, extent::MAX_LOGICAL_END, logical, span);
            }
        }
        return None;
    }
    let raw = inode.raw();
    let position = crate::inode_table::position(index, number).unwrap();
    proof {
        assert(raw@.subrange(40, 100) =~= index.view().source.subrange(position as int + 40, position as int + 100));
        assert(raw@.subrange(40, 100) == root_node(c).raw);
    }
    let node = extent_node::parse_inline_root(&raw[40..100], blocks as u64).unwrap();
    let expected_depth = node.header_fields().2;
    proof { reveal(extent_node::valid); }
    let geometry = Geometry { root: position + 40, blocks: blocks as u64, size: 4096,
        checksum: BlockChecksum::Crc32c(crate::inode::inode_seed(seed, number, info.generation)) };
    let walked = match walk(index.source(), &geometry, node, None, logical, expected_depth, None, extent::MAX_LOGICAL_END) {
        Ok(walked) => walked, Err(_) => { assert(false); return None; },
    };
    proof { crate::extent_tree_model::audited_route_equals_complete_tree_mapping(c, walked.path@, logical, expected_depth, None, extent::MAX_LOGICAL_END, span_view(walked.span)); }
    Some(CheckedPath { span: walked.span, nodes: walked.nodes, logical, context: Ghost(c), path: walked.path })
}

}
