// SPDX-License-Identifier: MPL-2.0

//! Complete immutable HTree logical-block reachability and role census. Every
//! supplied logical block is reached exactly once as an index or parsed leaf.
//! This is not physical-allocation, hash/leaf-range, namespace or VFS authority.

use vstd::prelude::*;
use crate::{block_claims::{self, Census, CensusView, Claim}, bytes, directory_block::{self, BlockView}, htree::{self, Index, IndexView, Root}};

verus! {

pub const MAX_BLOCKS: usize = 65536;
pub open spec fn source_views(blocks: Seq<&[u8]>) -> Seq<Seq<u8>> { Seq::new(blocks.len(), |i: int| blocks[i]@) }
pub struct Context { pub source: Seq<Seq<u8>>, pub inodes: u32, pub seed: u32, pub large: bool }
pub open spec fn geometry(c: Context) -> bool {
    2 <= c.source.len() <= MAX_BLOCKS && forall|i: int| 0 <= i < c.source.len() ==> (#[trigger] c.source[i]).len() == 4096
}
pub open spec fn capacity(c: Context) -> nat { if c.source.len() < 3 { 3nat } else { c.source.len() } }
pub open spec fn first(number: u32) -> usize { if number == 0 { 32usize } else { 8usize } }
pub open spec fn index_view(c: Context, number: u32) -> IndexView {
    IndexView { raw: c.source[number as int], first: first(number), blocks: c.source.len() as u32, seed: c.seed, checksummed: true }
}
pub open spec fn count(c: Context, number: u32) -> nat { htree::count(index_view(c, number)) }
pub open spec fn child(c: Context, number: u32, i: nat) -> u32 { htree::edge(c.source[number as int], first(number) as nat, i).block }
#[verifier::opaque]
pub open spec fn local(c: Context, number: u32, depth: u8) -> bool {
    &&& number < c.source.len() && depth <= 2 && htree::valid(index_view(c, number))
    &&& if number == 0 { htree::root_header(c.source[0], c.inodes, c.large) && c.source[0][30] == depth }
        else { htree::node_header(c.source[number as int]) }
}
#[verifier::opaque]
pub open spec fn leaf(c: Context, number: u32) -> bool {
    number < c.source.len() && directory_block::valid(BlockView { raw: c.source[number as int],
        records: directory_block::canonical_records(c.source[number as int], c.inodes), inodes: c.inodes, seed: c.seed })
}
#[verifier::opaque]
pub open spec fn checked_prefix(c: Context, number: u32, depth: u8, length: nat) -> bool
    decreases depth, length,
{
    if length == 0 { local(c, number, depth) } else {
        let target = child(c, number, (length - 1) as nat);
        checked_prefix(c, number, depth, (length - 1) as nat) && if depth == 0 { leaf(c, target) }
            else { checked_prefix(c, target, (depth - 1) as u8, count(c, target)) }
    }
}
pub open spec fn subtree(c: Context, number: u32, depth: u8) -> bool { checked_prefix(c, number, depth, count(c, number)) }
pub open spec fn prefix(c: Context, number: u32, depth: u8, length: nat) -> bool { checked_prefix(c, number, depth, length) }

pub open spec fn owned(number: u32, kind: u8) -> Claim {
    Claim { start: number, length: 1, kind, inode: 0, generation: 0, logical: 0, initialized: false }
}
#[verifier::opaque]
pub open spec fn claims(c: Context, number: u32, depth: u8, length: nat) -> Seq<Claim>
    decreases depth, length,
{
    if length == 0 { seq![owned(number, 1)] } else {
        let target = child(c, number, (length - 1) as nat);
        claims(c, number, depth, (length - 1) as nat) + if depth == 0 { seq![owned(target, 3)] }
            else { claims(c, target, (depth - 1) as u8, count(c, target)) }
    }
}

proof fn extend_prefix(c: Context, number: u32, depth: u8, done: nat)
    requires prefix(c, number, depth, done),
        if depth == 0 { leaf(c, child(c, number, done)) } else { subtree(c, child(c, number, done), (depth - 1) as u8) },
    ensures prefix(c, number, depth, done + 1),
{ reveal(checked_prefix); }
proof fn finish_subtree(c: Context, number: u32, depth: u8)
    requires local(c, number, depth), prefix(c, number, depth, count(c, number)),
    ensures subtree(c, number, depth),
{ }

proof fn a_checked_prefix_retains_its_header(c: Context, number: u32, depth: u8, length: nat)
    requires checked_prefix(c, number, depth, length),
    ensures local(c, number, depth),
    decreases length,
{
    reveal(checked_prefix);
    if length > 0 { a_checked_prefix_retains_its_header(c, number, depth, (length - 1) as nat); }
}
proof fn a_checked_prefix_contains_each_child(c: Context, number: u32, depth: u8, length: nat, i: nat)
    requires checked_prefix(c, number, depth, length), i < length,
    ensures if depth == 0 { leaf(c, child(c, number, i)) } else { subtree(c, child(c, number, i), (depth - 1) as u8) },
    decreases length,
{
    reveal(checked_prefix);
    if i < length - 1 { a_checked_prefix_contains_each_child(c, number, depth, (length - 1) as nat, i); }
    else { assert(i == length - 1); }
}
pub proof fn a_checked_node_retains_its_header_and_every_source_child(c: Context, number: u32, depth: u8, i: nat)
    requires subtree(c, number, depth), i < count(c, number),
    ensures local(c, number, depth),
        if depth == 0 { leaf(c, child(c, number, i)) } else { subtree(c, child(c, number, i), (depth - 1) as u8) },
{
    a_checked_prefix_retains_its_header(c, number, depth, count(c, number));
    a_checked_prefix_contains_each_child(c, number, depth, count(c, number), i);
}

pub proof fn a_checked_subtree_retains_its_source_header(c: Context, number: u32, depth: u8)
    requires subtree(c, number, depth),
    ensures local(c, number, depth),
{
    a_checked_prefix_retains_its_header(c, number, depth, count(c, number));
}

fn collect<'a>(blocks: &[&'a [u8]], census: Census, index: &Index<'a>, number: u32, depth: u8,
    inodes: u32, seed: u32, Ghost(c): Ghost<Context>) -> (r: Option<Census>)
    requires geometry(c), c.source == source_views(blocks@), c.inodes == inodes, c.seed == seed,
        local(c, number, depth), index.wf(), index.view() == index_view(c, number), census.wf(), census.view().roles.len() == capacity(c),
    ensures index.wf(), match r { Some(next) => next.wf() && next.view().roles.len() == capacity(c)
        && next.view().claims == census.view().claims + claims(c, number, depth, count(c, number))
        && block_claims::preserves_occupied(census.view().roles, next.view().roles) && subtree(c, number, depth), None => true },
    decreases depth,
{
    let ghost initial = census.view();
    let own = Claim { start: number, length: 1, kind: 1, inode: 0, generation: 0, logical: 0, initialized: false };
    let mut current = match census.claim(own) { Ok(next) => next, Err(_) => { return None; } };
    let count = index.child_count();
    let mut i = 0usize;
    assert(claims(c, number, depth, 0) == seq![owned(number, 1)]) by { reveal(claims); }
    assert(current.view().claims =~= initial.claims + claims(c, number, depth, 0));
    assert(prefix(c, number, depth, 0)) by { reveal(checked_prefix); }
    while i < count
        invariant geometry(c), c.source == source_views(blocks@), c.inodes == inodes, c.seed == seed,
            local(c, number, depth), index.wf(), index.view() == index_view(c, number), i <= count == crate::htree_topology::count(c, number),
            current.wf(), current.view().roles.len() == capacity(c),
            current.view().claims == initial.claims + claims(c, number, depth, i as nat), prefix(c, number, depth, i as nat),
            block_claims::preserves_occupied(initial.roles, current.view().roles),
        decreases count - i,
    {
        let edge = index.child(i).unwrap();
        let target = edge.block;
        assert(target == child(c, number, i as nat));
        let ghost before = current.view();
        if depth == 0 {
            let block = match directory_block::parse(blocks[target as usize], inodes, seed) { Some(block) => block, None => { return None; } };
            proof {
                directory_block::checked_block_has_canonical_records(block.view());
                assert(leaf(c, target)) by { reveal(leaf); assert(directory_block::valid(block.view())); }
            }
            let own = Claim { start: target, length: 1, kind: 3, inode: 0, generation: 0, logical: 0, initialized: false };
            current = match current.claim(own) { Ok(next) => next, Err(_) => { return None; } };
            assert(current.view().claims =~= before.claims + seq![owned(target, 3)]);
        } else {
            let nested = match htree::parse_node(blocks[target as usize], blocks.len() as u32, seed, true) {
                Some(nested) => nested, None => { return None; }
            };
            assert(local(c, target, (depth - 1) as u8)) by { reveal(local); }
            current = match collect(blocks, current, &nested, target, depth - 1, inodes, seed, Ghost(c)) {
                Some(next) => next, None => { return None; }
            };
        }
        proof {
            block_claims::occupied_slot_preservation_is_transitive(initial.roles, before.roles, current.view().roles);
            assert(claims(c, number, depth, i as nat + 1) == claims(c, number, depth, i as nat)
                + if depth == 0 { seq![owned(target, 3)] } else { claims(c, target, (depth - 1) as u8, crate::htree_topology::count(c, target)) }) by { reveal(claims); }
            extend_prefix(c, number, depth, i as nat);
        }
        i += 1;
    }
    proof { finish_subtree(c, number, depth); }
    Some(current)
}

pub struct GraphView { pub context: Context, pub index: IndexView, pub depth: u8, pub census: CensusView }
#[verifier::opaque]
pub open spec fn valid(v: GraphView) -> bool {
    &&& geometry(v.context) && v.index == index_view(v.context, 0) && subtree(v.context, 0, v.depth)
    &&& block_claims::ledger(v.census.roles, v.census.claims) && v.census.roles.len() == capacity(v.context)
    &&& v.census.claims == claims(v.context, 0, v.depth, count(v.context, 0))
    &&& forall|i: int| 0 <= i < v.context.source.len() ==> (#[trigger] v.census.roles[i]).kind == 1 || v.census.roles[i].kind == 3
}
pub struct Graph<'a> { root: Root<'a>, depth: u8, census: Census, context: Ghost<Context>, blocks: u32 }
impl<'a> Graph<'a> {
    pub closed spec fn view(&self) -> GraphView { GraphView { context: self.context@, index: self.root.view(), depth: self.depth, census: self.census.view() } }
    pub closed spec fn stored_blocks(&self) -> u32 { self.blocks }
    pub open spec fn wf(&self) -> bool { valid(self.view()) && self.stored_blocks() == self.view().context.source.len() }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn logical_block_count(&self) -> (r: u32) ensures self.wf(), r == self.view().context.source.len(), 2 <= r <= MAX_BLOCKS {
        proof { use_type_invariant(self); reveal(valid); }
        self.blocks
    }
    pub fn logical_role(&self, number: u32) -> (r: Option<u8>)
        ensures self.wf(), match r { Some(kind) => number < self.view().context.source.len() && kind == self.view().census.roles[number as int].kind
            && (kind == 1 || kind == 3), None => number >= self.view().context.source.len() },
    {
        proof { use_type_invariant(self); reveal(valid); }
        if number >= self.blocks { return None; }
        Some(self.census.role_of(number).unwrap().kind)
    }
    pub fn checked_root(&self) -> (r: &Root<'a>) ensures self.wf(), r.wf(), r.view() == self.view().index {
        let _ = self.root.hash_and_levels();
        proof { use_type_invariant(self); }
        &self.root
    }
}

pub fn parse<'a>(blocks: &[&'a [u8]], inodes: u32, seed: u32, large: bool) -> (r: Option<Graph<'a>>)
    ensures match r { Some(graph) => graph.wf() && graph.view().context == Context { source: source_views(blocks@), inodes, seed, large }, None => true },
{
    if blocks.len() < 2 || blocks.len() > MAX_BLOCKS { return None; }
    let mut i = 0usize;
    while i < blocks.len()
        invariant 2 <= blocks.len() <= MAX_BLOCKS, i <= blocks.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] source_views(blocks@)[j]).len() == 4096,
        decreases blocks.len() - i,
    {
        if blocks[i].len() != 4096 { return None; }
        i += 1;
    }
    let root = match htree::parse_root(blocks[0], blocks.len() as u32, inodes, seed, true, large) { Some(root) => root, None => { return None; } };
    let (_, depth) = root.hash_and_levels();
    let ghost c = Context { source: source_views(blocks@), inodes, seed, large };
    assert(local(c, 0, depth)) by { reveal(local); }
    let slots = if blocks.len() < 3 { 3usize } else { blocks.len() };
    let initial = Census::new(slots as u32).unwrap();
    let census = match collect(blocks, initial, root.routing_index(), 0, depth, inodes, seed, Ghost(c)) { Some(next) => next, None => { return None; } };
    let mut number = 0u32;
    while (number as usize) < blocks.len()
        invariant geometry(c), c == (Context { source: source_views(blocks@), inodes, seed, large }),
            census.wf(), census.view().roles.len() == capacity(c),
            census.view().claims == claims(c, 0, depth, count(c, 0)), subtree(c, 0, depth),
            root.view() == index_view(c, 0), number <= blocks.len(), blocks.len() <= MAX_BLOCKS,
            forall|j: int| 0 <= j < number ==> (#[trigger] census.view().roles[j]).kind == 1 || census.view().roles[j].kind == 3,
        decreases blocks.len() - number,
    {
        let role = census.role_of(number).unwrap();
        if role.kind != 1 && role.kind != 3 { return None; }
        number += 1;
    }
    let ghost view = GraphView { context: c, index: root.view(), depth, census: census.view() };
    assert(valid(view)) by { reveal(valid); }
    Some(Graph { root, depth, census, context: Ghost(c), blocks: blocks.len() as u32 })
}

proof fn nonfree_lookup_has_a_covering_claim(entries: Seq<Claim>, block: int)
    requires block_claims::lookup(entries, block).kind != 0,
    ensures exists|i: int| 0 <= i < entries.len() && #[trigger] block_claims::covers(entries[i], block),
    decreases entries.len(),
{
    reveal(block_claims::lookup);
    if !block_claims::covers(entries.last(), block) {
        nonfree_lookup_has_a_covering_claim(entries.drop_last(), block);
        let i = choose|i: int| 0 <= i < entries.drop_last().len() && #[trigger] block_claims::covers(entries.drop_last()[i], block);
        assert(entries[i] == entries.drop_last()[i]);
    }
}

pub proof fn every_supplied_logical_block_is_reachable_from_the_exact_root(graph: &Graph<'_>, number: u32)
    requires graph.wf(), number < graph.view().context.source.len(),
    ensures exists|i: int| 0 <= i < claims(graph.view().context, 0, graph.view().depth, count(graph.view().context, 0)).len()
        && #[trigger] block_claims::covers(claims(graph.view().context, 0, graph.view().depth, count(graph.view().context, 0))[i], number as int),
{
    reveal(valid); reveal(block_claims::ledger);
    assert(graph.view().census.roles[number as int].kind == 1 || graph.view().census.roles[number as int].kind == 3);
    assert(block_claims::lookup(graph.view().census.claims, number as int) == graph.view().census.roles[number as int]);
    nonfree_lookup_has_a_covering_claim(graph.view().census.claims, number as int);
}

pub proof fn two_tree_claims_cannot_reuse_one_logical_block(graph: &Graph<'_>, a: nat, b: nat, number: u32)
    requires graph.wf(), a < graph.view().census.claims.len(), b < graph.view().census.claims.len(),
        block_claims::covers(graph.view().census.claims[a as int], number as int), block_claims::covers(graph.view().census.claims[b as int], number as int),
    ensures a == b,
{
    let _ = graph;
    reveal(valid);
    block_claims::two_recorded_claims_cannot_own_the_same_physical_block(&graph.census, a, b, number as int);
}

proof fn canonical_claims_are_unit_metadata(c: Context, number: u32, depth: u8, length: nat, i: nat)
    requires i < claims(c, number, depth, length).len(),
    ensures claims(c, number, depth, length)[i as int].length == 1,
        claims(c, number, depth, length)[i as int].kind == 1 || claims(c, number, depth, length)[i as int].kind == 3,
        claims(c, number, depth, length)[i as int] == owned(claims(c, number, depth, length)[i as int].start, claims(c, number, depth, length)[i as int].kind),
    decreases depth, length,
{
    reveal(claims);
    if length > 0 {
        let before = claims(c, number, depth, (length - 1) as nat);
        if i < before.len() { canonical_claims_are_unit_metadata(c, number, depth, (length - 1) as nat, i); }
        else if depth > 0 {
            let target = child(c, number, (length - 1) as nat);
            canonical_claims_are_unit_metadata(c, target, (depth - 1) as u8, count(c, target), (i - before.len()) as nat);
        }
    }
}
proof fn a_source_leaf_claim_has_checked_records(c: Context, number: u32, depth: u8, length: nat, i: nat, logical: u32)
    requires checked_prefix(c, number, depth, length), i < claims(c, number, depth, length).len(), claims(c, number, depth, length)[i as int] == owned(logical, 3),
    ensures leaf(c, logical),
    decreases depth, length,
{
    reveal(claims); reveal(checked_prefix);
    if length > 0 {
        let before = claims(c, number, depth, (length - 1) as nat);
        if i < before.len() { a_source_leaf_claim_has_checked_records(c, number, depth, (length - 1) as nat, i, logical); }
        else if depth > 0 {
            let target = child(c, number, (length - 1) as nat);
            a_source_leaf_claim_has_checked_records(c, target, (depth - 1) as u8, count(c, target), (i - before.len()) as nat, logical);
        }
    }
}

pub proof fn every_leaf_role_has_a_checked_source_leaf_claim(v: GraphView, logical: u32)
    requires valid(v), logical < v.context.source.len(), v.census.roles[logical as int].kind == 3,
    ensures leaf(v.context, logical), exists|i: int| 0 <= i < claims(v.context, 0, v.depth, count(v.context, 0)).len()
        && (#[trigger] claims(v.context, 0, v.depth, count(v.context, 0))[i]) == owned(logical, 3),
{
    reveal(valid); reveal(block_claims::ledger);
    assert(block_claims::lookup(v.census.claims, logical as int) == v.census.roles[logical as int]);
    nonfree_lookup_has_a_covering_claim(v.census.claims, logical as int);
    let i = choose|i: int| 0 <= i < v.census.claims.len() && #[trigger] block_claims::covers(v.census.claims[i], logical as int);
    canonical_claims_are_unit_metadata(v.context, 0, v.depth, count(v.context, 0), i as nat);
    let claim = v.census.claims[i];
    assert(v.census.claims.contains(claim));
    block_claims::a_ledger_claim_determines_its_exact_physical_slot(v.census.roles, v.census.claims, claim, logical as int);
    assert(claim == owned(logical, 3));
    a_source_leaf_claim_has_checked_records(v.context, 0, v.depth, count(v.context, 0), i as nat, logical);
}

}
