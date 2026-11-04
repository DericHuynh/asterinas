// SPDX-License-Identifier: MPL-2.0

//! Complete source-bound extent metadata/data claims for the initialized-group
//! profile. Candidate census construction is separate from publication and
//! from the eventual CortenMM, credential and device authority boundaries.

use vstd::prelude::*;
use crate::{allocated_inode, block_claims::{self, Census, Claim}, bytes, crc,
    extent, extent_node::{self, Node, NodeView, BlockChecksum}, extent_span,
    extent_tree::{self, Context, CheckedTree}, group, group_index::{self, GroupIndex, IndexView},
    group_metadata, inode::{self, Inode}, inode_claims, inode_blocks, inode_table, snapshot::Snapshot, source_block};

verus! {

#[derive(Clone, Copy)]
pub struct Owner { pub number: u32, pub generation: u32, pub kind: u8 }

pub open spec fn owner(index: IndexView, number: u32) -> Owner {
    let raw = inode_table::raw(index, number);
    Owner { number, generation: bytes::le32(raw, 100) as u32,
        kind: if bytes::le16(raw, 0) as u16 & 0xf000 == 0x4000 { 5u8 } else { 4u8 } }
}

pub open spec fn context(index: IndexView, number: u32) -> Context {
    Context { source: index.source, root: (inode_table::start(index, number) + 40) as u64,
        blocks: index.blocks as u64, size: 4096,
        checksum: BlockChecksum::Crc32c(crc::fold(crc::fold(index.seed, group::encoded_le(number)),
            group::encoded_le(bytes::le32(inode_table::raw(index, number), 100) as u32))) }
}

pub open spec fn depth(index: IndexView, number: u32) -> u16 { bytes::le16(inode_table::raw(index, number), 46) as u16 }

#[verifier::opaque]
pub open spec fn accepted(index: IndexView, number: u32) -> bool {
    let c = context(index, number);
    let raw = inode_table::raw(index, number);
    &&& group_index::valid(index) && allocated_inode::live(index, number)
    &&& inode::metadata_accepted_with_features(raw, number, index.inodes, index.seed, group_index::has_huge_files(index))
    &&& number == 2 ==> bytes::le16(raw, 0) as u16 & 0xf000 == 0x4000
    &&& extent_tree::context_valid(c)
    &&& extent_tree::subtree_valid(c, extent_tree::root_node(c), None, depth(index, number), None, extent::MAX_LOGICAL_END)
}

/// Structural admission and the exact number of audit visits are separate
/// from global allocation ownership. A repeated child address still consumes
/// another visit; the later census is responsible for rejecting aliases.
pub open spec fn binding_admissible(index: IndexView, number: u32, budget: u64) -> bool {
    let c = context(index, number);
    accepted(index, number) && extent_tree::tree_visits(c, extent_tree::root_node(c), depth(index, number)) <= budget
}

proof fn an_admitted_binding_supplies_the_parser_and_auditor_inputs(index: IndexView, number: u32, budget: u64)
    ensures binding_admissible(index, number, budget) ==> {
        let c = context(index, number);
        &&& allocated_inode::live(index, number)
        &&& inode::metadata_accepted_with_features(inode_table::raw(index, number), number, index.inodes,
            index.seed, group_index::has_huge_files(index))
        &&& (number == 2 ==> bytes::le16(inode_table::raw(index, number), 0) as u16 & 0xf000 == 0x4000)
        &&& extent_tree::context_valid(c)
        &&& bytes::le16(extent_tree::root_node(c).raw, 6) == depth(index, number)
        &&& extent_tree::subtree_valid(c, extent_tree::root_node(c), None, depth(index, number), None, extent::MAX_LOGICAL_END)
        &&& extent_tree::tree_visits(c, extent_tree::root_node(c), depth(index, number)) <= budget
    },
{
    hide(crc::fold);
    hide(extent_tree::children_valid);
    hide(extent_tree::tree_visits);
    if binding_admissible(index, number, budget) {
        reveal(accepted);
        reveal(extent_tree::subtree_valid);
    }
}

pub open spec fn metadata_claim(address: u64, owner: Owner) -> Claim {
    Claim { start: address as u32, length: 1, kind: 6, inode: owner.number, generation: owner.generation, logical: 0, initialized: false }
}

pub open spec fn leaf_claim(raw: Seq<u8>, index: int, owner: Owner) -> Claim {
    let offset = extent_node::offset(index);
    Claim { start: extent_span::physical(raw, offset) as u32,
        length: extent::length(bytes::le16(raw, offset + 4)) as u32, kind: owner.kind,
        inode: owner.number, generation: owner.generation, logical: bytes::le32(raw, offset) as u32,
        initialized: bytes::le16(raw, offset + 4) <= 32768 }
}

pub open spec fn leaf_claims(raw: Seq<u8>, count: nat, owner: Owner) -> Seq<Claim>
    decreases count,
{
    if count == 0 { Seq::empty() } else { leaf_claims(raw, (count - 1) as nat, owner).push(leaf_claim(raw, count as int - 1, owner)) }
}

pub open spec fn node_claims(c: Context, node: NodeView, address: Option<u64>, depth: u16, owner: Owner) -> Seq<Claim>
    decreases depth, 0nat, 0nat,
{
    let own = match address { Some(number) => seq![metadata_claim(number, owner)], None => Seq::empty() };
    own + if depth == 0 { leaf_claims(node.raw, bytes::le16(node.raw, 2), owner) }
        else { children_claims(c, node, bytes::le16(node.raw, 2), (depth - 1) as u16, owner) }
}

pub open spec fn children_claims(c: Context, node: NodeView, count: nat, depth: u16, owner: Owner) -> Seq<Claim>
    decreases depth, 1nat, count,
{
    if count == 0 { Seq::empty() } else {
        let number = extent_node::child(node.raw, count as int - 1) as u64;
        children_claims(c, node, (count - 1) as nat, depth, owner)
            + node_claims(c, extent_tree::external_node(c, number), Some(number), depth, owner)
    }
}

pub open spec fn claims(index: IndexView, number: u32) -> Seq<Claim> {
    let c = context(index, number);
    node_claims(c, extent_tree::root_node(c), None, depth(index, number), owner(index, number))
}

pub proof fn allocated_concatenation(a: Seq<Claim>, b: Seq<Claim>)
    ensures inode_claims::allocated(a + b) == inode_claims::allocated(a) + inode_claims::allocated(b),
    decreases b.len(),
{
    reveal(inode_claims::allocated);
    if b.len() > 0 {
        assert((a + b).drop_last() =~= a + b.drop_last());
        allocated_concatenation(a, b.drop_last());
    } else { assert(a + b =~= a); }
}

proof fn subtree_visits_are_bounded_by_collected_claim_lengths(c: Context, node: NodeView, address: Option<u64>, depth: u16, owner: Owner)
    ensures extent_tree::tree_visits(c, node, depth)
        <= inode_claims::allocated(node_claims(c, node, address, depth, owner)) + if address is None { 1nat } else { 0nat },
    decreases depth, 0nat, 0nat,
{
    hide(crc::fold);
    let own = match address { Some(number) => seq![metadata_claim(number, owner)], None => Seq::empty() };
    assert(inode_claims::allocated(Seq::empty()) == 0) by { reveal(inode_claims::allocated); }
    assert(inode_claims::allocated(own) == if address is None { 0nat } else { 1nat }) by {
        if let Some(number) = address {
            assert(own.drop_last() =~= Seq::<Claim>::empty());
            assert(own.last().length == 1);
        } else { assert(own =~= Seq::<Claim>::empty()); }
        reveal(inode_claims::allocated);
    }
    reveal(node_claims);
    reveal(extent_tree::tree_visits);
    if depth == 0 {
        allocated_concatenation(own, leaf_claims(node.raw, bytes::le16(node.raw, 2), owner));
    } else {
        children_visits_are_bounded_by_collected_claim_lengths(c, node, bytes::le16(node.raw, 2), (depth - 1) as u16, owner);
        allocated_concatenation(own, children_claims(c, node, bytes::le16(node.raw, 2), (depth - 1) as u16, owner));
    }
}

proof fn children_visits_are_bounded_by_collected_claim_lengths(c: Context, node: NodeView, count: nat, depth: u16, owner: Owner)
    ensures extent_tree::prefix_visits(c, node, count, depth) <= inode_claims::allocated(children_claims(c, node, count, depth, owner)),
    decreases depth, 1nat, count,
{
    hide(crc::fold);
    reveal(children_claims);
    reveal(extent_tree::prefix_visits);
    if count > 0 {
        let child = extent_node::child(node.raw, count as int - 1) as u64;
        children_visits_are_bounded_by_collected_claim_lengths(c, node, (count - 1) as nat, depth, owner);
        subtree_visits_are_bounded_by_collected_claim_lengths(c, extent_tree::external_node(c, child), Some(child), depth, owner);
        allocated_concatenation(children_claims(c, node, (count - 1) as nat, depth, owner),
            node_claims(c, extent_tree::external_node(c, child), Some(child), depth, owner));
    } else { reveal(inode_claims::allocated); }
}

/// Every external-node visit contributes a metadata-block claim. Data-block
/// lengths can only increase the budget; the inline root consumes one visit
/// without consuming a separate physical block. Repeated addresses are still
/// charged separately, before the global census rejects any physical alias.
pub proof fn an_inode_audit_visits_at_most_its_claimed_blocks_plus_the_inline_root(index: IndexView, number: u32)
    ensures extent_tree::tree_visits(context(index, number), extent_tree::root_node(context(index, number)), depth(index, number))
        <= inode_claims::allocated(claims(index, number)) + 1,
{
    subtree_visits_are_bounded_by_collected_claim_lengths(context(index, number), extent_tree::root_node(context(index, number)),
        None, depth(index, number), owner(index, number));
}

pub struct BoundInode<'v, 'image> { index: &'v GroupIndex<'image>, number: u32, info: Inode, tree: CheckedTree<'v, 'image> }

impl<'v, 'image> BoundInode<'v, 'image> {
    pub closed spec fn index_view(&self) -> IndexView { self.index.view() }
    pub closed spec fn inode_number(&self) -> u32 { self.number }
    pub open spec fn wf(&self) -> bool { accepted(self.index_view(), self.inode_number()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {
        &&& self.wf() && self.tree.wf() && self.tree.context() == context(self.index_view(), self.inode_number())
        &&& self.info.mode as nat == bytes::le16(inode_table::raw(self.index_view(), self.inode_number()), 0)
        &&& self.info.generation as nat == bytes::le32(inode_table::raw(self.index_view(), self.inode_number()), 100)
        &&& self.info.size as nat == crate::inode_size::value(inode_table::raw(self.index_view(), self.inode_number()), false)
        &&& self.info.links as nat == bytes::le16(inode_table::raw(self.index_view(), self.inode_number()), 26)
        &&& self.info.uid as nat == bytes::le16(inode_table::raw(self.index_view(), self.inode_number()), 2) + 65536 * bytes::le16(inode_table::raw(self.index_view(), self.inode_number()), 120)
        &&& self.info.gid as nat == bytes::le16(inode_table::raw(self.index_view(), self.inode_number()), 24) + 65536 * bytes::le16(inode_table::raw(self.index_view(), self.inode_number()), 122)
    }

    pub fn tree(&self) -> (r: &CheckedTree<'v, 'image>)
        ensures self.wf(), r.wf(), r.context() == context(self.index_view(), self.inode_number()),
    {
        proof { use_type_invariant(self); }
        &self.tree
    }

    pub fn metadata(&self) -> (r: &Inode)
        ensures self.wf(), r.mode as nat == bytes::le16(inode_table::raw(self.index_view(), self.inode_number()), 0),
            r.generation as nat == bytes::le32(inode_table::raw(self.index_view(), self.inode_number()), 100),
            r.size as nat == crate::inode_size::value(inode_table::raw(self.index_view(), self.inode_number()), false),
            r.links as nat == bytes::le16(inode_table::raw(self.index_view(), self.inode_number()), 26),
            r.uid as nat == bytes::le16(inode_table::raw(self.index_view(), self.inode_number()), 2) + 65536 * bytes::le16(inode_table::raw(self.index_view(), self.inode_number()), 120),
            r.gid as nat == bytes::le16(inode_table::raw(self.index_view(), self.inode_number()), 24) + 65536 * bytes::le16(inode_table::raw(self.index_view(), self.inode_number()), 122),
    {
        proof { use_type_invariant(self); }
        &self.info
    }
}

pub fn bind<'v, 'image>(index: &'v GroupIndex<'image>, number: u32, budget: u64) -> (r: Option<BoundInode<'v, 'image>>)
    ensures index.wf(), match r {
        Some(node) => node.wf() && node.index_view() == index.view() && node.inode_number() == number
            && binding_admissible(index.view(), number, budget),
        None => !binding_admissible(index.view(), number, budget),
    },
{
    hide(crc::fold);
    hide(accepted);
    hide(extent_tree::tree_visits);
    hide(extent_tree::subtree_valid);
    proof { an_admitted_binding_supplies_the_parser_and_auditor_inputs(index.view(), number, budget); }
    let (blocks, inodes, ipg, seed) = index.parameters();
    if (number != 2 && number < 11) || number == 0 || number > inodes { return None; }
    proof { reveal(group_index::valid); }
    let group_number = (number - 1) / ipg;
    let slot = (number - 1) % ipg;
    proof {
        vstd::arithmetic::mul::lemma_mul_is_commutative(ipg as int, index.view().groups.len() as int);
        vstd::arithmetic::div_mod::lemma_multiply_divide_lt(number as int - 1, ipg as int, index.view().groups.len() as int);
    }
    let group = index.get(group_number).unwrap();
    let (_, bitmap) = group.bitmaps();
    proof { reveal(group_index::records_match); reveal(group_metadata::valid); }
    if !bitmap.is_set(slot).unwrap() { return None; }
    let raw = inode_table::read(index, number).unwrap();
    let huge_file = index.huge_files();
    let info = match inode::parse_metadata_with_features(raw, number, inodes, seed, huge_file) { Some(info) => info, None => { return None; } };
    if number == 2 && info.mode & 0xf000 != 0x4000 { return None; }
    let root = inode_table::position(index, number).unwrap() + 40;
    let checksum_seed = inode::inode_seed(seed, number, info.generation);
    assert((extent_tree::Context { source: index.view().source, root, blocks: blocks as u64,
        size: 4096, checksum: BlockChecksum::Crc32c(checksum_seed) }) == context(index.view(), number));
    let tree = match extent_tree::audit(index.source(), root, blocks as u64, 4096, BlockChecksum::Crc32c(checksum_seed), budget) {
        Ok(tree) => tree, Err(_) => { return None; },
    };
    proof {
        assert(tree.context() == context(index.view(), number));
        assert(accepted(index.view(), number)) by { reveal(accepted); }
        assert(binding_admissible(index.view(), number, budget));
    }
    Some(BoundInode { index, number, info, tree })
}

/// A checked allocated inode needs no guessed budget and no fallible
/// structural-admission result. Its existing whole-volume ownership
/// certificate proves a sufficient visit budget for this complete audit.
pub fn audit_allocated<'v, 'image>(inode: &allocated_inode::AllocatedInode<'v, 'image>) -> (r: BoundInode<'v, 'image>)
    ensures inode.wf(), r.wf(), r.index_view() == inode.view().volume.index, r.inode_number() == inode.view().number,
{
    let volume = inode.volume();
    let number = inode.number();
    let index = volume.index();
    let (blocks, _, _, _) = index.parameters();
    proof {
        reveal(allocated_inode::valid);
        crate::allocation_budget::every_live_inode_fits_the_volume_sized_audit_budget(volume.view(), number);
    }
    bind(index, number, blocks as u64 + 1).unwrap()
}

struct Parameters { root: u64, blocks: u32, seed: u32, owner: Owner }
impl Parameters {
    spec fn context(&self, source: Seq<u8>) -> Context { Context { source, root: self.root, blocks: self.blocks as u64, size: 4096, checksum: BlockChecksum::Crc32c(self.seed) } }
}

fn collect_node(mut census: Census, source: &Snapshot<'_>, p: &Parameters, node: Node<'_>, address: Option<u64>, depth: u16, first: Option<u32>, upper: u64) -> (r: Option<(Census, u64)>)
    requires census.wf(), census.view().roles.len() == p.blocks, 0 < p.owner.number, p.owner.kind == 4 || p.owner.kind == 5,
        extent_tree::context_valid(p.context(source.view())), node.wf(), depth <= 5,
        extent_tree::subtree_valid(p.context(source.view()), node.view(), address, depth, first, upper),
    ensures match r {
        Some((next, count)) => next.wf() && next.view().roles.len() == census.view().roles.len()
            && block_claims::preserves_occupied(census.view().roles, next.view().roles)
            && next.view().claims == census.view().claims + node_claims(p.context(source.view()), node.view(), address, depth, p.owner)
            && count <= 536870911 && count as nat == inode_claims::allocated(node_claims(p.context(source.view()), node.view(), address, depth, p.owner)),
        None => true,
    },
    decreases depth,
{
    hide(crc::fold);
    let ghost c = p.context(source.view());
    let ghost v = node.view();
    let ghost before = census.view();
    let mut total = 0u64;
    if let Some(number) = address {
        let claim = Claim { start: number as u32, length: 1, kind: 6, inode: p.owner.number,
            generation: p.owner.generation, logical: 0, initialized: false };
        census = match census.claim(claim) { Ok(next) => next, Err(_) => { return None; } };
        total = 1;
    }
    let ghost own = match address { Some(number) => seq![metadata_claim(number, p.owner)], None => Seq::empty() };
    assert(census.view().claims == before.claims + own);
    assert(inode_claims::allocated(Seq::empty()) == 0) by { reveal(inode_claims::allocated); }
    assert(total as nat == inode_claims::allocated(own)) by {
        if let Some(number) = address {
            assert(own.drop_last() =~= Seq::<Claim>::empty());
            assert(own.last().length == 1);
        } else { assert(own =~= Seq::<Claim>::empty()); }
        reveal(inode_claims::allocated);
    }
    proof { if address is None { assert(block_claims::preserves_occupied(before.roles, census.view().roles)) by { reveal(block_claims::preserves_occupied); } } }
    let count = node.header_fields().0;
    proof { reveal(extent_node::valid); }
    if depth == 0 {
        let mut index = 0usize;
        while index < count as usize
            invariant node.wf(), v == node.view(), count as nat == bytes::le16(v.raw, 2), bytes::le16(v.raw, 6) == 0,
                p.context(source.view()) == c, v.blocks == p.blocks, index <= count <= 5460,
                census.wf(), census.view().roles.len() == p.blocks, before.roles.len() == p.blocks,
                census.view().claims == before.claims + own + leaf_claims(v.raw, index as nat, p.owner),
                block_claims::preserves_occupied(before.roles, census.view().roles),
                total <= 536870911, total as nat == inode_claims::allocated(own) + inode_claims::allocated(leaf_claims(v.raw, index as nat, p.owner)),
            decreases count as usize - index,
        {
            let span = node.leaf_extent(index).unwrap();
            let info = span.info();
            let claim = Claim { start: info.physical as u32, length: info.length, kind: p.owner.kind, inode: p.owner.number,
                generation: p.owner.generation, logical: info.logical, initialized: info.initialized };
            assert(claim == leaf_claim(v.raw, index as int, p.owner));
            let ghost prior_roles = census.view().roles;
            census = match census.claim(claim) { Ok(next) => next, Err(_) => { return None; } };
            proof { block_claims::occupied_slot_preservation_is_transitive(before.roles, prior_roles, census.view().roles); }
            total += info.length as u64;
            if total > 536870911 { return None; }
            proof {
                reveal(leaf_claims);
                reveal(inode_claims::allocated);
                assert(leaf_claims(v.raw, index as nat + 1, p.owner).drop_last() =~= leaf_claims(v.raw, index as nat, p.owner));
            }
            index += 1;
        }
        proof { allocated_concatenation(own, leaf_claims(v.raw, count as nat, p.owner)); }
    } else {
        let mut index = 0usize;
        while index < count as usize
            invariant node.wf(), v == node.view(), count as nat == bytes::le16(v.raw, 2), 0 < depth <= 5,
                extent_tree::subtree_valid(c, v, address, depth, first, upper), p.context(source.view()) == c,
                extent_tree::context_valid(c), v.blocks == p.blocks, index <= count <= 5460,
                0 < p.owner.number, p.owner.kind == 4 || p.owner.kind == 5,
                census.wf(), census.view().roles.len() == p.blocks, before.roles.len() == p.blocks,
                census.view().claims == before.claims + own + children_claims(c, v, index as nat, (depth - 1) as u16, p.owner),
                block_claims::preserves_occupied(before.roles, census.view().roles),
                total <= 536870911, total as nat == inode_claims::allocated(own)
                    + inode_claims::allocated(children_claims(c, v, index as nat, (depth - 1) as u16, p.owner)),
            decreases count as usize - index,
        {
            let entry = node.index_entry(index).unwrap();
            let high = if index + 1 < count as usize { node.key_at(index + 1).unwrap() as u64 } else { upper };
            proof {
                extent_tree::complete_tree_includes_each_child(c, v, address, depth, first, upper, index);
                vstd::arithmetic::mul::lemma_mul_inequality(entry.child as int + 1, p.blocks as int, 4096);
            }
            let block = source_block::capture(source, entry.child, 4096).unwrap();
            let child = block.parse_extent_node(p.blocks as u64, BlockChecksum::Crc32c(p.seed)).unwrap();
            let ghost prior_roles = census.view().roles;
            let (next, consumed) = match collect_node(census, source, p, child, Some(entry.child), depth - 1, Some(entry.logical), high) {
                Some(pair) => pair, None => { return None; },
            };
            census = next;
            proof {
                block_claims::occupied_slot_preservation_is_transitive(before.roles, prior_roles, census.view().roles);
                let child_claims = node_claims(c, extent_tree::external_node(c, entry.child), Some(entry.child), (depth - 1) as u16, p.owner);
                allocated_concatenation(children_claims(c, v, index as nat, (depth - 1) as u16, p.owner), child_claims);
                reveal(children_claims);
            }
            total += consumed;
            if total > 536870911 { return None; }
            index += 1;
        }
        proof { allocated_concatenation(own, children_claims(c, v, count as nat, (depth - 1) as u16, p.owner)); }
    }
    Some((census, total))
}

pub fn collect(census: Census, inode: &BoundInode<'_, '_>) -> (r: Option<Census>)
    ensures inode.wf(), match r {
        Some(next) => next.wf() && next.view().roles.len() == inode.index_view().blocks && next.view().roles.len() == census.view().roles.len()
            && next.view().claims == census.view().claims + claims(inode.index_view(), inode.inode_number())
            && block_claims::preserves_occupied(census.view().roles, next.view().roles)
            && block_claims::mapped_claims(next.view().roles, claims(inode.index_view(), inode.inode_number()))
            && (!group_index::has_huge_files(inode.index_view()) ==> bytes::le16(inode_table::raw(inode.index_view(), inode.inode_number()), 116) == 0)
            && inode_blocks::sectors(inode_table::raw(inode.index_view(), inode.inode_number()), 4096, group_index::has_huge_files(inode.index_view()))
                == 8 * inode_claims::allocated(claims(inode.index_view(), inode.inode_number())),
        None => true,
    },
{
    hide(crc::fold);
    proof { use_type_invariant(inode); reveal(accepted); }
    let (blocks, inodes, _, seed) = inode.index.parameters();
    if census.block_count() != blocks { return None; }
    let raw = inode_table::read(inode.index, inode.number).unwrap();
    let position = inode_table::position(inode.index, inode.number).unwrap();
    proof {
        assert(raw@.subrange(40, 100) =~= inode.index_view().source.subrange(position as int + 40, position as int + 100));
        assert(raw@.subrange(40, 100) == extent_tree::root_node(context(inode.index_view(), inode.number)).raw);
    }
    let root = extent_node::parse_inline_root(&raw[40..100], blocks as u64).unwrap();
    let depth = root.header_fields().2;
    proof { reveal(extent_node::valid); }
    let owner = Owner { number: inode.number, generation: inode.info.generation,
        kind: if inode.info.mode & 0xf000 == 0x4000 { 5u8 } else { 4u8 } };
    let p = Parameters { root: position + 40, blocks, seed: inode::inode_seed(seed, inode.number, owner.generation), owner };
    let (next, total) = match collect_node(census, inode.index.source(), &p, root, None, depth, None, extent::MAX_LOGICAL_END) {
        Some(pair) => pair, None => { return None; },
    };
    let huge_file = inode.index.huge_files();
    let sectors = inode_blocks::decode(raw, 4096, huge_file).unwrap();
    if (!huge_file && bytes::read_le16(raw, 116).unwrap() != 0) || sectors != total * 8 { return None; }
    proof { block_claims::every_appended_claim_has_its_exact_physical_slots(&next, census.view().claims, claims(inode.index_view(), inode.number)); }
    Some(next)
}

}
