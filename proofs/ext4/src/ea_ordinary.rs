// SPDX-License-Identifier: MPL-2.0

//! Complete ordinary-inode allocation and exact parent accounting in the
//! original EA_INODE-enabled source. The result is an immutable candidate,
//! not a namespace, journal, VFS, allocator or device authority.

use vstd::prelude::*;
use crate::{block_claims::{self, Census, Claim, Slot}, bytes, crc,
    ea_billing::{self, Usage}, ea_index::{self, Index, IndexView},
    ea_parent::{self, ParentView}, ea_source::NodeView,
    extent_claims::{self, Owner}, extent_node::BlockChecksum, extent_tree::{self, Context},
    inode, inode_claims};

verus! {

pub open spec fn directory(parent: ParentView) -> bool {
    bytes::le16(parent.node.raw, 0) as u16 & 0xf000 == 0x4000
}
pub open spec fn owner(parent: ParentView) -> Owner {
    Owner { number: parent.node.number, generation: bytes::le32(parent.node.raw, 100) as u32,
        kind: if directory(parent) { 5u8 } else { 4u8 } }
}
pub open spec fn context(node: NodeView) -> Context {
    Context { source: node.header.source, root: (node.position as int + 40) as u64,
        blocks: node.header.blocks as u64, size: 4096,
        checksum: BlockChecksum::Crc32c(crc::fold(crc::fold(node.header.seed,
            crate::group::encoded_le(node.number)), crate::group::encoded_le(bytes::le32(node.raw, 100) as u32))) }
}
pub open spec fn tree_claims(parent: ParentView) -> Seq<Claim> {
    extent_claims::checked_claims(context(parent.node), owner(parent))
}
pub open spec fn labeled(claim: Claim, parent: ParentView) -> bool {
    claim.inode == parent.node.number && claim.generation == bytes::le32(parent.node.raw, 100)
        && (claim.kind == owner(parent).kind || claim.kind == 6)
}
pub open spec fn indexed_feature_allowed(parent: ParentView) -> bool {
    bytes::le32(parent.node.raw, 32) as u32 & 0x1000 == 0
        || bytes::le32(parent.node.header.source, 1116) as u32 & 0x20 != 0
}

pub struct OrdinaryView {
    pub index: IndexView, pub parent: ParentView, pub billing: Usage,
    pub roles: Seq<Slot>, pub claims: Seq<Claim>, pub allocated: u64,
    pub budget: u64, pub visits: u64,
}
#[verifier::opaque]
pub open spec fn valid(v: OrdinaryView) -> bool {
    let c = context(v.parent.node);
    &&& ea_index::valid(v.index) && ea_parent::valid(v.parent)
    &&& v.parent.node.header == v.index.header
    &&& ea_index::inode_allocated(v.index, v.parent.node.number)
    &&& (v.parent.node.number == 2 ==> directory(v.parent))
    &&& indexed_feature_allowed(v.parent)
    &&& ea_billing::checked(v.parent.node.raw, ea_parent::huge(v.index.header), v.parent.node.number,
        ea_parent::logical_projection(v.parent), v.billing)
    &&& 1 <= v.visits <= v.budget <= v.index.header.blocks as nat + 1
    &&& extent_tree::context_valid(c)
    &&& extent_tree::subtree_valid(c, extent_tree::root_node(c), None,
        bytes::le16(extent_tree::root_node(c).raw, 6) as u16, None, crate::extent::MAX_LOGICAL_END)
    &&& v.visits == extent_tree::tree_visits(c, extent_tree::root_node(c), bytes::le16(extent_tree::root_node(c).raw, 6) as u16)
    &&& v.claims == tree_claims(v.parent) && v.roles.len() == v.index.header.blocks
    &&& block_claims::mapped_claims(v.roles, v.claims)
    &&& (forall|i: int, j: int| 0 <= i < j < v.claims.len() ==> #[trigger] block_claims::disjoint(v.claims[i], v.claims[j]))
    &&& (forall|i: int| 0 <= i < v.claims.len() ==> #[trigger] labeled(v.claims[i], v.parent))
    &&& v.allocated as nat == inode_claims::allocated(v.claims) && v.allocated <= v.index.header.blocks
    &&& v.billing.own as nat == v.allocated as nat * 8
}

pub struct Ordinary {
    number: u32, directory: bool, claims: Vec<Claim>, allocated: u64,
    external: u32, billing: Usage, checked: Ghost<OrdinaryView>,
}
impl Ordinary {
    pub closed spec fn view(&self) -> OrdinaryView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        valid(self.view()) && self.number == self.view().parent.node.number
            && self.directory == directory(self.view().parent) && self.claims@ == self.view().claims
            && self.allocated == self.view().allocated && self.external as nat == ea_parent::address(self.view().parent)
            && self.billing == self.view().billing
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn number(&self) -> (r: u32)
        ensures self.wf(), valid(self.view()), r == self.view().parent.node.number,
    { proof { use_type_invariant(self); } self.number }
    pub fn is_directory(&self) -> (r: bool)
        ensures self.wf(), valid(self.view()), r == directory(self.view().parent),
    { proof { use_type_invariant(self); } self.directory }
    pub fn claims(&self) -> (r: &[Claim])
        ensures self.wf(), valid(self.view()), r@ == self.view().claims,
    { proof { use_type_invariant(self); } &self.claims }
    pub fn allocated_blocks(&self) -> (r: u64)
        ensures self.wf(), valid(self.view()), r == self.view().allocated,
    { proof { use_type_invariant(self); } self.allocated }
    pub fn external_address(&self) -> (r: u32)
        ensures self.wf(), valid(self.view()), r as nat == ea_parent::address(self.view().parent),
    { proof { use_type_invariant(self); } self.external }
    pub fn usage(&self) -> (r: Usage)
        ensures self.wf(), valid(self.view()), r == self.view().billing,
    { proof { use_type_invariant(self); } self.billing }
}

fn copy_claims(entries: &[Claim]) -> (r: Vec<Claim>) ensures r@ == entries@ {
    let mut copied = Vec::new(); let mut i = 0usize;
    while i < entries.len()
        invariant i <= entries.len(), copied@ == entries@.take(i as int),
        decreases entries.len() - i,
    { copied.push(entries[i]); assert(copied@ =~= entries@.take(i as int + 1)); i += 1; }
    assert(entries@.take(i as int) =~= entries@); copied
}
fn check_labels(entries: &[Claim], number: u32, generation: u32, kind: u8, Ghost(parent): Ghost<ParentView>) -> (r: bool)
    requires parent.node.number == number, bytes::le32(parent.node.raw, 100) == generation,
        kind == owner(parent).kind,
    ensures r ==> forall|i: int| 0 <= i < entries.len() ==> #[trigger] labeled(entries@[i], parent),
{
    let mut i = 0usize;
    while i < entries.len()
        invariant i <= entries.len(), parent.node.number == number,
            bytes::le32(parent.node.raw, 100) == generation, kind == owner(parent).kind,
            forall|j: int| 0 <= j < i ==> #[trigger] labeled(entries@[j], parent),
        decreases entries.len() - i,
    {
        let claim = entries[i];
        if claim.inode != number || claim.generation != generation || (claim.kind != kind && claim.kind != 6) { return false; }
        assert(labeled(claim, parent)); i += 1;
    }
    true
}

pub fn collect(index: &Index<'_, '_>, number: u32, budget: u64, initial: Census) -> (r: Option<(Census, Ordinary)>)
    ensures index.wf(), ea_index::valid(index.view()), initial.wf(), match r {
        Some((next, ordinary)) => next.wf() && ordinary.wf() && valid(ordinary.view())
            && ordinary.view().index == index.view() && ordinary.view().parent.node.number == number
            && ordinary.view().budget == budget && ordinary.view().roles == next.view().roles
            && block_claims::mapped_claims(next.view().roles, ordinary.view().claims)
            && next.view().roles.len() == initial.view().roles.len()
            && next.view().claims == initial.view().claims + ordinary.view().claims
            && block_claims::preserves_occupied(initial.view().roles, next.view().roles),
        None => true,
    },
{
    let (blocks, _, _, seed) = index.parameters(); let _ = initial.block_count();
    if budget == 0 || budget > blocks as u64 + 1 { return None; }
    let allocated_node = match index.node(number) { Some(node) => node, None => { return None; } };
    let _ = allocated_node.number();
    let parent = match ea_parent::inspect(index.header(), number) { Some(parent) => parent, None => { return None; } };
    let raw = parent.node().raw();
    let mode = bytes::read_le16(raw, 0).unwrap(); let is_directory = mode & 0xf000 == 0x4000;
    if number == 2 && !is_directory { return None; }
    let (compat, _, _) = index.header().feature_flags();
    if bytes::read_le32(raw, 32).unwrap() & 0x1000 != 0 && compat & 0x20 == 0 { return None; }
    let logical = parent.logical_records().unwrap();
    let huge = index.header().huge_files();
    let billing = match ea_billing::split(raw, huge, number, &logical) { Some(usage) => usage, None => { return None; } };
    let generation = bytes::read_le32(raw, 100).unwrap();
    let position = parent.node().position(); if position > u64::MAX - 40 { return None; }
    let source = index.source(); let checksum_seed = inode::inode_seed(seed, number, generation);
    let prefix = initial.claims().len(); let ghost before = initial.view();
    let own = Owner { number, generation, kind: if is_directory { 5u8 } else { 4u8 } };
    let (next, allocated, tree) = match extent_claims::collect_checked(initial, source, position + 40, blocks, checksum_seed, own, budget) {
        Some(result) => result, None => { return None; }
    };
    let visits = tree.checked_nodes();
    let ghost c = tree.context();
    assert(c == context(parent.view().node));
    assert(own == owner(parent.view()));
    let ghost complete = tree_claims(parent.view());
    assert(next.view().claims == before.claims + complete);
    let all_claims = next.claims(); assert(prefix <= all_claims.len());
    let appended = copy_claims(&all_claims[prefix..]);
    assert(appended@ =~= complete);
    assert forall|i: int, j: int| 0 <= i < j < appended.len() implies #[trigger] block_claims::disjoint(appended@[i], appended@[j]) by {
        reveal(block_claims::ledger);
        assert(next.view().claims[prefix as int + i] == appended@[i]);
        assert(next.view().claims[prefix as int + j] == appended@[j]);
        assert(block_claims::disjoint(next.view().claims[prefix as int + i], next.view().claims[prefix as int + j]));
    }
    if !check_labels(&appended, number, generation, own.kind, Ghost(parent.view())) { return None; }
    if billing.own != allocated * 8 { return None; }
    let external = parent.external_address();
    let ghost view = OrdinaryView { index: index.view(), parent: parent.view(), billing,
        roles: next.view().roles, claims: appended@, allocated, budget, visits };
    assert(valid(view)) by { reveal(valid); }
    Some((next, Ordinary { number, directory: is_directory, claims: appended, allocated,
        external, billing, checked: Ghost(view) }))
}

pub proof fn every_ordinary_inode_contributes_its_complete_source_tree(v: OrdinaryView)
    requires valid(v),
    ensures v.claims == tree_claims(v.parent), block_claims::mapped_claims(v.roles, v.claims),
{ reveal(valid); }
pub proof fn ordinary_parent_residual_sectors_equal_owned_tree_storage(v: OrdinaryView)
    requires valid(v),
    ensures v.billing.own as nat == 8 * inode_claims::allocated(v.claims),
        ea_billing::checked(v.parent.node.raw, ea_parent::huge(v.index.header), v.parent.node.number,
            ea_parent::logical_projection(v.parent), v.billing),
{ reveal(valid); }
pub proof fn ordinary_inode_bills_logical_ea_and_external_xattrs_separately_from_owned_tree_blocks(v: OrdinaryView)
    requires valid(v),
    ensures v.billing.total as nat == 8 * inode_claims::allocated(v.claims) + v.billing.ea as nat + v.billing.external as nat,
{ reveal(valid); reveal(ea_billing::checked); }
pub proof fn every_ordinary_claim_is_labeled_by_its_actual_source_inode(v: OrdinaryView, i: int)
    requires valid(v), 0 <= i < v.claims.len(),
    ensures v.claims[i].inode == v.parent.node.number,
        v.claims[i].generation == bytes::le32(v.parent.node.raw, 100),
{ reveal(valid); assert(labeled(v.claims[i], v.parent)); }
pub proof fn ordinary_directory_data_allocations_are_initialized(v: OrdinaryView, i: int)
    requires valid(v), directory(v.parent), 0 <= i < v.claims.len(), v.claims[i].kind != 6,
    ensures v.claims[i].kind == 5, v.claims[i].initialized,
{
    reveal(valid);
    assert(labeled(v.claims[i], v.parent));
    reveal(block_claims::mapped_claims);
    assert(block_claims::valid_claim(v.claims[i], v.roles.len()));
}
pub proof fn ordinary_tree_claims_are_pairwise_physically_disjoint(v: OrdinaryView, i: int, j: int)
    requires valid(v), 0 <= i < j < v.claims.len(),
    ensures block_claims::disjoint(v.claims[i], v.claims[j]),
{ reveal(valid); }

}
