// SPDX-License-Identifier: MPL-2.0

//! Complete modern EA value extent allocations, initialized source bytes and
//! exact physical sector accounting. An owned claim ledger rejects aliases;
//! its pre-existing entries and allocation bitmap provenance remain the
//! caller's separate responsibility. This grants no mounted or I/O authority.

use vstd::prelude::*;
use crate::{block_claims::{self, Census, Claim, Slot}, bytes, crc,
    ea_index::{self, Index, IndexView}, ea_inode::{self, Info, Status},
    ea_source::{self, NodeView}, ea_value,
    extent_claims::{self, Owner}, extent_span::SpanView, extent_tree,
    inode, inode_claims};

verus! {

pub open spec fn owner(node: NodeView) -> Owner {
    Owner { number: node.number, generation: bytes::le32(node.raw, 100) as u32, kind: 4 }
}
pub open spec fn tree_claims(node: NodeView) -> Seq<Claim> {
    extent_claims::checked_claims(ea_value::context(node), owner(node))
}
pub open spec fn value_blocks(size: u32) -> nat { (size as nat + 4095) / 4096 }
pub open spec fn data_count(entries: Seq<Claim>) -> nat decreases entries.len() {
    if entries.len() == 0 { 0nat } else {
        data_count(entries.drop_last()) + if entries.last().kind == 4 { entries.last().length as nat } else { 0nat }
    }
}
pub open spec fn positioned(entry: Claim, number: u32, generation: u32, next: nat, limit: nat) -> bool {
    entry.inode == number && entry.generation == generation && entry.start > 0 && entry.length > 0
        && if entry.kind == 4 {
            entry.initialized && entry.logical as nat == next && next + entry.length <= limit
        } else { entry.kind == 6 && entry.length == 1 && entry.logical == 0 && !entry.initialized }
}
#[verifier::opaque]
pub open spec fn dense(entries: Seq<Claim>, number: u32, generation: u32, limit: nat) -> bool {
    data_count(entries) == limit
        && forall|i: int| 0 <= i < entries.len() ==> #[trigger] positioned(entries[i], number, generation, data_count(entries.take(i)), limit)
}
pub open spec fn map_roles(roles: Seq<Slot>, maps: Seq<u64>, number: u32, generation: u32) -> bool {
    maps.len() <= 4096 && forall|i: int| 0 <= i < maps.len() ==>
        (#[trigger] maps[i]) < roles.len() && roles[maps[i] as int].kind == 4
        && roles[maps[i] as int].inode == number && roles[maps[i] as int].generation == generation
        && roles[maps[i] as int].logical == i && roles[maps[i] as int].initialized
}

pub struct StoredView {
    pub index: IndexView, pub node: NodeView, pub info: Info,
    pub roles: Seq<Slot>, pub claims: Seq<Claim>, pub data: Seq<u8>,
    pub maps: Seq<u64>, pub spans: Seq<SpanView>, pub budget: u64,
    pub visits: u64, pub allocated: u64,
}
#[verifier::opaque]
pub open spec fn valid(v: StoredView) -> bool {
    let c = ea_value::context(v.node);
    &&& ea_index::valid(v.index) && ea_source::node_valid(v.node)
    &&& v.node.header == v.index.header && v.node.number == v.info.number
    &&& ea_index::inode_allocated(v.index, v.node.number)
    &&& ea_inode::represents(v.info, v.node.raw) && v.info.status == Status::Live
    &&& v.info.inodes == v.index.header.inodes && v.info.seed == v.index.header.seed
    &&& 0 < v.info.size <= ea_inode::MAX_VALUE
    &&& 1 <= v.visits <= v.budget <= ea_value::MAX_NODES
    &&& extent_tree::context_valid(c)
    &&& extent_tree::subtree_valid(c, extent_tree::root_node(c), None,
        bytes::le16(extent_tree::root_node(c).raw, 6) as u16, None, crate::extent::MAX_LOGICAL_END)
    &&& v.visits == extent_tree::tree_visits(c, extent_tree::root_node(c), bytes::le16(extent_tree::root_node(c).raw, 6) as u16)
    &&& v.claims == tree_claims(v.node) && v.roles.len() == v.index.header.blocks
    &&& block_claims::mapped_claims(v.roles, v.claims)
    &&& (forall|i: int, j: int| 0 <= i < j < v.claims.len() ==> #[trigger] block_claims::disjoint(v.claims[i], v.claims[j]))
    &&& v.allocated as nat == inode_claims::allocated(v.claims) && v.allocated <= v.index.header.blocks
    &&& bytes::le32(v.node.raw, 28) == v.allocated as nat * 8 && bytes::le16(v.node.raw, 116) == 0
    &&& dense(v.claims, v.info.number, v.info.generation, value_blocks(v.info.size))
    &&& v.data.len() == v.info.size && ea_value::content(v.node.header.source, v.maps, v.data)
    &&& v.maps.len() == value_blocks(v.info.size) && v.maps.no_duplicates() && v.spans.len() == v.maps.len()
    &&& (forall|i: int| 0 <= i < v.maps.len() ==> #[trigger] ea_value::mapped(c, i, v.maps[i], v.spans[i]))
    &&& map_roles(v.roles, v.maps, v.info.number, v.info.generation)
    &&& crc::fold(v.info.seed, v.data) == v.info.hash
}

pub struct Stored {
    info: Info, data: Vec<u8>, maps: Vec<u64>, claims: Vec<Claim>,
    allocated: u64, checked: Ghost<StoredView>,
}
impl Stored {
    pub closed spec fn view(&self) -> StoredView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        valid(self.view()) && self.info == self.view().info && self.data@ == self.view().data
            && self.maps@ == self.view().maps && self.claims@ == self.view().claims
            && self.allocated == self.view().allocated
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn info(&self) -> (r: Info) ensures self.wf(), valid(self.view()), r == self.view().info {
        proof { use_type_invariant(self); } self.info
    }
    pub fn as_slice(&self) -> (r: &[u8]) ensures self.wf(), valid(self.view()), r@ == self.view().data {
        proof { use_type_invariant(self); } &self.data
    }
    pub fn blocks(&self) -> (r: &[u64]) ensures self.wf(), valid(self.view()), r@ == self.view().maps {
        proof { use_type_invariant(self); } &self.maps
    }
    pub fn claims(&self) -> (r: &[Claim]) ensures self.wf(), valid(self.view()), r@ == self.view().claims {
        proof { use_type_invariant(self); } &self.claims
    }
    pub fn allocated_blocks(&self) -> (r: u64) ensures self.wf(), valid(self.view()), r == self.view().allocated {
        proof { use_type_invariant(self); } self.allocated
    }
}

fn check_dense(entries: &[Claim], number: u32, generation: u32, limit: u64) -> (r: bool)
    ensures r ==> dense(entries@, number, generation, limit as nat),
{
    let mut i = 0usize; let mut next = 0u64;
    while i < entries.len()
        invariant i <= entries.len(), next <= limit, next as nat == data_count(entries@.take(i as int)),
            forall|j: int| 0 <= j < i ==> #[trigger] positioned(entries@[j], number, generation, data_count(entries@.take(j)), limit as nat),
        decreases entries.len() - i,
    {
        let entry = entries[i]; let ghost prior = next;
        if entry.inode != number || entry.generation != generation || entry.start == 0 || entry.length == 0 { return false; }
        if entry.kind == 4 {
            if !entry.initialized || entry.logical as u64 != next || entry.length as u64 > limit - next { return false; }
            next += entry.length as u64;
        } else if entry.kind != 6 || entry.length != 1 || entry.logical != 0 || entry.initialized { return false; }
        assert(positioned(entry, number, generation, prior as nat, limit as nat));
        assert(entries@.take(i as int + 1).drop_last() =~= entries@.take(i as int));
        assert(entries@.take(i as int + 1).last() == entry);
        assert(next as nat == data_count(entries@.take(i as int + 1)));
        assert forall|j: int| 0 <= j < i + 1 implies #[trigger] positioned(entries@[j], number, generation, data_count(entries@.take(j)), limit as nat) by {
            if j == i { assert(entries@[j] == entry); }
        }
        i += 1;
    }
    if next != limit { return false; }
    assert(entries@.take(i as int) =~= entries@);
    assert(dense(entries@, number, generation, limit as nat)) by { reveal(dense); }
    true
}
fn copy_claims(entries: &[Claim]) -> (r: Vec<Claim>) ensures r@ == entries@ {
    let mut copied = Vec::new(); let mut i = 0usize;
    while i < entries.len()
        invariant i <= entries.len(), copied@ == entries@.take(i as int),
        decreases entries.len() - i,
    { copied.push(entries[i]); assert(copied@ =~= entries@.take(i as int + 1)); i += 1; }
    assert(entries@.take(i as int) =~= entries@); copied
}
fn check_map_roles(census: &Census, maps: &[u64], number: u32, generation: u32) -> (r: bool)
    ensures census.wf(), r ==> map_roles(census.view().roles, maps@, number, generation),
{
    let _ = census.block_count(); if maps.len() > 4096 { return false; }
    let mut i = 0usize;
    while i < maps.len()
        invariant census.wf(), i <= maps.len() <= 4096,
            forall|j: int| 0 <= j < i ==> (#[trigger] maps@[j]) < census.view().roles.len()
                && census.view().roles[maps@[j] as int].kind == 4
                && census.view().roles[maps@[j] as int].inode == number && census.view().roles[maps@[j] as int].generation == generation
                && census.view().roles[maps@[j] as int].logical == j && census.view().roles[maps@[j] as int].initialized,
        decreases maps.len() - i,
    {
        let physical = maps[i]; if physical > u32::MAX as u64 { return false; }
        let role = match census.role_of(physical as u32) { Some(role) => role, None => { return false; } };
        if role.kind != 4 || role.inode != number || role.generation != generation || role.logical != i as u32 || !role.initialized { return false; }
        i += 1;
    }
    true
}

pub fn inspect(index: &Index<'_, '_>, number: u32, budget: u64, initial: Census) -> (r: Option<(Census, Stored)>)
    ensures index.wf(), ea_index::valid(index.view()), initial.wf(), match r {
        Some((next, stored)) => next.wf() && stored.wf() && valid(stored.view())
            && stored.view().index == index.view() && stored.view().info.number == number
            && stored.view().budget == budget && stored.view().roles == next.view().roles
            && block_claims::mapped_claims(next.view().roles, stored.view().claims)
            && next.view().roles.len() == initial.view().roles.len()
            && next.view().claims == initial.view().claims + stored.view().claims
            && block_claims::preserves_occupied(initial.view().roles, next.view().roles),
        None => true,
    },
{
    hide(inode::checksum);
    let (blocks, inodes, _, seed) = index.parameters(); let _ = initial.block_count();
    if budget == 0 || budget > ea_value::MAX_NODES { return None; }
    let node = match index.node(number) { Some(node) => node, None => { return None; } };
    let info = match ea_inode::parse(node.raw(), number, inodes, seed, Status::Live) { Some(info) => info, None => { return None; } };
    if info.size == 0 || info.size > ea_inode::MAX_VALUE { return None; }
    let position = node.position(); if position > u64::MAX - 40 { return None; }
    let root = position + 40; let source = index.source();
    let checksum_seed = inode::inode_seed(seed, number, info.generation);
    let prefix = initial.claims().len(); let ghost before = initial.view();
    let own = Owner { number, generation: info.generation, kind: 4 };
    let (next, allocated, tree) = match extent_claims::collect_checked(initial, source, root, blocks, checksum_seed, own, budget) {
        Some(result) => result, None => { return None; }
    };
    let visits = tree.checked_nodes();
    let ghost c = tree.context();
    assert(c == ea_value::context(node.view()));
    assert(own == owner(node.view()));
    let ghost complete = tree_claims(node.view());
    assert(next.view().claims == before.claims + complete);
    let all_claims = next.claims();
    assert(prefix <= all_claims.len());
    let appended = copy_claims(&all_claims[prefix..]);
    assert(appended@ =~= complete);
    assert forall|i: int, j: int| 0 <= i < j < appended.len() implies #[trigger] block_claims::disjoint(appended@[i], appended@[j]) by {
        reveal(block_claims::ledger);
        assert(next.view().claims[prefix as int + i] == appended@[i]);
        assert(next.view().claims[prefix as int + j] == appended@[j]);
        assert(block_claims::disjoint(next.view().claims[prefix as int + i], next.view().claims[prefix as int + j]));
    }
    let logical_blocks = (info.size as u64 + 4095) / 4096;
    if !check_dense(&appended, number, info.generation, logical_blocks) { return None; }
    if bytes::read_le32(node.raw(), 28).unwrap() as u64 != allocated * 8 { return None; }
    let (data, maps, Ghost(spans)) = match ea_value::read_tree(&tree, source, info.size) {
        Some(parts) => parts, None => { return None; }
    };
    if !ea_value::distinct(&maps) || !ea_value::check_content(source, &maps, &data)
        || !check_map_roles(&next, &maps, number, info.generation) { return None; }
    if crc::crc32c(seed, &data) != info.hash { return None; }
    let ghost view = StoredView { index: index.view(), node: node.view(), info,
        roles: next.view().roles, claims: appended@, data: data@, maps: maps@, spans,
        budget, visits, allocated };
    assert(valid(view)) by { reveal(valid); reveal(ea_inode::accepted); }
    Some((next, Stored { info, data, maps, claims: appended, allocated, checked: Ghost(view) }))
}

pub proof fn every_stored_ea_value_has_all_its_source_tree_claims(v: StoredView)
    requires valid(v),
    ensures v.claims == tree_claims(v.node), block_claims::mapped_claims(v.roles, v.claims),
{ reveal(valid); }
pub proof fn every_stored_ea_extent_ends_within_the_value(v: StoredView, i: int)
    requires valid(v), 0 <= i < v.claims.len(), v.claims[i].kind == 4,
    ensures v.claims[i].initialized, v.claims[i].logical as nat + v.claims[i].length <= value_blocks(v.info.size),
{
    reveal(valid); reveal(dense);
    assert(positioned(v.claims[i], v.info.number, v.info.generation, data_count(v.claims.take(i)), value_blocks(v.info.size)));
}
pub proof fn every_complete_ea_tree_allocation_is_physically_disjoint(v: StoredView, i: int, j: int)
    requires valid(v), 0 <= i < j < v.claims.len(),
    ensures block_claims::disjoint(v.claims[i], v.claims[j]),
{ reveal(valid); }
pub proof fn stored_ea_physical_sectors_include_every_external_extent_node(v: StoredView)
    requires valid(v),
    ensures bytes::le32(v.node.raw, 28) == 8 * inode_claims::allocated(v.claims), bytes::le16(v.node.raw, 116) == 0,
{ reveal(valid); }
pub proof fn every_stored_ea_byte_and_hash_is_from_the_original_snapshot(v: StoredView, i: int)
    requires valid(v), 0 <= i < v.data.len(),
    ensures v.data[i] == v.node.header.source[v.maps[i / 4096] as int * 4096 + i % 4096],
        crc::fold(v.info.seed, v.data) == v.info.hash,
{ reveal(valid); }
pub proof fn stored_ea_maps_are_initialized_allocated_claim_slots(v: StoredView, i: int)
    requires valid(v), 0 <= i < v.maps.len(),
    ensures v.maps[i] < v.roles.len(), v.roles[v.maps[i] as int].kind == 4,
        v.roles[v.maps[i] as int].inode == v.info.number && v.roles[v.maps[i] as int].generation == v.info.generation,
        v.roles[v.maps[i] as int].logical == i && v.roles[v.maps[i] as int].initialized,
{ reveal(valid); }
pub proof fn the_same_live_ea_metadata_has_one_exact_representation(raw: Seq<u8>, a: Info, b: Info)
    requires ea_inode::represents(a, raw), ea_inode::represents(b, raw),
        a.number == b.number, a.inodes == b.inodes, a.seed == b.seed, a.status == b.status,
    ensures a == b,
{}

}
