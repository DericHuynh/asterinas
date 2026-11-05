// SPDX-License-Identifier: MPL-2.0

//! Complete bounded EA payload and allocation inspection over one source.
//! This retains the source reference census and validates every EA value once.
//! Ordinary inode/journal extent separation, full filesystem admission,
//! mutation, caller authority and CortenMM/device refinement remain separate.

use vstd::prelude::*;
use crate::{block_claims::{self, Census as Blocks, CensusView as BlocksView}, ea_block_policy,
    ea_census::{self, Census as References, CensusView as ReferencesView}, ea_inode::{Info, Status}, ea_refs::{self, Reference},
    ea_storage::{self, Stored, StoredView}, ea_value, snapshot::Snapshot};

verus! {

pub const MAX_BYTES: u64 = 67108864;

pub open spec fn claims(values: Seq<StoredView>) -> Seq<block_claims::Claim> decreases values.len() {
    if values.len() == 0 { Seq::empty() } else { claims(values.drop_last()) + values.last().claims }
}
pub open spec fn value_bytes(values: Seq<StoredView>) -> nat decreases values.len() {
    if values.len() == 0 { 0nat } else { value_bytes(values.drop_last()) + values.last().data.len() }
}
pub open spec fn value_blocks(values: Seq<StoredView>) -> nat decreases values.len() {
    if values.len() == 0 { 0nat } else { value_blocks(values.drop_last()) + values.last().allocated as nat }
}
pub open spec fn distinct_values(values: Seq<StoredView>) -> bool {
    forall|i: int, j: int| 0 <= i < j < values.len() ==> (#[trigger] values[i]).info.number != (#[trigger] values[j]).info.number
}
pub open spec fn covers_record(values: Seq<StoredView>, reference: Reference) -> bool {
    exists|i: int| 0 <= i < values.len() && (#[trigger] values[i]).info.number == reference.value && values[i].info.size == reference.size
}
pub open spec fn covers_records(values: Seq<StoredView>, records: Seq<Reference>) -> bool {
    forall|i: int| 0 <= i < records.len() ==> #[trigger] covers_record(values, records[i])
}
pub struct IntegrityView {
    pub references: ReferencesView, pub values: Seq<StoredView>, pub ownership: BlocksView,
    pub inode_budget: u32, pub node_budget: u64, pub byte_budget: u64,
}
#[verifier::opaque]
pub open spec fn valid(v: IntegrityView) -> bool {
    &&& ea_census::valid(v.references) && v.references.budget == v.inode_budget
    &&& 1 <= v.node_budget <= ea_value::MAX_NODES && v.byte_budget <= MAX_BYTES
    &&& value_bytes(v.values) <= v.byte_budget
    &&& v.values.len() == v.references.values.len() && distinct_values(v.values)
    &&& covers_records(v.values, v.references.graph.physical)
    &&& block_claims::ledger(v.ownership.roles, v.ownership.claims)
    &&& v.ownership.roles.len() == v.references.index.header.blocks
    &&& v.ownership.claims == claims(v.values)
    &&& value_blocks(v.values) <= v.ownership.roles.len()
    &&& forall|i: int| 0 <= i < v.values.len() ==> #[trigger] ea_storage::valid(v.values[i])
        && v.values[i].index == v.references.index && v.values[i].info == v.references.values[i]
        && v.values[i].budget == v.node_budget
        && block_claims::mapped_claims(v.ownership.roles, v.values[i].claims)
        && ea_block_policy::valid_claim_storage(v.references, v.values[i].claims)
}
proof fn assemble(v: IntegrityView)
    requires
    (ea_census::valid(v.references) && v.references.budget == v.inode_budget),
    (1 <= v.node_budget <= ea_value::MAX_NODES && v.byte_budget <= MAX_BYTES),
    (value_bytes(v.values) <= v.byte_budget),
    (v.values.len() == v.references.values.len() && distinct_values(v.values)),
    (covers_records(v.values, v.references.graph.physical)),
    (block_claims::ledger(v.ownership.roles, v.ownership.claims)),
    (v.ownership.roles.len() == v.references.index.header.blocks),
    (v.ownership.claims == claims(v.values)),
    (value_blocks(v.values) <= v.ownership.roles.len()),
    (forall|i: int| 0 <= i < v.values.len() ==> #[trigger] ea_storage::valid(v.values[i])
        && v.values[i].index == v.references.index && v.values[i].info == v.references.values[i]
        && v.values[i].budget == v.node_budget
        && block_claims::mapped_claims(v.ownership.roles, v.values[i].claims)
        && ea_block_policy::valid_claim_storage(v.references, v.values[i].claims)),
    ensures valid(v),
{ reveal(valid); }


pub struct Integrity<'s, 'a> {
    references: References<'s, 'a>, ownership: Blocks, values: Vec<Stored>,
    bytes: u64, blocks: u64, checked: Ghost<IntegrityView>,
}
impl<'s, 'a> Integrity<'s, 'a> {
    pub closed spec fn view(&self) -> IntegrityView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        valid(self.view()) && self.references.view() == self.view().references
            && self.ownership.view() == self.view().ownership && self.values.len() == self.view().values.len()
            && self.bytes as nat == value_bytes(self.view().values) && self.blocks as nat == value_blocks(self.view().values)
            && forall|i: int| 0 <= i < self.values.len() ==> (#[trigger] self.values@[i]).view() == self.view().values[i]
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn reference_census(&self) -> (r: &References<'s, 'a>)
        ensures self.wf(), valid(self.view()), r.wf(), r.view() == self.view().references,
    { proof { use_type_invariant(self); } let _ = self.references.values(); &self.references }
    pub fn ledger(&self) -> (r: &Blocks)
        ensures self.wf(), valid(self.view()), r.wf(), r.view() == self.view().ownership,
    { proof { use_type_invariant(self); } let _ = self.ownership.block_count(); &self.ownership }
    pub fn value_count(&self) -> (r: usize)
        ensures self.wf(), valid(self.view()), r == self.view().values.len(),
    { proof { use_type_invariant(self); } self.values.len() }
    pub fn value(&self, index: usize) -> (r: Option<&Stored>)
        ensures self.wf(), valid(self.view()), match r { Some(value) => index < self.view().values.len()
            && value.wf() && ea_storage::valid(value.view()) && value.view() == self.view().values[index as int],
            None => index >= self.view().values.len() },
    {
        proof { use_type_invariant(self); }
        if index >= self.values.len() { return None; }
        let value = &self.values[index]; let _ = value.info(); Some(value)
    }
    pub fn total_bytes(&self) -> (r: u64)
        ensures self.wf(), valid(self.view()), r as nat == value_bytes(self.view().values), r <= self.view().byte_budget,
    { proof { use_type_invariant(self); reveal(valid); } self.bytes }
    pub fn allocated_blocks(&self) -> (r: u64)
        ensures self.wf(), valid(self.view()), r as nat == value_blocks(self.view().values), r <= self.view().ownership.roles.len(),
    { proof { use_type_invariant(self); reveal(valid); } self.blocks }
}

fn same_info(a: Info, b: Info) -> (r: bool) ensures r == (a == b) {
    let status = match (a.status, b.status) { (Status::Live, Status::Live) => true,
        (Status::Unlinked, Status::Unlinked) => true, _ => false };
    status && a.number == b.number && a.inodes == b.inodes && a.seed == b.seed
        && a.mode == b.mode && a.uid == b.uid && a.gid == b.gid && a.size == b.size
        && a.generation == b.generation && a.hash == b.hash && a.refs == b.refs
}

fn new_number(values: &[Stored], number: u32) -> (r: bool)
    ensures r == (forall|j: int| 0 <= j < values.len() ==> (#[trigger] values@[j]).view().info.number != number),
{
    let mut i = 0usize;
    while i < values.len()
        invariant i <= values.len(), forall|j: int| 0 <= j < i ==> (#[trigger] values@[j]).view().info.number != number,
        decreases values.len() - i,
    { if values[i].info().number == number { return false; } i += 1; }
    true
}
fn check_coverage(values: &[Stored], records: &[Reference], Ghost(checked): Ghost<Seq<StoredView>>) -> (r: bool)
    requires checked.len() == values.len(), forall|i: int| 0 <= i < values.len() ==> (#[trigger] values@[i]).view() == checked[i],
    ensures r ==> covers_records(checked, records@),
{
    let mut i = 0usize;
    while i < records.len()
        invariant i <= records.len(), checked.len() == values.len(),
            forall|k: int| 0 <= k < values.len() ==> (#[trigger] values@[k]).view() == checked[k],
            forall|k: int| 0 <= k < i ==> #[trigger] covers_record(checked, records@[k]),
        decreases records.len() - i,
    {
        let mut j = 0usize; let mut found = false;
        while j < values.len()
            invariant i < records.len(), j <= values.len(), checked.len() == values.len(),
                forall|k: int| 0 <= k < values.len() ==> (#[trigger] values@[k]).view() == checked[k],
                forall|k: int| 0 <= k < i ==> #[trigger] covers_record(checked, records@[k]),
                found ==> covers_record(checked, records@[i as int]),
            decreases values.len() - j,
        {
            let info = values[j].info();
            if info.number == records[i].value && info.size == records[i].size {
                assert(checked[j as int].info.number == records@[i as int].value && checked[j as int].info.size == records@[i as int].size);
                assert(exists|k: int| 0 <= k < checked.len() && (#[trigger] checked[k]).info.number == records@[i as int].value && checked[k].info.size == records@[i as int].size);
                found = true; break;
            }
            j += 1;
        }
        if !found { return false; }
        i += 1;
    }
    true
}

pub fn inspect<'s, 'a>(source: &'s Snapshot<'a>, inode_budget: u32, node_budget: u64, byte_budget: u64)
    -> (r: Option<Integrity<'s, 'a>>)
    ensures match r { Some(result) => result.wf() && valid(result.view())
        && result.view().references.index.header.source == source.view()
        && result.view().inode_budget == inode_budget && result.view().node_budget == node_budget && result.view().byte_budget == byte_budget,
        None => true },
{
    if node_budget == 0 || node_budget > ea_value::MAX_NODES || byte_budget > MAX_BYTES { return None; }
    let references = match ea_census::inspect(source, inode_budget) { Some(references) => references, None => { return None; } };
    let infos = references.values(); let index = references.index(); let (blocks, _, _, _) = index.parameters();
    let mut ownership = Blocks::new(blocks).unwrap(); let mut values: Vec<Stored> = Vec::new();
    let mut bytes = 0u64; let mut allocated = 0u64; let mut i = 0usize;
    let ghost mut checked: Seq<StoredView> = Seq::empty();
    assert(ownership.view().claims =~= claims(checked));
    while i < infos.len()
        invariant references.wf(), ea_census::valid(references.view()), index.wf(), index.view() == references.view().index,
            infos@ == references.view().values, references.view().budget == inode_budget,
            blocks == index.view().header.blocks, ownership.wf(), ownership.view().roles.len() == blocks,
            1 <= node_budget <= ea_value::MAX_NODES, byte_budget <= MAX_BYTES,
            i <= infos.len(), values.len() == i, checked.len() == i, distinct_values(checked),
            bytes as nat == value_bytes(checked), bytes <= byte_budget,
            allocated as nat == value_blocks(checked), allocated <= blocks,
            ownership.view().claims == claims(checked),
            forall|j: int| 0 <= j < i ==> (#[trigger] values@[j]).view() == checked[j],
            forall|j: int| 0 <= j < i ==> #[trigger] ea_storage::valid(checked[j])
                && checked[j].index == references.view().index && checked[j].info == infos@[j] && checked[j].budget == node_budget
                && block_claims::mapped_claims(ownership.view().roles, checked[j].claims)
                && ea_block_policy::valid_claim_storage(references.view(), checked[j].claims),
        decreases infos.len() - i,
    {
        let expected = infos[i];
        if !new_number(&values, expected.number) { return None; }
        assert forall|j: int| 0 <= j < i implies (#[trigger] checked[j]).info.number != expected.number by {
            assert(values@[j].view() == checked[j]);
            assert(values@[j].view().info.number != expected.number);
        }
        if expected.size as u64 > byte_budget - bytes { return None; }
        let ghost prior_roles = ownership.view().roles;
        let (next, value) = match ea_storage::inspect(index, expected.number, node_budget, ownership) {
            Some(result) => result, None => { return None; },
        };
        let actual = value.info(); if !same_info(actual, expected) { return None; }
        let used = value.allocated_blocks();
        if used > blocks as u64 - allocated { return None; }
        if !ea_block_policy::check(&references, value.claims()) { return None; }
        proof {
            assert forall|j: int| 0 <= j < i implies block_claims::mapped_claims(next.view().roles, checked[j].claims) by {
                assert(ea_storage::valid(checked[j]));
                assert(block_claims::mapped_claims(prior_roles, checked[j].claims));
                block_claims::occupied_preservation_keeps_mapped_claims(prior_roles, next.view().roles, checked[j].claims);
            }
        }
        ownership = next;
        let ghost added = value.view(); let length = value.as_slice().len();
        assert(length == expected.size) by { reveal(ea_storage::valid); }
        bytes += length as u64; allocated += used;
        values.push(value);
        let ghost previous = checked; proof { checked = checked.push(added); }
        assert(checked.drop_last() =~= previous); assert(checked.last() == added);
        assert(ownership.view().claims == claims(checked));
        assert forall|a: int, b: int| 0 <= a < b < checked.len() implies (#[trigger] checked[a]).info.number != (#[trigger] checked[b]).info.number by {
            if b < previous.len() { assert(previous[a].info.number != previous[b].info.number); }
            else { assert(previous[a].info.number != expected.number); }
        }
        assert forall|j: int| 0 <= j < i + 1 implies (#[trigger] values@[j]).view() == checked[j] by {
            if j < i { assert(values@[j].view() == previous[j]); }
        }
        assert forall|j: int| 0 <= j < i + 1 implies #[trigger] ea_storage::valid(checked[j])
            && checked[j].index == references.view().index && checked[j].info == infos@[j] && checked[j].budget == node_budget
            && block_claims::mapped_claims(ownership.view().roles, checked[j].claims)
            && ea_block_policy::valid_claim_storage(references.view(), checked[j].claims) by {
            if j < i { assert(checked[j] == previous[j]); }
        }
        i += 1;
    }
    if !check_coverage(&values, references.physical().records(), Ghost(checked)) { return None; }
    let ghost view = IntegrityView { references: references.view(), values: checked, ownership: ownership.view(), inode_budget, node_budget, byte_budget };
    assert(ea_census::valid(view.references));
    assert(view.references.budget == view.inode_budget);
    assert(1 <= view.node_budget <= ea_value::MAX_NODES && view.byte_budget <= MAX_BYTES);
    assert(value_bytes(view.values) <= view.byte_budget);
    assert(view.values.len() == view.references.values.len() && distinct_values(view.values));
    assert(covers_records(view.values, view.references.graph.physical));
    assert(block_claims::ledger(view.ownership.roles, view.ownership.claims));
    assert(view.ownership.roles.len() == view.references.index.header.blocks);
    assert(view.ownership.claims == claims(view.values));
    assert(value_blocks(view.values) <= view.ownership.roles.len());
    assert forall|j: int| 0 <= j < view.values.len() implies #[trigger] ea_storage::valid(view.values[j])
        && view.values[j].index == view.references.index && view.values[j].info == view.references.values[j]
        && view.values[j].budget == view.node_budget
        && block_claims::mapped_claims(view.ownership.roles, view.values[j].claims)
        && ea_block_policy::valid_claim_storage(view.references, view.values[j].claims) by {
        assert(ea_storage::valid(checked[j]));
    }
    proof { assemble(view); }
    Some(Integrity { references, ownership, values, bytes, blocks: allocated, checked: Ghost(view) })
}

pub proof fn every_source_physical_ea_record_has_a_verified_payload(v: IntegrityView, index: int)
    requires valid(v), 0 <= index < v.references.graph.physical.len(),
    ensures covers_record(v.values, v.references.graph.physical[index]),
{ reveal(valid); }

pub proof fn every_source_logical_ea_record_has_a_verified_payload(v: IntegrityView, index: int)
    requires valid(v), 0 <= index < v.references.graph.logical.len(),
    ensures covers_record(v.values, v.references.graph.logical[index].physical),
{
    reveal(valid); reveal(ea_census::valid); reveal(crate::ea_ref_projection::valid);
    assert(crate::ea_ref_projection::contains_record(v.references.graph.physical, v.references.graph.logical[index].physical));
    let i = choose|i: int| 0 <= i < v.references.graph.physical.len()
        && #[trigger] v.references.graph.physical[i] == v.references.graph.logical[index].physical;
    assert(covers_record(v.values, v.references.graph.physical[i]));
}

pub proof fn distinct_integrity_values_have_distinct_inode_numbers(v: IntegrityView, a: int, b: int)
    requires valid(v), 0 <= a < v.values.len(), 0 <= b < v.values.len(), v.values[a].info.number == v.values[b].info.number,
    ensures a == b,
{ reveal(valid); }

pub proof fn every_source_ea_value_has_exactly_one_integrity_result(v: IntegrityView, index: int)
    requires valid(v), 0 <= index < v.references.values.len(),
    ensures ea_storage::valid(v.values[index]), v.values[index].index == v.references.index,
        v.values[index].info == v.references.values[index],
        forall|j: int| 0 <= j < v.values.len() && (#[trigger] v.values[j]).info.number == v.references.values[index].number ==> j == index,
{
    reveal(valid); assert(ea_storage::valid(v.values[index]));
    assert forall|j: int| 0 <= j < v.values.len() && (#[trigger] v.values[j]).info.number == v.references.values[index].number implies j == index by {
        distinct_integrity_values_have_distinct_inode_numbers(v, index, j);
    }
}

pub proof fn every_ea_extent_allocation_has_a_checked_source_block_role(v: IntegrityView, index: int)
    requires valid(v), 0 <= index < v.values.len(),
    ensures block_claims::mapped_claims(v.ownership.roles, v.values[index].claims),
        ea_block_policy::valid_claim_storage(v.references, v.values[index].claims),
{ reveal(valid); assert(ea_storage::valid(v.values[index])); }

pub proof fn integrity_resource_limits_never_return_a_partial_value_prefix(v: IntegrityView)
    requires valid(v),
    ensures v.values.len() == v.references.values.len(), value_bytes(v.values) <= v.byte_budget <= MAX_BYTES,
        v.references.classes.len() == v.references.index.header.inodes <= v.inode_budget,
{ reveal(valid); reveal(ea_census::valid); }

pub proof fn same_source_ea_inode_number_identifies_one_exact_node(a: crate::ea_source::NodeView, b: crate::ea_source::NodeView)
    requires crate::ea_source::node_valid(a), crate::ea_source::node_valid(b),
        a.header == b.header, a.number == b.number,
    ensures a == b,
{
    reveal(crate::ea_source::node_valid);
    assert(a.group == b.group);
    assert(a.slot == b.slot);
    assert(a.descriptor == b.descriptor);
    assert(a.bitmap == b.bitmap);
    assert(a.position == b.position);
    assert(a.raw == b.raw);
}

pub proof fn every_source_target_is_the_exact_verified_inode_and_payload(v: IntegrityView, index: int)
    requires valid(v), 0 <= index < v.references.graph.physical.len(),
    ensures exists|j: int| 0 <= j < v.values.len()
        && (#[trigger] v.values[j]).node == v.references.targets[index].node
        && v.values[j].info == v.references.targets[index].info
        && v.values[j].data.len() == v.references.graph.physical[index].size
        && crate::crc::fold(v.values[j].info.seed, v.values[j].data) == v.references.targets[index].info.hash,
{
    hide(crate::crc::fold);
    reveal(valid);
    reveal(crate::ea_census::valid);
    let reference = v.references.graph.physical[index];
    let target = v.references.targets[index];
    assert(crate::ea_census::target_valid(v.references.index, target));
    reveal(crate::ea_census::target_valid);
    assert(covers_record(v.values, reference));
    let j = choose|j: int| 0 <= j < v.values.len()
        && (#[trigger] v.values[j]).info.number == reference.value && v.values[j].info.size == reference.size;
    let stored = v.values[j];
    assert(crate::ea_storage::valid(stored));
    reveal(crate::ea_storage::valid);
    assert(stored.node.header == target.node.header && stored.node.number == target.node.number);
    same_source_ea_inode_number_identifies_one_exact_node(stored.node, target.node);
    crate::ea_storage::the_same_live_ea_metadata_has_one_exact_representation(stored.node.raw, stored.info, target.info);
    assert(stored.info == target.info);
    assert(stored.data.len() == reference.size);
    assert(exists|k: int| 0 <= k < v.values.len()
        && (#[trigger] v.values[k]).node == v.references.targets[index].node
        && v.values[k].info == v.references.targets[index].info
        && v.values[k].data.len() == v.references.graph.physical[index].size
        && crate::crc::fold(v.values[k].info.seed, v.values[k].data) == v.references.targets[index].info.hash);
}

pub proof fn distinct_ea_values_have_disjoint_complete_physical_claims(v: IntegrityView,
    a: int, b: int, left: int, right: int)
    requires valid(v), 0 <= a < v.values.len(), 0 <= b < v.values.len(), a != b,
        0 <= left < v.values[a].claims.len(), 0 <= right < v.values[b].claims.len(),
    ensures block_claims::disjoint(v.values[a].claims[left], v.values[b].claims[right]),
{
    reveal(valid);
    assert(ea_storage::valid(v.values[a]));
    assert(ea_storage::valid(v.values[b]));
    assert(block_claims::mapped_claims(v.ownership.roles, v.values[a].claims));
    assert(block_claims::mapped_claims(v.ownership.roles, v.values[b].claims));
    reveal(ea_storage::valid);
    reveal(ea_storage::dense);
    let first = v.values[a].claims[left];
    let second = v.values[b].claims[right];
    assert(ea_storage::positioned(first, v.values[a].info.number, v.values[a].info.generation,
        ea_storage::data_count(v.values[a].claims.take(left)), ea_storage::value_blocks(v.values[a].info.size)));
    assert(ea_storage::positioned(second, v.values[b].info.number, v.values[b].info.generation,
        ea_storage::data_count(v.values[b].claims.take(right)), ea_storage::value_blocks(v.values[b].info.size)));
    assert(first.inode == v.values[a].info.number);
    assert(second.inode == v.values[b].info.number);
    if a < b { assert(v.values[a].info.number != v.values[b].info.number); }
    else { assert(v.values[b].info.number != v.values[a].info.number); }
    reveal(block_claims::mapped_claims);
    assert(block_claims::valid_claim(first, v.ownership.roles.len()));
    assert(block_claims::valid_claim(second, v.ownership.roles.len()));
    if !block_claims::disjoint(first, second) {
        let block = if first.start >= second.start { first.start as int } else { second.start as int };
        assert(block_claims::covers(first, block));
        assert(block_claims::covers(second, block));
        assert(v.ownership.roles[block] == block_claims::at(first, block));
        assert(v.ownership.roles[block] == block_claims::at(second, block));
        assert(first.inode == second.inode);
        assert(false);
    }
}

pub proof fn every_logical_ea_binding_checks_its_exact_payload_crc_and_entry_hash(v: IntegrityView, index: int)
    requires valid(v), 0 <= index < v.references.graph.logical.len(),
    ensures exists|j: int| 0 <= j < v.values.len()
        && ea_storage::valid(#[trigger] v.values[j])
        && v.values[j].node == v.references.bindings[index].target.node
        && v.values[j].info == v.references.bindings[index].target.info
        && v.values[j].data.len() == v.references.graph.logical[index].physical.size
        && crate::crc::fold(v.values[j].info.seed, v.values[j].data) == v.references.bindings[index].target.info.hash
        && crate::ea_census::binding_hash(v.references.bindings[index].parent,
            v.references.bindings[index].logical.physical, v.references.bindings[index].entry,
            crate::crc::fold(v.values[j].info.seed, v.values[j].data)),
{
    hide(crate::crc::fold);
    reveal(valid);
    reveal(crate::ea_census::valid);
    reveal(crate::ea_ref_projection::valid);
    let logical = v.references.graph.logical[index];
    let binding = v.references.bindings[index];
    assert(crate::ea_census::binding_valid(v.references.index, binding));
    assert(binding.logical == logical);
    assert(crate::ea_ref_projection::contains_record(v.references.graph.physical, logical.physical));
    let p = choose|p: int| 0 <= p < v.references.graph.physical.len()
        && #[trigger] v.references.graph.physical[p] == logical.physical;
    every_source_target_is_the_exact_verified_inode_and_payload(v, p);
    let target = v.references.targets[p];
    assert(crate::ea_census::target_valid(v.references.index, target));
    reveal(crate::ea_census::binding_valid);
    reveal(crate::ea_census::target_valid);
    assert(binding.target.record == target.record);
    assert(binding.target.node.header == target.node.header && binding.target.node.number == target.node.number);
    same_source_ea_inode_number_identifies_one_exact_node(binding.target.node, target.node);
    crate::ea_storage::the_same_live_ea_metadata_has_one_exact_representation(target.node.raw, binding.target.info, target.info);
    assert(binding.target == target);
    let j = choose|j: int| 0 <= j < v.values.len()
        && (#[trigger] v.values[j]).node == v.references.targets[p].node
        && v.values[j].info == v.references.targets[p].info
        && v.values[j].data.len() == v.references.graph.physical[p].size
        && crate::crc::fold(v.values[j].info.seed, v.values[j].data) == v.references.targets[p].info.hash;
    assert(ea_storage::valid(v.values[j]));
    assert(crate::bytes::le32(binding.target.node.raw, 8) as u32 == binding.target.info.hash);
    assert(crate::ea_census::binding_hash(binding.parent, binding.logical.physical, binding.entry,
        crate::crc::fold(v.values[j].info.seed, v.values[j].data)));
    assert(exists|k: int| 0 <= k < v.values.len()
        && ea_storage::valid(#[trigger] v.values[k])
        && v.values[k].node == v.references.bindings[index].target.node
        && v.values[k].info == v.references.bindings[index].target.info
        && v.values[k].data.len() == v.references.graph.logical[index].physical.size
        && crate::crc::fold(v.values[k].info.seed, v.values[k].data) == v.references.bindings[index].target.info.hash
        && crate::ea_census::binding_hash(v.references.bindings[index].parent,
            v.references.bindings[index].logical.physical, v.references.bindings[index].entry,
            crate::crc::fold(v.values[k].info.seed, v.values[k].data)));
}

}
