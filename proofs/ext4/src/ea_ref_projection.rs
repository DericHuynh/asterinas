// SPDX-License-Identifier: MPL-2.0

//! Complete physical/logical EA reference projection over supplied parent data.
//! Parent inputs must be bound to admitted disk bytes by the caller. This layer
//! owns a checked accounting graph; it authenticates neither disk nor caller.

use vstd::prelude::*;
use crate::ea_refs::{self, Kind, Ledger, Location, ParentReference, Reference};

verus! {

pub const MAX_PARENTS: usize = ea_refs::MAX_RECORDS;
pub const MAX_PARENT_ENTRIES: usize = 260;

pub struct Input { pub parent: u32, pub body: Seq<Reference>, pub external: Seq<Reference> }
pub open spec fn body_matches(parent: u32, body: Seq<Reference>) -> bool {
    forall|i: int| 0 <= i < body.len() ==> (#[trigger] body[i]).location.kind == Kind::Inline && body[i].location.owner == parent as u64
}
pub open spec fn external_matches(external: Seq<Reference>) -> bool {
    forall|i: int| 0 <= i < external.len() ==> (#[trigger] external[i]).location.kind == Kind::External && external[i].location.owner == external[0].location.owner
}
pub open spec fn input_good(input: Input) -> bool {
    input.parent > 0 && input.body.len() + input.external.len() > 0
        && input.body.len() <= MAX_PARENT_ENTRIES && input.external.len() <= MAX_PARENT_ENTRIES && ea_refs::valid(input.body) && ea_refs::valid(input.external)
        && body_matches(input.parent, input.body) && external_matches(input.external)
}
pub open spec fn has_location(records: Seq<Reference>, location: Location) -> bool {
    exists|i: int| 0 <= i < records.len() && ea_refs::same_location((#[trigger] records[i]).location, location)
}
pub open spec fn contains_record(records: Seq<Reference>, reference: Reference) -> bool {
    exists|i: int| 0 <= i < records.len() && #[trigger] records[i] == reference
}
pub open spec fn prefix(before: Seq<Reference>, after: Seq<Reference>) -> bool {
    before.len() <= after.len() && after.take(before.len() as int) == before
}
pub open spec fn appended_physical(before: Seq<Reference>, incoming: Seq<Reference>) -> Seq<Reference> decreases incoming.len() {
    if incoming.len() == 0 { before }
    else {
        let previous = appended_physical(before, incoming.drop_last()); let next = incoming.last();
        if has_location(previous, next.location) { previous } else { previous.push(next) }
    }
}
pub open spec fn logical_entries(parent: u32, references: Seq<Reference>) -> Seq<ParentReference> {
    Seq::new(references.len(), |i: int| ParentReference { parent, physical: references[i] })
}
pub open spec fn physical_projection(inputs: Seq<Input>) -> Seq<Reference> decreases inputs.len() {
    if inputs.len() == 0 { Seq::empty() }
    else { appended_physical(appended_physical(physical_projection(inputs.drop_last()), inputs.last().body), inputs.last().external) }
}
pub open spec fn logical_projection(inputs: Seq<Input>) -> Seq<ParentReference> decreases inputs.len() {
    if inputs.len() == 0 { Seq::empty() }
    else { logical_projection(inputs.drop_last()) + logical_entries(inputs.last().parent, inputs.last().body) + logical_entries(inputs.last().parent, inputs.last().external) }
}
pub open spec fn parent_numbers(inputs: Seq<Input>) -> Seq<u32> {
    Seq::new(inputs.len(), |i: int| inputs[i].parent)
}
pub struct GraphView { pub physical: Seq<Reference>, pub logical: Seq<ParentReference>, pub parents: Seq<u32>, pub inputs: Seq<Input> }
#[verifier::opaque]
pub open spec fn valid(v: GraphView) -> bool {
    &&& v.parents.len() == v.inputs.len() <= MAX_PARENTS
    &&& v.parents == parent_numbers(v.inputs)
    &&& forall|i: int| 0 <= i < v.inputs.len() ==> #[trigger] input_good(v.inputs[i])
    &&& forall|i: int, j: int| 0 <= i < j < v.parents.len() ==> #[trigger] v.parents[i] != #[trigger] v.parents[j]
    &&& v.physical == physical_projection(v.inputs) && ea_refs::valid(v.physical)
    &&& v.logical == logical_projection(v.inputs) && ea_refs::logical_valid(v.logical)
    &&& forall|i: int| 0 <= i < v.logical.len() ==> #[trigger] contains_record(v.physical, v.logical[i].physical)
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Error { InvalidParent, DuplicateParent, ParentLimit, InvalidBody, InvalidExternal, InconsistentReference, ReferenceLimit, InvalidQuotaProjection }

fn equal_location(a: Location, b: Location) -> (r: bool) ensures r == ea_refs::same_location(a, b) {
    let kind = match (a.kind, b.kind) { (Kind::Inline, Kind::Inline) => true, (Kind::External, Kind::External) => true, _ => false };
    kind && a.owner == b.owner && a.offset == b.offset
}
fn locate(records: &[Reference], location: Location) -> (r: Option<usize>)
    ensures match r { Some(i) => i < records.len() && ea_refs::same_location(records@[i as int].location, location) && has_location(records@, location), None => !has_location(records@, location) },
{
    let mut i = 0usize;
    while i < records.len()
        invariant i <= records.len(), forall|j: int| 0 <= j < i ==> !ea_refs::same_location((#[trigger] records@[j]).location, location),
        decreases records.len() - i,
    {
        if equal_location(records[i].location, location) {
            assert(exists|j: int| 0 <= j < records.len() && ea_refs::same_location((#[trigger] records@[j]).location, location));
            return Some(i);
        }
        i += 1;
    }
    None
}
proof fn a_member_survives_an_append(records: Seq<Reference>, reference: Reference, next: Reference)
    requires contains_record(records, reference),
    ensures contains_record(records.push(next), reference),
{
    let i = choose|i: int| 0 <= i < records.len() && #[trigger] records[i] == reference;
    assert(records.push(next)[i] == reference);
}
proof fn a_member_survives_a_prefix(before: Seq<Reference>, after: Seq<Reference>, reference: Reference)
    requires prefix(before, after), contains_record(before, reference),
    ensures contains_record(after, reference),
{
    let i = choose|i: int| 0 <= i < before.len() && #[trigger] before[i] == reference;
    assert(after[i] == before[i]);
}
proof fn nested_prefixes_compose(before: Seq<Reference>, middle: Seq<Reference>, after: Seq<Reference>)
    requires prefix(before, middle), prefix(middle, after),
    ensures prefix(before, after),
{ assert(after.take(before.len() as int) =~= before); }

fn merge_references(original: Ledger, incoming: &[Reference]) -> (r: Result<Ledger, Error>)
    ensures original.wf(), match r { Ok(next) => next.wf() && next.view() == appended_physical(original.view(), incoming@)
        && prefix(original.view(), next.view()) && forall|i: int| 0 <= i < incoming.len() ==> #[trigger] contains_record(next.view(), incoming@[i]), Err(_) => true },
{
    let _ = original.len();
    let ghost before = original.view();
    assert(ea_refs::valid(before));
    let mut physical = original; let mut i = 0usize;
    assert(physical.view().take(before.len() as int) =~= before);
    assert(prefix(before, physical.view()));
    while i < incoming.len()
        invariant original.wf(), before == original.view(), ea_refs::valid(before), physical.wf(), i <= incoming.len(), physical.view() == appended_physical(before, incoming@.take(i as int)), prefix(before, physical.view()),
            forall|j: int| 0 <= j < i ==> #[trigger] contains_record(physical.view(), incoming@[j]),
        decreases incoming.len() - i,
    {
        let reference = incoming[i]; let ghost previous = physical.view();
        assert(incoming@.take(i as int + 1).drop_last() =~= incoming@.take(i as int));
        assert(incoming@.take(i as int + 1).last() == reference);
        match locate(physical.records(), reference.location) {
            Some(k) => {
                let existing = physical.at(k).unwrap();
                if existing.value != reference.value || existing.size != reference.size { return Err(Error::InconsistentReference); }
                assert(existing == reference);
                assert(physical.view()[k as int] == reference);
                assert(exists|j: int| 0 <= j < physical.view().len() && #[trigger] physical.view()[j] == reference);
                assert(contains_record(physical.view(), reference));
            },
            None => {
                physical = match physical.add(reference) { Ok(next) => next, Err((_, _)) => { return Err(Error::ReferenceLimit); } };
                assert(physical.view() == previous.push(reference));
                assert(physical.view().take(before.len() as int) =~= before);
                assert forall|j: int| 0 <= j < i implies #[trigger] contains_record(physical.view(), incoming@[j]) by {
                    a_member_survives_an_append(previous, incoming@[j], reference);
                }
                assert(physical.view()[previous.len() as int] == reference);
                assert(exists|j: int| 0 <= j < physical.view().len() && #[trigger] physical.view()[j] == reference);
                assert(contains_record(physical.view(), reference));
            },
        }
        assert(physical.view() == appended_physical(before, incoming@.take(i as int + 1)));
        assert forall|j: int| 0 <= j < i + 1 implies #[trigger] contains_record(physical.view(), incoming@[j]) by {
            if j == i { assert(incoming@[j] == reference); }
        }
        i += 1;
    }
    assert(incoming@.take(i as int) =~= incoming@);
    Ok(physical)
}

fn body_is_for_parent(body: &[Reference], parent: u32) -> (r: bool) ensures r == body_matches(parent, body@) {
    let mut i = 0usize;
    while i < body.len()
        invariant i <= body.len(), forall|j: int| 0 <= j < i ==> (#[trigger] body@[j]).location.kind == Kind::Inline && body@[j].location.owner == parent as u64,
        decreases body.len() - i,
    {
        if !matches!(body[i].location.kind, Kind::Inline) || body[i].location.owner != parent as u64 { return false; }
        i += 1;
    }
    true
}
fn external_is_one_block(external: &[Reference]) -> (r: bool) ensures r == external_matches(external@) {
    let mut i = 0usize;
    while i < external.len()
        invariant i <= external.len(), forall|j: int| 0 <= j < i ==> (#[trigger] external@[j]).location.kind == Kind::External && external@[j].location.owner == external@[0].location.owner,
        decreases external.len() - i,
    {
        if !matches!(external[i].location.kind, Kind::External) || external[i].location.owner != external[0].location.owner { return false; }
        i += 1;
    }
    true
}
fn append_logical(mut logical: Vec<ParentReference>, parent: u32, incoming: &[Reference]) -> (r: Option<Vec<ParentReference>>)
    requires logical.len() <= ea_refs::MAX_RECORDS,
    ensures match r { Some(records) => records.len() <= ea_refs::MAX_RECORDS && records@ == logical@ + logical_entries(parent, incoming@), None => true },
{
    if incoming.len() > ea_refs::MAX_RECORDS - logical.len() { return None; }
    let ghost before = logical@; let mut i = 0usize;
    while i < incoming.len()
        invariant i <= incoming.len(), before.len() + incoming.len() <= ea_refs::MAX_RECORDS, logical@ == before + logical_entries(parent, incoming@.take(i as int)),
        decreases incoming.len() - i,
    {
        logical.push(ParentReference { parent, physical: incoming[i] });
        assert(logical@ =~= before + logical_entries(parent, incoming@.take(i as int + 1))); i += 1;
    }
    assert(incoming@.take(i as int) =~= incoming@); Some(logical)
}

pub struct Graph { physical: Ledger, logical: Vec<ParentReference>, parents: Vec<u32>, inputs: Ghost<Seq<Input>> }
impl Graph {
    pub closed spec fn view(&self) -> GraphView {
        GraphView { physical: self.physical.view(), logical: self.logical@, parents: self.parents@, inputs: self.inputs@ }
    }
    pub closed spec fn wf(&self) -> bool { valid(self.view()) && self.physical.wf() }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn new() -> (r: Self) ensures r.wf(), valid(r.view()), r.view().inputs == Seq::<Input>::empty() {
        let physical = Ledger::new(); let logical = Vec::new(); let parents = Vec::new();
        let ghost inputs = Seq::<Input>::empty();
        assert(physical.view() =~= Seq::<Reference>::empty());
        assert(logical@ =~= Seq::<ParentReference>::empty());
        assert(parents@ =~= Seq::<u32>::empty());
        assert(ea_refs::valid(physical.view()));
        assert(ea_refs::logical_valid(logical@)) by { reveal(ea_refs::logical_valid); }
        assert(valid(GraphView { physical: physical.view(), logical: logical@, parents: parents@, inputs })) by {
            reveal(valid);
            reveal_with_fuel(physical_projection, 1);
            reveal_with_fuel(logical_projection, 1);
            assert(inputs.len() == 0);
            assert(parent_numbers(inputs) =~= parents@);
            assert(physical_projection(inputs) == physical.view());
            assert(logical_projection(inputs) == logical@);
        }
        Graph { physical, logical, parents, inputs: Ghost(inputs) }
    }
    pub fn physical(&self) -> (r: &Ledger) ensures self.wf(), r.wf(), r.view() == self.view().physical {
        proof { use_type_invariant(self); } &self.physical
    }
    pub fn logical(&self) -> (r: &[ParentReference]) ensures self.wf(), r@ == self.view().logical {
        proof { use_type_invariant(self); } &self.logical
    }
    pub fn parents(&self) -> (r: &[u32]) ensures self.wf(), r@ == self.view().parents {
        proof { use_type_invariant(self); } &self.parents
    }
    pub fn add_parent(self, parent: u32, body: &[Reference], external: &[Reference]) -> (r: Result<Self, (Self, Error)>)
        ensures self.wf(), match r {
            Ok(next) => next.wf() && valid(next.view()) && next.view().inputs == self.view().inputs.push(Input { parent, body: body@, external: external@ })
                && next.view().parents == self.view().parents.push(parent)
                && next.view().physical == appended_physical(appended_physical(self.view().physical, body@), external@)
                && next.view().logical == self.view().logical + logical_entries(parent, body@) + logical_entries(parent, external@),
            Err((original, _)) => original.wf() && original.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); reveal(valid); reveal(ea_refs::logical_valid); }
        if parent == 0 { return Err((self, Error::InvalidParent)); }
        if body.len() == 0 && external.len() == 0 || body.len() > MAX_PARENT_ENTRIES || external.len() > MAX_PARENT_ENTRIES { return Err((self, Error::InvalidBody)); }
        if self.parents.len() >= MAX_PARENTS { return Err((self, Error::ParentLimit)); }
        let ghost old = self.view(); let mut i = 0usize;
        while i < self.parents.len()
            invariant self.wf(), i <= self.parents.len(), forall|j: int| 0 <= j < i ==> #[trigger] self.view().parents[j] != parent,
            decreases self.parents.len() - i,
        {
            if self.parents[i] == parent { return Err((self, Error::DuplicateParent)); }
            i += 1;
        }
        let body_ledger = match Ledger::from_records(body) { Some(ledger) => ledger, None => { return Err((self, Error::InvalidBody)); } };
        if !body_is_for_parent(body, parent) { return Err((self, Error::InvalidBody)); }
        let external_ledger = match Ledger::from_records(external) { Some(ledger) => ledger, None => { return Err((self, Error::InvalidExternal)); } };
        if !external_is_one_block(external) { return Err((self, Error::InvalidExternal)); }
        let physical = match Ledger::from_records(self.physical.records()) { Some(ledger) => ledger, None => { return Err((self, Error::InconsistentReference)); } };
        let body_physical = match merge_references(physical, body) { Ok(ledger) => ledger, Err(error) => { return Err((self, error)); } };
        let ghost middle = body_physical.view();
        let physical = match merge_references(body_physical, external) { Ok(ledger) => ledger, Err(error) => { return Err((self, error)); } };
        let mut logical = Vec::new(); i = 0;
        while i < self.logical.len()
            invariant self.wf(), i <= self.logical.len(), logical@ == old.logical.take(i as int), old == self.view(),
            decreases self.logical.len() - i,
        { logical.push(self.logical[i]); assert(logical@ =~= old.logical.take(i as int + 1)); i += 1; }
        assert(old.logical.take(i as int) =~= old.logical);
        proof { reveal(valid); reveal(ea_refs::logical_valid); }
        let logical = match append_logical(logical, parent, body) { Some(records) => records, None => { return Err((self, Error::ReferenceLimit)); } };
        let logical = match append_logical(logical, parent, external) { Some(records) => records, None => { return Err((self, Error::ReferenceLimit)); } };
        if ea_refs::quota_usage(&logical, parent, 1).is_none() { return Err((self, Error::InvalidQuotaProjection)); }
        let mut parents = Vec::new(); i = 0;
        while i < self.parents.len()
            invariant self.wf(), i <= self.parents.len() < MAX_PARENTS, parents@ == old.parents.take(i as int), old == self.view(),
            decreases self.parents.len() - i,
        { parents.push(self.parents[i]); assert(parents@ =~= old.parents.take(i as int + 1)); i += 1; }
        assert(old.parents.take(i as int) =~= old.parents); parents.push(parent);
        let ghost input = Input { parent, body: body@, external: external@ };
        proof {
            reveal(valid); reveal(ea_refs::logical_valid);
            assert(input_good(input));
            assert(old.inputs.push(input).drop_last() =~= old.inputs);
            assert(old.inputs.push(input).last() == input);
            assert(parents@ =~= parent_numbers(old.inputs.push(input)));
            assert forall|j: int| 0 <= j < old.inputs.push(input).len() implies #[trigger] input_good(old.inputs.push(input)[j]) by {
                if j < old.inputs.len() { assert(input_good(old.inputs[j])); }
            }
            assert forall|a: int, b: int| 0 <= a < b < parents.len() implies #[trigger] parents@[a] != #[trigger] parents@[b] by {
                if b < old.parents.len() { assert(old.parents[a] != old.parents[b]); }
            }
            nested_prefixes_compose(old.physical, middle, physical.view());
            assert forall|j: int| 0 <= j < logical.len() implies #[trigger] contains_record(physical.view(), logical@[j].physical) by {
                if j < old.logical.len() {
                    assert(logical@[j] == old.logical[j]);
                    a_member_survives_a_prefix(old.physical, physical.view(), old.logical[j].physical);
                } else if j < old.logical.len() + body.len() {
                    let k = j - old.logical.len(); assert(logical@[j].physical == body@[k]);
                    a_member_survives_a_prefix(middle, physical.view(), body@[k]);
                } else {
                    let k = j - old.logical.len() - body.len(); assert(logical@[j].physical == external@[k]);
                    assert(contains_record(physical.view(), external@[k]));
                }
            }
            assert(valid(GraphView { physical: physical.view(), logical: logical@, parents: parents@, inputs: old.inputs.push(input) }));
        }
        Ok(Graph { physical, logical, parents, inputs: Ghost(old.inputs.push(input)) })
    }
}

pub proof fn every_projected_logical_ea_reference_has_its_exact_physical_entry(v: GraphView, i: int)
    requires valid(v), 0 <= i < v.logical.len(),
    ensures contains_record(v.physical, v.logical[i].physical),
{ reveal(valid); }
pub proof fn projected_parents_are_never_counted_twice(v: GraphView, first: int, second: int)
    requires valid(v), 0 <= first < v.parents.len(), 0 <= second < v.parents.len(), v.parents[first] == v.parents[second],
    ensures first == second,
{ reveal(valid); }
pub proof fn projected_shared_external_entries_have_one_physical_location(v: GraphView, first: int, second: int)
    requires valid(v), 0 <= first < v.physical.len(), 0 <= second < v.physical.len(),
        ea_refs::same_location(v.physical[first].location, v.physical[second].location),
    ensures first == second,
{ reveal(valid); reveal(ea_refs::valid); }
pub proof fn graph_quota_input_is_the_complete_logical_parent_projection(v: GraphView)
    requires valid(v),
    ensures ea_refs::logical_valid(v.logical), v.logical == logical_projection(v.inputs), v.physical == physical_projection(v.inputs),
{ reveal(valid); }

}
