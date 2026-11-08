// SPDX-License-Identifier: MPL-2.0

//! Bounded EA_INODE physical-reference and per-parent quota accounting.
//! Records are caller-supplied data, not authenticated disk-census certificates.
//! A distinct inode-body entry or external-block entry contributes one physical
//! reference. An external block's h_refcount is deliberately not an input.

use alloc::vec::Vec;

use vstd::prelude::*;

verus! {

pub const MAX_RECORDS: usize = 4096;
pub const MAX_VALUE: u32 = 16777216;

#[derive(Clone, Copy)]
pub enum Kind { Inline, External }
#[derive(Clone, Copy)]
pub struct Location { pub kind: Kind, pub owner: u64, pub offset: u32 }
#[derive(Clone, Copy)]
pub struct Reference { pub location: Location, pub value: u32, pub size: u32 }

pub open spec fn same_location(a: Location, b: Location) -> bool {
    a.kind == b.kind && a.owner == b.owner && a.offset == b.offset
}
pub open spec fn good_location(location: Location) -> bool {
    0 < location.owner <= 4294967295 && location.offset % 4 == 0
        && match location.kind {
            Kind::Inline => 160 <= location.offset <= 236,
            Kind::External => 32 <= location.offset <= 4076,
        }
}
pub open spec fn good(reference: Reference) -> bool {
    good_location(reference.location) && reference.value > 0 && 0 < reference.size <= MAX_VALUE
}
#[verifier::opaque]
pub open spec fn valid(records: Seq<Reference>) -> bool {
    records.len() <= MAX_RECORDS && (forall|i: int| 0 <= i < records.len() ==> #[trigger] good(records[i]))
        && forall|i: int, j: int| 0 <= i < j < records.len() ==> !same_location((#[trigger] records[i]).location, (#[trigger] records[j]).location)
            && (records[i].value == records[j].value ==> records[i].size == records[j].size)
}
pub open spec fn lookup_index(records: Seq<Reference>, location: Location) -> Option<int> {
    if exists|i: int| 0 <= i < records.len() && same_location((#[trigger] records[i]).location, location) {
        Some(choose|i: int| 0 <= i < records.len() && same_location((#[trigger] records[i]).location, location))
    } else { None }
}
pub open spec fn deleted(records: Seq<Reference>, location: Location) -> Seq<Reference> {
    match lookup_index(records, location) { Some(i) => records.remove(i), None => records }
}
pub open spec fn references_to(records: Seq<Reference>, value: u32) -> nat decreases records.len() {
    if records.len() == 0 { 0nat }
    else { references_to(records.drop_last(), value) + if records.last().value == value { 1nat } else { 0nat } }
}
pub open spec fn from_block(reference: Reference, block: u64) -> bool {
    reference.location.kind == Kind::External && reference.location.owner == block
}
pub open spec fn relocated(reference: Reference, block: u64) -> Reference {
    Reference { location: Location { kind: Kind::External, owner: block, offset: reference.location.offset }, value: reference.value, size: reference.size }
}
pub open spec fn copied_entries(records: Seq<Reference>, source: u64, destination: u64) -> Seq<Reference> decreases records.len() {
    if records.len() == 0 { Seq::empty() }
    else if from_block(records.last(), source) { copied_entries(records.drop_last(), source, destination).push(relocated(records.last(), destination)) }
    else { copied_entries(records.drop_last(), source, destination) }
}
pub open spec fn references_from_block(records: Seq<Reference>, block: u64, value: u32) -> nat decreases records.len() {
    if records.len() == 0 { 0nat }
    else { references_from_block(records.drop_last(), block, value) + if from_block(records.last(), block) && records.last().value == value { 1nat } else { 0nat } }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Error { InvalidReference, DuplicateLocation, ConflictingSize, Missing, Limit, InvalidBlock, DestinationOccupied }

fn equal_location(a: Location, b: Location) -> (r: bool) ensures r == same_location(a, b) {
    let kind = match (a.kind, b.kind) { (Kind::Inline, Kind::Inline) => true, (Kind::External, Kind::External) => true, _ => false };
    kind && a.owner == b.owner && a.offset == b.offset
}
fn valid_reference(reference: Reference) -> (r: bool) ensures r == good(reference) {
    let location = reference.location;
    let offset_ok = match location.kind { Kind::Inline => 160 <= location.offset && location.offset <= 236, Kind::External => 32 <= location.offset && location.offset <= 4076 };
    location.owner > 0 && location.owner <= 4294967295 && location.offset % 4 == 0 && offset_ok && reference.value > 0 && reference.size > 0 && reference.size <= MAX_VALUE
}
proof fn a_bad_physical_record_rejects_the_complete_ledger(records: Seq<Reference>, index: int)
    requires 0 <= index < records.len(), !good(records[index]),
    ensures !valid(records),
{
    reveal(valid);
    if valid(records) { assert(good(records[index])); }
}
proof fn a_bad_physical_pair_rejects_the_complete_ledger(records: Seq<Reference>, first: int, second: int)
    requires 0 <= first < second < records.len(),
        same_location(records[first].location, records[second].location)
            || records[first].value == records[second].value && records[first].size != records[second].size,
    ensures !valid(records),
{
    reveal(valid);
    if valid(records) {
        assert(!same_location(records[first].location, records[second].location)
            && (records[first].value == records[second].value ==> records[first].size == records[second].size));
    }
}
proof fn a_complete_location_identifies_one_physical_record(records: Seq<Reference>, first: int, second: int, location: Location)
    requires valid(records), 0 <= first < records.len(), 0 <= second < records.len(),
        same_location(records[first].location, location), same_location(records[second].location, location),
    ensures first == second,
{
    reveal(valid);
    if first < second {
        assert(!same_location(records[first].location, records[second].location));
        assert(same_location(records[first].location, records[second].location));
    } else if second < first {
        assert(!same_location(records[second].location, records[first].location));
        assert(same_location(records[second].location, records[first].location));
    }
}
fn validate(records: &[Reference]) -> (r: bool) ensures r == valid(records@) {
    reveal(valid);
    if records.len() > MAX_RECORDS { return false; }
    let mut i = 0usize;
    while i < records.len()
        invariant i <= records.len() <= MAX_RECORDS,
            forall|a: int| 0 <= a < i ==> #[trigger] good(records@[a]),
            forall|a: int, b: int| 0 <= a < b < i ==> !same_location((#[trigger] records@[a]).location, (#[trigger] records@[b]).location)
                && (records@[a].value == records@[b].value ==> records@[a].size == records@[b].size),
        decreases records.len() - i,
    {
        let current = records[i];
        if !valid_reference(current) {
            proof { a_bad_physical_record_rejects_the_complete_ledger(records@, i as int); }
            return false;
        }
        let mut j = 0usize;
        while j < i
            invariant i < records.len() <= MAX_RECORDS, j <= i, current == records@[i as int], good(current),
                forall|a: int| 0 <= a < i ==> #[trigger] good(records@[a]),
                forall|a: int, b: int| 0 <= a < b < i ==> !same_location((#[trigger] records@[a]).location, (#[trigger] records@[b]).location)
                    && (records@[a].value == records@[b].value ==> records@[a].size == records@[b].size),
                forall|a: int| 0 <= a < j ==> !same_location((#[trigger] records@[a]).location, current.location)
                    && (records@[a].value == current.value ==> records@[a].size == current.size),
            decreases i - j,
        {
            let previous = records[j];
            if equal_location(previous.location, current.location) || previous.value == current.value && previous.size != current.size {
                proof { a_bad_physical_pair_rejects_the_complete_ledger(records@, j as int, i as int); }
                return false;
            }
            j += 1;
        }
        assert forall|a: int, b: int| 0 <= a < b < i + 1 implies !same_location((#[trigger] records@[a]).location, (#[trigger] records@[b]).location)
            && (records@[a].value == records@[b].value ==> records@[a].size == records@[b].size) by {
            if b < i { assert(!same_location(records@[a].location, records@[b].location)); }
        }
        i += 1;
    }
    true
}
fn copy(records: &[Reference]) -> (r: Vec<Reference>) requires records.len() <= MAX_RECORDS, ensures r@ == records@ {
    let mut result = Vec::new(); let mut i = 0usize;
    while i < records.len() invariant i <= records.len() <= MAX_RECORDS, result@ == records@.take(i as int), decreases records.len() - i,
    { result.push(records[i]); assert(result@ =~= records@.take(i as int + 1)); i += 1; }
    result
}
fn is_from_block(reference: Reference, block: u64) -> (r: bool) ensures r == from_block(reference, block) {
    matches!(reference.location.kind, Kind::External) && reference.location.owner == block
}

pub struct Ledger { records: Vec<Reference> }
impl Ledger {
    pub closed spec fn view(&self) -> Seq<Reference> { self.records@ }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn new() -> (r: Self) ensures r.wf(), r.view().len() == 0 {
        let records = Vec::new(); assert(valid(records@)) by { reveal(valid); } Ledger { records }
    }
    pub fn from_records(records: &[Reference]) -> (r: Option<Self>)
        ensures match r { Some(ledger) => ledger.wf() && ledger.view() == records@, None => true },
    {
        if !validate(records) { return None; }
        proof { reveal(valid); }
        Some(Ledger { records: copy(records) })
    }
    pub fn len(&self) -> (r: usize) ensures self.wf(), r == self.view().len(), r <= MAX_RECORDS {
        proof { use_type_invariant(self); reveal(valid); } self.records.len()
    }
    pub fn records(&self) -> (r: &[Reference]) ensures self.wf(), r@ == self.view() {
        proof { use_type_invariant(self); } &self.records
    }
    pub fn at(&self, i: usize) -> (r: Option<Reference>)
        ensures self.wf(), match r { Some(reference) => i < self.view().len() && reference == self.view()[i as int], None => i >= self.view().len() },
    {
        proof { use_type_invariant(self); }
        if i < self.records.len() { Some(self.records[i]) } else { None }
    }
    pub fn refs(&self, value: u32) -> (r: u64) ensures self.wf(), r as nat == references_to(self.view(), value), r <= MAX_RECORDS as u64 {
        proof { use_type_invariant(self); reveal(valid); }
        let mut i = 0usize; let mut count = 0u64;
        while i < self.records.len()
            invariant self.wf(), i <= self.records.len() <= MAX_RECORDS, count as nat <= i,
                count as nat == references_to(self.view().take(i as int), value),
            decreases self.records.len() - i,
        {
            if self.records[i].value == value { count += 1; }
            assert(self.view().take(i as int + 1).drop_last() =~= self.view().take(i as int));
            assert(self.view().take(i as int + 1).last() == self.view()[i as int]); i += 1;
        }
        assert(self.view().take(i as int) =~= self.view()); count
    }
    fn locate(&self, location: Location) -> (r: Option<usize>)
        ensures self.wf(), match r { Some(i) => lookup_index(self.view(), location) == Some(i as int), None => lookup_index(self.view(), location).is_none() },
    {
        proof { use_type_invariant(self); reveal(valid); }
        let mut i = 0usize;
        while i < self.records.len()
            invariant self.wf(), i <= self.records.len(),
                forall|j: int| 0 <= j < i ==> !same_location((#[trigger] self.view()[j]).location, location),
            decreases self.records.len() - i,
        {
            if equal_location(self.records[i].location, location) {
                assert(exists|j: int| 0 <= j < self.view().len() && same_location((#[trigger] self.view()[j]).location, location));
                assert(lookup_index(self.view(), location).is_some());
                proof {
                    let k = lookup_index(self.view(), location).unwrap();
                    a_complete_location_identifies_one_physical_record(self.view(), i as int, k, location);
                    assert(k == i);
                }
                return Some(i);
            }
            i += 1;
        }
        None
    }
    pub fn add(self, reference: Reference) -> (r: Result<Self, (Self, Error)>)
        ensures self.wf(), match r {
            Ok(next) => next.wf() && next.view() == self.view().push(reference),
            Err((original, _)) => original.wf() && original.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); reveal(valid); }
        if !valid_reference(reference) { return Err((self, Error::InvalidReference)); }
        if self.locate(reference.location).is_some() { return Err((self, Error::DuplicateLocation)); }
        if self.records.len() >= MAX_RECORDS { return Err((self, Error::Limit)); }
        let mut i = 0usize;
        while i < self.records.len() invariant self.wf(), i <= self.records.len(), decreases self.records.len() - i,
        {
            if self.records[i].value == reference.value && self.records[i].size != reference.size { return Err((self, Error::ConflictingSize)); }
            i += 1;
        }
        let mut records = copy(&self.records); records.push(reference);
        if !validate(&records) { return Err((self, Error::InvalidReference)); }
        Ok(Ledger { records })
    }
    pub fn remove(self, location: Location) -> (r: Result<Self, (Self, Error)>)
        ensures self.wf(), match r {
            Ok(next) => next.wf() && lookup_index(self.view(), location).is_some() && next.view() == deleted(self.view(), location),
            Err((original, _)) => original.wf() && original.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); reveal(valid); }
        let i = match self.locate(location) { Some(i) => i, None => { return Err((self, Error::Missing)); } };
        let mut records = copy(&self.records); records.remove(i);
        if !validate(&records) { return Err((self, Error::InvalidReference)); }
        Ok(Ledger { records })
    }
    pub fn clone_external(self, source: u64, destination: u64) -> (r: Result<Self, (Self, Error)>)
        ensures self.wf(), match r {
            Ok(next) => next.wf() && source != destination && next.view() == self.view() + copied_entries(self.view(), source, destination),
            Err((original, _)) => original.wf() && original.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); reveal(valid); }
        if source == 0 || source > 4294967295 || destination == 0 || destination > 4294967295 || source == destination { return Err((self, Error::InvalidBlock)); }
        let mut i = 0usize;
        while i < self.records.len() invariant self.wf(), i <= self.records.len(), decreases self.records.len() - i,
        {
            if is_from_block(self.records[i], destination) { return Err((self, Error::DestinationOccupied)); }
            i += 1;
        }
        let mut records = copy(&self.records); i = 0;
        assert(copied_entries(self.view().take(0), source, destination) =~= Seq::<Reference>::empty());
        assert(records@ =~= self.view() + copied_entries(self.view().take(0), source, destination));
        while i < self.records.len()
            invariant self.wf(), i <= self.records.len() <= MAX_RECORDS, records.len() <= MAX_RECORDS,
                records@ == self.view() + copied_entries(self.view().take(i as int), source, destination),
            decreases self.records.len() - i,
        {
            let reference = self.records[i];
            assert(self.view().take(i as int + 1).drop_last() =~= self.view().take(i as int));
            assert(self.view().take(i as int + 1).last() == reference);
            if is_from_block(reference, source) {
                if records.len() >= MAX_RECORDS { return Err((self, Error::Limit)); }
                let next = Reference { location: Location { kind: Kind::External, owner: destination, offset: reference.location.offset }, value: reference.value, size: reference.size };
                records.push(next);
                assert(next == relocated(reference, destination));
                assert(records@ =~= self.view() + copied_entries(self.view().take(i as int + 1), source, destination));
            }
            i += 1;
        }
        assert(self.view().take(i as int) =~= self.view());
        if !validate(&records) { return Err((self, Error::InvalidReference)); }
        Ok(Ledger { records })
    }
}

pub proof fn adding_one_physical_entry_changes_only_its_value_count(records: Seq<Reference>, reference: Reference, value: u32)
    ensures references_to(records.push(reference), value) == references_to(records, value) + if reference.value == value { 1nat } else { 0nat },
{ assert(records.push(reference).drop_last() =~= records); }
pub proof fn removing_one_physical_entry_changes_only_its_value_count(records: Seq<Reference>, index: int, value: u32)
    requires 0 <= index < records.len(),
    ensures references_to(records.remove(index), value) + if records[index].value == value { 1nat } else { 0nat } == references_to(records, value),
    decreases records.len(),
{
    if index == records.len() - 1 { assert(records.remove(index) =~= records.drop_last()); }
    else {
        removing_one_physical_entry_changes_only_its_value_count(records.drop_last(), index, value);
        assert(records.remove(index).drop_last() =~= records.drop_last().remove(index));
        assert(records.remove(index).last() == records.last());
    }
}
proof fn concatenated_counts(a: Seq<Reference>, b: Seq<Reference>, value: u32)
    ensures references_to(a + b, value) == references_to(a, value) + references_to(b, value),
    decreases b.len(),
{
    if b.len() == 0 { assert(a + b =~= a); }
    else { concatenated_counts(a, b.drop_last(), value); assert((a + b).drop_last() =~= a + b.drop_last()); assert((a + b).last() == b.last()); }
}
proof fn copied_counts(records: Seq<Reference>, source: u64, destination: u64, value: u32)
    ensures references_to(copied_entries(records, source, destination), value) == references_from_block(records, source, value),
    decreases records.len(),
{
    if records.len() > 0 {
        copied_counts(records.drop_last(), source, destination, value);
        if from_block(records.last(), source) {
            adding_one_physical_entry_changes_only_its_value_count(copied_entries(records.drop_last(), source, destination), relocated(records.last(), destination), value);
        }
    }
}
pub proof fn cloning_an_external_block_adds_each_physical_ea_entry_once(records: Seq<Reference>, source: u64, destination: u64, value: u32)
    ensures references_to(records + copied_entries(records, source, destination), value)
        == references_to(records, value) + references_from_block(records, source, value),
{
    concatenated_counts(records, copied_entries(records, source, destination), value);
    copied_counts(records, source, destination, value);
}
pub proof fn one_shared_external_entry_is_one_physical_reference(reference: Reference)
    requires reference.location.kind == Kind::External,
    ensures references_to(seq![reference], reference.value) == 1,
{
    reveal_with_fuel(references_to, 2);
    let singleton = seq![reference];
    assert(singleton.len() == 1);
    assert(singleton.last() == reference);
    assert(singleton.drop_last() =~= Seq::<Reference>::empty());
    assert(references_to(Seq::<Reference>::empty(), reference.value) == 0);
}

// Each logical parent is charged even when its external block and EA inode
// are shared. These are EA additions to quota, excluding the parent's own inode.
#[derive(Clone, Copy)]
pub struct ParentReference { pub parent: u32, pub physical: Reference }
pub open spec fn parent_good(reference: ParentReference) -> bool {
    reference.parent > 0 && good(reference.physical)
        && (reference.physical.location.kind == Kind::Inline ==> reference.physical.location.owner == reference.parent as u64)
}
#[verifier::opaque]
pub open spec fn logical_valid(records: Seq<ParentReference>) -> bool {
    records.len() <= MAX_RECORDS && (forall|i: int| 0 <= i < records.len() ==> #[trigger] parent_good(records[i]))
        && forall|i: int, j: int| 0 <= i < j < records.len() ==>
            !((#[trigger] records[i]).parent == (#[trigger] records[j]).parent && same_location(records[i].physical.location, records[j].physical.location))
            && (same_location(records[i].physical.location, records[j].physical.location) ==> records[i].physical.value == records[j].physical.value && records[i].physical.size == records[j].physical.size)
            && (records[i].physical.value == records[j].physical.value ==> records[i].physical.size == records[j].physical.size)
}
pub open spec fn rounded_size(size: u32, cluster: u32) -> nat {
    if cluster == 0 { 0nat } else { (((size as int + cluster as int - 1) / cluster as int) * cluster as int) as nat }
}
pub open spec fn parent_count(records: Seq<ParentReference>, parent: u32) -> nat decreases records.len() {
    if records.len() == 0 { 0nat } else { parent_count(records.drop_last(), parent) + if records.last().parent == parent { 1nat } else { 0nat } }
}
pub open spec fn parent_bytes(records: Seq<ParentReference>, parent: u32, cluster: u32) -> nat decreases records.len() {
    if records.len() == 0 { 0nat }
    else { parent_bytes(records.drop_last(), parent, cluster) + if records.last().parent == parent { rounded_size(records.last().physical.size, cluster) } else { 0nat } }
}
pub struct Usage { pub ea_inodes: u64, pub bytes: u64 }

fn valid_parent(reference: ParentReference) -> (r: bool) ensures r == parent_good(reference) {
    reference.parent > 0 && valid_reference(reference.physical)
        && (!matches!(reference.physical.location.kind, Kind::Inline) || reference.physical.location.owner == reference.parent as u64)
}
proof fn a_bad_logical_record_rejects_the_complete_quota_view(records: Seq<ParentReference>, index: int)
    requires 0 <= index < records.len(), !parent_good(records[index]),
    ensures !logical_valid(records),
{
    reveal(logical_valid);
    if logical_valid(records) { assert(parent_good(records[index])); }
}
proof fn a_bad_logical_pair_rejects_the_complete_quota_view(records: Seq<ParentReference>, first: int, second: int)
    requires 0 <= first < second < records.len(),
        records[first].parent == records[second].parent && same_location(records[first].physical.location, records[second].physical.location)
            || same_location(records[first].physical.location, records[second].physical.location)
                && (records[first].physical.value != records[second].physical.value || records[first].physical.size != records[second].physical.size)
            || records[first].physical.value == records[second].physical.value && records[first].physical.size != records[second].physical.size,
    ensures !logical_valid(records),
{
    reveal(logical_valid);
    if logical_valid(records) {
        assert(!(records[first].parent == records[second].parent && same_location(records[first].physical.location, records[second].physical.location))
            && (same_location(records[first].physical.location, records[second].physical.location) ==> records[first].physical.value == records[second].physical.value && records[first].physical.size == records[second].physical.size)
            && (records[first].physical.value == records[second].physical.value ==> records[first].physical.size == records[second].physical.size));
    }
}
fn validate_logical(records: &[ParentReference]) -> (r: bool) ensures r == logical_valid(records@) {
    reveal(logical_valid);
    if records.len() > MAX_RECORDS { return false; }
    let mut i = 0usize;
    while i < records.len()
        invariant i <= records.len() <= MAX_RECORDS,
            forall|a: int| 0 <= a < i ==> #[trigger] parent_good(records@[a]),
            forall|a: int, b: int| 0 <= a < b < i ==> !((#[trigger] records@[a]).parent == (#[trigger] records@[b]).parent && same_location(records@[a].physical.location, records@[b].physical.location))
                && (same_location(records@[a].physical.location, records@[b].physical.location) ==> records@[a].physical.value == records@[b].physical.value && records@[a].physical.size == records@[b].physical.size)
                && (records@[a].physical.value == records@[b].physical.value ==> records@[a].physical.size == records@[b].physical.size),
        decreases records.len() - i,
    {
        let current = records[i];
        if !valid_parent(current) {
            proof { a_bad_logical_record_rejects_the_complete_quota_view(records@, i as int); }
            return false;
        }
        let mut j = 0usize;
        while j < i
            invariant i < records.len() <= MAX_RECORDS, j <= i, current == records@[i as int], parent_good(current),
                forall|a: int| 0 <= a < i ==> #[trigger] parent_good(records@[a]),
                forall|a: int, b: int| 0 <= a < b < i ==> !((#[trigger] records@[a]).parent == (#[trigger] records@[b]).parent && same_location(records@[a].physical.location, records@[b].physical.location))
                    && (same_location(records@[a].physical.location, records@[b].physical.location) ==> records@[a].physical.value == records@[b].physical.value && records@[a].physical.size == records@[b].physical.size)
                    && (records@[a].physical.value == records@[b].physical.value ==> records@[a].physical.size == records@[b].physical.size),
                forall|a: int| 0 <= a < j ==> !((#[trigger] records@[a]).parent == current.parent && same_location(records@[a].physical.location, current.physical.location))
                    && (same_location(records@[a].physical.location, current.physical.location) ==> records@[a].physical.value == current.physical.value && records@[a].physical.size == current.physical.size)
                    && (records@[a].physical.value == current.physical.value ==> records@[a].physical.size == current.physical.size),
            decreases i - j,
        {
            let previous = records[j]; let same = equal_location(previous.physical.location, current.physical.location);
            if previous.parent == current.parent && same || same && (previous.physical.value != current.physical.value || previous.physical.size != current.physical.size)
                || previous.physical.value == current.physical.value && previous.physical.size != current.physical.size {
                proof { a_bad_logical_pair_rejects_the_complete_quota_view(records@, j as int, i as int); }
                return false;
            }
            j += 1;
        }
        assert forall|a: int, b: int| 0 <= a < b < i + 1 implies !((#[trigger] records@[a]).parent == (#[trigger] records@[b]).parent && same_location(records@[a].physical.location, records@[b].physical.location))
            && (same_location(records@[a].physical.location, records@[b].physical.location) ==> records@[a].physical.value == records@[b].physical.value && records@[a].physical.size == records@[b].physical.size)
            && (records@[a].physical.value == records@[b].physical.value ==> records@[a].physical.size == records@[b].physical.size) by {
            if b < i { assert(!(records@[a].parent == records@[b].parent && same_location(records@[a].physical.location, records@[b].physical.location))); }
        }
        i += 1;
    }
    true
}
fn rounded(size: u32, cluster: u32) -> (r: Option<u64>)
    ensures match r { Some(amount) => cluster > 0 && amount as nat == rounded_size(size, cluster), None => true },
{
    if cluster == 0 { return None; }
    let numerator = size as u64 + cluster as u64 - 1;
    let units = numerator / cluster as u64;
    let q = units as u128; let c = cluster as u128;
    assert(q as int * c as int <= 79228162514264337593543950336int) by (nonlinear_arith)
        requires 0 <= q <= 18446744073709551615u128, 0 < c <= 4294967295u128;
    let amount = q * c;
    if amount > 18446744073709551615u128 { return None; }
    Some(amount as u64)
}
pub fn quota_usage(records: &[ParentReference], parent: u32, cluster: u32) -> (r: Option<Usage>)
    ensures match r { Some(usage) => parent > 0 && cluster > 0 && logical_valid(records@)
        && usage.ea_inodes as nat == parent_count(records@, parent) && usage.bytes as nat == parent_bytes(records@, parent, cluster), None => true },
{
    if parent == 0 || cluster == 0 || !validate_logical(records) { return None; }
    let mut count = 0u64; let mut total = 0u64; let mut i = 0usize;
    while i < records.len()
        invariant i <= records.len(), parent > 0, cluster > 0, logical_valid(records@),
            count as nat == parent_count(records@.take(i as int), parent), total as nat == parent_bytes(records@.take(i as int), parent, cluster),
        decreases records.len() - i,
    {
        if records[i].parent == parent {
            let amount = match rounded(records[i].physical.size, cluster) { Some(amount) => amount, None => { return None; } };
            if count == 18446744073709551615u64 || amount > 18446744073709551615u64 - total { return None; }
            count += 1; total += amount;
        }
        assert(records@.take(i as int + 1).drop_last() =~= records@.take(i as int));
        assert(records@.take(i as int + 1).last() == records@[i as int]); i += 1;
    }
    assert(records@.take(i as int) =~= records@);
    Some(Usage { ea_inodes: count, bytes: total })
}
pub proof fn a_shared_physical_entry_charges_each_logical_parent(reference: Reference, first: u32, second: u32, cluster: u32)
    requires good(reference), reference.location.kind == Kind::External, first > 0, second > 0, first != second, cluster > 0,
    ensures logical_valid(seq![ParentReference { parent: first, physical: reference }, ParentReference { parent: second, physical: reference }]),
        parent_count(seq![ParentReference { parent: first, physical: reference }, ParentReference { parent: second, physical: reference }], first) == 1,
        parent_count(seq![ParentReference { parent: first, physical: reference }, ParentReference { parent: second, physical: reference }], second) == 1,
        parent_bytes(seq![ParentReference { parent: first, physical: reference }, ParentReference { parent: second, physical: reference }], first, cluster) == rounded_size(reference.size, cluster),
        parent_bytes(seq![ParentReference { parent: first, physical: reference }, ParentReference { parent: second, physical: reference }], second, cluster) == rounded_size(reference.size, cluster),
        references_to(seq![reference], reference.value) == 1,
{
    reveal(logical_valid);
    reveal_with_fuel(parent_count, 3);
    reveal_with_fuel(parent_bytes, 3);
    let a = ParentReference { parent: first, physical: reference }; let b = ParentReference { parent: second, physical: reference };
    let pair = seq![a, b];
    assert(pair.len() == 2);
    assert(pair.last() == b);
    assert(pair.drop_last() =~= seq![a]);
    assert(seq![a].last() == a);
    assert(seq![a].drop_last() =~= Seq::<ParentReference>::empty());
    assert(parent_count(Seq::<ParentReference>::empty(), first) == 0);
    assert(parent_count(Seq::<ParentReference>::empty(), second) == 0);
    assert(parent_bytes(Seq::<ParentReference>::empty(), first, cluster) == 0);
    assert(parent_bytes(Seq::<ParentReference>::empty(), second, cluster) == 0);
    assert(parent_count(seq![a], first) == 1);
    assert(parent_count(seq![a], second) == 0);
    assert(parent_bytes(seq![a], first, cluster) == rounded_size(reference.size, cluster));
    assert(parent_bytes(seq![a], second, cluster) == 0);
    assert(parent_count(pair, first) == 1);
    assert(parent_count(pair, second) == 1);
    assert(parent_bytes(pair, first, cluster) == rounded_size(reference.size, cluster));
    assert(parent_bytes(pair, second, cluster) == rounded_size(reference.size, cluster));
    assert forall|i: int| 0 <= i < pair.len() implies #[trigger] parent_good(pair[i]) by {
        if i == 0 { assert(pair[i] == a); } else { assert(i == 1 && pair[i] == b); }
    }
    assert forall|i: int, j: int| 0 <= i < j < pair.len() implies !((#[trigger] pair[i]).parent == (#[trigger] pair[j]).parent && same_location(pair[i].physical.location, pair[j].physical.location))
        && (same_location(pair[i].physical.location, pair[j].physical.location) ==> pair[i].physical.value == pair[j].physical.value && pair[i].physical.size == pair[j].physical.size)
        && (pair[i].physical.value == pair[j].physical.value ==> pair[i].physical.size == pair[j].physical.size) by {
        assert(i == 0 && j == 1); assert(pair[i] == a && pair[j] == b);
    }
    assert(logical_valid(pair));
    one_shared_external_entry_is_one_physical_reference(reference);

}

pub proof fn physical_reference_counts_are_bounded_by_distinct_entries(records: Seq<Reference>, value: u32)
    ensures references_to(records, value) <= records.len(),
    decreases records.len(),
{
    if records.len() > 0 { physical_reference_counts_are_bounded_by_distinct_entries(records.drop_last(), value); }
}
pub proof fn removing_an_existing_physical_entry_cannot_underflow_its_ea_inode_count(records: Seq<Reference>, index: int)
    requires 0 <= index < records.len(),
    ensures references_to(records, records[index].value) >= 1,
        references_to(records.remove(index), records[index].value) + 1 == references_to(records, records[index].value),
{
    removing_one_physical_entry_changes_only_its_value_count(records, index, records[index].value);
}
pub proof fn detaching_one_shared_parent_leaves_the_other_parent_charge_and_physical_reference(reference: Reference,
    first: u32, second: u32, cluster: u32)
    requires good(reference), reference.location.kind == Kind::External, first > 0, second > 0, first != second, cluster > 0,
    ensures parent_count(seq![ParentReference { parent: second, physical: reference }], first) == 0,
        parent_bytes(seq![ParentReference { parent: second, physical: reference }], first, cluster) == 0,
        parent_count(seq![ParentReference { parent: second, physical: reference }], second) == 1,
        parent_bytes(seq![ParentReference { parent: second, physical: reference }], second, cluster) == rounded_size(reference.size, cluster),
        references_to(seq![reference], reference.value) == 1,
{
    reveal_with_fuel(parent_count, 2);
    reveal_with_fuel(parent_bytes, 2);
    let entry = ParentReference { parent: second, physical: reference };
    let remaining = seq![entry];
    assert(remaining.len() == 1);
    assert(remaining.last() == entry);
    assert(remaining.drop_last() =~= Seq::<ParentReference>::empty());
    assert(parent_count(Seq::<ParentReference>::empty(), first) == 0);
    assert(parent_count(Seq::<ParentReference>::empty(), second) == 0);
    assert(parent_bytes(Seq::<ParentReference>::empty(), first, cluster) == 0);
    assert(parent_bytes(Seq::<ParentReference>::empty(), second, cluster) == 0);
    assert(parent_count(remaining, first) == 0);
    assert(parent_count(remaining, second) == 1);
    assert(parent_bytes(remaining, first, cluster) == 0);
    assert(parent_bytes(remaining, second, cluster) == rounded_size(reference.size, cluster));
    one_shared_external_entry_is_one_physical_reference(reference);
}

}
