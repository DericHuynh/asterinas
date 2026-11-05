// SPDX-License-Identifier: MPL-2.0

//! Complete source-bound EA descriptor projection for one ordinary parent.
//! This read-only object grants no VFS, allocation, count-edit or I/O authority.

use vstd::prelude::*;
use crate::{bytes, ea_refs::{self, Kind, Location, Reference, ParentReference},
    ea_source::{self, Header, Node, NodeView}, inode, xattr::{self, Body, BodyView, Block},
    xattr_entry::Entry, xattr_inode, xattr_table::{self as table, TableView}};

verus! {

pub const MAX_PARENT_ENTRIES: usize = 260;
pub open spec fn huge(v: ea_source::HeaderView) -> bool { bytes::le32(v.source, 1124) as u32 & 8u32 != 0 }
pub open spec fn block_bytes(v: ea_source::HeaderView, address: nat) -> Seq<u8> {
    v.source.subrange(address as int * 4096, (address as int + 1) * 4096)
}
pub open spec fn physical(e: Entry, kind: Kind, owner: u64) -> Reference {
    Reference { location: Location { kind, owner, offset: e.position as u32 }, value: e.value_inode, size: e.value_size }
}
pub open spec fn projection(entries: Seq<Entry>, kind: Kind, owner: u64) -> Seq<Reference> decreases entries.len() {
    if entries.len() == 0 { Seq::empty() }
    else if entries.last().value_inode > 0 { projection(entries.drop_last(), kind, owner).push(physical(entries.last(), kind, owner)) }
    else { projection(entries.drop_last(), kind, owner) }
}
pub open spec fn projectable(entries: Seq<Entry>, kind: Kind, owner: u64, parent: u32) -> bool {
    entries.len() <= MAX_PARENT_ENTRIES && forall|i: int| 0 <= i < entries.len() && (#[trigger] entries[i]).value_inode > 0 ==>
        entries[i].value_inode != parent && ea_refs::good(physical(entries[i], kind, owner))
}
pub struct ParentView { pub node: NodeView, pub body: BodyView, pub external: Option<TableView> }
pub open spec fn address(v: ParentView) -> nat { xattr::inode_address(v.node.raw) }
pub open spec fn body_projection(v: ParentView) -> Seq<Reference> {
    match v.body.table { Some(t) => projection(t.entries, Kind::Inline, v.node.number as u64), None => Seq::empty() }
}
pub open spec fn external_projection(v: ParentView) -> Seq<Reference> {
    match v.external { Some(t) => projection(t.entries, Kind::External, address(v) as u64), None => Seq::empty() }
}
pub open spec fn logical_projection(v: ParentView) -> Seq<ParentReference> {
    let records = body_projection(v) + external_projection(v);
    Seq::new(records.len(), |i: int| ParentReference { parent: v.node.number, physical: records[i] })
}
pub open spec fn external_reference_count(v: ParentView) -> nat {
    match v.external { Some(t) => bytes::le32(t.raw, 4), None => 0nat }
}
#[verifier::opaque]
pub open spec fn valid(v: ParentView) -> bool {
    let h = v.node.header;
    &&& ea_source::node_valid(v.node) && (v.node.number == 2 || v.node.number >= 11)
    &&& inode::metadata_accepted_with_features(v.node.raw, v.node.number, h.inodes, h.seed, huge(h))
    &&& xattr::valid_body(v.body) && v.body.raw == v.node.raw && v.body.ea && v.body.inodes == h.inodes
    &&& match v.body.table { Some(t) => projectable(t.entries, Kind::Inline, v.node.number as u64, v.node.number), None => true }
    &&& match v.external {
        None => address(v) == 0,
        Some(t) => 0 < address(v) < h.blocks && table::valid(t) && t.raw == block_bytes(h, address(v))
            && t.first == 32 && t.base == 0 && t.sorted && t.ea && t.inodes == h.inodes
            && xattr::header(t.raw, address(v) as u64, h.seed, true) && xattr_inode::disjoint(v.body, t)
            && projectable(t.entries, Kind::External, address(v) as u64, v.node.number),
    }
    &&& body_projection(v).len() + external_projection(v).len() <= MAX_PARENT_ENTRIES
}

pub struct Parent<'a> {
    node: Node<'a>, body: Body<'a>, external: Option<Block<'a>>, address: u32, references: u32,
    body_records: Vec<Reference>, external_records: Vec<Reference>, checked: Ghost<ParentView>,
}
impl<'a> Parent<'a> {
    pub closed spec fn view(&self) -> ParentView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        valid(self.view()) && self.node.view() == self.view().node && self.body.view() == self.view().body
            && self.view().external == match &self.external { Some(block) => Some(block.view()), None => None }
            && self.address as nat == address(self.view()) && self.references as nat == external_reference_count(self.view())
            && self.body_records@ == body_projection(self.view()) && self.external_records@ == external_projection(self.view())
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn node(&self) -> (r: &Node<'a>)
        ensures self.wf(), valid(self.view()), r.wf(), ea_source::node_valid(r.view()), r.view() == self.view().node,
    { proof { use_type_invariant(self); reveal(valid); } let _ = self.node.number(); &self.node }
    pub fn external_address(&self) -> (r: u32)
        ensures self.wf(), valid(self.view()), r as nat == address(self.view()),
    { proof { use_type_invariant(self); } self.address }
    pub fn external_refs(&self) -> (r: u32)
        ensures self.wf(), valid(self.view()), r as nat == external_reference_count(self.view()),
    { proof { use_type_invariant(self); } self.references }
    pub fn source_tables(&self) -> (r: (Option<&table::Table<'a>>, Option<&table::Table<'a>>))
        ensures self.wf(), valid(self.view()),
            match r.0 { Some(table) => table.wf() && self.view().body.table == Some(table.view()), None => self.view().body.table is None },
            match r.1 { Some(table) => table.wf() && self.view().external == Some(table.view()), None => self.view().external is None },
    {
        proof { use_type_invariant(self); }
        let body = self.body.entry_table();
        let external = match &self.external { Some(block) => Some(block.entries()), None => None };
        (body, external)
    }
    pub fn body_records(&self) -> (r: Option<Vec<Reference>>)
        ensures self.wf(), valid(self.view()), match r { Some(records) => records@ == body_projection(self.view()) && records.len() <= MAX_PARENT_ENTRIES, None => false },
    {
        proof { use_type_invariant(self); reveal(valid); }
        Some(copy(&self.body_records))
    }
    pub fn external_records(&self) -> (r: Option<Vec<Reference>>)
        ensures self.wf(), valid(self.view()), match r { Some(records) => records@ == external_projection(self.view()) && records.len() <= MAX_PARENT_ENTRIES, None => false },
    {
        proof { use_type_invariant(self); reveal(valid); }
        Some(copy(&self.external_records))
    }
    pub fn logical_records(&self) -> (r: Option<Vec<ParentReference>>)
        ensures self.wf(), valid(self.view()), match r { Some(records) => records@ == logical_projection(self.view()) && records.len() <= MAX_PARENT_ENTRIES, None => false },
    {
        proof { use_type_invariant(self); projection_bounds(self.view()); }
        let number = self.node.number();
        let records = label_records(number, &self.body_records, &self.external_records);
        assert forall|i: int| 0 <= i < records.len() implies records@[i] == #[trigger] logical_projection(self.view())[i] by {
            assert(records@[i].parent == self.view().node.number);
            assert(records@[i].physical == (self.body_records@ + self.external_records@)[i]);
        }
        assert(records@ =~= logical_projection(self.view()));
        Some(records)
    }

}

proof fn projection_bounds(v: ParentView)
    requires valid(v),
    ensures body_projection(v).len() + external_projection(v).len() <= MAX_PARENT_ENTRIES,
{ reveal(valid); }
fn label_records(parent: u32, body: &[Reference], external: &[Reference]) -> (r: Vec<ParentReference>)
    requires body.len() + external.len() <= MAX_PARENT_ENTRIES,
    ensures r.len() == body.len() + external.len(),
        forall|i: int| 0 <= i < r.len() ==> (#[trigger] r@[i]).parent == parent
            && r@[i].physical == (body@ + external@)[i],
{
    let total = body.len() + external.len(); let mut records: Vec<ParentReference> = Vec::new(); let mut i = 0usize;
    while i < total
        invariant total == body.len() + external.len() <= MAX_PARENT_ENTRIES,
            i <= total, records.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] records@[j]).parent == parent
                && records@[j].physical == (body@ + external@)[j],
        decreases total - i,
    {
        let physical = if i < body.len() { body[i] } else { external[i - body.len()] };
        assert(physical == (body@ + external@)[i as int]);
        records.push(ParentReference { parent, physical }); i += 1;
    }
    records
}

fn copy(records: &[Reference]) -> (r: Vec<Reference>) ensures r@ == records@ {
    let mut result = Vec::new(); let mut i = 0usize;
    while i < records.len() invariant i <= records.len(), result@ == records@.take(i as int), decreases records.len() - i,
    { result.push(records[i]); assert(result@ =~= records@.take(i as int + 1)); i += 1; }
    result
}
fn make_reference(e: Entry, kind: Kind, owner: u64) -> (r: Option<Reference>)
    ensures match r { Some(reference) => reference == physical(e, kind, owner) && ea_refs::good(reference), None => true },
{
    if owner == 0 || owner > u32::MAX as u64 || e.position > u32::MAX as usize || e.position % 4 != 0
        || e.value_inode == 0 || e.value_size == 0 || e.value_size > ea_refs::MAX_VALUE { return None; }
    let position = e.position as u32;
    let good_position = match kind { Kind::Inline => 160 <= position && position <= 236, Kind::External => 32 <= position && position <= 4076 };
    if !good_position { return None; }
    Some(Reference { location: Location { kind, owner, offset: position }, value: e.value_inode, size: e.value_size })
}
fn collect(table: &table::Table<'_>, kind: Kind, owner: u64, parent: u32) -> (r: Option<Vec<Reference>>)
    ensures table.wf(), match r { Some(records) => records@ == projection(table.view().entries, kind, owner)
        && projectable(table.view().entries, kind, owner, parent) && records.len() <= MAX_PARENT_ENTRIES, None => true },
{
    let n = table.len(); if n > MAX_PARENT_ENTRIES { return None; }
    let mut records = Vec::new(); let mut i = 0usize;
    while i < n
        invariant table.wf(), n == table.view().entries.len(), i <= n <= MAX_PARENT_ENTRIES, records.len() <= i,
            records@ == projection(table.view().entries.take(i as int), kind, owner),
            forall|j: int| 0 <= j < i && (#[trigger] table.view().entries[j]).value_inode > 0 ==>
                table.view().entries[j].value_inode != parent && ea_refs::good(physical(table.view().entries[j], kind, owner)),
        decreases n - i,
    {
        let e = table.metadata(i).unwrap();
        if e.value_inode > 0 {
            if e.value_inode == parent { return None; }
            let reference = match make_reference(e, kind, owner) { Some(reference) => reference, None => { return None; } };
            records.push(reference);
        }
        assert(table.view().entries.take(i as int + 1).drop_last() =~= table.view().entries.take(i as int));
        assert(table.view().entries.take(i as int + 1).last() == e);
        i += 1;
    }
    assert(table.view().entries.take(i as int) =~= table.view().entries);
    Some(records)
}

#[verifier::opaque]
spec fn tables_valid(v: ParentView) -> bool {
    let h = v.node.header;
    &&& ea_source::node_valid(v.node) && (v.node.number == 2 || v.node.number >= 11)
    &&& inode::metadata_accepted_with_features(v.node.raw, v.node.number, h.inodes, h.seed, huge(h))
    &&& xattr::valid_body(v.body) && v.body.raw == v.node.raw && v.body.ea && v.body.inodes == h.inodes
    &&& match v.external {
        None => address(v) == 0,
        Some(t) => 0 < address(v) < h.blocks && table::valid(t) && t.raw == block_bytes(h, address(v))
            && t.first == 32 && t.base == 0 && t.sorted && t.ea && t.inodes == h.inodes
            && xattr::header(t.raw, address(v) as u64, h.seed, true) && xattr_inode::disjoint(v.body, t),
    }
}
fn read_parent<'s, 'a>(header: &Header<'s, 'a>, number: u32)
    -> (r: Option<(Node<'a>, Body<'a>, Option<Block<'a>>, u32, u32, Ghost<ParentView>)>)
    ensures match r { Some((node, body, external, pointer, references, cert)) =>
        node.wf() && body.wf() && tables_valid(cert@)
        && (cert@).node == node.view() && (cert@).body == body.view()
        && (cert@).external == match &external { Some(block) => Some(block.view()), None => None }
        && (match &external { Some(block) => block.wf(), None => true })
        && pointer as nat == address(cert@) && references as nat == external_reference_count(cert@)
        && (cert@).node.header == header.view() && (cert@).node.number == number,
        None => true },
{
    hide(inode::checksum);
    if number != 2 && number < 11 { return None; }
    let node = match header.get(number) { Some(node) => node, None => { return None; } };
    let raw = node.raw(); let (blocks, inodes, _, seed) = header.parameters();
    if inode::parse_metadata_with_features(raw, number, inodes, seed, header.huge_files()).is_none() { return None; }
    let body = match xattr::parse_body(raw, true, inodes) { Some(body) => body, None => { return None; } };
    let pointer = xattr::inode_pointer(raw).unwrap();
    let external = if pointer == 0 { None } else {
        if pointer >= blocks as u64 { return None; }
        let block = match header.source().block(pointer as u32) { Some(block) => block, None => { return None; } };
        let parsed = match xattr::parse_block(block.as_slice(), pointer, seed, true, true, inodes) { Some(block) => block, None => { return None; } };
        if !xattr_inode::distinct_keys(&body, &parsed) { return None; }
        Some(parsed)
    };
    let references = match &external { Some(block) => block.refcount(), None => 0u32 };
    let ghost view = ParentView { node: node.view(), body: body.view(), external: match &external { Some(block) => Some(block.view()), None => None } };
    assert(tables_valid(view)) by { reveal(tables_valid); }
    Some((node, body, external, pointer as u32, references, Ghost(view)))
}
proof fn projected_tables_are_a_valid_parent(v: ParentView)
    requires tables_valid(v),
        match v.body.table { Some(t) => projectable(t.entries, Kind::Inline, v.node.number as u64, v.node.number), None => true },
        match v.external { Some(t) => projectable(t.entries, Kind::External, address(v) as u64, v.node.number), None => true },
        body_projection(v).len() + external_projection(v).len() <= MAX_PARENT_ENTRIES,
    ensures valid(v),
{ reveal(tables_valid); reveal(valid); }

pub fn inspect<'s, 'a>(header: &Header<'s, 'a>, number: u32) -> (r: Option<Parent<'a>>)
    ensures header.wf(), ea_source::header_valid(header.view()), match r { Some(parent) => parent.wf() && valid(parent.view())
        && parent.view().node.header == header.view() && parent.view().node.number == number, None => true },
{
    let _ = header.parameters();
    let (node, body, external, pointer, references, Ghost(view)) = match read_parent(header, number) {
        Some(parts) => parts, None => { return None; }
    };
    let body_records = match body.entry_table() {
        Some(table) => match collect(table, Kind::Inline, number as u64, number) { Some(records) => records, None => { return None; } },
        None => { let records = Vec::new(); assert(records@ =~= Seq::<Reference>::empty()); records },
    };
    let external_records = match &external {
        Some(block) => match collect(block.entries(), Kind::External, pointer as u64, number) { Some(records) => records, None => { return None; } },
        None => { let records = Vec::new(); assert(records@ =~= Seq::<Reference>::empty()); records },
    };
    if body_records.len() + external_records.len() > MAX_PARENT_ENTRIES { return None; }
    proof { projected_tables_are_a_valid_parent(view); }
    Some(Parent { node, body, external, address: pointer, references, body_records, external_records, checked: Ghost(view) })
}

proof fn projected_member(entries: Seq<Entry>, kind: Kind, owner: u64, i: int)
    requires 0 <= i < entries.len(), entries[i].value_inode > 0,
    ensures projection(entries, kind, owner).contains(physical(entries[i], kind, owner)),
    decreases entries.len(),
{
    let target = physical(entries[i], kind, owner);
    let prefix = projection(entries.drop_last(), kind, owner);
    if i < entries.len() - 1 {
        assert(entries.drop_last()[i] == entries[i]);
        projected_member(entries.drop_last(), kind, owner, i);
        assert(prefix.contains(target));
        let k = choose|k: int| 0 <= k < prefix.len() && prefix[k] == target;
        if entries.last().value_inode > 0 {
            assert(projection(entries, kind, owner) == prefix.push(physical(entries.last(), kind, owner)));
            assert(projection(entries, kind, owner)[k] == target);
            assert(exists|j: int| 0 <= j < projection(entries, kind, owner).len() && projection(entries, kind, owner)[j] == target);
        } else {
            assert(projection(entries, kind, owner) == prefix);
        }
    } else {
        assert(i == entries.len() - 1 && entries.last() == entries[i]);
        assert(projection(entries, kind, owner) == prefix.push(target));
        assert(projection(entries, kind, owner)[prefix.len() as int] == target);
        assert(exists|j: int| 0 <= j < projection(entries, kind, owner).len() && projection(entries, kind, owner)[j] == target);
    }
}

pub proof fn every_ea_entry_in_an_admitted_parent_occurs_in_its_complete_projection(v: ParentView, from_body: bool, i: int)
    requires valid(v), (if from_body { v.body.table } else { v.external }) is Some,
        0 <= i < (if from_body { v.body.table } else { v.external }).unwrap().entries.len(),
        (if from_body { v.body.table } else { v.external }).unwrap().entries[i].value_inode > 0,
    ensures (if from_body { body_projection(v) } else { external_projection(v) }).contains(physical(
        (if from_body { v.body.table } else { v.external }).unwrap().entries[i],
        if from_body { Kind::Inline } else { Kind::External }, if from_body { v.node.number as u64 } else { address(v) as u64 })),
{
    let t = (if from_body { v.body.table } else { v.external }).unwrap();
    projected_member(t.entries, if from_body { Kind::Inline } else { Kind::External }, if from_body { v.node.number as u64 } else { address(v) as u64 }, i);
}
pub proof fn parent_projections_are_bound_to_the_exact_source_and_table_slot(v: ParentView)
    requires valid(v),
    ensures v.body.raw == v.node.raw, v.node.raw == v.node.header.source.subrange(v.node.position as int, v.node.position as int + 256),
        body_projection(v).len() + external_projection(v).len() <= MAX_PARENT_ENTRIES,
{ reveal(valid); reveal(ea_source::node_valid); }

}
