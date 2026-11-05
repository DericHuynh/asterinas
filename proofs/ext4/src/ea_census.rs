// SPDX-License-Identifier: MPL-2.0

//! Complete bounded EA reference metadata census over one original snapshot.
//! This is not physical block ownership, namespace/journal admission, an
//! orphan protocol, quota enforcement, or CortenMM/device/VFS authority.

use vstd::prelude::*;
use crate::{bytes, ea_billing, ea_hash, ea_index::{self, Index, IndexView}, ea_inode::{self, Info, Status},
    ea_parent::{self, Parent, ParentView}, ea_ref_projection::{self as projection, Graph, GraphView, Input},
    ea_refs::{self, Kind, Ledger, ParentReference, Reference}, ea_source::{self, NodeView},
    inode, inode_group, snapshot::Snapshot, xattr, xattr_entry::{self, Entry}};

verus! {

pub const MAX_TRACKED: usize = 4096;

pub enum Class { Empty, Reserved(NodeView), Parent(ParentView, ea_billing::Usage), Value(NodeView, Info) }
pub open spec fn reserved_ok(node: NodeView) -> bool {
    if node.number == 8 {
        inode::metadata_accepted_with_features(node.raw, node.number, node.header.inodes, node.header.seed, ea_parent::huge(node.header))
            && bytes::le16(node.raw, 0) as u16 & 0xf000 == 0x8000
            && xattr::inode_address(node.raw) == 0 && !xattr::body_present(node.raw)
    } else { inode_group::empty_reserved(node.raw) && !xattr::body_present(node.raw) }
}
#[verifier::opaque]
pub open spec fn class_valid(index: IndexView, number: u32, class: Class) -> bool {
    &&& ea_index::valid(index) && 0 < number <= index.header.inodes
    &&& match class {
        Class::Empty => number > 10 && !ea_index::inode_allocated(index, number),
        Class::Reserved(node) => ea_index::inode_allocated(index, number) && ea_source::node_valid(node)
            && node.header == index.header && node.number == number && number <= 10 && number != 2 && reserved_ok(node),
        Class::Parent(parent, billing) => ea_index::inode_allocated(index, number) && ea_parent::valid(parent)
            && parent.node.header == index.header && parent.node.number == number
            && (number != 2 || bytes::le16(parent.node.raw, 0) as u16 & 0xf000 == 0x4000)
            && ea_billing::checked(parent.node.raw, ea_parent::huge(index.header), number, ea_parent::logical_projection(parent), billing),
        Class::Value(node, info) => ea_index::inode_allocated(index, number) && ea_source::node_valid(node)
            && node.header == index.header && node.number == number && (number >= 11 || number == 3 || number == 4)
            && ea_inode::represents(info, node.raw) && info.number == number && info.inodes == index.header.inodes
            && info.seed == index.header.seed && info.status == Status::Live,
    }
}
pub open spec fn interesting(parent: ParentView) -> bool {
    ea_parent::body_projection(parent).len() + ea_parent::external_projection(parent).len() > 0
}
pub open spec fn input(parent: ParentView) -> Input {
    Input { parent: parent.node.number, body: ea_parent::body_projection(parent), external: ea_parent::external_projection(parent) }
}
pub open spec fn inputs(classes: Seq<Class>) -> Seq<Input> decreases classes.len() {
    if classes.len() == 0 { Seq::empty() } else {
        let previous = inputs(classes.drop_last());
        match classes.last() { Class::Parent(parent, _) => if interesting(parent) { previous.push(input(parent)) } else { previous }, _ => previous }
    }
}
pub open spec fn value_infos(classes: Seq<Class>) -> Seq<Info> decreases classes.len() {
    if classes.len() == 0 { Seq::empty() } else {
        let previous = value_infos(classes.drop_last());
        match classes.last() { Class::Value(_, info) => previous.push(info), _ => previous }
    }
}
#[derive(Clone, Copy)]
pub struct External { pub parent: u32, pub address: u32, pub references: u32 }
pub open spec fn externals(classes: Seq<Class>) -> Seq<External> decreases classes.len() {
    if classes.len() == 0 { Seq::empty() } else {
        let previous = externals(classes.drop_last());
        match classes.last() { Class::Parent(parent, _) => if ea_parent::address(parent) > 0 {
            previous.push(External { parent: parent.node.number, address: ea_parent::address(parent) as u32,
                references: ea_parent::external_reference_count(parent) as u32 })
        } else { previous }, _ => previous }
    }
}
pub open spec fn external_count(records: Seq<External>, block: u32) -> nat decreases records.len() {
    if records.len() == 0 { 0nat } else { external_count(records.drop_last(), block) + if records.last().address == block { 1nat } else { 0nat } }
}
pub open spec fn external_counts_exact(records: Seq<External>) -> bool {
    records.len() <= MAX_TRACKED && forall|i: int| 0 <= i < records.len() ==> (#[trigger] records[i]).references == external_count(records, records[i].address)
}

pub struct Target { pub record: Reference, pub node: NodeView, pub info: Info }
#[verifier::opaque]
pub open spec fn target_valid(index: IndexView, target: Target) -> bool {
    ea_index::valid(index) && ea_refs::good(target.record) && ea_index::inode_allocated(index, target.record.value)
        && ea_source::node_valid(target.node) && target.node.header == index.header && target.node.number == target.record.value
        && ea_inode::represents(target.info, target.node.raw) && target.info.number == target.record.value
        && target.info.inodes == index.header.inodes && target.info.seed == index.header.seed && target.info.status == Status::Live
        && target.info.size == target.record.size
}
pub open spec fn selected(parent: ParentView, reference: Reference, entry: Entry) -> bool {
    match reference.location.kind {
        Kind::Inline => reference.location.owner == parent.node.number as u64 && match parent.body.table {
            Some(table) => exists|i: int| 0 <= i < table.entries.len() && (#[trigger] table.entries[i]) == entry
                && reference == ea_parent::physical(entry, Kind::Inline, parent.node.number as u64), None => false },
        Kind::External => reference.location.owner as nat == ea_parent::address(parent) && match parent.external {
            Some(table) => exists|i: int| 0 <= i < table.entries.len() && (#[trigger] table.entries[i]) == entry
                && reference == ea_parent::physical(entry, Kind::External, reference.location.owner), None => false },
    }
}
pub open spec fn binding_name(parent: ParentView, reference: Reference, entry: Entry) -> Seq<u8> {
    match reference.location.kind {
        Kind::Inline => match parent.body.table { Some(table) => xattr_entry::name(table.raw, entry), None => Seq::empty() },
        Kind::External => match parent.external { Some(table) => xattr_entry::name(table.raw, entry), None => Seq::empty() },
    }
}
pub open spec fn binding_hash(parent: ParentView, reference: Reference, entry: Entry, inode_hash: u32) -> bool {
    entry.hash == ea_hash::entry(binding_name(parent, reference, entry), inode_hash, false)
        || entry.hash == ea_hash::entry(binding_name(parent, reference, entry), inode_hash, true)
}
pub struct Binding { pub logical: ParentReference, pub parent: ParentView, pub target: Target, pub entry: Entry }
#[verifier::opaque]
pub open spec fn binding_valid(index: IndexView, binding: Binding) -> bool {
    ea_parent::valid(binding.parent) && binding.parent.node.header == index.header && binding.parent.node.number == binding.logical.parent
        && binding.target.record == binding.logical.physical && target_valid(index, binding.target)
        && selected(binding.parent, binding.logical.physical, binding.entry)
        && binding_hash(binding.parent, binding.logical.physical, binding.entry, bytes::le32(binding.target.node.raw, 8) as u32)
        && !(binding.entry.hash as nat != bytes::le32(binding.target.node.raw, 8)
            && bytes::le32(binding.target.node.raw, 16) == binding.logical.parent
            && bytes::le32(binding.target.node.raw, 100) == bytes::le32(binding.parent.node.raw, 100))
}
pub struct CensusView { pub index: IndexView, pub classes: Seq<Class>, pub graph: GraphView, pub values: Seq<Info>,
    pub external: Seq<External>, pub targets: Seq<Target>, pub bindings: Seq<Binding>, pub budget: u32 }
#[verifier::opaque]
pub open spec fn valid(v: CensusView) -> bool {
    &&& ea_index::valid(v.index) && v.classes.len() == v.index.header.inodes <= v.budget
    &&& forall|i: int| 0 <= i < v.classes.len() ==> #[trigger] class_valid(v.index, (i + 1) as u32, v.classes[i])
    &&& projection::valid(v.graph) && v.graph.inputs == inputs(v.classes)
    &&& v.values == value_infos(v.classes) && v.values.len() <= MAX_TRACKED
    &&& forall|i: int| 0 <= i < v.values.len() ==> (#[trigger] v.values[i]).refs > 0
        && v.values[i].refs == ea_refs::references_to(v.graph.physical, v.values[i].number)
    &&& v.external == externals(v.classes) && external_counts_exact(v.external)
    &&& forall|i: int| 0 <= i < v.external.len() ==> !ea_index::table_member(v.index, (#[trigger] v.external[i]).address)
    &&& v.targets.len() == v.graph.physical.len() && forall|i: int| 0 <= i < v.targets.len() ==>
        #[trigger] target_valid(v.index, v.targets[i]) && v.targets[i].record == v.graph.physical[i]
    &&& v.bindings.len() == v.graph.logical.len() && forall|i: int| 0 <= i < v.bindings.len() ==>
        #[trigger] binding_valid(v.index, v.bindings[i]) && v.bindings[i].logical == v.graph.logical[i]
}

pub struct Census<'s, 'a> { index: Index<'s, 'a>, graph: Graph, values: Vec<Info>, external: Vec<External>, checked: Ghost<CensusView> }
impl<'s, 'a> Census<'s, 'a> {
    pub closed spec fn view(&self) -> CensusView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        valid(self.view()) && self.index.view() == self.view().index && self.graph.view() == self.view().graph
            && self.values@ == self.view().values && self.external@ == self.view().external
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn index(&self) -> (r: &Index<'s, 'a>) ensures self.wf(), valid(self.view()), r.wf(), r.view() == self.view().index {
        proof { use_type_invariant(self); } let _ = self.index.parameters(); &self.index
    }
    pub fn physical(&self) -> (r: &Ledger) ensures self.wf(), valid(self.view()), r.wf(), r.view() == self.view().graph.physical {
        proof { use_type_invariant(self); } self.graph.physical()
    }
    pub fn logical(&self) -> (r: &[ParentReference]) ensures self.wf(), valid(self.view()), r@ == self.view().graph.logical {
        proof { use_type_invariant(self); } self.graph.logical()
    }
    pub fn values(&self) -> (r: &[Info]) ensures self.wf(), valid(self.view()), r@ == self.view().values {
        proof { use_type_invariant(self); } &self.values
    }
    pub fn quota(&self, parent: u32) -> (r: Option<ea_refs::Usage>)
        ensures self.wf(), valid(self.view()), match r { Some(usage) => parent > 0 && usage.ea_inodes == ea_refs::parent_count(self.view().graph.logical, parent)
            && usage.bytes == ea_refs::parent_bytes(self.view().graph.logical, parent, 4096), None => true },
    { proof { use_type_invariant(self); } ea_refs::quota_usage(self.graph.logical(), parent, 4096) }
    /// Every ordinary parent's exact retained external-xattr pointer, including
    /// shared and local-value-only blocks. This grants no mutation authority.
    pub fn external_pointers(&self) -> (r: &[External])
        ensures self.wf(), valid(self.view()), r@ == self.view().external,
    { proof { use_type_invariant(self); } &self.external }
    pub fn external_parents(&self, block: u32) -> (r: u32)
        ensures self.wf(), valid(self.view()), r as nat == external_count(self.view().external, block),
    { proof { use_type_invariant(self); reveal(valid); } count_external(&self.external, block).unwrap() }
}

fn count_external(records: &[External], block: u32) -> (r: Option<u32>)
    ensures match r { Some(count) => records.len() <= MAX_TRACKED && count as nat == external_count(records@, block),
        None => records.len() > MAX_TRACKED },
{
    if records.len() > MAX_TRACKED { return None; }
    let mut count = 0u32; let mut i = 0usize;
    while i < records.len()
        invariant i <= records.len() <= MAX_TRACKED, count <= i, count as nat == external_count(records@.take(i as int), block),
        decreases records.len() - i,
    {
        if records[i].address == block { count += 1; }
        assert(records@.take(i as int + 1).drop_last() =~= records@.take(i as int));
        assert(records@.take(i as int + 1).last() == records@[i as int]); i += 1;
    }
    assert(records@.take(i as int) =~= records@); Some(count)
}
fn check_external(records: &[External]) -> (r: bool) ensures r ==> external_counts_exact(records@) {
    if records.len() > MAX_TRACKED { return false; }
    let mut i = 0usize;
    while i < records.len()
        invariant i <= records.len() <= MAX_TRACKED,
            forall|j: int| 0 <= j < i ==> (#[trigger] records@[j]).references == external_count(records@, records@[j].address),
        decreases records.len() - i,
    { if count_external(records, records[i].address).unwrap() != records[i].references { return false; } i += 1; }
    true
}
fn check_external_layout(index: &Index<'_, '_>, records: &[External]) -> (r: bool)
    ensures index.wf(), r ==> forall|i: int| 0 <= i < records.len() ==> !ea_index::table_member(index.view(), (#[trigger] records@[i]).address),
{
    let _ = index.parameters(); let mut i = 0usize;
    while i < records.len()
        invariant index.wf(), i <= records.len(),
            forall|j: int| 0 <= j < i ==> !ea_index::table_member(index.view(), (#[trigger] records@[j]).address),
        decreases records.len() - i,
    { if index.is_inode_table_block(records[i].address) { return false; } i += 1; }
    true
}
fn check_values(values: &[Info], physical: &Ledger) -> (r: bool)
    ensures physical.wf(), r ==> values.len() <= MAX_TRACKED && (forall|i: int| 0 <= i < values.len() ==> (#[trigger] values@[i]).refs > 0
        && values@[i].refs == ea_refs::references_to(physical.view(), values@[i].number)),
{
    let _ = physical.len(); if values.len() > MAX_TRACKED { return false; }
    let mut i = 0usize;
    while i < values.len()
        invariant physical.wf(), i <= values.len() <= MAX_TRACKED,
            forall|j: int| 0 <= j < i ==> (#[trigger] values@[j]).refs > 0 && values@[j].refs == ea_refs::references_to(physical.view(), values@[j].number),
        decreases values.len() - i,
    { if values[i].refs == 0 || values[i].refs != physical.refs(values[i].number) { return false; } i += 1; }
    true
}
fn check_targets(index: &Index<'_, '_>, physical: &Ledger) -> (r: Option<Ghost<Seq<Target>>>)
    ensures index.wf(), physical.wf(), match r { Some(checked) => checked@.len() == physical.view().len()
        && forall|i: int| 0 <= i < checked@.len() ==> #[trigger] target_valid(index.view(), checked@[i]) && checked@[i].record == physical.view()[i], None => true },
{
    let (_, inodes, _, seed) = index.parameters(); let n = physical.len(); let mut i = 0usize;
    let ghost mut checked: Seq<Target> = Seq::empty();
    while i < n
        invariant index.wf(), physical.wf(), n == physical.view().len(), i <= n, checked.len() == i,
            inodes == index.view().header.inodes, seed == index.view().header.seed,
            forall|j: int| 0 <= j < i ==> #[trigger] target_valid(index.view(), checked[j]) && checked[j].record == physical.view()[j],
        decreases n - i,
    {
        let record = physical.at(i).unwrap();
        let node = match index.node(record.value) { Some(node) => node, None => { return None; } };
        let info = match ea_inode::parse(node.raw(), record.value, inodes, seed, Status::Live) { Some(info) => info, None => { return None; } };
        if info.size != record.size { return None; }
        let ghost target = Target { record, node: node.view(), info };
        assert(target_valid(index.view(), target)) by { reveal(target_valid); reveal(ea_refs::valid); }
        proof { checked = checked.push(target); } i += 1;
    }
    Some(Ghost(checked))
}
fn select<'a>(parent: &Parent<'a>, reference: Reference) -> (r: Option<(Entry, &'a [u8])>)
    ensures parent.wf(), match r { Some((entry, name)) => selected(parent.view(), reference, entry)
        && name@ == binding_name(parent.view(), reference, entry), None => true },
{
    let number = parent.node().number(); let address = parent.external_address(); let (body, external) = parent.source_tables();
    let table = match reference.location.kind {
        Kind::Inline => { if reference.location.owner != number as u64 { return None; } match body { Some(table) => table, None => { return None; } } },
        Kind::External => { if reference.location.owner != address as u64 { return None; } match external { Some(table) => table, None => { return None; } } },
    };
    let n = table.len(); let mut i = 0usize;
    while i < n
        invariant parent.wf(), table.wf(), n == table.view().entries.len(), i <= n,
            (match reference.location.kind { Kind::Inline => parent.view().body.table == Some(table.view()) && reference.location.owner == parent.view().node.number as u64,
                Kind::External => parent.view().external == Some(table.view()) && reference.location.owner as nat == ea_parent::address(parent.view()) }),
        decreases n - i,
    {
        let e = table.metadata(i).unwrap();
        if e.position as u64 == reference.location.offset as u64 {
            if e.value_inode != reference.value || e.value_size != reference.size { return None; }
            let (_, name) = table.name(i).unwrap();
            assert(reference == ea_parent::physical(e, reference.location.kind, reference.location.owner));
            proof {
                match reference.location.kind {
                    Kind::Inline => {
                        let table_view = parent.view().body.table.unwrap();
                        assert(table_view == table.view());
                        assert(table_view.entries[i as int] == e);
                        assert(exists|j: int| 0 <= j < table_view.entries.len() && (#[trigger] table_view.entries[j]) == e
                            && reference == ea_parent::physical(e, Kind::Inline, parent.view().node.number as u64));
                    },
                    Kind::External => {
                        let table_view = parent.view().external.unwrap();
                        assert(table_view == table.view());
                        assert(table_view.entries[i as int] == e);
                        assert(exists|j: int| 0 <= j < table_view.entries.len() && (#[trigger] table_view.entries[j]) == e
                            && reference == ea_parent::physical(e, Kind::External, reference.location.owner));
                    },
                }
                assert(selected(parent.view(), reference, e));
                assert(name@ == binding_name(parent.view(), reference, e));
            }
            return Some((e, name));
        }
        i += 1;
    }
    None
}
fn check_bindings(index: &Index<'_, '_>, logical: &[ParentReference]) -> (r: Option<Ghost<Seq<Binding>>>)
    requires ea_refs::logical_valid(logical@),
    ensures index.wf(), match r { Some(checked) => checked@.len() == logical.len() && (forall|i: int| 0 <= i < checked@.len() ==>
        #[trigger] binding_valid(index.view(), checked@[i]) && checked@[i].logical == logical@[i]), None => true },
{
    let (_, inodes, _, seed) = index.parameters(); let mut i = 0usize;
    let ghost mut checked: Seq<Binding> = Seq::empty();
    while i < logical.len()
        invariant index.wf(), ea_refs::logical_valid(logical@), inodes == index.view().header.inodes, seed == index.view().header.seed,
            i <= logical.len(), checked.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] binding_valid(index.view(), checked[j]) && checked[j].logical == logical@[j],
        decreases logical.len() - i,
    {
        let record = logical[i];
        let parent = match ea_parent::inspect(index.header(), record.parent) { Some(parent) => parent, None => { return None; } };
        let (entry, name) = match select(&parent, record.physical) { Some(selected) => selected, None => { return None; } };
        let node = match index.node(record.physical.value) { Some(node) => node, None => { return None; } };
        let info = match ea_inode::parse(node.raw(), record.physical.value, inodes, seed, Status::Live) { Some(info) => info, None => { return None; } };
        if info.size != record.physical.size { return None; }
        let unsigned = match ea_hash::entry_hash(name, info.hash, false) { Some(hash) => hash, None => { return None; } };
        let signed = match ea_hash::entry_hash(name, info.hash, true) { Some(hash) => hash, None => { return None; } };
        if entry.hash != unsigned && entry.hash != signed { return None; }
        if entry.hash != info.hash && bytes::read_le32(node.raw(), 16).unwrap() == record.parent
            && info.generation == bytes::read_le32(parent.node().raw(), 100).unwrap() { return None; }
        let ghost target = Target { record: record.physical, node: node.view(), info };
        let ghost binding = Binding { logical: record, parent: parent.view(), target, entry };
        assert(target_valid(index.view(), target)) by { reveal(target_valid); reveal(ea_parent::valid); reveal(ea_refs::logical_valid); }
        assert(binding_valid(index.view(), binding)) by { reveal(binding_valid); }
        proof { checked = checked.push(binding); } i += 1;
    }
    Some(Ghost(checked))
}
pub(crate) fn check_reserved(raw: &[u8], number: u32, inodes: u32, seed: u32, huge: bool) -> (r: bool)
    requires raw.len() == 256,
    ensures r ==> (if number == 8 { inode::metadata_accepted_with_features(raw@, number, inodes, seed, huge)
        && bytes::le16(raw@, 0) as u16 & 0xf000 == 0x8000 && xattr::inode_address(raw@) == 0 && !xattr::body_present(raw@) }
        else { inode_group::empty_reserved(raw@) && !xattr::body_present(raw@) }),
{
    let body = match xattr::parse_body(raw, true, inodes) { Some(body) => body, None => { return false; } };
    if body.present() { return false; }
    if number != 8 { return inode_group::reserved_is_empty(raw); }
    let info = match inode::parse_metadata_with_features(raw, number, inodes, seed, huge) { Some(info) => info, None => { return false; } };
    info.mode & 0xf000 == 0x8000 && xattr::inode_pointer(raw).unwrap() == 0 && bytes::read_le32(raw, 160).unwrap() == 0
}

pub fn inspect<'s, 'a>(source: &'s Snapshot<'a>, inode_budget: u32) -> (r: Option<Census<'s, 'a>>)
    ensures match r { Some(census) => census.wf() && valid(census.view()) && census.view().index.header.source == source.view()
        && census.view().budget == inode_budget, None => true },
{
    hide(inode::checksum);
    let header = match ea_source::parse(source) { Some(header) => header, None => { return None; } };
    let index = match ea_index::parse(header) { Some(index) => index, None => { return None; } };
    let (_, inodes, _, seed) = index.parameters(); if inodes > inode_budget { return None; }
    let huge = index.header().huge_files(); let ghost iv = index.view();
    let mut graph = Graph::new(); let mut values = Vec::new(); let mut external = Vec::new(); let mut i = 0usize;
    let ghost mut classes: Seq<Class> = Seq::empty();
    while i < inodes as usize
        invariant index.wf(), ea_index::valid(iv), index.view() == iv, inodes == iv.header.inodes <= inode_budget,
            11 <= inodes <= 1048576, seed == iv.header.seed, huge == ea_parent::huge(iv.header),
            graph.wf(), projection::valid(graph.view()), graph.view().inputs == inputs(classes),
            values@ == value_infos(classes), values.len() <= MAX_TRACKED, external@ == externals(classes), external.len() <= MAX_TRACKED,
            i <= inodes, classes.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] class_valid(iv, (j + 1) as u32, classes[j]),
        decreases inodes as usize - i,
    {
        let number = (i + 1) as u32; let allocated = index.allocated(number).unwrap(); let ghost mut class = Class::Empty;
        if !allocated { if number <= 10 { return None; } }
        else {
            let node = match index.node(number) { Some(node) => node, None => { return None; } };
            let raw = node.raw();
            if bytes::read_le32(raw, 32).unwrap() & ea_inode::FLAG != 0 {
                if number < 11 && number != 3 && number != 4 { return None; }
                let info = match ea_inode::parse(raw, number, inodes, seed, Status::Live) { Some(info) => info, None => { return None; } };
                if values.len() >= MAX_TRACKED { return None; }
                values.push(info); proof { class = Class::Value(node.view(), info); }
            } else if number == 2 || number >= 11 {
                let parent = match ea_parent::inspect(index.header(), number) { Some(parent) => parent, None => { return None; } };
                if number == 2 && bytes::read_le16(parent.node().raw(), 0).unwrap() & 0xf000 != 0x4000 { return None; }
                let logical = parent.logical_records().unwrap();
                let billing = match ea_billing::split(parent.node().raw(), huge, number, &logical) { Some(billing) => billing, None => { return None; } };
                let body = parent.body_records().unwrap(); let other = parent.external_records().unwrap();
                if body.len() + other.len() > 0 {
                    graph = match graph.add_parent(number, &body, &other) { Ok(next) => next, Err(_) => { return None; } };
                }
                let address = parent.external_address(); let references = parent.external_refs();
                if address > 0 {
                    if external.len() >= MAX_TRACKED { return None; }
                    external.push(External { parent: number, address, references });
                }
                proof { class = Class::Parent(parent.view(), billing); }
            } else {
                if !check_reserved(raw, number, inodes, seed, huge) { return None; }
                proof { class = Class::Reserved(node.view()); }
            }
        }
        assert(class_valid(iv, number, class)) by { reveal(class_valid); }
        let ghost previous_classes = classes;
        proof { classes = classes.push(class); }
        assert(classes.drop_last() =~= previous_classes); assert(classes.last() == class);
        assert(graph.view().inputs == inputs(classes));
        assert(values@ == value_infos(classes)); assert(external@ == externals(classes));
        i += 1;
    }
    if !check_external(&external) || !check_external_layout(&index, &external) || !check_values(&values, graph.physical()) { return None; }
    let targets = match check_targets(&index, graph.physical()) { Some(targets) => targets, None => { return None; } };
    proof { reveal(projection::valid); }
    let bindings = match check_bindings(&index, graph.logical()) { Some(bindings) => bindings, None => { return None; } };
    let ghost view = CensusView { index: index.view(), classes, graph: graph.view(), values: values@, external: external@,
        targets: targets@, bindings: bindings@, budget: inode_budget };
    assert(valid(view)) by { reveal(valid); }
    Some(Census { index, graph, values, external, checked: Ghost(view) })
}

pub proof fn every_allocated_inode_has_exactly_its_source_class(v: CensusView, number: u32)
    requires valid(v), 0 < number <= v.index.header.inodes,
    ensures class_valid(v.index, number, v.classes[number as int - 1]),
{
    reveal(valid); let i = number as int - 1;
    assert(0 <= i < v.classes.len());
    assert(class_valid(v.index, (i + 1) as u32, v.classes[i]));
}
pub proof fn physical_ea_reference_words_equal_the_complete_source_projection(v: CensusView, i: int)
    requires valid(v), 0 <= i < v.values.len(),
    ensures v.values[i].refs > 0, v.values[i].refs == ea_refs::references_to(v.graph.physical, v.values[i].number),
        v.graph.physical == projection::physical_projection(inputs(v.classes)),
{ reveal(valid); reveal(projection::valid); }
pub proof fn every_physical_ea_record_targets_an_allocated_live_value_of_exact_size(v: CensusView, i: int)
    requires valid(v), 0 <= i < v.graph.physical.len(),
    ensures target_valid(v.index, v.targets[i]), v.targets[i].record == v.graph.physical[i],
{ reveal(valid); assert(target_valid(v.index, v.targets[i])); }
pub proof fn every_logical_parent_binding_excludes_linux_lustre_refcount_rules(v: CensusView, i: int)
    requires valid(v), 0 <= i < v.graph.logical.len(),
    ensures binding_valid(v.index, v.bindings[i]), v.bindings[i].logical == v.graph.logical[i],
{ reveal(valid); assert(binding_valid(v.index, v.bindings[i])); }
pub proof fn every_logical_parent_binding_checks_the_exact_source_name_and_entry_hash(v: CensusView, i: int)
    requires valid(v), 0 <= i < v.graph.logical.len(),
    ensures binding_hash(v.bindings[i].parent, v.bindings[i].logical.physical, v.bindings[i].entry,
        bytes::le32(v.bindings[i].target.node.raw, 8) as u32),
{
    reveal(valid);
    assert(binding_valid(v.index, v.bindings[i]));
    reveal(binding_valid);
}
pub proof fn every_external_xattr_refcount_counts_parent_pointers_even_without_ea_entries(v: CensusView, i: int)
    requires valid(v), 0 <= i < v.external.len(),
    ensures v.external == externals(v.classes), v.external[i].references == external_count(v.external, v.external[i].address),
{ reveal(valid); }

pub proof fn external_xattr_blocks_do_not_alias_any_source_inode_slot(v: CensusView, i: int, node: NodeView)
    requires valid(v), 0 <= i < v.external.len(), ea_source::node_valid(node), node.header == v.index.header,
    ensures v.external[i].address != (node.position / 4096) as u32,
{
    reveal(valid);
    ea_index::source_inode_block_belongs_to_one_checked_inode_table(v.index, node);
    assert(!ea_index::table_member(v.index, v.external[i].address));
}

pub proof fn source_parent_billing_uses_every_ondisk_logical_ea_entry(v: CensusView, number: u32, parent: ParentView, billing: ea_billing::Usage)
    requires valid(v), 0 < number <= v.index.header.inodes, v.classes[number as int - 1] == Class::Parent(parent, billing),
    ensures ea_billing::checked(parent.node.raw, ea_parent::huge(v.index.header), number, ea_parent::logical_projection(parent), billing),
{
    every_allocated_inode_has_exactly_its_source_class(v, number);
    reveal(class_valid);
}

}
