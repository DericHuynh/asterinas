// SPDX-License-Identifier: MPL-2.0

//! An EA_INODE descriptor selected by its complete source-bound xattr key.
//! This immutable reader establishes neither caller authority nor a complete
//! allocation/reference census, value-inode lifetime or filesystem admission.

use vstd::prelude::*;
use crate::{bytes, ea_source::{self, Header, Node, NodeView}, inode, xattr::{self, Body, BodyView, Block},
    xattr_entry::{self as entry, Entry}, xattr_inode, xattr_table::{self as table, TableView, ValueRef}};

verus! {

pub open spec fn huge(v: ea_source::HeaderView) -> bool { bytes::le32(v.source, 1124) as u32 & 8u32 != 0 }
pub open spec fn block_bytes(v: ea_source::HeaderView, address: nat) -> Seq<u8> {
    v.source.subrange(address as int * 4096, (address as int + 1) * 4096)
}
pub struct ReferenceView {
    pub parent: NodeView, pub body: BodyView, pub external: Option<TableView>,
    pub from_body: bool, pub index: usize, pub selected: Entry, pub namespace: u8, pub name: Seq<u8>,
}
pub open spec fn source_table(v: ReferenceView, from_body: bool) -> Option<TableView> {
    if from_body { v.body.table } else { v.external }
}
#[verifier::opaque]
pub open spec fn valid(v: ReferenceView) -> bool {
    let h = v.parent.header; let address = xattr::inode_address(v.parent.raw);
    &&& ea_source::node_valid(v.parent) && (v.parent.number == 2 || v.parent.number >= 11)
    &&& inode::metadata_accepted_with_features(v.parent.raw, v.parent.number, h.inodes, h.seed, huge(h))
    &&& xattr::valid_body(v.body) && v.body.raw == v.parent.raw && v.body.ea && v.body.inodes == h.inodes
    &&& match v.external {
        None => address == 0,
        Some(t) => 0 < address < h.blocks && table::valid(t) && t.raw == block_bytes(h, address)
            && t.first == 32 && t.base == 0 && t.sorted && t.ea && t.inodes == h.inodes
            && xattr::header(t.raw, address as u64, h.seed, true) && xattr_inode::disjoint(v.body, t),
    }
    &&& match source_table(v, v.from_body) {
        Some(t) => v.index < t.entries.len() && v.selected == t.entries[v.index as int]
            && v.selected.namespace == v.namespace && entry::name(t.raw, v.selected) == v.name,
        None => false,
    }
    &&& v.selected.value_inode > 0 && v.selected.value_inode != v.parent.number
}

pub struct Reference<'a> {
    parent: Node<'a>, body: Body<'a>, external: Option<Block<'a>>, from_body: bool, index: usize,
    selected: Entry, namespace: u8, name: Vec<u8>, checked: Ghost<ReferenceView>,
}
impl<'a> Reference<'a> {
    pub closed spec fn view(&self) -> ReferenceView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        valid(self.view()) && self.parent.view() == self.view().parent && self.body.view() == self.view().body
            && self.view().external == match &self.external { Some(block) => Some(block.view()), None => None }
            && self.from_body == self.view().from_body && self.index == self.view().index && self.selected == self.view().selected
            && self.namespace == self.view().namespace && self.name@ == self.view().name
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn parameters(&self) -> (r: (u32, u32, u32))
        ensures self.wf(), valid(self.view()), r == (self.view().selected.value_inode, self.view().selected.value_size, self.view().selected.hash),
    { proof { use_type_invariant(self); } (self.selected.value_inode, self.selected.value_size, self.selected.hash) }
    pub fn namespace(&self) -> (r: u8) ensures self.wf(), valid(self.view()), r == self.view().namespace {
        proof { use_type_invariant(self); } self.namespace
    }
    pub fn name(&self) -> (r: &[u8]) ensures self.wf(), valid(self.view()), r@ == self.view().name {
        proof { use_type_invariant(self); } &self.name
    }
    pub fn parent(&self) -> (r: &Node<'a>)
        ensures self.wf(), valid(self.view()), r.wf(), ea_source::node_valid(r.view()), r.view() == self.view().parent,
    { proof { use_type_invariant(self); reveal(valid); } let _ = self.parent.number(); &self.parent }
}

fn copy(input: &[u8]) -> (r: Vec<u8>) ensures r@ == input@ {
    let mut result = Vec::new(); let mut i = 0usize;
    while i < input.len()
        invariant i <= input.len(), result@ == input@.take(i as int),
        decreases input.len() - i,
    { result.push(input[i]); assert(result@ =~= input@.take(i as int + 1)); i += 1; }
    result
}

fn select(table: &table::Table<'_>, namespace: u8, name: &[u8]) -> (r: Option<(usize, Entry)>)
    ensures table.wf(), match r {
        Some((i, e)) => i < table.view().entries.len() && e == table.view().entries[i as int]
            && e.namespace == namespace && entry::name(table.view().raw, e) == name@ && e.value_inode > 0
            && table::value_view(table.view().raw, e) == table::ValueView::Inode { number: e.value_inode, bytes: e.value_size, hash: e.hash },
        None => true,
    },
{
    let i = match table.find(namespace, name) { Some(i) => i, None => { return None; } };
    let e = table.metadata(i).unwrap();
    match table.value(i).unwrap() {
        ValueRef::Inode { number, bytes, hash } => {
            if number == 0 || number != e.value_inode || bytes != e.value_size || hash != e.hash { return None; }
        },
        ValueRef::Bytes(_) => { return None; },
    }
    Some((i, e))
}

pub fn inspect<'s, 'a>(header: &Header<'s, 'a>, parent_number: u32, namespace: u8, name: &[u8]) -> (r: Option<Reference<'a>>)
    ensures header.wf(), ea_source::header_valid(header.view()), match r {
        Some(reference) => reference.wf() && valid(reference.view()) && reference.view().parent.header == header.view()
            && reference.view().parent.number == parent_number && reference.view().namespace == namespace && reference.view().name == name@,
        None => true,
    },
{
    let (blocks, inodes, _, seed) = header.parameters();
    if (parent_number != 2 && parent_number < 11) || name.len() > 255 { return None; }
    let parent = match header.get(parent_number) { Some(node) => node, None => { return None; } };
    let raw = parent.raw();
    if inode::parse_metadata_with_features(raw, parent_number, inodes, seed, header.huge_files()).is_none() { return None; }
    let body = match xattr::parse_body(raw, true, inodes) { Some(body) => body, None => { return None; } };
    let address = xattr::inode_pointer(raw).unwrap();
    let external = if address == 0 { None } else {
        if address >= blocks as u64 { return None; }
        let block = match header.source().block(address as u32) { Some(block) => block, None => { return None; } };
        let parsed = match xattr::parse_block(block.as_slice(), address, seed, true, true, inodes) { Some(block) => block, None => { return None; } };
        if !xattr_inode::distinct_keys(&body, &parsed) { return None; }
        Some(parsed)
    };
    let mut selected: Option<(bool, usize, Entry)> = None;
    if let Some(table) = body.entry_table() {
        if let Some((i, e)) = select(table, namespace, name) { selected = Some((true, i, e)); }
    }
    if selected.is_none() {
        if let Some(block) = &external {
            if let Some((i, e)) = select(block.entries(), namespace, name) { selected = Some((false, i, e)); }
        }
    }
    let (from_body, index, e) = match selected { Some(selected) => selected, None => { return None; } };
    if e.value_inode == parent_number { return None; }
    let ghost view = ReferenceView { parent: parent.view(), body: body.view(),
        external: match &external { Some(block) => Some(block.view()), None => None },
        from_body, index, selected: e, namespace, name: name@ };
    assert(valid(view)) by { reveal(valid); }
    Some(Reference { parent, body, external, from_body, index, selected: e, namespace, name: copy(name), checked: Ghost(view) })
}

pub proof fn ea_references_bind_the_exact_parent_source_and_complete_key(v: ReferenceView)
    requires valid(v),
    ensures v.body.raw == v.parent.raw,
        v.parent.raw == v.parent.header.source.subrange(v.parent.position as int, v.parent.position as int + 256),
        source_table(v, v.from_body) is Some,
        source_table(v, v.from_body).unwrap().entries[v.index as int] == v.selected,
        v.selected.namespace == v.namespace && entry::name(source_table(v, v.from_body).unwrap().raw, v.selected) == v.name,
{ reveal(valid); reveal(ea_source::node_valid); }

pub proof fn ea_reference_descriptors_are_bounded_nonself_values(v: ReferenceView)
    requires valid(v),
    ensures 0 < v.selected.value_inode <= v.parent.header.inodes, v.selected.value_inode != 2,
        v.selected.value_inode != v.parent.number, 0 < v.selected.value_size <= entry::MAX_VALUE,
{
    reveal(valid); let t = source_table(v, v.from_body).unwrap();
    if v.from_body { assert(t == v.body.table.unwrap()); }
    reveal(table::valid); reveal(table::chain);
    assert(entry::record(t.raw, t.base, t.ea, t.inodes, t.entries[v.index as int]));
    reveal(entry::record);
}

pub proof fn an_ea_reference_full_key_cannot_select_another_entry(v: ReferenceView, from_body: bool, index: int)
    requires valid(v), source_table(v, from_body) is Some,
        0 <= index < source_table(v, from_body).unwrap().entries.len(),
        source_table(v, from_body).unwrap().entries[index].namespace == v.namespace,
        entry::name(source_table(v, from_body).unwrap().raw, source_table(v, from_body).unwrap().entries[index]) == v.name,
    ensures source_table(v, from_body).unwrap().entries[index] == v.selected,
{
    reveal(valid); let a = source_table(v, v.from_body).unwrap(); let b = source_table(v, from_body).unwrap();
    if v.from_body == from_body {
        table::successful_tables_have_one_value_for_each_full_namespace_and_name_key(a, v.index as int, index);
    } else {
        let body = v.body.table.unwrap(); let external = v.external.unwrap();
        if v.from_body {
            assert(body.entries[v.index as int].namespace == external.entries[index].namespace);
            assert(entry::name(body.raw, body.entries[v.index as int]) == entry::name(external.raw, external.entries[index]));
            assert(!xattr_inode::disjoint(v.body, external));
        } else {
            assert(body.entries[index].namespace == external.entries[v.index as int].namespace);
            assert(entry::name(body.raw, body.entries[index]) == entry::name(external.raw, external.entries[v.index as int]));
            assert(!xattr_inode::disjoint(v.body, external));
        }
    }
}

}
