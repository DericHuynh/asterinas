// SPDX-License-Identifier: MPL-2.0

//! Immutable xattrs bound to one exact inode and volume snapshot. Lookup uses
//! the complete namespace/name key across both storage locations. Parsing is
//! structural; callers still need inode allocation and VFS authorization.

use vstd::prelude::*;
use crate::{bytes, group_index::{self, GroupIndex, IndexView}, inode_table, xattr::{self, Body, Block, BodyView},
    xattr_entry, xattr_source, xattr_table::{self, Table, TableView, ValueRef, ValueView}};

verus! {

pub open spec fn disjoint(body: BodyView, external: TableView) -> bool {
    match body.table { Some(table) => forall|i: int, j: int| 0 <= i < table.entries.len() && 0 <= j < external.entries.len() ==>
        (#[trigger] table.entries[i]).namespace != (#[trigger] external.entries[j]).namespace
            || xattr_entry::name(table.raw, table.entries[i]) != xattr_entry::name(external.raw, external.entries[j]),
        None => true }
}

pub fn distinct_keys(body: &Body<'_>, external: &Block<'_>) -> (r: bool)
    ensures body.wf(), external.wf(), r == disjoint(body.view(), external.view()),
{
    let other = external.entries();
    let table = match body.entry_table() { Some(table) => table, None => { return true; } };
    let mut i = 0usize;
    let count = table.len();
    while i < count
        invariant body.wf(), external.wf(), table.wf(), other.wf(), body.view().table == Some(table.view()), other.view() == external.view(),
            i <= count == table.view().entries.len(),
            forall|a: int, b: int| 0 <= a < i && 0 <= b < other.view().entries.len() ==>
                (#[trigger] table.view().entries[a]).namespace != (#[trigger] other.view().entries[b]).namespace
                    || xattr_entry::name(table.view().raw, table.view().entries[a]) != xattr_entry::name(other.view().raw, other.view().entries[b]),
        decreases count - i,
    {
        let (namespace, name) = table.name(i).unwrap();
        if other.find(namespace, name).is_some() { return false; }
        i += 1;
    }
    true
}

pub struct AttributesView { pub index: IndexView, pub number: u32, pub body: BodyView, pub external: Option<TableView> }

pub open spec fn valid(v: AttributesView) -> bool {
    &&& group_index::valid(v.index) && 0 < v.number <= v.index.inodes
    &&& xattr::valid_body(v.body) && v.body.raw == inode_table::raw(v.index, v.number) && !v.body.ea && v.body.inodes == v.index.inodes
    &&& xattr_source::body_checked(v.index, v.number)
    &&& match v.external {
        Some(table) => xattr_source::pointer(v.index, v.number) > 0
            && xattr_source::block_checked(v.index, xattr_source::pointer(v.index, v.number))
            && xattr_table::valid(table) && table.raw == xattr_source::block_bytes(v.index, xattr_source::pointer(v.index, v.number))
            && table.first == 32 && table.base == 0 && table.sorted && !table.ea && table.inodes == v.index.inodes && disjoint(v.body, table),
        None => xattr_source::pointer(v.index, v.number) == 0,
    }
}

pub open spec fn table_has(table: TableView, namespace: u8, name: Seq<u8>, value: ValueView) -> bool {
    exists|i: int| 0 <= i < table.entries.len() && (#[trigger] table.entries[i]).namespace == namespace
        && xattr_entry::name(table.raw, table.entries[i]) == name && xattr_table::value_view(table.raw, table.entries[i]) == value
}
pub open spec fn contains(v: AttributesView, namespace: u8, name: Seq<u8>, value: ValueView) -> bool {
    (match v.body.table { Some(t) => table_has(t, namespace, name, value), None => false })
        || (match v.external { Some(t) => table_has(t, namespace, name, value), None => false })
}
pub open spec fn absent(v: AttributesView, namespace: u8, name: Seq<u8>) -> bool {
    forall|value: ValueView| !contains(v, namespace, name, value)
}

pub struct Attributes<'a> { body: Body<'a>, external: Option<Block<'a>>, index: Ghost<IndexView>, number: u32 }
impl<'a> Attributes<'a> {
    pub closed spec fn view(&self) -> AttributesView { AttributesView { index: self.index@, number: self.number, body: self.body.view(),
        external: match &self.external { Some(block) => Some(block.view()), None => None } } }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn get(&self, namespace: u8, name: &[u8]) -> (r: Option<ValueRef<'a>>)
        ensures self.wf(), match r { Some(value) => contains(self.view(), namespace, name@, value.view()), None => absent(self.view(), namespace, name@) },
    {
        proof { use_type_invariant(self); }
        if let Some(table) = self.body.entry_table() {
            if let Some(i) = table.find(namespace, name) {
                let value = table.value(i).unwrap();
                assert(table_has(table.view(), namespace, name@, value.view()));
                return Some(value);
            }
        }
        if let Some(block) = &self.external {
            let table = block.entries();
            if let Some(i) = table.find(namespace, name) {
                let value = table.value(i).unwrap();
                assert(table_has(table.view(), namespace, name@, value.view()));
                return Some(value);
            }
        }
        None
    }
}

pub fn inspect<'a>(index: &GroupIndex<'a>, number: u32) -> (r: Option<Attributes<'a>>)
    ensures index.wf(), match r { Some(attributes) => attributes.wf() && attributes.view().index == index.view() && attributes.view().number == number, None => true },
{
    let (_, inodes, _, _) = index.parameters();
    if number == 0 || number > inodes { return None; }
    let body = match xattr_source::inspect_body(index, number) { Some(body) => body, None => { return None; } };
    let raw = inode_table::read(index, number).unwrap();
    let address = xattr::inode_pointer(raw).unwrap();
    if address == 0 { return Some(Attributes { body, external: None, index: Ghost(index.view()), number }); }
    let external = match xattr_source::inspect_block(index, address) { Some(block) => block, None => { return None; } };
    if !distinct_keys(&body, &external) { return None; }
    Some(Attributes { body, external: Some(external), index: Ghost(index.view()), number })
}

pub proof fn a_full_xattr_key_cannot_select_two_different_values(v: AttributesView, namespace: u8, name: Seq<u8>, a: ValueView, b: ValueView)
    requires valid(v), contains(v, namespace, name, a), contains(v, namespace, name, b),
    ensures a == b,
{
    if let Some(t) = v.body.table {
        if table_has(t, namespace, name, a) {
            let i = choose|i: int| 0 <= i < t.entries.len() && (#[trigger] t.entries[i]).namespace == namespace
                && xattr_entry::name(t.raw, t.entries[i]) == name && xattr_table::value_view(t.raw, t.entries[i]) == a;
            if table_has(t, namespace, name, b) {
                let j = choose|j: int| 0 <= j < t.entries.len() && (#[trigger] t.entries[j]).namespace == namespace
                    && xattr_entry::name(t.raw, t.entries[j]) == name && xattr_table::value_view(t.raw, t.entries[j]) == b;
                xattr_table::successful_tables_have_one_value_for_each_full_namespace_and_name_key(t, i, j);
            } else if let Some(e) = v.external {
                let j = choose|j: int| 0 <= j < e.entries.len() && (#[trigger] e.entries[j]).namespace == namespace
                    && xattr_entry::name(e.raw, e.entries[j]) == name && xattr_table::value_view(e.raw, e.entries[j]) == b;
                assert(!disjoint(v.body, e));
            }
            return;
        }
    }
    let e = v.external.unwrap();
    let i = choose|i: int| 0 <= i < e.entries.len() && (#[trigger] e.entries[i]).namespace == namespace
        && xattr_entry::name(e.raw, e.entries[i]) == name && xattr_table::value_view(e.raw, e.entries[i]) == a;
    if let Some(t) = v.body.table {
        if table_has(t, namespace, name, b) {
            let j = choose|j: int| 0 <= j < t.entries.len() && (#[trigger] t.entries[j]).namespace == namespace
                && xattr_entry::name(t.raw, t.entries[j]) == name && xattr_table::value_view(t.raw, t.entries[j]) == b;
            assert(!disjoint(v.body, e));
        }
    }
    let j = choose|j: int| 0 <= j < e.entries.len() && (#[trigger] e.entries[j]).namespace == namespace
        && xattr_entry::name(e.raw, e.entries[j]) == name && xattr_table::value_view(e.raw, e.entries[j]) == b;
    xattr_table::successful_tables_have_one_value_for_each_full_namespace_and_name_key(e, i, j);
}

}
