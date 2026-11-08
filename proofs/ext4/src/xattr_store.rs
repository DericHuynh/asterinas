// SPDX-License-Identifier: MPL-2.0

//! Owned complete-key xattr values and Linux create/replace/remove semantics.
//! This layer owns bytes, not filesystem blocks or credential authority.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, xattr_entry, xattr_table::{self, Table, ValueRef}};

verus! {

pub const MAX_ENTRIES: usize = 260;
pub const MAX_VALUE: usize = 65536;
pub struct ItemView { pub namespace: u8, pub name: Seq<u8>, pub value: Seq<u8> }
pub open spec fn key_good(namespace: u8, name: Seq<u8>) -> bool {
    namespace > 0 && name.len() <= 255 && forall|i: int| 0 <= i < name.len() ==> #[trigger] name[i] != 0
}
pub open spec fn good(e: ItemView) -> bool { key_good(e.namespace, e.name) && e.value.len() <= MAX_VALUE }
pub open spec fn same_key(a: ItemView, b: ItemView) -> bool { a.namespace == b.namespace && a.name == b.name }
#[verifier::opaque]
pub open spec fn valid(v: Seq<ItemView>) -> bool {
    v.len() <= MAX_ENTRIES && (forall|i: int| 0 <= i < v.len() ==> #[trigger] good(v[i]))
        && forall|i: int, j: int| 0 <= i < j < v.len() ==> !same_key(#[trigger] v[i], #[trigger] v[j])
}
pub open spec fn lookup_index(v: Seq<ItemView>, namespace: u8, name: Seq<u8>) -> Option<int> {
    if exists|i: int| 0 <= i < v.len() && (#[trigger] v[i]).namespace == namespace && v[i].name == name {
        Some(choose|i: int| 0 <= i < v.len() && (#[trigger] v[i]).namespace == namespace && v[i].name == name)
    } else { None }
}
pub open spec fn get(v: Seq<ItemView>, namespace: u8, name: Seq<u8>) -> Option<Seq<u8>> {
    match lookup_index(v, namespace, name) { Some(i) => Some(v[i].value), None => None }
}
pub open spec fn updated(v: Seq<ItemView>, namespace: u8, name: Seq<u8>, value: Seq<u8>) -> Seq<ItemView> {
    let next = ItemView { namespace, name, value };
    match lookup_index(v, namespace, name) { Some(i) => v.update(i, next), None => v.push(next) }
}
pub open spec fn deleted(v: Seq<ItemView>, namespace: u8, name: Seq<u8>) -> Seq<ItemView> {
    match lookup_index(v, namespace, name) { Some(i) => v.remove(i), None => v }
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Error { InvalidKey, ValueTooLarge, InvalidFlags, Exists, Missing, EntryLimit }
pub open spec fn set_error(v: Seq<ItemView>, namespace: u8, name: Seq<u8>, value: Seq<u8>, flags: u32) -> Option<Error> {
    if !key_good(namespace, name) { Some(Error::InvalidKey) } else if value.len() > MAX_VALUE { Some(Error::ValueTooLarge) }
    else if flags & !3u32 != 0 { Some(Error::InvalidFlags) }
    else if lookup_index(v, namespace, name).is_some() && flags & 1 != 0 { Some(Error::Exists) }
    else if lookup_index(v, namespace, name).is_none() && flags & 2 != 0 { Some(Error::Missing) }
    else if lookup_index(v, namespace, name).is_none() && v.len() >= MAX_ENTRIES { Some(Error::EntryLimit) } else { None }
}
pub open spec fn remove_error(v: Seq<ItemView>, namespace: u8, name: Seq<u8>) -> Option<Error> {
    if !key_good(namespace, name) { Some(Error::InvalidKey) } else if lookup_index(v, namespace, name).is_none() { Some(Error::Missing) } else { None }
}
pub proof fn a_complete_key_has_one_owned_value(v: Seq<ItemView>, i: int, j: int)
    requires valid(v), 0 <= i < v.len(), 0 <= j < v.len(), same_key(v[i], v[j]),
    ensures i == j,
{ reveal(valid); }
proof fn setting_a_full_key_preserves_unique_well_formed_values(v: Seq<ItemView>, namespace: u8, name: Seq<u8>, value: Seq<u8>)
    requires valid(v), key_good(namespace, name), value.len() <= MAX_VALUE, lookup_index(v, namespace, name).is_none() ==> v.len() < MAX_ENTRIES,
    ensures valid(updated(v, namespace, name, value)),
{
    reveal(valid);
    let next = ItemView { namespace, name, value };
    let after = updated(v, namespace, name, value);
    if let Some(k) = lookup_index(v, namespace, name) {
        assert forall|i: int, j: int| 0 <= i < j < after.len() implies !same_key(#[trigger] after[i], #[trigger] after[j]) by {
            if i == k || j == k { assert(same_key(next, v[k])); }
        }
    } else {
        assert forall|i: int, j: int| 0 <= i < j < after.len() implies !same_key(#[trigger] after[i], #[trigger] after[j]) by {
            if j == v.len() { assert(v[i].namespace != namespace || v[i].name != name); }
        }
    }
    assert forall|i: int| 0 <= i < after.len() implies #[trigger] good(after[i]) by { }
}
proof fn removing_a_full_key_preserves_unique_well_formed_values(v: Seq<ItemView>, namespace: u8, name: Seq<u8>)
    requires valid(v), ensures valid(deleted(v, namespace, name)),
{
    reveal(valid);
    let after = deleted(v, namespace, name);
    if let Some(k) = lookup_index(v, namespace, name) {
        assert forall|i: int| 0 <= i < after.len() implies #[trigger] good(after[i]) by {
            assert(after[i] == v[if i < k { i } else { i + 1 }]);
        }
        assert forall|i: int, j: int| 0 <= i < j < after.len() implies !same_key(#[trigger] after[i], #[trigger] after[j]) by {
            let a = if i < k { i } else { i + 1 }; let b = if j < k { j } else { j + 1 };
            assert(a < b && !same_key(v[a], v[b]));
        }
    }
}

pub struct Item { namespace: u8, name: Vec<u8>, value: Vec<u8> }
impl Item {
    pub closed spec fn view(&self) -> ItemView { ItemView { namespace: self.namespace, name: self.name@, value: self.value@ } }
    pub fn key(&self) -> (r: (u8, &[u8])) ensures r.0 == self.view().namespace, r.1@ == self.view().name { (self.namespace, &self.name) }
    pub fn bytes(&self) -> (r: &[u8]) ensures r@ == self.view().value { &self.value }
}
pub open spec fn views(v: Seq<Item>) -> Seq<ItemView> { Seq::new(v.len(), |i: int| v[i].view()) }
fn copy(raw: &[u8]) -> (r: Vec<u8>) requires raw.len() <= MAX_VALUE, ensures r@ == raw@ {
    let mut result = Vec::new(); let mut i = 0usize;
    while i < raw.len() invariant i <= raw.len() <= MAX_VALUE, result@ == raw@.take(i as int), decreases raw.len() - i,
    { result.push(raw[i]); assert(result@ =~= raw@.take(i as int + 1)); i += 1; }
    result
}
fn valid_key(namespace: u8, name: &[u8]) -> (r: bool) ensures r == key_good(namespace, name@) {
    if namespace == 0 || name.len() > 255 { return false; }
    let mut i = 0usize;
    while i < name.len() invariant i <= name.len(), forall|j: int| 0 <= j < i ==> #[trigger] name@[j] != 0, decreases name.len() - i,
    { if name[i] == 0 { return false; } i += 1; }
    true
}

pub struct Store { items: Vec<Item> }
impl Store {
    pub closed spec fn view(&self) -> Seq<ItemView> { views(self.items@) }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn new() -> (r: Self) ensures r.wf(), r.view().len() == 0 {
        let items = Vec::new(); assert(valid(views(items@))) by { reveal(valid); } Store { items }
    }
    pub fn len(&self) -> (r: usize) ensures self.wf(), r == self.view().len(), r <= MAX_ENTRIES {
        proof { use_type_invariant(self); reveal(valid); } self.items.len()
    }
    pub fn item(&self, i: usize) -> (r: Option<&Item>)
        ensures self.wf(), match r { Some(item) => i < self.view().len() && item.view() == self.view()[i as int], None => i >= self.view().len() },
    { proof { use_type_invariant(self); } if i < self.items.len() { Some(&self.items[i]) } else { None } }
    pub fn find(&self, namespace: u8, name: &[u8]) -> (r: Option<usize>)
        ensures self.wf(), match r { Some(i) => lookup_index(self.view(), namespace, name@) == Some(i as int), None => lookup_index(self.view(), namespace, name@).is_none() },
    {
        proof { use_type_invariant(self); }
        let count = self.items.len(); let mut i = 0usize;
        while i < count
            invariant self.wf(), i <= count == self.view().len(),
                forall|j: int| 0 <= j < i ==> (#[trigger] self.view()[j]).namespace != namespace || self.view()[j].name != name@,
            decreases count - i,
        {
            let item = &self.items[i];
            if item.namespace == namespace && bytes::equal(&item.name, name) {
                proof {
                    assert(self.view()[i as int].namespace == namespace && self.view()[i as int].name == name@);
                    assert(exists|j: int| 0 <= j < self.view().len() && (#[trigger] self.view()[j]).namespace == namespace && self.view()[j].name == name@);
                    assert(lookup_index(self.view(), namespace, name@).is_some());
                    let k = lookup_index(self.view(), namespace, name@).unwrap();
                    a_complete_key_has_one_owned_value(self.view(), i as int, k);
                }
                return Some(i);
            }
            i += 1;
        }
        None
    }
    pub fn set(self, namespace: u8, name: &[u8], value: &[u8], flags: u32) -> (r: Result<Self, (Self, Error)>)
        ensures self.wf(), match r {
            Ok(next) => next.wf() && set_error(self.view(), namespace, name@, value@, flags).is_none() && next.view() == updated(self.view(), namespace, name@, value@),
            Err((original, error)) => original.wf() && original.view() == self.view() && set_error(self.view(), namespace, name@, value@, flags) == Some(error),
        },
    {
        proof { use_type_invariant(&self); }
        if !valid_key(namespace, name) { return Err((self, Error::InvalidKey)); }
        if value.len() > MAX_VALUE { return Err((self, Error::ValueTooLarge)); }
        if flags & !3u32 != 0 { return Err((self, Error::InvalidFlags)); }
        let position = self.find(namespace, name);
        if position.is_some() && flags & 1 != 0 { return Err((self, Error::Exists)); }
        if position.is_none() && flags & 2 != 0 { return Err((self, Error::Missing)); }
        if position.is_none() && self.items.len() >= MAX_ENTRIES { return Err((self, Error::EntryLimit)); }
        let ghost before = self.view();
        let item = Item { namespace, name: copy(name), value: copy(value) };
        let Store { mut items } = self;
        match position { Some(i) => { items.set(i, item); }, None => { items.push(item); } }
        assert(views(items@) =~= updated(before, namespace, name@, value@));
        proof { setting_a_full_key_preserves_unique_well_formed_values(before, namespace, name@, value@); }
        Ok(Store { items })
    }
    pub fn remove(self, namespace: u8, name: &[u8]) -> (r: Result<Self, (Self, Error)>)
        ensures self.wf(), match r {
            Ok(next) => next.wf() && remove_error(self.view(), namespace, name@).is_none() && next.view() == deleted(self.view(), namespace, name@),
            Err((original, error)) => original.wf() && original.view() == self.view() && remove_error(self.view(), namespace, name@) == Some(error),
        },
    {
        proof { use_type_invariant(&self); }
        if !valid_key(namespace, name) { return Err((self, Error::InvalidKey)); }
        let i = match self.find(namespace, name) { Some(i) => i, None => { return Err((self, Error::Missing)); } };
        let ghost before = self.view();
        let Store { mut items } = self;
        items.remove(i);
        assert(views(items@) =~= deleted(before, namespace, name@));
        proof { removing_a_full_key_preserves_unique_well_formed_values(before, namespace, name@); }
        Ok(Store { items })
    }
}

pub proof fn set_preserves_every_other_complete_key(v: Seq<ItemView>, namespace: u8, name: Seq<u8>, value: Seq<u8>, other_namespace: u8, other_name: Seq<u8>)
    requires valid(v), key_good(namespace, name), value.len() <= MAX_VALUE, lookup_index(v, namespace, name).is_none() ==> v.len() < MAX_ENTRIES,
        namespace != other_namespace || name != other_name,
    ensures get(updated(v, namespace, name, value), other_namespace, other_name) == get(v, other_namespace, other_name),
{
    setting_a_full_key_preserves_unique_well_formed_values(v, namespace, name, value);
    reveal(valid);
    let after = updated(v, namespace, name, value);
    if let Some(i) = lookup_index(v, other_namespace, other_name) {
        assert(after[i].namespace == other_namespace && after[i].name == other_name && after[i].value == v[i].value);
        assert(lookup_index(after, other_namespace, other_name).is_some());
        a_complete_key_has_one_owned_value(after, i, lookup_index(after, other_namespace, other_name).unwrap());
    } else if let Some(j) = lookup_index(after, other_namespace, other_name) {
        assert(j < v.len());
        assert(v[j].namespace == other_namespace && v[j].name == other_name);
    }
}

pub open spec fn table_items(v: xattr_table::TableView) -> Seq<ItemView> {
    Seq::new(v.entries.len(), |i: int| ItemView { namespace: v.entries[i].namespace,
        name: xattr_entry::name(v.raw, v.entries[i]), value: match xattr_table::value_view(v.raw, v.entries[i]) {
            xattr_table::ValueView::Bytes(value) => value, xattr_table::ValueView::Inode { .. } => Seq::empty(),
        } })
}
pub open spec fn source_items(v: crate::xattr_inode::AttributesView) -> Seq<ItemView> {
    (match v.body.table { Some(table) => table_items(table), None => Seq::empty() })
        + (match v.external { Some(table) => table_items(table), None => Seq::empty() })
}
impl Store {
    pub fn extend_table(self, table: &Table<'_>) -> (r: Option<Self>)
        ensures self.wf(), table.wf(), match r { Some(next) => next.wf() && next.view() == self.view() + table_items(table.view()), None => true },
    {
        proof { use_type_invariant(&self); }
        let ghost original = self.view();
        let count = table.len();
        if count > MAX_ENTRIES { return None; }
        let mut current = self; let mut i = 0usize;
        while i < count
            invariant valid(original), original == self.view(), table.wf(), i <= count <= MAX_ENTRIES, count == table.view().entries.len(), current.wf(),
                current.view() == original + table_items(table.view()).take(i as int),
            decreases count - i,
        {
            let (namespace, name) = table.name(i).unwrap();
            let value = match table.value(i).unwrap() { ValueRef::Bytes(value) => value, _ => { return None; } };
            if current.find(namespace, name).is_some() { return None; }
            let ghost previous = current.view();
            current = match current.set(namespace, name, value, 1) { Ok(next) => next, Err(_) => { return None; } };
            assert(lookup_index(previous, namespace, name@).is_none());
            assert(current.view() =~= original + table_items(table.view()).take(i as int + 1));
            i += 1;
        }
        Some(current)
    }
}
pub fn capture(attributes: &crate::xattr_inode::Attributes<'_>) -> (r: Option<Store>)
    ensures attributes.wf(), match r { Some(store) => store.wf() && store.view() == source_items(attributes.view()), None => true },
{
    let (body, external) = attributes.source_tables();
    let mut store = Store::new();
    if let Some(table) = body { store = match store.extend_table(table) { Some(next) => next, None => { return None; } }; }
    if let Some(table) = external { store = match store.extend_table(table) { Some(next) => next, None => { return None; } }; }
    Some(store)
}

pub proof fn setting_a_complete_key_returns_the_requested_value(v: Seq<ItemView>, namespace: u8, name: Seq<u8>, value: Seq<u8>)
    requires valid(v), key_good(namespace, name), value.len() <= MAX_VALUE, lookup_index(v, namespace, name).is_none() ==> v.len() < MAX_ENTRIES,
    ensures get(updated(v, namespace, name, value), namespace, name) == Some(value),
{
    setting_a_full_key_preserves_unique_well_formed_values(v, namespace, name, value);
    let after = updated(v, namespace, name, value);
    let i = if let Some(k) = lookup_index(v, namespace, name) { k } else { v.len() as int };
    assert(after[i].namespace == namespace && after[i].name == name && after[i].value == value);
    assert(lookup_index(after, namespace, name).is_some());
    a_complete_key_has_one_owned_value(after, i, lookup_index(after, namespace, name).unwrap());
}
pub proof fn removing_a_complete_key_removes_only_that_key(v: Seq<ItemView>, namespace: u8, name: Seq<u8>, other_namespace: u8, other_name: Seq<u8>)
    requires valid(v),
    ensures get(deleted(v, namespace, name), namespace, name).is_none(),
        namespace != other_namespace || name != other_name ==> get(deleted(v, namespace, name), other_namespace, other_name) == get(v, other_namespace, other_name),
{
    removing_a_full_key_preserves_unique_well_formed_values(v, namespace, name);
    reveal(valid);
    let after = deleted(v, namespace, name);
    if let Some(k) = lookup_index(v, namespace, name) {
        if let Some(j) = lookup_index(after, namespace, name) {
            let old = if j < k { j } else { j + 1 };
            assert(same_key(v[k], v[old]));
            a_complete_key_has_one_owned_value(v, k, old);
        }
        if namespace != other_namespace || name != other_name {
            if let Some(i) = lookup_index(v, other_namespace, other_name) {
                assert(i != k);
                let j = if i < k { i } else { i - 1 };
                assert(after[j].namespace == other_namespace && after[j].name == other_name && after[j].value == v[i].value);
                assert(lookup_index(after, other_namespace, other_name).is_some());
                a_complete_key_has_one_owned_value(after, j, lookup_index(after, other_namespace, other_name).unwrap());
            } else if let Some(j) = lookup_index(after, other_namespace, other_name) {
                let old = if j < k { j } else { j + 1 };
                assert(v[old].namespace == other_namespace && v[old].name == other_name);
            }
        }
    }
}
pub open spec fn has(v: Seq<ItemView>, item: ItemView) -> bool { exists|j: int| 0 <= j < v.len() && #[trigger] v[j] == item }
pub open spec fn subset(a: Seq<ItemView>, b: Seq<ItemView>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> #[trigger] has(b, a[i])
}
pub open spec fn same_contents(a: Seq<ItemView>, b: Seq<ItemView>) -> bool { subset(a, b) && subset(b, a) }
impl Store {
    fn contained_in(&self, other: &Self) -> (r: bool)
        ensures self.wf(), other.wf(), r ==> subset(self.view(), other.view()),
    {
        proof { use_type_invariant(self); use_type_invariant(other); }
        let n = self.len(); let mut i = 0usize;
        while i < n
            invariant self.wf(), other.wf(), n == self.view().len(), n <= 260, i <= n,
                forall|k: int| 0 <= k < i ==> #[trigger] has(other.view(), self.view()[k]),
            decreases n - i,
        {
            let item = self.item(i).unwrap(); let (namespace, name) = item.key();
            let j = match other.find(namespace, name) { Some(j) => j, None => { return false; } };
            let selected = other.item(j).unwrap();
            if !bytes::equal(item.bytes(), selected.bytes()) { return false; }
            assert(other.view()[j as int] == self.view()[i as int]);
            assert(exists|k: int| 0 <= k < other.view().len() && #[trigger] other.view()[k] == self.view()[i as int]);
            assert(has(other.view(), self.view()[i as int]));
            i += 1;
        }
        assert(subset(self.view(), other.view()));
        true
    }
    pub fn equivalent(&self, other: &Self) -> (r: bool)
        ensures self.wf(), other.wf(), r ==> same_contents(self.view(), other.view()),
    { self.contained_in(other) && other.contained_in(self) }
}
pub proof fn equivalent_stores_have_identical_full_key_lookup(a: Seq<ItemView>, b: Seq<ItemView>, namespace: u8, name: Seq<u8>)
    requires valid(a), valid(b), same_contents(a, b),
    ensures get(a, namespace, name) == get(b, namespace, name),
{
    if let Some(i) = lookup_index(a, namespace, name) {
        assert(has(b, a[i]));
        assert(exists|j: int| 0 <= j < b.len() && #[trigger] b[j] == #[trigger] a[i]);
        let j = choose|j: int| 0 <= j < b.len() && #[trigger] b[j] == #[trigger] a[i];
        assert(lookup_index(b, namespace, name).is_some());
        a_complete_key_has_one_owned_value(b, j, lookup_index(b, namespace, name).unwrap());
    } else if let Some(j) = lookup_index(b, namespace, name) {
        assert(has(a, b[j]));
        assert(exists|i: int| 0 <= i < a.len() && #[trigger] a[i] == b[j]);
        let i = choose|i: int| 0 <= i < a.len() && #[trigger] a[i] == b[j];
        assert(lookup_index(a, namespace, name).is_some());
    }
}

}
