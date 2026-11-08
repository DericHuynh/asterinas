// SPDX-License-Identifier: MPL-2.0

//! Complete, source-bound xattr entry tables, terminators and immutable values.
//! Full keys, never hashes, establish name identity. Parsing grants no access
//! permission and no authority to follow a returned value-inode descriptor.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, xattr_entry::{self as entry, Entry}};

verus! {

#[verifier::opaque]
pub open spec fn chain(raw: Seq<u8>, entries: Seq<Entry>, first: usize, base: usize, ea: bool, inodes: u32, sorted: bool, end: usize) -> bool {
    &&& raw.len() <= 65536 && first <= end && end as nat + 4 <= raw.len() && base <= raw.len()
    &&& end == if entries.len() == 0 { first } else { entries.last().next }
    &&& (forall|i: int| 0 <= i < entries.len() ==> #[trigger] entry::record(raw, base, ea, inodes, entries[i])
        && entries[i].position == if i == 0 { first } else { entries[i - 1].next })
    &&& (forall|i: int, j: int| 0 <= i < j < entries.len() ==> !entry::same_key(raw, #[trigger] entries[i], #[trigger] entries[j]))
    &&& (sorted ==> forall|i: int| 0 < i < entries.len() ==> #[trigger] entry::key_less(raw, entries[i - 1], entries[i]))
}

proof fn append_record(raw: Seq<u8>, entries: Seq<Entry>, first: usize, base: usize, ea: bool, inodes: u32, sorted: bool, end: usize, e: Entry)
    requires chain(raw, entries, first, base, ea, inodes, sorted, end), entry::record(raw, base, ea, inodes, e), e.position == end,
        forall|i: int| 0 <= i < entries.len() ==> !entry::same_key(raw, #[trigger] entries[i], e),
        sorted && entries.len() > 0 ==> entry::key_less(raw, entries.last(), e),
    ensures chain(raw, entries.push(e), first, base, ea, inodes, sorted, e.next),
{
    reveal(chain); reveal(entry::record);
    assert forall|i: int| 0 <= i < entries.len() + 1 implies #[trigger] entry::record(raw, base, ea, inodes, entries.push(e)[i])
        && entries.push(e)[i].position == if i == 0 { first } else { entries.push(e)[i - 1].next } by {
        if i < entries.len() { assert(entry::record(raw, base, ea, inodes, entries[i])); }
    }
    assert forall|i: int, j: int| 0 <= i < j < entries.len() + 1 implies !entry::same_key(raw, #[trigger] entries.push(e)[i], #[trigger] entries.push(e)[j]) by {
        if j < entries.len() { assert(!entry::same_key(raw, entries[i], entries[j])); }
    }
    if sorted {
        assert forall|i: int| 0 < i < entries.len() + 1 implies #[trigger] entry::key_less(raw, entries.push(e)[i - 1], entries.push(e)[i]) by {
            if i < entries.len() { assert(entry::key_less(raw, entries[i - 1], entries[i])); }
        }
    }
}

fn novel(raw: &[u8], entries: &[Entry], e: Entry, Ghost(base): Ghost<usize>, Ghost(ea): Ghost<bool>, Ghost(inodes): Ghost<u32>) -> (r: bool)
    requires entry::record(raw@, base, ea, inodes, e),
        forall|i: int| 0 <= i < entries.len() ==> #[trigger] entry::record(raw@, base, ea, inodes, entries@[i]),
    ensures r == (forall|i: int| 0 <= i < entries.len() ==> !entry::same_key(raw@, #[trigger] entries@[i], e)),
{
    proof { entry::decoded_entry_has_a_bounded_name(raw@, base, ea, inodes, e); }
    let name = &raw[e.position + 16..e.position + 16 + e.name_length];
    let mut i = 0usize;
    while i < entries.len()
        invariant i <= entries.len(), entry::record(raw@, base, ea, inodes, e),
            name@ == entry::name(raw@, e),
            (forall|j: int| 0 <= j < entries.len() ==> #[trigger] entry::record(raw@, base, ea, inodes, entries@[j])),
            (forall|j: int| 0 <= j < i ==> !entry::same_key(raw@, #[trigger] entries@[j], e)),
        decreases entries.len() - i,
    {
        let old = entries[i];
        proof { entry::decoded_entry_has_a_bounded_name(raw@, base, ea, inodes, old); }
        if old.namespace == e.namespace && bytes::equal(&raw[old.position + 16..old.position + 16 + old.name_length], name) { return false; }
        i += 1;
    }
    true
}

pub struct TableView { pub raw: Seq<u8>, pub entries: Seq<Entry>, pub first: usize, pub base: usize, pub ea: bool, pub inodes: u32, pub sorted: bool, pub end: usize }

#[verifier::opaque]
pub open spec fn valid(v: TableView) -> bool {
    &&& chain(v.raw, v.entries, v.first, v.base, v.ea, v.inodes, v.sorted, v.end)
    &&& bytes::le32(v.raw, v.end as int) == 0
    &&& (forall|i: int| 0 <= i < v.entries.len() ==> (#[trigger] v.entries[i]).value_inode == 0 && v.entries[i].value_size > 0
        ==> v.entries[i].value_offset as nat >= v.end as nat + 4)
}

pub struct Table<'a> { raw: &'a [u8], entries: Vec<Entry>, first: usize, base: usize, ea: bool, inodes: u32, sorted: bool, end: usize }

pub enum ValueRef<'a> { Bytes(&'a [u8]), Inode { number: u32, bytes: u32, hash: u32 } }
pub enum ValueView { Bytes(Seq<u8>), Inode { number: u32, bytes: u32, hash: u32 } }
impl<'a> ValueRef<'a> {
    pub open spec fn view(&self) -> ValueView { match self {
        ValueRef::Bytes(raw) => ValueView::Bytes(raw@), ValueRef::Inode { number, bytes, hash } => ValueView::Inode { number: *number, bytes: *bytes, hash: *hash },
    } }
}

pub open spec fn value_view(raw: Seq<u8>, e: Entry) -> ValueView {
    if e.value_inode != 0 { ValueView::Inode { number: e.value_inode, bytes: e.value_size, hash: e.hash } }
    else { ValueView::Bytes(raw.subrange(e.value_offset as int, e.value_offset as int + e.value_size as int)) }
}

impl<'a> Table<'a> {
    pub closed spec fn view(&self) -> TableView { TableView { raw: self.raw@, entries: self.entries@, first: self.first, base: self.base, ea: self.ea, inodes: self.inodes, sorted: self.sorted, end: self.end } }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn len(&self) -> (r: usize) ensures self.wf(), r == self.view().entries.len() {
        proof { use_type_invariant(self); } self.entries.len()
    }
    pub fn source_bytes(&self) -> (r: &'a [u8]) ensures self.wf(), r@ == self.view().raw {
        proof { use_type_invariant(self); } self.raw
    }
    pub fn metadata(&self, index: usize) -> (r: Option<Entry>)
        ensures self.wf(), match r { Some(e) => index < self.view().entries.len() && e == self.view().entries[index as int], None => index >= self.view().entries.len() },
    {
        proof { use_type_invariant(self); }
        if index < self.entries.len() { Some(self.entries[index]) } else { None }
    }
    pub fn name(&self, index: usize) -> (r: Option<(u8, &'a [u8])>)
        ensures self.wf(), match r { Some((namespace, name)) => index < self.view().entries.len() && namespace == self.view().entries[index as int].namespace
            && name@ == entry::name(self.view().raw, self.view().entries[index as int]), None => index >= self.view().entries.len() },
    {
        let e = match self.metadata(index) { Some(e) => e, None => { return None; } };
        proof { reveal(valid); reveal(chain); entry::decoded_entry_has_a_bounded_name(self.view().raw, self.base, self.ea, self.inodes, e); }
        Some((e.namespace, &self.raw[e.position + 16..e.position + 16 + e.name_length]))
    }
    pub fn value(&self, index: usize) -> (r: Option<ValueRef<'a>>)
        ensures self.wf(), match r { Some(v) => index < self.view().entries.len() && v.view() == value_view(self.view().raw, self.view().entries[index as int]), None => index >= self.view().entries.len() },
    {
        let e = match self.metadata(index) { Some(e) => e, None => { return None; } };
        if e.value_inode != 0 { return Some(ValueRef::Inode { number: e.value_inode, bytes: e.value_size, hash: e.hash }); }
        proof { reveal(valid); reveal(chain); entry::decoded_values_cannot_escape_their_container(self.view().raw, self.base, self.ea, self.inodes, e); }
        Some(ValueRef::Bytes(&self.raw[e.value_offset..e.value_offset + e.value_size as usize]))
    }
    pub fn find(&self, namespace: u8, name: &[u8]) -> (r: Option<usize>)
        ensures self.wf(), match r { Some(i) => i < self.view().entries.len() && self.view().entries[i as int].namespace == namespace && entry::name(self.view().raw, self.view().entries[i as int]) == name@,
            None => forall|i: int| 0 <= i < self.view().entries.len() ==> (#[trigger] self.view().entries[i]).namespace != namespace || entry::name(self.view().raw, self.view().entries[i]) != name@ },
    {
        proof { use_type_invariant(self); }
        let count = self.len();
        let mut i = 0usize;
        while i < count
            invariant self.wf(), i <= count == self.view().entries.len(),
                forall|j: int| 0 <= j < i ==> (#[trigger] self.view().entries[j]).namespace != namespace || entry::name(self.view().raw, self.view().entries[j]) != name@,
            decreases count - i,
        {
            let (tag, key) = self.name(i).unwrap();
            if tag == namespace && bytes::equal(key, name) { return Some(i); }
            i += 1;
        }
        None
    }
}

pub(crate) fn parse(raw: &[u8], first: usize, base: usize, ea: bool, inodes: u32, sorted: bool) -> (r: Option<Table<'_>>)
    ensures match r { Some(table) => table.wf() && table.view().raw == raw@ && table.view().first == first && table.view().base == base
        && table.view().ea == ea && table.view().inodes == inodes && table.view().sorted == sorted, None => true },
{
    if raw.len() > 65536 || first > raw.len() || raw.len() - first < 4 || base > raw.len() { return None; }
    let mut entries = Vec::<Entry>::new();
    let mut offset = first;
    assert(chain(raw@, entries@, first, base, ea, inodes, sorted, offset)) by { reveal(chain); }
    while bytes::read_le32(raw, offset).unwrap() != 0
        invariant chain(raw@, entries@, first, base, ea, inodes, sorted, offset),
            offset + 4 <= raw.len() <= 65536, first <= offset,
        decreases raw.len() - offset,
    {
        let e = match entry::decode(raw, offset, base, ea, inodes) { Some(e) => e, None => { return None; } };
        proof { reveal(chain); entry::decoded_entry_has_a_bounded_name(raw@, base, ea, inodes, e); }
        if !novel(raw, &entries, e, Ghost(base), Ghost(ea), Ghost(inodes)) { return None; }
        if sorted && entries.len() > 0 {
            let old = entries[entries.len() - 1];
            proof { entry::decoded_entry_has_a_bounded_name(raw@, base, ea, inodes, old); }
            if !entry::before(raw, old, e) { return None; }
        }
        proof { append_record(raw@, entries@, first, base, ea, inodes, sorted, offset, e); }
        entries.push(e);
        offset = e.next;
    }
    let mut index = 0usize;
    while index < entries.len()
        invariant chain(raw@, entries@, first, base, ea, inodes, sorted, offset), bytes::le32(raw@, offset as int) == 0,
            offset + 4 <= raw.len() <= 65536,
            index <= entries.len(), forall|i: int| 0 <= i < index && (#[trigger] entries@[i]).value_inode == 0 && entries@[i].value_size > 0 ==> entries@[i].value_offset as nat >= offset as nat + 4,
        decreases entries.len() - index,
    {
        let e = entries[index];
        if e.value_inode == 0 && e.value_size > 0 && e.value_offset < offset + 4 { return None; }
        index += 1;
    }
    assert(valid(TableView { raw: raw@, entries: entries@, first, base, ea, inodes, sorted, end: offset })) by { reveal(valid); }
    Some(Table { raw, entries, first, base, ea, inodes, sorted, end: offset })
}

pub proof fn successful_tables_have_one_value_for_each_full_namespace_and_name_key(v: TableView, i: int, j: int)
    requires valid(v), 0 <= i < v.entries.len(), 0 <= j < v.entries.len(), entry::same_key(v.raw, v.entries[i], v.entries[j]),
    ensures i == j,
{
    reveal(valid); reveal(chain);
    if i < j { assert(!entry::same_key(v.raw, v.entries[i], v.entries[j])); }
    if j < i { assert(!entry::same_key(v.raw, v.entries[j], v.entries[i])); }
}

pub proof fn every_local_value_is_disjoint_from_all_entry_and_terminator_bytes(v: TableView, i: int)
    requires valid(v), 0 <= i < v.entries.len(), v.entries[i].value_inode == 0, v.entries[i].value_size > 0,
    ensures v.entries[i].value_offset as nat >= v.end as nat + 4,
        v.entries[i].value_offset as nat + entry::padded(v.entries[i].value_size as nat) <= v.raw.len(),
{
    reveal(valid); reveal(chain);
    assert(entry::record(v.raw, v.base, v.ea, v.inodes, v.entries[i]));
    entry::decoded_values_cannot_escape_their_container(v.raw, v.base, v.ea, v.inodes, v.entries[i]);
}

}
