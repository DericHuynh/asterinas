// SPDX-License-Identifier: MPL-2.0

//! Check generated xattr padding and Linux hash fields against complete bytes.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, xattr_entry as entry, xattr_hash, xattr_table::{self as table, Table, TableView, ValueRef, ValueView}};

verus! {

pub open spec fn zeros(raw: Seq<u8>, first: int, end: int) -> bool {
    0 <= first <= end <= raw.len() && forall|i: int| first <= i < end ==> #[trigger] raw[i] == 0
}
pub open spec fn exact(v: TableView, i: int, external: bool) -> bool {
    let e = v.entries[i];
    &&& e.value_inode == 0
    &&& zeros(v.raw, e.position as int + 16 + e.name_length, e.next as int)
    &&& zeros(v.raw, e.value_offset as int + e.value_size, e.value_offset as int + entry::padded(e.value_size as nat))
    &&& e.hash == if external { xattr_hash::entry(entry::name(v.raw, e), match table::value_view(v.raw, e) { ValueView::Bytes(value) => value, _ => Seq::empty() }) } else { 0u32 }
}
pub open spec fn hashes(v: TableView) -> Seq<u32> { Seq::new(v.entries.len(), |i: int| v.entries[i].hash) }
pub open spec fn canonical(v: TableView, external: bool) -> bool {
    v.entries.len() <= 260 && (forall|i: int| 0 <= i < v.entries.len() ==> #[trigger] exact(v, i, external))
        && (external ==> bytes::le32(v.raw, 12) == xattr_hash::prefix(hashes(v), hashes(v).len()) as nat)
}
fn zero_span(raw: &[u8], first: usize, end: usize) -> (r: bool) ensures r ==> zeros(raw@, first as int, end as int) {
    if first > end || end > raw.len() { return false; }
    let mut i = first;
    while i < end invariant first <= i <= end <= raw.len(), forall|j: int| first <= j < i ==> #[trigger] raw@[j] == 0, decreases end - i,
    { if raw[i] != 0 { return false; } i += 1; }
    true
}
pub fn check(value: &Table<'_>, external: bool) -> (r: bool)
    ensures value.wf(), r ==> canonical(value.view(), external),
{
    let n = value.len(); if n > 260 { return false; }
    let raw = value.source_bytes(); if raw.len() < 16 { return false; }
    let mut hashes = Vec::new(); let mut i = 0usize;
    while i < n
        invariant value.wf(), n == value.view().entries.len(), i <= n <= 260, raw@ == value.view().raw, raw.len() >= 16,
            hashes.len() == i, hashes@ == self::hashes(value.view()).take(i as int),
            forall|j: int| 0 <= j < i ==> #[trigger] exact(value.view(), j, external),
        decreases n - i,
    {
        let e = value.metadata(i).unwrap(); let (_, name) = value.name(i).unwrap();
        let data = match value.value(i).unwrap() { ValueRef::Bytes(data) => data, _ => { return false; } };
        if e.position > 65536 || e.name_length > 255 || e.value_offset > 65536 || e.value_size > 65536 { return false; }
        let end = e.value_offset + (e.value_size as usize + 3) / 4 * 4;
        if !zero_span(raw, e.position + 16 + e.name_length, e.next) || !zero_span(raw, e.value_offset + e.value_size as usize, end) { return false; }
        if external { let hash = match xattr_hash::entry_hash(name, data) { Some(hash) => hash, None => { return false; } }; if hash != e.hash { return false; } }
        else if e.hash != 0 { return false; }
        hashes.push(e.hash); assert(hashes@ =~= self::hashes(value.view()).take(i as int + 1));
        assert(exact(value.view(), i as int, external)); i += 1;
    }
    assert(hashes@ =~= self::hashes(value.view()));
    if external { let hash = xattr_hash::block_hash(&hashes).unwrap(); if bytes::read_le32(raw, 12).unwrap() != hash { return false; } }
    true
}

pub proof fn canonical_images_expose_no_nonzero_name_or_value_padding(v: TableView, external: bool, i: int)
    requires canonical(v, external), 0 <= i < v.entries.len(),
    ensures zeros(v.raw, v.entries[i].position as int + 16 + v.entries[i].name_length, v.entries[i].next as int),
        zeros(v.raw, v.entries[i].value_offset as int + v.entries[i].value_size,
            v.entries[i].value_offset as int + entry::padded(v.entries[i].value_size as nat)),
{ assert(exact(v, i, external)); }

}
