// SPDX-License-Identifier: MPL-2.0

//! Complete-table uniqueness and byte framing for checked local-value edits.
//! Immutable tables may contain aliased values; a writable value must be
//! isolated from every other value, including security/ACL namespaces.

use vstd::prelude::*;
use crate::{bytes, xattr_entry::{self as entry, Entry}, xattr_table::{self as table, Table, TableView}};

verus! {

proof fn common_entries_agree(a: TableView, b: TableView, length: nat)
    requires table::valid(a), table::valid(b), a.raw == b.raw, a.first == b.first, a.base == b.base,
        a.ea == b.ea, a.inodes == b.inodes, length <= a.entries.len(), length <= b.entries.len(),
    ensures forall|i: int| 0 <= i < length ==> #[trigger] a.entries[i] == b.entries[i],
    decreases length,
{
    reveal(table::valid); reveal(table::chain); reveal(entry::record);
    if length > 0 {
        common_entries_agree(a, b, (length - 1) as nat);
        let i = length as int - 1;
        assert(entry::record(a.raw, a.base, a.ea, a.inodes, a.entries[i]));
        assert(entry::record(b.raw, b.base, b.ea, b.inodes, b.entries[i]));
        if i > 0 { assert(a.entries[i - 1] == b.entries[i - 1]); }
        assert(a.entries[i].position == b.entries[i].position);
        assert(a.entries[i] == b.entries[i]);
        assert forall|j: int| 0 <= j < length implies #[trigger] a.entries[j] == b.entries[j] by { }
    }
}

pub proof fn two_complete_tables_from_the_same_bytes_have_identical_records(a: TableView, b: TableView)
    requires table::valid(a), table::valid(b), a.raw == b.raw, a.first == b.first, a.base == b.base,
        a.ea == b.ea, a.inodes == b.inodes,
    ensures a.entries == b.entries, a.end == b.end,
{
    reveal(table::valid); reveal(table::chain); reveal(entry::record);
    let count = if a.entries.len() < b.entries.len() { a.entries.len() } else { b.entries.len() };
    common_entries_agree(a, b, count);
    if a.entries.len() < b.entries.len() {
        if a.entries.len() > 0 { assert(a.entries.last() == b.entries[a.entries.len() as int - 1]); }
        assert(entry::record(b.raw, b.base, b.ea, b.inodes, b.entries[a.entries.len() as int]));
        assert(b.entries[a.entries.len() as int].position == a.end);
    }
    if b.entries.len() < a.entries.len() {
        if b.entries.len() > 0 { assert(b.entries.last() == a.entries[b.entries.len() as int - 1]); }
        assert(entry::record(a.raw, a.base, a.ea, a.inodes, a.entries[b.entries.len() as int]));
        assert(a.entries[b.entries.len() as int].position == b.end);
    }
    assert(a.entries =~= b.entries);
}

proof fn positions_are_monotone(v: TableView, a: int, b: int)
    requires table::valid(v), 0 <= a <= b < v.entries.len(),
    ensures v.entries[a].position <= v.entries[b].position,
    decreases b - a,
{
    reveal(table::valid); reveal(table::chain);
    if a < b {
        positions_are_monotone(v, a, b - 1);
        assert(entry::record(v.raw, v.base, v.ea, v.inodes, v.entries[b]));
        assert(entry::record(v.raw, v.base, v.ea, v.inodes, v.entries[b - 1]));
        entry::decoded_entry_has_a_bounded_name(v.raw, v.base, v.ea, v.inodes, v.entries[b - 1]);
    }
}
pub proof fn every_entry_precedes_the_complete_table_terminator(v: TableView, i: int)
    requires table::valid(v), 0 <= i < v.entries.len(),
    ensures v.first <= v.entries[i].position < v.entries[i].next <= v.end,
        v.entries[i].position as nat + 16 + v.entries[i].name_length <= v.entries[i].next,
{
    reveal(table::valid); reveal(table::chain); reveal(entry::record);
    assert(entry::record(v.raw, v.base, v.ea, v.inodes, v.entries[i]));
    assert(entry::record(v.raw, v.base, v.ea, v.inodes, v.entries[0]));
    assert(entry::record(v.raw, v.base, v.ea, v.inodes, v.entries.last()));
    entry::decoded_entry_has_a_bounded_name(v.raw, v.base, v.ea, v.inodes, v.entries[i]);
    positions_are_monotone(v, 0, i);
    if i + 1 < v.entries.len() {
        assert(entry::record(v.raw, v.base, v.ea, v.inodes, v.entries[i + 1]));
        positions_are_monotone(v, i + 1, v.entries.len() as int - 1);
    }
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(v.entries[i].name_length as int + 3, 4);
}

pub open spec fn with_raw(v: TableView, raw: Seq<u8>) -> TableView {
    TableView { raw, entries: v.entries, first: v.first, base: v.base, ea: v.ea, inodes: v.inodes, sorted: v.sorted, end: v.end }
}
pub open spec fn same_structure(v: TableView, after: Seq<u8>) -> bool {
    after.len() == v.raw.len() && forall|i: int| v.first <= i < v.end as nat + 4 ==> #[trigger] after[i] == v.raw[i]
}
pub proof fn preserving_entry_and_terminator_bytes_preserves_the_complete_table(v: TableView, after: Seq<u8>)
    requires table::valid(v), same_structure(v, after),
    ensures table::valid(with_raw(v, after)),
        forall|i: int| 0 <= i < v.entries.len() ==> #[trigger] entry::name(after, v.entries[i]) == entry::name(v.raw, v.entries[i]),
{
    reveal(table::valid); reveal(table::chain);
    assert forall|i: int| 0 <= i < v.entries.len() implies #[trigger] entry::record(after, v.base, v.ea, v.inodes, v.entries[i])
        && entry::name(after, v.entries[i]) == entry::name(v.raw, v.entries[i]) by {
        every_entry_precedes_the_complete_table_terminator(v, i);
        let e = v.entries[i];
        assert(entry::record(v.raw, v.base, v.ea, v.inodes, e));
        assert(entry::name(after, e) =~= entry::name(v.raw, e));
        reveal(entry::record);
        assert forall|j: int| 0 <= j < e.name_length implies #[trigger] after[e.position as int + 16 + j] != 0 by { }
    }
    assert forall|i: int, j: int| 0 <= i < j < v.entries.len() implies !entry::same_key(after, #[trigger] v.entries[i], #[trigger] v.entries[j]) by {
        assert(!entry::same_key(v.raw, v.entries[i], v.entries[j]));
        assert(entry::record(after, v.base, v.ea, v.inodes, v.entries[i]));
        assert(entry::record(after, v.base, v.ea, v.inodes, v.entries[j]));
    }
    if v.sorted {
        assert forall|i: int| 0 < i < v.entries.len() implies #[trigger] entry::key_less(after, v.entries[i - 1], v.entries[i]) by {
            assert(entry::key_less(v.raw, v.entries[i - 1], v.entries[i]));
            assert(entry::record(after, v.base, v.ea, v.inodes, v.entries[i - 1]));
            assert(entry::record(after, v.base, v.ea, v.inodes, v.entries[i]));
        }
    }
    assert forall|i: int| 0 <= i < v.entries.len() implies #[trigger] entry::record(after, v.base, v.ea, v.inodes, v.entries[i])
        && v.entries[i].position == if i == 0 { v.first } else { v.entries[i - 1].next } by {
        assert(entry::record(v.raw, v.base, v.ea, v.inodes, v.entries[i]));
    }
    assert forall|i: int| 0 <= i < v.entries.len() implies #[trigger] entry::name(after, v.entries[i]) == entry::name(v.raw, v.entries[i]) by {
        assert(entry::record(after, v.base, v.ea, v.inodes, v.entries[i]));
    }
    assert(table::chain(after, v.entries, v.first, v.base, v.ea, v.inodes, v.sorted, v.end));
}

pub open spec fn end(e: Entry) -> nat { e.value_offset as nat + entry::padded(e.value_size as nat) }
pub open spec fn apart(a: Entry, b: Entry) -> bool {
    end(a) <= b.value_offset || end(b) <= a.value_offset
}
pub open spec fn isolated(v: TableView, i: usize) -> bool {
    i < v.entries.len() && v.entries[i as int].value_inode == 0 && v.entries[i as int].value_size > 0
        && (forall|j: int| 0 <= j < v.entries.len() && j != i && (#[trigger] v.entries[j]).value_inode == 0 && v.entries[j].value_size > 0
            ==> apart(v.entries[i as int], v.entries[j]))
}
pub fn has_isolated_local_value(value: &Table<'_>, i: usize) -> (r: bool)
    ensures value.wf(), r == isolated(value.view(), i),
{
    let selected = match value.metadata(i) { Some(e) => e, None => { return false; } };
    if selected.value_inode != 0 || selected.value_size == 0 { return false; }
    proof { reveal(table::valid); reveal(table::chain); entry::decoded_values_cannot_escape_their_container(value.view().raw, value.view().base, value.view().ea, value.view().inodes, selected); }
    let selected_end = selected.value_offset as u64 + (selected.value_size as u64 + 3) / 4 * 4;
    let count = value.len();
    let mut j = 0usize;
    while j < count
        invariant value.wf(), i < count == value.view().entries.len(), selected == value.view().entries[i as int],
            selected.value_inode == 0, selected.value_size > 0, selected_end == end(selected), j <= count,
            forall|k: int| 0 <= k < j && k != i && (#[trigger] value.view().entries[k]).value_inode == 0 && value.view().entries[k].value_size > 0
                ==> apart(selected, value.view().entries[k]),
        decreases count - j,
    {
        let other = value.metadata(j).unwrap();
        if j != i && other.value_inode == 0 && other.value_size > 0 {
            proof { reveal(table::valid); reveal(table::chain); entry::decoded_values_cannot_escape_their_container(value.view().raw, value.view().base, value.view().ea, value.view().inodes, other); }
            let other_end = other.value_offset as u64 + (other.value_size as u64 + 3) / 4 * 4;
            if selected_end > other.value_offset as u64 && other_end > selected.value_offset as u64 { return false; }
        }
        j += 1;
    }
    true
}

pub proof fn an_isolated_value_edit_preserves_every_other_value(v: TableView, i: usize, after: Seq<u8>)
    requires table::valid(v), isolated(v, i), same_structure(v, after),
        forall|n: int| v.end as nat + 4 <= n < v.raw.len() && !(v.entries[i as int].value_offset <= n < end(v.entries[i as int])) ==> #[trigger] after[n] == v.raw[n],
    ensures forall|j: int| 0 <= j < v.entries.len() && j != i ==> #[trigger] table::value_view(after, v.entries[j]) == table::value_view(v.raw, v.entries[j]),
{
    reveal(table::valid); reveal(table::chain);
    assert forall|j: int| 0 <= j < v.entries.len() && j != i implies #[trigger] table::value_view(after, v.entries[j]) == table::value_view(v.raw, v.entries[j]) by {
        let other = v.entries[j];
        if other.value_inode == 0 {
            entry::decoded_values_cannot_escape_their_container(v.raw, v.base, v.ea, v.inodes, other);
            assert(after.subrange(other.value_offset as int, other.value_offset as int + other.value_size as int)
                =~= v.raw.subrange(other.value_offset as int, other.value_offset as int + other.value_size as int));
        }
    }
}

}
