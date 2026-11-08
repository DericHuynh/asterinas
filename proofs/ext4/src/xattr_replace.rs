// SPDX-License-Identifier: MPL-2.0

//! Same-length, isolated inode-body user-value replacement with ctime,
//! bounded ordinary-inode disk-version increment and checksum reseal. These owned bytes
//! alone confer no inode, VFS, journal, memory-frame or device authority.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, inode, inode_time, inode_time_fields::{self as fields, Field}, xattr::{self, Body, BodyView},
    xattr_entry as entry, xattr_table::{self as table, TableView, ValueView}, xattr_table_edit as edit};

verus! {

// Linux reserves one internal i_version bit for the queried marker.
pub const MAX_VERSION: u64 = 9223372036854775807;

pub struct Change { pub body: BodyView, pub index: usize, pub data: Seq<u8>, pub number: u32, pub inodes: u32,
    pub seed: u32, pub huge: bool, pub seconds: int, pub nanos: nat }
pub open spec fn selected(c: Change) -> entry::Entry { c.body.table.unwrap().entries[c.index as int] }
pub open spec fn version(raw: Seq<u8>) -> nat { bytes::le32(raw, 36) + 4294967296 * bytes::le32(raw, 152) }
#[verifier::opaque]
pub open spec fn allowed(c: Change) -> bool {
    let t = c.body.table.unwrap(); let e = selected(c);
    &&& xattr::valid_body(c.body) && c.body.table is Some && !c.body.ea && c.body.inodes == c.inodes
    &&& inode::metadata_accepted_with_features(c.body.raw, c.number, c.inodes, c.seed, c.huge)
    &&& t.first == 164 && t.base == 164 && !t.sorted && !t.ea && t.inodes == c.inodes
    &&& edit::isolated(t, c.index) && e.namespace == 1 && e.name_length > 0 && e.hash == 0 && e.value_offset % 4 == 0
    &&& c.data.len() == e.value_size && c.data != c.body.raw.subrange(e.value_offset as int, e.value_offset as int + e.value_size as int)
    &&& inode_time::representable(c.seconds, c.nanos) && version(c.body.raw) < MAX_VERSION
}
pub open spec fn padded_data(c: Change) -> Seq<u8> { c.data + Seq::new((entry::padded(c.data.len()) - c.data.len()) as nat, |i: int| 0u8) }
pub open spec fn replaced(c: Change) -> Seq<u8> { bytes::splice(c.body.raw, selected(c).value_offset as int, padded_data(c)) }
pub open spec fn timed(c: Change) -> Seq<u8> { fields::update(replaced(c), Field::Ctime, c.seconds, c.nanos) }
pub open spec fn versioned(c: Change) -> Seq<u8> {
    let next = version(c.body.raw) + 1;
    bytes::splice(bytes::splice(timed(c), 36, bytes::encoded_le((next % 4294967296) as u32)), 152, bytes::encoded_le((next / 4294967296) as u32))
}
pub open spec fn sealed(raw: Seq<u8>, number: u32, seed: u32) -> Seq<u8> {
    let word = bytes::encoded_le(inode::checksum(raw, number, seed));
    bytes::splice(bytes::splice(raw, 124, word.take(2)), 130, word.skip(2))
}
pub open spec fn result(c: Change) -> Seq<u8> { sealed(versioned(c), c.number, c.seed) }
pub open spec fn changed(c: Change, i: int) -> bool {
    selected(c).value_offset <= i < edit::end(selected(c)) || 12 <= i < 16 || 36 <= i < 40
        || 124 <= i < 126 || 130 <= i < 136 || 152 <= i < 156
}
pub open spec fn after_body(c: Change) -> BodyView {
    BodyView { raw: result(c), table: Some(edit::with_raw(c.body.table.unwrap(), result(c))), ea: c.body.ea, inodes: c.body.inodes }
}

proof fn resealing_recovers_the_inode_checksum(raw: Seq<u8>, number: u32, seed: u32)
    requires raw.len() == 256,
    ensures sealed(raw, number, seed).len() == 256,
        bytes::le16(sealed(raw, number, seed), 124) + 65536 * bytes::le16(sealed(raw, number, seed), 130)
            == inode::checksum(sealed(raw, number, seed), number, seed) as nat,
{
    hide(crate::crc::fold);
    let checksum = inode::checksum(raw, number, seed);
    bytes::little_endian_encoding_recovers_every_word(checksum);
    let after = sealed(raw, number, seed);
    assert(inode::checksum_input(after) =~= inode::checksum_input(raw));
    assert(bytes::le32(after, 100) == bytes::le32(raw, 100));
    assert(inode::checksum(after, number, seed) == checksum);
}

pub proof fn replacement_changes_only_its_value_ctime_version_and_checksum(c: Change, i: int)
    requires allowed(c), 0 <= i < 256, !changed(c, i),
    ensures result(c)[i] == c.body.raw[i],
{
    reveal(allowed); reveal(table::valid); reveal(table::chain);
    let e = selected(c); let t = c.body.table.unwrap();
    table::every_local_value_is_disjoint_from_all_entry_and_terminator_bytes(t, c.index as int);
    entry::decoded_values_cannot_escape_their_container(t.raw, t.base, t.ea, t.inodes, e);
    assert(padded_data(c).len() == entry::padded(e.value_size as nat));
    assert(replaced(c)[i] == c.body.raw[i]);
    fields::time_updates_preserve_every_unrelated_inode_byte(replaced(c), Field::Ctime, c.seconds, c.nanos, i);
}
proof fn sealing_and_ctime_preserve_all_body_bytes(c: Change, i: int)
    requires allowed(c), 160 <= i < 256,
    ensures result(c)[i] == replaced(c)[i],
{
    reveal(allowed); reveal(table::valid); reveal(table::chain);
    let e = selected(c); let t = c.body.table.unwrap();
    table::every_local_value_is_disjoint_from_all_entry_and_terminator_bytes(t, c.index as int);
    entry::decoded_values_cannot_escape_their_container(t.raw, t.base, t.ea, t.inodes, e);
    assert(padded_data(c).len() == entry::padded(e.value_size as nat));
    fields::time_updates_preserve_every_unrelated_inode_byte(replaced(c), Field::Ctime, c.seconds, c.nanos, i);
}

#[verifier::rlimit(25)]
pub proof fn replacement_retains_inode_and_table_validity_and_every_other_attribute(c: Change)
    requires allowed(c),
    ensures inode::metadata_accepted_with_features(result(c), c.number, c.inodes, c.seed, c.huge), xattr::valid_body(after_body(c)),
        table::value_view(result(c), selected(c)) == ValueView::Bytes(c.data),
        version(result(c)) == version(c.body.raw) + 1, version(result(c)) <= MAX_VERSION,
        fields::seconds(result(c), Field::Ctime) == c.seconds, fields::nanoseconds(result(c), Field::Ctime) == c.nanos,
        forall|j: int| 0 <= j < c.body.table.unwrap().entries.len() && j != c.index ==>
            #[trigger] table::value_view(result(c), c.body.table.unwrap().entries[j]) == table::value_view(c.body.raw, c.body.table.unwrap().entries[j]),
{
    hide(crate::crc::fold);
    reveal(allowed); reveal(table::valid); reveal(table::chain);
    let t = c.body.table.unwrap(); let e = selected(c);
    table::every_local_value_is_disjoint_from_all_entry_and_terminator_bytes(t, c.index as int);
    entry::decoded_values_cannot_escape_their_container(t.raw, t.base, t.ea, t.inodes, e);
    assert(padded_data(c).len() == entry::padded(e.value_size as nat));
    assert(replaced(c).len() == 256 && fields::can_set(replaced(c), Field::Ctime, c.seconds, c.nanos));
    fields::updated_field_decodes_to_the_requested_time(replaced(c), Field::Ctime, c.seconds, c.nanos);
    let next = version(c.body.raw) + 1;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(next as int, 4294967296);
    bytes::little_endian_encoding_recovers_every_word((next % 4294967296) as u32);
    bytes::little_endian_encoding_recovers_every_word((next / 4294967296) as u32);
    resealing_recovers_the_inode_checksum(versioned(c), c.number, c.seed);
    assert forall|i: int| 0 <= i < 256 && !changed(c, i) implies (#[trigger] result(c)[i]) == c.body.raw[i] by {
        replacement_changes_only_its_value_ctime_version_and_checksum(c, i);
    }
    assert forall|i: int| 160 <= i < 256 implies (#[trigger] result(c)[i]) == replaced(c)[i] by { sealing_and_ctime_preserve_all_body_bytes(c, i); }
    assert(result(c).subrange(e.value_offset as int, e.value_offset as int + e.value_size as int) =~= c.data);
    assert(edit::same_structure(t, result(c)));
    edit::preserving_entry_and_terminator_bytes_preserves_the_complete_table(t, result(c));
    edit::an_isolated_value_edit_preserves_every_other_value(t, c.index, result(c));
    assert(xattr::valid_body(after_body(c)));
}

pub fn encode(body: &Body<'_>, index: usize, data: &[u8], number: u32, inodes: u32, seed: u32, huge: bool, seconds: i64, nanos: u32) -> (r: Option<Vec<u8>>)
    ensures body.wf(), match r { Some(raw) => allowed(Change { body: body.view(), index, data: data@, number, inodes, seed, huge, seconds: seconds as int, nanos: nanos as nat })
        && raw@ == result(Change { body: body.view(), index, data: data@, number, inodes, seed, huge, seconds: seconds as int, nanos: nanos as nat }), None => true },
{
    hide(crate::crc::fold);
    let (ea, bound_inodes) = body.parameters();
    if ea || bound_inodes != inodes { return None; }
    let table = match body.entry_table() { Some(table) => table, None => { return None; } };
    let raw = table.source_bytes();
    if raw.len() != 256 { return None; }
    match inode::parse_metadata_with_features(raw, number, inodes, seed, huge) { Some(_) => {}, None => { return None; } }
    let e = match table.metadata(index) { Some(e) => e, None => { return None; } };
    if e.namespace != 1 || e.name_length == 0 || e.hash != 0 || e.value_offset % 4 != 0
        || e.value_size == 0 || e.value_inode != 0 || data.len() != e.value_size as usize { return None; }
    if !edit::has_isolated_local_value(table, index) { return None; }
    proof { reveal(table::valid); reveal(table::chain); entry::decoded_values_cannot_escape_their_container(table.view().raw, table.view().base, table.view().ea, table.view().inodes, e); }
    if bytes::equal(&raw[e.value_offset..e.value_offset + data.len()], data) { return None; }
    if seconds < inode_time::MIN_SECONDS || seconds > inode_time::MAX_SECONDS || nanos >= 1000000000 { return None; }
    let old_version = bytes::read_le32(raw, 36).unwrap() as u64 + 4294967296 * bytes::read_le32(raw, 152).unwrap() as u64;
    if old_version >= MAX_VERSION { return None; }
    let next = old_version + 1;
    let ghost c = Change { body: body.view(), index, data: data@, number, inodes, seed, huge, seconds: seconds as int, nanos: nanos as nat };
    assert(allowed(c)) by { reveal(allowed); }
    let mut copy = Vec::<u8>::new();
    let mut i = 0usize;
    while i < 256 invariant i <= 256, raw.len() == 256, copy@ == raw@.take(i as int), decreases 256 - i,
    { copy.push(raw[i]); assert(copy@ =~= raw@.take(i as int + 1)); i += 1; }
    assert(copy@ =~= raw@);
    let padding = (data.len() + 3) / 4 * 4;
    let mut value = Vec::new();
    let mut i = 0usize;
    while i < padding
        invariant data.len() <= padding <= 256, padding == entry::padded(data.len() as nat), i <= padding,
            value@ == padded_data(c).take(i as int), c.data == data@,
        decreases padding - i,
    { value.push(if i < data.len() { data[i] } else { 0u8 }); assert(value@ =~= padded_data(c).take(i as int + 1)); i += 1; }
    if !bytes::write_bytes(copy.as_mut_slice(), e.value_offset, &value) { return None; }
    assert(copy@ == replaced(c));
    if !fields::set_time(copy.as_mut_slice(), Field::Ctime, seconds, nanos) { return None; }
    assert(copy@ == timed(c));
    bytes::write_le32(copy.as_mut_slice(), 36, (next % 4294967296) as u32);
    bytes::write_le32(copy.as_mut_slice(), 152, (next / 4294967296) as u32);
    assert(copy@ == versioned(c));
    let checksum = inode::calculated_checksum(&copy, number, seed).unwrap();
    let word = bytes::encode_le32(checksum);
    bytes::write_bytes(copy.as_mut_slice(), 124, &word[..2]);
    bytes::write_bytes(copy.as_mut_slice(), 130, &word[2..]);
    assert(copy@ == result(c));
    Some(copy)
}

}
