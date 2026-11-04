// SPDX-License-Identifier: MPL-2.0

//! Range-checked ext4 inode time fields. Extended-word presence follows the
//! actual i_extra_isize and buffer size. Updating fields does not reseal the
//! inode checksum or confer a filesystem-operation/clock authority.

use vstd::prelude::*;
use crate::{bytes, inode_time::{self, Timestamp}};

verus! {

#[derive(Clone, Copy)]
pub enum Field { Atime, Ctime, Mtime, Crtime }

pub open spec fn base_offset(field: Field) -> nat {
    match field { Field::Atime => 8, Field::Ctime => 12, Field::Mtime => 16, Field::Crtime => 144 }
}

pub open spec fn extra_offset(field: Field) -> nat {
    match field { Field::Atime => 140, Field::Ctime => 132, Field::Mtime => 136, Field::Crtime => 148 }
}

pub open spec fn shape(raw: Seq<u8>) -> bool {
    raw.len() == 128 || raw.len() >= 132 && bytes::le16(raw, 128) <= raw.len() - 128
}

pub open spec fn effective_size(raw: Seq<u8>) -> nat {
    if raw.len() == 128 { 128 } else { 128 + bytes::le16(raw, 128) }
}

pub open spec fn admitted(raw: Seq<u8>, field: Field) -> bool {
    shape(raw) && base_offset(field) + 4 <= effective_size(raw)
}

pub open spec fn has_extra(raw: Seq<u8>, field: Field) -> bool { extra_offset(field) + 4 <= effective_size(raw) }

pub open spec fn seconds(raw: Seq<u8>, field: Field) -> int {
    inode_time::seconds_value(bytes::le32(raw, base_offset(field) as int) as u32,
        if has_extra(raw, field) { bytes::le32(raw, extra_offset(field) as int) as u32 } else { 0 }, has_extra(raw, field))
}

pub open spec fn nanoseconds(raw: Seq<u8>, field: Field) -> nat {
    if has_extra(raw, field) { bytes::le32(raw, extra_offset(field) as int) / 4 } else { 0 }
}

pub open spec fn can_set(raw: Seq<u8>, field: Field, seconds: int, nanos: nat) -> bool {
    admitted(raw, field) && (!has_extra(raw, field) || inode_time::representable(seconds, nanos))
}

pub open spec fn update(raw: Seq<u8>, field: Field, seconds: int, nanos: nat) -> Seq<u8> {
    let extended = has_extra(raw, field);
    let base = if extended { inode_time::base_word(seconds) } else { inode_time::legacy_word(seconds) };
    let first = bytes::splice(raw, base_offset(field) as int, bytes::encoded_le(base as u32));
    if extended { bytes::splice(first, extra_offset(field) as int, bytes::encoded_le(inode_time::extra_word(seconds, nanos) as u32)) }
    else { first }
}

fn offsets(field: Field) -> (r: (usize, usize))
    ensures r.0 == base_offset(field), r.1 == extra_offset(field), r.0 + 4 <= r.1,
        r.0 != 128 && r.0 != 129 && r.1 >= 132,
{
    match field { Field::Atime => (8, 140), Field::Ctime => (12, 132), Field::Mtime => (16, 136), Field::Crtime => (144, 148) }
}

fn available_size(raw: &[u8]) -> (r: Option<usize>)
    ensures match r { Some(size) => shape(raw@) && size == effective_size(raw@) && size <= raw.len(), None => !shape(raw@) },
{
    if raw.len() == 128 { return Some(128); }
    if raw.len() < 132 { return None; }
    let extra = bytes::read_le16(raw, 128).unwrap() as usize;
    if extra > raw.len() - 128 { return None; }
    Some(128 + extra)
}

pub fn get_time(raw: &[u8], field: Field) -> (r: Option<Timestamp>)
    ensures match r {
        Some(time) => admitted(raw@, field) && time.seconds as int == seconds(raw@, field)
            && time.nanoseconds as nat == nanoseconds(raw@, field),
        None => !admitted(raw@, field),
    },
{
    let size = match available_size(raw) { Some(size) => size, None => { return None; } };
    let (base, extra) = offsets(field);
    if base + 4 > size { return None; }
    let low = bytes::read_le32(raw, base).unwrap();
    let extended = extra + 4 <= size;
    let high = if extended { bytes::read_le32(raw, extra).unwrap() } else { 0 };
    Some(inode_time::decode_words(low, high, extended))
}

pub fn set_time(raw: &mut [u8], field: Field, seconds: i64, nanoseconds: u32) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r == can_set(old(raw)@, field, seconds as int, nanoseconds as nat),
        final(raw)@ == if r { update(old(raw)@, field, seconds as int, nanoseconds as nat) } else { old(raw)@ },
        r ==> admitted(final(raw)@, field)
            && self::seconds(final(raw)@, field) == (if has_extra(old(raw)@, field) { seconds as int } else { inode_time::legacy_value(seconds as int) })
            && self::nanoseconds(final(raw)@, field) == (if has_extra(old(raw)@, field) { nanoseconds as nat } else { 0nat }),
{
    let ghost before = raw@;
    let size = match available_size(raw) { Some(size) => size, None => { return false; } };
    let (base, extra) = offsets(field);
    if base + 4 > size { return false; }
    let extended = extra + 4 <= size;
    let (low, high) = if extended {
        match inode_time::encode_extended(seconds, nanoseconds) {
            Some(words) => (words.base, Some(words.extra)), None => { return false; }
        }
    } else { (inode_time::encode_legacy(seconds), None) };
    assert(base + 4 <= raw.len());
    let success = bytes::write_le32(raw, base, low);
    assert(success);
    match high {
        Some(high) => { let success = bytes::write_le32(raw, extra, high); assert(success); },
        None => {},
    }
    proof { updated_field_decodes_to_the_requested_time(before, field, seconds as int, nanoseconds as nat); }
    true
}

pub proof fn updated_field_decodes_to_the_requested_time(raw: Seq<u8>, field: Field, sec: int, nanos: nat)
    requires can_set(raw, field, sec, nanos),
    ensures admitted(update(raw, field, sec, nanos), field),
        has_extra(update(raw, field, sec, nanos), field) == has_extra(raw, field),
        seconds(update(raw, field, sec, nanos), field) == (if has_extra(raw, field) { sec } else { inode_time::legacy_value(sec) }),
        nanoseconds(update(raw, field, sec, nanos), field) == (if has_extra(raw, field) { nanos } else { 0nat }),
{
    let after = update(raw, field, sec, nanos);
    match field { Field::Atime => {}, Field::Ctime => {}, Field::Mtime => {}, Field::Crtime => {} }
    time_updates_preserve_every_unrelated_inode_byte(raw, field, sec, nanos, 0);
    if raw.len() >= 132 {
        time_updates_preserve_every_unrelated_inode_byte(raw, field, sec, nanos, 128);
        time_updates_preserve_every_unrelated_inode_byte(raw, field, sec, nanos, 129);
        assert(bytes::le16(after, 128) == bytes::le16(raw, 128));
    }
    assert(shape(after) && effective_size(after) == effective_size(raw));
    let extended = has_extra(raw, field);
    let low = (if extended { inode_time::base_word(sec) } else { inode_time::legacy_word(sec) }) as u32;
    bytes::little_endian_encoding_recovers_every_word(low);
    let base = base_offset(field) as int;
    assert(after.subrange(base, base + 4) =~= bytes::encoded_le(low));
    assert(bytes::le32(after, base) == low);
    if extended {
        inode_time::extended_fields_reconstruct_the_original_seconds_and_nanoseconds(sec, nanos);
        let high = inode_time::extra_word(sec, nanos) as u32;
        bytes::little_endian_encoding_recovers_every_word(high);
        let extra = extra_offset(field) as int;
        assert(after.subrange(extra, extra + 4) =~= bytes::encoded_le(high));
        assert(bytes::le32(after, extra) == high);
    }
}

pub proof fn time_updates_preserve_every_unrelated_inode_byte(raw: Seq<u8>, field: Field, sec: int, nanos: nat, index: int)
    requires can_set(raw, field, sec, nanos), 0 <= index < raw.len(),
        !(base_offset(field) <= index < base_offset(field) + 4),
        !has_extra(raw, field) || !(extra_offset(field) <= index < extra_offset(field) + 4),
    ensures update(raw, field, sec, nanos).len() == raw.len(), update(raw, field, sec, nanos)[index] == raw[index],
{
    assert(base_offset(field) + 4 <= effective_size(raw) <= raw.len());
    if has_extra(raw, field) { assert(extra_offset(field) + 4 <= raw.len()); }
}

pub proof fn field_presence_uses_declared_extra_size_not_buffer_capacity(raw: Seq<u8>, field: Field)
    requires shape(raw), raw.len() > 128, bytes::le16(raw, 128) == 0,
    ensures !has_extra(raw, field), admitted(raw, field) == (field != Field::Crtime),
{
    match field { Field::Atime => {}, Field::Ctime => {}, Field::Mtime => {}, Field::Crtime => {} }
}

}
