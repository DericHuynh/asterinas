// SPDX-License-Identifier: MPL-2.0

//! Modern ext4 EA_INODE metadata and reference-word codec.
//!
//! The local `Unlinked` state only describes zero references and zero links.
//! Neither a parsed image nor a reference edit proves orphan-list membership,
//! allocation, value-block ownership, quota charging, durability or authority.
//! In particular, a zero transition requires a separately admitted orphan
//! protocol before it may be used by a filesystem transaction.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, inode, inode_time_fields::{self, Field}};

verus! {

pub const FLAG: u32 = 0x200000;
pub const EXTENT_FLAG: u32 = 0x80000;
pub const MAX_VALUE: u32 = 16777216;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Status { Live, Unlinked }

#[derive(Clone, Copy)]
pub struct Info {
    pub number: u32, pub inodes: u32, pub seed: u32,
    pub mode: u16, pub uid: u32, pub gid: u32, pub size: u32,
    pub generation: u32, pub hash: u32, pub refs: u64, pub status: Status,
}

pub open spec fn reference(raw: Seq<u8>) -> nat {
    bytes::le32(raw, 12) * 4294967296 + bytes::le32(raw, 36)
}
pub open spec fn status_for(refs: nat) -> Status { if refs == 0 { Status::Unlinked } else { Status::Live } }
pub open spec fn no_nested_attributes(raw: Seq<u8>) -> bool {
    bytes::le32(raw, 104) == 0 && bytes::le16(raw, 118) == 0
        && forall|i: int| 160 <= i < 256 ==> #[trigger] raw[i] == 0
}
#[verifier::opaque]
pub open spec fn accepted(raw: Seq<u8>, number: u32, inodes: u32, seed: u32, status: Status) -> bool {
    &&& raw.len() == 256 && 0 < number <= inodes
    &&& bytes::le16(raw, 0) as u16 & 0xf000 == 0x8000
    &&& bytes::le32(raw, 20) == 0 && bytes::le32(raw, 32) == FLAG | EXTENT_FLAG
    &&& bytes::le16(raw, 128) == 32 && bytes::le32(raw, 108) == 0
    &&& 0 < bytes::le32(raw, 4) <= MAX_VALUE
    // This modern profile uses the raw low i_version word exclusively, and
    // does not admit huge-sector accounting. Extent ownership is checked by
    // the source-bound value reader rather than this metadata codec.
    &&& bytes::le32(raw, 152) == 0 && bytes::le16(raw, 116) == 0
    &&& no_nested_attributes(raw)
    &&& match status {
        Status::Live => reference(raw) > 0 && bytes::le16(raw, 26) == 1,
        Status::Unlinked => reference(raw) == 0 && bytes::le16(raw, 26) == 0,
    }
    &&& bytes::le16(raw, 124) + 65536 * bytes::le16(raw, 130) == inode::checksum(raw, number, seed) as nat
}
pub open spec fn represents(info: Info, raw: Seq<u8>) -> bool {
    accepted(raw, info.number, info.inodes, info.seed, info.status)
        && info.mode == bytes::le16(raw, 0)
        && info.uid == bytes::le16(raw, 2) + 65536 * bytes::le16(raw, 120)
        && info.gid == bytes::le16(raw, 24) + 65536 * bytes::le16(raw, 122)
        && info.size == bytes::le32(raw, 4) && info.generation == bytes::le32(raw, 100)
        && info.hash == bytes::le32(raw, 8) && info.refs == reference(raw)
}

pub fn parse(raw: &[u8], number: u32, inodes: u32, seed: u32, status: Status) -> (r: Option<Info>)
    ensures match r {
        Some(info) => represents(info, raw@) && info.number == number && info.inodes == inodes && info.seed == seed && info.status == status,
        None => !accepted(raw@, number, inodes, seed, status),
    },
{
    hide(inode::checksum);
    reveal(accepted);
    if raw.len() != 256 || number == 0 || number > inodes { return None; }
    let mode = bytes::read_le16(raw, 0).unwrap();
    if mode & 0xf000 != 0x8000 || bytes::read_le32(raw, 20).unwrap() != 0
        || bytes::read_le32(raw, 32).unwrap() != FLAG | EXTENT_FLAG
        || bytes::read_le16(raw, 128).unwrap() != 32
        || bytes::read_le32(raw, 108).unwrap() != 0
        || bytes::read_le32(raw, 4).unwrap() == 0 || bytes::read_le32(raw, 4).unwrap() > MAX_VALUE
        || bytes::read_le32(raw, 152).unwrap() != 0 || bytes::read_le16(raw, 116).unwrap() != 0
        || bytes::read_le32(raw, 104).unwrap() != 0 || bytes::read_le16(raw, 118).unwrap() != 0
    { return None; }
    let mut i = 160usize;
    while i < 256
        invariant raw.len() == 256, 160 <= i <= 256,
            forall|j: int| 160 <= j < i ==> #[trigger] raw@[j] == 0,
        decreases 256 - i,
    {
        if raw[i] != 0 {
            proof {
                assert(raw@[i as int] != 0);
                assert(!no_nested_attributes(raw@)) by {
                    if no_nested_attributes(raw@) { assert(raw@[i as int] == 0); }
                }
                assert(!accepted(raw@, number, inodes, seed, status)) by { reveal(accepted); }
            }
            return None;
        }
        i += 1;
    }
    let refs = bytes::read_le32(raw, 12).unwrap() as u64 * 4294967296 + bytes::read_le32(raw, 36).unwrap() as u64;
    let links = bytes::read_le16(raw, 26).unwrap();
    if matches!(status, Status::Live) { if refs == 0 || links != 1 { return None; } }
    else { if refs != 0 || links != 0 { return None; } }
    let checksum = bytes::read_le16(raw, 124).unwrap() as u32 + 65536 * bytes::read_le16(raw, 130).unwrap() as u32;
    if checksum != inode::calculated_checksum(raw, number, seed).unwrap() { return None; }
    let info = Info { number, inodes, seed, mode,
        uid: bytes::read_le16(raw, 2).unwrap() as u32 + 65536 * bytes::read_le16(raw, 120).unwrap() as u32,
        gid: bytes::read_le16(raw, 24).unwrap() as u32 + 65536 * bytes::read_le16(raw, 122).unwrap() as u32,
        size: bytes::read_le32(raw, 4).unwrap(), generation: bytes::read_le32(raw, 100).unwrap(),
        hash: bytes::read_le32(raw, 8).unwrap(), refs, status };
    assert(represents(info, raw@));
    Some(info)
}

pub struct Change {
    pub before: Seq<u8>, pub after: Seq<u8>, pub number: u32, pub inodes: u32,
    pub seed: u32, pub before_status: Status, pub next: u64,
}
pub open spec fn mutable(i: int) -> bool {
    12 <= i < 16 || 26 <= i < 28 || 36 <= i < 40
        || 124 <= i < 126 || 130 <= i < 136
}
pub open spec fn framed(before: Seq<u8>, after: Seq<u8>) -> bool {
    before.len() == 256 && after.len() == 256
        && forall|i: int| 0 <= i < 256 && !mutable(i) ==> #[trigger] after[i] == before[i]
}
pub open spec fn canonical_reference_words(raw: Seq<u8>, refs: u64) -> bool {
    bytes::le32(raw, 12) == refs as nat / 4294967296
        && bytes::le32(raw, 36) == refs as nat % 4294967296
        && bytes::le32(raw, 132) == if refs as nat / 4294967296 >= 2147483648 { 1nat } else { 0nat }
}
#[verifier::opaque]
pub open spec fn valid_change(v: Change) -> bool {
    accepted(v.before, v.number, v.inodes, v.seed, v.before_status)
        && accepted(v.after, v.number, v.inodes, v.seed, status_for(v.next as nat))
        && reference(v.after) == v.next && canonical_reference_words(v.after, v.next)
        && framed(v.before, v.after)
}
fn checked_change(before: &[u8], after: &[u8], number: u32, inodes: u32, seed: u32, before_status: Status, next: u64) -> (r: bool)
    ensures r ==> valid_change(Change { before: before@, after: after@, number, inodes, seed, before_status, next }),
{
    hide(inode::checksum);
    reveal(accepted);
    let _ = match parse(before, number, inodes, seed, before_status) { Some(info) => info, None => { return false; } };
    let status = if next == 0 { Status::Unlinked } else { Status::Live };
    let info = match parse(after, number, inodes, seed, status) { Some(info) => info, None => { return false; } };
    if info.refs != next || bytes::read_le32(after, 12).unwrap() as u64 != next / 4294967296
        || bytes::read_le32(after, 36).unwrap() as u64 != next % 4294967296
        || bytes::read_le32(after, 132).unwrap() != if next / 4294967296 >= 2147483648 { 1u32 } else { 0u32 }
    { return false; }
    let mut i = 0usize;
    while i < 256
        invariant before.len() == 256, after.len() == 256, i <= 256,
            forall|j: int| 0 <= j < i && !mutable(j) ==> #[trigger] after@[j] == before@[j],
        decreases 256 - i,
    {
        if !(12 <= i && i < 16 || 26 <= i && i < 28 || 36 <= i && i < 40 || 124 <= i && i < 126 || 130 <= i && i < 136)
            && after[i] != before[i] { return false; }
        i += 1;
    }
    assert(valid_change(Change { before: before@, after: after@, number, inodes, seed, before_status, next })) by { reveal(valid_change); }
    true
}

pub fn set_refcount(raw: &[u8], number: u32, inodes: u32, seed: u32, before_status: Status, next: u64) -> (r: Option<Vec<u8>>)
    ensures match r { Some(after) => valid_change(Change { before: raw@, after: after@, number, inodes, seed, before_status, next }), None => true },
{
    hide(inode::checksum);
    reveal(accepted);
    if parse(raw, number, inodes, seed, before_status).is_none() { return None; }
    let mut after = Vec::new(); let mut i = 0usize;
    while i < 256
        invariant raw.len() == 256, i <= 256, after@ == raw@.take(i as int),
        decreases 256 - i,
    { after.push(raw[i]); assert(after@ =~= raw@.take(i as int + 1)); i += 1; }
    let high = (next / 4294967296) as u32; let low = (next % 4294967296) as u32;
    bytes::write_le32(after.as_mut_slice(), 12, high);
    bytes::write_le32(after.as_mut_slice(), 36, low);
    let extra = if high >= 2147483648 { 1u32 } else { 0u32 };
    bytes::write_le32(after.as_mut_slice(), 132, extra);
    let links = bytes::encode_le16(if next == 0 { 0u16 } else { 1u16 });
    bytes::write_bytes(after.as_mut_slice(), 26, &links);
    let checksum = inode::calculated_checksum(&after, number, seed).unwrap(); let checksum = bytes::encode_le32(checksum);
    bytes::write_bytes(after.as_mut_slice(), 124, &checksum[..2]); bytes::write_bytes(after.as_mut_slice(), 130, &checksum[2..]);
    if !checked_change(raw, &after, number, inodes, seed, before_status, next) { return None; }
    Some(after)
}

pub proof fn ordinary_inode_metadata_does_not_admit_ea_value_inodes(raw: Seq<u8>, number: u32, inodes: u32, seed: u32, status: Status, huge: bool)
    requires accepted(raw, number, inodes, seed, status),
    ensures !inode::metadata_accepted_with_features(raw, number, inodes, seed, huge),
{
    reveal(accepted);
    let flags = bytes::le32(raw, 32) as u32;
    assert(flags & !0x1000u32 != 0x80000u32 && flags & !0x1000u32 != 0xc0000u32) by (bit_vector)
        requires flags == FLAG | EXTENT_FLAG;
}
pub proof fn live_references_and_unlinked_zero_are_distinct(raw: Seq<u8>, number: u32, inodes: u32, seed: u32, status: Status)
    requires accepted(raw, number, inodes, seed, status),
    ensures status == status_for(reference(raw)),
        status == Status::Live ==> reference(raw) > 0 && bytes::le16(raw, 26) == 1,
        status == Status::Unlinked ==> reference(raw) == 0 && bytes::le16(raw, 26) == 0,
{ reveal(accepted); }
pub proof fn reference_edits_preserve_every_unrelated_inode_byte(v: Change, i: int)
    requires valid_change(v), 0 <= i < 256, !mutable(i),
    ensures v.after[i] == v.before[i],
{ reveal(valid_change); }
pub proof fn reference_edits_preserve_value_hash_and_identity(v: Change)
    requires valid_change(v),
    ensures bytes::le32(v.after, 8) == bytes::le32(v.before, 8),
        bytes::le16(v.after, 0) == bytes::le16(v.before, 0),
        bytes::le32(v.after, 4) == bytes::le32(v.before, 4),
        bytes::le32(v.after, 100) == bytes::le32(v.before, 100),
        v.after.subrange(40, 100) == v.before.subrange(40, 100),
{
    reveal(valid_change);
    assert forall|i: int| 40 <= i < 100 implies v.after[i] == v.before[i] by { assert(!mutable(i)); }
    assert(v.after.subrange(40, 100) =~= v.before.subrange(40, 100));
}
pub proof fn reference_edits_use_raw_low_version_and_canonical_unsigned_high_word(v: Change)
    requires valid_change(v),
    ensures bytes::le32(v.after, 36) == v.next as nat % 4294967296,
        bytes::le32(v.after, 12) == v.next as nat / 4294967296,
        bytes::le32(v.after, 132) == if v.next as nat / 4294967296 >= 2147483648 { 1nat } else { 0nat },
        bytes::le32(v.after, 152) == 0,
{ reveal(valid_change); reveal(accepted); }


pub proof fn canonical_reference_time_decodes_to_the_unsigned_high_reference_word(v: Change)
    requires valid_change(v),
    ensures inode_time_fields::seconds(v.after, Field::Ctime) == v.next as nat / 4294967296,
        inode_time_fields::nanoseconds(v.after, Field::Ctime) == 0,
{
    reveal(valid_change); reveal(accepted);
    let high = v.next as nat / 4294967296;
    assert(inode_time_fields::has_extra(v.after, Field::Ctime));
    if high >= 2147483648 {
        assert(bytes::le32(v.after, 132) == 1);
    } else {
        assert(bytes::le32(v.after, 132) == 0);
    }
}
pub proof fn edited_link_count_tracks_the_resulting_local_reference_state(v: Change)
    requires valid_change(v),
    ensures if v.next == 0 { bytes::le16(v.after, 26) == 0 } else { bytes::le16(v.after, 26) == 1 },
        bytes::le32(v.after, 20) == 0,
{ reveal(valid_change); reveal(accepted); }


pub proof fn ea_reference_and_hash_words_ignore_extended_time_epochs(raw: Seq<u8>, number: u32, inodes: u32, seed: u32, status: Status, field: Field)
    requires accepted(raw, number, inodes, seed, status), field == Field::Atime || field == Field::Ctime,
    ensures (inode_time_fields::seconds(raw, field) + 4294967296) % 4294967296
        == bytes::le32(raw, inode_time_fields::base_offset(field) as int),
{
    reveal(accepted);
    match field { Field::Atime => {}, Field::Ctime => {}, Field::Mtime => {}, Field::Crtime => {} }
    assert(inode_time_fields::has_extra(raw, field));
    let base = bytes::le32(raw, inode_time_fields::base_offset(field) as int);
    let epoch = bytes::le32(raw, inode_time_fields::extra_offset(field) as int) as int % 4;
    let seconds = inode_time_fields::seconds(raw, field);
    if base >= 2147483648 {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(seconds + 4294967296, 4294967296, epoch, base as int);
    } else {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(seconds + 4294967296, 4294967296, epoch + 1, base as int);
    }
}

}
