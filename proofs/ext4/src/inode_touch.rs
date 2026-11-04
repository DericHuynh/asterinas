// SPDX-License-Identifier: MPL-2.0

//! Exact ctime/mtime update and checksum reseal for the current 256-byte
//! metadata-checksummed inode profile. Clock and VFS authority are separate.

use vstd::prelude::*;
use crate::{bytes, inode, inode_time, inode_time_fields::{self as fields, Field}};

verus! {

pub open spec fn time_payload(raw: Seq<u8>, seconds: int, nanos: nat) -> Seq<u8> {
    fields::update(fields::update(raw, Field::Mtime, seconds, nanos), Field::Ctime, seconds, nanos)
}

pub open spec fn changed_byte(index: int) -> bool {
    12 <= index < 20 || 124 <= index < 126 || 130 <= index < 140
}

pub open spec fn sealed_bytes(raw: Seq<u8>, number: u32, seed: u32, seconds: int, nanos: nat) -> Seq<u8> {
    let timed = time_payload(raw, seconds, nanos);
    let word = bytes::encoded_le(inode::checksum(timed, number, seed));
    bytes::splice(bytes::splice(timed, 124, word.take(2)), 130, word.skip(2))
}

pub proof fn touching_times_preserves_inode_metadata_identity_and_validity(raw: Seq<u8>, number: u32, inodes: u32,
    seed: u32, huge: bool, sec: int, nanos: nat)
    requires inode::metadata_accepted_with_features(raw, number, inodes, seed, huge), inode_time::representable(sec, nanos),
    ensures inode::metadata_accepted_with_features(sealed_bytes(raw, number, seed, sec, nanos), number, inodes, seed, huge),
        sealed_bytes(raw, number, seed, sec, nanos).len() == 256,
        fields::seconds(sealed_bytes(raw, number, seed, sec, nanos), Field::Mtime) == sec,
        fields::seconds(sealed_bytes(raw, number, seed, sec, nanos), Field::Ctime) == sec,
        fields::nanoseconds(sealed_bytes(raw, number, seed, sec, nanos), Field::Mtime) == nanos,
        fields::nanoseconds(sealed_bytes(raw, number, seed, sec, nanos), Field::Ctime) == nanos,
        forall|i: int| 0 <= i < raw.len() && !changed_byte(i) ==> (#[trigger] sealed_bytes(raw, number, seed, sec, nanos)[i]) == raw[i],
{
    hide(crate::crc::fold);
    let first = fields::update(raw, Field::Mtime, sec, nanos);
    fields::updated_field_decodes_to_the_requested_time(raw, Field::Mtime, sec, nanos);
    let timed = time_payload(raw, sec, nanos);
    fields::updated_field_decodes_to_the_requested_time(first, Field::Ctime, sec, nanos);
    assert forall|i: int| 0 <= i < raw.len() && !(12 <= i < 20 || 132 <= i < 140) implies (#[trigger] timed[i]) == raw[i] by {
        fields::time_updates_preserve_every_unrelated_inode_byte(raw, Field::Mtime, sec, nanos, i);
        fields::time_updates_preserve_every_unrelated_inode_byte(first, Field::Ctime, sec, nanos, i);
    }
    let checksum = inode::checksum(timed, number, seed);
    bytes::little_endian_encoding_recovers_every_word(checksum);
    let after = sealed_bytes(raw, number, seed, sec, nanos);
    assert(inode::checksum_input(after) =~= inode::checksum_input(timed));
    assert(bytes::le32(after, 100) == bytes::le32(timed, 100));
    assert(inode::checksum(after, number, seed) == checksum);
    assert(bytes::le16(after, 124) + 65536 * bytes::le16(after, 130) == checksum as nat);
    assert forall|i: int| 0 <= i < raw.len() && !changed_byte(i) implies (#[trigger] after[i]) == raw[i] by {
        assert(timed[i] == raw[i]);
    }
}

pub fn touch(raw: &mut [u8], number: u32, inodes: u32, seed: u32, huge: bool, seconds: i64, nanoseconds: u32) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r == (inode::metadata_accepted_with_features(old(raw)@, number, inodes, seed, huge)
            && inode_time::representable(seconds as int, nanoseconds as nat)),
        final(raw)@ == if r { sealed_bytes(old(raw)@, number, seed, seconds as int, nanoseconds as nat) } else { old(raw)@ },
        r ==> inode::metadata_accepted_with_features(final(raw)@, number, inodes, seed, huge),
{
    hide(crate::crc::fold);
    let ghost before = raw@;
    match inode::parse_metadata_with_features(raw, number, inodes, seed, huge) { Some(_) => {}, None => { return false; } }
    if seconds < inode_time::MIN_SECONDS || seconds > inode_time::MAX_SECONDS || nanoseconds >= 1000000000 { return false; }
    let mtime = fields::set_time(raw, Field::Mtime, seconds, nanoseconds);
    assert(mtime);
    let ctime = fields::set_time(raw, Field::Ctime, seconds, nanoseconds);
    assert(ctime);
    assert(raw@ == time_payload(before, seconds as int, nanoseconds as nat));
    let checksum = inode::calculated_checksum(raw, number, seed).unwrap();
    let word = bytes::encode_le32(checksum);
    let low = bytes::write_bytes(raw, 124, &word[..2]);
    assert(low);
    let high = bytes::write_bytes(raw, 130, &word[2..]);
    assert(high);
    proof { touching_times_preserves_inode_metadata_identity_and_validity(before, number, inodes, seed, huge, seconds as int, nanoseconds as nat); }
    true
}

}
