// SPDX-License-Identifier: MPL-2.0

//! Inode metadata for xattr attach/detach/rebuild. Normalized sector counts,
//! ctime, ordinary i_version and both inode checksum halves are checked.
//! A checked byte result conveys no source, credential or block authority.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, inode, inode_blocks, inode_time, inode_time_fields::{self as time, Field}, xattr, xattr_replace};

verus! {

pub struct Change { pub before: Seq<u8>, pub packed: Seq<u8>, pub after: Seq<u8>, pub physical: u32,
    pub number: u32, pub inodes: u32, pub seed: u32, pub huge: bool, pub seconds: int, pub nanos: nat }
pub open spec fn mutable(i: int) -> bool {
    12 <= i < 16 || 28 <= i < 40 || 104 <= i < 108 || 116 <= i < 120
        || 124 <= i < 126 || 130 <= i < 136 || 152 <= i < 156 || 160 <= i < 256
}
pub open spec fn frame(before: Seq<u8>, after: Seq<u8>) -> bool {
    before.len() == 256 && after.len() == 256 && (forall|i: int| 0 <= i < 256 && !mutable(i) ==> #[trigger] after[i] == before[i])
        && bytes::le32(after, 32) as u32 & !inode_blocks::HUGE_FLAG == bytes::le32(before, 32) as u32 & !inode_blocks::HUGE_FLAG
}
pub open spec fn owned_sectors(raw: Seq<u8>, huge: bool) -> int {
    inode_blocks::sectors(raw, 4096, huge) as int - if xattr::inode_address(raw) > 0 { 8int } else { 0int }
}
#[verifier::opaque]
pub open spec fn valid(c: Change) -> bool {
    &&& inode::metadata_accepted_with_features(c.before, c.number, c.inodes, c.seed, c.huge)
    &&& inode::metadata_accepted_with_features(c.after, c.number, c.inodes, c.seed, c.huge)
    &&& c.before.len() == 256 && c.packed.len() == 256 && c.after.len() == 256
    &&& bytes::le16(c.before, 128) == 32 && bytes::le16(c.after, 128) == 32
    &&& frame(c.before, c.after) && c.after.subrange(160, 256) == c.packed.subrange(160, 256)
    &&& xattr::inode_address(c.after) == c.physical && owned_sectors(c.before, c.huge) >= 0
    &&& owned_sectors(c.after, c.huge) == owned_sectors(c.before, c.huge)
    &&& inode_time::representable(c.seconds, c.nanos) && time::seconds(c.after, Field::Ctime) == c.seconds && time::nanoseconds(c.after, Field::Ctime) == c.nanos
    &&& xattr_replace::version(c.before) < xattr_replace::MAX_VERSION
    &&& xattr_replace::version(c.after) == xattr_replace::version(c.before) + 1
}
fn framed(before: &[u8], after: &[u8]) -> (r: bool) ensures r ==> frame(before@, after@) {
    if before.len() != 256 || after.len() != 256 { return false; }
    if bytes::read_le32(before, 32).unwrap() & !inode_blocks::HUGE_FLAG != bytes::read_le32(after, 32).unwrap() & !inode_blocks::HUGE_FLAG { return false; }
    let mut i = 0usize;
    while i < 256
        invariant before.len() == 256, after.len() == 256, i <= 256,
            bytes::le32(after@, 32) as u32 & !inode_blocks::HUGE_FLAG == bytes::le32(before@, 32) as u32 & !inode_blocks::HUGE_FLAG,
            forall|j: int| 0 <= j < i && !mutable(j) ==> #[trigger] after@[j] == before@[j],
        decreases 256 - i,
    {
        let changed = 12 <= i && i < 16 || 28 <= i && i < 40 || 104 <= i && i < 108 || 116 <= i && i < 120
            || 124 <= i && i < 126 || 130 <= i && i < 136 || 152 <= i && i < 156 || 160 <= i && i < 256;
        if !changed && before[i] != after[i] { return false; } i += 1;
    }
    true
}
fn version(raw: &[u8]) -> (r: u64) requires raw.len() == 256, ensures r as nat == xattr_replace::version(raw@) {
    bytes::read_le32(raw, 36).unwrap() as u64 + 4294967296 * bytes::read_le32(raw, 152).unwrap() as u64
}
pub fn encode(before: &[u8], packed: &[u8], physical: u32, number: u32, inodes: u32, seed: u32, huge: bool, seconds: i64, nanos: u32) -> (r: Option<Vec<u8>>)
    ensures match r { Some(after) => valid(Change { before: before@, packed: packed@, after: after@, physical, number, inodes, seed, huge, seconds: seconds as int, nanos: nanos as nat }), None => true },
{
    hide(crate::crc::fold);
    if before.len() != 256 || packed.len() != 256 || bytes::read_le16(before, 128).unwrap() != 32 { return None; }
    if inode::parse_metadata_with_features(before, number, inodes, seed, huge).is_none() { return None; }
    let old = version(before); if old >= xattr_replace::MAX_VERSION { return None; } let next = old + 1;
    if seconds < inode_time::MIN_SECONDS || seconds > inode_time::MAX_SECONDS || nanos >= 1000000000 { return None; }
    let old_pointer = xattr::inode_pointer(before).unwrap(); let old_sectors = inode_blocks::decode(before, 4096, huge).unwrap();
    let old_ea = if old_pointer > 0 { 8u64 } else { 0u64 }; let new_ea = if physical > 0 { 8u64 } else { 0u64 };
    if old_sectors < old_ea { return None; } let owned = old_sectors - old_ea;
    if owned > u64::MAX - new_ea { return None; } let sectors = owned + new_ea;
    let encoded = match inode_blocks::encode(sectors, 4096, huge) { Some(encoded) => encoded, None => { return None; } };
    let mut raw = Vec::new(); let mut i = 0usize;
    while i < 256 invariant i <= 256, packed.len() == 256, raw@ == packed@.take(i as int), decreases 256 - i,
    { raw.push(packed[i]); assert(raw@ =~= packed@.take(i as int + 1)); i += 1; }
    bytes::write_le32(raw.as_mut_slice(), 104, physical); bytes::write_bytes(raw.as_mut_slice(), 118, &[0u8, 0u8]);
    bytes::write_bytes(raw.as_mut_slice(), 28, &encoded.low); bytes::write_bytes(raw.as_mut_slice(), 116, &encoded.high);
    let flags = bytes::read_le32(before, 32).unwrap() & !inode_blocks::HUGE_FLAG;
    bytes::write_le32(raw.as_mut_slice(), 32, if encoded.huge { flags | inode_blocks::HUGE_FLAG } else { flags });
    if !time::set_time(raw.as_mut_slice(), Field::Ctime, seconds, nanos) { return None; }
    bytes::write_le32(raw.as_mut_slice(), 36, (next % 4294967296) as u32); bytes::write_le32(raw.as_mut_slice(), 152, (next / 4294967296) as u32);
    let checksum = inode::calculated_checksum(&raw, number, seed).unwrap(); let word = bytes::encode_le32(checksum);
    bytes::write_bytes(raw.as_mut_slice(), 124, &word[..2]); bytes::write_bytes(raw.as_mut_slice(), 130, &word[2..]);
    if inode::parse_metadata_with_features(&raw, number, inodes, seed, huge).is_none() || !framed(before, &raw) { return None; }
    if bytes::read_le16(&raw, 128).unwrap() != 32 || !bytes::equal(&raw[160..], &packed[160..]) { return None; }
    if xattr::inode_pointer(&raw).unwrap() != physical as u64 || inode_blocks::decode(&raw, 4096, huge).unwrap() != sectors || version(&raw) != next { return None; }
    let ctime = time::get_time(&raw, Field::Ctime).unwrap(); if ctime.seconds != seconds || ctime.nanoseconds != nanos { return None; }
    assert(valid(Change { before: before@, packed: packed@, after: raw@, physical, number, inodes, seed, huge, seconds: seconds as int, nanos: nanos as nat })) by { reveal(valid); }
    Some(raw)
}

pub proof fn xattr_updates_preserve_every_non_xattr_sector(c: Change)
    requires valid(c), ensures owned_sectors(c.after, c.huge) == owned_sectors(c.before, c.huge),
{ reveal(valid); }
pub proof fn xattr_updates_preserve_inode_identity_mode_owners_and_extent_root(c: Change, i: int)
    requires valid(c), 0 <= i < 256, !mutable(i), ensures c.after[i] == c.before[i],
{ reveal(valid); }

}
