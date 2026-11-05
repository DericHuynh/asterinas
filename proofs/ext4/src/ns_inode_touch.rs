// SPDX-License-Identifier: MPL-2.0

//! Ordinary inode ctime/optional mtime and nonwrapping version resealing.
//! This checked byte codec preserves namespace identity, storage and EA billing;
//! it grants no source freshness, credential, lock, publication or I/O authority.

use vstd::prelude::*;
use crate::{bytes, inode, inode_time, inode_time_fields::{self as time, Field}, xattr_replace};

verus! {

pub struct Change {
    pub before: Seq<u8>, pub after: Seq<u8>, pub number: u32, pub inodes: u32,
    pub seed: u32, pub huge: bool, pub touch_mtime: bool, pub seconds: int, pub nanos: nat,
}

pub open spec fn mutable(touch_mtime: bool, i: int) -> bool {
    12 <= i < 16 || 36 <= i < 40 || 124 <= i < 126
        || 130 <= i < 136 || 152 <= i < 156
        || touch_mtime && (16 <= i < 20 || 136 <= i < 140)
}

pub open spec fn frame(before: Seq<u8>, after: Seq<u8>, touch_mtime: bool) -> bool {
    before.len() == 256 && after.len() == 256
        && (forall|i: int| 0 <= i < 256 && !mutable(touch_mtime, i) ==> #[trigger] after[i] == before[i])
}

#[verifier::opaque]
pub open spec fn valid(c: Change) -> bool {
    &&& c.before.len() == 256 && c.after.len() == 256
    &&& inode::metadata_accepted_with_features(c.before, c.number, c.inodes, c.seed, c.huge)
    &&& inode::metadata_accepted_with_features(c.after, c.number, c.inodes, c.seed, c.huge)
    &&& bytes::le16(c.before, 128) == 32 && bytes::le16(c.after, 128) == 32
    &&& frame(c.before, c.after, c.touch_mtime)
    &&& inode_time::representable(c.seconds, c.nanos)
    &&& time::seconds(c.after, Field::Ctime) == c.seconds
    &&& time::nanoseconds(c.after, Field::Ctime) == c.nanos
    &&& if c.touch_mtime {
        time::seconds(c.after, Field::Mtime) == c.seconds
            && time::nanoseconds(c.after, Field::Mtime) == c.nanos
    } else {
        c.after.subrange(16, 20) == c.before.subrange(16, 20)
            && c.after.subrange(136, 140) == c.before.subrange(136, 140)
    }
    &&& xattr_replace::version(c.before) < xattr_replace::MAX_VERSION
    &&& xattr_replace::version(c.after) == xattr_replace::version(c.before) + 1
}

fn framed(before: &[u8], after: &[u8], touch_mtime: bool) -> (r: bool)
    ensures r ==> frame(before@, after@, touch_mtime),
{
    if before.len() != 256 || after.len() != 256 { return false; }
    let mut i = 0usize;
    while i < 256
        invariant before.len() == 256, after.len() == 256, i <= 256,
            forall|j: int| 0 <= j < i && !mutable(touch_mtime, j) ==> #[trigger] after@[j] == before@[j],
        decreases 256 - i,
    {
        let changed = 12 <= i && i < 16 || 36 <= i && i < 40 || 124 <= i && i < 126
            || 130 <= i && i < 136 || 152 <= i && i < 156
            || touch_mtime && (16 <= i && i < 20 || 136 <= i && i < 140);
        if !changed && before[i] != after[i] { return false; }
        i += 1;
    }
    true
}

fn version(raw: &[u8]) -> (r: u64)
    requires raw.len() == 256,
    ensures r as nat == xattr_replace::version(raw@),
{
    bytes::read_le32(raw, 36).unwrap() as u64
        + 4294967296 * bytes::read_le32(raw, 152).unwrap() as u64
}

fn check(before: &[u8], after: &[u8], number: u32, inodes: u32, seed: u32,
    huge: bool, touch_mtime: bool, seconds: i64, nanos: u32) -> (r: bool)
    ensures r ==> valid(Change { before: before@, after: after@, number, inodes, seed,
        huge, touch_mtime, seconds: seconds as int, nanos: nanos as nat }),
{
    hide(inode::checksum);
    if before.len() != 256 || after.len() != 256 { return false; }
    if inode::parse_metadata_with_features(before, number, inodes, seed, huge).is_none()
        || inode::parse_metadata_with_features(after, number, inodes, seed, huge).is_none() { return false; }
    if bytes::read_le16(before, 128).unwrap() != 32 || bytes::read_le16(after, 128).unwrap() != 32 { return false; }
    if seconds < inode_time::MIN_SECONDS || seconds > inode_time::MAX_SECONDS || nanos >= 1000000000 { return false; }
    let old = version(before);
    if old >= xattr_replace::MAX_VERSION || version(after) != old + 1 { return false; }
    let ctime = match time::get_time(after, Field::Ctime) { Some(ctime) => ctime, None => { return false; } };
    if ctime.seconds != seconds || ctime.nanoseconds != nanos { return false; }
    if touch_mtime {
        let mtime = match time::get_time(after, Field::Mtime) { Some(mtime) => mtime, None => { return false; } };
        if mtime.seconds != seconds || mtime.nanoseconds != nanos { return false; }
    } else if !bytes::equal(&after[16..20], &before[16..20])
        || !bytes::equal(&after[136..140], &before[136..140]) { return false; }
    if !framed(before, after, touch_mtime) { return false; }
    assert(valid(Change { before: before@, after: after@, number, inodes, seed,
        huge, touch_mtime, seconds: seconds as int, nanos: nanos as nat })) by { reveal(valid); }
    true
}

pub fn encode(before: &[u8], number: u32, inodes: u32, seed: u32, huge: bool,
    touch_mtime: bool, seconds: i64, nanos: u32) -> (r: Option<Vec<u8>>)
    ensures match r {
        Some(after) => valid(Change { before: before@, after: after@, number, inodes,
            seed, huge, touch_mtime, seconds: seconds as int, nanos: nanos as nat }),
        None => true,
    },
{
    hide(inode::checksum);
    if before.len() != 256 || bytes::read_le16(before, 128).unwrap() != 32 { return None; }
    if inode::parse_metadata_with_features(before, number, inodes, seed, huge).is_none() { return None; }
    let old = version(before);
    if old >= xattr_replace::MAX_VERSION { return None; }
    let next = old + 1;
    if seconds < inode_time::MIN_SECONDS || seconds > inode_time::MAX_SECONDS || nanos >= 1000000000 { return None; }
    let mut after = Vec::new(); let mut i = 0usize;
    while i < 256
        invariant before.len() == 256, i <= 256, after@ == before@.take(i as int),
        decreases 256 - i,
    { after.push(before[i]); assert(after@ =~= before@.take(i as int + 1)); i += 1; }
    if !time::set_time(after.as_mut_slice(), Field::Ctime, seconds, nanos) { return None; }
    if touch_mtime && !time::set_time(after.as_mut_slice(), Field::Mtime, seconds, nanos) { return None; }
    bytes::write_le32(after.as_mut_slice(), 36, (next % 4294967296) as u32);
    bytes::write_le32(after.as_mut_slice(), 152, (next / 4294967296) as u32);
    let checksum = inode::calculated_checksum(&after, number, seed).unwrap();
    let word = bytes::encode_le32(checksum);
    bytes::write_bytes(after.as_mut_slice(), 124, &word[..2]);
    bytes::write_bytes(after.as_mut_slice(), 130, &word[2..]);
    if !check(before, &after, number, inodes, seed, huge, touch_mtime, seconds, nanos) { return None; }
    Some(after)
}

pub proof fn namespace_touches_preserve_identity_owners_links_and_extent_root(c: Change, i: int)
    requires valid(c), 0 <= i < 256,
        i < 12 || 20 <= i < 36 || 40 <= i < 124 || 126 <= i < 130
            || 140 <= i < 152 || 156 <= i < 256,
    ensures c.after[i] == c.before[i],
{ reveal(valid); }

pub proof fn namespace_touches_preserve_xattrs_and_ea_billing_bytes(c: Change)
    requires valid(c),
    ensures c.after.subrange(28, 36) == c.before.subrange(28, 36),
        c.after.subrange(104, 124) == c.before.subrange(104, 124),
        c.after.subrange(160, 256) == c.before.subrange(160, 256),
{
    reveal(valid);
    assert(c.after.subrange(28, 36) =~= c.before.subrange(28, 36));
    assert(c.after.subrange(104, 124) =~= c.before.subrange(104, 124));
    assert(c.after.subrange(160, 256) =~= c.before.subrange(160, 256));
}

pub proof fn namespace_touches_increment_one_nonwrapping_ordinary_version(c: Change)
    requires valid(c),
    ensures xattr_replace::version(c.before) < xattr_replace::version(c.after)
        <= xattr_replace::MAX_VERSION,
        xattr_replace::version(c.after) == xattr_replace::version(c.before) + 1,
{ reveal(valid); }

pub proof fn namespace_touches_publish_the_exact_requested_times(c: Change)
    requires valid(c),
    ensures time::seconds(c.after, Field::Ctime) == c.seconds,
        time::nanoseconds(c.after, Field::Ctime) == c.nanos,
        c.touch_mtime ==> time::seconds(c.after, Field::Mtime) == c.seconds
            && time::nanoseconds(c.after, Field::Mtime) == c.nanos,
        !c.touch_mtime ==> c.after.subrange(16, 20) == c.before.subrange(16, 20)
            && c.after.subrange(136, 140) == c.before.subrange(136, 140),
{ reveal(valid); }

}
