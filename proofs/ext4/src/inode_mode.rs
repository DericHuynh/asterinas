// SPDX-License-Identifier: MPL-2.0

//! Permission/SGID inode resealing for an already checked metadata image.
//! This codec grants no permission to change a filesystem inode.

use vstd::prelude::*;
use crate::{bytes, inode};

verus! {

pub struct Change { pub before: Seq<u8>, pub after: Seq<u8>, pub mode: u16, pub number: u32, pub inodes: u32, pub seed: u32, pub huge: bool }
pub open spec fn allowed(old: u16, next: u16) -> bool {
    old & !0o2777u16 == next & !0o2777u16 && (old & 0o2000 == 0 ==> next & 0o2000 == 0)
}
pub open spec fn framed(before: Seq<u8>, after: Seq<u8>) -> bool {
    before.len() == 256 && after.len() == 256 && forall|i: int| 0 <= i < 256 && !(0 <= i < 2) && !(124 <= i < 126) && !(130 <= i < 132) ==> #[trigger] after[i] == before[i]
}
#[verifier::opaque]
pub open spec fn valid(v: Change) -> bool {
    v.before.len() == 256 && v.after.len() == 256
        && inode::metadata_accepted_with_features(v.before, v.number, v.inodes, v.seed, v.huge)
        && inode::metadata_accepted_with_features(v.after, v.number, v.inodes, v.seed, v.huge)
        && allowed(bytes::le16(v.before, 0) as u16, v.mode) && bytes::le16(v.after, 0) == v.mode
        && framed(v.before, v.after)
        && (bytes::le16(v.before, 0) == v.mode ==> v.after == v.before)
}
fn check(before: &[u8], after: &[u8], mode: u16, number: u32, inodes: u32, seed: u32, huge: bool) -> (r: bool)
    ensures r ==> valid(Change { before: before@, after: after@, mode, number, inodes, seed, huge }),
{
    hide(inode::checksum);
    if before.len() != 256 || after.len() != 256 { return false; }
    if inode::parse_metadata_with_features(before, number, inodes, seed, huge).is_none()
        || inode::parse_metadata_with_features(after, number, inodes, seed, huge).is_none() { return false; }
    let old = bytes::read_le16(before, 0).unwrap();
    if old & !0o2777u16 != mode & !0o2777u16 || old & 0o2000 == 0 && mode & 0o2000 != 0 || bytes::read_le16(after, 0).unwrap() != mode { return false; }
    if old == mode && !bytes::equal(before, after) { return false; }
    let mut i = 0usize;
    while i < 256
        invariant before.len() == 256, after.len() == 256, i <= 256,
            forall|j: int| 0 <= j < i && !(0 <= j < 2) && !(124 <= j < 126) && !(130 <= j < 132) ==> #[trigger] after@[j] == before@[j],
        decreases 256 - i,
    { if !(0 <= i && i < 2) && !(124 <= i && i < 126) && !(130 <= i && i < 132) && after[i] != before[i] { return false; } i += 1; }
    assert(valid(Change { before: before@, after: after@, mode, number, inodes, seed, huge })) by { reveal(valid); }
    true
}
pub fn encode(before: &[u8], mode: u16, number: u32, inodes: u32, seed: u32, huge: bool) -> (r: Option<Vec<u8>>)
    ensures match r { Some(after) => valid(Change { before: before@, after: after@, mode, number, inodes, seed, huge }), None => true },
{
    hide(inode::checksum);
    if before.len() != 256 { return None; }
    let old = bytes::read_le16(before, 0).unwrap();
    let mut after = Vec::new(); let mut i = 0usize;
    while i < 256 invariant before.len() == 256, i <= 256, after@ == before@.take(i as int), decreases 256 - i,
    { after.push(before[i]); assert(after@ =~= before@.take(i as int + 1)); i += 1; }
    if old != mode {
        let word = bytes::encode_le16(mode); bytes::write_bytes(after.as_mut_slice(), 0, &word);
        let crc = inode::calculated_checksum(&after, number, seed).unwrap(); let word = bytes::encode_le32(crc);
        bytes::write_bytes(after.as_mut_slice(), 124, &word[..2]); bytes::write_bytes(after.as_mut_slice(), 130, &word[2..]);
    }
    if !check(before, &after, mode, number, inodes, seed, huge) { return None; }
    Some(after)
}
pub proof fn permission_changes_never_add_set_id_bits_or_change_file_type(v: Change)
    requires valid(v),
    ensures bytes::le16(v.after, 0) as u16 & !0o2777u16 == bytes::le16(v.before, 0) as u16 & !0o2777u16,
        bytes::le16(v.before, 0) as u16 & 0o2000 == 0 ==> bytes::le16(v.after, 0) as u16 & 0o2000 == 0,
{ reveal(valid); }
pub proof fn permission_changes_preserve_every_unrelated_inode_byte(v: Change, i: int)
    requires valid(v), 0 <= i < 256, !(0 <= i < 2), !(124 <= i < 126), !(130 <= i < 132),
    ensures v.after[i] == v.before[i],
{ reveal(valid); }

}
