// SPDX-License-Identifier: MPL-2.0

//! EA value hashes and the historical signed-name read variant. CRC equality
//! is an integrity check; full value bytes are required for deduplication.

use vstd::prelude::*;
use crate::{crc, xattr_hash};

verus! {

pub open spec fn name_word(byte: u8, signed: bool) -> u32 {
    if signed && byte >= 128 { 0xffffff00u32 | byte as u32 } else { byte as u32 }
}
pub open spec fn names(name: Seq<u8>, signed: bool) -> u32 decreases name.len() {
    if name.len() == 0 { 0u32 } else { xattr_hash::rotate5(names(name.drop_last(), signed)) ^ name_word(name.last(), signed) }
}
pub open spec fn entry(name: Seq<u8>, hash: u32, signed: bool) -> u32 {
    xattr_hash::rotate16(names(name, signed)) ^ hash
}
pub fn entry_hash(name: &[u8], hash: u32, signed: bool) -> (r: Option<u32>)
    ensures match r { Some(value) => name.len() <= 255 && value == entry(name@, hash, signed), None => name.len() > 255 },
{
    if name.len() > 255 { return None; }
    let mut value = 0u32; let mut i = 0usize;
    while i < name.len()
        invariant i <= name.len() <= 255, value == names(name@.take(i as int), signed),
        decreases name.len() - i,
    {
        let word = if signed && name[i] >= 128 { 0xffffff00u32 | name[i] as u32 } else { name[i] as u32 };
        value = (value << 5) ^ (value >> 27) ^ word;
        assert(name@.take(i as int + 1).drop_last() =~= name@.take(i as int));
        i += 1;
    }
    assert(name@.take(i as int) =~= name@);
    Some((value << 16) ^ (value >> 16) ^ hash)
}
pub fn matches(name: &[u8], data: &[u8], seed: u32, inode_hash: u32, entry_hash: u32) -> (r: bool)
    ensures r ==> name.len() <= 255 && 0 < data.len() <= 16777216 && crc::fold(seed, data@) == inode_hash
        && (entry_hash == entry(name@, inode_hash, false) || entry_hash == entry(name@, inode_hash, true)),
{
    if data.len() == 0 || data.len() > 16777216 || name.len() > 255 { return false; }
    let hash = crc::crc32c(seed, data);
    if hash != inode_hash { return false; }
    entry_hash == self::entry_hash(name, hash, false).unwrap() || entry_hash == self::entry_hash(name, hash, true).unwrap()
}
pub proof fn ea_entry_hashes_combine_the_name_with_one_value_crc_word(name: Seq<u8>, hash: u32, signed: bool)
    ensures entry(name, hash, signed) == xattr_hash::rotate16(names(name, signed)) ^ hash,
{}
pub proof fn ascii_names_have_identical_signed_and_unsigned_ea_hashes(name: Seq<u8>, hash: u32)
    requires forall|i: int| 0 <= i < name.len() ==> #[trigger] name[i] < 128,
    ensures names(name, false) == names(name, true), entry(name, hash, false) == entry(name, hash, true),
    decreases name.len(),
{
    if name.len() > 0 {
        assert forall|i: int| 0 <= i < name.drop_last().len() implies #[trigger] name.drop_last()[i] < 128 by { }
        ascii_names_have_identical_signed_and_unsigned_ea_hashes(name.drop_last(), hash);
    }
}

}
