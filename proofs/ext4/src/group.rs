// SPDX-License-Identifier: MPL-2.0

//! 32-byte descriptors for the non-flex_bg, non-meta_bg, metadata_csum profile.
//! Local range checks do not replace global allocation/extent validation.

use vstd::prelude::*;
use crate::bytes::{le16, le32, read_le16, read_le32, encode_le32};
use crate::crc;

verus! {

pub struct Group {
    pub number: u32,
    pub block_bitmap: u32,
    pub inode_bitmap: u32,
    pub inode_table: u32,
    pub inode_table_blocks: u32,
}

pub open spec fn end(blocks: u32, group: u32) -> nat {
    if (group as nat + 1) * 32768 < blocks { (group as nat + 1) * 32768 }
    else { blocks as nat }
}

pub open spec fn encoded_le(v: u32) -> Seq<u8> {
    seq![(v % 256) as u8, ((v / 256) % 256) as u8,
        ((v / 65536) % 256) as u8, (v / 16777216) as u8]
}

pub open spec fn accepted(s: Seq<u8>, group: u32, blocks: u32, ipg: u32, uuid_seed: u32) -> bool {
    &&& s.len() == 32
    &&& blocks > 2 && 0 < ipg <= 32768 && ipg % 16 == 0
    &&& (group as nat) < (blocks as nat + 32767) / 32768
    &&& group as nat * 32768 <= le32(s, 0) < end(blocks, group)
    &&& group as nat * 32768 <= le32(s, 4) < end(blocks, group)
    &&& group as nat * 32768 <= le32(s, 8)
    &&& le32(s, 8) + ipg as nat / 16 <= end(blocks, group)
    &&& le32(s, 0) != le32(s, 4)
    &&& !(le32(s, 8) <= le32(s, 0) < le32(s, 8) + ipg as nat / 16)
    &&& !(le32(s, 8) <= le32(s, 4) < le32(s, 8) + ipg as nat / 16)
    &&& le16(s, 12) <= end(blocks, group) - group as nat * 32768
    &&& le16(s, 14) <= ipg && le16(s, 16) <= ipg && le16(s, 28) <= ipg
    &&& le16(s, 18) == 4
    &&& le16(s, 30) == (crc::fold(crc::fold(uuid_seed, encoded_le(group)),
        s.subrange(0, 30) + seq![0u8, 0u8]) & 0xffffu32) as nat
}

pub fn parse(s: &[u8], group: u32, blocks: u32, ipg: u32, uuid_seed: u32) -> (r: Option<Group>)
    ensures match r {
        Some(g) => accepted(s@, group, blocks, ipg, uuid_seed) && g.number == group
            && g.block_bitmap as nat == le32(s@, 0) && g.inode_bitmap as nat == le32(s@, 4)
            && g.inode_table as nat == le32(s@, 8) && g.inode_table_blocks == ipg / 16,
        None => !accepted(s@, group, blocks, ipg, uuid_seed),
    },
{
    if s.len() != 32 || blocks <= 2 || ipg == 0 || ipg > 32768 || ipg % 16 != 0
        || group as u64 >= (blocks as u64 + 32767) / 32768 { return None; }
    let first = group as u64 * 32768;
    let next = (group as u64 + 1) * 32768;
    let limit = if next < blocks as u64 { next } else { blocks as u64 };
    let block_bitmap = read_le32(s, 0).unwrap();
    let inode_bitmap = read_le32(s, 4).unwrap();
    let inode_table = read_le32(s, 8).unwrap();
    let table_end = inode_table as u64 + (ipg / 16) as u64;
    if (block_bitmap as u64) < first || block_bitmap as u64 >= limit
        || (inode_bitmap as u64) < first || inode_bitmap as u64 >= limit
        || (inode_table as u64) < first || table_end > limit || block_bitmap == inode_bitmap
        || (inode_table <= block_bitmap && (block_bitmap as u64) < table_end)
        || (inode_table <= inode_bitmap && (inode_bitmap as u64) < table_end)
        || read_le16(s, 12).unwrap() as u64 > limit - first
        || read_le16(s, 14).unwrap() as u32 > ipg || read_le16(s, 16).unwrap() as u32 > ipg
        || read_le16(s, 28).unwrap() as u32 > ipg || read_le16(s, 18).unwrap() != 4
    { return None; }
    let number = encode_le32(group);
    proof { assert(number@ =~= encoded_le(group)); }
    let seed = crc::crc32c(uuid_seed, &number);
    let partial = crc::crc32c(seed, &s[0..30]);
    let zeros = [0u8, 0u8];
    let checksum = crc::crc32c(partial, &zeros) & 0xffffu32;
    proof { crc::streaming(seed, s@.subrange(0, 30), zeros@); }
    if read_le16(s, 30).unwrap() as u32 != checksum { return None; }
    Some(Group { number: group, block_bitmap, inode_bitmap, inode_table, inode_table_blocks: ipg / 16 })
}

}
