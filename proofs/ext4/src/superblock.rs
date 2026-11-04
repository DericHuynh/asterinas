// SPDX-License-Identifier: MPL-2.0

//! Structural admission only. A successful parse is not a mount certificate:
//! group metadata, ownership, namespace, and journal recovery need validation.

use vstd::prelude::*;
use crate::bytes::{le16, le32, read_le16, read_le32, block_offset};
use crate::crc;

verus! {

/// ext4 metadata checksums use the stored seed when CSUM_SEED is enabled.
/// The superblock's own checksum always starts from ~0; JBD2 has a separate
/// UUID-derived checksum domain.
#[verifier::opaque]
pub open spec fn metadata_seed(s: Seq<u8>) -> u32 {
    if le32(s, 96) as u32 & 0x2000 != 0 { le32(s, 624) as u32 }
    else { crc::fold(0xffffffff, s.subrange(104, 120)) }
}

pub fn metadata_checksum_seed(s: &[u8]) -> (r: Option<u32>)
    ensures match r { Some(seed) => s.len() == 1024 && seed == metadata_seed(s@), None => s.len() != 1024 },
{
    proof { reveal(metadata_seed); }
    if s.len() != 1024 { return None; }
    if read_le32(s, 96).unwrap() & 0x2000 != 0 { read_le32(s, 624) }
    else { Some(crc::crc32c(0xffffffff, &s[104..120])) }
}

pub open spec fn descriptor_bytes(s: Seq<u8>) -> nat {
    if le32(s, 96) as u32 & 0x80 != 0 { 64nat } else { 32nat }
}

pub fn descriptor_length(s: &[u8]) -> (r: Option<usize>)
    ensures match r { Some(length) => s.len() == 1024 && length as nat == descriptor_bytes(s@) && (length == 32 || length == 64),
        None => s.len() != 1024 },
{
    if s.len() != 1024 { return None; }
    Some(if read_le32(s, 96).unwrap() & 0x80 != 0 { 64usize } else { 32usize })
}

pub open spec fn flex_bg(s: Seq<u8>) -> bool { le32(s, 96) as u32 & 0x200 != 0 }

pub open spec fn flex_shift(s: Seq<u8>) -> u8 {
    if flex_bg(s) && 1 <= s[372] <= 31 { s[372] } else { 0u8 }
}

pub fn flex_enabled(s: &[u8]) -> (r: Option<bool>)
    ensures match r { Some(enabled) => s.len() == 1024 && enabled == flex_bg(s@), None => s.len() != 1024 },
{
    if s.len() != 1024 { return None; }
    Some(read_le32(s, 96).unwrap() & 0x200 != 0)
}

pub fn normalized_flex_shift(s: &[u8]) -> (r: Option<u8>)
    ensures match r { Some(shift) => s.len() == 1024 && shift == flex_shift(s@) && shift <= 31,
        None => s.len() != 1024 },
{
    if s.len() != 1024 { return None; }
    Some(if read_le32(s, 96).unwrap() & 0x200 != 0 && 1 <= s[372] && s[372] <= 31 { s[372] } else { 0u8 })
}

pub struct Superblock {
    blocks: u32,
    inodes: u32,
    groups: u32,
    inodes_per_group: u32,
    journal_inode: u32,
    needs_recovery: bool,
}

pub open spec fn accepted(s: Seq<u8>, partition_bytes: u64) -> bool {
    &&& s.len() == 1024
    &&& le16(s, 56) == 0xef53
    &&& le16(s, 58) == 1
    &&& le32(s, 20) == 0
    &&& le32(s, 24) == 2
    &&& le32(s, 28) == 2
    &&& le32(s, 32) == 32768
    &&& le32(s, 36) == 32768
    &&& le32(s, 72) == 0
    &&& le32(s, 76) == 1
    &&& le32(s, 84) == 11
    &&& le16(s, 88) == 256
    &&& le32(s, 92) == 4
    &&& (le32(s, 96) as u32 & 0xffffdd7bu32 == 0x42)
    &&& (le32(s, 100) == 0x443 || le32(s, 100) == 0x44b)
    &&& (if descriptor_bytes(s) == 64 { le16(s, 254) == 64 } else { le16(s, 254) == 0 || le16(s, 254) == 32 })
    &&& le16(s, 206) == 0
    &&& le32(s, 228) == 0
    &&& le32(s, 232) == 0
    &&& le16(s, 348) == 32
    &&& le16(s, 350) == 32
    &&& s[373] == 1
    &&& le32(s, 336) == 0
    &&& le32(s, 340) == 0
    &&& le32(s, 344) == 0
    &&& 2 < le32(s, 4)
    &&& le32(s, 4) * 4096 <= partition_bytes
    &&& le32(s, 8) <= le32(s, 4)
    &&& le32(s, 12) <= le32(s, 4)
    &&& le32(s, 16) <= le32(s, 0)
    &&& 0 < le32(s, 40) <= 32768
    &&& le32(s, 40) % 16 == 0
    &&& le32(s, 0) == ((le32(s, 4) + 32767) / 32768) * le32(s, 40)
    &&& le32(s, 224) == 8 && le32(s, 0) >= 11
    &&& le32(s, 1020) == crc::fold(0xffffffff, s.subrange(0, 1020)) as nat
}

pub struct Geometry {
    pub blocks: u32,
    pub inodes: u32,
    pub groups: u32,
    pub inodes_per_group: u32,
    pub journal_inode: u32,
    pub needs_recovery: bool,
}

impl Superblock {
    pub closed spec fn view(&self) -> Geometry {
        Geometry { blocks: self.blocks, inodes: self.inodes, groups: self.groups,
            inodes_per_group: self.inodes_per_group, journal_inode: self.journal_inode,
            needs_recovery: self.needs_recovery }
    }
    pub open spec fn wf(&self) -> bool {
        &&& self.view().blocks > 2
        &&& self.view().groups as nat == (self.view().blocks as nat + 32767) / 32768
        &&& 0 < self.view().inodes_per_group <= 32768
        &&& self.view().inodes_per_group % 16 == 0
        &&& self.view().inodes as nat == self.view().groups as nat * self.view().inodes_per_group as nat
        &&& self.view().journal_inode == 8 && self.view().inodes >= 11
    }

    pub open spec fn represents(&self, s: Seq<u8>) -> bool {
        &&& self.view().blocks as nat == le32(s, 4)
        &&& self.view().inodes as nat == le32(s, 0)
        &&& self.view().inodes_per_group as nat == le32(s, 40)
        &&& self.view().journal_inode as nat == le32(s, 224)
        &&& self.view().needs_recovery == (le32(s, 96) as u32 & 4 != 0)
    }

    pub fn blocks(&self) -> (r: u32) ensures r == self.view().blocks { self.blocks }
    pub fn inodes(&self) -> (r: u32) ensures r == self.view().inodes { self.inodes }
    pub fn groups(&self) -> (r: u32) ensures r == self.view().groups { self.groups }
    pub fn journal_inode(&self) -> (r: u32) ensures r == self.view().journal_inode { self.journal_inode }
    pub fn needs_recovery(&self) -> (r: bool) ensures r == self.view().needs_recovery { self.needs_recovery }

    pub fn offset(&self, block: u32, partition_bytes: u64) -> (r: Option<u64>)
        ensures match r {
            Some(o) => block < self.view().blocks && o as int == block as int * 4096
                && o as int + 4096 <= partition_bytes,
            None => block >= self.view().blocks || block as int * 4096 + 4096 > partition_bytes,
        },
    {
        block_offset(block, self.blocks, partition_bytes)
    }
}

pub fn parse(s: &[u8], partition_bytes: u64) -> (r: Option<Superblock>)
    ensures match r {
        Some(sb) => accepted(s@, partition_bytes) && sb.wf() && sb.represents(s@),
        None => !accepted(s@, partition_bytes),
    },
{
    if s.len() != 1024 { return None; }
    if read_le16(s, 56).unwrap() != 0xef53 || read_le16(s, 58).unwrap() != 1
        || read_le32(s, 20).unwrap() != 0 || read_le32(s, 24).unwrap() != 2
        || read_le32(s, 28).unwrap() != 2 || read_le32(s, 32).unwrap() != 32768
        || read_le32(s, 36).unwrap() != 32768 || read_le32(s, 72).unwrap() != 0
        || read_le32(s, 76).unwrap() != 1 || read_le32(s, 84).unwrap() != 11
        || read_le16(s, 88).unwrap() != 256 || read_le32(s, 92).unwrap() != 4
    { return None; }
    let incompat = read_le32(s, 96).unwrap();
    let desc_size = read_le16(s, 254).unwrap();
    let ro_compat = read_le32(s, 100).unwrap();
    if (incompat & 0xffffdd7bu32 != 0x42) || (ro_compat != 0x443 && ro_compat != 0x44b)
        || (if incompat & 0x80 != 0 { desc_size != 64 } else { desc_size != 0 && desc_size != 32 }) || read_le16(s, 206).unwrap() != 0
        || read_le32(s, 228).unwrap() != 0 || read_le32(s, 232).unwrap() != 0
        || read_le16(s, 348).unwrap() != 32 || read_le16(s, 350).unwrap() != 32
        || s[373] != 1 || read_le32(s, 336).unwrap() != 0
        || read_le32(s, 340).unwrap() != 0 || read_le32(s, 344).unwrap() != 0
    { return None; }
    let blocks = read_le32(s, 4).unwrap();
    let inodes = read_le32(s, 0).unwrap();
    let ipg = read_le32(s, 40).unwrap();
    let journal_inode = read_le32(s, 224).unwrap();
    let groups = ((blocks as u64 + 32767) / 32768) as u32;
    assert(groups as int * ipg as int <= 18446744073709551615) by (nonlinear_arith);
    if blocks <= 2 || blocks as u64 * 4096 > partition_bytes
        || read_le32(s, 8).unwrap() > blocks || read_le32(s, 12).unwrap() > blocks
        || read_le32(s, 16).unwrap() > inodes
        || ipg == 0 || ipg > 32768 || ipg % 16 != 0
        || inodes as u64 != groups as u64 * ipg as u64
        || journal_inode != 8 || inodes < 11
    { return None; }
    let checksum = crc::crc32c(0xffffffff, &s[0..1020]);
    if read_le32(s, 1020).unwrap() != checksum { return None; }
    Some(Superblock { blocks, inodes, groups, inodes_per_group: ipg,
        journal_inode, needs_recovery: incompat & 4 != 0 })
}

}
