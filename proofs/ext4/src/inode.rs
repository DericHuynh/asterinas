// SPDX-License-Identifier: MPL-2.0

//! A 256-byte Linux inode subset: regular files and linear directories,
//! metadata checksums and no xattrs/ACL block. Metadata parsing is separate
//! from the legacy inline-leaf parser and wider source-bound tree validation.
//! Link topology, allocation accounting and global ownership remain separate.

use vstd::prelude::*;
use crate::bytes::{le16, le32, read_le16, read_le32, encode_le32};
use crate::{crc, extent, group::encoded_le, inode_size};

verus! {

pub struct Inode {
    pub mode: u16,
    pub uid: u32,
    pub gid: u32,
    pub size: u64,
    pub generation: u32,
    pub links: u16,
}

pub open spec fn checksum_input(s: Seq<u8>) -> Seq<u8> {
    s.subrange(0, 124) + seq![0u8, 0u8] + s.subrange(126, 130)
        + seq![0u8, 0u8] + s.subrange(132, 256)
}

pub open spec fn checksum(s: Seq<u8>, inode: u32, uuid_seed: u32) -> u32 {
    crc::fold(crc::fold(crc::fold(uuid_seed, encoded_le(inode)),
        encoded_le(le32(s, 100) as u32)), checksum_input(s))
}

pub open spec fn metadata_accepted_with_features(s: Seq<u8>, inode: u32, inodes: u32, uuid_seed: u32, huge_file: bool) -> bool {
    &&& s.len() == 256
    &&& 0 < inode <= inodes
    &&& ((le16(s, 0) as u16 & 0xf000) == 0x8000 || (le16(s, 0) as u16 & 0xf000) == 0x4000)
    &&& le32(s, 20) == 0 && le16(s, 26) > 0
    &&& (le32(s, 32) == 0x80000 || huge_file && le32(s, 32) == 0xc0000)
    &&& le32(s, 104) == 0 && le16(s, 118) == 0
    &&& ((le16(s, 0) as u16 & 0xf000) == 0x4000 ==> le32(s, 108) == 0)
    &&& inode_size::accepted(s, 4096, huge_file, false)
    &&& le16(s, 128) == 32
    &&& le16(s, 124) + 65536 * le16(s, 130) == checksum(s, inode, uuid_seed) as nat
}

pub open spec fn metadata_accepted(s: Seq<u8>, inode: u32, inodes: u32, uuid_seed: u32) -> bool {
    metadata_accepted_with_features(s, inode, inodes, uuid_seed, false)
}

pub open spec fn accepted(s: Seq<u8>, inode: u32, inodes: u32, blocks: u32, uuid_seed: u32) -> bool {
    &&& metadata_accepted(s, inode, inodes, uuid_seed) && le32(s, 108) == 0
    &&& extent::leaf_header(s.subrange(40, 100))
    &&& extent::leaf_entries(s.subrange(40, 100), le16(s, 42), blocks)
}

pub fn inode_seed(uuid_seed: u32, number: u32, generation: u32) -> (r: u32)
    ensures r == crc::fold(crc::fold(uuid_seed, encoded_le(number)), encoded_le(generation)),
{
    let n = encode_le32(number);
    let g = encode_le32(generation);
    proof { assert(n@ =~= encoded_le(number)); assert(g@ =~= encoded_le(generation)); }
    let seed = crc::crc32c(uuid_seed, &n);
    crc::crc32c(seed, &g)
}

pub fn calculated_checksum(s: &[u8], inode: u32, uuid_seed: u32) -> (r: Option<u32>)
    ensures match r {
        Some(c) => s.len() == 256 && c == checksum(s@, inode, uuid_seed),
        None => s.len() != 256,
    },
{
    if s.len() != 256 { return None; }
    let seed = inode_seed(uuid_seed, inode, read_le32(s, 100).unwrap());
    let zeros = [0u8, 0u8];
    let a = crc::crc32c(seed, &s[0..124]);
    let b = crc::crc32c(a, &zeros);
    let c = crc::crc32c(b, &s[126..130]);
    let d = crc::crc32c(c, &zeros);
    let e = crc::crc32c(d, &s[132..256]);
    proof {
        crc::streaming(seed, s@.subrange(0, 124), zeros@);
        crc::streaming(seed, s@.subrange(0, 124) + zeros@, s@.subrange(126, 130));
        crc::streaming(seed, s@.subrange(0, 124) + zeros@ + s@.subrange(126, 130), zeros@);
        crc::streaming(seed, s@.subrange(0, 124) + zeros@ + s@.subrange(126, 130) + zeros@,
            s@.subrange(132, 256));
    }
    Some(e)
}

pub fn parse_metadata_with_features(s: &[u8], number: u32, inodes: u32, uuid_seed: u32, huge_file: bool) -> (r: Option<Inode>)
    ensures match r {
        Some(i) => metadata_accepted_with_features(s@, number, inodes, uuid_seed, huge_file)
            && i.mode as nat == le16(s@, 0) && i.size as nat == inode_size::value(s@, false)
            && i.generation as nat == le32(s@, 100) && i.links as nat == le16(s@, 26)
            && i.uid as nat == le16(s@, 2) + 65536 * le16(s@, 120)
            && i.gid as nat == le16(s@, 24) + 65536 * le16(s@, 122),
        None => !metadata_accepted_with_features(s@, number, inodes, uuid_seed, huge_file),
    },
{
    if s.len() != 256 || number == 0 || number > inodes { return None; }
    let mode = read_le16(s, 0).unwrap();
    let links = read_le16(s, 26).unwrap();
    if (mode & 0xf000 != 0x8000 && mode & 0xf000 != 0x4000)
        || read_le32(s, 20).unwrap() != 0 || links == 0 || (read_le32(s, 32).unwrap() != 0x80000 && (!huge_file || read_le32(s, 32).unwrap() != 0xc0000))
        || read_le32(s, 104).unwrap() != 0 || (mode & 0xf000 == 0x4000 && read_le32(s, 108).unwrap() != 0)
        || read_le16(s, 118).unwrap() != 0 || read_le16(s, 128).unwrap() != 32
    { return None; }
    let size = match inode_size::decode(s, 4096, huge_file, false) { Some(size) => size, None => { return None; } };
    let supplied = read_le16(s, 124).unwrap() as u32 + 65536 * read_le16(s, 130).unwrap() as u32;
    if supplied != calculated_checksum(s, number, uuid_seed).unwrap() { return None; }
    let uid = read_le16(s, 2).unwrap() as u32 + 65536 * read_le16(s, 120).unwrap() as u32;
    let gid = read_le16(s, 24).unwrap() as u32 + 65536 * read_le16(s, 122).unwrap() as u32;
    Some(Inode { mode, uid, gid, links, size,
        generation: read_le32(s, 100).unwrap() })
}

pub fn parse_metadata(s: &[u8], number: u32, inodes: u32, uuid_seed: u32) -> (r: Option<Inode>)
    ensures match r {
        Some(i) => metadata_accepted(s@, number, inodes, uuid_seed)
            && i.mode as nat == le16(s@, 0) && i.size as nat == inode_size::value(s@, false)
            && i.generation as nat == le32(s@, 100) && i.links as nat == le16(s@, 26)
            && i.uid as nat == le16(s@, 2) + 65536 * le16(s@, 120)
            && i.gid as nat == le16(s@, 24) + 65536 * le16(s@, 122),
        None => !metadata_accepted(s@, number, inodes, uuid_seed),
    },
{
    parse_metadata_with_features(s, number, inodes, uuid_seed, false)
}

pub fn parse(s: &[u8], number: u32, inodes: u32, blocks: u32, uuid_seed: u32) -> (r: Option<Inode>)
    ensures match r {
        Some(i) => accepted(s@, number, inodes, blocks, uuid_seed)
            && i.mode as nat == le16(s@, 0) && i.size as nat == le32(s@, 4)
            && i.generation as nat == le32(s@, 100) && i.links as nat == le16(s@, 26)
            && i.uid as nat == le16(s@, 2) + 65536 * le16(s@, 120)
            && i.gid as nat == le16(s@, 24) + 65536 * le16(s@, 122),
        None => !accepted(s@, number, inodes, blocks, uuid_seed),
    },
{
    let meta = match parse_metadata(s, number, inodes, uuid_seed) { Some(meta) => meta, None => { return None; } };
    if read_le32(s, 108).unwrap() != 0 || extent::validate_inline_root(&s[40..100], blocks).is_none() { return None; }
    Some(meta)
}

}
