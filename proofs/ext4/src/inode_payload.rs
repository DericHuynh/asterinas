// SPDX-License-Identifier: MPL-2.0

//! Variable-size Linux inode checksum and payload codecs. These decode wire
//! representations; inode allocation, identity and credential authority remain
//! obligations of filesystem admission and the operation layer.

use vstd::prelude::*;
use crate::{block_size, bytes, crc, inode, inode_blocks, xattr};

verus! {

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Kind { Unused, Fifo, Character, Directory, Block, Regular, Symlink, Socket }

pub open spec fn kind_of(s: Seq<u8>) -> Option<Kind> {
    if s.len() < 2 { None } else { match bytes::le16(s, 0) as u16 & 0xf000 {
        0 => Some(Kind::Unused), 0x1000 => Some(Kind::Fifo), 0x2000 => Some(Kind::Character),
        0x4000 => Some(Kind::Directory), 0x6000 => Some(Kind::Block), 0x8000 => Some(Kind::Regular),
        0xa000 => Some(Kind::Symlink), 0xc000 => Some(Kind::Socket), _ => None,
    } }
}
pub open spec fn size_accepted(inode_bytes: nat, block_bytes: u32) -> bool {
    block_size::accepted(block_bytes as nat) && inode_bytes <= 32768 && inode_bytes <= block_bytes
        && (inode_bytes == 128 || inode_bytes == 256 || inode_bytes == 512 || block_size::accepted(inode_bytes))
}
pub open spec fn extra_present(s: Seq<u8>) -> bool {
    s.len() == 128 || 132 <= s.len() <= 65536
        && bytes::le16(s, 128) % 4 == 0 && bytes::le16(s, 128) <= s.len() - 128
}
pub open spec fn extra(s: Seq<u8>) -> nat { if s.len() == 128 { 0 } else { bytes::le16(s, 128) } }
pub open spec fn checksum_available(s: Seq<u8>, number: u32) -> bool {
    number > 0 && 128 <= s.len() <= 65536 && extra_present(s)
}
pub open spec fn checksum_bytes(s: Seq<u8>) -> Seq<u8> {
    Seq::new(s.len(), |i: int| if i == 124 || i == 125 || extra(s) >= 4 && (i == 130 || i == 131) { 0u8 } else { s[i] })
}
pub open spec fn checksum_value(s: Seq<u8>, number: u32, metadata_seed: u32) -> u32 {
    crc::fold(crc::fold(crc::fold(metadata_seed, bytes::encoded_le(number)),
        bytes::encoded_le(bytes::le32(s, 100) as u32)), checksum_bytes(s))
}
pub open spec fn checksum_matches(s: Seq<u8>, number: u32, metadata_seed: u32) -> bool {
    checksum_available(s, number) && if extra(s) >= 4 {
        bytes::le16(s, 124) + 65536 * bytes::le16(s, 130) == checksum_value(s, number, metadata_seed)
    } else { bytes::le16(s, 124) == checksum_value(s, number, metadata_seed) as nat % 65536 }
}

pub fn kind(raw: &[u8]) -> (r: Option<Kind>)
    ensures r == kind_of(raw@),
{
    let mode = match bytes::read_le16(raw, 0) { Some(mode) => mode & 0xf000, None => { return None; } };
    match mode {
        0 => Some(Kind::Unused), 0x1000 => Some(Kind::Fifo), 0x2000 => Some(Kind::Character),
        0x4000 => Some(Kind::Directory), 0x6000 => Some(Kind::Block), 0x8000 => Some(Kind::Regular),
        0xa000 => Some(Kind::Symlink), 0xc000 => Some(Kind::Socket), _ => None,
    }
}

pub fn valid_size(inode_bytes: usize, block_bytes: u32) -> (r: bool)
    ensures r == size_accepted(inode_bytes as nat, block_bytes),
{
    block_size::valid(block_bytes as usize) && inode_bytes <= 32768 && inode_bytes <= block_bytes as usize
        && (inode_bytes == 128 || inode_bytes == 256 || inode_bytes == 512 || block_size::valid(inode_bytes))
}

/// i_extra_isize specifies a four-byte-aligned prefix of present extra fields.
pub fn extra_size(raw: &[u8]) -> (r: Option<usize>)
    ensures match r { Some(e) => extra_present(raw@) && e == extra(raw@), None => !extra_present(raw@) },
{
    if raw.len() == 128 { return Some(0); }
    if raw.len() < 132 || raw.len() > 65536 { return None; }
    let extra = bytes::read_le16(raw, 128).unwrap() as usize;
    if extra % 4 != 0 || extra > raw.len() - 128 { return None; }
    Some(extra)
}

pub fn checksum(raw: &[u8], number: u32, metadata_seed: u32) -> (r: Option<u32>)
    ensures match r { Some(c) => checksum_available(raw@, number) && c == checksum_value(raw@, number, metadata_seed),
        None => !checksum_available(raw@, number) },
{
    if number == 0 || raw.len() < 128 || raw.len() > 65536 { return None; }
    let extra = match extra_size(raw) { Some(extra) => extra, None => { return None; } };
    let generation = bytes::read_le32(raw, 100).unwrap();
    let seed = inode::inode_seed(metadata_seed, number, generation);
    let mut bytes = Vec::<u8>::new();
    let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len(), extra == self::extra(raw@),
            bytes@ == checksum_bytes(raw@).subrange(0, i as int),
        decreases raw.len() - i,
    {
        let zero = i == 124 || i == 125 || extra >= 4 && (i == 130 || i == 131);
        bytes.push(if zero { 0 } else { raw[i] });
        proof { assert(bytes@ =~= checksum_bytes(raw@).subrange(0, i as int + 1)); }
        i += 1;
    }
    proof { assert(bytes@ =~= checksum_bytes(raw@)); }
    Some(crc::crc32c(seed, bytes.as_slice()))
}

pub fn checksum_valid(raw: &[u8], number: u32, metadata_seed: u32) -> (r: bool)
    ensures r == checksum_matches(raw@, number, metadata_seed),
{
    let calculated = match checksum(raw, number, metadata_seed) {
        Some(calculated) => calculated, None => { return false; }
    };
    let low = bytes::read_le16(raw, 124).unwrap() as u32;
    let extra = extra_size(raw).unwrap();
    if extra >= 4 {
        low + (bytes::read_le16(raw, 130).unwrap() as u32) * 65536 == calculated
    } else { low == calculated % 65536 }
}

pub fn seal(raw: &[u8], number: u32, metadata_seed: u32) -> (r: Option<Vec<u8>>)
    ensures match r {
        Some(sealed) => sealed.len() == raw.len() && checksum_matches(sealed@, number, metadata_seed)
            && checksum_bytes(sealed@) == checksum_bytes(raw@)
            && forall|i: int| 0 <= i < raw.len()
                && i != 124 && i != 125 && !(extra(raw@) >= 4 && (i == 130 || i == 131))
                ==> #[trigger] sealed@[i] == raw@[i],
        None => !checksum_available(raw@, number),
    },
{
    let sum = match checksum(raw, number, metadata_seed) { Some(sum) => sum, None => { return None; } };
    let mut result = Vec::<u8>::new();
    let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len(), result@ == raw@.subrange(0, i as int),
        decreases raw.len() - i,
    { result.push(raw[i]); i += 1; }
    proof { assert(result@ =~= raw@); }
    let low = bytes::encode_le16((sum % 65536) as u16);
    result.set(124, low[0]); result.set(125, low[1]);
    if extra_size(raw).unwrap() >= 4 {
        let high = bytes::encode_le16((sum / 65536) as u16);
        result.set(130, high[0]); result.set(131, high[1]);
    }
    proof {
        assert(checksum_bytes(result@) =~= checksum_bytes(raw@));
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(sum as int, 65536);
    }
    Some(result)
}

/// Linux selects fast symlinks differently when EA_INODE billing is enabled:
/// i_blocks may then include EA values and is not a discriminator.
/// This returns stored bytes, including orphan/crypto representations; it does
/// not admit a plaintext target. Use plain_fast_symlink for a live plain target.
pub fn fast_symlink<'a>(raw: &'a [u8], block_bytes: u32, cluster_bytes: u32,
    huge_file: bool, ea_inode: bool) -> (r: Option<&'a [u8]>)
    ensures match r { Some(target) => 128 <= raw.len() <= 65536
        && block_size::accepted(block_bytes as nat)
        && cluster_bytes >= block_bytes && cluster_bytes % block_bytes == 0
        && bytes::le16(raw@, 0) as u16 & 0xf000 == 0xa000
        && bytes::le32(raw@, 4) < 60
        && target@ == raw@.subrange(40, 40 + bytes::le32(raw@, 4) as int),
        None => true },
{
    if raw.len() < 128 || raw.len() > 65536 || !block_size::valid(block_bytes as usize)
        || cluster_bytes < block_bytes || cluster_bytes % block_bytes != 0 { return None; }
    if bytes::read_le16(raw, 0).unwrap() & 0xf000 != 0xa000 { return None; }
    let size = bytes::read_le32(raw, 4).unwrap() as usize;
    let fast = if ea_inode { size > 0 && size < 60 } else {
        if bytes::read_le32(raw, 32).unwrap() & 0x10000000 != 0 { return None; }
        let sectors = inode_blocks::decode(raw, block_bytes, huge_file).unwrap();
        let ea_blocks = if xattr::inode_pointer(raw).unwrap() != 0 { cluster_bytes as u64 / 512 } else { 0 };
        sectors == ea_blocks
    };
    if !fast || size >= 60 { return None; }
    Some(&raw[40..40 + size])
}

/// Live, unencrypted fast target admitted with Linux iget's terminating-NUL
/// rule. Empty orphan storage is deliberately handled by a separate workflow.
pub fn plain_fast_symlink<'a>(raw: &'a [u8], block_bytes: u32, cluster_bytes: u32,
    huge_file: bool, ea_inode: bool) -> (r: Option<&'a [u8]>)
    ensures match r { Some(target) => 0 < target.len() < 60
        && raw.len() >= 128 && bytes::le32(raw@, 32) as u32 & 0x830 == 0
        && target@ == raw@.subrange(40, 40 + target.len() as int)
        && raw@[40 + target.len() as int] == 0
        && forall|i: int| 0 <= i < target.len() ==> #[trigger] target@[i] != 0,
        None => true },
{
    let target = match fast_symlink(raw, block_bytes, cluster_bytes, huge_file, ea_inode) {
        Some(target) => target, None => { return None; }
    };
    // ENCRYPT, IMMUTABLE and APPEND are not ordinary live plain targets.
    if bytes::read_le32(raw, 32).unwrap() & 0x830 != 0 || target.len() == 0
        || raw[40 + target.len()] != 0 { return None; }
    let mut i = 0usize;
    while i < target.len()
        invariant i <= target.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] target@[j] != 0,
        decreases target.len() - i,
    {
        if target[i] == 0 { return None; }
        i += 1;
    }
    Some(target)
}

pub struct DeviceNumber { pub major: u32, pub minor: u32 }

pub fn device(raw: &[u8]) -> (r: Option<DeviceNumber>)
    ensures match r { Some(d) => raw.len() >= 100 && d.major <= 0xfff && d.minor <= 0xfffff,
        None => true },
{
    if raw.len() < 100 { return None; }
    let mode = bytes::read_le16(raw, 0).unwrap() & 0xf000;
    if mode != 0x2000 && mode != 0x6000 { return None; }
    let old = bytes::read_le32(raw, 40).unwrap();
    if old != 0 {
        if old > 65535 { return None; }
        assert(old >> 8 <= 0xfff) by (bit_vector) requires old <= 65535;
        assert(old & 255 <= 0xfffff) by (bit_vector);
        Some(DeviceNumber { major: old >> 8, minor: old & 255 })
    } else {
        let new = bytes::read_le32(raw, 44).unwrap();
        assert((new >> 8) & 0xfff <= 0xfff) by (bit_vector);
        assert((new & 0xff) | ((new >> 12) & 0xfff00) <= 0xfffff) by (bit_vector);
        Some(DeviceNumber { major: (new >> 8) & 0xfff, minor: (new & 0xff) | ((new >> 12) & 0xfff00) })
    }
}

pub fn encode_device(major: u32, minor: u32) -> (r: Option<[u8; 60]>)
    ensures r.is_some() == (major <= 0xfff && minor <= 0xfffff),
{
    if major > 0xfff || minor > 0xfffff { return None; }
    let mut result = [0u8; 60];
    let (at, value) = if major <= 255 && minor <= 255 { (0usize, (major << 8) | minor) }
        else { (4usize, (minor & 255) | (major << 8) | ((minor & 0xfff00) << 12)) };
    let encoded = bytes::encode_le32(value);
    let mut i = 0usize;
    while i < 4
        invariant i <= 4, at == 0 || at == 4,
        decreases 4 - i,
    { result[at + i] = encoded[i]; i += 1; }
    Some(result)
}

}
