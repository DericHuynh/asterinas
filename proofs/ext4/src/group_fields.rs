// SPDX-License-Identifier: MPL-2.0

//! Exact Linux low/high group fields. These total codecs preserve all bits;
//! geometry, source ownership and allocation admission are separate checks.

use vstd::prelude::*;
use crate::bytes;

verus! {

pub open spec fn address(raw: Seq<u8>, low: int, high: int, wide: bool) -> nat {
    bytes::le32(raw, low) + if wide { 4294967296 * bytes::le32(raw, high) } else { 0nat }
}

pub open spec fn counter(raw: Seq<u8>, low: int, high: int, wide: bool) -> nat {
    bytes::le16(raw, low) + if wide { 65536 * bytes::le16(raw, high) } else { 0nat }
}

pub fn read_address(raw: &[u8], low: usize, high: usize, wide: bool) -> (r: Option<u64>)
    ensures match r {
        Some(value) => low as nat + 4 <= raw.len() && (!wide || high as nat + 4 <= raw.len())
            && value as nat == address(raw@, low as int, high as int, wide),
        None => low as nat + 4 > raw.len() || wide && high as nat + 4 > raw.len(),
    },
{
    let low_value = match bytes::read_le32(raw, low) { Some(v) => v, None => { return None; } };
    let high_value = if wide {
        match bytes::read_le32(raw, high) { Some(v) => v, None => { return None; } }
    } else { 0u32 };
    Some(low_value as u64 + high_value as u64 * 4294967296)
}

pub fn read_counter(raw: &[u8], low: usize, high: usize, wide: bool) -> (r: Option<u32>)
    ensures match r {
        Some(value) => low as nat + 2 <= raw.len() && (!wide || high as nat + 2 <= raw.len())
            && value as nat == counter(raw@, low as int, high as int, wide),
        None => low as nat + 2 > raw.len() || wide && high as nat + 2 > raw.len(),
    },
{
    let low_value = match bytes::read_le16(raw, low) { Some(v) => v, None => { return None; } };
    let high_value = if wide {
        match bytes::read_le16(raw, high) { Some(v) => v, None => { return None; } }
    } else { 0u16 };
    Some(low_value as u32 + high_value as u32 * 65536)
}

pub fn encode_address(value: u64, wide: bool) -> (r: Option<([u8; 4], [u8; 4])>)
    ensures match r {
        Some((low, high)) => (wide || value <= 4294967295)
            && bytes::le32(low@, 0) + 4294967296 * bytes::le32(high@, 0) == value as nat
            && (!wide ==> bytes::le32(high@, 0) == 0),
        None => !wide && value > 4294967295,
    },
{
    if !wide && value > 4294967295 { return None; }
    Some((bytes::encode_le32((value % 4294967296) as u32), bytes::encode_le32((value / 4294967296) as u32)))
}

pub fn encode_counter(value: u32, wide: bool) -> (r: Option<([u8; 2], [u8; 2])>)
    ensures match r {
        Some((low, high)) => (wide || value <= 65535)
            && bytes::le16(low@, 0) + 65536 * bytes::le16(high@, 0) == value as nat
            && (!wide ==> bytes::le16(high@, 0) == 0),
        None => !wide && value > 65535,
    },
{
    if !wide && value > 65535 { return None; }
    Some((bytes::encode_le16((value % 65536) as u16), bytes::encode_le16((value / 65536) as u16)))
}

pub struct Fields {
    pub block_bitmap: u64, pub inode_bitmap: u64, pub inode_table: u64,
    pub free_blocks: u32, pub free_inodes: u32, pub directories: u32, pub unused: u32,
    pub block_checksum: u32, pub inode_checksum: u32,
}

pub open spec fn represents(f: Fields, raw: Seq<u8>, wide: bool) -> bool {
    &&& raw.len() == if wide { 64int } else { 32int }
    &&& f.block_bitmap as nat == address(raw, 0, 32, wide)
    &&& f.inode_bitmap as nat == address(raw, 4, 36, wide)
    &&& f.inode_table as nat == address(raw, 8, 40, wide)
    &&& f.free_blocks as nat == counter(raw, 12, 44, wide)
    &&& f.free_inodes as nat == counter(raw, 14, 46, wide)
    &&& f.directories as nat == counter(raw, 16, 48, wide)
    &&& f.unused as nat == counter(raw, 28, 50, wide)
    &&& f.block_checksum as nat == counter(raw, 24, 56, wide)
    &&& f.inode_checksum as nat == counter(raw, 26, 58, wide)
}

pub fn decode(raw: &[u8], wide: bool) -> (r: Option<Fields>)
    ensures match r { Some(f) => represents(f, raw@, wide), None => raw.len() != if wide { 64int } else { 32int } },
{
    if raw.len() != if wide { 64usize } else { 32usize } { return None; }
    Some(Fields {
        block_bitmap: read_address(raw, 0, 32, wide).unwrap(),
        inode_bitmap: read_address(raw, 4, 36, wide).unwrap(),
        inode_table: read_address(raw, 8, 40, wide).unwrap(),
        free_blocks: read_counter(raw, 12, 44, wide).unwrap(),
        free_inodes: read_counter(raw, 14, 46, wide).unwrap(),
        directories: read_counter(raw, 16, 48, wide).unwrap(),
        unused: read_counter(raw, 28, 50, wide).unwrap(),
        block_checksum: read_counter(raw, 24, 56, wide).unwrap(),
        inode_checksum: read_counter(raw, 26, 58, wide).unwrap(),
    })
}

/// Full-width superblock counters are never silently reduced to their low
/// halves. The bounded image validator separately rejects larger geometry.
pub fn super_counts(raw: &[u8], wide: bool) -> (r: Option<(u64, u64, u64)>)
    ensures match r {
        Some((blocks, reserved, free)) => raw.len() == 1024
            && blocks as nat == address(raw@, 4, 336, wide)
            && reserved as nat == address(raw@, 8, 340, wide)
            && free as nat == address(raw@, 12, 344, wide),
        None => raw.len() != 1024,
    },
{
    if raw.len() != 1024 { return None; }
    Some((read_address(raw, 4, 336, wide).unwrap(), read_address(raw, 8, 340, wide).unwrap(),
        read_address(raw, 12, 344, wide).unwrap()))
}

pub proof fn a_nonzero_high_address_cannot_alias_its_low_half(raw: Seq<u8>, low: int, high: int)
    requires 0 <= low, low + 4 <= raw.len(), 0 <= high, high + 4 <= raw.len(), bytes::le32(raw, high) > 0,
    ensures address(raw, low, high, true) >= 4294967296,
        address(raw, low, high, true) != address(raw, low, high, false),
{
}

}
