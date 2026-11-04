// SPDX-License-Identifier: MPL-2.0

//! Linux ext4_isize and ext4_max_size field/limit rules. Feature inputs to
//! these standalone codecs are descriptions; inode admission must derive
//! them from its checked volume. i_blocks units are a separate protocol.

use vstd::prelude::*;
use crate::{block_size, bytes, extent};

verus! {

pub open spec fn value(raw: Seq<u8>, large_dir: bool) -> nat {
    bytes::le32(raw, 4) + if large_dir || bytes::le16(raw, 0) as u16 & 0xf000 == 0x8000 {
        4294967296 * bytes::le32(raw, 108)
    } else { 0nat }
}

pub open spec fn linux_max(block_bytes: u32, huge_file: bool) -> nat {
    let extent_limit = extent::MAX_LOGICAL_END as nat * block_bytes as nat;
    if huge_file { extent_limit } else if block_bytes < 512 { 0nat } else {
        let sector_limit = 4294967295nat / (block_bytes as nat / 512) * block_bytes as nat;
        if extent_limit < sector_limit { extent_limit } else { sector_limit }
    }
}

pub open spec fn accepted(raw: Seq<u8>, block_bytes: u32, huge_file: bool, large_dir: bool) -> bool {
    raw.len() >= 112 && block_size::accepted(block_bytes as nat) && value(raw, large_dir) <= linux_max(block_bytes, huge_file)
}

pub fn limit(block_bytes: u32, huge_file: bool) -> (r: Option<u64>)
    ensures match r {
        Some(limit) => block_size::accepted(block_bytes as nat) && limit as nat == linux_max(block_bytes, huge_file),
        None => !block_size::accepted(block_bytes as nat),
    },
{
    if !block_size::valid(block_bytes as usize) { return None; }
    let extent_limit = extent::MAX_LOGICAL_END * block_bytes as u64;
    if huge_file { return Some(extent_limit); }
    let sector_limit = (4294967295u64 / (block_bytes as u64 / 512)) * block_bytes as u64;
    Some(if extent_limit < sector_limit { extent_limit } else { sector_limit })
}

pub fn decode(raw: &[u8], block_bytes: u32, huge_file: bool, large_dir: bool) -> (r: Option<u64>)
    ensures match r {
        Some(size) => accepted(raw@, block_bytes, huge_file, large_dir) && size as nat == value(raw@, large_dir),
        None => !accepted(raw@, block_bytes, huge_file, large_dir),
    },
{
    if raw.len() < 112 { return None; }
    let maximum = match limit(block_bytes, huge_file) { Some(maximum) => maximum, None => { return None; } };
    let mode = bytes::read_le16(raw, 0).unwrap();
    let low = bytes::read_le32(raw, 4).unwrap() as u64;
    let size = if large_dir || mode & 0xf000 == 0x8000 {
        low + bytes::read_le32(raw, 108).unwrap() as u64 * 4294967296
    } else { low };
    if size > maximum { return None; }
    Some(size)
}

pub fn encode(size: u64, block_bytes: u32, huge_file: bool) -> (r: Option<([u8; 4], [u8; 4])>)
    ensures match r {
        Some((low, high)) => block_size::accepted(block_bytes as nat) && size <= linux_max(block_bytes, huge_file)
            && bytes::le32(low@, 0) + 4294967296 * bytes::le32(high@, 0) == size,
        None => !block_size::accepted(block_bytes as nat) || size > linux_max(block_bytes, huge_file),
    },
{
    let maximum = match limit(block_bytes, huge_file) { Some(maximum) => maximum, None => { return None; } };
    if size > maximum { return None; }
    let low = bytes::encode_le32((size % 4294967296) as u32);
    let high = bytes::encode_le32((size / 4294967296) as u32);
    proof { vstd::arithmetic::div_mod::lemma_fundamental_div_mod(size as int, 4294967296); }
    Some((low, high))
}

pub proof fn offsets_never_truncate_to_a_different_logical_block(block_bytes: u32, huge_file: bool, size: u64, offset: u64)
    requires block_size::accepted(block_bytes as nat), size <= linux_max(block_bytes, huge_file), offset < size,
    ensures (offset as nat / block_bytes as nat) < extent::MAX_LOGICAL_END,
        (((offset as nat / block_bytes as nat) as u32) as nat) == (offset as nat / block_bytes as nat),
{
    assert(offset < extent::MAX_LOGICAL_END as nat * block_bytes as nat);
    vstd::arithmetic::mul::lemma_mul_is_commutative(extent::MAX_LOGICAL_END as int, block_bytes as int);
    vstd::arithmetic::div_mod::lemma_multiply_divide_lt(offset as int, block_bytes as int, extent::MAX_LOGICAL_END as int);
}

}
