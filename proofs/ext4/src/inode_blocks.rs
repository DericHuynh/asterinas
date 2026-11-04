// SPDX-License-Identifier: MPL-2.0

//! Linux ext4_inode_blocks/ext4_inode_blocks_set accounting. Encoders retain
//! exact normalized sectors; a nonaligned huge-unit value is rejected rather
//! than losing sectors. Feature inputs alone confer no filesystem authority.

use vstd::prelude::*;
use crate::{block_size, bytes};

verus! {

pub const HUGE_FLAG: u32 = 0x40000;
pub const FIELD_LIMIT: u64 = 281474976710656;

pub open spec fn raw_count(raw: Seq<u8>, huge_file: bool) -> nat {
    bytes::le32(raw, 28) + if huge_file { 4294967296 * bytes::le16(raw, 116) } else { 0nat }
}

pub open spec fn sectors(raw: Seq<u8>, block_bytes: u32, huge_file: bool) -> nat {
    raw_count(raw, huge_file) * if huge_file && bytes::le32(raw, 32) as u32 & HUGE_FLAG != 0 { block_bytes as nat / 512 } else { 1nat }
}

pub open spec fn representable(count: u64, block_bytes: u32, huge_file: bool) -> bool {
    &&& block_size::accepted(block_bytes as nat)
    &&& count <= 4294967295 || huge_file && (count < FIELD_LIMIT
        || count as nat % (block_bytes as nat / 512) == 0 && count as nat / (block_bytes as nat / 512) < FIELD_LIMIT)
}

pub fn decode(raw: &[u8], block_bytes: u32, huge_file: bool) -> (r: Option<u64>)
    ensures match r {
        Some(count) => raw.len() >= 118 && block_size::accepted(block_bytes as nat) && count as nat == sectors(raw@, block_bytes, huge_file),
        None => raw.len() < 118 || !block_size::accepted(block_bytes as nat),
    },
{
    if raw.len() < 118 || !block_size::valid(block_bytes as usize) { return None; }
    let low = bytes::read_le32(raw, 28).unwrap() as u64;
    if !huge_file { return Some(low); }
    let count = low + bytes::read_le16(raw, 116).unwrap() as u64 * 4294967296;
    let factor = if bytes::read_le32(raw, 32).unwrap() & HUGE_FLAG != 0 { block_bytes as u64 / 512 } else { 1u64 };
    assert(count as nat * factor <= 36028797018963840) by (nonlinear_arith)
        requires count < FIELD_LIMIT, factor <= 128;
    Some(count * factor)
}

pub struct Encoded { pub low: [u8; 4], pub high: [u8; 2], pub huge: bool }

pub open spec fn encoded_sectors(e: Encoded, block_bytes: u32) -> nat {
    (bytes::le32(e.low@, 0) + 4294967296 * bytes::le16(e.high@, 0))
        * if e.huge { block_bytes as nat / 512 } else { 1nat }
}

fn fields(count: u64, huge: bool) -> (r: Encoded)
    requires count < FIELD_LIMIT,
    ensures r.huge == huge, bytes::le32(r.low@, 0) + 4294967296 * bytes::le16(r.high@, 0) == count,
{
    let low = bytes::encode_le32((count % 4294967296) as u32);
    let high = bytes::encode_le16((count / 4294967296) as u16);
    proof { vstd::arithmetic::div_mod::lemma_fundamental_div_mod(count as int, 4294967296); }
    Encoded { low, high, huge }
}

pub fn encode(count: u64, block_bytes: u32, huge_file: bool) -> (r: Option<Encoded>)
    ensures match r {
        Some(e) => representable(count, block_bytes, huge_file) && encoded_sectors(e, block_bytes) == count
            && (e.huge ==> huge_file && count >= FIELD_LIMIT)
            && (count <= 4294967295 ==> bytes::le16(e.high@, 0) == 0 && !e.huge),
        None => !representable(count, block_bytes, huge_file),
    },
{
    if !block_size::valid(block_bytes as usize) { return None; }
    if count <= 4294967295 { return Some(fields(count, false)); }
    if !huge_file { return None; }
    if count < FIELD_LIMIT { return Some(fields(count, false)); }
    let factor = block_bytes as u64 / 512;
    if count % factor != 0 || count / factor >= FIELD_LIMIT { return None; }
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(count as int, factor as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(count as int / factor as int, factor as int);
    }
    Some(fields(count / factor, true))
}

}
