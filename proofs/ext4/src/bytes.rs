// SPDX-License-Identifier: MPL-2.0

//! Total, allocation-free decoding. Offsets are checked by subtraction, so an
//! attacker-controlled usize cannot wrap before a bounds check.

use vstd::prelude::*;

verus! {

pub open spec fn le16(s: Seq<u8>, o: int) -> nat {
    s[o] as nat + 256 * s[o + 1] as nat
}

pub open spec fn le32(s: Seq<u8>, o: int) -> nat {
    s[o] as nat + 256 * s[o + 1] as nat
        + 65536 * s[o + 2] as nat + 16777216 * s[o + 3] as nat
}

pub open spec fn be32(s: Seq<u8>, o: int) -> nat {
    16777216 * s[o] as nat + 65536 * s[o + 1] as nat
        + 256 * s[o + 2] as nat + s[o + 3] as nat
}

pub fn read_le16(s: &[u8], o: usize) -> (r: Option<u16>)
    ensures match r {
        Some(v) => o as int + 2 <= s.len() && v as nat == le16(s@, o as int),
        None => o as int + 2 > s.len(),
    },
{
    if o > s.len() || s.len() - o < 2 { return None; }
    Some((s[o] as u16) + 256 * (s[o + 1] as u16))
}

pub fn read_le32(s: &[u8], o: usize) -> (r: Option<u32>)
    ensures match r {
        Some(v) => o as int + 4 <= s.len() && v as nat == le32(s@, o as int),
        None => o as int + 4 > s.len(),
    },
{
    if o > s.len() || s.len() - o < 4 { return None; }
    Some((s[o] as u32) + 256 * (s[o + 1] as u32)
        + 65536 * (s[o + 2] as u32) + 16777216 * (s[o + 3] as u32))
}

pub fn read_be32(s: &[u8], o: usize) -> (r: Option<u32>)
    ensures match r {
        Some(v) => o as int + 4 <= s.len() && v as nat == be32(s@, o as int),
        None => o as int + 4 > s.len(),
    },
{
    if o > s.len() || s.len() - o < 4 { return None; }
    Some(16777216 * (s[o] as u32) + 65536 * (s[o + 1] as u32)
        + 256 * (s[o + 2] as u32) + (s[o + 3] as u32))
}

pub fn encode_le16(v: u16) -> (r: [u8; 2])
    ensures le16(r@, 0) == v as nat,
{
    let a = (v % 256) as u8;
    let b = (v / 256) as u8;
    assert(v as int == (v as int % 256) + 256 * (v as int / 256)) by (nonlinear_arith);
    [a, b]
}

pub fn encode_le32(v: u32) -> (r: [u8; 4])
    ensures le32(r@, 0) == v as nat,
        r@[0] == (v % 256) as u8, r@[1] == ((v / 256) % 256) as u8,
        r@[2] == ((v / 65536) % 256) as u8, r@[3] == (v / 16777216) as u8,
{
    let a = (v % 256) as u8;
    let b = ((v / 256) % 256) as u8;
    let c = ((v / 65536) % 256) as u8;
    let d = (v / 16777216) as u8;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(v as int, 256);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(v as int / 256, 256);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(v as int / 65536, 256);
        vstd::arithmetic::div_mod::lemma_div_denominator(v as int, 256, 256);
        vstd::arithmetic::div_mod::lemma_div_denominator(v as int, 65536, 256);
    }
    [a, b, c, d]
}

pub fn encode_be32(v: u32) -> (r: [u8; 4])
    ensures be32(r@, 0) == v as nat,
        r@[0] == (v / 16777216) as u8, r@[1] == ((v / 65536) % 256) as u8,
        r@[2] == ((v / 256) % 256) as u8, r@[3] == (v % 256) as u8,
{
    let b = encode_le32(v);
    [b[3], b[2], b[1], b[0]]
}

/// Inclusive start, exclusive end, in bytes. None has no side effects.
pub fn checked_range(start: u64, count: u64, limit: u64) -> (r: Option<u64>)
    ensures match r {
        Some(end) => start as int + count <= limit && end as int == start as int + count,
        None => start as int + count > limit,
    },
{
    if start > limit || count > limit - start { None } else { Some(start + count) }
}

/// A filesystem block is always confined to the selected partition. This
/// returns an offset relative to it; no physical-device base is added here.
pub fn block_offset(block: u32, blocks: u32, partition_bytes: u64) -> (r: Option<u64>)
    ensures match r {
        Some(offset) => block < blocks && offset as nat == block as nat * 4096
            && offset as int + 4096 <= partition_bytes,
        None => block >= blocks || block as int * 4096 + 4096 > partition_bytes,
    },
{
    if block >= blocks { return None; }
    let offset = (block as u64) * 4096;
    if partition_bytes < 4096 || offset > partition_bytes - 4096 { None }
    else { Some(offset) }
}

}
