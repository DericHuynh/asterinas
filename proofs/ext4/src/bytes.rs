// SPDX-License-Identifier: MPL-2.0

//! Total, allocation-free decoding. Offsets are checked by subtraction, so an
//! attacker-controlled usize cannot wrap before a bounds check.

use alloc::vec::Vec;

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

pub open spec fn encoded_be(v: u32) -> Seq<u8> {
    seq![(v / 16777216) as u8, ((v / 65536) % 256) as u8,
        ((v / 256) % 256) as u8, (v % 256) as u8]
}

pub open spec fn encoded_le(v: u32) -> Seq<u8> {
    seq![(v % 256) as u8, ((v / 256) % 256) as u8,
        ((v / 65536) % 256) as u8, (v / 16777216) as u8]
}

pub open spec fn splice(s: Seq<u8>, offset: int, data: Seq<u8>) -> Seq<u8> {
    s.subrange(0, offset) + data + s.subrange(offset + data.len(), s.len() as int)
}

pub proof fn splice_frame(s: Seq<u8>, offset: int, data: Seq<u8>, index: int)
    requires 0 <= offset, offset + data.len() <= s.len(), 0 <= index < s.len(),
        index < offset || index >= offset + data.len(),
    ensures splice(s, offset, data).len() == s.len(), splice(s, offset, data)[index] == s[index],
{
}

pub proof fn splice_word_frame(s: Seq<u8>, offset: int, data: Seq<u8>, word: int)
    requires 0 <= offset, offset + data.len() <= s.len(), 0 <= word, word + 4 <= s.len(),
        word + 4 <= offset || word >= offset + data.len(),
    ensures be32(splice(s, offset, data), word) == be32(s, word),
{
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

pub fn equal(s: &[u8], expected: &[u8]) -> (r: bool)
    ensures r == (s@ == expected@),
{
    if s.len() != expected.len() { return false; }
    let mut i = 0usize;
    while i < s.len()
        invariant i <= s.len(), s.len() == expected.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] s@[j] == expected@[j],
        decreases s.len() - i,
    {
        if s[i] != expected[i] { return false; }
        proof {
            assert forall|j: int| 0 <= j < i + 1 implies #[trigger] s@[j] == expected@[j] by {
                if j < i { assert(s@[j] == expected@[j]); }
            }
        }
        i += 1;
    }
    proof { assert(s@ =~= expected@); }
    true
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
        r@ == encoded_le(v),
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
        r@ == encoded_be(v),
        r@[0] == (v / 16777216) as u8, r@[1] == ((v / 65536) % 256) as u8,
        r@[2] == ((v / 256) % 256) as u8, r@[3] == (v % 256) as u8,
{
    let b = encode_le32(v);
    [b[3], b[2], b[1], b[0]]
}

pub proof fn little_endian_encoding_recovers_every_word(value: u32)
    ensures le32(encoded_le(value), 0) == value,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(value as int, 256);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(value as int / 256, 256);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(value as int / 65536, 256);
    vstd::arithmetic::div_mod::lemma_div_denominator(value as int, 256, 256);
    vstd::arithmetic::div_mod::lemma_div_denominator(value as int, 65536, 256);
}

/// Copies captured bytes only after validating the complete destination span.
pub fn write_bytes(s: &mut [u8], offset: usize, data: &[u8]) -> (r: bool)
    ensures final(s).len() == old(s).len(),
        r == (offset as int + data.len() <= old(s).len()),
        final(s)@ == if r { splice(old(s)@, offset as int, data@) } else { old(s)@ },
{
    if offset > s.len() || data.len() > s.len() - offset { return false; }
    let ghost before = s@;
    let mut i = 0usize;
    while i < data.len()
        invariant i <= data.len(), offset as int + data.len() <= s.len(),
            s.len() == before.len(),
            s@ == splice(before, offset as int, data@.subrange(0, i as int)),
        decreases data.len() - i,
    {
        s[offset + i] = data[i];
        proof { assert(s@ =~= splice(before, offset as int, data@.subrange(0, i as int + 1))); }
        i += 1;
    }
    proof { assert(data@.subrange(0, data.len() as int) =~= data@); }
    true
}

pub fn write_be32(s: &mut [u8], offset: usize, value: u32) -> (r: bool)
    ensures final(s).len() == old(s).len(),
        r == (offset as int + 4 <= old(s).len()),
        final(s)@ == if r { splice(old(s)@, offset as int, encoded_be(value)) } else { old(s)@ },
        r ==> be32(final(s)@, offset as int) == value as nat,
{
    let encoded = encode_be32(value);
    write_bytes(s, offset, &encoded)
}

pub fn write_le32(s: &mut [u8], offset: usize, value: u32) -> (r: bool)
    ensures final(s).len() == old(s).len(),
        r == (offset as int + 4 <= old(s).len()),
        final(s)@ == if r { splice(old(s)@, offset as int, encoded_le(value)) } else { old(s)@ },
        r ==> le32(final(s)@, offset as int) == value as nat,
{
    let encoded = encode_le32(value);
    write_bytes(s, offset, &encoded)
}

pub fn zero_block() -> (r: Vec<u8>)
    ensures r@ == Seq::<u8>::new(4096, |i: int| 0u8),
{
    let mut r = Vec::new();
    let mut i = 0usize;
    while i < 4096
        invariant i <= 4096, r.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] r@[j] == 0,
        decreases 4096 - i,
    {
        r.push(0u8);
        i += 1;
    }
    proof { assert(r@ =~= Seq::<u8>::new(4096, |i: int| 0u8)); }
    r
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
