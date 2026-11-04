// SPDX-License-Identifier: MPL-2.0

//! Reflected Castagnoli CRC, with Linux's raw accumulator convention (no
//! implicit initial or final complement). This is error detection, not a MAC.

use vstd::prelude::*;

verus! {

pub open spec fn bit(c: u32) -> u32 {
    if c & 1 == 1 { (c >> 1) ^ 0x82f63b78u32 } else { c >> 1 }
}

pub open spec fn steps(c: u32, n: nat) -> u32
    decreases n,
{
    if n == 0 { c } else { bit(steps(c, (n - 1) as nat)) }
}

pub open spec fn byte(c: u32, b: u8) -> u32 { steps(c ^ b as u32, 8) }

pub open spec fn fold(c: u32, s: Seq<u8>) -> u32
    decreases s.len(),
{
    if s.len() == 0 { c } else { byte(fold(c, s.drop_last()), s.last()) }
}

pub fn update_byte(seed: u32, b: u8) -> (r: u32)
    ensures r == byte(seed, b),
{
    let mut c = seed ^ b as u32;
    let mut i = 0usize;
    while i < 8
        invariant i <= 8, c == steps(seed ^ b as u32, i as nat),
        decreases 8 - i,
    {
        c = if c & 1 == 1 { (c >> 1) ^ 0x82f63b78u32 } else { c >> 1 };
        i += 1;
    }
    c
}

pub fn crc32c(seed: u32, s: &[u8]) -> (r: u32)
    ensures r == fold(seed, s@),
{
    let mut c = seed;
    let mut i = 0usize;
    while i < s.len()
        invariant i <= s.len(), c == fold(seed, s@.subrange(0, i as int)),
        decreases s.len() - i,
    {
        c = update_byte(c, s[i]);
        proof {
            assert(s@.subrange(0, i as int + 1).drop_last()
                =~= s@.subrange(0, i as int));
            assert(s@.subrange(0, i as int + 1).last() == s@[i as int]);
        }
        i += 1;
    }
    proof { assert(s@.subrange(0, s.len() as int) =~= s@); }
    c
}

pub proof fn streaming(seed: u32, a: Seq<u8>, b: Seq<u8>)
    ensures fold(fold(seed, a), b) == fold(seed, a + b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        streaming(seed, a, b.drop_last());
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

pub open spec fn zero4(s: Seq<u8>, offset: int) -> Seq<u8> {
    s.subrange(0, offset) + seq![0u8, 0u8, 0u8, 0u8]
        + s.subrange(offset + 4, s.len() as int)
}

pub proof fn zero4_restores_written_checksum(s: Seq<u8>, offset: int, value: u32)
    requires 0 <= offset, offset + 4 <= s.len(),
        s.subrange(offset, offset + 4) == seq![0u8, 0u8, 0u8, 0u8],
    ensures zero4(crate::bytes::splice(s, offset, crate::bytes::encoded_be(value)), offset) == s,
{
    assert(zero4(crate::bytes::splice(s, offset, crate::bytes::encoded_be(value)), offset) =~= s);
}

pub fn crc32c_zero4(seed: u32, s: &[u8], offset: usize) -> (r: Option<u32>)
    ensures match r {
        Some(c) => offset as int + 4 <= s.len() && c == fold(seed, zero4(s@, offset as int)),
        None => offset as int + 4 > s.len(),
    },
{
    if offset > s.len() || s.len() - offset < 4 { return None; }
    let a = crc32c(seed, &s[0..offset]);
    let zeros = [0u8, 0u8, 0u8, 0u8];
    let b = crc32c(a, &zeros);
    let c = crc32c(b, &s[offset + 4..]);
    proof {
        streaming(seed, s@.subrange(0, offset as int), zeros@);
        streaming(seed, s@.subrange(0, offset as int) + zeros@,
            s@.subrange(offset as int + 4, s.len() as int));
    }
    Some(c)
}

}
