// SPDX-License-Identifier: MPL-2.0

//! Owned, initialized 4 KiB snapshots. No Clone or mutable borrow is exposed.
//! CortenMM frame/DMA loans must refine this ownership before kernel use.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::bytes::*;

verus! {

pub struct FrozenBlock { bytes: Vec<u8> }

impl FrozenBlock {
    pub closed spec fn view(&self) -> Seq<u8> { self.bytes@ }

    pub fn from_vec(bytes: Vec<u8>) -> (r: Option<Self>)
        ensures match r {
            Some(b) => bytes.len() == 4096 && b.view() == bytes@,
            None => bytes.len() != 4096,
        },
    {
        if bytes.len() != 4096 { None } else { Some(FrozenBlock { bytes }) }
    }

    pub fn capture(s: &[u8]) -> (r: Option<Self>)
        ensures match r {
            Some(b) => s.len() == 4096 && b.view() == s@,
            None => s.len() != 4096,
        },
    {
        if s.len() != 4096 { return None; }
        let mut bytes = Vec::new();
        let mut i = 0usize;
        while i < 4096
            invariant s.len() == 4096, i <= 4096,
                bytes@ == s@.subrange(0, i as int),
            decreases 4096 - i,
        {
            bytes.push(s[i]);
            proof { assert(bytes@ =~= s@.subrange(0, i as int + 1)); }
            i += 1;
        }
        proof { assert(s@.subrange(0, 4096) =~= s@); }
        Some(FrozenBlock { bytes })
    }

    pub fn as_slice(&self) -> (r: &[u8]) ensures r@ == self.view() {
        self.bytes.as_slice()
    }

    /// This transformation never exposes a mutable reference to the original
    /// snapshot. The returned flag is the tag's JBD2_FLAG_ESCAPE bit.
    pub fn escape(&self) -> (r: Option<(Self, bool)>)
        ensures match r {
            Some((b, flag)) => self.view().len() == 4096
                && flag == (be32(self.view(), 0) == 0xc03b3998)
                && b.view().len() == 4096
                && b.view() == if flag {
                    seq![0u8, 0u8, 0u8, 0u8] + self.view().subrange(4, 4096)
                } else { self.view() },
            None => self.view().len() != 4096,
        },
    {
        let s = self.bytes.as_slice();
        if s.len() != 4096 { return None; }
        let flag = crate::bytes::read_be32(s, 0).unwrap() == 0xc03b3998;
        let mut bytes = Vec::new();
        let mut i = 0usize;
        let ghost expected = if flag {
            seq![0u8, 0u8, 0u8, 0u8] + self.view().subrange(4, 4096)
        } else { self.view() };
        while i < 4096
            invariant i <= 4096, s.len() == 4096, s@ == self.view(),
                expected.len() == 4096,
                expected == if flag {
                    seq![0u8, 0u8, 0u8, 0u8] + self.view().subrange(4, 4096)
                } else { self.view() },
                bytes@ == expected.subrange(0, i as int),
            decreases 4096 - i,
        {
            bytes.push(if flag && i < 4 { 0 } else { s[i] });
            proof { assert(bytes@ =~= expected.subrange(0, i as int + 1)); }
            i += 1;
        }
        proof { assert(expected.subrange(0, 4096) =~= expected); }
        Some((FrozenBlock { bytes }, flag))
    }

    pub fn restore(&self, escaped: bool) -> (r: Option<Self>)
        ensures match r {
            Some(b) => self.view().len() == 4096 && b.view().len() == 4096
                && b.view() == if escaped {
                    seq![0xc0u8, 0x3bu8, 0x39u8, 0x98u8] + self.view().subrange(4, 4096)
                } else { self.view() },
            None => self.view().len() != 4096,
        },
    {
        let s = self.bytes.as_slice();
        if s.len() != 4096 { return None; }
        let magic = [0xc0u8, 0x3bu8, 0x39u8, 0x98u8];
        let ghost expected = if escaped { magic@ + self.view().subrange(4, 4096) }
            else { self.view() };
        let mut bytes = Vec::new();
        let mut i = 0usize;
        while i < 4096
            invariant i <= 4096, s.len() == 4096, s@ == self.view(),
                magic@ == seq![0xc0u8, 0x3bu8, 0x39u8, 0x98u8],
                expected.len() == 4096,
                expected == if escaped { magic@ + self.view().subrange(4, 4096) }
                    else { self.view() },
                bytes@ == expected.subrange(0, i as int),
            decreases 4096 - i,
        {
            bytes.push(if escaped && i < 4 { magic[i] } else { s[i] });
            proof { assert(bytes@ =~= expected.subrange(0, i as int + 1)); }
            i += 1;
        }
        proof { assert(expected.subrange(0, 4096) =~= expected); }
        Some(FrozenBlock { bytes })
    }
}

pub proof fn escape_restore_roundtrip(original: Seq<u8>)
    requires original.len() == 4096, be32(original, 0) == 0xc03b3998,
    ensures seq![0xc0u8, 0x3bu8, 0x39u8, 0x98u8] + original.subrange(4, 4096) == original,
{
    assert(original[0] == 0xc0 && original[1] == 0x3b
        && original[2] == 0x39 && original[3] == 0x98);
    assert(seq![0xc0u8, 0x3bu8, 0x39u8, 0x98u8] + original.subrange(4, 4096) =~= original);
}

}
