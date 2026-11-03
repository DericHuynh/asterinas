// SPDX-License-Identifier: MPL-2.0

//! Initialized ext4 allocation bitmaps for the 4 KiB, 32-byte-descriptor
//! metadata-checksum profile. Parsing is not an allocation capability.

use vstd::prelude::*;
use crate::{crc, frozen::FrozenBlock};

verus! {

pub open spec fn set(raw: Seq<u8>, index: int) -> bool {
    0 <= index < raw.len() * 8 && ((raw[index / 8] >> ((index % 8) as u8)) & 1u8) == 1u8
}

#[verifier::opaque]
pub open spec fn free_bits(raw: Seq<u8>, count: nat) -> nat
    decreases count,
{
    if count == 0 { 0nat }
    else { free_bits(raw, (count - 1) as nat) + if set(raw, count as int - 1) { 0nat } else { 1nat } }
}

pub open spec fn accepted(raw: Seq<u8>, valid: u32, meaningful: u32, free: u32, checksum: u16, seed: u32) -> bool {
    &&& raw.len() == 4096 && valid <= meaningful && 0 < meaningful <= 32768 && meaningful % 8 == 0 && free <= valid
    &&& free_bits(raw, valid as nat) == free as nat
    &&& (forall|i: int| valid <= i < 32768 ==> #[trigger] set(raw, i))
    &&& (crc::fold(seed, raw.take(meaningful as int / 8)) & 0xffffu32) == checksum as u32
}

pub fn read_bit(raw: &[u8], index: u32) -> (r: Option<bool>)
    ensures match r {
        Some(value) => (index as nat) < raw.len() as nat * 8 && value == set(raw@, index as int),
        None => index as nat >= raw.len() as nat * 8,
    },
{
    let byte = (index / 8) as usize;
    if byte >= raw.len() { return None; }
    Some(((raw[byte] >> ((index % 8) as u8)) & 1u8) == 1u8)
}

pub struct BitmapView {
    pub raw: Seq<u8>, pub valid: u32, pub meaningful: u32, pub free: u32, pub checksum: u16, pub seed: u32,
}

pub struct Bitmap { raw: FrozenBlock, valid: u32, meaningful: u32, free: u32, checksum: u16, seed: u32 }

impl Bitmap {
    pub closed spec fn view(&self) -> BitmapView {
        BitmapView { raw: self.raw.view(), valid: self.valid, meaningful: self.meaningful,
            free: self.free, checksum: self.checksum, seed: self.seed }
    }

    #[verifier::type_invariant]
    spec fn well_formed(self) -> bool {
        accepted(self.view().raw, self.view().valid, self.view().meaningful, self.view().free, self.view().checksum, self.view().seed)
    }

    pub fn is_set(&self, index: u32) -> (r: Option<bool>)
        ensures match r {
            Some(value) => index < self.view().valid && value == set(self.view().raw, index as int),
            None => index >= self.view().valid,
        },
    {
        proof { use_type_invariant(self); }
        if index >= self.valid { return None; }
        read_bit(self.raw.as_slice(), index)
    }

    pub fn free_count(&self) -> (r: u32)
        ensures r == self.view().free && r <= 32768 && r as nat == free_bits(self.view().raw, self.view().valid as nat),
    {
        proof { use_type_invariant(self); }
        self.free
    }

    pub fn entry_count(&self) -> (r: u32)
        ensures r == self.view().valid && r <= 32768,
            accepted(self.view().raw, self.view().valid, self.view().meaningful, self.view().free, self.view().checksum, self.view().seed),
    {
        proof { use_type_invariant(self); }
        self.valid
    }

    pub fn raw_image(&self) -> (r: &[u8]) ensures r@ == self.view().raw { self.raw.as_slice() }
}

pub fn parse(raw: &[u8], valid: u32, meaningful: u32, free: u32, checksum: u16, seed: u32) -> (r: Option<Bitmap>)
    ensures match r {
        Some(bitmap) => accepted(raw@, valid, meaningful, free, checksum, seed)
            && bitmap.view() == (BitmapView { raw: raw@, valid, meaningful, free, checksum, seed }),
        None => !accepted(raw@, valid, meaningful, free, checksum, seed),
    },
{
    hide(crc::fold);
    if raw.len() != 4096 || valid > meaningful || meaningful == 0 || meaningful > 32768 || meaningful % 8 != 0 || free > valid { return None; }
    let length = (meaningful / 8) as usize;
    if (crc::crc32c(seed, &raw[..length]) & 0xffffu32) != checksum as u32 { return None; }
    let mut count = 0u32;
    let mut index = 0u32;
    assert(free_bits(raw@, 0) == 0) by { reveal(free_bits); }
    while index < 32768
        invariant index <= 32768, raw.len() == 4096, valid <= meaningful, 0 < meaningful <= 32768,
            count <= index, count as nat == free_bits(raw@, if index < valid { index as nat } else { valid as nat }),
            forall|i: int| valid <= i < index ==> #[trigger] set(raw@, i),
        decreases 32768 - index,
    {
        let value = read_bit(raw, index).unwrap();
        if index < valid {
            if !value { count += 1; }
            assert(count as nat == free_bits(raw@, index as nat + 1)) by { reveal(free_bits); }
        } else if !value {
            assert(!accepted(raw@, valid, meaningful, free, checksum, seed)) by {
                assert(!set(raw@, index as int));
            }
            return None;
        }
        index += 1;
    }
    if count != free { return None; }
    let image = FrozenBlock::capture(raw).unwrap();
    Some(Bitmap { raw: image, valid, meaningful, free, checksum, seed })
}

}
