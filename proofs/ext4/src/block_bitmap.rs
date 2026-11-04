// SPDX-License-Identifier: MPL-2.0

//! Logical BLOCK_UNINIT bitmaps for bounded source-selected group placement.
//! META_BG and reserved GDT growth remain outside the supported layout.
//! Set real bits name reserved metadata; padding is allocated. This describes
//! allocation state, not a CortenMM frame or filesystem mutation capability.

use vstd::prelude::*;
use crate::{bitmap::{self, Bitmap}, block_claims, bytes, crc, group, group_claims};

verus! {

pub struct Layout {
    pub number: u32, pub blocks: u32, pub block_bitmap: u32, pub inode_bitmap: u32,
    pub inode_table: u32, pub table_blocks: u32, pub backup: bool,
}

pub open spec fn context(raw: Seq<u8>, number: u32, blocks: u32, ipg: u32) -> Layout {
context_with_backup(raw, number, blocks, ipg, group_claims::sparse_super(number))
}

pub open spec fn context_with_backup(raw: Seq<u8>, number: u32, blocks: u32, ipg: u32, backup: bool) -> Layout {
    Layout { number, blocks, block_bitmap: bytes::le32(raw, 0) as u32, inode_bitmap: bytes::le32(raw, 4) as u32,
        inode_table: bytes::le32(raw, 8) as u32, table_blocks: (ipg / 16) as u32, backup }
}

pub open spec fn valid(l: Layout) -> bool {
    l.number < 32 && l.number as nat * 32768 < l.blocks && l.blocks <= block_claims::MAX_BLOCKS
}

pub open spec fn real_bits(l: Layout) -> nat { (group::end(l.blocks, l.number) - l.number as nat * 32768) as nat }

pub open spec fn reserved(l: Layout, index: nat) -> bool {
    let physical = l.number as nat * 32768 + index;
    index >= real_bits(l) || l.backup && index < 2 || physical == l.block_bitmap || physical == l.inode_bitmap
        || l.inode_table <= physical < l.inode_table as nat + l.table_blocks as nat
}

pub open spec fn packed(a: bool, b: bool, c: bool, d: bool, e: bool, f: bool, g: bool, h: bool) -> u8 {
    (if a { 1u8 } else { 0u8 }) | (if b { 2u8 } else { 0u8 }) | (if c { 4u8 } else { 0u8 })
        | (if d { 8u8 } else { 0u8 }) | (if e { 16u8 } else { 0u8 }) | (if f { 32u8 } else { 0u8 })
        | (if g { 64u8 } else { 0u8 }) | (if h { 128u8 } else { 0u8 })
}

pub open spec fn byte(l: Layout, index: nat) -> u8 {
    packed(reserved(l, index * 8), reserved(l, index * 8 + 1), reserved(l, index * 8 + 2), reserved(l, index * 8 + 3),
        reserved(l, index * 8 + 4), reserved(l, index * 8 + 5), reserved(l, index * 8 + 6), reserved(l, index * 8 + 7))
}

#[verifier::opaque]
pub open spec fn canonical(l: Layout) -> Seq<u8> { Seq::new(4096, |i: int| byte(l, i as nat)) }

proof fn packed_bit(a: bool, b: bool, c: bool, d: bool, e: bool, f: bool, g: bool, h: bool, index: u8)
    requires index < 8,
    ensures ((packed(a, b, c, d, e, f, g, h) >> index) & 1u8 == 1u8)
        == if index == 0 { a } else if index == 1 { b } else if index == 2 { c } else if index == 3 { d }
            else if index == 4 { e } else if index == 5 { f } else if index == 6 { g } else { h },
{
    assert(((((if a { 1u8 } else { 0u8 }) | (if b { 2u8 } else { 0u8 }) | (if c { 4u8 } else { 0u8 }) | (if d { 8u8 } else { 0u8 }) | (if e { 16u8 } else { 0u8 }) | (if f { 32u8 } else { 0u8 }) | (if g { 64u8 } else { 0u8 }) | (if h { 128u8 } else { 0u8 })) >> index) & 1u8 == 1u8) == (if index == 0 { a } else if index == 1 { b } else if index == 2 { c } else if index == 3 { d } else if index == 4 { e } else if index == 5 { f } else if index == 6 { g } else { h })) by (bit_vector) requires index < 8;
}

pub proof fn every_canonical_bit_has_the_exact_reserved_or_padding_meaning(l: Layout, index: u32)
    requires valid(l), index < 32768,
    ensures canonical(l).len() == 4096, bitmap::set(canonical(l), index as int) == reserved(l, index as nat),
{
    reveal(canonical);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(index as int, 8);
    let base = index as nat / 8 * 8;
    let shift = (index % 8) as u8;
    assert(base + shift as nat == index as nat);
    assert(canonical(l)[index as int / 8] == packed(reserved(l, base), reserved(l, base + 1),
        reserved(l, base + 2), reserved(l, base + 3), reserved(l, base + 4), reserved(l, base + 5),
        reserved(l, base + 6), reserved(l, base + 7)));
    packed_bit(reserved(l, base), reserved(l, base + 1), reserved(l, base + 2), reserved(l, base + 3),
        reserved(l, base + 4), reserved(l, base + 5), reserved(l, base + 6), reserved(l, base + 7), shift);
    if shift == 0 { assert(base == index as nat); }
    else if shift == 1 { assert(base + 1 == index as nat); }
    else if shift == 2 { assert(base + 2 == index as nat); }
    else if shift == 3 { assert(base + 3 == index as nat); }
    else if shift == 4 { assert(base + 4 == index as nat); }
    else if shift == 5 { assert(base + 5 == index as nat); }
    else if shift == 6 { assert(base + 6 == index as nat); }
    else { assert(base + 7 == index as nat); }

}

fn is_reserved(l: &Layout, index: u32) -> (r: bool)
    requires valid(*l), index < 32768,
    ensures r == reserved(*l, index as nat),
{
    let first = l.number as u64 * 32768;
    let available = l.blocks as u64 - first;
    let valid = if available < 32768 { available } else { 32768 };
    let physical = first + index as u64;
    index as u64 >= valid || (l.backup && index < 2) || physical == l.block_bitmap as u64
        || physical == l.inode_bitmap as u64
        || (l.inode_table as u64 <= physical && physical < l.inode_table as u64 + l.table_blocks as u64)
}

fn make_byte(l: &Layout, index: u32) -> (r: u8)
    requires valid(*l), index < 4096,
    ensures r == byte(*l, index as nat),
{
    let base = index * 8;
    let a = is_reserved(l, base);
    let b = is_reserved(l, base + 1);
    let c = is_reserved(l, base + 2);
    let d = is_reserved(l, base + 3);
    let e = is_reserved(l, base + 4);
    let f = is_reserved(l, base + 5);
    let g = is_reserved(l, base + 6);
    let h = is_reserved(l, base + 7);
    (if a { 1u8 } else { 0u8 }) | (if b { 2u8 } else { 0u8 }) | (if c { 4u8 } else { 0u8 })
        | (if d { 8u8 } else { 0u8 }) | (if e { 16u8 } else { 0u8 }) | (if f { 32u8 } else { 0u8 })
        | (if g { 64u8 } else { 0u8 }) | (if h { 128u8 } else { 0u8 })
}

#[verifier::opaque]
pub open spec fn admitted(raw: Seq<u8>, number: u32, blocks: u32, ipg: u32, seed: u32) -> bool {
    admitted_with_features(raw, number, blocks, ipg, seed, false)
}

#[verifier::opaque]
pub open spec fn admitted_with_features(raw: Seq<u8>, number: u32, blocks: u32, ipg: u32, seed: u32, flex: bool) -> bool {
    admitted_with_backup(raw, number, blocks, ipg, seed, flex, group_claims::sparse_super(number))
}

#[verifier::opaque]
pub open spec fn admitted_with_backup(raw: Seq<u8>, number: u32, blocks: u32, ipg: u32, seed: u32, flex: bool, backup: bool) -> bool {
    &&& number < 32 && blocks <= block_claims::MAX_BLOCKS
    &&& group::accepted_with_features(raw, number, blocks, ipg, seed, flex)
    &&& bitmap::free_bits(canonical(context_with_backup(raw, number, blocks, ipg, backup)), real_bits(context_with_backup(raw, number, blocks, ipg, backup)))
        == bytes::le16(raw, 12)
}

pub fn synthesize(raw: &[u8], number: u32, blocks: u32, ipg: u32, seed: u32) -> (r: Option<Bitmap>)
    ensures match r {
        Some(result) => admitted(raw@, number, blocks, ipg, seed)
            && group::accepted(raw@, number, blocks, ipg, seed) && valid(context(raw@, number, blocks, ipg))
            && result.view().raw == canonical(context(raw@, number, blocks, ipg))
            && result.view().valid as nat == real_bits(context(raw@, number, blocks, ipg)) && result.view().meaningful == 32768
            && result.view().free as nat == bytes::le16(raw@, 12) && result.view().seed == seed
            && result.view().checksum == (crc::fold(seed, canonical(context(raw@, number, blocks, ipg))) & 0xffffu32) as u16
            && bitmap::accepted(result.view().raw, result.view().valid, 32768, result.view().free, result.view().checksum, seed),
        None => !admitted(raw@, number, blocks, ipg, seed),
    },
{
    reveal(admitted);
    synthesize_with_features(raw, number, blocks, ipg, seed, false)
}

pub fn synthesize_with_features(raw: &[u8], number: u32, blocks: u32, ipg: u32, seed: u32, flex: bool) -> (r: Option<Bitmap>)
    ensures match r {
        Some(result) => admitted_with_features(raw@, number, blocks, ipg, seed, flex)
            && group::accepted_with_features(raw@, number, blocks, ipg, seed, flex) && valid(context(raw@, number, blocks, ipg))
            && result.view().raw == canonical(context(raw@, number, blocks, ipg))
            && result.view().valid as nat == real_bits(context(raw@, number, blocks, ipg)) && result.view().meaningful == 32768
            && result.view().free as nat == bytes::le16(raw@, 12) && result.view().seed == seed
            && result.view().checksum == (crc::fold(seed, canonical(context(raw@, number, blocks, ipg))) & 0xffffu32) as u16
            && bitmap::accepted(result.view().raw, result.view().valid, 32768, result.view().free, result.view().checksum, seed),
        None => !admitted_with_features(raw@, number, blocks, ipg, seed, flex),
    },
{
    reveal(admitted_with_features);
    reveal(admitted_with_backup);
    if number >= 32 { return None; }
    synthesize_with_backup(raw, number, blocks, ipg, seed, flex, group_claims::backup_group(number).unwrap())
}

pub fn synthesize_with_backup(raw: &[u8], number: u32, blocks: u32, ipg: u32, seed: u32, flex: bool, backup: bool) -> (r: Option<Bitmap>)
    ensures match r {
        Some(result) => admitted_with_backup(raw@, number, blocks, ipg, seed, flex, backup)
            && group::accepted_with_features(raw@, number, blocks, ipg, seed, flex) && valid(context_with_backup(raw@, number, blocks, ipg, backup))
            && result.view().raw == canonical(context_with_backup(raw@, number, blocks, ipg, backup))
            && result.view().valid as nat == real_bits(context_with_backup(raw@, number, blocks, ipg, backup)) && result.view().meaningful == 32768
            && result.view().free as nat == bytes::le16(raw@, 12) && result.view().seed == seed
            && result.view().checksum == (crc::fold(seed, canonical(context_with_backup(raw@, number, blocks, ipg, backup))) & 0xffffu32) as u16
            && bitmap::accepted(result.view().raw, result.view().valid, 32768, result.view().free, result.view().checksum, seed),
        None => !admitted_with_backup(raw@, number, blocks, ipg, seed, flex, backup),
    },
{
    hide(crc::fold);
    hide(group::accepted_with_features);
    reveal(admitted_with_backup);
    if number >= 32 || blocks > block_claims::MAX_BLOCKS { return None; }
    let fields = match group::parse_with_features(raw, number, blocks, ipg, seed, flex) { Some(f) => f, None => { return None; } };
    assert(raw.len() == 32 || raw.len() == 64) by { reveal(group::accepted_with_features); }
    let free = bytes::read_le16(raw, 12).unwrap() as u32;
    assert(number as nat * 32768 < blocks) by { reveal(group::accepted_with_features); }
    let layout = Layout { number, blocks, block_bitmap: fields.block_bitmap, inode_bitmap: fields.inode_bitmap,
        inode_table: fields.inode_table, table_blocks: fields.inode_table_blocks, backup };
    assert(layout == context_with_backup(raw@, number, blocks, ipg, backup));
    let mut bytes: Vec<u8> = Vec::new();
    let mut index = 0u32;
    while index < 4096
        invariant index <= 4096, bytes.len() == index, valid(layout),
            group::accepted_with_features(raw@, number, blocks, ipg, seed, flex), layout == context_with_backup(raw@, number, blocks, ipg, backup),
            free as nat == bytes::le16(raw@, 12),
            forall|i: int| 0 <= i < index ==> #[trigger] bytes@[i] == byte(layout, i as nat),
        decreases 4096 - index,
    {
        bytes.push(make_byte(&layout, index));
        index += 1;
    }
    assert(bytes@ =~= canonical(layout)) by { reveal(canonical); }
    let calculated = crc::crc32c(seed, &bytes);
    let masked = calculated & 0xffffu32;
    proof { assert(calculated & 0xffffu32 <= 65535) by (bit_vector); }
    let checksum = masked as u16;
    let first = number * 32768;
    let available = blocks - first;
    let valid = if available < 32768 { available } else { 32768 };
    assert(valid as nat == real_bits(layout));
    proof {
        assert(free <= valid) by { reveal(group::accepted_with_features); }
        assert(bytes@.take(4096) =~= bytes@);
        assert forall|i: int| valid <= i < 32768 implies #[trigger] bitmap::set(bytes@, i) by {
            every_canonical_bit_has_the_exact_reserved_or_padding_meaning(layout, i as u32);
        }
    }
    bitmap::parse(&bytes, valid, 32768, free, checksum, seed)
}

/// Every real set bit is explained by an actual reserved metadata claim.
/// Disjoint whole-image census composition therefore cannot repurpose it as
/// ordinary file data, extent metadata or journal storage.
pub proof fn every_set_real_bit_has_a_reserved_metadata_claim(raw: Seq<u8>, number: u32, blocks: u32, ipg: u32, seed: u32, index: u32, flex: bool)
    requires group::accepted_with_features(raw, number, blocks, ipg, seed, flex), valid(context(raw, number, blocks, ipg)),
        index < real_bits(context(raw, number, blocks, ipg)),
        bitmap::set(canonical(context(raw, number, blocks, ipg)), index as int),
    ensures exists|i: int| 0 <= i < group_claims::claims(raw, number, ipg).len()
        && block_claims::covers(#[trigger] group_claims::claims(raw, number, ipg)[i], number as int * 32768 + index as int),
{
    every_set_real_bit_has_a_source_selected_reserved_metadata_claim(raw, number, blocks, ipg, seed, index, flex, group_claims::sparse_super(number));
    assert(group_claims::claims(raw, number, ipg) == group_claims::claims_with_backup(raw, number, ipg, group_claims::sparse_super(number)));
}

pub proof fn every_set_real_bit_has_a_source_selected_reserved_metadata_claim(raw: Seq<u8>, number: u32, blocks: u32, ipg: u32, seed: u32, index: u32, flex: bool, backup: bool)
    requires group::accepted_with_features(raw, number, blocks, ipg, seed, flex), valid(context_with_backup(raw, number, blocks, ipg, backup)),
        index < real_bits(context_with_backup(raw, number, blocks, ipg, backup)),
        bitmap::set(canonical(context_with_backup(raw, number, blocks, ipg, backup)), index as int),
    ensures exists|i: int| 0 <= i < group_claims::claims_with_backup(raw, number, ipg, backup).len()
        && block_claims::covers(#[trigger] group_claims::claims_with_backup(raw, number, ipg, backup)[i], number as int * 32768 + index as int),
{
    hide(crc::fold);
    let l = context_with_backup(raw, number, blocks, ipg, backup);
    assert(real_bits(l) <= 32768);
    every_canonical_bit_has_the_exact_reserved_or_padding_meaning(l, index);
    let prefix = if l.backup { 1int } else { 0int };
    let claims = group_claims::claims_with_backup(raw, number, ipg, backup);
    let physical = number as int * 32768 + index as int;
    if l.backup && index < 2 { assert(block_claims::covers(claims[0], physical)); }
    else if physical == l.block_bitmap { assert(block_claims::covers(claims[prefix], physical)); }
    else if physical == l.inode_bitmap { assert(block_claims::covers(claims[prefix + 1], physical)); }
    else { assert(block_claims::covers(claims[prefix + 2], physical)); }
}

}
