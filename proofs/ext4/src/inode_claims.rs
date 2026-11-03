// SPDX-License-Identifier: MPL-2.0

//! Source-bound census entries from checked inode extent bytes. A failed
//! candidate is discarded before publication. This does not yet certify a
//! complete volume, namespace or file-access capability.

use vstd::prelude::*;
use crate::{block_claims::{self, Census, Claim}, bytes, crc, extent, inode, layout::{self, JournalLayout}};

verus! {

pub open spec fn claim_at(raw: Seq<u8>, number: u32, index: int) -> Claim {
    let offset = 52 + 12 * index;
    Claim { start: bytes::le32(raw, offset + 8) as u32,
        length: extent::length(bytes::le16(raw, offset + 4)) as u32,
        kind: if (bytes::le16(raw, 0) as u16 & 0xf000) == 0x4000 { 5u8 } else { 4u8 },
        inode: number, generation: bytes::le32(raw, 100) as u32,
        logical: bytes::le32(raw, offset) as u32, initialized: bytes::le16(raw, offset + 4) <= 32768 }
}

pub open spec fn claims(raw: Seq<u8>, number: u32) -> Seq<Claim> {
    Seq::new(bytes::le16(raw, 42), |i: int| claim_at(raw, number, i))
}

#[verifier::opaque]
pub open spec fn allocated(entries: Seq<Claim>) -> nat
    decreases entries.len(),
{
    if entries.len() == 0 { 0nat } else { allocated(entries.drop_last()) + entries.last().length as nat }
}

pub fn collect(mut census: Census, raw: &[u8], number: u32, inodes: u32, blocks: u32, seed: u32) -> (r: Option<Census>)
    ensures match r {
        Some(next) => inode::accepted(raw@, number, inodes, blocks, seed) && (number == 2 || number >= 11)
            && next.wf() && next.view().roles.len() == census.view().roles.len() && next.view().roles.len() == blocks
            && next.view().claims == census.view().claims + claims(raw@, number)
            && block_claims::mapped_claims(next.view().roles, claims(raw@, number))
            && block_claims::preserves_occupied(census.view().roles, next.view().roles)
            && bytes::le16(raw@, 116) == 0 && bytes::le32(raw@, 28) == 8 * allocated(claims(raw@, number)),
        None => true,
    },
{
    hide(crc::fold);
    hide(inode::accepted);
    let ghost original = census.view();
    if (number != 2 && number < 11) || census.block_count() != blocks { return None; }
    let meta = match inode::parse(raw, number, inodes, blocks, seed) { Some(meta) => meta, None => { return None; } };
    assert(raw.len() == 256 && bytes::le16(raw@, 42) <= 4) by { reveal(inode::accepted); }
    let root = &raw[40..100];
    let count = bytes::read_le16(raw, 42).unwrap();
    let kind = if meta.mode & 0xf000 == 0x4000 { 5u8 } else { 4u8 };
    let ghost source = claims(raw@, number);
    let mut index = 0usize;
    let mut total = 0u32;
    assert(allocated(Seq::empty()) == 0) by { reveal(allocated); }
    assert(source.take(0) =~= Seq::<Claim>::empty());
    assert(block_claims::preserves_occupied(original.roles, census.view().roles)) by { reveal(block_claims::preserves_occupied); }
    while index < count as usize
        invariant index <= count <= 4, raw.len() == 256, root@ == raw@.subrange(40, 100),
            census.wf(), census.view().roles.len() == blocks, original.roles.len() == blocks,
            census.view().claims == original.claims + source.take(index as int),
            block_claims::preserves_occupied(original.roles, census.view().roles),
            source == claims(raw@, number), source.len() == count,
            meta.generation as nat == bytes::le32(raw@, 100),
            kind == if (bytes::le16(raw@, 0) as u16 & 0xf000) == 0x4000 { 5u8 } else { 4u8 },
            total as nat == allocated(source.take(index as int)), total as nat <= index as nat * 32768,
        decreases count as usize - index,
    {
        let e = match extent::parse(root, 12 + 12 * index, blocks) { Some(e) => e, None => { return None; } };
        let claim = Claim { start: e.physical, length: e.length, kind, inode: number,
            generation: meta.generation, logical: e.logical, initialized: e.initialized };
        assert(claim == source[index as int]);
        let ghost before_roles = census.view().roles;
        census = match census.claim(claim) { Ok(next) => next, Err(_) => { return None; } };
        proof { block_claims::occupied_slot_preservation_is_transitive(original.roles, before_roles, census.view().roles); }
        total += e.length;
        proof {
            assert(source.take(index as int + 1).drop_last() =~= source.take(index as int));
            assert(source.take(index as int + 1).last() == claim);
            assert(allocated(source.take(index as int + 1)) == allocated(source.take(index as int)) + claim.length as nat) by { reveal(allocated); }
            assert(source.take(index as int + 1) =~= source.take(index as int).push(claim));
        }
        index += 1;
    }
    if bytes::read_le16(raw, 116).unwrap() != 0 || bytes::read_le32(raw, 28).unwrap() != total * 8 { return None; }
    assert(source.take(source.len() as int) =~= source);
    proof { block_claims::every_appended_claim_has_its_exact_physical_slots(&census, original.claims, source); }
    Some(census)
}

pub fn reserve_journal(census: Census, raw: &[u8], inodes: u32, blocks: u32, seed: u32) -> (r: Option<(Census, JournalLayout)>)
    ensures match r {
        Some((next, journal)) => layout::admitted(raw@, inodes, blocks, seed) && journal.wf()
            && block_claims::preserves_occupied(census.view().roles, next.view().roles)
            && journal.view().fs_blocks == blocks && next.wf() && next.view().roles.len() == census.view().roles.len()
            && next.view().claims == census.view().claims.push(Claim { start: journal.view().start,
                length: journal.view().journal_blocks, kind: 2, inode: 0, generation: 0, logical: 0, initialized: false })
            && bytes::le16(raw@, 116) == 0 && bytes::le32(raw@, 28) == journal.view().journal_blocks as nat * 8,
        None => true,
    },
{
    if census.block_count() != blocks { return None; }
    let journal = match layout::from_inode(raw, inodes, blocks, seed) { Some(j) => j, None => { return None; } };
    if bytes::read_le16(raw, 116).unwrap() != 0
        || bytes::read_le32(raw, 28).unwrap() != journal.blocks() * 8 { return None; }
    let claim = Claim { start: (journal.offset(0, 18446744073709551615).unwrap() / 4096) as u32,
        length: journal.blocks(), kind: 2, inode: 0, generation: 0, logical: 0, initialized: false };
    match census.claim(claim) { Ok(next) => Some((next, journal)), Err(_) => None }
}

}
