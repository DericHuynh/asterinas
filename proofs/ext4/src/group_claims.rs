// SPDX-License-Identifier: MPL-2.0

//! Source-bound reserved regions for the bounded census profile. With at most
//! 32 groups and 32-byte descriptors, each sparse-super group has one superblock
//! and one descriptor block. META_BG and reserved-GDT growth are not admitted.

use vstd::prelude::*;
use crate::{block_claims::{self, Census, Claim}, bytes, crc, group};

verus! {

pub open spec fn power3(n: u32) -> bool
    decreases n,
{ n == 1 || n > 1 && n % 3 == 0 && power3((n / 3) as u32) }

pub open spec fn power5(n: u32) -> bool
    decreases n,
{ n == 1 || n > 1 && n % 5 == 0 && power5((n / 5) as u32) }

pub open spec fn power7(n: u32) -> bool
    decreases n,
{ n == 1 || n > 1 && n % 7 == 0 && power7((n / 7) as u32) }

pub open spec fn sparse_super(group: u32) -> bool { group <= 1 || power3(group) || power5(group) || power7(group) }

pub open spec fn bounded_set(group: u32) -> bool {
    group == 0 || group == 1 || group == 3 || group == 5 || group == 7 || group == 9 || group == 25 || group == 27
}

pub proof fn bounded_sparse_super_set_matches_the_power_rule(group: u32)
    requires group < 32,
    ensures bounded_set(group) == sparse_super(group),
{
    reveal_with_fuel(power3, 5);
    reveal_with_fuel(power5, 5);
    reveal_with_fuel(power7, 5);
}

pub fn backup_group(group: u32) -> (r: Option<bool>)
    ensures match r {
        Some(backup) => group < 32 && backup == sparse_super(group),
        None => group >= 32,
    },
{
    if group >= 32 { return None; }
    proof { bounded_sparse_super_set_matches_the_power_rule(group); }
    Some(group == 0 || group == 1 || group == 3 || group == 5 || group == 7 || group == 9 || group == 25 || group == 27)
}

pub open spec fn metadata(start: u32, length: u32, kind: u8) -> Claim {
    Claim { start, length, kind, inode: 0, generation: 0, logical: 0, initialized: false }
}

fn candidate(start: u32, length: u32, kind: u8) -> (r: Claim) ensures r == metadata(start, length, kind) {
    Claim { start, length, kind, inode: 0, generation: 0, logical: 0, initialized: false }
}

pub open spec fn claims(raw: Seq<u8>, number: u32, ipg: u32) -> Seq<Claim> {
    let ordinary = seq![metadata(bytes::le32(raw, 0) as u32, 1, 3), metadata(bytes::le32(raw, 4) as u32, 1, 3),
        metadata(bytes::le32(raw, 8) as u32, (ipg / 16) as u32, 3)];
    if sparse_super(number) { seq![metadata((number as nat * 32768) as u32, 2, 1)] + ordinary }
    else { ordinary }
}

pub fn reserve(mut census: Census, raw: &[u8], number: u32, blocks: u32, ipg: u32, seed: u32) -> (r: Option<Census>)
    ensures match r {
        Some(next) => group::accepted(raw@, number, blocks, ipg, seed) && number < 32
            && next.wf() && next.view().roles.len() == census.view().roles.len() && next.view().roles.len() == blocks
            && next.view().claims == census.view().claims + claims(raw@, number, ipg)
            && block_claims::mapped_claims(next.view().roles, claims(raw@, number, ipg))
            && block_claims::preserves_occupied(census.view().roles, next.view().roles),
        None => true,
    },
{
    hide(crc::fold);
    hide(group::accepted);
    let ghost original = census.view();
    if census.block_count() != blocks { return None; }
    let desc = match group::parse(raw, number, blocks, ipg, seed) { Some(desc) => desc, None => { return None; } };
    let backup = match backup_group(number) { Some(backup) => backup, None => { return None; } };
    let mut input = Vec::new();
    if backup { input.push(candidate(number * 32768, 2, 1)); }
    input.push(candidate(desc.block_bitmap, 1, 3));
    input.push(candidate(desc.inode_bitmap, 1, 3));
    input.push(candidate(desc.inode_table, desc.inode_table_blocks, 3));
    let ghost source = claims(raw@, number, ipg);
    assert(input@ =~= source);
    assert(block_claims::preserves_occupied(original.roles, census.view().roles)) by { reveal(block_claims::preserves_occupied); }
    let mut index = 0usize;
    while index < input.len()
        invariant index <= input.len() <= 4, input@ == source,
            census.wf(), census.view().roles.len() == blocks,
            census.view().claims == original.claims + source.take(index as int),
            block_claims::preserves_occupied(original.roles, census.view().roles),
        decreases input.len() - index,
    {
        let ghost before = census.view().roles;
        census = match census.claim(input[index]) { Ok(next) => next, Err(_) => { return None; } };
        proof {
            block_claims::occupied_slot_preservation_is_transitive(original.roles, before, census.view().roles);
            assert(source.take(index as int + 1) =~= source.take(index as int).push(source[index as int]));
        }
        index += 1;
    }
    assert(source.take(source.len() as int) =~= source);
    proof { block_claims::every_appended_claim_has_its_exact_physical_slots(&census, original.claims, source); }
    Some(census)
}

}
