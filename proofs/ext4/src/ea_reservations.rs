// SPDX-License-Identifier: MPL-2.0

//! Exact source-selected fixed metadata and external-xattr reservations for
//! the bounded EA profile. The owned ledger rejects overlaps before recording
//! a new claim. This is physical role inspection, not filesystem admission,
//! allocation authority, journalling or a CortenMM/device binding.

use vstd::prelude::*;
use crate::{backup_layout, block_claims::{self, Census as Blocks, Claim},
    ea_census::{self, Census as References, External}, ea_index::{self, Index, IndexView},
    ea_source, group, group_claims};

verus! {

#[verifier::opaque]
pub open spec fn reserved(v: IndexView, count: nat) -> Seq<Claim> decreases count {
    if count == 0 { Seq::empty() } else {
        reserved(v, (count - 1) as nat) + group_claims::claims_for_source(v.header.source,
            v.groups[count as int - 1].descriptor, (count - 1) as u32, v.header.ipg)
    }
}

proof fn group_inputs(v: IndexView, number: u32)
    requires ea_index::valid(v), number < v.groups.len(),
    ensures v.groups[number as int].header == v.header,
        group::accepted_with_features(v.groups[number as int].descriptor, number,
            v.header.blocks, v.header.ipg, v.header.seed, v.header.flex),
{
    reveal(ea_index::valid); reveal(ea_index::ordered);
    assert(ea_index::group_valid(v.groups[number as int]));
    reveal(ea_index::group_valid);
}

pub fn reserve_groups(index: &Index<'_, '_>, initial: Blocks) -> (r: Option<Blocks>)
    ensures index.wf(), ea_index::valid(index.view()), initial.wf(), match r {
        Some(next) => next.wf() && next.view().roles.len() == index.view().header.blocks
            && next.view().roles.len() == initial.view().roles.len()
            && next.view().claims == initial.view().claims + reserved(index.view(), index.view().groups.len())
            && block_claims::preserves_occupied(initial.view().roles, next.view().roles)
            && block_claims::mapped_claims(next.view().roles, reserved(index.view(), index.view().groups.len())),
        None => true,
    },
{
    let (blocks, _, ipg, seed) = index.parameters(); let count = index.group_count();
    if initial.block_count() != blocks { return None; }
    let header = index.header(); let (_, _, incompatible) = header.feature_flags();
    let flex = incompatible & 0x200u32 != 0;
    proof { reveal(ea_source::header_valid); }
    assert(flex == index.view().header.flex);
    let source = index.source();
    assert(source.view().len() >= 4096);
    let ghost before = initial.view(); let mut census = initial; let mut i = 0usize;
    assert(reserved(index.view(), 0) =~= Seq::<Claim>::empty()) by { reveal(reserved); }
    assert(block_claims::preserves_occupied(before.roles, census.view().roles)) by { reveal(block_claims::preserves_occupied); }
    while i < count
        invariant index.wf(), ea_index::valid(index.view()), initial.wf(), before == initial.view(),
            blocks == index.view().header.blocks, ipg == index.view().header.ipg, seed == index.view().header.seed,
            flex == index.view().header.flex, source.view() == index.view().header.source,
            source.view().len() >= 4096, count == index.view().groups.len(), count <= 32, i <= count,
            census.wf(), census.view().roles.len() == blocks, before.roles.len() == blocks,
            census.view().claims == before.claims + reserved(index.view(), i as nat),
            block_claims::preserves_occupied(before.roles, census.view().roles),
        decreases count - i,
    {
        let meta = index.group(i as u32).unwrap();
        proof { group_inputs(index.view(), i as u32); }
        let descriptor = meta.descriptor();
        let backup = backup_layout::source_group(source, i as u32).unwrap();
        let ghost previous_roles = census.view().roles;
        census = match group_claims::reserve_with_backup(census, descriptor, i as u32, blocks, ipg, seed, flex, backup) {
            Some(next) => next, None => { return None; }
        };
        proof {
            block_claims::occupied_slot_preservation_is_transitive(before.roles, previous_roles, census.view().roles);
            reveal(reserved);
            assert(census.view().claims == before.claims + reserved(index.view(), i as nat + 1));
        }
        i += 1;
    }
    proof { block_claims::every_appended_claim_has_its_exact_physical_slots(&census, before.claims, reserved(index.view(), count as nat)); }
    Some(census)
}

pub open spec fn external_claim(address: u32) -> Claim {
    Claim { start: address, length: 1, kind: 7, inode: 0, generation: 0, logical: 0, initialized: false }
}
pub open spec fn contains_address(records: Seq<External>, address: u32) -> bool {
    exists|i: int| 0 <= i < records.len() && (#[trigger] records[i]).address == address
}
pub open spec fn external_claims(records: Seq<External>) -> Seq<Claim> decreases records.len() {
    if records.len() == 0 { Seq::empty() } else {
        let prior = external_claims(records.drop_last());
        if contains_address(records.drop_last(), records.last().address) { prior }
        else { prior.push(external_claim(records.last().address)) }
    }
}

fn seen(records: &[External], end: usize, address: u32) -> (r: bool)
    requires end <= records.len(),
    ensures r == contains_address(records@.take(end as int), address),
{
    let mut i = 0usize;
    while i < end
        invariant i <= end <= records.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] records@[j]).address != address,
        decreases end - i,
    {
        if records[i].address == address {
            assert(records@.take(end as int)[i as int].address == address);
            assert(exists|j: int| 0 <= j < records@.take(end as int).len() && (#[trigger] records@.take(end as int)[j]).address == address);
            return true;
        }
        i += 1;
    }
    assert(!contains_address(records@.take(end as int), address));
    false
}

pub fn reserve_external(refs: &References<'_, '_>, initial: Blocks) -> (r: Option<Blocks>)
    ensures refs.wf(), ea_census::valid(refs.view()), initial.wf(), match r {
        Some(next) => next.wf() && next.view().roles.len() == refs.view().index.header.blocks
            && next.view().roles.len() == initial.view().roles.len()
            && next.view().claims == initial.view().claims + external_claims(refs.view().external)
            && block_claims::preserves_occupied(initial.view().roles, next.view().roles)
            && block_claims::mapped_claims(next.view().roles, external_claims(refs.view().external)),
        None => true,
    },
{
    let index = refs.index(); let (blocks, _, _, _) = index.parameters(); let records = refs.external_pointers();
    if initial.block_count() != blocks { return None; }
    let ghost before = initial.view(); let mut census = initial; let mut i = 0usize;
    assert(external_claims(records@.take(0)) =~= Seq::<Claim>::empty());
    assert(block_claims::preserves_occupied(before.roles, census.view().roles)) by { reveal(block_claims::preserves_occupied); }
    while i < records.len()
        invariant refs.wf(), ea_census::valid(refs.view()), initial.wf(), before == initial.view(),
            records@ == refs.view().external, blocks == refs.view().index.header.blocks,
            census.wf(), census.view().roles.len() == blocks, before.roles.len() == blocks, i <= records.len(),
            census.view().claims == before.claims + external_claims(records@.take(i as int)),
            block_claims::preserves_occupied(before.roles, census.view().roles),
        decreases records.len() - i,
    {
        let address = records[i].address;
        if address == 0 || address >= blocks { return None; }
        let previous = seen(records, i, address);
        assert(records@.take(i as int + 1).drop_last() =~= records@.take(i as int));
        assert(records@.take(i as int + 1).last() == records@[i as int]);
        if !previous {
            let claim = Claim { start: address, length: 1, kind: 7, inode: 0, generation: 0, logical: 0, initialized: false };
            assert(claim == external_claim(address));
            let ghost previous_roles = census.view().roles;
            census = match census.claim(claim) { Ok(next) => next, Err(_) => { return None; } };
            proof { block_claims::occupied_slot_preservation_is_transitive(before.roles, previous_roles, census.view().roles); }
        }
        assert(census.view().claims == before.claims + external_claims(records@.take(i as int + 1)));
        i += 1;
    }
    assert(records@.take(i as int) =~= records@);
    proof { block_claims::every_appended_claim_has_its_exact_physical_slots(&census, before.claims, external_claims(records@)); }
    Some(census)
}

pub proof fn every_source_group_claim_occurs_in_the_complete_reservation(v: IndexView, count: nat, number: u32, claim: Claim)
    requires number < count <= v.groups.len(), group_claims::claims_for_source(v.header.source, v.groups[number as int].descriptor, number, v.header.ipg).contains(claim),
    ensures reserved(v, count).contains(claim),
    decreases count,
{
    reveal(reserved);
    let prior = reserved(v, (count - 1) as nat);
    let added = group_claims::claims_for_source(v.header.source, v.groups[count as int - 1].descriptor, (count - 1) as u32, v.header.ipg);
    if number < count - 1 {
        every_source_group_claim_occurs_in_the_complete_reservation(v, (count - 1) as nat, number, claim);
        let i = choose|i: int| 0 <= i < prior.len() && prior[i] == claim;
        assert((prior + added)[i] == claim);
        assert((prior + added).contains(claim));
    } else {
        assert(number as int == count - 1 && (count - 1) as u32 == number);
        let i = choose|i: int| 0 <= i < added.len() && added[i] == claim;
        assert((prior + added)[prior.len() as int + i] == claim);
        assert((prior + added).contains(claim));
    }
}

pub proof fn every_source_external_pointer_occurs_in_the_physical_reservation(records: Seq<External>, index: int)
    requires 0 <= index < records.len(),
    ensures external_claims(records).contains(external_claim(records[index].address)),
    decreases records.len(),
{
    let prior = records.drop_last(); let address = records[index].address;
    let claim = external_claim(address);
    if index < prior.len() {
        assert(prior[index] == records[index]);
        every_source_external_pointer_occurs_in_the_physical_reservation(prior, index);
    } else if contains_address(prior, address) {
        let j = choose|j: int| 0 <= j < prior.len() && (#[trigger] prior[j]).address == address;
        every_source_external_pointer_occurs_in_the_physical_reservation(prior, j);
    } else {
        assert(records.last().address == address);
        assert(external_claims(records) == external_claims(prior).push(claim));
        assert(external_claims(records)[external_claims(prior).len() as int] == claim);
        assert(external_claims(records).contains(claim));
        return;
    }
    let k = choose|k: int| 0 <= k < external_claims(prior).len() && external_claims(prior)[k] == claim;
    if contains_address(prior, records.last().address) {
        assert(external_claims(records) == external_claims(prior));
    } else {
        assert(external_claims(records) == external_claims(prior).push(external_claim(records.last().address)));
        assert(external_claims(records)[k] == claim);
    }
    assert(external_claims(records).contains(claim));
}

}
