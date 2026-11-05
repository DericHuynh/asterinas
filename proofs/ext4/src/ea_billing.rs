// SPDX-License-Identifier: MPL-2.0

//! Split Linux parent i_blocks accounting in the 4-KiB, non-BIGALLOC profile.
//!
//! Linux charges every logical EA entry to its parent even when the EA inode
//! or external xattr block is shared and even when quotas are disabled. This
//! module receives caller-supplied logical records: a source-bound complete
//! census must establish that they are exactly the parent's on-disk records.
//! The residual is arithmetic only; it proves neither physical block ownership
//! nor an extent audit, quota enforcement, caller authority or I/O authority.
//! The supplied huge-file feature must likewise come from checked geometry.

use vstd::prelude::*;
use crate::{ea_refs::{self, ParentReference}, inode_blocks, xattr};

verus! {

#[derive(Clone, Copy)]
pub struct Usage { pub total: u64, pub ea: u64, pub external: u64, pub own: u64 }

#[verifier::opaque]
pub open spec fn checked(raw: Seq<u8>, huge: bool, parent: u32, logical: Seq<ParentReference>, usage: Usage) -> bool {
    &&& raw.len() >= 120 && parent > 0 && ea_refs::logical_valid(logical)
    &&& usage.total as nat == inode_blocks::sectors(raw, 4096, huge)
    &&& usage.ea as nat * 512 == ea_refs::parent_bytes(logical, parent, 4096)
    &&& usage.ea % 8 == 0
    &&& usage.external as nat == xattr::allocated_block_count(raw) * 8
    &&& usage.own % 8 == 0
    &&& usage.total as nat == usage.ea as nat + usage.external as nat + usage.own as nat
}

pub fn split(raw: &[u8], huge: bool, parent: u32, logical: &[ParentReference]) -> (r: Option<Usage>)
    ensures match r { Some(usage) => checked(raw@, huge, parent, logical@, usage), None => true },
{
    let total = match inode_blocks::decode(raw, 4096, huge) { Some(total) => total, None => { return None; } };
    let address = match xattr::inode_pointer(raw) { Some(address) => address, None => { return None; } };
    let charge = match ea_refs::quota_usage(logical, parent, 4096) { Some(charge) => charge, None => { return None; } };
    let ea = charge.bytes / 512;
    // These guards make the sector split sound independently of a theorem
    // about successful admission/completeness of quota_usage's rounded sum.
    if charge.bytes % 512 != 0 || ea % 8 != 0 { return None; }
    let external = if address == 0 { 0u64 } else { 8u64 };
    if ea > 18446744073709551615u64 - external { return None; }
    let charged = ea + external;
    if total < charged { return None; }
    let own = total - charged;
    if own % 8 != 0 { return None; }
    proof { vstd::arithmetic::div_mod::lemma_fundamental_div_mod(charge.bytes as int, 512); }
    let usage = Usage { total, ea, external, own };
    assert(checked(raw@, huge, parent, logical@, usage)) by { reveal(checked); }
    Some(usage)
}

proof fn every_matching_logical_record_is_in_the_parent_sum(logical: Seq<ParentReference>, parent: u32, index: int)
    requires 0 <= index < logical.len(), logical[index].parent == parent,
    ensures ea_refs::rounded_size(logical[index].physical.size, 4096) <= ea_refs::parent_bytes(logical, parent, 4096),
    decreases logical.len(),
{
    if index < logical.len() - 1 {
        assert(logical.drop_last()[index] == logical[index]);
        every_matching_logical_record_is_in_the_parent_sum(logical.drop_last(), parent, index);
    } else {
        assert(index == logical.len() - 1);
        assert(logical.last() == logical[index]);
    }
}

pub proof fn every_logical_ea_entry_contributes_its_rounded_parent_charge(raw: Seq<u8>, huge: bool, parent: u32,
    logical: Seq<ParentReference>, usage: Usage, index: int)
    requires checked(raw, huge, parent, logical, usage), 0 <= index < logical.len(), logical[index].parent == parent,
    ensures ea_refs::rounded_size(logical[index].physical.size, 4096) <= usage.ea as nat * 512,
{
    reveal(checked);
    every_matching_logical_record_is_in_the_parent_sum(logical, parent, index);
}

pub proof fn the_residual_subtracts_logical_ea_charges_and_the_external_block(raw: Seq<u8>, huge: bool, parent: u32,
    logical: Seq<ParentReference>, usage: Usage)
    requires checked(raw, huge, parent, logical, usage),
    ensures usage.total as nat >= usage.ea as nat + usage.external as nat,
        usage.own as nat == usage.total as nat - usage.ea as nat - usage.external as nat,
        usage.external == if xattr::inode_address(raw) == 0 { 0u64 } else { 8u64 },
        usage.ea % 8 == 0 && usage.own % 8 == 0,
{ reveal(checked); }

pub proof fn the_ea_charge_uses_the_complete_logical_sum_even_with_shared_values(raw: Seq<u8>, huge: bool, parent: u32,
    logical: Seq<ParentReference>, usage: Usage)
    requires checked(raw, huge, parent, logical, usage),
    ensures usage.ea as nat * 512 == ea_refs::parent_bytes(logical, parent, 4096),
        usage.total as nat == usage.own as nat + usage.external as nat + ea_refs::parent_bytes(logical, parent, 4096) / 512,
{
    reveal(checked);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(ea_refs::parent_bytes(logical, parent, 4096) as int,
        512, usage.ea as int, 0);
}


proof fn two_matching_logical_records_are_both_in_the_parent_sum(logical: Seq<ParentReference>, parent: u32, first: int, second: int)
    requires 0 <= first < second < logical.len(), logical[first].parent == parent && logical[second].parent == parent,
    ensures ea_refs::rounded_size(logical[first].physical.size, 4096) + ea_refs::rounded_size(logical[second].physical.size, 4096)
        <= ea_refs::parent_bytes(logical, parent, 4096),
    decreases logical.len(),
{
    if second < logical.len() - 1 {
        assert(logical.drop_last()[first] == logical[first]);
        assert(logical.drop_last()[second] == logical[second]);
        two_matching_logical_records_are_both_in_the_parent_sum(logical.drop_last(), parent, first, second);
    } else {
        assert(second == logical.len() - 1);
        assert(logical.last() == logical[second]);
        assert(logical.drop_last()[first] == logical[first]);
        every_matching_logical_record_is_in_the_parent_sum(logical.drop_last(), parent, first);
    }
}
pub proof fn distinct_logical_entries_are_charged_separately_even_for_the_same_ea_inode(raw: Seq<u8>, huge: bool, parent: u32,
    logical: Seq<ParentReference>, usage: Usage, first: int, second: int)
    requires checked(raw, huge, parent, logical, usage), 0 <= first < second < logical.len(),
        logical[first].parent == parent && logical[second].parent == parent,
    ensures ea_refs::rounded_size(logical[first].physical.size, 4096) + ea_refs::rounded_size(logical[second].physical.size, 4096)
        <= usage.ea as nat * 512,
{
    reveal(checked);
    two_matching_logical_records_are_both_in_the_parent_sum(logical, parent, first, second);
}

}
