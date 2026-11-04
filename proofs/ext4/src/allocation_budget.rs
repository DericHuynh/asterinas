// SPDX-License-Identifier: MPL-2.0

//! Complete inode-audit admission within the physical volume's block budget.

use vstd::prelude::*;
use crate::{allocated_inode, allocation::{self, AllocationView}, claim_budget,
    extent_claims, extent_tree, group_index::{self, IndexView}, inode_claims, inode_group};

verus! {

proof fn an_inode_contribution_fits_the_group_claim_sum(v: IndexView, group: u32, slot: nat, count: nat)
    requires slot < count <= v.ipg, inode_group::allocated(v, group, slot),
        inode_group::ordinary(inode_group::number(v, group, slot)),
    ensures inode_claims::allocated(extent_claims::claims(v, inode_group::number(v, group, slot)))
        <= inode_claims::allocated(inode_group::claims(v, group, count)),
    decreases count,
{
    reveal(inode_group::claims);
    if slot < count - 1 {
        an_inode_contribution_fits_the_group_claim_sum(v, group, slot, (count - 1) as nat);
    } else {
        assert(slot == count - 1);
        assert(inode_group::contribution(v, group, (count - 1) as nat)
            == extent_claims::claims(v, inode_group::number(v, group, slot)));
    }
    extent_claims::allocated_concatenation(inode_group::claims(v, group, (count - 1) as nat),
        inode_group::contribution(v, group, (count - 1) as nat));
}

proof fn a_group_claim_sum_fits_the_complete_data_claim_sum(v: IndexView, group: u32, count: nat)
    requires group < count <= v.groups.len() <= 32,
    ensures inode_claims::allocated(inode_group::claims(v, group, v.ipg as nat))
        <= inode_claims::allocated(allocation::data(v, count)),
    decreases count,
{
    reveal(allocation::data);
    if group < count - 1 {
        a_group_claim_sum_fits_the_complete_data_claim_sum(v, group, (count - 1) as nat);
    } else { assert(group == (count - 1) as u32); }
    extent_claims::allocated_concatenation(allocation::data(v, (count - 1) as nat),
        inode_group::claims(v, (count - 1) as u32, v.ipg as nat));
}

/// Global allocation validity gives each live ordinary inode enough audit
/// budget at blocks+1. The proof counts all inode-owned external metadata as
/// well as data, and relies on physical disjointness rather than tree depth
/// alone or a guessed maximum number of nodes.
pub proof fn every_live_inode_fits_the_volume_sized_audit_budget(v: AllocationView, number: u32)
    requires allocation::valid(v), allocated_inode::live(v.index, number),
    ensures inode_claims::allocated(extent_claims::claims(v.index, number)) <= v.index.blocks,
        extent_tree::tree_visits(extent_claims::context(v.index, number),
            extent_tree::root_node(extent_claims::context(v.index, number)), extent_claims::depth(v.index, number))
            <= v.index.blocks as nat + 1,
        extent_claims::binding_admissible(v.index, number, (v.index.blocks as nat + 1) as u64),
{
    hide(crate::crc::fold);
    allocated_inode::every_live_inode_has_source_bound_claims(v, number);
    reveal(inode_group::ordinary_checked);
    reveal(allocation::valid);
    reveal(group_index::valid);
    claim_budget::every_disjoint_claim_ledger_fits_the_physical_volume(v.census.roles, v.census.claims);
    vstd::arithmetic::mul::lemma_mul_is_commutative(v.index.ipg as int, v.index.groups.len() as int);
    vstd::arithmetic::div_mod::lemma_multiply_divide_lt(number as int - 1, v.index.ipg as int, v.index.groups.len() as int);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(number as int - 1, v.index.ipg as int);
    let group = ((number as int - 1) / v.index.ipg as int) as u32;
    let slot = ((number as int - 1) % v.index.ipg as int) as nat;
    assert(group as int == (number as int - 1) / v.index.ipg as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(v.index.ipg as int, group as int);
    assert(inode_group::number(v.index, group, slot) == number);
    assert(inode_group::allocated(v.index, group, slot));
    an_inode_contribution_fits_the_group_claim_sum(v.index, group, slot, v.index.ipg as nat);
    a_group_claim_sum_fits_the_complete_data_claim_sum(v.index, group, v.index.groups.len());
    extent_claims::allocated_concatenation(allocation::reserved(v.index, v.index.groups.len()) + seq![allocation::journal_claim(v.journal)],
        allocation::data(v.index, v.index.groups.len()));
    extent_claims::an_inode_audit_visits_at_most_its_claimed_blocks_plus_the_inline_root(v.index, number);
}

}
