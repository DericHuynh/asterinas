// SPDX-License-Identifier: MPL-2.0

//! Refinement of all group allocation bitmaps to the global free-block count.

use vstd::prelude::*;
use crate::{block_claims::{self, Slot}, bytes, group_index::{self, IndexView}, group_metadata};

verus! {

pub open spec fn end(v: IndexView, count: nat) -> nat {
    if count * 32768 < v.blocks { count * 32768 } else { v.blocks as nat }
}

#[verifier::opaque]
pub open spec fn bitmaps_match(v: IndexView, roles: Seq<Slot>, count: nat) -> bool {
    forall|g: nat| g < count ==> #[trigger] block_claims::bitmap_matches(roles, (g * 32768) as u32, v.groups[g as int].allocation)
}

proof fn free_ranges_split(roles: Seq<Slot>, first: u32, left: nat, right: nat)
    requires roles.len() <= block_claims::MAX_BLOCKS, first as nat + left + right <= roles.len(),
    ensures block_claims::free_roles(roles, first, left + right)
        == block_claims::free_roles(roles, first, left) + block_claims::free_roles(roles, (first as nat + left) as u32, right),
    decreases right,
{
    reveal(block_claims::free_roles);
    if right > 0 { free_ranges_split(roles, first, left, (right - 1) as nat); }
}

proof fn checked_groups_sum_to_the_census(v: IndexView, roles: Seq<Slot>, count: nat)
    requires group_index::valid(v), roles.len() == v.blocks, count <= v.groups.len(), bitmaps_match(v, roles, count),
    ensures block_claims::free_roles(roles, 0, end(v, count)) == group_index::free_blocks(v.groups.take(count as int)),
    decreases count,
{
    reveal(group_index::valid);
    reveal(bitmaps_match);
    reveal(group_index::free_blocks);
    if count == 0 {
        reveal(block_claims::free_roles);
        assert(v.groups.take(0) =~= Seq::<group_metadata::GroupView>::empty());
    } else {
        let g = (count - 1) as nat;
        assert(bitmaps_match(v, roles, g));
        checked_groups_sum_to_the_census(v, roles, g);
        reveal(group_index::records_match);
        assert(group_metadata::valid(v.groups[g as int]));
        reveal(group_metadata::valid);
        let first = (g * 32768) as u32;
        let amount = v.groups[g as int].allocation.valid as nat;
        assert(g * 32768 < v.blocks);
        assert(end(v, g) == first as nat && end(v, count) == first as nat + amount);
        block_claims::a_matching_bitmap_has_the_exact_census_free_count(roles, first, v.groups[g as int].allocation);
        free_ranges_split(roles, 0, first as nat, amount);
        assert(v.groups.take(count as int).drop_last() =~= v.groups.take(g as int));
        assert(v.groups.take(count as int).last() == v.groups[g as int]);
    }
}

pub proof fn all_matching_groups_have_the_exact_superblock_free_count(v: IndexView, roles: Seq<Slot>)
    requires group_index::valid(v), roles.len() == v.blocks, bitmaps_match(v, roles, v.groups.len()),
    ensures block_claims::free_roles(roles, 0, roles.len()) == bytes::le32(v.source, 1036),
{
    reveal(group_index::valid);
    checked_groups_sum_to_the_census(v, roles, v.groups.len());
    assert(end(v, v.groups.len()) == v.blocks);
    assert(v.groups.take(v.groups.len() as int) =~= v.groups);
}

}
