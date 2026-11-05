// SPDX-License-Identifier: MPL-2.0

//! Exact complete allocation-bitmap equality and source directory counters for
//! the EA-enabled index. The supplied ordinary catalogue's completeness is a
//! separate obligation of the whole-volume constructor, not this checker.

use vstd::prelude::*;
use crate::{block_claims::{self, Census, Slot}, bytes, ea_block_policy,
    ea_index::{self, Index, IndexView}, ea_ordinary::{Ordinary, OrdinaryView},
    ea_source, group};

verus! {

pub open spec fn views(ordinary: Seq<Ordinary>) -> Seq<OrdinaryView> {
    Seq::new(ordinary.len(), |i: int| ordinary[i].view())
}
pub open spec fn end(v: IndexView, count: nat) -> nat {
    if count * 32768 < v.header.blocks { count * 32768 } else { v.header.blocks as nat }
}
#[verifier::opaque]
pub open spec fn bitmaps_match(v: IndexView, roles: Seq<Slot>, count: nat) -> bool {
    forall|g: nat| g < count ==> #[trigger] block_claims::bitmap_matches(roles, (g * 32768) as u32, v.groups[g as int].allocation)
}
pub open spec fn directory_in_group(ordinary: OrdinaryView, group: u32, ipg: u32) -> bool {
    ipg > 0 && ordinary.parent.node.number > 0
        && (ordinary.parent.node.number as int - 1) / ipg as int == group
        && bytes::le16(ordinary.parent.node.raw, 0) as u16 & 0xf000 == 0x4000
}
pub open spec fn directory_count(ordinary: Seq<OrdinaryView>, group: u32, ipg: u32) -> nat
    decreases ordinary.len(),
{
    if ordinary.len() == 0 { 0nat } else {
        directory_count(ordinary.drop_last(), group, ipg)
            + if directory_in_group(ordinary.last(), group, ipg) { 1nat } else { 0nat }
    }
}
#[verifier::opaque]
pub open spec fn directory_counts_match(v: IndexView, ordinary: Seq<OrdinaryView>, count: nat) -> bool {
    forall|g: nat| g < count ==> #[trigger] directory_count(ordinary, g as u32, v.header.ipg)
        == bytes::le16(v.groups[g as int].descriptor, 16)
}

fn count_directories(ordinary: &[Ordinary], group: u32, ipg: u32) -> (r: u32)
    requires ordinary.len() <= 1048576, ipg > 0,
    ensures r as nat == directory_count(views(ordinary@), group, ipg), r <= ordinary.len(),
{
    let mut i = 0usize; let mut count = 0u32;
    while i < ordinary.len()
        invariant i <= ordinary.len() <= 1048576, count <= i, ipg > 0,
            count as nat == directory_count(views(ordinary@).take(i as int), group, ipg),
        decreases ordinary.len() - i,
    {
        let number = ordinary[i].number(); let directory = ordinary[i].is_directory();
        if directory && number > 0 && (number - 1) / ipg == group { count += 1; }
        assert(views(ordinary@).take(i as int + 1).drop_last() =~= views(ordinary@).take(i as int));
        assert(views(ordinary@).take(i as int + 1).last() == ordinary@[i as int].view());
        i += 1;
    }
    assert(views(ordinary@).take(i as int) =~= views(ordinary@));
    count
}

pub fn check(index: &Index<'_, '_>, census: &Census, ordinary: &[Ordinary]) -> (r: bool)
    ensures index.wf(), ea_index::valid(index.view()), census.wf(), r ==>
        census.view().roles.len() == index.view().header.blocks && ordinary.len() <= index.view().header.inodes
        && bitmaps_match(index.view(), census.view().roles, index.view().groups.len())
        && directory_counts_match(index.view(), views(ordinary@), index.view().groups.len())
        && block_claims::free_roles(census.view().roles, 0, census.view().roles.len()) == bytes::le32(index.view().header.source, 1036),
{
    let (blocks, inodes, ipg, _) = index.parameters();
    if census.block_count() != blocks || ordinary.len() > inodes as usize { return false; }
    let count = index.group_count(); let mut i = 0usize;
    assert(bitmaps_match(index.view(), census.view().roles, 0)) by { reveal(bitmaps_match); }
    assert(directory_counts_match(index.view(), views(ordinary@), 0)) by { reveal(directory_counts_match); }
    while i < count
        invariant index.wf(), ea_index::valid(index.view()), census.wf(),
            blocks == index.view().header.blocks, inodes == index.view().header.inodes,
            ipg == index.view().header.ipg, 0 < ipg <= 32768,
            ordinary.len() <= inodes <= 1048576, census.view().roles.len() == blocks,
            i <= count <= 32, count == index.view().groups.len(),
            bitmaps_match(index.view(), census.view().roles, i as nat),
            directory_counts_match(index.view(), views(ordinary@), i as nat),
        decreases count - i,
    {
        let group = index.group(i as u32).unwrap(); let (bitmap, _) = group.bitmaps();
        let first = i as u32 * 32768;
        if !census.matches_bitmap(first, bitmap) { return false; }
        let directories = count_directories(ordinary, i as u32, ipg);
        let descriptor = group.descriptor();
        proof { reveal(ea_index::group_valid); }
        assert(descriptor.len() == 32 || descriptor.len() == 64);
        if directories != bytes::read_le16(descriptor, 16).unwrap() as u32 { return false; }
        proof {
            reveal(ea_index::group_valid);
            reveal(bitmaps_match); reveal(directory_counts_match);
            assert forall|g: nat| g < i as nat + 1 implies #[trigger] block_claims::bitmap_matches(
                census.view().roles, (g * 32768) as u32, index.view().groups[g as int].allocation) by {
                if g < i { assert(block_claims::bitmap_matches(census.view().roles, (g * 32768) as u32, index.view().groups[g as int].allocation)); }
                else { assert(g == i); }
            }
            assert forall|g: nat| g < i as nat + 1 implies #[trigger] directory_count(views(ordinary@), g as u32, index.view().header.ipg)
                == bytes::le16(index.view().groups[g as int].descriptor, 16) by {
                if g < i { assert(directory_count(views(ordinary@), g as u32, index.view().header.ipg) == bytes::le16(index.view().groups[g as int].descriptor, 16)); }
                else { assert(g == i); }
            }
        }
        i += 1;
    }
    proof { all_matching_groups_have_the_exact_superblock_free_count(index.view(), census.view().roles); }
    true
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
    requires ea_index::valid(v), roles.len() == v.header.blocks, count <= v.groups.len(), bitmaps_match(v, roles, count),
    ensures block_claims::free_roles(roles, 0, end(v, count)) == ea_index::free_block_count(v.groups.take(count as int)),
    decreases count,
{
    reveal(ea_index::valid); reveal(ea_source::header_valid);
    reveal(bitmaps_match); reveal(ea_index::free_block_count);
    if count == 0 {
        reveal(block_claims::free_roles);
        assert(v.groups.take(0) =~= Seq::<ea_index::GroupView>::empty());
    } else {
        let g = (count - 1) as nat;
        assert(bitmaps_match(v, roles, g));
        checked_groups_sum_to_the_census(v, roles, g);
        ea_index::every_index_group_retains_its_exact_source_header_and_order(v, g as int);
        reveal(ea_index::group_valid);
        let first = (g * 32768) as u32;
        let amount = v.groups[g as int].allocation.valid as nat;
        assert(g * 32768 < v.header.blocks);
        assert(end(v, g) == first as nat && end(v, count) == first as nat + amount);
        block_claims::a_matching_bitmap_has_the_exact_census_free_count(roles, first, v.groups[g as int].allocation);
        free_ranges_split(roles, 0, first as nat, amount);
        assert(v.groups.take(count as int).drop_last() =~= v.groups.take(g as int));
        assert(v.groups.take(count as int).last() == v.groups[g as int]);
    }
}

pub proof fn all_matching_groups_have_the_exact_superblock_free_count(v: IndexView, roles: Seq<Slot>)
    requires ea_index::valid(v), roles.len() == v.header.blocks, bitmaps_match(v, roles, v.groups.len()),
    ensures block_claims::free_roles(roles, 0, roles.len()) == bytes::le32(v.header.source, 1036),
{
    reveal(ea_index::valid); reveal(ea_source::header_valid);
    checked_groups_sum_to_the_census(v, roles, v.groups.len());
    assert(end(v, v.groups.len()) == v.header.blocks);
    assert(v.groups.take(v.groups.len() as int) =~= v.groups);
}

pub proof fn matching_group_bitmaps_identify_every_allocated_physical_block(v: IndexView, roles: Seq<Slot>, block: u32)
    requires ea_index::valid(v), roles.len() == v.header.blocks, bitmaps_match(v, roles, v.groups.len()), block < v.header.blocks,
    ensures ea_block_policy::allocated(v, block) == (roles[block as int].kind != 0),
{
    reveal(ea_index::valid); reveal(ea_source::header_valid); reveal(bitmaps_match);
    let g = (block / 32768) as int;
    let slot = (block % 32768) as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(block as int, 32768);
    assert(0 <= g < v.groups.len());
    ea_index::every_index_group_retains_its_exact_source_header_and_order(v, g);
    reveal(ea_index::group_valid);
    assert(0 <= slot < v.groups[g].allocation.valid);
    let first = (g * 32768) as u32;
    assert(block_claims::bitmap_matches(roles, first, v.groups[g].allocation));
    reveal(block_claims::bitmap_matches);
    assert(first as int + slot == block);
    assert(crate::bitmap::set(v.groups[g].allocation.raw, slot) == (roles[block as int].kind != 0));
}

pub proof fn checked_directory_counts_match_each_source_descriptor(v: IndexView, ordinary: Seq<OrdinaryView>, number: u32)
    requires directory_counts_match(v, ordinary, v.groups.len()), number < v.groups.len(),
    ensures directory_count(ordinary, number, v.header.ipg) == bytes::le16(v.groups[number as int].descriptor, 16),
{
    reveal(directory_counts_match);
    let n = number as nat;
    assert(n < v.groups.len() && n as u32 == number);
    assert(directory_count(ordinary, n as u32, v.header.ipg) == bytes::le16(v.groups[n as int].descriptor, 16));
}

}
