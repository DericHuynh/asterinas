// SPDX-License-Identifier: MPL-2.0

//! Whole-image allocation validation for the bounded initialized-group profile.
//! This certifies physical ownership and counters, not namespace consistency,
//! permissions, recovery completion, a mount, or an OSTD/device snapshot.

use vstd::prelude::*;
use crate::{allocation_counts, block_claims::{self, Census, CensusView, Claim, Slot}, bytes,
    group_claims, group_index::{self, GroupIndex, IndexView}, inode_claims, inode_group, inode_table,
    layout::{self, JournalLayout, LayoutView}, snapshot::Snapshot};

verus! {

#[verifier::opaque]
pub open spec fn reserved(v: IndexView, count: nat) -> Seq<Claim>
    decreases count,
{
    if count == 0 { Seq::empty() }
    else { reserved(v, (count - 1) as nat) + group_claims::claims_for_source(v.source, v.groups[count as int - 1].descriptor, (count - 1) as u32, v.ipg) }
}

#[verifier::opaque]
pub open spec fn data(v: IndexView, count: nat) -> Seq<Claim>
    decreases count,
{
    if count == 0 { Seq::empty() }
    else { data(v, (count - 1) as nat) + inode_group::claims(v, (count - 1) as u32, v.ipg as nat) }
}

pub open spec fn journal_claim(j: LayoutView) -> Claim {
    Claim { start: j.start, length: j.journal_blocks, kind: 2, inode: 0, generation: 0, logical: 0, initialized: false }
}

#[verifier::opaque]
pub open spec fn journal_matches(v: IndexView, j: LayoutView) -> bool {
    let raw = inode_table::raw(v, 8);
    &&& layout::admitted(raw, v.inodes, v.blocks, v.seed)
    &&& j.fs_blocks == v.blocks && j.start > 1 && 1024 <= j.journal_blocks <= 32768
    &&& j.start as nat + j.journal_blocks <= v.blocks
    &&& j.start as nat == bytes::le32(raw, 60) && j.journal_blocks as nat == bytes::le32(raw, 4) / 4096
    &&& bytes::le16(raw, 116) == 0 && bytes::le32(raw, 28) == (j.journal_blocks as nat + crate::xattr::allocated_block_count(raw)) * 8
}

#[verifier::opaque]
pub open spec fn checked_groups(v: IndexView, roles: Seq<Slot>, count: nat) -> bool {
    forall|g: nat| g < count ==> #[trigger] inode_group::checked_prefix(v, roles, g as u32, v.ipg as nat)
        && inode_group::directory_count(v, g as u32, v.ipg as nat) == bytes::le16(v.groups[g as int].descriptor, 16)
}

proof fn append_checked_group(v: IndexView, before: Seq<Slot>, after: Seq<Slot>, count: u32)
    requires checked_groups(v, before, count as nat), block_claims::preserves_occupied(before, after),
        count < 32, count < v.groups.len(), inode_group::checked_prefix(v, after, count, v.ipg as nat),
        inode_group::directory_count(v, count, v.ipg as nat) == bytes::le16(v.groups[count as int].descriptor, 16),
    ensures checked_groups(v, after, count as nat + 1),
{
    reveal(checked_groups);
    assert forall|g: nat| g < count as nat + 1 implies #[trigger] inode_group::checked_prefix(v, after, g as u32, v.ipg as nat)
        && inode_group::directory_count(v, g as u32, v.ipg as nat) == bytes::le16(v.groups[g as int].descriptor, 16) by {
        if g < count as nat {
            assert(inode_group::checked_prefix(v, before, g as u32, v.ipg as nat));
            assert(inode_group::directory_count(v, g as u32, v.ipg as nat) == bytes::le16(v.groups[g as int].descriptor, 16));
            inode_group::occupied_preservation_keeps_checked_nodes(v, before, after, g as u32, v.ipg as nat);
        } else { assert(g == count as nat && g as u32 == count); }
    }
}

pub struct AllocationView { pub index: IndexView, pub census: CensusView, pub journal: LayoutView }

#[verifier::opaque]
pub open spec fn valid(v: AllocationView) -> bool {
    &&& group_index::valid(v.index)
    &&& block_claims::ledger(v.census.roles, v.census.claims) && v.census.roles.len() == v.index.blocks
    &&& journal_matches(v.index, v.journal)
    &&& v.census.claims == reserved(v.index, v.index.groups.len()) + seq![journal_claim(v.journal)] + data(v.index, v.index.groups.len()) + crate::xattr_source::claims(v.index, v.index.inodes as nat)
    &&& crate::xattr_source::checked(v.index, v.census.roles)
    &&& checked_groups(v.index, v.census.roles, v.index.groups.len())
    &&& allocation_counts::bitmaps_match(v.index, v.census.roles, v.index.groups.len())
    &&& block_claims::free_roles(v.census.roles, 0, v.census.roles.len()) == bytes::le32(v.index.source, 1036)
}

proof fn a_reserved_prefix_contains_each_group_claim(v: IndexView, count: nat, number: u32, claim: Claim)
    requires number < count <= v.groups.len(), group_claims::claims_for_source(v.source, v.groups[number as int].descriptor, number, v.ipg).contains(claim),
    ensures reserved(v, count).contains(claim),
    decreases count,
{
    reveal(reserved);
    let prefix = reserved(v, (count - 1) as nat);
    let suffix = group_claims::claims_for_source(v.source, v.groups[count as int - 1].descriptor, (count - 1) as u32, v.ipg);
    if number < count - 1 {
        a_reserved_prefix_contains_each_group_claim(v, (count - 1) as nat, number, claim);
        let i = choose|i: int| 0 <= i < prefix.len() && prefix[i] == claim;
        assert((prefix + suffix)[i] == claim);
    } else {
        assert(number as int == count - 1 && (count - 1) as u32 == number);
        let i = choose|i: int| 0 <= i < suffix.len() && suffix[i] == claim;
        assert((prefix + suffix)[prefix.len() as int + i] == claim);
    }
}

pub proof fn every_reserved_group_claim_has_its_exact_role(v: AllocationView, number: u32, claim: Claim, block: int)
    requires valid(v), number < v.index.groups.len(),
        group_claims::claims_for_source(v.index.source, v.index.groups[number as int].descriptor, number, v.index.ipg).contains(claim),
        block_claims::covers(claim, block),
    ensures 0 <= block < v.census.roles.len(), v.census.roles[block] == block_claims::at(claim, block),
{
    reveal(valid);
    let reserved = reserved(v.index, v.index.groups.len());
    a_reserved_prefix_contains_each_group_claim(v.index, v.index.groups.len(), number, claim);
    let i = choose|i: int| 0 <= i < reserved.len() && reserved[i] == claim;
    assert(v.census.claims[i] == claim);
    block_claims::a_ledger_claim_determines_its_exact_physical_slot(v.census.roles, v.census.claims, claim, block);
}

pub proof fn the_internal_journal_has_only_journal_roles(v: AllocationView, block: u32)
    requires valid(v), v.journal.start <= block < v.journal.start as nat + v.journal.journal_blocks,
    ensures block < v.census.roles.len(), v.census.roles[block as int].kind == 2,
{
    reveal(valid);
    let claim = journal_claim(v.journal);
    let i = reserved(v.index, v.index.groups.len()).len() as int;
    assert(v.census.claims[i] == claim);
    assert(v.census.claims.contains(claim));
    block_claims::a_ledger_claim_determines_its_exact_physical_slot(v.census.roles, v.census.claims, claim, block as int);
}

pub proof fn the_primary_superblock_and_descriptor_have_reserved_roles(v: AllocationView)
    requires valid(v),
    ensures v.census.roles.len() > 2, v.census.roles[0].kind == 1, v.census.roles[1].kind == 1,
{
    reveal(valid);
    reveal(group_index::valid);
    let claim = group_claims::metadata(0, 2, 1);
    let claims = group_claims::claims_for_source(v.index.source, v.index.groups[0].descriptor, 0, v.index.ipg);
    assert(claims[0] == claim && claims.contains(claim));
    every_reserved_group_claim_has_its_exact_role(v, 0, claim, 0);
    every_reserved_group_claim_has_its_exact_role(v, 0, claim, 1);
}

pub proof fn every_inode_table_position_has_a_metadata_role(v: AllocationView, number: u32)
    requires valid(v), 0 < number <= v.index.inodes,
    ensures inode_table::start(v.index, number) + 256 <= v.index.blocks as nat * 4096 <= v.index.source.len(),
        inode_table::start(v.index, number) % 4096 <= 3840,
        v.census.roles[(inode_table::start(v.index, number) / 4096) as int].kind == 3,
        0 <= ((number as int - 1) / (v.index.ipg as int)) < v.index.groups.len(),
        v.index.groups[(number as int - 1) / v.index.ipg as int].inode_table <= inode_table::start(v.index, number) / 4096
            < v.index.groups[(number as int - 1) / v.index.ipg as int].inode_table as nat + v.index.ipg as nat / 16,
{
    reveal(valid);
    reveal(group_index::valid);
    reveal(group_index::records_match);
    vstd::arithmetic::mul::lemma_mul_is_commutative(v.index.ipg as int, v.index.groups.len() as int);
    vstd::arithmetic::div_mod::lemma_multiply_divide_lt(number as int - 1, v.index.ipg as int, v.index.groups.len() as int);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(number as int - 1, v.index.ipg as int);
    let group = (number as int - 1) / v.index.ipg as int;
    let slot = (number as int - 1) % v.index.ipg as int;
    let meta = v.index.groups[group];
    assert(crate::group_metadata::valid(meta));
    reveal(crate::group_metadata::valid);
    reveal(crate::group::accepted_with_features);
    let claim = group_claims::metadata(meta.inode_table, (v.index.ipg / 16) as u32, 3);
    let claims = group_claims::claims_for_source(v.index.source, meta.descriptor, group as u32, v.index.ipg);
    let index = if crate::backup_layout::present(v.index.source.subrange(1024, 2048), group as u32) { 3int } else { 2int };
    assert(group as u32 as int == group);
    assert(meta.inode_table as nat == bytes::le32(meta.descriptor, 8));
    assert(0 <= index < claims.len() && claims[index] == claim);
    assert(claims.contains(claim));
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(slot, 16);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(meta.inode_table as int * 4096 + slot * 256, 4096,
        meta.inode_table as int + slot / 16, slot % 16 * 256);
    vstd::arithmetic::div_mod::lemma_multiply_divide_lt(slot, 16, (v.index.ipg / 16) as int);
    let block = (inode_table::start(v.index, number) / 4096) as int;
    assert(block_claims::covers(claim, block));
    every_reserved_group_claim_has_its_exact_role(v, group as u32, claim, block);
}

pub proof fn every_group_inode_bitmap_has_a_metadata_role(v: AllocationView, number: u32)
    requires valid(v), number < v.index.groups.len(),
    ensures v.index.groups[number as int].inode_bitmap < v.census.roles.len(),
        v.census.roles[v.index.groups[number as int].inode_bitmap as int].kind == 3,
{
    hide(crate::crc::fold);
    reveal(valid);
    reveal(group_index::valid);
    reveal(group_index::records_match);
    let meta = v.index.groups[number as int];
    assert(crate::group_metadata::valid(meta));
    reveal(crate::group_metadata::valid);
    let claim = group_claims::metadata(meta.inode_bitmap, 1, 3);
    let claims = group_claims::claims_for_source(v.index.source, meta.descriptor, number, v.index.ipg);
    let index = if crate::backup_layout::present(v.index.source.subrange(1024, 2048), number) { 2int } else { 1int };
    assert(meta.inode_bitmap as nat == bytes::le32(meta.descriptor, 4));
    assert(0 <= index < claims.len() && claims[index] == claim);
    assert(claims.contains(claim));
    every_reserved_group_claim_has_its_exact_role(v, number, claim, meta.inode_bitmap as int);
}

pub struct Allocation<'a> { index: GroupIndex<'a>, census: Census, journal: JournalLayout }

impl<'a> Allocation<'a> {
    pub closed spec fn view(&self) -> AllocationView {
        AllocationView { index: self.index.view(), census: self.census.view(), journal: self.journal.view() }
    }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn index(&self) -> (r: &GroupIndex<'a>) ensures self.wf(), r.view() == self.view().index {
        proof { use_type_invariant(self); }
        &self.index
    }

    pub fn census(&self) -> (r: &Census) ensures self.wf(), r.view() == self.view().census {
        proof { use_type_invariant(self); }
        &self.census
    }

    pub fn journal(&self) -> (r: &JournalLayout) ensures self.wf(), r.view() == self.view().journal, r.wf() {
        proof { use_type_invariant(self); reveal(valid); reveal(journal_matches); }
        &self.journal
    }
}

pub fn parse<'a>(source: Snapshot<'a>) -> (r: Option<Allocation<'a>>)
    ensures match r { Some(volume) => volume.wf() && volume.view().index.source == source.view(), None => true },
{
    let index = match group_index::parse(source) { Some(index) => index, None => { return None; } };
    let (blocks, inodes, ipg, seed) = index.parameters();
    let count = index.group_count() as u32;
    let flex = index.flex_groups();
    assert(2 < blocks <= block_claims::MAX_BLOCKS && inodes >= 11) by { reveal(group_index::valid); }
    let mut census = Census::new(blocks).unwrap();
    let mut g = 0u32;
    assert(reserved(index.view(), 0) == Seq::<Claim>::empty()) by { reveal(reserved); }
    while g < count
        invariant index.wf(), count == index.view().groups.len(), count <= 32, g <= count,
            (blocks, inodes, ipg, seed) == (index.view().blocks, index.view().inodes, index.view().ipg, index.view().seed),
            census.wf(), census.view().roles.len() == blocks, census.view().claims == reserved(index.view(), g as nat),
            flex == group_index::has_flex_groups(index.view()),
        decreases count - g,
    {
        let meta = index.get(g).unwrap();
        assert(index.view().source.len() >= 4096) by { reveal(group_index::valid); }
        let backup = crate::backup_layout::source_group(index.source(), g).unwrap();
        assert(backup == crate::backup_layout::present(index.view().source.subrange(1024, 2048), g));
        census = match group_claims::reserve_with_backup(census, meta.descriptor(), g, blocks, ipg, seed, flex, backup) {
            Some(next) => next, None => { return None; }
        };
        assert(reserved(index.view(), g as nat + 1) == reserved(index.view(), g as nat)
            + group_claims::claims_for_source(index.view().source, index.view().groups[g as int].descriptor, g, ipg)) by { reveal(reserved); }
        g += 1;
    }
    let raw = inode_table::read(&index, 8).unwrap();
    let (mut census, journal) = match inode_claims::reserve_journal(census, raw, inodes, blocks, seed) {
        Some(pair) => pair, None => { return None; }
    };
    assert(journal_matches(index.view(), journal.view())) by { reveal(journal_matches); }
    let ghost base = reserved(index.view(), count as nat) + seq![journal_claim(journal.view())];
    assert(census.view().claims == base);
    assert(data(index.view(), 0) == Seq::<Claim>::empty()) by { reveal(data); }
    assert(checked_groups(index.view(), census.view().roles, 0)) by { reveal(checked_groups); }
    g = 0;
    while g < count
        invariant index.wf(), count == index.view().groups.len(), count <= 32, g <= count,
            census.wf(), census.view().roles.len() == index.view().blocks,
            journal_matches(index.view(), journal.view()),
            base == reserved(index.view(), count as nat) + seq![journal_claim(journal.view())],
            census.view().claims == base + data(index.view(), g as nat),
            checked_groups(index.view(), census.view().roles, g as nat),
        decreases count - g,
    {
        let ghost before = census.view().roles;
        census = match inode_group::collect(&index, census, g) { Some(next) => next, None => { return None; } };
        proof {
            append_checked_group(index.view(), before, census.view().roles, g);
            assert(data(index.view(), g as nat + 1) == data(index.view(), g as nat)
                + inode_group::claims(index.view(), g, index.view().ipg as nat)) by { reveal(data); }
        }
        g += 1;
    }
    let ghost before_attributes = census.view().roles;
    census = match crate::xattr_source::audit(census, &index) { Some(next) => next, None => { return None; } };
    proof {
        reveal(checked_groups);
        assert forall|g: nat| g < count implies #[trigger] inode_group::checked_prefix(index.view(), census.view().roles, g as u32, index.view().ipg as nat)
            && inode_group::directory_count(index.view(), g as u32, index.view().ipg as nat) == bytes::le16(index.view().groups[g as int].descriptor, 16) by {
            inode_group::occupied_preservation_keeps_checked_nodes(index.view(), before_attributes, census.view().roles, g as u32, index.view().ipg as nat);
        }
    }
    g = 0;
    assert(allocation_counts::bitmaps_match(index.view(), census.view().roles, 0)) by { reveal(allocation_counts::bitmaps_match); }
    while g < count
        invariant index.wf(), count == index.view().groups.len(), count <= 32, g <= count,
            census.wf(), census.view().roles.len() == index.view().blocks,
            journal_matches(index.view(), journal.view()),
            census.view().claims == reserved(index.view(), count as nat) + seq![journal_claim(journal.view())] + data(index.view(), count as nat) + crate::xattr_source::claims(index.view(), index.view().inodes as nat),
            crate::xattr_source::checked(index.view(), census.view().roles),
            checked_groups(index.view(), census.view().roles, count as nat),
            allocation_counts::bitmaps_match(index.view(), census.view().roles, g as nat),
        decreases count - g,
    {
        let meta = index.get(g).unwrap();
        let (bitmap, _) = meta.bitmaps();
        if !census.matches_bitmap(g * 32768, bitmap) { return None; }
        assert(allocation_counts::bitmaps_match(index.view(), census.view().roles, g as nat + 1)) by {
            reveal(allocation_counts::bitmaps_match);
            assert forall|n: nat| n < g as nat + 1 implies #[trigger] block_claims::bitmap_matches(
                census.view().roles, (n * 32768) as u32, index.view().groups[n as int].allocation) by { }
        }
        g += 1;
    }
    proof { allocation_counts::all_matching_groups_have_the_exact_superblock_free_count(index.view(), census.view().roles); }
    let ghost assembled = AllocationView { index: index.view(), census: census.view(), journal: journal.view() };
    assert(valid(assembled)) by { reveal(valid); }
    Some(Allocation { index, census, journal })
}

}
