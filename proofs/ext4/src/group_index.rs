// SPDX-License-Identifier: MPL-2.0

//! All initialized group metadata from one immutable validation snapshot.
//! Group and superblock free counters agree exactly. The snapshot is retained
//! so later inode traversal cannot silently switch to a different input.

use vstd::prelude::*;
use crate::{block_claims, bytes, crc, group_metadata::{self, GroupMetadata, GroupView}, snapshot::Snapshot, superblock};

verus! {

pub open spec fn views(groups: Seq<GroupMetadata>) -> Seq<GroupView> {
    Seq::new(groups.len(), |i: int| groups[i].view())
}

#[verifier::opaque]
pub open spec fn free_blocks(groups: Seq<GroupView>) -> nat
    decreases groups.len(),
{ if groups.len() == 0 { 0nat } else { free_blocks(groups.drop_last()) + groups.last().allocation.free as nat } }

#[verifier::opaque]
pub open spec fn free_inodes(groups: Seq<GroupView>) -> nat
    decreases groups.len(),
{ if groups.len() == 0 { 0nat } else { free_inodes(groups.drop_last()) + groups.last().inodes.free as nat } }

pub struct IndexView {
    pub source: Seq<u8>, pub groups: Seq<GroupView>, pub blocks: u32, pub inodes: u32, pub ipg: u32, pub seed: u32,
}

pub open spec fn projected_groups(source: Seq<u8>, count: nat) -> Seq<GroupView> {
    Seq::new(count, |i: int| group_metadata::projection(source, i as u32))
}

pub open spec fn projection(source: Seq<u8>) -> IndexView {
    let blocks = bytes::le32(source, 1028) as u32;
    IndexView { source, blocks, inodes: bytes::le32(source, 1024) as u32,
        ipg: bytes::le32(source, 1064) as u32, seed: superblock::metadata_seed(source.subrange(1024, 2048)),
        groups: projected_groups(source, (blocks as nat + 32767) / 32768) }
}

pub open spec fn admissible(source: Seq<u8>) -> bool { valid(projection(source)) }

pub open spec fn has_flex_groups(v: IndexView) -> bool { superblock::flex_bg(v.source.subrange(1024, 2048)) }

pub open spec fn has_huge_files(v: IndexView) -> bool { bytes::le32(v.source, 1124) as u32 & 8 != 0 }

#[verifier::opaque]
pub open spec fn records_match(groups: Seq<GroupView>, source: Seq<u8>, blocks: u32, ipg: u32, seed: u32) -> bool {
    forall|i: int| 0 <= i < groups.len() ==> #[trigger] group_metadata::valid(groups[i])
        && groups[i].source == source && groups[i].number as int == i
        && groups[i].blocks == blocks && groups[i].ipg == ipg && groups[i].seed == seed
}

proof fn append_checked_group(groups: Seq<GroupView>, source: Seq<u8>, blocks: u32, ipg: u32, seed: u32, next: GroupView)
    requires records_match(groups, source, blocks, ipg, seed), group_metadata::valid(next),
        next.source == source, next.number as nat == groups.len(), next.blocks == blocks, next.ipg == ipg, next.seed == seed,
    ensures records_match(groups.push(next), source, blocks, ipg, seed),
{
    hide(group_metadata::valid);
    reveal(records_match);
    assert forall|i: int| 0 <= i < groups.push(next).len() implies #[trigger] group_metadata::valid(groups.push(next)[i])
        && groups.push(next)[i].source == source && groups.push(next)[i].number as int == i
        && groups.push(next)[i].blocks == blocks && groups.push(next)[i].ipg == ipg && groups.push(next)[i].seed == seed by {
        if i < groups.len() {
            assert(groups.push(next)[i] == groups[i]);
            assert(group_metadata::valid(groups[i]));
        } else { assert(i == groups.len()); assert(groups.push(next)[i] == next); }
    }
}

#[verifier::opaque]
pub open spec fn valid(v: IndexView) -> bool {
    &&& 4096 <= v.source.len() <= 18446744073709551615
    &&& superblock::accepted(v.source.subrange(1024, 2048), v.source.len() as u64)
    &&& 2 < v.blocks <= block_claims::MAX_BLOCKS && 0 < v.groups.len() <= 32
    &&& v.blocks as nat * 4096 <= v.source.len()
    &&& 0 < v.ipg <= 32768 && v.ipg % 16 == 0 && v.inodes >= 11
    &&& v.groups.len() == (v.blocks as nat + 32767) / 32768
    &&& v.blocks as nat == bytes::le32(v.source, 1028) && v.inodes as nat == bytes::le32(v.source, 1024)
    &&& v.ipg as nat == bytes::le32(v.source, 1064) && v.inodes as nat == v.groups.len() * v.ipg as nat
    &&& v.seed == superblock::metadata_seed(v.source.subrange(1024, 2048))
    &&& records_match(v.groups, v.source, v.blocks, v.ipg, v.seed)
    &&& free_blocks(v.groups) == bytes::le32(v.source, 1036)
    &&& free_inodes(v.groups) == bytes::le32(v.source, 1040)
}

pub proof fn every_checked_group_retains_its_source_and_geometry(index: IndexView, number: int)
    requires valid(index), 0 <= number < index.groups.len(),
    ensures group_metadata::valid(index.groups[number]), index.groups[number].source == index.source,
        index.groups[number].number as int == number, index.groups[number].ipg == index.ipg,
        index.groups[number].blocks == index.blocks, index.groups[number].seed == index.seed,
{
    reveal(valid);
    reveal(records_match);
    assert(group_metadata::valid(index.groups[number]));
}

pub proof fn every_valid_index_is_the_unique_source_projection(index: IndexView)
    requires valid(index),
    ensures index == projection(index.source), admissible(index.source),
{
    hide(group_metadata::valid);
    hide(superblock::accepted);
    reveal(valid);
    assert(index.groups =~= projection(index.source).groups) by {
        assert forall|i: int| 0 <= i < index.groups.len() implies
            #[trigger] index.groups[i] == projection(index.source).groups[i] by {
            every_checked_group_retains_its_source_and_geometry(index, i);
            group_metadata::every_valid_group_is_the_unique_source_projection(index.groups[i]);
        }
    }
}

proof fn an_admitted_source_supplies_the_index_parser_inputs(source: Seq<u8>)
    ensures admissible(source) ==> 8192 <= source.len() <= 18446744073709551615
        && superblock::accepted(source.subrange(1024, 2048), source.len() as u64)
        && 2 < bytes::le32(source, 1028) <= block_claims::MAX_BLOCKS,
{
    hide(superblock::accepted);
    if admissible(source) { reveal(valid); }
}

proof fn every_group_of_an_admitted_index_is_admissible(source: Seq<u8>, number: u32)
    ensures admissible(source) && number < projection(source).groups.len() ==> group_metadata::admissible(source, number),
{
    hide(group_metadata::valid);
    if admissible(source) && number < projection(source).groups.len() {
        every_checked_group_retains_its_source_and_geometry(projection(source), number as int);
        group_metadata::every_valid_group_is_the_unique_source_projection(projection(source).groups[number as int]);
    }
}

proof fn appending_the_next_group_extends_the_source_projection(source: Seq<u8>, count: nat, next: GroupView)
    requires count < 32, next == group_metadata::projection(source, count as u32),
    ensures projected_groups(source, count).push(next) == projected_groups(source, count + 1),
{
    assert(projected_groups(source, count).push(next) =~= projected_groups(source, count + 1));
}

pub struct GroupIndex<'a> {
    source: Snapshot<'a>, groups: Vec<GroupMetadata>, blocks: u32, inodes: u32, ipg: u32, seed: u32,
}

impl<'a> GroupIndex<'a> {
    pub closed spec fn view(&self) -> IndexView {
        IndexView { source: self.source.view(), groups: views(self.groups@), blocks: self.blocks,
            inodes: self.inodes, ipg: self.ipg, seed: self.seed }
    }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn source(&self) -> (r: &Snapshot<'a>) ensures self.wf(), r.view() == self.view().source {
        proof { use_type_invariant(self); }
        &self.source
    }

    pub fn parameters(&self) -> (r: (u32, u32, u32, u32))
        ensures self.wf(), r == (self.view().blocks, self.view().inodes, self.view().ipg, self.view().seed),
    {
        proof { use_type_invariant(self); }
        (self.blocks, self.inodes, self.ipg, self.seed)
    }

    pub fn flex_groups(&self) -> (r: bool) ensures self.wf(), r == has_flex_groups(self.view()) {
        let source = self.source();
        proof { reveal(valid); }
        let primary = source.block(0).unwrap();
        superblock::flex_enabled(primary.range(1024, 1024).unwrap()).unwrap()
    }

    pub fn huge_files(&self) -> (r: bool) ensures self.wf(), r == has_huge_files(self.view()) {
        proof { use_type_invariant(self); reveal(valid); }
        let primary = self.source.block(0).unwrap();
        bytes::read_le32(primary.as_slice(), 1124).unwrap() & 8 != 0
    }

    pub fn group_count(&self) -> (r: usize) ensures self.wf(), r == self.view().groups.len(), 0 < r <= 32 {
        proof { use_type_invariant(self); reveal(valid); }
        self.groups.len()
    }

    pub fn get(&self, number: u32) -> (r: Option<&GroupMetadata>)
        ensures self.wf(), match r {
            Some(group) => number < self.view().groups.len() && group.view() == self.view().groups[number as int],
            None => number >= self.view().groups.len(),
        },
    {
        proof { use_type_invariant(self); }
        if number as usize >= self.groups.len() { None } else { Some(&self.groups[number as usize]) }
    }
}

pub fn parse<'a>(source: Snapshot<'a>) -> (r: Option<GroupIndex<'a>>)
    ensures match r {
        Some(index) => index.wf() && index.view().source == source.view()
            && index.view() == projection(source.view()) && admissible(source.view()),
        None => !admissible(source.view()),
    },
{
    hide(crc::fold);
    hide(superblock::accepted);
    proof { an_admitted_source_supplies_the_index_parser_inputs(source.view()); }
    let primary = match source.block(0) { Some(block) => block, None => { return None; } };
    let boot = primary.range(1024, 1024).unwrap();
    let sb = match superblock::parse(boot, source.partition_bytes()) { Some(sb) => sb, None => { return None; } };
    let blocks = sb.blocks();
    let inodes = sb.inodes();
    let count = sb.groups();
    if blocks > block_claims::MAX_BLOCKS { return None; }
    let ipg = bytes::read_le32(boot, 40).unwrap();
    let seed = superblock::metadata_checksum_seed(boot).unwrap();
    assert(blocks as nat * 4096 <= source.view().len() && 0 < ipg <= 32768 && ipg % 16 == 0 && inodes >= 11)
        by { reveal(superblock::accepted); }
    let mut groups: Vec<GroupMetadata> = Vec::new();
    let mut number = 0u32;
    let mut block_free = 0u64;
    let mut inode_free = 0u64;
    assert(free_blocks(Seq::empty()) == 0 && free_inodes(Seq::empty()) == 0) by { reveal(free_blocks); reveal(free_inodes); }
    assert(views(groups@) =~= Seq::<GroupView>::empty());
    assert(views(groups@) =~= projected_groups(source.view(), 0));
    assert(records_match(views(groups@), source.view(), blocks, ipg, seed)) by { reveal(records_match); }
    while number < count
        invariant groups.len() == number, number <= count <= 32,
            count as nat == projection(source.view()).groups.len(),
            views(groups@) == projected_groups(source.view(), number as nat),
            source.view().len() >= 4096,
            blocks as nat * 4096 <= source.view().len(), 0 < ipg <= 32768, ipg % 16 == 0, inodes >= 11,
            blocks as nat == bytes::le32(source.view(), 1028), ipg as nat == bytes::le32(source.view(), 1064),
            seed == superblock::metadata_seed(source.view().subrange(1024, 2048)),
            block_free as nat == free_blocks(views(groups@)), inode_free as nat == free_inodes(views(groups@)),
            block_free as nat <= number as nat * 32768, inode_free as nat <= number as nat * 32768,
            records_match(views(groups@), source.view(), blocks, ipg, seed),
        decreases count - number,
    {
        proof { every_group_of_an_admitted_index_is_admissible(source.view(), number); }
        let meta = match group_metadata::parse(&source, number) { Some(meta) => meta, None => { return None; } };
        assert(meta.view().blocks == blocks && meta.view().ipg == ipg && meta.view().seed == seed) by { reveal(group_metadata::valid); }
        let (allocation, inodes) = meta.bitmaps();
        block_free += allocation.free_count() as u64;
        inode_free += inodes.free_count() as u64;
        let ghost previous = views(groups@);
        let ghost latest = meta.view();
        proof { append_checked_group(previous, source.view(), blocks, ipg, seed, latest); }
        groups.push(meta);
        proof {
            assert(views(groups@) =~= previous.push(latest));
            appending_the_next_group_extends_the_source_projection(source.view(), number as nat, latest);
            assert(views(groups@).drop_last() =~= previous);
            assert(free_blocks(views(groups@)) == free_blocks(previous) + latest.allocation.free as nat) by { reveal(free_blocks); }
            assert(free_inodes(views(groups@)) == free_inodes(previous) + latest.inodes.free as nat) by { reveal(free_inodes); }
            assert(records_match(views(groups@), source.view(), blocks, ipg, seed));
        }
        number += 1;
    }
    assert(views(groups@) == projection(source.view()).groups);
    proof { if admissible(source.view()) { reveal(valid); } }
    if block_free != bytes::read_le32(boot, 12).unwrap() as u64
        || inode_free != bytes::read_le32(boot, 16).unwrap() as u64 { return None; }
    let ghost assembled = IndexView { source: source.view(), groups: views(groups@), blocks, inodes, ipg, seed };
    assert(valid(assembled)) by { reveal(valid); }
    proof { every_valid_index_is_the_unique_source_projection(assembled); }
    Some(GroupIndex { source, groups, blocks, inodes, ipg, seed })
}

}
