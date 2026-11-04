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
    ensures match r { Some(index) => index.wf() && index.view().source == source.view(), None => true },
{
    hide(crc::fold);
    hide(superblock::accepted);
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
    assert(records_match(views(groups@), source.view(), blocks, ipg, seed)) by { reveal(records_match); }
    while number < count
        invariant groups.len() == number, number <= count <= 32,
            source.view().len() >= 4096,
            blocks as nat * 4096 <= source.view().len(), 0 < ipg <= 32768, ipg % 16 == 0, inodes >= 11,
            blocks as nat == bytes::le32(source.view(), 1028), ipg as nat == bytes::le32(source.view(), 1064),
            seed == superblock::metadata_seed(source.view().subrange(1024, 2048)),
            block_free as nat == free_blocks(views(groups@)), inode_free as nat == free_inodes(views(groups@)),
            block_free as nat <= number as nat * 32768, inode_free as nat <= number as nat * 32768,
            records_match(views(groups@), source.view(), blocks, ipg, seed),
        decreases count - number,
    {
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
            assert(views(groups@).drop_last() =~= previous);
            assert(free_blocks(views(groups@)) == free_blocks(previous) + latest.allocation.free as nat) by { reveal(free_blocks); }
            assert(free_inodes(views(groups@)) == free_inodes(previous) + latest.inodes.free as nat) by { reveal(free_inodes); }
            assert(records_match(views(groups@), source.view(), blocks, ipg, seed));
        }
        number += 1;
    }
    if block_free != bytes::read_le32(boot, 12).unwrap() as u64
        || inode_free != bytes::read_le32(boot, 16).unwrap() as u64 { return None; }
    let ghost assembled = IndexView { source: source.view(), groups: views(groups@), blocks, inodes, ipg, seed };
    assert(valid(assembled)) by { reveal(valid); }
    Some(GroupIndex { source, groups, blocks, inodes, ipg, seed })
}

}
