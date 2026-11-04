// SPDX-License-Identifier: MPL-2.0

//! A group descriptor and its initialized bitmaps from one immutable source.
//! Address provenance is a checked byte-range relation, not CRC injectivity.
//! This is metadata admission, not a complete filesystem or mount authority.

use vstd::prelude::*;
use crate::{bitmap::{self, Bitmap, BitmapView}, block_claims, bytes, crc, group::{self, Group}, group_fields, snapshot::Snapshot, superblock};

verus! {

pub struct GroupView {
    pub source: Seq<u8>, pub descriptor: Seq<u8>, pub number: u32, pub blocks: u32, pub ipg: u32, pub seed: u32,
    pub block_bitmap: u32, pub inode_bitmap: u32, pub inode_table: u32, pub table_blocks: u32,
    pub allocation: BitmapView, pub inodes: BitmapView,
}

pub open spec fn valid_bits(blocks: u32, number: u32) -> nat {
    (group::end(blocks, number) - number as nat * 32768) as nat
}

#[verifier::opaque]
pub open spec fn valid(v: GroupView) -> bool {
    &&& v.source.len() <= 18446744073709551615
    &&& superblock::accepted(v.source.subrange(1024, 2048), v.source.len() as u64)
    &&& 2 < v.blocks <= block_claims::MAX_BLOCKS && v.number < 32
    &&& v.blocks as nat == bytes::le32(v.source, 1028) && v.ipg as nat == bytes::le32(v.source, 1064)
    &&& v.seed == superblock::metadata_seed(v.source.subrange(1024, 2048))
    &&& v.descriptor == v.source.subrange(4096 + v.number as int * superblock::descriptor_bytes(v.source.subrange(1024, 2048)), 4096 + (v.number as int + 1) * superblock::descriptor_bytes(v.source.subrange(1024, 2048)))
    &&& group::accepted(v.descriptor, v.number, v.blocks, v.ipg, v.seed)
    &&& v.block_bitmap as nat == bytes::le32(v.descriptor, 0) && v.inode_bitmap as nat == bytes::le32(v.descriptor, 4)
    &&& v.inode_table as nat == bytes::le32(v.descriptor, 8) && v.table_blocks == v.ipg / 16
    &&& v.allocation.raw == v.source.subrange(v.block_bitmap as int * 4096, (v.block_bitmap as int + 1) * 4096)
    &&& v.allocation.valid as nat == valid_bits(v.blocks, v.number) && v.allocation.meaningful == 32768
    &&& v.allocation.free as nat == bytes::le16(v.descriptor, 12) && v.allocation.checksum as nat == bytes::le16(v.descriptor, 24)
    &&& v.allocation.seed == v.seed
    &&& bitmap::accepted(v.allocation.raw, v.allocation.valid, v.allocation.meaningful, v.allocation.free, v.allocation.checksum, v.seed)
    &&& (v.descriptor.len() == 64 ==> crc::fold(v.seed, v.allocation.raw)
        == group_fields::counter(v.descriptor, 24, 56, true))
    &&& v.inodes.raw == v.source.subrange(v.inode_bitmap as int * 4096, (v.inode_bitmap as int + 1) * 4096)
    &&& v.inodes.valid == v.ipg && v.inodes.meaningful == v.ipg
    &&& v.inodes.free as nat == bytes::le16(v.descriptor, 14) && v.inodes.checksum as nat == bytes::le16(v.descriptor, 26)
    &&& v.inodes.seed == v.seed
    &&& bitmap::accepted(v.inodes.raw, v.inodes.valid, v.inodes.meaningful, v.inodes.free, v.inodes.checksum, v.seed)
    &&& (v.descriptor.len() == 64 ==> crc::fold(v.seed, v.inodes.raw.take(v.ipg as int / 8))
        == group_fields::counter(v.descriptor, 26, 58, true))
}

pub struct GroupMetadata {
    source: Ghost<Seq<u8>>, descriptor: Vec<u8>, group: Group, blocks: u32, ipg: u32, seed: u32,
    allocation: Bitmap, inodes: Bitmap,
}

impl GroupMetadata {
    pub closed spec fn view(&self) -> GroupView {
        GroupView { source: self.source@, descriptor: self.descriptor@, number: self.group.number,
            blocks: self.blocks, ipg: self.ipg, seed: self.seed, block_bitmap: self.group.block_bitmap,
            inode_bitmap: self.group.inode_bitmap, inode_table: self.group.inode_table, table_blocks: self.group.inode_table_blocks,
            allocation: self.allocation.view(), inodes: self.inodes.view() }
    }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn parameters(&self) -> (r: (u32, u32, u32))
        ensures self.wf(), r == (self.view().blocks, self.view().ipg, self.view().seed),
    {
        proof { use_type_invariant(self); }
        (self.blocks, self.ipg, self.seed)
    }

    pub fn descriptor(&self) -> (r: &[u8]) ensures self.wf(), r@ == self.view().descriptor {
        proof { use_type_invariant(self); }
        &self.descriptor[..]
    }

    pub fn info(&self) -> (r: &Group)
        ensures self.wf(), r.number == self.view().number, r.block_bitmap == self.view().block_bitmap,
            r.inode_bitmap == self.view().inode_bitmap, r.inode_table == self.view().inode_table,
            r.inode_table_blocks == self.view().table_blocks,
    {
        proof { use_type_invariant(self); }
        &self.group
    }

    pub fn bitmaps(&self) -> (r: (&Bitmap, &Bitmap))
        ensures self.wf(), r.0.view() == self.view().allocation, r.1.view() == self.view().inodes,
    {
        proof { use_type_invariant(self); }
        (&self.allocation, &self.inodes)
    }
}

fn capture_descriptor(raw: &[u8]) -> (r: Vec<u8>)
    requires raw.len() == 32 || raw.len() == 64,
    ensures r@ == raw@,
{
    let mut copy = Vec::new();
    let mut index = 0usize;
    while index < raw.len()
        invariant copy.len() == index, index <= raw.len() <= 64,
            forall|i: int| 0 <= i < index ==> #[trigger] copy@[i] == raw@[i],
        decreases raw.len() - index,
    {
        copy.push(raw[index]);
        index += 1;
    }
    assert(copy@ =~= raw@);
    copy
}

pub fn parse(source: &Snapshot<'_>, number: u32) -> (r: Option<GroupMetadata>)
    ensures match r {
        Some(meta) => meta.wf() && meta.view().source == source.view() && meta.view().number == number,
        None => true,
    },
{
    hide(crc::fold);
    hide(superblock::accepted);
    hide(group::accepted);
    if number >= 32 { return None; }
    let primary = match source.block(0) { Some(block) => block, None => { return None; } };
    let boot = primary.range(1024, 1024).unwrap();
    let superblock = match superblock::parse(boot, source.partition_bytes()) { Some(sb) => sb, None => { return None; } };
    let blocks = superblock.blocks();
    if blocks > block_claims::MAX_BLOCKS || number * 32768 >= blocks { return None; }
    let ipg = bytes::read_le32(boot, 40).unwrap();
    let seed = superblock::metadata_checksum_seed(boot).unwrap();
    let gdt = match source.block(1) { Some(block) => block, None => { return None; } };
    let length = superblock::descriptor_length(boot).unwrap();
    let raw = gdt.range(number as usize * length, length).unwrap();
    let group = match group::parse(raw, number, blocks, ipg, seed) { Some(g) => g, None => { return None; } };
    let block_bitmap = match source.block(group.block_bitmap) { Some(block) => block, None => { return None; } };
    let inode_bitmap = match source.block(group.inode_bitmap) { Some(block) => block, None => { return None; } };
    let available = blocks - number * 32768;
    let valid_blocks = if available < 32768 { available } else { 32768 };
    if length == 64 {
        let block_checksum = group_fields::read_counter(raw, 24, 56, true).unwrap();
        let inode_checksum = group_fields::read_counter(raw, 26, 58, true).unwrap();
        if crc::crc32c(seed, block_bitmap.as_slice()) != block_checksum
            || crc::crc32c(seed, &inode_bitmap.as_slice()[..(ipg / 8) as usize]) != inode_checksum { return None; }
    }
    let allocation = match bitmap::parse(block_bitmap.as_slice(), valid_blocks, 32768,
        bytes::read_le16(raw, 12).unwrap() as u32, bytes::read_le16(raw, 24).unwrap(), seed) {
        Some(bitmap) => bitmap, None => { return None; }
    };
    let inodes = match bitmap::parse(inode_bitmap.as_slice(), ipg, ipg,
        bytes::read_le16(raw, 14).unwrap() as u32, bytes::read_le16(raw, 26).unwrap(), seed) {
        Some(bitmap) => bitmap, None => { return None; }
    };
    let descriptor = capture_descriptor(raw);
    let ghost assembled = GroupView { source: source.view(), descriptor: descriptor@, number: group.number,
        blocks, ipg, seed, block_bitmap: group.block_bitmap, inode_bitmap: group.inode_bitmap,
        inode_table: group.inode_table, table_blocks: group.inode_table_blocks,
        allocation: allocation.view(), inodes: inodes.view() };
    assert(valid(assembled)) by { reveal(valid); }
    let meta = GroupMetadata { source: Ghost(source.view()), descriptor, group, blocks, ipg, seed, allocation, inodes };
    assert(meta.view() == assembled);
    Some(meta)
}

}
