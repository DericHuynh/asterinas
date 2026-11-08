// SPDX-License-Identifier: MPL-2.0

//! Linux orphan-file blocks and private copy-on-update images. The caller
//! binds the supplied inode checksum seed and physical address to its source.
//! No block allocation, journal submission or mount capability is returned.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{block_size, bytes, crc, inode};

verus! {

pub const MAGIC: u32 = 0x0b10ca04;
pub const TAIL_BYTES: usize = 8;
pub const MAX_BLOCK_BYTES: usize = 65536;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Error { Geometry, Address, Inode, Magic, Checksum, Full, Occupied, Stale, Duplicate }

pub open spec fn capacity_for(raw: Seq<u8>) -> nat {
    if raw.len() >= 8 { ((raw.len() - 8) / 4) as nat } else { 0nat }
}
pub open spec fn checksum_value(raw: Seq<u8>, physical: u64, seed: u32) -> u32 {
    let address = bytes::encoded_le((physical & 0xffffffffu64) as u32)
        + bytes::encoded_le((physical >> 32) as u32);
    crc::fold(crc::fold(seed, address), raw.take(raw.len() as int - 8))
}
pub open spec fn valid_raw(raw: Seq<u8>, physical: u64, seed: u32, metadata: bool, inodes: u32) -> bool {
    &&& block_size::accepted(raw.len())
    &&& raw.len() >= 8 && inodes > 0
    &&& bytes::le32(raw, raw.len() as int - 8) == MAGIC
    &&& (!metadata || bytes::le32(raw, raw.len() as int - 4) == checksum_value(raw, physical, seed))
    &&& forall|i: int| 0 <= i < capacity_for(raw) ==> #[trigger] bytes::le32(raw, i * 4) <= inodes
}

fn copy(raw: &[u8]) -> (r: Vec<u8>)
    ensures r@ == raw@,
{
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len(), out.len() == i, out@ == raw@.take(i as int),
        decreases raw.len() - i,
    { out.push(raw[i]); i += 1; }
    out
}
fn write32(raw: &mut Vec<u8>, at: usize, value: u32) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r == (at as int + 4 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, at as int, bytes::encoded_le(value)) } else { old(raw)@ },
        r ==> bytes::le32(final(raw)@, at as int) == value as nat,
{
    bytes::write_le32(raw.as_mut_slice(), at, value)
}

/// The orphan-file seed is the inode seed, not the filesystem seed alone.
pub fn inode_seed(fs_seed: u32, number: u32, generation: u32) -> (r: u32)
    ensures r == crc::fold(crc::fold(fs_seed, bytes::encoded_le(number)), bytes::encoded_le(generation)),
{
    inode::inode_seed(fs_seed, number, generation)
}

/// Linux excludes both tail words from this checksum and prefixes LE64 pblk.
pub fn calculate_checksum(raw: &[u8], physical: u64, seed: u32) -> (r: Option<u32>)
    ensures match r {
        Some(value) => block_size::accepted(raw.len() as nat) && value == checksum_value(raw@, physical, seed),
        None => !block_size::accepted(raw.len() as nat),
    },
{
    if !block_size::valid(raw.len()) || raw.len() < TAIL_BYTES { return None; }
    let low = bytes::encode_le32((physical & 0xffffffffu64) as u32);
    let high = bytes::encode_le32((physical >> 32) as u32);
    let a = crc::crc32c(seed, &low);
    let b = crc::crc32c(a, &high);
    let value = crc::crc32c(b, &raw[..raw.len() - TAIL_BYTES]);
    proof {
        assert(low@ == bytes::encoded_le((physical & 0xffffffffu64) as u32));
        assert(high@ == bytes::encoded_le((physical >> 32) as u32));
        crc::streaming(seed, low@, high@);
    }
    Some(value)
}

/// Exact byte-envelope admission. This binds the supplied profile and
/// physical checksum coordinate, not filesystem allocation or write authority.
pub open spec fn parse_admissible(raw: Seq<u8>, physical: u64, fs_blocks: u64,
    seed: u32, metadata: bool, inodes: u32) -> bool
{
    valid_raw(raw, physical, seed, metadata, inodes) && physical < fs_blocks
}

pub struct BlockView {
    pub raw: Seq<u8>, pub physical: u64, pub seed: u32, pub metadata: bool, pub inodes: u32,
}
pub open spec fn block_valid(v: BlockView) -> bool { valid_raw(v.raw, v.physical, v.seed, v.metadata, v.inodes) }
pub open spec fn same_profile(a: BlockView, b: BlockView) -> bool {
    a.raw.len() == b.raw.len() && a.physical == b.physical && a.seed == b.seed
        && a.metadata == b.metadata && a.inodes == b.inodes
}
pub open spec fn slot(v: BlockView, i: nat) -> u32 { bytes::le32(v.raw, (i * 4) as int) as u32 }
pub open spec fn slot_frame(before: BlockView, after: BlockView, i: nat, value: u32) -> bool {
    &&& same_profile(before, after) && i < capacity_for(before.raw)
    &&& slot(after, i) == value
    &&& !before.metadata ==> after.raw.subrange(after.raw.len() as int - 4, after.raw.len() as int)
        == before.raw.subrange(before.raw.len() as int - 4, before.raw.len() as int)
    &&& forall|j: nat| j < capacity_for(before.raw) && j != i ==> #[trigger] slot(before, j) == slot(after, j)
}
pub open spec fn unique(v: BlockView) -> bool {
    forall|i: nat, j: nat| i < j < capacity_for(v.raw) && slot(v, i) != 0 ==> #[trigger] slot(v, i) != #[trigger] slot(v, j)
}

#[verifier::opaque]
pub open spec fn empty_prefix(v: BlockView, count: nat) -> nat
    recommends count <= capacity_for(v.raw),
    decreases count,
{
    if count == 0 { 0nat } else {
        (empty_prefix(v, (count - 1) as nat) + if slot(v, (count - 1) as nat) == 0 { 1nat } else { 0nat }) as nat
    }
}
proof fn empty_prefix_facts(v: BlockView, count: nat)
    requires count <= capacity_for(v.raw),
    ensures empty_prefix(v, count) <= count,
        empty_prefix(v, count) == 0 <==> forall|i: nat| i < count ==> #[trigger] slot(v, i) != 0,
    decreases count,
{
    reveal(empty_prefix);
    if count > 0 {
        empty_prefix_facts(v, (count - 1) as nat);
        if slot(v, (count - 1) as nat) == 0 {
            assert(!(forall|i: nat| i < count ==> #[trigger] slot(v, i) != 0)) by {
                if forall|i: nat| i < count ==> #[trigger] slot(v, i) != 0 {
                    assert(slot(v, (count - 1) as nat) != 0);
                }
            }
        } else {
            assert((forall|i: nat| i < count ==> #[trigger] slot(v, i) != 0)
                <==> (forall|i: nat| i < count - 1 ==> #[trigger] slot(v, i) != 0)) by {
                if forall|i: nat| i < count - 1 ==> #[trigger] slot(v, i) != 0 {
                    assert forall|i: nat| i < count implies #[trigger] slot(v, i) != 0 by {
                        if i >= count - 1 { assert(i == count - 1); }
                    }
                }
            }
        }
    }
}

proof fn prefix_retains_word(before: Seq<u8>, after: Seq<u8>, at: nat)
    requires before.len() == after.len(), before.len() >= 8,
        before.take(before.len() as int - 8) == after.take(after.len() as int - 8),
        at * 4 + 4 <= before.len() - 8,
    ensures bytes::le32(before, (at * 4) as int) == bytes::le32(after, (at * 4) as int),
{
    assert forall|i: int| 0 <= i < 4 implies before[(at * 4) as int + i] == after[(at * 4) as int + i] by {
        assert(before.take(before.len() as int - 8)[(at * 4) as int + i]
            == after.take(after.len() as int - 8)[(at * 4) as int + i]);
    }
}
proof fn spliced_word_retains_other_slot(raw: Seq<u8>, changed: nat, other: nat, number: u32)
    requires (changed + 1) * 4 <= raw.len(), (other + 1) * 4 <= raw.len(), changed != other,
    ensures bytes::le32(bytes::splice(raw, (changed * 4) as int, bytes::encoded_le(number)), (other * 4) as int)
        == bytes::le32(raw, (other * 4) as int),
{
    assert forall|i: int| 0 <= i < 4 implies
        bytes::splice(raw, (changed * 4) as int, bytes::encoded_le(number))[(other * 4) as int + i]
            == raw[(other * 4) as int + i] by {
        bytes::splice_frame(raw, (changed * 4) as int, bytes::encoded_le(number), (other * 4) as int + i);
    }
}
proof fn inserting_an_absent_word_preserves_unique(before: BlockView, after: BlockView, changed: nat, number: u32)
    requires unique(before), slot_frame(before, after, changed, number),
        forall|i: nat| i < capacity_for(before.raw) && i != changed ==> #[trigger] slot(before, i) != number,
    ensures unique(after),
{
    assert forall|i: nat, j: nat| i < j < capacity_for(after.raw) && slot(after, i) != 0
        implies #[trigger] slot(after, i) != slot(after, j) by {
        if i != changed && j != changed { assert(slot(before, i) != slot(before, j)); }
    }
}

fn seal_raw(raw: &mut Vec<u8>, physical: u64, seed: u32, metadata: bool)
    requires block_size::accepted(old(raw).len() as nat),
    ensures final(raw).len() == old(raw).len(),
        final(raw)@.take(old(raw).len() as int - 8) == old(raw)@.take(old(raw).len() as int - 8),
        bytes::le32(final(raw)@, final(raw).len() as int - 8) == MAGIC,
        metadata ==> bytes::le32(final(raw)@, final(raw).len() as int - 4) == checksum_value(final(raw)@, physical, seed),
        !metadata ==> final(raw)@.subrange(final(raw).len() as int - 4, final(raw).len() as int)
            == old(raw)@.subrange(old(raw).len() as int - 4, old(raw).len() as int),
{
    let length = raw.len();
    write32(raw, length - 8, MAGIC);
    if metadata {
        let checksum = calculate_checksum(&raw[..], physical, seed).unwrap();
        write32(raw, length - 4, checksum);
    }
}

/// A private validated block. Updates consume its exact current bytes.
pub struct Block {
    raw: Vec<u8>, physical: u64, seed: u32, metadata: bool, inodes: u32,
}
impl Block {
    pub closed spec fn view(&self) -> BlockView {
        BlockView { raw: self.raw@, physical: self.physical, seed: self.seed, metadata: self.metadata, inodes: self.inodes }
    }
    pub open spec fn wf(&self) -> bool { block_valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn bytes(&self) -> (r: &[u8]) ensures r@ == self.view().raw { &self.raw }
    pub fn physical(&self) -> (r: u64) ensures r == self.view().physical { self.physical }
    pub fn capacity(&self) -> (r: usize)
        ensures self.wf(), r == capacity_for(self.view().raw), 254 <= r <= 16382,
    { proof { use_type_invariant(self); }
        if self.raw.len() >= TAIL_BYTES { (self.raw.len() - TAIL_BYTES) / 4 } else { 0 }
    }
    pub fn inode_limit(&self) -> (r: u32) ensures r == self.view().inodes { self.inodes }
    pub fn at(&self, slot: usize) -> (r: Option<u32>)
        ensures self.wf(), match r {
            Some(value) => slot < capacity_for(self.view().raw) && value == crate::orphan_file::slot(self.view(), slot as nat) && value <= self.view().inodes,
            None => slot >= capacity_for(self.view().raw),
        },
    { proof { use_type_invariant(self); }
        if slot >= self.capacity() { return None; }
        bytes::read_le32(&self.raw, slot * 4)
    }
    pub fn free_entries(&self) -> (r: usize)
        ensures self.wf(), r == empty_prefix(self.view(), capacity_for(self.view().raw)),
            r <= capacity_for(self.view().raw),
            r == 0 <==> forall|i: nat| i < capacity_for(self.view().raw) ==> #[trigger] slot(self.view(), i) != 0,
    {
        proof { use_type_invariant(self); }
        let count = self.capacity();
        proof { reveal(empty_prefix); }
        let mut i = 0usize; let mut free = 0usize;
        while i < count
            invariant self.wf(), i <= count, free <= i, count == capacity_for(self.view().raw),
                free as nat == empty_prefix(self.view(), i as nat),
            decreases count - i,
        {
            if self.at(i) == Some(0) { free += 1; }
            proof { reveal(empty_prefix); }
            i += 1;
        }
        proof { empty_prefix_facts(self.view(), count as nat); }
        free
    }
    pub fn find(&self, number: u32) -> (r: Option<usize>)
        ensures self.wf(), match r {
            Some(i) => 0 < number <= self.view().inodes && i < capacity_for(self.view().raw) && slot(self.view(), i as nat) == number
                && forall|j: nat| j < i ==> #[trigger] slot(self.view(), j) != number,
            None => 0 < number <= self.view().inodes ==> forall|j: nat| j < capacity_for(self.view().raw) ==> #[trigger] slot(self.view(), j) != number,
        },
    { proof { use_type_invariant(self); }
        if number == 0 || number > self.inodes { return None; }
        let count = self.capacity();
        let mut i = 0usize;
        while i < count
            invariant self.wf(), i <= count, count == capacity_for(self.view().raw), 0 < number <= self.view().inodes,
                forall|j: nat| j < i ==> #[trigger] slot(self.view(), j) != number,
            decreases count - i,
        {
            if self.at(i) == Some(number) { return Some(i); }
            i += 1;
        }
        None
    }
    /// Move the raw bytes out of their invariant-bearing owner before editing,
    /// then construct the owner only after resealing its exact new image.
    fn updated(self, at: usize, number: u32) -> (r: Self)
        requires self.wf(), at < capacity_for(self.view().raw), number <= self.view().inodes,
        ensures r.wf(), slot_frame(self.view(), r.view(), at as nat, number),
    {
        proof { use_type_invariant(&self); }
        let ghost before = self.view();
        let Block { mut raw, physical, seed, metadata, inodes } = self;
        write32(&mut raw, at * 4, number);
        let ghost edited = raw@;
        proof {
            assert(edited.subrange(edited.len() as int - 4, edited.len() as int)
                =~= before.raw.subrange(before.raw.len() as int - 4, before.raw.len() as int));
            assert forall|j: nat| j < capacity_for(before.raw) && j != at implies
                bytes::le32(edited, (j * 4) as int) == bytes::le32(before.raw, (j * 4) as int) by {
                spliced_word_retains_other_slot(before.raw, at as nat, j, number);
            }
            assert forall|j: nat| j < capacity_for(before.raw) implies bytes::le32(edited, (j * 4) as int) <= inodes by {
                if j != at {
                    spliced_word_retains_other_slot(before.raw, at as nat, j, number);
                    assert(slot(before, j) <= inodes);
                }
            }
        }
        seal_raw(&mut raw, physical, seed, metadata);
        proof {
            assert forall|j: nat| j < capacity_for(before.raw) implies
                bytes::le32(raw@, (j * 4) as int) == bytes::le32(edited, (j * 4) as int) by {
                prefix_retains_word(edited, raw@, j);
            }
            assert(valid_raw(raw@, physical, seed, metadata, inodes));
        }
        let result = Block { raw, physical, seed, metadata, inodes };
        proof { assert(slot_frame(before, result.view(), at as nat, number)); }
        result
    }
    /// Idempotent insertion retains an existing matching slot.
    pub fn insert(mut self, number: u32) -> (r: Result<(Self, usize), (Self, Error)>)
        ensures self.wf(), match r {
            Ok((after, i)) => after.wf() && 0 < number <= self.view().inodes
                && slot_frame(self.view(), after.view(), i as nat, number)
                && (slot(self.view(), i as nat) == 0 || slot(self.view(), i as nat) == number)
                && (unique(self.view()) ==> unique(after.view())),
            Err((after, _)) => after.wf() && after.view() == self.view(),
        },
    { proof { use_type_invariant(&self); }
        let ghost before = self.view();
        if number == 0 || number > self.inodes { return Err((self, Error::Inode)); }
        if let Some(slot) = self.find(number) { return Ok((self, slot)); }
        let count = self.capacity();
        let mut i = 0usize;
        while i < count
            invariant self.wf(), i <= count, count == capacity_for(self.view().raw), 0 < number <= self.view().inodes,
                forall|j: nat| j < capacity_for(self.view().raw) ==> #[trigger] crate::orphan_file::slot(self.view(), j) != number,
            decreases count - i,
        {
            if self.at(i) == Some(0) {
                let after = self.updated(i, number);
                proof { if unique(before) { inserting_an_absent_word_preserves_unique(before, after.view(), i as nat, number); } }
                return Ok((after, i));
            }
            i += 1;
        }
        Err((self, Error::Full))
    }
    /// Compare the expected current inode before removing its source slot.
    pub fn remove(mut self, slot: usize, expected: u32) -> (r: Result<Self, (Self, Error)>)
        ensures self.wf(), match r {
            Ok(after) => after.wf() && 0 < expected <= self.view().inodes
                && crate::orphan_file::slot(self.view(), slot as nat) == expected
                && slot_frame(self.view(), after.view(), slot as nat, 0)
                && (unique(self.view()) ==> unique(after.view())),
            Err((after, _)) => after.wf() && after.view() == self.view(),
        },
    { proof { use_type_invariant(&self); }
        let ghost before = self.view();
        if expected == 0 || expected > self.inodes { return Err((self, Error::Inode)); }
        match self.at(slot) {
            None => { return Err((self, Error::Address)); },
            Some(value) => {
                if value != expected { return Err((self, Error::Stale)); }
            },
        }
        let after = self.updated(slot, 0);
        proof { if unique(before) { clearing_an_exact_slot_preserves_uniqueness(before, after.view(), slot as nat); } }
        Ok(after)
    }
    /// CAS-style insertion for callers reserving a particular free slot.
    pub fn insert_at(mut self, slot: usize, number: u32) -> (r: Result<Self, (Self, Error)>)
        ensures self.wf(), match r {
            Ok(after) => after.wf() && 0 < number <= self.view().inodes
                && slot_frame(self.view(), after.view(), slot as nat, number)
                && (crate::orphan_file::slot(self.view(), slot as nat) == 0
                    || crate::orphan_file::slot(self.view(), slot as nat) == number)
                && (unique(self.view()) ==> unique(after.view())),
            Err((after, _)) => after.wf() && after.view() == self.view(),
        },
    { proof { use_type_invariant(&self); }
        let ghost before = self.view();
        if number == 0 || number > self.inodes { return Err((self, Error::Inode)); }
        match self.at(slot) {
            None => { return Err((self, Error::Address)); },
            Some(value) => {
                if value == number { return Ok(self); }
                if value != 0 { return Err((self, Error::Occupied)); }
            },
        }
        if self.find(number).is_some() { return Err((self, Error::Occupied)); }
        let after = self.updated(slot, number);
        proof { if unique(before) { inserting_an_absent_word_preserves_unique(before, after.view(), slot as nat, number); } }
        Ok(after)
    }
}

pub fn parse(raw: &[u8], physical: u64, fs_blocks: u64, seed: u32,
    metadata: bool, inodes: u32) -> (r: Result<Block, Error>)
    ensures (r is Ok) <==> parse_admissible(raw@, physical, fs_blocks, seed, metadata, inodes),
        match r {
        Ok(block) => block.wf() && block.view() == (BlockView { raw: raw@, physical, seed, metadata, inodes })
            && physical < fs_blocks,
        Err(_) => true,
    },
{
    if !block_size::valid(raw.len()) || raw.len() < TAIL_BYTES || inodes == 0 {
        return Err(Error::Geometry);
    }
    if physical >= fs_blocks { return Err(Error::Address); }
    let len = raw.len();
    if bytes::read_le32(raw, len - TAIL_BYTES) != Some(MAGIC) { return Err(Error::Magic); }
    if metadata {
        let actual = match calculate_checksum(raw, physical, seed) {
            Some(value) => value, None => { return Err(Error::Geometry); }
        };
        if bytes::read_le32(raw, len - 4) != Some(actual) { return Err(Error::Checksum); }
    }
    let slots = (len - TAIL_BYTES) / 4;
    let mut i = 0usize;
    while i < slots
        invariant i <= slots, slots == (len - TAIL_BYTES) / 4, len == raw.len(), len >= TAIL_BYTES,
            forall|j: int| 0 <= j < i ==> #[trigger] bytes::le32(raw@, j * 4) <= inodes,
        decreases slots - i,
    {
        match bytes::read_le32(raw, i * 4) {
            Some(number) => { if number > inodes { return Err(Error::Inode); } },
            None => { return Err(Error::Geometry); },
        }
        i += 1;
    }
    Ok(Block { raw: copy(raw), physical, seed, metadata, inodes })
}

pub fn empty(block_bytes: usize, physical: u64, fs_blocks: u64, seed: u32,
    metadata: bool, inodes: u32) -> (r: Result<Block, Error>)
    ensures (r is Ok) <==> block_size::accepted(block_bytes as nat) && inodes > 0 && physical < fs_blocks,
        match r {
        Ok(block) => block.wf() && block.view().raw.len() == block_bytes && block.view().physical == physical
            && block.view().seed == seed && block.view().metadata == metadata && block.view().inodes == inodes
            && physical < fs_blocks && unique(block.view())
            && (!metadata ==> bytes::le32(block.view().raw, block_bytes as int - 4) == 0)
            && forall|i: nat| i < capacity_for(block.view().raw) ==> #[trigger] slot(block.view(), i) == 0,
        Err(_) => true,
    },
{
    if !block_size::valid(block_bytes) || block_bytes < TAIL_BYTES || inodes == 0 {
        return Err(Error::Geometry);
    }
    if physical >= fs_blocks { return Err(Error::Address); }
    let mut raw = Vec::new();
    let mut i = 0usize;
    while i < block_bytes
        invariant i <= block_bytes, raw.len() == i, forall|j: int| 0 <= j < i ==> #[trigger] raw@[j] == 0,
        decreases block_bytes - i,
    { raw.push(0); i += 1; }
    seal_raw(&mut raw, physical, seed, metadata);
    Ok(Block { raw, physical, seed, metadata, inodes })
}

pub const MAX_FILE_BLOCKS: usize = 512;
#[derive(Clone, Copy)]
pub struct Location { physical: u64, slot: usize }
impl Location {
    pub closed spec fn view(&self) -> LocationView { LocationView { physical: self.physical, slot: self.slot } }
    pub fn location_physical(&self) -> (r: u64) ensures r == self.view().physical { self.physical }
    pub fn location_slot(&self) -> (r: usize) ensures r == self.view().slot { self.slot }
}

pub struct LocationView { pub physical: u64, pub slot: usize }
pub struct FileView { pub blocks: Seq<BlockView>, pub inodes: u32, pub seed: u32, pub metadata: bool }
pub open spec fn views(blocks: Seq<Block>) -> Seq<BlockView> { blocks.map_values(|block: Block| block.view()) }
pub open spec fn globally_unique(blocks: Seq<BlockView>) -> bool {
    forall|a: int, b: int, i: nat, j: nat|
        0 <= a <= b < blocks.len() && i < capacity_for(blocks[a].raw) && j < capacity_for(blocks[b].raw)
            && (a < b || i < j) && slot(blocks[a], i) != 0
        ==> #[trigger] slot(blocks[a], i) != #[trigger] slot(blocks[b], j)
}
pub open spec fn file_valid(v: FileView) -> bool {
    &&& v.inodes > 0 && v.blocks.len() <= 512
    &&& forall|i: int| 0 <= i < v.blocks.len() ==> block_valid(#[trigger] v.blocks[i])
        && v.blocks[i].inodes == v.inodes && v.blocks[i].seed == v.seed && v.blocks[i].metadata == v.metadata
        && (i > 0 ==> v.blocks[i].raw.len() == v.blocks[0].raw.len())
    &&& forall|i: int, j: int| 0 <= i < j < v.blocks.len() ==> (#[trigger] v.blocks[i]).physical != (#[trigger] v.blocks[j]).physical
    &&& globally_unique(v.blocks)
}
pub open spec fn contains_at(v: FileView, location: LocationView, number: u32) -> bool {
    exists|i: int| 0 <= i < v.blocks.len() && (#[trigger] v.blocks[i]).physical == location.physical
        && location.slot < capacity_for(v.blocks[i].raw) && slot(v.blocks[i], location.slot as nat) == number
}
pub open spec fn file_slot_frame(before: FileView, after: FileView, location: LocationView, number: u32) -> bool {
    &&& before.inodes == after.inodes && before.seed == after.seed && before.metadata == after.metadata
    &&& before.blocks.len() == after.blocks.len()
    &&& exists|changed: int| 0 <= changed < before.blocks.len()
        && (#[trigger] before.blocks[changed]).physical == location.physical
        && slot_frame(before.blocks[changed], after.blocks[changed], location.slot as nat, number)
        && forall|i: int| 0 <= i < before.blocks.len() && i != changed ==> before.blocks[i] == #[trigger] after.blocks[i]
}

/// One owned orphan-file image collection. Physical aliases and profile
/// mismatches are rejected at construction. This is not an allocation token.
pub struct File { blocks: Vec<Block>, inodes: u32, seed: u32, metadata: bool }
fn duplicate_block(block: &Block) -> (r: Block)
    ensures block.wf(), r.wf(), r.view() == block.view(),
{ proof { use_type_invariant(block); }
    Block { raw: copy(&block.raw), physical: block.physical, seed: block.seed,
        metadata: block.metadata, inodes: block.inodes }
}
impl File {
    pub closed spec fn view(&self) -> FileView {
        FileView { blocks: views(self.blocks@), inodes: self.inodes, seed: self.seed, metadata: self.metadata }
    }
    pub open spec fn wf(&self) -> bool { file_valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn file_len(&self) -> (r: usize) ensures r == self.view().blocks.len() { self.blocks.len() }
    pub fn file_block(&self, ordinal: usize) -> (r: Option<&Block>)
        ensures self.wf(), match r {
            Some(block) => ordinal < self.view().blocks.len() && block.wf() && block.view() == self.view().blocks[ordinal as int],
            None => ordinal >= self.view().blocks.len(),
        },
    { proof { use_type_invariant(self); }
        if ordinal >= self.blocks.len() { None } else { Some(&self.blocks[ordinal]) }
    }
    /// Cold/reconciliation lookup. A runtime inode cache retains Location
    /// after insertion, so ordinary removal need not rediscover it.
    pub fn file_find(&self, number: u32) -> (r: Option<Location>)
        ensures self.wf(), match r {
            Some(location) => 0 < number <= self.view().inodes && contains_at(self.view(), location.view(), number)
                && forall|other: LocationView| contains_at(self.view(), other, number) ==> other == location.view(),
            None => 0 < number <= self.view().inodes ==> forall|location: LocationView| !contains_at(self.view(), location, number),
        },
    { proof { use_type_invariant(self); }
        if number == 0 || number > self.inodes { return None; }
        let mut i = 0usize;
        while i < self.blocks.len()
            invariant i <= self.blocks.len(),
            decreases self.blocks.len() - i,
        {
            if let Some(slot) = self.blocks[i].find(number) {
                return Some(Location { physical: self.blocks[i].physical, slot });
            }
            i += 1;
        }
        None
    }
    /// Round-robin placement; Full permits caller fallback to the legacy
    /// chain in the same operation's journal closure. Existing entries are
    /// retained idempotently. Candidates are copied before any modification.
    pub fn file_insert(mut self, number: u32, start: usize)
        -> (r: Result<(Self, Location), (Self, Error)>)
        ensures self.wf(), match r {
            Ok((after, location)) => after.wf() && 0 < number <= self.view().inodes
                && contains_at(after.view(), location.view(), number)
                && (after.view() == self.view() || file_slot_frame(self.view(), after.view(), location.view(), number)),
            Err((after, _)) => after.wf() && after.view() == self.view(),
        },
    { proof { use_type_invariant(&self); }
        if number == 0 || number > self.inodes { return Err((self, Error::Inode)); }
        if let Some(location) = self.file_find(number) { return Ok((self, location)); }
        let length = self.blocks.len();
        if length == 0 { return Err((self, Error::Full)); }
        let mut ordinal = start % length;
        let mut checked = 0usize;
        while checked < length
            invariant checked <= length, ordinal < length, length == self.blocks.len(),
            decreases length - checked,
        {
            if self.blocks[ordinal].free_entries() != 0 {
                let candidate = duplicate_block(&self.blocks[ordinal]);
                match candidate.insert(number) {
                    Ok((block, slot)) => {
                        let location = Location { physical: block.physical, slot };
                        let File { mut blocks, inodes, seed, metadata } = self;
                        blocks.set(ordinal, block);
                        return Ok((File { blocks, inodes, seed, metadata }, location));
                    },
                    Err((_, error)) => { return Err((self, error)); },
                }
            }
            checked += 1;
            ordinal = if ordinal + 1 == length { 0 } else { ordinal + 1 };
        }
        Err((self, Error::Full))
    }
    pub fn file_remove(mut self, location: Location, expected: u32) -> (r: Result<Self, (Self, Error)>)
        ensures self.wf(), match r {
            Ok(after) => after.wf() && 0 < expected <= self.view().inodes
                && contains_at(self.view(), location.view(), expected)
                && file_slot_frame(self.view(), after.view(), location.view(), 0),
            Err((after, _)) => after.wf() && after.view() == self.view(),
        },
    { proof { use_type_invariant(&self); }
        if expected == 0 || expected > self.inodes { return Err((self, Error::Inode)); }
        let mut i = 0usize;
        while i < self.blocks.len()
            invariant i <= self.blocks.len(),
            decreases self.blocks.len() - i,
        {
            if self.blocks[i].physical == location.physical {
                let candidate = duplicate_block(&self.blocks[i]);
                match candidate.remove(location.slot, expected) {
                    Ok(block) => {
                        let File { mut blocks, inodes, seed, metadata } = self;
                        blocks.set(i, block); return Ok(File { blocks, inodes, seed, metadata });
                    },
                    Err((_, error)) => { return Err((self, error)); },
                }
            }
            i += 1;
        }
        Err((self, Error::Address))
    }
}

#[verifier::opaque]
pub open spec fn occupied_block_words(block: BlockView, count: nat) -> Seq<u32>
    recommends count <= capacity_for(block.raw),
    decreases count,
{
    if count == 0 { Seq::empty() } else {
        let earlier = occupied_block_words(block, (count - 1) as nat);
        let number = slot(block, (count - 1) as nat);
        if number == 0 { earlier } else { earlier.push(number) }
    }
}
#[verifier::opaque]
pub open spec fn occupied_file_words(blocks: Seq<BlockView>, count: nat) -> Seq<u32>
    recommends count <= blocks.len(),
    decreases count,
{
    if count == 0 { Seq::empty() } else {
        let block = blocks[count as int - 1];
        occupied_file_words(blocks, (count - 1) as nat) + occupied_block_words(block, capacity_for(block.raw))
    }
}
proof fn block_word_membership_is_exact(block: BlockView, count: nat, number: u32)
    requires count <= capacity_for(block.raw),
    ensures occupied_block_words(block, count).contains(number)
        <==> number != 0 && exists|i: nat| i < count && #[trigger] slot(block, i) == number,
    decreases count,
{
    reveal(occupied_block_words);
    if count > 0 {
        block_word_membership_is_exact(block, (count - 1) as nat, number);
        let last = slot(block, (count - 1) as nat);
        if exists|i: nat| i < count && #[trigger] slot(block, i) == number {
            let i = choose|i: nat| i < count && #[trigger] slot(block, i) == number;
            if i < count - 1 { assert(occupied_block_words(block, (count - 1) as nat).contains(number) <==> number != 0); }
        }
    }
}
proof fn file_word_membership_is_exact(blocks: Seq<BlockView>, count: nat, number: u32)
    requires count <= blocks.len(),
    ensures occupied_file_words(blocks, count).contains(number)
        <==> number != 0 && exists|b: int, i: nat| 0 <= b < count
            && i < capacity_for(blocks[b].raw) && #[trigger] slot(blocks[b], i) == number,
    decreases count,
{
    reveal(occupied_file_words);
    if count > 0 {
        file_word_membership_is_exact(blocks, (count - 1) as nat, number);
        let block = blocks[count as int - 1];
        block_word_membership_is_exact(block, capacity_for(block.raw), number);
        if exists|b: int, i: nat| 0 <= b < count
            && i < capacity_for(blocks[b].raw) && #[trigger] slot(blocks[b], i) == number {
            let (b, i) = choose|pair: (int, nat)| 0 <= pair.0 < count
                && pair.1 < capacity_for(blocks[pair.0].raw) && #[trigger] slot(blocks[pair.0], pair.1) == number;
            if b < count - 1 { assert(occupied_file_words(blocks, (count - 1) as nat).contains(number) <==> number != 0); }
        }
    }
}

proof fn concatenation_is_duplicate_free_exactly_when_parts_are_disjoint(left: Seq<u32>, right: Seq<u32>)
    ensures (left + right).no_duplicates() <==> left.no_duplicates() && right.no_duplicates()
        && forall|number: u32| left.contains(number) ==> !right.contains(number),
{
    if (left + right).no_duplicates() {
        assert forall|i: int, j: int| 0 <= i < j < left.len() implies left[i] != left[j] by {
            assert((left + right)[i] != (left + right)[j]);
        }
        assert forall|i: int, j: int| 0 <= i < j < right.len() implies right[i] != right[j] by {
            assert((left + right)[left.len() + i] != (left + right)[left.len() + j]);
        }
        assert forall|number: u32| left.contains(number) implies !right.contains(number) by {
            if right.contains(number) {
                let i = choose|i: int| 0 <= i < left.len() && left[i] == number;
                let j = choose|j: int| 0 <= j < right.len() && right[j] == number;
                assert((left + right)[i] != (left + right)[left.len() + j]);
            }
        }
    } else if left.no_duplicates() && right.no_duplicates()
        && forall|number: u32| left.contains(number) ==> !right.contains(number) {
        assert forall|i: int, j: int| 0 <= i < j < left.len() + right.len()
            implies (left + right)[i] != (left + right)[j] by {
            if j < left.len() { assert(left[i] != left[j]); }
            else if i >= left.len() { assert(right[i - left.len()] != right[j - left.len()]); }
            else {
                assert(left.contains(left[i]));
                assert(right.contains(right[j - left.len()]));
                assert(left[i] != right[j - left.len()]);
            }
        }
    }
}
pub open spec fn block_prefix_unique(block: BlockView, count: nat) -> bool {
    forall|i: nat, j: nat| i < j < count && slot(block, i) != 0 ==> #[trigger] slot(block, i) != #[trigger] slot(block, j)
}
proof fn block_word_uniqueness_is_exact(block: BlockView, count: nat)
    requires count <= capacity_for(block.raw),
    ensures occupied_block_words(block, count).no_duplicates() <==> block_prefix_unique(block, count),
    decreases count,
{
    reveal(occupied_block_words);
    if count > 0 {
        block_word_uniqueness_is_exact(block, (count - 1) as nat);
        let previous = occupied_block_words(block, (count - 1) as nat);
        let last = slot(block, (count - 1) as nat);
        if last != 0 {
            block_word_membership_is_exact(block, (count - 1) as nat, last);
            concatenation_is_duplicate_free_exactly_when_parts_are_disjoint(previous, seq![last]);
            assert(previous.push(last) =~= previous + seq![last]);
            if block_prefix_unique(block, count) {
                assert(block_prefix_unique(block, (count - 1) as nat));
                assert(!previous.contains(last)) by {
                    if previous.contains(last) {
                        let i = choose|i: nat| i < count - 1 && #[trigger] slot(block, i) == last;
                        assert(slot(block, i) != slot(block, (count - 1) as nat));
                    }
                }
            } else if previous.no_duplicates() && !previous.contains(last) {
                assert forall|i: nat, j: nat| i < j < count && slot(block, i) != 0
                    implies #[trigger] slot(block, i) != #[trigger] slot(block, j) by {
                    if j < count - 1 { assert(slot(block, i) != slot(block, j)); }
                    else if slot(block, i) == last {
                        assert(exists|k: nat| k < count - 1 && #[trigger] slot(block, k) == last);
                        assert(previous.contains(last));
                    }
                }
            }
        } else {
            if block_prefix_unique(block, (count - 1) as nat) {
                assert forall|i: nat, j: nat| i < j < count && slot(block, i) != 0
                    implies #[trigger] slot(block, i) != #[trigger] slot(block, j) by {
                    if j < count - 1 { assert(slot(block, i) != slot(block, j)); }
                }
            } else if block_prefix_unique(block, count) {
                assert(block_prefix_unique(block, (count - 1) as nat));
            }
        }
    }
}
proof fn file_word_uniqueness_is_exact(blocks: Seq<BlockView>, count: nat)
    requires count <= blocks.len(),
    ensures occupied_file_words(blocks, count).no_duplicates() <==> globally_unique(blocks.take(count as int)),
    decreases count,
{
    reveal(occupied_file_words);
    if count > 0 {
        file_word_uniqueness_is_exact(blocks, (count - 1) as nat);
        let earlier = occupied_file_words(blocks, (count - 1) as nat);
        let last = blocks[count as int - 1];
        let words = occupied_block_words(last, capacity_for(last.raw));
        block_word_uniqueness_is_exact(last, capacity_for(last.raw));
        concatenation_is_duplicate_free_exactly_when_parts_are_disjoint(earlier, words);
        if globally_unique(blocks.take(count as int)) {
            assert(globally_unique(blocks.take(count as int - 1)));
            assert(block_prefix_unique(last, capacity_for(last.raw)));
            assert forall|number: u32| earlier.contains(number) implies !words.contains(number) by {
                file_word_membership_is_exact(blocks, (count - 1) as nat, number);
                block_word_membership_is_exact(last, capacity_for(last.raw), number);
                if words.contains(number) {
                    let (b, i) = choose|pair: (int, nat)| 0 <= pair.0 < count - 1
                        && pair.1 < capacity_for(blocks[pair.0].raw) && #[trigger] slot(blocks[pair.0], pair.1) == number;
                    let j = choose|j: nat| j < capacity_for(last.raw) && #[trigger] slot(last, j) == number;
                    assert(slot(blocks[b], i) != slot(blocks[count as int - 1], j));
                }
            }
        } else if earlier.no_duplicates() && words.no_duplicates()
            && forall|number: u32| earlier.contains(number) ==> !words.contains(number) {
            assert forall|a: int, b: int, i: nat, j: nat|
                0 <= a <= b < count && i < capacity_for(blocks[a].raw) && j < capacity_for(blocks[b].raw)
                    && (a < b || i < j) && slot(blocks[a], i) != 0
                implies #[trigger] slot(blocks[a], i) != #[trigger] slot(blocks[b], j) by {
                if b < count - 1 {
                    assert(slot(blocks[a], i) != slot(blocks[b], j));
                } else if a == b {
                    assert(slot(last, i) != slot(last, j));
                } else if slot(blocks[a], i) == slot(blocks[b], j) {
                    let number = slot(blocks[a], i);
                    file_word_membership_is_exact(blocks, (count - 1) as nat, number);
                    block_word_membership_is_exact(last, capacity_for(last.raw), number);
                    assert(earlier.contains(number) && words.contains(number));
                }
            }
        }
    }
}

pub open spec fn ordered_window(values: Seq<u32>, first: nat, end: nat) -> bool {
    first <= end <= values.len()
        && forall|i: int, j: int| first <= i < j < end ==> #[trigger] values[i] <= #[trigger] values[j]
}
pub open spec fn ordered_runs(values: Seq<u32>, width: nat) -> bool {
    width > 0 && forall|run: nat| run * width < values.len() ==> #[trigger] ordered_window(values,
        run * width, if (run + 1) * width < values.len() { (run + 1) * width } else { values.len() })
}
proof fn an_ordered_window_can_append_a_larger_word(before: Seq<u32>, after: Seq<u32>, first: nat, end: nat, number: u32)
    requires ordered_window(before, first, end), first <= end < after.len(),
        before.len() == after.len(), after.take(end as int) == before.take(end as int),
        after[end as int] == number,
        forall|i: int| first <= i < end ==> #[trigger] before[i] <= number,
    ensures ordered_window(after, first, end + 1),
{
    assert forall|i: int, j: int| first <= i < j < end + 1 implies #[trigger] after[i] <= #[trigger] after[j] by {
        if j < end { assert(before[i] <= before[j]); }
    }
}
proof fn preserving_a_prefix_preserves_its_ordered_windows(before: Seq<u32>, after: Seq<u32>, first: nat, end: nat, prefix: nat)
    requires ordered_window(before, first, end), end <= prefix <= before.len(),
        before.len() == after.len(), before.take(prefix as int) == after.take(prefix as int),
    ensures ordered_window(after, first, end),
{
    assert forall|i: int, j: int| first <= i < j < end implies #[trigger] after[i] <= #[trigger] after[j] by {
        assert(before.take(prefix as int)[i] == after.take(prefix as int)[i]);
        assert(before.take(prefix as int)[j] == after.take(prefix as int)[j]);
    }
}

proof fn aligned_pair_of_runs_is_ordered(values: Seq<u32>, width: nat, run: nat, first: nat, middle: nat, end: nat)
    requires ordered_runs(values, width), first == run * (2 * width), first < values.len(),
        middle == if first + width < values.len() { first + width } else { values.len() },
        end == if middle + width < values.len() { middle + width } else { values.len() },
    ensures ordered_window(values, first, middle), ordered_window(values, middle, end),
{
    assert((2 * run) * width == first) by (nonlinear_arith);
    assert((2 * run + 1) * width == first + width) by (nonlinear_arith);
    assert((2 * run + 2) * width == first + 2 * width) by (nonlinear_arith);
    if middle < values.len() {
        assert(middle == (2 * run + 1) * width);
        assert(end == if (2 * run + 2) * width < values.len() { (2 * run + 2) * width } else { values.len() });
    }
}

pub open spec fn words_ordered(values: Seq<u32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < values.len() ==> #[trigger] values[i] <= #[trigger] values[j]
}
proof fn unequal_neighbors_in_an_ordered_sequence_are_distinct(values: Seq<u32>, left: int, right: int)
    requires words_ordered(values), 0 <= left < right < values.len(),
        forall|i: int| 1 <= i < values.len() ==> #[trigger] values[i - 1] != values[i],
    ensures values[left] < values[right],
{
    assert(values[right - 1] <= values[right]);
    assert(values[right - 1] != values[right]);
    if left < right - 1 { assert(values[left] <= values[right - 1]); }
}
proof fn ordered_neighbor_scan_establishes_no_duplicates(values: Seq<u32>)
    requires words_ordered(values),
        forall|i: int| 1 <= i < values.len() ==> #[trigger] values[i - 1] != values[i],
    ensures values.no_duplicates(),
{
    assert forall|left: int, right: int| 0 <= left < right < values.len()
        implies values[left] != values[right] by {
        unequal_neighbors_in_an_ordered_sequence_are_distinct(values, left, right);
    }
}
proof fn permutation_preserves_duplicate_status(before: Seq<u32>, after: Seq<u32>)
    requires before.to_multiset() == after.to_multiset(),
    ensures before.no_duplicates() <==> after.no_duplicates(),
{
    if before.no_duplicates() {
        before.lemma_multiset_has_no_duplicates();
        after.lemma_multiset_has_no_duplicates_conv();
    } else if after.no_duplicates() {
        after.lemma_multiset_has_no_duplicates();
        before.lemma_multiset_has_no_duplicates_conv();
    }
}

/// Validate the one-record-per-orphan property before constructing a whole
/// file. The block codec remains structural so damaged sources can be
/// diagnosed separately. Sort only occupied words: O(slots + occupied log occupied).
fn distinct_file_entries(blocks: &[Block]) -> (r: bool)
    requires blocks.len() <= MAX_FILE_BLOCKS, forall|i: int| 0 <= i < blocks.len() ==> blocks[i].wf(),
    ensures r <==> globally_unique(views(blocks@)),
{
    let mut values: Vec<u32> = Vec::new();
    let ghost source_blocks = views(blocks@);
    proof { reveal(occupied_file_words); }
    let mut i = 0usize;
    while i < blocks.len()
        invariant i <= blocks.len(), blocks.len() <= MAX_FILE_BLOCKS,
            values.len() <= i * 16382, source_blocks == views(blocks@),
            values@ == occupied_file_words(source_blocks, i as nat),
        decreases blocks.len() - i,
    {
        let mut j = 0usize; let capacity = blocks[i].capacity();
        proof { reveal(occupied_block_words); }
        while j < capacity
            invariant j <= capacity <= 16382, i < blocks.len(), blocks.len() <= MAX_FILE_BLOCKS,
                values.len() <= i * 16382 + j, source_blocks == views(blocks@),
                capacity == capacity_for(source_blocks[i as int].raw),
                values@ == occupied_file_words(source_blocks, i as nat)
                    + occupied_block_words(source_blocks[i as int], j as nat),
            decreases capacity - j,
        {
            let number = match blocks[i].at(j) { Some(value) => value, None => { return false; } };
            let ghost earlier = values@;
            if number != 0 { values.push(number); }
            proof {
                reveal(occupied_block_words);
                assert(values@ == occupied_file_words(source_blocks, i as nat)
                    + occupied_block_words(source_blocks[i as int], (j + 1) as nat));
            }
            j += 1;
        }
        proof {
            reveal(occupied_file_words);
            assert(values@ == occupied_file_words(source_blocks, (i + 1) as nat));
        }
        i += 1;
    }
    let ghost unsorted = values@;
    proof {
        file_word_uniqueness_is_exact(source_blocks, source_blocks.len());
        assert(unsorted.no_duplicates() <==> globally_unique(source_blocks));
    }
    let length = values.len(); let mut other: Vec<u32> = Vec::new(); i = 0;
    while i < length
        invariant i <= length, other.len() == i,
        decreases length - i,
    { other.push(0); i += 1; }
    let mut width = 1usize;
    proof { assert(ordered_runs(values@, 1)); }
    while width < length
        invariant ordered_runs(values@, width as nat), 0 < width, values.len() == length, other.len() == length, length <= 8387584,
            values@.to_multiset() == unsorted.to_multiset(),
        decreases length - width,
    {
        let ghost run_width: nat = 2nat * (width as nat);
        let mut left = 0usize;
        let ghost mut completed_runs = 0nat;
        while left < length
            invariant ordered_runs(values@, width as nat), left <= length,
                left as nat == if completed_runs * (run_width) < length { completed_runs * (run_width) } else { length as nat },
                forall|run: nat| run < completed_runs ==> ordered_window(other@, run * (run_width),
                    if (run + 1) * (run_width) < length { (run + 1) * (run_width) } else { length as nat }), 0 < width, values.len() == length, other.len() == length, length <= 8387584,
                values@.to_multiset() == unsorted.to_multiset(),
                other@.take(left as int).to_multiset() == values@.take(left as int).to_multiset(),
            decreases length - left,
        {
            let middle = left + if width < length - left { width } else { length - left };
            let right = middle + if width < length - middle { width } else { length - middle };
            proof {
                aligned_pair_of_runs_is_ordered(values@, width as nat, completed_runs, left as nat, middle as nat, right as nat);
            }
            let mut a = left; let mut b = middle; let mut out = left;
            while out < right
                invariant left <= a <= middle <= b <= right <= length, left <= out <= right,
                    out as int - left as int == (a as int - left as int) + (b as int - middle as int),
                    values.len() == length, other.len() == length,
                    ordered_window(values@, left as nat, middle as nat),
                    ordered_window(values@, middle as nat, right as nat),
                    ordered_window(other@, left as nat, out as nat),
                    out > left ==> forall|p: int| a <= p < middle ==> #[trigger] values@[p] >= other@[out as int - 1],
                    out > left ==> forall|p: int| b <= p < right ==> #[trigger] values@[p] >= other@[out as int - 1],
                    forall|run: nat| run < completed_runs ==> ordered_window(other@, run * (run_width),
                        if (run + 1) * (run_width) < length { (run + 1) * (run_width) } else { length as nat }),
                    other@.take(left as int).to_multiset() == values@.take(left as int).to_multiset(),
                    other@.subrange(left as int, out as int).to_multiset()
                        == values@.subrange(left as int, a as int).to_multiset()
                            .add(values@.subrange(middle as int, b as int).to_multiset()),
                decreases right - out,
            {
                let ghost previous_a = a;
                let ghost previous_b = b;
                let ghost previous_output = other@;
                if a < middle && (b == right || values[a] <= values[b]) {
                    other.set(out, values[a]); a += 1;
                } else { other.set(out, values[b]); b += 1; }
                proof {
                    broadcast use vstd::seq_lib::group_to_multiset_ensures;
                    broadcast use vstd::multiset::group_multiset_axioms;
                    assert(other@.take(left as int) =~= previous_output.take(left as int));
                    assert(other@.take(out as int) =~= previous_output.take(out as int));
                    if a > previous_a {
                        assert(other@.subrange(left as int, out as int + 1)
                            =~= previous_output.subrange(left as int, out as int).push(values@[previous_a as int]));
                        assert(values@.subrange(left as int, a as int)
                            =~= values@.subrange(left as int, previous_a as int).push(values@[previous_a as int]));
                    } else {
                        assert(other@.subrange(left as int, out as int + 1)
                            =~= previous_output.subrange(left as int, out as int).push(values@[previous_b as int]));
                        assert(values@.subrange(middle as int, b as int)
                            =~= values@.subrange(middle as int, previous_b as int).push(values@[previous_b as int]));
                    }
                    let chosen = other@[out as int];
                    assert forall|p: int| left <= p < out implies #[trigger] previous_output[p] <= chosen by {
                        if p < out as int - 1 { assert(previous_output[p] <= previous_output[out as int - 1]); }
                    }
                    an_ordered_window_can_append_a_larger_word(previous_output, other@, left as nat, out as nat, chosen);
                    assert forall|p: int| a <= p < middle implies #[trigger] values@[p] >= chosen by {
                        if a > previous_a { assert(values@[previous_a as int] <= values@[p]); }
                        else {
                            assert(previous_a < middle);
                            assert(values@[previous_b as int] < values@[previous_a as int]);
                            if previous_a < p { assert(values@[previous_a as int] <= values@[p]); }
                        }
                    }
                    assert forall|p: int| b <= p < right implies #[trigger] values@[p] >= chosen by {
                        if b > previous_b { assert(values@[previous_b as int] <= values@[p]); }
                        else {
                            assert(previous_b < right);
                            assert(values@[previous_a as int] <= values@[previous_b as int]);
                            if previous_b < p { assert(values@[previous_b as int] <= values@[p]); }
                        }
                    }
                    assert forall|run: nat| run < completed_runs implies ordered_window(other@, run * (run_width),
                        if (run + 1) * (run_width) < length { (run + 1) * (run_width) } else { length as nat }) by {
                        let first = run * (run_width);
                        let end = if (run + 1) * (run_width) < length { (run + 1) * (run_width) } else { length as nat };
                        assert(end <= left) by (nonlinear_arith);
                        preserving_a_prefix_preserves_its_ordered_windows(previous_output, other@, first, end, left as nat);
                    }
                }
                out += 1;
            }
            proof {
                assert(a == middle && b == right);
                assert(values@.subrange(left as int, right as int)
                    =~= values@.subrange(left as int, middle as int) + values@.subrange(middle as int, right as int));
                vstd::seq_lib::lemma_multiset_commutative(values@.subrange(left as int, middle as int), values@.subrange(middle as int, right as int));
                assert(other@.take(right as int)
                    =~= other@.take(left as int) + other@.subrange(left as int, right as int));
                assert(values@.take(right as int)
                    =~= values@.take(left as int) + values@.subrange(left as int, right as int));
                vstd::seq_lib::lemma_multiset_commutative(other@.take(left as int), other@.subrange(left as int, right as int));
                vstd::seq_lib::lemma_multiset_commutative(values@.take(left as int), values@.subrange(left as int, right as int));
                assert forall|run: nat| run < completed_runs + 1 implies ordered_window(other@, run * (run_width),
                    if (run + 1) * (run_width) < length { (run + 1) * (run_width) } else { length as nat }) by {
                    if run == completed_runs {
                        assert(run * (run_width) == left);
                        assert((run + 1) * (run_width) == left as nat + run_width) by (nonlinear_arith);
                    }
                }
                assert(right as nat == if (completed_runs + 1) * (run_width) < length {
                    (completed_runs + 1) * (run_width)
                } else { length as nat });
                completed_runs = completed_runs + 1;
            }
            left = right;
        }
        proof {
            assert(ordered_runs(other@, run_width)) by {
                assert forall|run: nat| run * (run_width) < length implies ordered_window(other@, run * (run_width),
                    if (run + 1) * (run_width) < length { (run + 1) * (run_width) } else { length as nat }) by {
                    assert(run < completed_runs) by (nonlinear_arith);
                }
            }
        }
        let ghost previous_width = width;
        let old = values; values = other; other = old;
        width = if width > length / 2 { length } else { width * 2 };
        proof {
            if width == length {
                assert(ordered_window(values@, 0, length as nat));
                assert(ordered_runs(values@, width as nat));
            } else { assert(width == 2 * previous_width); }
        }
    }
    proof {
        permutation_preserves_duplicate_status(unsorted, values@);
        assert(words_ordered(values@));
    }
    i = 1;
    while i < length
        invariant 1 <= i, i <= length || length == 0, values.len() == length,
            values@.to_multiset() == unsorted.to_multiset(), words_ordered(values@),
            values@.no_duplicates() <==> globally_unique(source_blocks),
            forall|j: int| 1 <= j < i ==> #[trigger] values@[j - 1] != values@[j],
        decreases length - i,
    {
        if values[i - 1] == values[i] { return false; }
        i += 1;
    }
    proof { ordered_neighbor_scan_establishes_no_duplicates(values@); }
    true
}

pub fn file_from_blocks(blocks: Vec<Block>, inodes: u32, seed: u32, metadata: bool)
    -> (r: Result<File, (Vec<Block>, Error)>)
    ensures (r is Ok) <==> file_valid(FileView { blocks: views(blocks@), inodes, seed, metadata }),
        match r {
        Ok(file) => file.wf() && file.view() == (FileView { blocks: views(blocks@), inodes, seed, metadata }),
        Err((after, _)) => views(after@) == views(blocks@),
    },
{
    if blocks.len() > MAX_FILE_BLOCKS || inodes == 0 { return Err((blocks, Error::Geometry)); }
    let mut i = 0usize;
    while i < blocks.len()
        invariant i <= blocks.len() <= MAX_FILE_BLOCKS, inodes > 0,
            forall|j: int| 0 <= j < i ==> (#[trigger] blocks[j]).wf()
                && blocks[j].inodes == inodes && blocks[j].seed == seed && blocks[j].metadata == metadata
                && (j > 0 ==> blocks[j].raw.len() == blocks[0].raw.len()),
            forall|a: int, b: int| 0 <= a < b < i ==> (#[trigger] blocks[a]).physical != (#[trigger] blocks[b]).physical,
        decreases blocks.len() - i,
    {
        let checked_block = &blocks[i];
        proof { use_type_invariant(checked_block); }
        if blocks[i].inodes != inodes || blocks[i].seed != seed || blocks[i].metadata != metadata {
            return Err((blocks, Error::Geometry));
        }
        if i > 0 && blocks[i].raw.len() != blocks[0].raw.len() { return Err((blocks, Error::Geometry)); }
        let mut j = 0usize;
        while j < i
            invariant j <= i, i < blocks.len(),
                forall|k: int| 0 <= k < j ==> (#[trigger] blocks[k]).physical != blocks[i as int].physical,
            decreases i - j,
        {
            if blocks[j].physical == blocks[i].physical { return Err((blocks, Error::Address)); }
            j += 1;
        }
        i += 1;
    }
    if !distinct_file_entries(&blocks) { return Err((blocks, Error::Duplicate)); }
    Ok(File { blocks, inodes, seed, metadata })
}


pub proof fn exact_slot_update_preserves_other_orphan_entries(before: BlockView, after: BlockView, changed: nat, value: u32, other: nat)
    requires slot_frame(before, after, changed, value), other < capacity_for(before.raw), other != changed,
    ensures slot(before, other) == slot(after, other),
{ }
pub proof fn clearing_an_exact_slot_preserves_uniqueness(before: BlockView, after: BlockView, changed: nat)
    requires unique(before), slot_frame(before, after, changed, 0),
    ensures unique(after),
{
    assert forall|i: nat, j: nat| i < j < capacity_for(after.raw) && slot(after, i) != 0
        implies #[trigger] slot(after, i) != slot(after, j) by {
        if i != changed && j != changed { assert(slot(before, i) != slot(before, j)); }
    }
}

pub proof fn global_uniqueness_binds_an_orphan_to_one_physical_slot(v: FileView, a: LocationView, b: LocationView, number: u32)
    requires file_valid(v), number != 0, contains_at(v, a, number), contains_at(v, b, number),
    ensures a == b,
{
    let i = choose|i: int| 0 <= i < v.blocks.len() && (#[trigger] v.blocks[i]).physical == a.physical
        && a.slot < capacity_for(v.blocks[i].raw) && slot(v.blocks[i], a.slot as nat) == number;
    let j = choose|j: int| 0 <= j < v.blocks.len() && (#[trigger] v.blocks[j]).physical == b.physical
        && b.slot < capacity_for(v.blocks[j].raw) && slot(v.blocks[j], b.slot as nat) == number;
    if i < j { assert(slot(v.blocks[i], a.slot as nat) != slot(v.blocks[j], b.slot as nat)); }
    if j < i { assert(slot(v.blocks[j], b.slot as nat) != slot(v.blocks[i], a.slot as nat)); }
    if a.slot < b.slot { assert(slot(v.blocks[i], a.slot as nat) != slot(v.blocks[i], b.slot as nat)); }
    if b.slot < a.slot { assert(slot(v.blocks[i], b.slot as nat) != slot(v.blocks[i], a.slot as nat)); }
}

}
