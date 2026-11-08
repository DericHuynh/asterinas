// SPDX-License-Identifier: MPL-2.0

//! Linux orphan-file blocks and private copy-on-update images. The caller
//! binds the supplied inode checksum seed and physical address to its source.
//! No block allocation, journal submission or mount capability is returned.

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

#[verifier::ext_equal]
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

proof fn subrange_retains_element<A>(before: Seq<A>, after: Seq<A>, first: int, end: int, index: int)
    requires before.len() == after.len(), 0 <= first <= index < end <= before.len(),
        before.subrange(first, end) == after.subrange(first, end),
    ensures before[index] == after[index],
{
    vstd::seq::lemma_seq_subrange_index(before, first, end, index - first);
    vstd::seq::lemma_seq_subrange_index(after, first, end, index - first);
}
proof fn subrange_retains_word(before: Seq<u8>, after: Seq<u8>, first: int, end: int, at: int)
    requires before.len() == after.len(), 0 <= first <= at, at + 4 <= end <= before.len(),
        before.subrange(first, end) == after.subrange(first, end),
    ensures bytes::le32(before, at) == bytes::le32(after, at),
{
    subrange_retains_element(before, after, first, end, at);
    subrange_retains_element(before, after, first, end, at + 1);
    subrange_retains_element(before, after, first, end, at + 2);
    subrange_retains_element(before, after, first, end, at + 3);
}
proof fn prefix_retains_word(before: Seq<u8>, after: Seq<u8>, at: nat)
    requires before.len() == after.len(), before.len() >= 8,
        before.take(before.len() as int - 8) == after.take(after.len() as int - 8),
        at * 4 + 4 <= before.len() - 8,
    ensures bytes::le32(before, (at * 4) as int) == bytes::le32(after, (at * 4) as int),
{
    subrange_retains_word(before, after, 0, before.len() as int - 8, (at * 4) as int);
}
proof fn spliced_word_retains_other_slot(raw: Seq<u8>, changed: nat, other: nat, number: u32)
    requires (changed + 1) * 4 <= raw.len(), (other + 1) * 4 <= raw.len(), changed != other,
    ensures bytes::le32(bytes::splice(raw, (changed * 4) as int, bytes::encoded_le(number)), (other * 4) as int)
        == bytes::le32(raw, (other * 4) as int),
{
    assert forall|i: int| 0 <= i < 4 implies
        #[trigger] bytes::splice(raw, (changed * 4) as int, bytes::encoded_le(number))[(other * 4) as int + i]
            == #[trigger] raw[(other * 4) as int + i] by {
        bytes::splice_frame(raw, (changed * 4) as int, bytes::encoded_le(number), (other * 4) as int + i);
    }
}
proof fn inserting_an_absent_word_preserves_unique(before: BlockView, after: BlockView, changed: nat, number: u32)
    requires unique(before), slot_frame(before, after, changed, number),
        forall|i: nat| i < capacity_for(before.raw) && i != changed ==> #[trigger] slot(before, i) != number,
    ensures unique(after),
{
    assert forall|i: nat, j: nat| i < j < capacity_for(after.raw) && slot(after, i) != 0
        implies #[trigger] slot(after, i) != #[trigger] slot(after, j) by {
        if i == changed {
            assert(j != changed && slot(before, j) != number);
            assert(slot(after, j) == slot(before, j));
        } else if j == changed {
            assert(slot(before, i) != number);
            assert(slot(after, i) == slot(before, i));
        } else {
            assert(slot(after, i) == slot(before, i) && slot(after, j) == slot(before, j));
            assert(slot(before, i) != 0 && slot(before, i) != slot(before, j));
        }
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
    hide(crc::fold);
    let length = raw.len();
    write32(raw, length - 8, MAGIC);
    if metadata {
        let ghost source = raw@;
        let checksum = calculate_checksum(&raw[..], physical, seed).unwrap();
        write32(raw, length - 4, checksum);
        proof {
            assert(raw@.take(length as int - 8) =~= source.take(length as int - 8));
            assert(checksum_value(raw@, physical, seed) == checksum_value(source, physical, seed));
            assert(bytes::le32(raw@, length as int - 4) == checksum);
            assert(bytes::le32(raw@, length as int - 4) == checksum_value(raw@, physical, seed));
        }
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
                #[trigger] bytes::le32(edited, (j * 4) as int) == bytes::le32(before.raw, (j * 4) as int) by {
                spliced_word_retains_other_slot(before.raw, at as nat, j, number);
            }
            assert forall|j: int| 0 <= j < capacity_for(before.raw) implies #[trigger] bytes::le32(edited, j * 4) <= inodes by {
                if j != at {
                    spliced_word_retains_other_slot(before.raw, at as nat, j as nat, number);
                    assert(bytes::le32(before.raw, j * 4) <= inodes);
                } else { assert(bytes::le32(edited, j * 4) == number); }
            }
        }
        seal_raw(&mut raw, physical, seed, metadata);
        proof {
            assert forall|j: nat| j < capacity_for(before.raw) implies
                #[trigger] bytes::le32(raw@, (j * 4) as int) == bytes::le32(edited, (j * 4) as int) by {
                prefix_retains_word(edited, raw@, j);
            }
            assert forall|j: int| 0 <= j < capacity_for(raw@) implies #[trigger] bytes::le32(raw@, j * 4) <= inodes by {
                assert(capacity_for(raw@) == capacity_for(before.raw));
                prefix_retains_word(edited, raw@, j as nat);
                assert(bytes::le32(raw@, j * 4) == bytes::le32(edited, j * 4));
                assert(bytes::le32(edited, j * 4) <= inodes);
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
            invariant self.wf(), self.view() == before,
                i <= count, count == capacity_for(self.view().raw), 0 < number <= self.view().inodes,
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
    let ghost zeroed = raw@;
    seal_raw(&mut raw, physical, seed, metadata);
    proof {
        assert forall|j: int| 0 <= j < capacity_for(raw@) implies #[trigger] bytes::le32(raw@, j * 4) == 0 by {
            prefix_retains_word(zeroed, raw@, j as nat);
            assert(zeroed[j * 4] == 0 && zeroed[j * 4 + 1] == 0
                && zeroed[j * 4 + 2] == 0 && zeroed[j * 4 + 3] == 0);
        }
        assert(valid_raw(raw@, physical, seed, metadata, inodes));
        if !metadata {
            assert(raw@.subrange(raw.len() as int - 4, raw.len() as int)
                =~= zeroed.subrange(zeroed.len() as int - 4, zeroed.len() as int));
            subrange_retains_word(zeroed, raw@, raw.len() as int - 4, raw.len() as int, raw.len() as int - 4);
            assert(zeroed[zeroed.len() as int - 4] == 0 && zeroed[zeroed.len() as int - 3] == 0
                && zeroed[zeroed.len() as int - 2] == 0 && zeroed[zeroed.len() as int - 1] == 0);
            assert(bytes::le32(raw@, raw.len() as int - 4) == 0);
        }
    }
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

#[verifier::ext_equal]
pub struct LocationView { pub physical: u64, pub slot: usize }
#[verifier::ext_equal]
pub struct FileView { pub blocks: Seq<BlockView>, pub inodes: u32, pub seed: u32, pub metadata: bool }
pub open spec fn views(blocks: Seq<Block>) -> Seq<BlockView> { blocks.map_values(|block: Block| block.view()) }
#[verifier::opaque]
pub open spec fn globally_unique(blocks: Seq<BlockView>) -> bool {
    forall|a: int, b: int, i: nat, j: nat|
        0 <= a <= b < blocks.len() && i < capacity_for(blocks[a].raw) && j < capacity_for(blocks[b].raw)
            && (a < b || i < j) && slot(blocks[a], i) != 0
        ==> #[trigger] slot(blocks[a], i) != #[trigger] slot(blocks[b], j)
}
#[verifier::opaque]
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


proof fn file_shape(v: FileView)
    requires file_valid(v),
    ensures v.inodes > 0, v.blocks.len() <= MAX_FILE_BLOCKS, globally_unique(v.blocks),
{ reveal(file_valid); }
proof fn file_block_profile(v: FileView, index: int)
    requires file_valid(v), 0 <= index < v.blocks.len(),
    ensures block_valid(v.blocks[index]), v.blocks[index].inodes == v.inodes,
        v.blocks[index].seed == v.seed, v.blocks[index].metadata == v.metadata,
        index > 0 ==> v.blocks[index].raw.len() == v.blocks[0].raw.len(),
{ reveal(file_valid); }
proof fn distinct_global_slots(blocks: Seq<BlockView>, a: int, b: int, i: nat, j: nat)
    requires globally_unique(blocks), 0 <= a <= b < blocks.len(),
        i < capacity_for(blocks[a].raw), j < capacity_for(blocks[b].raw),
        a < b || i < j, slot(blocks[a], i) != 0,
    ensures slot(blocks[a], i) != slot(blocks[b], j),
{ reveal(globally_unique); }

proof fn absent_file_number_has_no_slot(v: FileView, number: u32)
    requires file_valid(v), number != 0,
        forall|location: LocationView| !(#[trigger] contains_at(v, location, number)),
    ensures forall|b: int, i: nat| 0 <= b < v.blocks.len() && i < capacity_for(v.blocks[b].raw)
        ==> #[trigger] slot(v.blocks[b], i) != number,
{
    assert forall|b: int, i: nat| 0 <= b < v.blocks.len() && i < capacity_for(v.blocks[b].raw)
        implies #[trigger] slot(v.blocks[b], i) != number by {
        file_block_profile(v, b);
        assert(i <= 16382);
        let location = LocationView { physical: v.blocks[b].physical, slot: i as usize };
        if slot(v.blocks[b], i) == number {
            assert(contains_at(v, location, number));
        }
    }
}
proof fn replacing_one_file_slot(v: FileView, changed: int, replacement: BlockView, at: nat, number: u32)
    requires file_valid(v), 0 <= changed < v.blocks.len(), block_valid(replacement),
        slot_frame(v.blocks[changed], replacement, at, number),
        number == 0 || forall|b: int, i: nat| 0 <= b < v.blocks.len() && i < capacity_for(v.blocks[b].raw)
            ==> #[trigger] slot(v.blocks[b], i) != number,
    ensures file_valid(FileView { blocks: v.blocks.update(changed, replacement), ..v }),
        file_slot_frame(v, FileView { blocks: v.blocks.update(changed, replacement), ..v },
            LocationView { physical: replacement.physical, slot: at as usize }, number),
        number != 0 ==> contains_at(FileView { blocks: v.blocks.update(changed, replacement), ..v },
            LocationView { physical: replacement.physical, slot: at as usize }, number),
{
    reveal(file_valid);
    let after = FileView { blocks: v.blocks.update(changed, replacement), ..v };
    assert(at <= 16382);
    assert forall|a: int| 0 <= a < after.blocks.len() implies block_valid(#[trigger] after.blocks[a])
        && after.blocks[a].inodes == after.inodes && after.blocks[a].seed == after.seed
        && after.blocks[a].metadata == after.metadata
        && (a > 0 ==> after.blocks[a].raw.len() == after.blocks[0].raw.len()) by {
        if a == changed { assert(same_profile(v.blocks[a], replacement)); }
    }
    assert forall|a: int, b: int| 0 <= a < b < after.blocks.len()
        implies (#[trigger] after.blocks[a]).physical != (#[trigger] after.blocks[b]).physical by {
        assert(after.blocks[a].physical == v.blocks[a].physical);
        assert(after.blocks[b].physical == v.blocks[b].physical);
    }
    assert(globally_unique(after.blocks)) by {
        reveal(globally_unique);
        assert forall|a: int, b: int, i: nat, j: nat|
            0 <= a <= b < after.blocks.len() && i < capacity_for(after.blocks[a].raw)
                && j < capacity_for(after.blocks[b].raw) && (a < b || i < j) && slot(after.blocks[a], i) != 0
            implies #[trigger] slot(after.blocks[a], i) != #[trigger] slot(after.blocks[b], j) by {
            assert(capacity_for(after.blocks[a].raw) == capacity_for(v.blocks[a].raw));
            assert(capacity_for(after.blocks[b].raw) == capacity_for(v.blocks[b].raw));
            if a == changed && i == at {
                assert(slot(after.blocks[a], i) == number && number != 0);
                assert(b != changed || j != at);
                assert(slot(after.blocks[b], j) == slot(v.blocks[b], j));
                assert(slot(v.blocks[b], j) != number);
            } else if b == changed && j == at {
                assert(slot(after.blocks[a], i) == slot(v.blocks[a], i));
                assert(slot(after.blocks[b], j) == number);
                if number != 0 { assert(slot(v.blocks[a], i) != number); }
            } else {
                assert(slot(after.blocks[a], i) == slot(v.blocks[a], i));
                assert(slot(after.blocks[b], j) == slot(v.blocks[b], j));
                distinct_global_slots(v.blocks, a, b, i, j);
            }
        }
    }
    assert(file_slot_frame(v, after, LocationView { physical: replacement.physical, slot: at as usize }, number));
    if number != 0 {
        assert(after.blocks[changed] == replacement);
        assert(contains_at(after, LocationView { physical: replacement.physical, slot: at as usize }, number));
    }
}


proof fn rejected_file_header(v: FileView)
    requires v.inodes == 0 || v.blocks.len() > MAX_FILE_BLOCKS,
    ensures !file_valid(v),
{ reveal(file_valid); }
proof fn rejected_file_profile(v: FileView, index: int)
    requires 0 <= index < v.blocks.len(),
        v.blocks[index].inodes != v.inodes || v.blocks[index].seed != v.seed
            || v.blocks[index].metadata != v.metadata
            || index > 0 && v.blocks[index].raw.len() != v.blocks[0].raw.len(),
    ensures !file_valid(v),
{ reveal(file_valid); }
proof fn rejected_file_alias(v: FileView, left: int, right: int)
    requires 0 <= left < right < v.blocks.len(), v.blocks[left].physical == v.blocks[right].physical,
    ensures !file_valid(v),
{ reveal(file_valid); }
proof fn rejected_file_duplicates(v: FileView)
    requires !globally_unique(v.blocks),
    ensures !file_valid(v),
{ reveal(file_valid); }

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
        if ordinal >= self.blocks.len() { None } else {
            let block = &self.blocks[ordinal];
            proof { use_type_invariant(block); assert(block.view() == self.view().blocks[ordinal as int]); }
            Some(block)
        }
    }
    /// Cold/reconciliation lookup. A runtime inode cache retains Location
    /// after insertion, so ordinary removal need not rediscover it.
    pub fn file_find(&self, number: u32) -> (r: Option<Location>)
        ensures self.wf(), match r {
            Some(location) => 0 < number <= self.view().inodes && contains_at(self.view(), location.view(), number)
                && forall|other: LocationView| #[trigger] contains_at(self.view(), other, number) ==> other == location.view(),
            None => 0 < number <= self.view().inodes ==> forall|location: LocationView| !(#[trigger] contains_at(self.view(), location, number)),
        },
    { proof { use_type_invariant(self); }
        let ghost before = self.view();
        if number == 0 || number > self.inodes { return None; }
        let mut i = 0usize;
        while i < self.blocks.len()
            invariant self.wf(), self.view() == before, i <= self.blocks.len(),
                0 < number <= before.inodes,
                forall|b: int, j: nat| 0 <= b < i && j < capacity_for(before.blocks[b].raw)
                    ==> #[trigger] slot(before.blocks[b], j) != number,
            decreases self.blocks.len() - i,
        {
            proof { file_block_profile(before, i as int); }
            if let Some(slot) = self.blocks[i].find(number) {
                let location = Location { physical: self.blocks[i].physical, slot };
                proof {
                    assert(contains_at(before, location.view(), number));
                    assert forall|other: LocationView| #[trigger] contains_at(before, other, number)
                        implies other == location.view() by {
                        global_uniqueness_binds_an_orphan_to_one_physical_slot(before, other, location.view(), number);
                    }
                }
                return Some(location);
            }
            i += 1;
        }
        proof {
            assert forall|location: LocationView| !(#[trigger] contains_at(before, location, number)) by {
                if contains_at(before, location, number) {
                    let b = choose|b: int| 0 <= b < before.blocks.len()
                        && (#[trigger] before.blocks[b]).physical == location.physical
                        && location.slot < capacity_for(before.blocks[b].raw)
                        && slot(before.blocks[b], location.slot as nat) == number;
                    assert(slot(before.blocks[b], location.slot as nat) != number);
                }
            }
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
        let ghost before = self.view();
        if number == 0 || number > self.inodes { return Err((self, Error::Inode)); }
        if let Some(location) = self.file_find(number) { return Ok((self, location)); }
        proof { file_shape(before); absent_file_number_has_no_slot(before, number); }
        let length = self.blocks.len();
        if length == 0 { return Err((self, Error::Full)); }
        let mut ordinal = start % length;
        let mut checked = 0usize;
        while checked < length
            invariant self.wf(), self.view() == before,
                checked <= length, ordinal < length, length == self.blocks.len(), 0 < number <= before.inodes,
                forall|b: int, j: nat| 0 <= b < before.blocks.len() && j < capacity_for(before.blocks[b].raw)
                    ==> #[trigger] slot(before.blocks[b], j) != number,
            decreases length - checked,
        {
            proof { file_block_profile(before, ordinal as int); }
            if self.blocks[ordinal].free_entries() != 0 {
                let candidate = duplicate_block(&self.blocks[ordinal]);
                match candidate.insert(number) {
                    Ok((block, slot)) => {
                        let location = Location { physical: block.physical, slot };
                        let ghost replacement = block.view();
                        proof { replacing_one_file_slot(before, ordinal as int, replacement, slot as nat, number); }
                        let File { mut blocks, inodes, seed, metadata } = self;
                        blocks.set(ordinal, block);
                        proof { assert(views(blocks@) =~= before.blocks.update(ordinal as int, replacement)); }
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
        let ghost before = self.view();
        if expected == 0 || expected > self.inodes { return Err((self, Error::Inode)); }
        let mut i = 0usize;
        while i < self.blocks.len()
            invariant self.wf(), self.view() == before, i <= self.blocks.len(), 0 < expected <= before.inodes,
            decreases self.blocks.len() - i,
        {
            proof { file_block_profile(before, i as int); }
            if self.blocks[i].physical == location.physical {
                let candidate = duplicate_block(&self.blocks[i]);
                match candidate.remove(location.slot, expected) {
                    Ok(block) => {
                        let ghost replacement = block.view();
                        proof {
                            assert(contains_at(before, location.view(), expected));
                            replacing_one_file_slot(before, i as int, replacement, location.slot as nat, 0);
                        }
                        let File { mut blocks, inodes, seed, metadata } = self;
                        blocks.set(i, block);
                        proof { assert(views(blocks@) =~= before.blocks.update(i as int, replacement)); }
                        return Ok(File { blocks, inodes, seed, metadata });
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
proof fn occupied_block_zero(block: BlockView)
    ensures occupied_block_words(block, 0) == Seq::<u32>::empty(),
{ reveal_with_fuel(occupied_block_words, 1); }
proof fn occupied_block_successor(block: BlockView, count: nat)
    requires count < capacity_for(block.raw),
    ensures occupied_block_words(block, count + 1)
        == if slot(block, count) == 0 { occupied_block_words(block, count) }
            else { occupied_block_words(block, count).push(slot(block, count)) },
{ reveal_with_fuel(occupied_block_words, 1); }
proof fn occupied_file_zero(blocks: Seq<BlockView>)
    ensures occupied_file_words(blocks, 0) == Seq::<u32>::empty(),
{ reveal_with_fuel(occupied_file_words, 1); }
proof fn occupied_file_successor(blocks: Seq<BlockView>, count: nat)
    requires count < blocks.len(),
    ensures occupied_file_words(blocks, count + 1) == occupied_file_words(blocks, count)
        + occupied_block_words(blocks[count as int], capacity_for(blocks[count as int].raw)),
{ reveal_with_fuel(occupied_file_words, 1); }

proof fn block_word_membership_is_exact(block: BlockView, count: nat, number: u32)
    requires count <= capacity_for(block.raw),
    ensures occupied_block_words(block, count).contains(number)
        <==> number != 0 && exists|i: nat| i < count && #[trigger] slot(block, i) == number,
    decreases count,
{
    if count == 0 { occupied_block_zero(block); }
    else {
        let previous_count = (count - 1) as nat;
        occupied_block_successor(block, previous_count);
        block_word_membership_is_exact(block, previous_count, number);
        let previous = occupied_block_words(block, previous_count);
        let current = occupied_block_words(block, count);
        let last = slot(block, previous_count);
        vstd::seq_lib::lemma_seq_contains_after_push(previous, last, number);
        assert(previous.contains(number) <==> number != 0 && exists|i: nat| i < previous_count && #[trigger] slot(block, i) == number);
        if current.contains(number) {
            if last != 0 && last == number {
                assert(exists|i: nat| i < count && #[trigger] slot(block, i) == number) by {
                    assert(previous_count < count && slot(block, previous_count) == number);
                }
            } else {
                assert(previous.contains(number));
                let i = choose|i: nat| i < previous_count && #[trigger] slot(block, i) == number;
                assert(exists|j: nat| j < count && #[trigger] slot(block, j) == number) by {
                    assert(i < count && slot(block, i) == number);
                }
            }
        }
        if number != 0 && exists|i: nat| i < count && #[trigger] slot(block, i) == number {
            let i = choose|i: nat| i < count && #[trigger] slot(block, i) == number;
            if i < previous_count {
                assert(exists|j: nat| j < previous_count && #[trigger] slot(block, j) == number);
                assert(previous.contains(number));
            } else { assert(i == previous_count && last == number && last != 0); }
            assert(current.contains(number));
        }
    }
}
pub open spec fn block_contains_number(block: BlockView, number: u32) -> bool {
    exists|i: nat| i < capacity_for(block.raw) && #[trigger] slot(block, i) == number
}
proof fn file_word_membership_is_exact(blocks: Seq<BlockView>, count: nat, number: u32)
    requires count <= blocks.len(),
    ensures occupied_file_words(blocks, count).contains(number)
        <==> number != 0 && exists|b: int, i: nat| 0 <= b < count
            && i < capacity_for(blocks[b].raw) && #[trigger] slot(blocks[b], i) == number,
    decreases count,
{
    if count == 0 { occupied_file_zero(blocks); }
    else {
        let previous_count = (count - 1) as nat;
        let last_index = count as int - 1;
        occupied_file_successor(blocks, previous_count);
        file_word_membership_is_exact(blocks, previous_count, number);
        let block = blocks[last_index];
        block_word_membership_is_exact(block, capacity_for(block.raw), number);
        let previous = occupied_file_words(blocks, previous_count);
        let words = occupied_block_words(block, capacity_for(block.raw));
        let current = occupied_file_words(blocks, count);
        vstd::seq_lib::lemma_seq_concat_contains_all_elements(previous, words, number);
        assert(previous.contains(number) <==> number != 0 && exists|b: int, i: nat| 0 <= b < previous_count
            && i < capacity_for(blocks[b].raw) && #[trigger] slot(blocks[b], i) == number);
        if current.contains(number) {
            if previous.contains(number) {
                assert(exists|b: int| 0 <= b < previous_count
                    && #[trigger] block_contains_number(blocks[b], number));
                let b = choose|b: int| 0 <= b < previous_count
                    && #[trigger] block_contains_number(blocks[b], number);
                let i = choose|i: nat| i < capacity_for(blocks[b].raw) && #[trigger] slot(blocks[b], i) == number;
                assert(exists|a: int, j: nat| 0 <= a < count
                    && j < capacity_for(blocks[a].raw) && #[trigger] slot(blocks[a], j) == number) by {
                    assert(0 <= b < count && i < capacity_for(blocks[b].raw) && slot(blocks[b], i) == number);
                }
            } else {
                assert(words.contains(number));
                let i = choose|i: nat| i < capacity_for(block.raw) && #[trigger] slot(block, i) == number;
                assert(exists|a: int, j: nat| 0 <= a < count
                    && j < capacity_for(blocks[a].raw) && #[trigger] slot(blocks[a], j) == number) by {
                    assert(0 <= last_index < count && i < capacity_for(blocks[last_index].raw)
                        && slot(blocks[last_index], i) == number);
                }
            }
        }
        if number != 0 && exists|b: int, i: nat| 0 <= b < count
            && i < capacity_for(blocks[b].raw) && #[trigger] slot(blocks[b], i) == number {
            assert(exists|b: int| 0 <= b < count
                && #[trigger] block_contains_number(blocks[b], number));
            let b = choose|b: int| 0 <= b < count
                && #[trigger] block_contains_number(blocks[b], number);
            let i = choose|i: nat| i < capacity_for(blocks[b].raw) && #[trigger] slot(blocks[b], i) == number;
            if b < previous_count {
                assert(exists|a: int, j: nat| 0 <= a < previous_count
                    && j < capacity_for(blocks[a].raw) && #[trigger] slot(blocks[a], j) == number);
                assert(previous.contains(number));
            } else {
                assert(b == last_index);
                assert(exists|j: nat| j < capacity_for(block.raw) && #[trigger] slot(block, j) == number);
                assert(words.contains(number));
            }
            assert(current.contains(number));
        }
    }
}

proof fn concatenation_is_duplicate_free_exactly_when_parts_are_disjoint(left: Seq<u32>, right: Seq<u32>)
    ensures (left + right).no_duplicates() <==> left.no_duplicates() && right.no_duplicates()
        && forall|number: u32| #[trigger] left.contains(number) ==> !right.contains(number),
{
    if (left + right).no_duplicates() {
        assert forall|i: int, j: int| 0 <= i < j < left.len() implies #[trigger] left[i] != #[trigger] left[j] by {
            assert((left + right)[i] != (left + right)[j]);
        }
        assert forall|i: int, j: int| 0 <= i < j < right.len() implies #[trigger] right[i] != #[trigger] right[j] by {
            assert((left + right)[left.len() + i] != (left + right)[left.len() + j]);
        }
        assert forall|number: u32| #[trigger] left.contains(number) implies !right.contains(number) by {
            if right.contains(number) {
                let i = choose|i: int| 0 <= i < left.len() && left[i] == number;
                let j = choose|j: int| 0 <= j < right.len() && right[j] == number;
                assert((left + right)[i] != (left + right)[left.len() + j]);
            }
        }
    } else if left.no_duplicates() && right.no_duplicates()
        && forall|number: u32| #[trigger] left.contains(number) ==> !right.contains(number) {
        assert forall|i: int, j: int| 0 <= i < j < left.len() + right.len()
            implies #[trigger] (left + right)[i] != #[trigger] (left + right)[j] by {
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
    if count == 0 { occupied_block_zero(block); }
    else {
        occupied_block_successor(block, (count - 1) as nat);
        block_word_uniqueness_is_exact(block, (count - 1) as nat);
        let previous = occupied_block_words(block, (count - 1) as nat);
        let last = slot(block, (count - 1) as nat);
        vstd::seq_lib::lemma_seq_contains_after_push(previous, last, last);
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
    let prefix = blocks.take(count as int);
    vstd::seq::lemma_seq_subrange_len(blocks, 0, count as int);
    if count == 0 { occupied_file_zero(blocks); reveal(globally_unique); }
    else {
        occupied_file_successor(blocks, (count - 1) as nat);
        file_word_uniqueness_is_exact(blocks, (count - 1) as nat);
        let previous_count = (count - 1) as nat;
        let earlier_prefix = blocks.take(count as int - 1);
        let earlier = occupied_file_words(blocks, previous_count);
        let last_index = count as int - 1;
        let last = blocks[last_index];
        vstd::seq::lemma_seq_subrange_len(blocks, 0, count as int - 1);
        vstd::seq::lemma_seq_subrange_index(blocks, 0, count as int, last_index);
        let words = occupied_block_words(last, capacity_for(last.raw));
        block_word_uniqueness_is_exact(last, capacity_for(last.raw));
        concatenation_is_duplicate_free_exactly_when_parts_are_disjoint(earlier, words);
        if globally_unique(prefix) {
            assert(globally_unique(earlier_prefix)) by {
                reveal(globally_unique);
                assert forall|a: int, b: int, i: nat, j: nat|
                    0 <= a <= b < earlier_prefix.len() && i < capacity_for(earlier_prefix[a].raw)
                        && j < capacity_for(earlier_prefix[b].raw) && (a < b || i < j) && slot(earlier_prefix[a], i) != 0
                    implies #[trigger] slot(earlier_prefix[a], i) != #[trigger] slot(earlier_prefix[b], j) by {
                    vstd::seq::lemma_seq_subrange_index(blocks, 0, count as int - 1, a);
                    vstd::seq::lemma_seq_subrange_index(blocks, 0, count as int - 1, b);
                    vstd::seq::lemma_seq_subrange_index(blocks, 0, count as int, a);
                    vstd::seq::lemma_seq_subrange_index(blocks, 0, count as int, b);
                    assert(earlier_prefix[a] == prefix[a] && earlier_prefix[b] == prefix[b]);
                    distinct_global_slots(prefix, a, b, i, j);
                }
            }
            assert(block_prefix_unique(last, capacity_for(last.raw))) by {
                assert forall|i: nat, j: nat| i < j < capacity_for(last.raw) && slot(last, i) != 0
                    implies #[trigger] slot(last, i) != #[trigger] slot(last, j) by {
                    assert(prefix[last_index] == last);
                    distinct_global_slots(prefix, last_index, last_index, i, j);
                }
            }
            assert forall|number: u32| #[trigger] earlier.contains(number) implies !words.contains(number) by {
                file_word_membership_is_exact(blocks, previous_count, number);
                block_word_membership_is_exact(last, capacity_for(last.raw), number);
                if words.contains(number) {
                    assert(exists|b: int| 0 <= b < previous_count
                        && #[trigger] block_contains_number(blocks[b], number));
                    let b = choose|b: int| 0 <= b < previous_count
                        && #[trigger] block_contains_number(blocks[b], number);
                    let i = choose|i: nat| i < capacity_for(blocks[b].raw) && #[trigger] slot(blocks[b], i) == number;
                    let j = choose|j: nat| j < capacity_for(last.raw) && #[trigger] slot(last, j) == number;
                    vstd::seq::lemma_seq_subrange_index(blocks, 0, count as int, b);
                    assert(number != 0 && prefix[b] == blocks[b] && prefix[last_index] == last);
                    distinct_global_slots(prefix, b, last_index, i, j);
                }
            }
        } else if earlier.no_duplicates() && words.no_duplicates()
            && forall|number: u32| #[trigger] earlier.contains(number) ==> !words.contains(number) {
            assert(globally_unique(prefix)) by {
                reveal(globally_unique);
                assert forall|a: int, b: int, i: nat, j: nat|
                    0 <= a <= b < prefix.len() && i < capacity_for(prefix[a].raw)
                        && j < capacity_for(prefix[b].raw) && (a < b || i < j) && slot(prefix[a], i) != 0
                    implies #[trigger] slot(prefix[a], i) != #[trigger] slot(prefix[b], j) by {
                    vstd::seq::lemma_seq_subrange_index(blocks, 0, count as int, a);
                    vstd::seq::lemma_seq_subrange_index(blocks, 0, count as int, b);
                    assert(prefix[a] == blocks[a] && prefix[b] == blocks[b]);
                    if b < last_index {
                        vstd::seq::lemma_seq_subrange_index(blocks, 0, count as int - 1, a);
                        vstd::seq::lemma_seq_subrange_index(blocks, 0, count as int - 1, b);
                        assert(earlier_prefix[a] == prefix[a] && earlier_prefix[b] == prefix[b]);
                        distinct_global_slots(earlier_prefix, a, b, i, j);
                    } else if a == b {
                        assert(a == last_index && prefix[a] == last);
                        assert(slot(last, i) != slot(last, j));
                    } else if slot(prefix[a], i) == slot(prefix[b], j) {
                        assert(b == last_index && a < previous_count && prefix[b] == last);
                        let number = slot(prefix[a], i);
                        file_word_membership_is_exact(blocks, previous_count, number);
                        block_word_membership_is_exact(last, capacity_for(last.raw), number);
                        assert(exists|c: int, k: nat| 0 <= c < previous_count
                            && k < capacity_for(blocks[c].raw) && #[trigger] slot(blocks[c], k) == number);
                        assert(exists|k: nat| k < capacity_for(last.raw) && #[trigger] slot(last, k) == number);
                        assert(earlier.contains(number) && words.contains(number));
                    }
                }
            }
        }
    }
}

pub open spec fn ordered_window(values: Seq<u32>, first: nat, end: nat) -> bool {
    first <= end <= values.len()
        && forall|i: int, j: int| first <= i < j < end ==> #[trigger] values[i] <= #[trigger] values[j]
}
pub open spec fn ordered_run(values: Seq<u32>, width: nat, run: nat) -> bool {
    ordered_window(values, run * width,
        if (run + 1) * width < values.len() { (run + 1) * width } else { values.len() })
}
pub open spec fn ordered_runs(values: Seq<u32>, width: nat) -> bool {
    width > 0 && forall|run: nat| run * width < values.len() ==> #[trigger] ordered_run(values, width, run)
}
proof fn an_ordered_window_can_append_a_larger_word(before: Seq<u32>, after: Seq<u32>, first: nat, end: nat, number: u32)
    requires ordered_window(before, first, end), first <= end < after.len(),
        before.len() == after.len(), after.take(end as int) == before.take(end as int),
        after[end as int] == number,
        forall|i: int| first <= i < end ==> #[trigger] before[i] <= number,
    ensures ordered_window(after, first, end + 1),
{
    assert forall|i: int, j: int| first <= i < j < end + 1 implies #[trigger] after[i] <= #[trigger] after[j] by {
        subrange_retains_element(before, after, 0, end as int, i);
        assert(after[i] == before[i]);
        if j < end {
            subrange_retains_element(before, after, 0, end as int, j);
            assert(after[j] == before[j]); assert(before[i] <= before[j]);
        }
        else { assert(j == end && after[j] == number && before[i] <= number); }
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
        subrange_retains_element(before, after, 0, prefix as int, i);
        subrange_retains_element(before, after, 0, prefix as int, j);
        assert(after[i] == before[i] && after[j] == before[j]);
        assert(before[i] <= before[j]);
    }
}

proof fn two_capped_steps(first: nat, width: nat, length: nat, middle: nat, end: nat)
    requires first <= length,
        middle == if first + width < length { first + width } else { length },
        end == if middle + width < length { middle + width } else { length },
    ensures end == if first + 2 * width < length { first + 2 * width } else { length },
{
    if middle < length { assert(middle == first + width); }
    else { assert(middle == length && end == length && first + width >= length); }
}
proof fn whole_ordered_run(values: Seq<u32>, width: nat)
    requires ordered_run(values, width, 0), width >= values.len(),
    ensures ordered_window(values, 0, values.len()),
{
    assert(0nat * width == 0 && (0nat + 1) * width == width);
    assert((if width < values.len() { width } else { values.len() }) == values.len());
}

proof fn aligned_pair_of_runs_is_ordered(values: Seq<u32>, width: nat, run: nat, first: nat, middle: nat, end: nat)
    requires ordered_runs(values, width), first == run * (2 * width), first < values.len(),
        middle == if first + width < values.len() { first + width } else { values.len() },
        end == if middle + width < values.len() { middle + width } else { values.len() },
    ensures ordered_window(values, first, middle), ordered_window(values, middle, end),
{
    assert((2 * run) * width == first) by (nonlinear_arith)
        requires first == run * (2 * width);
    assert((2 * run + 1) * width == first + width) by (nonlinear_arith)
        requires first == run * (2 * width);
    assert((2 * run + 2) * width == first + 2 * width) by (nonlinear_arith)
        requires first == run * (2 * width);
    assert(ordered_run(values, width, 2 * run));
    assert(ordered_window(values, first, middle));
    if middle < values.len() {
        assert(middle == (2 * run + 1) * width);
        assert(ordered_run(values, width, 2 * run + 1));
        assert(end == if (2 * run + 2) * width < values.len() { (2 * run + 2) * width } else { values.len() });
    } else { assert(middle == values.len() && end == values.len()); }
    assert(ordered_window(values, middle, end));
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
        implies #[trigger] values[left] != #[trigger] values[right] by {
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
    requires blocks.len() <= MAX_FILE_BLOCKS, forall|i: int| 0 <= i < blocks.len() ==> (#[trigger] blocks[i]).wf(),
    ensures r <==> globally_unique(views(blocks@)),
{
    let mut values: Vec<u32> = Vec::new();
    let ghost source_blocks = views(blocks@);
    proof { occupied_file_zero(source_blocks); }
    let mut i = 0usize;
    while i < blocks.len()
        invariant i <= blocks.len(), blocks.len() <= MAX_FILE_BLOCKS,
            values.len() <= i * 16382, source_blocks == views(blocks@),
            values@ == occupied_file_words(source_blocks, i as nat),
        decreases blocks.len() - i,
    {
        let mut j = 0usize; let capacity = blocks[i].capacity();
        proof { occupied_block_zero(source_blocks[i as int]); }
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
                occupied_block_successor(source_blocks[i as int], j as nat);
                assert(values@ == occupied_file_words(source_blocks, i as nat)
                    + occupied_block_words(source_blocks[i as int], (j + 1) as nat));
            }
            j += 1;
        }
        proof {
            occupied_file_successor(source_blocks, i as nat);
            assert(values@ == occupied_file_words(source_blocks, (i + 1) as nat));
        }
        i += 1;
    }
    let ghost unsorted = values@;
    proof {
        file_word_uniqueness_is_exact(source_blocks, source_blocks.len());
        assert(source_blocks.take(source_blocks.len() as int) =~= source_blocks);
        assert(unsorted.no_duplicates() <==> globally_unique(source_blocks));
    }
    let length = values.len(); let mut other: Vec<u32> = Vec::new(); i = 0;
    while i < length
        invariant i <= length, other.len() == i, values@ == unsorted, values.len() == length, length <= 8387584,
            source_blocks == views(blocks@), unsorted.no_duplicates() <==> globally_unique(source_blocks),
        decreases length - i,
    { other.push(0); i += 1; }
    let mut width = 1usize;
    proof { assert(ordered_runs(values@, 1)); }
    while width < length
        invariant ordered_runs(values@, width as nat), 0 < width, width <= length || length <= 1,
            values.len() == length, other.len() == length, length <= 8387584,
            source_blocks == views(blocks@), unsorted.no_duplicates() <==> globally_unique(source_blocks),
            values@.to_multiset() == unsorted.to_multiset(),
        decreases length - width,
    {
        let ghost run_width: nat = 2nat * (width as nat);
        let mut left = 0usize;
        let ghost mut completed_runs = 0nat;
        proof {
            broadcast use vstd::seq_lib::group_to_multiset_ensures;
            broadcast use vstd::multiset::group_multiset_axioms;
            assert(other@.take(0) =~= Seq::<u32>::empty());
            assert(values@.take(0) =~= Seq::<u32>::empty());
        }
        while left < length
            invariant ordered_runs(values@, width as nat), left <= length,
                run_width == 2nat * (width as nat), run_width > 0,
                source_blocks == views(blocks@), unsorted.no_duplicates() <==> globally_unique(source_blocks),
                left as nat == if completed_runs * (run_width) < length { completed_runs * (run_width) } else { length as nat },
                forall|run: nat| run < completed_runs ==> #[trigger] ordered_run(other@, run_width, run), 0 < width, values.len() == length, other.len() == length, length <= 8387584,
                values@.to_multiset() == unsorted.to_multiset(),
                other@.take(left as int).to_multiset() == values@.take(left as int).to_multiset(),
            decreases length - left,
        {
            let middle = left + if width < length - left { width } else { length - left };
            let right = middle + if width < length - middle { width } else { length - middle };
            proof {
                assert(left as nat == completed_runs * run_width);
                aligned_pair_of_runs_is_ordered(values@, width as nat, completed_runs, left as nat, middle as nat, right as nat);
                two_capped_steps(left as nat, width as nat, length as nat, middle as nat, right as nat);
                assert(left as nat + run_width == (completed_runs + 1) * run_width) by (nonlinear_arith)
                    requires left as nat == completed_runs * run_width;
                assert(right as nat == if (completed_runs + 1) * run_width < length {
                    (completed_runs + 1) * run_width
                } else { length as nat });
            }
            let mut a = left; let mut b = middle; let mut out = left;
            proof {
                broadcast use vstd::seq_lib::group_to_multiset_ensures;
                broadcast use vstd::multiset::group_multiset_axioms;
                assert(other@.subrange(left as int, left as int) =~= Seq::<u32>::empty());
                assert(values@.subrange(left as int, left as int) =~= Seq::<u32>::empty());
                assert(values@.subrange(middle as int, middle as int) =~= Seq::<u32>::empty());
            }
            while out < right
                invariant left <= a <= middle <= b <= right <= length, left <= out <= right,
                    run_width == 2nat * (width as nat), run_width > 0,
                    ordered_runs(values@, width as nat), values@.to_multiset() == unsorted.to_multiset(),
                    right as nat == if (completed_runs + 1) * run_width < length {
                        (completed_runs + 1) * run_width
                    } else { length as nat },
                    left as nat == completed_runs * run_width,
                    source_blocks == views(blocks@), unsorted.no_duplicates() <==> globally_unique(source_blocks),
                    out as int - left as int == (a as int - left as int) + (b as int - middle as int),
                    values.len() == length, other.len() == length,
                    ordered_window(values@, left as nat, middle as nat),
                    ordered_window(values@, middle as nat, right as nat),
                    ordered_window(other@, left as nat, out as nat),
                    out > left ==> forall|p: int| a <= p < middle ==> #[trigger] values@[p] >= other@[out as int - 1],
                    out > left ==> forall|p: int| b <= p < right ==> #[trigger] values@[p] >= other@[out as int - 1],
                    forall|run: nat| run < completed_runs ==> #[trigger] ordered_run(other@, run_width, run),
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
                    assert forall|run: nat| run < completed_runs implies #[trigger] ordered_run(other@, run_width, run) by {
                        let first = run * (run_width);
                        let end = if (run + 1) * (run_width) < length { (run + 1) * (run_width) } else { length as nat };
                        assert(end <= left) by (nonlinear_arith)
                            requires run < completed_runs, run_width > 0,
                                left as nat == completed_runs * run_width, end <= (run + 1) * run_width;
                        assert(ordered_run(previous_output, run_width, run));
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
                assert forall|run: nat| run < completed_runs + 1 implies #[trigger] ordered_run(other@, run_width, run) by {
                    if run == completed_runs {
                        assert(run * (run_width) == left);
                        assert((run + 1) * (run_width) == left as nat + run_width) by (nonlinear_arith)
                            requires run == completed_runs, left as nat == completed_runs * run_width;
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
            assert(left == length);
            other@.lemma_take_len();
            values@.lemma_take_len();
            assert(other@.to_multiset() == values@.to_multiset());
            assert(other@.to_multiset() == unsorted.to_multiset());
            assert(ordered_runs(other@, run_width)) by {
                assert forall|run: nat| run * (run_width) < length implies #[trigger] ordered_run(other@, run_width, run) by {
                    assert(length <= completed_runs * run_width);
                    assert(run < completed_runs) by (nonlinear_arith)
                        requires length <= completed_runs * run_width, run * run_width < length, run_width > 0;
                }
            }
        }
        let ghost previous_width = width;
        let old = values; values = other; other = old;
        width = if width > length / 2 { length } else { width * 2 };
        proof {
            if width == length {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(length as int, 2);
                assert(run_width >= length) by (nonlinear_arith)
                    requires run_width == 2nat * (previous_width as nat),
                        width == length, width as int == if previous_width > length / 2 { length as int } else { previous_width as int * 2 },
                        length as int == 2 * (length as int / 2) + length as int % 2,
                        0 <= length as int % 2 < 2;
                assert(ordered_run(values@, run_width, 0));
                whole_ordered_run(values@, run_width);
                assert(ordered_window(values@, 0, length as nat));
                assert(ordered_runs(values@, width as nat)) by {
                    assert forall|run: nat| run * width < length implies #[trigger] ordered_run(values@, width as nat, run) by {
                        assert(run == 0) by (nonlinear_arith) requires width == length, width > 0, run * width < length;
                    }
                }
            } else { assert(width == 2 * previous_width); }
        }
    }
    proof {
        permutation_preserves_duplicate_status(unsorted, values@);
        if length > 0 {
            assert(width >= length);
            assert(ordered_run(values@, width as nat, 0));
            whole_ordered_run(values@, width as nat);
            assert(ordered_window(values@, 0, length as nat));
        }
        assert(words_ordered(values@));
    }
    i = 1;
    while i < length
        invariant 1 <= i, i <= length || length == 0, values.len() == length, source_blocks == views(blocks@),
            values@.to_multiset() == unsorted.to_multiset(), words_ordered(values@),
            values@.no_duplicates() <==> globally_unique(source_blocks),
            forall|j: int| 1 <= j < i ==> #[trigger] values@[j - 1] != values@[j],
        decreases length - i,
    {
        if values[i - 1] == values[i] {
            proof { assert(!values@.no_duplicates()) by {
                if values@.no_duplicates() { assert(values@[i as int - 1] != values@[i as int]); }
            } }
            return false;
        }
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
    let ghost input = FileView { blocks: views(blocks@), inodes, seed, metadata };
    if blocks.len() > MAX_FILE_BLOCKS || inodes == 0 {
        proof { rejected_file_header(input); }
        return Err((blocks, Error::Geometry));
    }
    let mut i = 0usize;
    while i < blocks.len()
        invariant i <= blocks.len() <= MAX_FILE_BLOCKS, inodes > 0,
            input == (FileView { blocks: views(blocks@), inodes, seed, metadata }),
            forall|j: int| 0 <= j < i ==> (#[trigger] blocks[j]).wf()
                && blocks[j].inodes == inodes && blocks[j].seed == seed && blocks[j].metadata == metadata
                && (j > 0 ==> blocks[j].raw.len() == blocks[0].raw.len()),
            forall|a: int, b: int| 0 <= a < b < i ==> (#[trigger] blocks[a]).physical != (#[trigger] blocks[b]).physical,
        decreases blocks.len() - i,
    {
        let checked_block = &blocks[i];
        proof { use_type_invariant(checked_block); }
        if blocks[i].inodes != inodes || blocks[i].seed != seed || blocks[i].metadata != metadata {
            proof { assert(input.blocks[i as int] == blocks[i as int].view()); rejected_file_profile(input, i as int); }
            return Err((blocks, Error::Geometry));
        }
        if i > 0 && blocks[i].raw.len() != blocks[0].raw.len() {
            proof { assert(input.blocks[i as int] == blocks[i as int].view()); rejected_file_profile(input, i as int); }
            return Err((blocks, Error::Geometry));
        }
        let mut j = 0usize;
        while j < i
            invariant j <= i, i < blocks.len() <= MAX_FILE_BLOCKS, inodes > 0,
                input == (FileView { blocks: views(blocks@), inodes, seed, metadata }),
                blocks[i as int].wf(), blocks[i as int].inodes == inodes,
                blocks[i as int].seed == seed, blocks[i as int].metadata == metadata,
                i > 0 ==> blocks[i as int].raw.len() == blocks[0].raw.len(),
                forall|k: int| 0 <= k < i ==> (#[trigger] blocks[k]).wf()
                    && blocks[k].inodes == inodes && blocks[k].seed == seed && blocks[k].metadata == metadata
                    && (k > 0 ==> blocks[k].raw.len() == blocks[0].raw.len()),
                forall|a: int, b: int| 0 <= a < b < i ==> (#[trigger] blocks[a]).physical != (#[trigger] blocks[b]).physical,
                forall|k: int| 0 <= k < j ==> (#[trigger] blocks[k]).physical != blocks[i as int].physical,
            decreases i - j,
        {
            if blocks[j].physical == blocks[i].physical {
                proof {
                    assert(input.blocks[j as int] == blocks[j as int].view());
                    assert(input.blocks[i as int] == blocks[i as int].view());
                    rejected_file_alias(input, j as int, i as int);
                }
                return Err((blocks, Error::Address));
            }
            j += 1;
        }
        proof {
            assert forall|a: int, b: int| 0 <= a < b < i + 1
                implies (#[trigger] blocks[a]).physical != (#[trigger] blocks[b]).physical by {
                if b < i { assert(blocks[a].physical != blocks[b].physical); }
                else { assert(b == i && a < j); }
            }
        }
        i += 1;
    }
    if !distinct_file_entries(&blocks) {
        proof { rejected_file_duplicates(input); }
        return Err((blocks, Error::Duplicate));
    }
    proof {
        reveal(file_valid);
        assert forall|a: int| 0 <= a < input.blocks.len() implies block_valid(#[trigger] input.blocks[a])
            && input.blocks[a].inodes == inodes && input.blocks[a].seed == seed && input.blocks[a].metadata == metadata
            && (a > 0 ==> input.blocks[a].raw.len() == input.blocks[0].raw.len()) by {
            assert(input.blocks[a] == blocks[a].view());
        }
        assert forall|a: int, b: int| 0 <= a < b < input.blocks.len()
            implies (#[trigger] input.blocks[a]).physical != (#[trigger] input.blocks[b]).physical by {
            assert(input.blocks[a] == blocks[a].view() && input.blocks[b] == blocks[b].view());
        }
        assert(file_valid(input));
    }
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
        implies #[trigger] slot(after, i) != #[trigger] slot(after, j) by {
        if i != changed && j != changed { assert(slot(before, i) != slot(before, j)); }
    }
}

pub proof fn global_uniqueness_binds_an_orphan_to_one_physical_slot(v: FileView, a: LocationView, b: LocationView, number: u32)
    requires file_valid(v), number != 0, contains_at(v, a, number), contains_at(v, b, number),
    ensures a == b,
{
    reveal(file_valid); reveal(globally_unique);
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
