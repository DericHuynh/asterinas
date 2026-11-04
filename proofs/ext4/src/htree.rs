// SPDX-License-Identifier: MPL-2.0

//! Linux HTree root/internal tables and collision-aware routing. These are
//! immutable structural codecs, not a complete directory admission witness.
//! Hash/name equivalence, whole-tree ownership and mutations are separate.

use vstd::prelude::*;
use crate::{block_size, bytes, crc};

verus! {

#[derive(Clone, Copy)]
pub struct Edge { pub hash: u32, pub block: u32 }
pub open spec fn edge(raw: Seq<u8>, first: nat, i: nat) -> Edge {
    Edge { hash: if i == 0 { 0u32 } else { bytes::le32(raw, (first + 8 * i) as int) as u32 },
        block: bytes::le32(raw, (first + 8 * i + 4) as int) as u32 & 0x0fffffffu32 }
}
pub open spec fn record_length(word: u16, block_bytes: nat) -> nat {
    if block_bytes < 65536 { word as nat }
    else if word == 0 || word == 65535 { 65536nat }
    else { (word as nat / 4) * 4 + (word as nat % 4) * 65536 }
}
pub open spec fn capacity(length: nat, first: nat, checksummed: bool) -> nat {
    ((length - first - if checksummed { 8nat } else { 0nat }) / 8) as nat
}
pub open spec fn checksum(raw: Seq<u8>, first: nat, count: nat, limit: nat, seed: u32) -> u32 {
    let tail = first + limit * 8;
    crc::fold(crc::fold(crc::fold(seed, raw.subrange(0, (first + count * 8) as int)), raw.subrange(tail as int, tail as int + 4)), seq![0u8, 0u8, 0u8, 0u8])
}
#[verifier::opaque]
pub open spec fn table(raw: Seq<u8>, first: usize, blocks: u32, seed: u32, checksummed: bool) -> bool {
    let limit = bytes::le16(raw, first as int);
    let count = bytes::le16(raw, first as int + 2);
    &&& block_size::accepted(raw.len()) && (first == 8 || first == 32) && blocks > 1
    &&& limit == capacity(raw.len(), first as nat, checksummed) && 0 < count <= limit
    &&& first as nat + limit * 8 + if checksummed { 8nat } else { 0nat } <= raw.len()
    &&& forall|i: nat| i < count ==> 0 < (#[trigger] edge(raw, first as nat, i)).block < blocks
        && (i > 0 ==> edge(raw, first as nat, (i - 1) as nat).hash <= edge(raw, first as nat, i).hash)
    &&& checksummed ==> bytes::le32(raw, (first as nat + limit * 8) as int) == 0
        && bytes::le32(raw, (first as nat + limit * 8 + 4) as int) == checksum(raw, first as nat, count, limit, seed) as nat
}

pub struct IndexView { pub raw: Seq<u8>, pub first: usize, pub blocks: u32, pub seed: u32, pub checksummed: bool }
pub open spec fn valid(v: IndexView) -> bool { table(v.raw, v.first, v.blocks, v.seed, v.checksummed) }
pub open spec fn count(v: IndexView) -> nat { bytes::le16(v.raw, v.first as int + 2) }
pub open spec fn selected(v: IndexView, hash: u32, i: nat) -> bool {
    i < count(v) && edge(v.raw, v.first as nat, i).hash <= hash
        && forall|j: nat| i < j < count(v) ==> (#[trigger] edge(v.raw, v.first as nat, j)).hash > hash
}
pub open spec fn continuation(v: IndexView, hash: u32, i: nat) -> bool {
    0 < i < count(v) && (edge(v.raw, v.first as nat, i).hash & !1u32) == hash
}

pub struct Index<'a> { raw: &'a [u8], first: usize, blocks: u32, seed: u32, checksummed: bool, count: usize }
impl<'a> Index<'a> {
    pub closed spec fn view(&self) -> IndexView { IndexView { raw: self.raw@, first: self.first, blocks: self.blocks, seed: self.seed, checksummed: self.checksummed } }
    pub closed spec fn stored_count(&self) -> usize { self.count }
    pub open spec fn wf(&self) -> bool { valid(self.view()) && self.stored_count() == count(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn child_count(&self) -> (r: usize) ensures self.wf(), r == count(self.view()), 0 < r <= 8191 {
        proof { use_type_invariant(self); reveal(table); } self.count
    }
    pub fn child(&self, i: usize) -> (r: Option<Edge>)
        ensures self.wf(), match r { Some(e) => i < count(self.view()) && e == edge(self.view().raw, self.view().first as nat, i as nat)
            && 0 < e.block < self.view().blocks, None => i >= count(self.view()) },
    {
        hide(crc::fold);
        proof { use_type_invariant(self); reveal(table); }
        if i >= self.count { return None; }
        let offset = self.first + i * 8;
        let hash = if i == 0 { 0u32 } else { bytes::read_le32(self.raw, offset).unwrap() };
        let block = bytes::read_le32(self.raw, offset + 4).unwrap() & 0x0fffffff;
        Some(Edge { hash, block })
    }
    pub fn probe(&self, hash: u32) -> (r: usize)
        ensures self.wf(), selected(self.view(), hash, r as nat),
    {
        let count = self.child_count();
        let mut low = 1usize;
        let mut high = count;
        while low < high
            invariant self.wf(), 1 <= low <= high <= count == crate::htree::count(self.view()) <= 8191,
                forall|i: nat| i < low ==> (#[trigger] edge(self.view().raw, self.view().first as nat, i)).hash <= hash,
                forall|i: nat| high <= i < count ==> (#[trigger] edge(self.view().raw, self.view().first as nat, i)).hash > hash,
            decreases high - low,
        {
            let middle = low + (high - low) / 2;
            let e = self.child(middle).unwrap();
            proof { reveal(table); }
            if e.hash <= hash {
                proof {
                    assert forall|i: nat| i < middle + 1 implies (#[trigger] edge(self.view().raw, self.view().first as nat, i)).hash <= hash by {
                        if i >= low { monotone(self.view(), i, middle as nat); }
                    }
                }
                low = middle + 1;
            } else {
                proof {
                    assert forall|i: nat| middle <= i < count implies (#[trigger] edge(self.view().raw, self.view().first as nat, i)).hash > hash by {
                        if i < high { monotone(self.view(), middle as nat, i); }
                    }
                }
                high = middle;
            }
        }
        low - 1
    }
    pub fn continues(&self, hash: u32, i: usize) -> (r: bool)
        ensures self.wf(), r == continuation(self.view(), hash, i as nat),
    {
        if i == 0 { let _ = self.child_count(); return false; }
        match self.child(i) { Some(e) => (e.hash & !1u32) == hash, None => false }
    }
}

proof fn monotone(v: IndexView, a: nat, b: nat)
    requires valid(v), a <= b < count(v),
    ensures edge(v.raw, v.first as nat, a).hash <= edge(v.raw, v.first as nat, b).hash,
    decreases b - a,
{
    reveal(table);
    if a < b { monotone(v, a, (b - 1) as nat); }
}

fn parse_table(raw: &[u8], first: usize, blocks: u32, seed: u32, checksummed: bool) -> (r: Option<Index<'_>>)
    ensures match r { Some(index) => index.wf() && index.view() == IndexView { raw: raw@, first, blocks, seed, checksummed }, None => true },
{
    if !block_size::valid(raw.len()) || (first != 8 && first != 32) || blocks <= 1 { return None; }
    let tail_bytes = if checksummed { 8usize } else { 0usize };
    let limit = (raw.len() - first - tail_bytes) / 8;
    let count = bytes::read_le16(raw, first + 2).unwrap() as usize;
    if bytes::read_le16(raw, first).unwrap() as usize != limit || count == 0 || count > limit { return None; }
    let mut i = 0usize;
    while i < count
        invariant block_size::accepted(raw.len() as nat), raw.len() <= 65536, (first == 8 || first == 32), blocks > 1,
            limit == capacity(raw.len() as nat, first as nat, checksummed), first + limit * 8 + tail_bytes <= raw.len(),
            count == bytes::le16(raw@, first as int + 2), limit == bytes::le16(raw@, first as int), 0 < count <= limit, i <= count,
            tail_bytes == if checksummed { 8usize } else { 0usize },
            forall|j: nat| j < i ==> 0 < (#[trigger] edge(raw@, first as nat, j)).block < blocks
                && (j > 0 ==> edge(raw@, first as nat, (j - 1) as nat).hash <= edge(raw@, first as nat, j).hash),
        decreases count - i,
    {
        let offset = first + i * 8;
        let block = bytes::read_le32(raw, offset + 4).unwrap() & 0x0fffffff;
        if block == 0 || block >= blocks { return None; }
        if i > 0 {
            let hash = bytes::read_le32(raw, offset).unwrap();
            let before = if i == 1 { 0u32 } else { bytes::read_le32(raw, offset - 8).unwrap() };
            if hash < before { return None; }
        }
        i += 1;
    }
    if checksummed {
        let tail = first + limit * 8;
        if bytes::read_le32(raw, tail).unwrap() != 0 { return None; }
        let prefix = crc::crc32c(seed, &raw[..first + count * 8]);
        let tail_seed = crc::crc32c(prefix, &raw[tail..tail + 4]);
        let actual = crc::crc32c(tail_seed, &[0u8, 0u8, 0u8, 0u8]);
        if bytes::read_le32(raw, tail + 4).unwrap() != actual { return None; }
    }
    assert(table(raw@, first, blocks, seed, checksummed)) by { reveal(table); }
    Some(Index { raw, first, blocks, seed, checksummed, count })
}

pub open spec fn node_header(raw: Seq<u8>) -> bool {
    block_size::accepted(raw.len()) && bytes::le32(raw, 0) == 0 && record_length(bytes::le16(raw, 4) as u16, raw.len()) == raw.len() && raw[6] == 0 && raw[7] == 0
}
pub fn parse_node(raw: &[u8], blocks: u32, seed: u32, checksummed: bool) -> (r: Option<Index<'_>>)
    ensures match r { Some(index) => index.wf() && index.view() == IndexView { raw: raw@, first: 8, blocks, seed, checksummed } && node_header(raw@), None => true },
{
    if !block_size::valid(raw.len()) { return None; }
    let length = bytes::read_le16(raw, 4).unwrap();
    let decoded = if raw.len() < 65536 { length as usize } else if length == 0 || length == 65535 { 65536usize }
        else { (length as usize / 4) * 4 + (length as usize % 4) * 65536 };
    if bytes::read_le32(raw, 0).unwrap() != 0 || decoded != raw.len() || raw[6] != 0 || raw[7] != 0 { return None; }
    parse_table(raw, 8, blocks, seed, checksummed)
}

pub open spec fn root_header(raw: Seq<u8>, inodes: u32, large: bool) -> bool {
    &&& block_size::accepted(raw.len()) && 0 < bytes::le32(raw, 0) <= inodes && bytes::le16(raw, 4) == 12
    &&& raw[6] == 1 && raw[7] == 2 && raw[8] == 46
    &&& 0 < bytes::le32(raw, 12) <= inodes && bytes::le16(raw, 16) == raw.len() - 12
    &&& raw[18] == 2 && raw[19] == 2 && raw[20] == 46 && raw[21] == 46
    &&& bytes::le32(raw, 24) == 0 && (raw[28] <= 2 || raw[28] == 6) && raw[29] == 8
    &&& raw[30] <= if large { 2u8 } else { 1u8 } && raw[31] == 0
}
pub struct Root<'a> { index: Index<'a>, inodes: u32, large: bool }
impl<'a> Root<'a> {
    pub closed spec fn view(&self) -> IndexView { self.index.view() }
    pub closed spec fn inodes(&self) -> u32 { self.inodes }
    pub closed spec fn large(&self) -> bool { self.large }
    pub open spec fn wf(&self) -> bool { valid(self.view()) && self.view().first == 32 && root_header(self.view().raw, self.inodes(), self.large()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn routing_index(&self) -> (r: &Index<'a>) ensures self.wf(), r.wf(), r.view() == self.view() {
        proof { use_type_invariant(self); } let _ = self.index.child_count(); &self.index
    }
    pub fn hash_and_levels(&self) -> (r: (u8, u8)) ensures self.wf(), r == (self.view().raw[28], self.view().raw[30]) {
        proof { use_type_invariant(self); } (self.index.raw[28], self.index.raw[30])
    }
}

pub fn parse_root(raw: &[u8], blocks: u32, inodes: u32, seed: u32, checksummed: bool, large: bool) -> (r: Option<Root<'_>>)
    ensures match r { Some(root) => root.wf() && root.view() == IndexView { raw: raw@, first: 32, blocks, seed, checksummed }
        && root.inodes() == inodes && root.large() == large, None => true },
{
    if !block_size::valid(raw.len()) { return None; }
    let own = bytes::read_le32(raw, 0).unwrap();
    let parent = bytes::read_le32(raw, 12).unwrap();
    if own == 0 || own > inodes || bytes::read_le16(raw, 4).unwrap() != 12 || raw[6] != 1 || raw[7] != 2 || raw[8] != 46
        || parent == 0 || parent > inodes || bytes::read_le16(raw, 16).unwrap() as usize != raw.len() - 12
        || raw[18] != 2 || raw[19] != 2 || raw[20] != 46 || raw[21] != 46 || bytes::read_le32(raw, 24).unwrap() != 0
        || (raw[28] > 2 && raw[28] != 6) || raw[29] != 8 || raw[30] > if large { 2u8 } else { 1u8 } || raw[31] != 0 { return None; }
    let index = match parse_table(raw, 32, blocks, seed, checksummed) { Some(index) => index, None => { return None; } };
    Some(Root { index, inodes, large })
}

pub proof fn a_probe_has_one_exact_initial_child(v: IndexView, hash: u32, a: nat, b: nat)
    requires valid(v), selected(v, hash, a), selected(v, hash, b),
    ensures a == b,
{
    if a < b { assert(edge(v.raw, v.first as nat, b).hash > hash); }
    if b < a { assert(edge(v.raw, v.first as nat, a).hash > hash); }
}

pub proof fn odd_hash_continuations_are_distinct_from_initial_even_boundaries(v: IndexView, hash: u32, i: nat)
    requires valid(v), hash & 1u32 == 0, continuation(v, hash, i), edge(v.raw, v.first as nat, i).hash & 1u32 != 0,
    ensures edge(v.raw, v.first as nat, i).hash > hash,
{
    let h = edge(v.raw, v.first as nat, i).hash;
    assert(h & !1u32 == hash && h & 1u32 != 0 && hash & 1u32 == 0 ==> h > hash) by (bit_vector);
}

}
