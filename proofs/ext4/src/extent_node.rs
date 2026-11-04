// SPDX-License-Identifier: MPL-2.0

//! Local inline/external extent-node validation for depths 0 through 5,
//! 48-bit child pointers and 1 through 64 KiB blocks. Metadata checksums cover
//! eh_max entries, matching Linux. This is not whole-tree/ownership validation;
//! the source adapter must bind the inode seed, node address and feature mode.

use vstd::prelude::*;
use crate::{block_size, bytes, crc, extent, extent_span::{self, ExtentSpan}};

verus! {

pub enum BlockChecksum { Legacy, Crc32c(u32) }
pub enum NodeKind { Inline, LegacyBlock, ChecksummedBlock(u32) }
pub struct NodeView { pub raw: Seq<u8>, pub blocks: u64, pub kind: NodeKind }
pub struct IndexEntry { pub logical: u32, pub child: u64 }
pub struct ChildLink { pub index: usize, pub number: u64, pub first: u32, pub upper: u64, pub depth: u16 }

pub open spec fn offset(index: int) -> int { 12 + index * 12 }
#[verifier::opaque]
pub open spec fn key(raw: Seq<u8>, index: int) -> nat { bytes::le32(raw, offset(index)) }
pub open spec fn child(raw: Seq<u8>, index: int) -> nat {
    bytes::le32(raw, offset(index) + 4) + 4294967296 * bytes::le16(raw, offset(index) + 8)
}
pub open spec fn end(raw: Seq<u8>, depth: u16, index: int) -> nat {
    key(raw, index) + if depth == 0 { extent::length(bytes::le16(raw, offset(index) + 4)) } else { 1nat }
}
#[verifier::opaque]
pub open spec fn record_valid(raw: Seq<u8>, blocks: u64, depth: u16, index: int) -> bool {
    &&& 0 <= index && offset(index) + 12 <= raw.len()
    &&& if depth == 0 { extent_span::accepted(raw, offset(index), blocks) } else { 0 < child(raw, index) < blocks }
}

pub open spec fn shape(raw: Seq<u8>, kind: NodeKind) -> bool {
    if kind is Inline { raw.len() == 60 } else { block_size::accepted(raw.len()) }
}
pub open spec fn capacity(v: NodeView) -> nat { if v.kind is Inline { 4nat } else { ((v.raw.len() - 12) / 12) as nat } }
pub open spec fn header(v: NodeView) -> bool {
    &&& shape(v.raw, v.kind) && v.blocks > 0
    &&& bytes::le16(v.raw, 0) == 0xf30a && bytes::le16(v.raw, 6) <= 5
    &&& 0 < bytes::le16(v.raw, 4) <= capacity(v)
    &&& bytes::le16(v.raw, 2) <= bytes::le16(v.raw, 4)
}

#[verifier::opaque]
pub open spec fn records(v: NodeView, count: nat) -> bool {
    &&& count <= bytes::le16(v.raw, 2)
    &&& (forall|i: int| 0 <= i < count ==> #[trigger] record_valid(v.raw, v.blocks, bytes::le16(v.raw, 6) as u16, i))
    &&& (forall|i: int| 0 < i < count ==> end(v.raw, bytes::le16(v.raw, 6) as u16, i - 1) <= #[trigger] key(v.raw, i))
}

pub open spec fn checksum_ok(v: NodeView) -> bool {
    match v.kind {
        NodeKind::ChecksummedBlock(seed) => {
            let tail = 12 + bytes::le16(v.raw, 4) * 12;
            tail + 4 <= v.raw.len() && bytes::le32(v.raw, tail as int) == crc::fold(seed, v.raw.subrange(0, tail as int)) as nat
        },
        _ => true,
    }
}

#[verifier::opaque]
pub open spec fn valid(v: NodeView) -> bool { header(v) && records(v, bytes::le16(v.raw, 2)) && checksum_ok(v) }

pub open spec fn branch_bounds(v: NodeView, depth: u16, first: Option<u32>, upper: u64) -> bool {
    &&& bytes::le16(v.raw, 6) == depth
    &&& if bytes::le16(v.raw, 2) == 0 { depth == 0 } else {
        &&& match first { Some(logical) => key(v.raw, 0) == logical, None => true }
        &&& end(v.raw, depth, bytes::le16(v.raw, 2) as int - 1) <= upper
    }
}

pub open spec fn covers(v: NodeView, index: int, logical: u32) -> bool {
    key(v.raw, index) <= logical < end(v.raw, 0, index)
}

pub open spec fn leaf_result(v: NodeView, logical: u32, result: Option<extent_span::SpanView>) -> bool {
    match result {
        Some(span) => extent_span::valid(span) && extent_span::mapping(span, logical) is Some && span.blocks == v.blocks
            && exists|i: int| 0 <= i < bytes::le16(v.raw, 2) && #[trigger] covers(v, i, logical)
                && extent_span::represents(span, v.raw, offset(i)),
        None => forall|i: int| 0 <= i < bytes::le16(v.raw, 2) ==> !#[trigger] covers(v, i, logical),
    }
}

pub open spec fn branch_link(v: NodeView, index: usize, upper: u64) -> ChildLink {
    ChildLink { index, number: child(v.raw, index as int) as u64, first: key(v.raw, index as int) as u32,
        upper: if index as nat + 1 < bytes::le16(v.raw, 2) { key(v.raw, index as int + 1) as u64 } else { upper },
        depth: (bytes::le16(v.raw, 6) - 1) as u16 }
}

pub open spec fn chosen_link(v: NodeView, logical: u32, upper: u64, link: ChildLink) -> bool {
    &&& bytes::le16(v.raw, 6) > 0 && link.index < bytes::le16(v.raw, 2)
    &&& link == branch_link(v, link.index, upper) && 0 < link.number < v.blocks
    &&& link.index == 0 || key(v.raw, link.index as int) <= logical
    &&& forall|i: int| link.index < i < bytes::le16(v.raw, 2) ==> logical < #[trigger] key(v.raw, i)
}

proof fn record_at(v: NodeView, count: nat, index: int)
    requires records(v, count), 0 <= index < count,
    ensures record_valid(v.raw, v.blocks, bytes::le16(v.raw, 6) as u16, index),
{
    reveal(records);
}

proof fn neighboring_records(v: NodeView, count: nat, index: int)
    requires records(v, count), 0 < index < count,
    ensures end(v.raw, bytes::le16(v.raw, 6) as u16, index - 1) <= key(v.raw, index),
{
    reveal(records);
}

proof fn append_record(v: NodeView, count: nat)
    requires records(v, count), count < bytes::le16(v.raw, 2),
        record_valid(v.raw, v.blocks, bytes::le16(v.raw, 6) as u16, count as int),
        count > 0 ==> end(v.raw, bytes::le16(v.raw, 6) as u16, count as int - 1) <= key(v.raw, count as int),
    ensures records(v, count + 1),
{
    reveal(records);
    assert forall|i: int| 0 <= i < count + 1 implies #[trigger] record_valid(v.raw, v.blocks, bytes::le16(v.raw, 6) as u16, i) by {
        if i < count { assert(record_valid(v.raw, v.blocks, bytes::le16(v.raw, 6) as u16, i)); }
    }
    assert forall|i: int| 0 < i < count + 1 implies end(v.raw, bytes::le16(v.raw, 6) as u16, i - 1) <= #[trigger] key(v.raw, i) by {
        if i < count { assert(end(v.raw, bytes::le16(v.raw, 6) as u16, i - 1) <= key(v.raw, i)); }
    }
}

pub proof fn record_keys_are_strictly_increasing(v: NodeView, first: int, last: int)
    requires valid(v), 0 <= first < last < bytes::le16(v.raw, 2),
    ensures key(v.raw, first) < key(v.raw, last),
    decreases last - first,
{
    reveal(valid);
    record_at(v, bytes::le16(v.raw, 2), last - 1);
    neighboring_records(v, bytes::le16(v.raw, 2), last);
    reveal(record_valid);
    assert(end(v.raw, bytes::le16(v.raw, 6) as u16, last - 1) > key(v.raw, last - 1));
    if first < last - 1 { record_keys_are_strictly_increasing(v, first, last - 1); }
}

pub proof fn record_intervals_are_ordered(v: NodeView, first: int, last: int)
    requires valid(v), 0 <= first < last < bytes::le16(v.raw, 2),
    ensures end(v.raw, bytes::le16(v.raw, 6) as u16, first) <= key(v.raw, last),
{
    reveal(valid);
    neighboring_records(v, bytes::le16(v.raw, 2), first + 1);
    if first + 1 < last { record_keys_are_strictly_increasing(v, first + 1, last); }
}

pub proof fn leaf_mapping_is_unique(v: NodeView, logical: u32, first: int, last: int)
    requires valid(v), bytes::le16(v.raw, 6) == 0,
        0 <= first < bytes::le16(v.raw, 2), 0 <= last < bytes::le16(v.raw, 2),
        covers(v, first, logical), covers(v, last, logical),
    ensures first == last,
{
    if first < last { record_intervals_are_ordered(v, first, last); }
    if last < first { record_intervals_are_ordered(v, last, first); }
}

pub proof fn every_record_respects_branch_bounds(v: NodeView, depth: u16, first: Option<u32>, upper: u64, index: int)
    requires valid(v), branch_bounds(v, depth, first, upper), 0 <= index < bytes::le16(v.raw, 2),
    ensures key(v.raw, index) < end(v.raw, depth, index) <= upper,
        match first { Some(low) => low <= key(v.raw, index), None => true },
{
    reveal(valid);
    let last = bytes::le16(v.raw, 2) as int - 1;
    record_at(v, bytes::le16(v.raw, 2), last);
    record_at(v, bytes::le16(v.raw, 2), index);
    reveal(record_valid);
    if index < last { record_intervals_are_ordered(v, index, last); }
    if index > 0 { record_keys_are_strictly_increasing(v, 0, index); }
}

pub proof fn child_intervals_stay_within_parent(v: NodeView, depth: u16, first: Option<u32>, upper: u64, index: usize)
    requires valid(v), branch_bounds(v, depth, first, upper), depth > 0, index < bytes::le16(v.raw, 2),
    ensures {
        let link = branch_link(v, index, upper);
        &&& link.first < link.upper <= upper
        &&& link.first as nat == key(v.raw, index as int)
        &&& if index as nat + 1 < bytes::le16(v.raw, 2) { link.upper as nat == key(v.raw, index as int + 1) } else { link.upper == upper }
        &&& match first { Some(low) => low <= link.first, None => true }
    },
{
    every_record_respects_branch_bounds(v, depth, first, upper, index as int);
    if index as nat + 1 < bytes::le16(v.raw, 2) {
        every_record_respects_branch_bounds(v, depth, first, upper, index as int + 1);
        record_keys_are_strictly_increasing(v, index as int, index as int + 1);
    }
    reveal(valid);
    record_at(v, bytes::le16(v.raw, 2), index as int);
    reveal(record_valid);
    reveal(key);
}

pub proof fn leaf_result_is_unique(v: NodeView, logical: u32, a: Option<extent_span::SpanView>, b: Option<extent_span::SpanView>)
    requires valid(v), bytes::le16(v.raw, 6) == 0, leaf_result(v, logical, a), leaf_result(v, logical, b),
    ensures a == b,
{
    if let Some(x) = a {
        let i = choose|i: int| 0 <= i < bytes::le16(v.raw, 2) && #[trigger] covers(v, i, logical)
            && extent_span::represents(x, v.raw, offset(i));
        if let Some(y) = b {
            let j = choose|j: int| 0 <= j < bytes::le16(v.raw, 2) && #[trigger] covers(v, j, logical)
                && extent_span::represents(y, v.raw, offset(j));
            leaf_mapping_is_unique(v, logical, i, j);
            assert(x == y);
        } else { assert(!covers(v, i, logical)); }
    } else if let Some(y) = b {
        let j = choose|j: int| 0 <= j < bytes::le16(v.raw, 2) && #[trigger] covers(v, j, logical)
            && extent_span::represents(y, v.raw, offset(j));
        assert(!covers(v, j, logical));
    }
}

pub struct Node<'a> { raw: &'a [u8], blocks: u64, kind: NodeKind, entries: u16, maximum: u16, depth: u16 }

impl<'a> Node<'a> {
    pub closed spec fn view(&self) -> NodeView { NodeView { raw: self.raw@, blocks: self.blocks, kind: self.kind } }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {
        self.wf() && self.entries as nat == bytes::le16(self.raw@, 2)
            && self.maximum as nat == bytes::le16(self.raw@, 4) && self.depth as nat == bytes::le16(self.raw@, 6)
    }

    pub fn header_fields(&self) -> (r: (u16, u16, u16))
        ensures self.wf(), r.0 as nat == bytes::le16(self.view().raw, 2), r.1 as nat == bytes::le16(self.view().raw, 4),
            r.2 as nat == bytes::le16(self.view().raw, 6),
    {
        proof { use_type_invariant(self); }
        (self.entries, self.maximum, self.depth)
    }

    pub fn raw(&self) -> (r: &'a [u8]) ensures self.wf(), r@ == self.view().raw {
        proof { use_type_invariant(self); }
        self.raw
    }

    pub fn key_at(&self, index: usize) -> (r: Option<u32>)
        ensures self.wf(), match r {
            Some(logical) => index < bytes::le16(self.view().raw, 2) && logical as nat == key(self.view().raw, index as int),
            None => index >= bytes::le16(self.view().raw, 2),
        },
    {
        proof { use_type_invariant(self); reveal(valid); }
        if index >= self.entries as usize { return None; }
        proof { record_at(self.view(), self.entries as nat, index as int); reveal(record_valid); reveal(key); }
        Some(bytes::read_le32(self.raw, 12 + index * 12).unwrap())
    }

    // Position after all keys <= logical, for either index or leaf entries.
    // The caller handles a query preceding the first entry explicitly.
    pub fn upper_bound(&self, logical: u32) -> (r: usize)
        ensures self.wf(), r <= bytes::le16(self.view().raw, 2),
            forall|i: int| 0 <= i < r ==> #[trigger] key(self.view().raw, i) <= logical,
            forall|i: int| r <= i < bytes::le16(self.view().raw, 2) ==> logical < #[trigger] key(self.view().raw, i),
    {
        proof { use_type_invariant(self); reveal(valid); }
        let mut low = 0usize;
        let mut high = self.entries as usize;
        while low < high
            invariant self.wf(), self.entries as nat == bytes::le16(self.view().raw, 2),
                low <= high <= self.entries <= 5460,
                forall|i: int| 0 <= i < low ==> #[trigger] key(self.view().raw, i) <= logical,
                forall|i: int| high <= i < self.entries ==> logical < #[trigger] key(self.view().raw, i),
            decreases high - low,
        {
            let middle = low + (high - low) / 2;
            let current = self.key_at(middle).unwrap();
            if current <= logical {
                assert forall|i: int| 0 <= i < middle + 1 implies #[trigger] key(self.view().raw, i) <= logical by {
                    if i < middle { record_keys_are_strictly_increasing(self.view(), i, middle as int); }
                }
                low = middle + 1;
            } else {
                assert forall|i: int| middle <= i < self.entries implies logical < #[trigger] key(self.view().raw, i) by {
                    if middle < i { record_keys_are_strictly_increasing(self.view(), middle as int, i); }
                }
                high = middle;
            }
        }
        low
    }

    pub fn fits_branch(&self, depth: u16, first: Option<u32>, upper: u64) -> (r: bool)
        ensures self.wf(), r == branch_bounds(self.view(), depth, first, upper),
    {
        proof { use_type_invariant(self); reveal(valid); }
        if self.depth != depth { return false; }
        if self.entries == 0 { return depth == 0; }
        if let Some(first) = first { if self.key_at(0).unwrap() != first { return false; } }
        let last = self.entries as usize - 1;
        if depth == 0 {
            let span = self.leaf_extent(last).unwrap();
            let info = span.info();
            proof { reveal(key); }
            info.logical as u64 + info.length as u64 <= upper
        } else {
            self.key_at(last).unwrap() as u64 + 1 <= upper
        }
    }

    pub fn find_child(&self, logical: u32, upper: u64) -> (r: Option<ChildLink>)
        ensures self.wf(), match r {
            Some(link) => chosen_link(self.view(), logical, upper, link),
            None => bytes::le16(self.view().raw, 6) == 0 || bytes::le16(self.view().raw, 2) == 0,
        },
    {
        proof { use_type_invariant(self); reveal(valid); }
        if self.depth == 0 || self.entries == 0 { return None; }
        let position = self.upper_bound(logical);
        let index = if position == 0 { 0usize } else { position - 1 };
        let entry = self.index_entry(index).unwrap();
        let high = if index + 1 < self.entries as usize { self.key_at(index + 1).unwrap() as u64 } else { upper };
        Some(ChildLink { index, number: entry.child, first: entry.logical, upper: high, depth: self.depth - 1 })
    }

    pub fn find_leaf(&self, logical: u32) -> (r: Option<ExtentSpan>)
        ensures self.wf(), bytes::le16(self.view().raw, 6) == 0 ==> leaf_result(self.view(), logical, match r { Some(span) => Some(span.view()), None => None }),
            bytes::le16(self.view().raw, 6) != 0 ==> r is None,
    {
        proof { use_type_invariant(self); reveal(valid); }
        if self.depth != 0 { return None; }
        let position = self.upper_bound(logical);
        if position == 0 {
            assert forall|i: int| 0 <= i < self.entries implies !#[trigger] covers(self.view(), i, logical) by {}
            return None;
        }
        let index = position - 1;
        let span = self.leaf_extent(index).unwrap();
        let physical = span.physical_block(logical);
        proof { reveal(key); }
        if physical.is_some() {
            assert(covers(self.view(), index as int, logical));
            assert(exists|i: int| 0 <= i < self.entries && #[trigger] covers(self.view(), i, logical)
                && extent_span::represents(span.view(), self.view().raw, offset(i)));
            Some(span)
        } else {
            assert forall|i: int| 0 <= i < self.entries implies !#[trigger] covers(self.view(), i, logical) by {
                if i < index { record_intervals_are_ordered(self.view(), i, index as int); }
            }
            None
        }
    }

    pub fn leaf_extent(&self, index: usize) -> (r: Option<ExtentSpan>)
        ensures self.wf(), match r {
            Some(span) => bytes::le16(self.view().raw, 6) == 0 && index < bytes::le16(self.view().raw, 2)
                && span.wf() && span.view().blocks == self.view().blocks
                && extent_span::represents(span.view(), self.view().raw, offset(index as int)),
            None => bytes::le16(self.view().raw, 6) != 0 || index >= bytes::le16(self.view().raw, 2),
        },
    {
        proof { use_type_invariant(self); reveal(valid); }
        if self.depth != 0 || index >= self.entries as usize { return None; }
        proof { record_at(self.view(), self.entries as nat, index as int); reveal(record_valid); }
        Some(extent_span::parse(self.raw, 12 + index * 12, self.blocks).unwrap())
    }

    pub fn index_entry(&self, index: usize) -> (r: Option<IndexEntry>)
        ensures self.wf(), match r {
            Some(entry) => bytes::le16(self.view().raw, 6) > 0 && index < bytes::le16(self.view().raw, 2)
                && entry.logical as nat == key(self.view().raw, index as int)
                && entry.child as nat == child(self.view().raw, index as int) && 0 < entry.child < self.view().blocks,
            None => bytes::le16(self.view().raw, 6) == 0 || index >= bytes::le16(self.view().raw, 2),
        },
    {
        proof { use_type_invariant(self); reveal(valid); }
        if self.depth == 0 || index >= self.entries as usize { return None; }
        proof { record_at(self.view(), self.entries as nat, index as int); reveal(record_valid); reveal(key); }
        let offset = 12 + index * 12;
        let logical = bytes::read_le32(self.raw, offset).unwrap();
        let low = bytes::read_le32(self.raw, offset + 4).unwrap() as u64;
        let high = bytes::read_le16(self.raw, offset + 8).unwrap() as u64;
        Some(IndexEntry { logical, child: low + high * 4294967296 })
    }
}

fn check_record(raw: &[u8], blocks: u64, depth: u16, index: usize) -> (r: Option<u64>)
    requires index <= 5460, offset(index as int) + 12 <= raw.len(),
    ensures match r {
        Some(last) => record_valid(raw@, blocks, depth, index as int) && last as nat == end(raw@, depth, index as int),
        None => !record_valid(raw@, blocks, depth, index as int),
    },
{
    reveal(record_valid);
    reveal(key);
    let offset = 12 + index * 12;
    if depth == 0 {
        let span = match extent_span::parse(raw, offset, blocks) { Some(span) => span, None => { return None; } };
        let info = span.info();
        Some(info.logical as u64 + info.length as u64)
    } else {
        let low = bytes::read_le32(raw, offset + 4).unwrap() as u64;
        let high = bytes::read_le16(raw, offset + 8).unwrap() as u64;
        let child = low + high * 4294967296;
        if child == 0 || child >= blocks { return None; }
        Some(bytes::read_le32(raw, offset).unwrap() as u64 + 1)
    }
}

fn parse<'a>(raw: &'a [u8], blocks: u64, kind: NodeKind) -> (r: Option<Node<'a>>)
    ensures match r {
        Some(node) => node.wf() && node.view() == (NodeView { raw: raw@, blocks, kind }),
        None => !valid(NodeView { raw: raw@, blocks, kind }),
    },
{
    hide(crc::fold);
    reveal(valid);
    if match kind { NodeKind::Inline => raw.len() != 60, _ => !block_size::valid(raw.len()) } { return None; }
    if blocks == 0 || bytes::read_le16(raw, 0).unwrap() != 0xf30a { return None; }
    let entries = bytes::read_le16(raw, 2).unwrap();
    let maximum = bytes::read_le16(raw, 4).unwrap();
    let depth = bytes::read_le16(raw, 6).unwrap();
    let capacity = match kind { NodeKind::Inline => 4usize, _ => (raw.len() - 12) / 12 };
    if maximum == 0 || maximum as usize > capacity || entries > maximum || depth > 5 { return None; }
    if let NodeKind::ChecksummedBlock(seed) = kind {
        let tail = 12 + maximum as usize * 12;
        if tail + 4 > raw.len() || bytes::read_le32(raw, tail).unwrap() != crc::crc32c(seed, &raw[..tail]) { return None; }
    }
    let ghost v = NodeView { raw: raw@, blocks, kind };
    let mut index = 0usize;
    let mut previous_end = 0u64;
    assert(records(v, 0)) by { reveal(records); }
    while index < entries as usize
        invariant header(v), checksum_ok(v), v == (NodeView { raw: raw@, blocks, kind }),
            entries as nat == bytes::le16(raw@, 2), maximum as nat == bytes::le16(raw@, 4), depth as nat == bytes::le16(raw@, 6),
            index <= entries <= maximum <= 5460, raw.len() <= 65536,
            records(v, index as nat),
            index == 0 ==> previous_end == 0,
            index > 0 ==> previous_end as nat == end(raw@, depth, index as int - 1),
        decreases entries as usize - index,
    {
        let last = match check_record(raw, blocks, depth, index) {
            Some(last) => last,
            None => {
                proof {
                    if records(v, entries as nat) { record_at(v, entries as nat, index as int); }
                    assert(!valid(v)) by { reveal(valid); }
                }
                return None;
            },
        };
        let logical = bytes::read_le32(raw, 12 + index * 12).unwrap();
        assert(key(raw@, index as int) == logical as nat) by { reveal(key); }
        if (logical as u64) < previous_end {
            proof { if records(v, entries as nat) {
                if index == 0 { assert(previous_end == 0); }
                else { neighboring_records(v, entries as nat, index as int); }
            }
                assert(!valid(v)) by { reveal(valid); }
            }
            return None;
        }
        proof { append_record(v, index as nat); }
        previous_end = last;
        index += 1;
    }
    Some(Node { raw, blocks, kind, entries, maximum, depth })
}

pub fn parse_inline_root<'a>(raw: &'a [u8], blocks: u64) -> (r: Option<Node<'a>>)
    ensures match r {
        Some(node) => node.wf() && node.view() == (NodeView { raw: raw@, blocks, kind: NodeKind::Inline }),
        None => !valid(NodeView { raw: raw@, blocks, kind: NodeKind::Inline }),
    },
{
    parse(raw, blocks, NodeKind::Inline)
}

pub open spec fn block_kind(checksum: BlockChecksum) -> NodeKind {
    match checksum { BlockChecksum::Legacy => NodeKind::LegacyBlock, BlockChecksum::Crc32c(seed) => NodeKind::ChecksummedBlock(seed) }
}

pub fn parse_block<'a>(raw: &'a [u8], blocks: u64, checksum: BlockChecksum) -> (r: Option<Node<'a>>)
    ensures match r {
        Some(node) => node.wf() && node.view() == (NodeView { raw: raw@, blocks, kind: block_kind(checksum) }),
        None => !valid(NodeView { raw: raw@, blocks, kind: block_kind(checksum) }),
    },
{
    let kind = match checksum { BlockChecksum::Legacy => NodeKind::LegacyBlock, BlockChecksum::Crc32c(seed) => NodeKind::ChecksummedBlock(seed) };
    parse(raw, blocks, kind)
}

}
