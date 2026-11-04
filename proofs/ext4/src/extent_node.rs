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
