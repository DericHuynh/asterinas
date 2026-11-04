// SPDX-License-Identifier: MPL-2.0

//! Extent interval foundation with 64-bit physical arithmetic and Linux's
//! 48-bit on-disk starts. Split preserves the complete logical/physical map.
//! These descriptors convey no allocation or initialized-data authority.

use vstd::prelude::*;
use crate::{block_range::BlockRange, bytes, extent};

verus! {

pub const PHYSICAL_START_LIMIT: u64 = 281474976710656;
pub enum ExtentState { Written, Unwritten }

#[verifier::ext_equal]
pub struct SpanView { pub logical: u32, pub length: u32, pub physical: u64, pub initialized: bool, pub blocks: u64 }

pub open spec fn valid(v: SpanView) -> bool {
    &&& 0 < v.length <= if v.initialized { 32768u32 } else { 32767u32 }
    &&& v.logical as nat + v.length <= extent::MAX_LOGICAL_END
    &&& 0 < v.physical && v.physical as nat + v.length <= v.blocks
}

pub open spec fn physical(raw: Seq<u8>, offset: int) -> nat {
    bytes::le32(raw, offset + 8) + 4294967296 * bytes::le16(raw, offset + 6)
}

pub open spec fn accepted(raw: Seq<u8>, offset: int, blocks: u64) -> bool {
    &&& 0 <= offset && offset + 12 <= raw.len()
    &&& bytes::le16(raw, offset + 4) > 0
    &&& bytes::le32(raw, offset) + extent::length(bytes::le16(raw, offset + 4)) <= extent::MAX_LOGICAL_END
    &&& physical(raw, offset) > 0
    &&& physical(raw, offset) + extent::length(bytes::le16(raw, offset + 4)) <= blocks
}

pub open spec fn represents(v: SpanView, raw: Seq<u8>, offset: int) -> bool {
    &&& v.logical as nat == bytes::le32(raw, offset)
    &&& v.physical as nat == physical(raw, offset)
    &&& v.length as nat == extent::length(bytes::le16(raw, offset + 4))
    &&& v.initialized == (bytes::le16(raw, offset + 4) <= 32768)
}

pub open spec fn mapping(v: SpanView, logical: u32) -> Option<u64> {
    if v.logical <= logical < v.logical as nat + v.length {
        Some((v.physical as nat + logical - v.logical) as u64)
    } else { None }
}

pub open spec fn mergeable(a: SpanView, b: SpanView) -> bool {
    &&& a.initialized == b.initialized && a.blocks == b.blocks
    &&& a.logical as nat + a.length == b.logical && a.physical as nat + a.length == b.physical
    &&& a.length as nat + b.length <= if a.initialized { 32768nat } else { 32767nat }
}

pub struct ExtentSpan { logical: u32, length: u32, range: BlockRange, state: ExtentState }

impl ExtentSpan {
    pub closed spec fn view(&self) -> SpanView {
        SpanView { logical: self.logical, length: self.length, physical: self.range.view().start,
            initialized: self.state is Written, blocks: self.range.view().limit }
    }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() && self.range.view().length == self.length }

    pub fn new(logical: u32, length: u32, physical: u64, state: ExtentState, blocks: u64) -> (r: Option<Self>)
        ensures match r {
            Some(span) => span.wf() && span.view() == (SpanView { logical, length, physical, initialized: state is Written, blocks }),
            None => !valid(SpanView { logical, length, physical, initialized: state is Written, blocks }),
        },
    {
        let max_length = match state { ExtentState::Written => 32768u32, ExtentState::Unwritten => 32767u32 };
        if length == 0 || length > max_length || logical as u64 + length as u64 > extent::MAX_LOGICAL_END || physical == 0 { return None; }
        let range = match BlockRange::new(physical, length as u64, blocks) { Some(range) => range, None => { return None; } };
        Some(ExtentSpan { logical, length, range, state })
    }

    pub fn info(&self) -> (r: SpanView) ensures self.wf(), r == self.view() {
        proof { use_type_invariant(self); }
        SpanView { logical: self.logical, length: self.length, physical: self.range.start(),
            initialized: match self.state { ExtentState::Written => true, ExtentState::Unwritten => false }, blocks: self.range.limit() }
    }

    // Unwritten extents have backing blocks too; returning this description
    // never grants permission to expose their previous contents.
    pub fn physical_block(&self, logical: u32) -> (r: Option<u64>) ensures self.wf(), r == mapping(self.view(), logical) {
        proof { use_type_invariant(self); }
        if logical < self.logical || logical as u64 >= self.logical as u64 + self.length as u64 { return None; }
        Some(self.range.start() + (logical - self.logical) as u64)
    }

    pub fn encode(&self) -> (r: Option<[u8; 12]>)
        ensures self.wf(), match r {
            Some(raw) => self.view().physical < PHYSICAL_START_LIMIT && accepted(raw@, 0, self.view().blocks)
                && represents(self.view(), raw@, 0),
            None => self.view().physical >= PHYSICAL_START_LIMIT,
        },
    {
        proof { use_type_invariant(self); }
        let physical = self.range.start();
        if physical >= PHYSICAL_START_LIMIT { return None; }
        let low = bytes::encode_le32((physical % 4294967296) as u32);
        let high = bytes::encode_le16((physical / 4294967296) as u16);
        let logical = bytes::encode_le32(self.logical);
        let length = bytes::encode_le16(match self.state {
            ExtentState::Written => self.length as u16, ExtentState::Unwritten => (self.length + 32768) as u16,
        });
        proof { vstd::arithmetic::div_mod::lemma_fundamental_div_mod(physical as int, 4294967296); }
        Some([logical[0], logical[1], logical[2], logical[3], length[0], length[1], high[0], high[1], low[0], low[1], low[2], low[3]])
    }

    pub fn split(&self, left: u32) -> (r: Option<(Self, Self)>)
        ensures self.wf(), match r {
            Some((a, b)) => 0 < left < self.view().length && a.wf() && b.wf()
                && a.view() == (SpanView { length: left, ..self.view() })
                && b.view() == (SpanView { logical: (self.view().logical + left) as u32, length: (self.view().length - left) as u32,
                    physical: (self.view().physical + left) as u64, ..self.view() }),
            None => left == 0 || left >= self.view().length,
        },
    {
        proof { use_type_invariant(self); }
        if left == 0 || left >= self.length { return None; }
        let (a, b) = self.range.split(left as u64).unwrap();
        let left_state = match self.state { ExtentState::Written => ExtentState::Written, ExtentState::Unwritten => ExtentState::Unwritten };
        let right_state = match self.state { ExtentState::Written => ExtentState::Written, ExtentState::Unwritten => ExtentState::Unwritten };
        Some((ExtentSpan { logical: self.logical, length: left, range: a, state: left_state },
            ExtentSpan { logical: self.logical + left, length: self.length - left, range: b, state: right_state }))
    }

    pub fn merge(&self, other: &Self) -> (r: Option<Self>)
        ensures self.wf(), other.wf(), match r {
            Some(joined) => mergeable(self.view(), other.view()) && joined.wf()
                && joined.view() == (SpanView { length: (self.view().length + other.view().length) as u32, ..self.view() }),
            None => !mergeable(self.view(), other.view()),
        },
    {
        proof { use_type_invariant(self); use_type_invariant(other); }
        let a = self.info();
        let b = other.info();
        let length = a.length + b.length;
        let max_length = if a.initialized { 32768u32 } else { 32767u32 };
        if a.initialized != b.initialized || a.blocks != b.blocks || a.logical as u64 + a.length as u64 != b.logical as u64
            || a.physical + a.length as u64 != b.physical || length > max_length { return None; }
        let state = if a.initialized { ExtentState::Written } else { ExtentState::Unwritten };
        Some(ExtentSpan::new(a.logical, length, a.physical, state, a.blocks).unwrap())
    }
}

pub fn parse(raw: &[u8], offset: usize, blocks: u64) -> (r: Option<ExtentSpan>)
    ensures match r {
        Some(span) => span.wf() && span.view().blocks == blocks && accepted(raw@, offset as int, blocks) && represents(span.view(), raw@, offset as int),
        None => !accepted(raw@, offset as int, blocks),
    },
{
    if offset > raw.len() || raw.len() - offset < 12 { return None; }
    let logical = bytes::read_le32(raw, offset).unwrap();
    let encoded_length = bytes::read_le16(raw, offset + 4).unwrap();
    let high = bytes::read_le16(raw, offset + 6).unwrap() as u64;
    let low = bytes::read_le32(raw, offset + 8).unwrap() as u64;
    let physical = low + high * 4294967296;
    let length = if encoded_length <= 32768 { encoded_length as u32 } else { encoded_length as u32 - 32768 };
    let state = if encoded_length <= 32768 { ExtentState::Written } else { ExtentState::Unwritten };
    ExtentSpan::new(logical, length, physical, state, blocks)
}

pub proof fn splitting_preserves_every_mapping(before: SpanView, left: u32, logical: u32)
    requires valid(before), 0 < left < before.length,
    ensures {
        let a = SpanView { length: left, ..before };
        let b = SpanView { logical: (before.logical + left) as u32, length: (before.length - left) as u32,
            physical: (before.physical + left) as u64, ..before };
        &&& valid(a) && valid(b)
        &&& mapping(before, logical) == if mapping(a, logical).is_some() { mapping(a, logical) } else { mapping(b, logical) }
        &&& !(mapping(a, logical).is_some() && mapping(b, logical).is_some())
    },
{
}

pub proof fn merging_preserves_every_mapping(a: SpanView, b: SpanView, logical: u32)
    requires valid(a), valid(b), mergeable(a, b),
    ensures {
        let joined = SpanView { length: (a.length + b.length) as u32, ..a };
        &&& valid(joined)
        &&& mapping(joined, logical) == if mapping(a, logical).is_some() { mapping(a, logical) } else { mapping(b, logical) }
        &&& !(mapping(a, logical).is_some() && mapping(b, logical).is_some())
    },
{
}

}
