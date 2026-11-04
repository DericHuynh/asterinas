// SPDX-License-Identifier: MPL-2.0

//! Overflow-safe 64-bit filesystem block intervals. These are descriptions,
//! not allocation, lock, CortenMM frame or I/O capabilities.

use vstd::prelude::*;

verus! {

#[verifier::ext_equal]
pub struct RangeView { pub start: u64, pub length: u64, pub limit: u64 }

pub open spec fn valid(v: RangeView) -> bool { v.length > 0 && v.start as nat + v.length <= v.limit }
pub open spec fn contains(v: RangeView, block: u64) -> bool { v.start <= block < v.start as nat + v.length }
pub open spec fn disjoint(a: RangeView, b: RangeView) -> bool {
    a.start as nat + a.length <= b.start || b.start as nat + b.length <= a.start
}

pub struct BlockRange { start: u64, length: u64, limit: u64 }

impl BlockRange {
    pub closed spec fn view(&self) -> RangeView { RangeView { start: self.start, length: self.length, limit: self.limit } }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn new(start: u64, length: u64, limit: u64) -> (r: Option<Self>)
        ensures match r {
            Some(range) => range.wf() && range.view() == (RangeView { start, length, limit }),
            None => !valid(RangeView { start, length, limit }),
        },
    {
        if length == 0 || start >= limit || length > limit - start { return None; }
        Some(BlockRange { start, length, limit })
    }

    pub fn start(&self) -> (r: u64) ensures self.wf(), r == self.view().start {
        proof { use_type_invariant(self); }
        self.start
    }

    pub fn length(&self) -> (r: u64) ensures self.wf(), r == self.view().length {
        proof { use_type_invariant(self); }
        self.length
    }

    pub fn limit(&self) -> (r: u64) ensures self.wf(), r == self.view().limit {
        proof { use_type_invariant(self); }
        self.limit
    }

    pub fn has_block(&self, block: u64) -> (r: bool) ensures self.wf(), r == contains(self.view(), block) {
        proof { use_type_invariant(self); }
        block >= self.start && block - self.start < self.length
    }

    pub fn is_disjoint(&self, other: &Self) -> (r: bool) ensures self.wf(), other.wf(), r == disjoint(self.view(), other.view()) {
        proof { use_type_invariant(self); use_type_invariant(other); }
        if self.start < other.start { self.length <= other.start - self.start }
        else { other.length <= self.start - other.start }
    }

    pub fn split(&self, left: u64) -> (r: Option<(Self, Self)>)
        ensures self.wf(), match r {
            Some((a, b)) => 0 < left < self.view().length && a.wf() && b.wf()
                && a.view() == (RangeView { start: self.view().start, length: left, limit: self.view().limit })
                && b.view() == (RangeView { start: (self.view().start + left) as u64, length: (self.view().length - left) as u64, limit: self.view().limit })
                && disjoint(a.view(), b.view()),
            None => left == 0 || left >= self.view().length,
        },
    {
        proof { use_type_invariant(self); }
        if left == 0 || left >= self.length { return None; }
        Some((BlockRange { start: self.start, length: left, limit: self.limit },
            BlockRange { start: self.start + left, length: self.length - left, limit: self.limit }))
    }
}

pub proof fn split_is_an_exact_disjoint_partition(before: RangeView, left: u64, block: u64)
    requires valid(before), 0 < left < before.length,
    ensures {
        let a = RangeView { start: before.start, length: left, limit: before.limit };
        let b = RangeView { start: (before.start + left) as u64, length: (before.length - left) as u64, limit: before.limit };
        &&& valid(a) && valid(b) && disjoint(a, b)
        &&& contains(before, block) == (contains(a, block) || contains(b, block))
        &&& !(contains(a, block) && contains(b, block))
    },
{
}

}
