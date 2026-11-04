// SPDX-License-Identifier: MPL-2.0

//! HTree hash intervals, inherited bounds and Linux probe/continuation closure.
//! Bounds select candidates; full byte names still decide identity.

use vstd::prelude::*;
use crate::htree::{self, Index, IndexView};

verus! {

#[derive(Clone, Copy)]
pub struct Bounds { pub lower: u32, pub upper: u64, pub inclusive: bool }
pub open spec fn valid(b: Bounds) -> bool { b.lower as nat <= b.upper <= 4294967296 }
pub open spec fn contains(b: Bounds, hash: u32) -> bool {
    b.lower <= hash && ((hash as nat) < b.upper || hash as nat == b.upper && b.inclusive)
}
pub open spec fn fits(parent: Bounds, next: Bounds) -> bool {
    valid(parent) && valid(next) && parent.lower <= next.lower && next.upper <= parent.upper
        && (next.upper == parent.upper && next.inclusive ==> parent.inclusive)
}
pub open spec fn child(v: IndexView, parent: Bounds, i: nat) -> Bounds {
    let following = htree::edge(v.raw, v.first as nat, i + 1).hash;
    Bounds { lower: if i == 0 { parent.lower } else { htree::edge(v.raw, v.first as nat, i).hash & !1u32 },
        upper: if i + 1 < htree::count(v) { (following & !1u32) as u64 } else { parent.upper },
        inclusive: if i + 1 < htree::count(v) { following & 1u32 != 0 } else { parent.inclusive } }
}
pub open spec fn candidate(v: IndexView, hash: u32, start: nat, i: nat) -> bool {
    htree::selected(v, hash, start) && start <= i < htree::count(v)
        && forall|j: nat| start < j <= i ==> #[trigger] htree::continuation(v, hash, j)
}

pub fn full() -> (r: Bounds) ensures valid(r), r == (Bounds { lower: 0, upper: 4294967296, inclusive: false }),
{ Bounds { lower: 0, upper: 4294967296, inclusive: false } }
pub fn includes(bounds: &Bounds, hash: u32) -> (r: bool) ensures r == contains(*bounds, hash) {
    bounds.lower <= hash && ((hash as u64) < bounds.upper || hash as u64 == bounds.upper && bounds.inclusive)
}
pub fn subdivide(index: &Index<'_>, parent: &Bounds, i: usize) -> (r: Option<Bounds>)
    ensures index.wf(), match r { Some(next) => i < htree::count(index.view()) && next == child(index.view(), *parent, i as nat) && fits(*parent, next), None => true },
{
    let count = index.child_count();
    if parent.upper > 4294967296 || parent.lower as u64 > parent.upper { return None; }
    let current = match index.child(i) { Some(e) => e, None => { return None; } };
    let lower = if i == 0 { parent.lower } else { current.hash & !1u32 };
    let (upper, inclusive) = if i + 1 < count {
        let next = index.child(i + 1).unwrap(); ((next.hash & !1u32) as u64, next.hash & 1u32 != 0)
    } else { (parent.upper, parent.inclusive) };
    if lower as u64 > upper || lower < parent.lower || upper > parent.upper
        || upper == parent.upper && inclusive && !parent.inclusive { return None; }
    Some(Bounds { lower, upper, inclusive })
}

pub proof fn a_checked_child_interval_cannot_escape_its_parent(parent: Bounds, next: Bounds, hash: u32)
    requires fits(parent, next), contains(next, hash),
    ensures contains(parent, hash),
{ }

proof fn before_an_upper_boundary(hash: u32, boundary: u32)
    requires hash < boundary & !1u32 || hash == boundary & !1u32 && boundary & 1u32 != 0,
    ensures hash < boundary,
{
    assert(hash < boundary & !1u32 || hash == boundary & !1u32 && boundary & 1u32 != 0 ==> hash < boundary) by (bit_vector);
}
proof fn between_a_base_hash_and_its_boundary(hash: u32, boundary: u32)
    requires boundary > hash, hash >= boundary & !1u32,
    ensures hash == boundary & !1u32, boundary & 1u32 != 0,
{
    assert(boundary > hash && hash >= boundary & !1u32 ==> hash == boundary & !1u32 && boundary & 1u32 != 0) by (bit_vector);
}
proof fn an_intermediate_boundary_has_the_same_base(hash: u32, boundary: u32, end: u32)
    requires hash & 1u32 == 0, hash < boundary <= end, end & !1u32 == hash,
    ensures boundary & !1u32 == hash,
{
    assert(hash & 1u32 == 0 && hash < boundary <= end && end & !1u32 == hash ==> boundary & !1u32 == hash) by (bit_vector);
}

pub proof fn every_contained_hash_is_in_the_linux_probe_continuation_set(v: IndexView, parent: Bounds, i: nat, hash: u32, start: nat)
    requires htree::valid(v), i < htree::count(v), fits(parent, child(v, parent, i)), contains(child(v, parent, i), hash),
        hash & 1u32 == 0, htree::selected(v, hash, start),
    ensures candidate(v, hash, start, i),
{
    if i + 1 < htree::count(v) {
        let next = htree::edge(v.raw, v.first as nat, i + 1).hash;
        assert(hash < next & !1u32 || hash == next & !1u32 && next & 1u32 != 0);
        before_an_upper_boundary(hash, next);
        if start > i { htree::monotone(v, i + 1, start); }
    }
    assert(start <= i);
    if start < i {
        let end = htree::edge(v.raw, v.first as nat, i).hash;
        assert(i > 0 && end > hash && hash >= end & !1u32);
        between_a_base_hash_and_its_boundary(hash, end);
        assert forall|j: nat| start < j <= i implies #[trigger] htree::continuation(v, hash, j) by {
            htree::monotone(v, j, i);
            let boundary = htree::edge(v.raw, v.first as nat, j).hash;
            assert(boundary > hash);
            an_intermediate_boundary_has_the_same_base(hash, boundary, end);
        }
    }
}

#[verifier::opaque]
pub open spec fn initial(v: IndexView, hash: u32, length: nat) -> nat decreases length {
    if length <= 1 { 0nat } else if htree::edge(v.raw, v.first as nat, (length - 1) as nat).hash <= hash { (length - 1) as nat }
    else { initial(v, hash, (length - 1) as nat) }
}
proof fn an_initial_prefix_selects_the_last_eligible_boundary(v: IndexView, hash: u32, length: nat)
    requires length > 0,
    ensures initial(v, hash, length) < length, htree::edge(v.raw, v.first as nat, initial(v, hash, length)).hash <= hash,
        forall|j: nat| initial(v, hash, length) < j < length ==> (#[trigger] htree::edge(v.raw, v.first as nat, j)).hash > hash,
    decreases length,
{
    reveal(initial);
    if length > 1 && htree::edge(v.raw, v.first as nat, (length - 1) as nat).hash > hash {
        an_initial_prefix_selects_the_last_eligible_boundary(v, hash, (length - 1) as nat);
        assert forall|j: nat| initial(v, hash, length) < j < length implies (#[trigger] htree::edge(v.raw, v.first as nat, j)).hash > hash by {
            if j < length - 1 { assert(htree::edge(v.raw, v.first as nat, j).hash > hash); } else { assert(j == length - 1); }
        }
    }
}
pub proof fn every_checked_index_has_a_linux_probe_selection(v: IndexView, hash: u32)
    requires htree::valid(v),
    ensures exists|start: nat| #[trigger] htree::selected(v, hash, start),
{
    reveal(htree::table);
    an_initial_prefix_selects_the_last_eligible_boundary(v, hash, htree::count(v));
    assert(htree::selected(v, hash, initial(v, hash, htree::count(v))));
}
pub open spec fn possible(v: IndexView, hash: u32, i: nat) -> bool { exists|start: nat| #[trigger] candidate(v, hash, start, i) }

}
