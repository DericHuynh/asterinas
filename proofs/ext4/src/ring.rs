// SPDX-License-Identifier: MPL-2.0

//! Bounded logical journal reservations. These are positions in a validated
//! journal mapping, not physical BIO addresses or a proof of retirement.

use vstd::prelude::*;

verus! {

pub open spec fn position(first: u32, end: u32, start: u32, index: u32) -> nat {
    if start as int + index < end { start as nat + index as nat }
    else { (first as int + start as int + index - end) as nat }
}

pub fn slot(first: u32, end: u32, start: u32, index: u32) -> (r: Option<u32>)
    ensures match r {
        Some(p) => 0 < first <= start < end && index < end - first
            && first <= p < end && p as nat == position(first, end, start, index),
        None => first == 0 || first > start || start >= end
            || index as int >= end as int - first,
    },
{
    if first == 0 || first > start || start >= end || index >= end - first { return None; }
    let remaining = end - start;
    Some(if index < remaining { start + index } else { first + (index - remaining) })
}

pub struct Credits { pub payloads: u32, pub total: u32 }

/// A bounded transaction uses one descriptor and one commit block. Reserving
/// space does not authorize any home-block mutation or disk-slot reuse.
pub fn reserve(payloads: u32, capacity: u32) -> (r: Option<Credits>)
    ensures match r {
        Some(c) => 0 < payloads <= 250 && payloads as int + 2 <= capacity
            && c.payloads == payloads && c.total as int == payloads as int + 2,
        None => payloads == 0 || payloads > 250 || payloads as int + 2 > capacity,
    },
{
    if payloads == 0 || payloads > 250 || capacity < 2 || payloads > capacity - 2 { None }
    else { Some(Credits { payloads, total: payloads + 2 }) }
}

pub proof fn reservations_have_no_duplicate_slots(first: u32, end: u32, start: u32, i: u32, j: u32)
    requires 0 < first <= start < end, i < end - first, j < end - first, i != j,
    ensures position(first, end, start, i) != position(first, end, start, j),
{
}

pub proof fn reservations_never_include_the_superblock(first: u32, end: u32, start: u32, i: u32)
    requires 0 < first <= start < end, i < end - first,
    ensures 0 < position(first, end, start, i) < end,
{
}

}
