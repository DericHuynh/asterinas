// SPDX-License-Identifier: MPL-2.0

//! Owned extent-set mutations and a bounded Linux extent-tree rebuilding plan.
//! Supplied block numbers are checked descriptions. This module does not mint
//! allocation, frame, initialized-data, replay or write authority.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, crc, extent_node::{self, BlockChecksum}, extent_span::{ExtentSpan, ExtentState}};

verus! {

pub const MAX_EXTENTS: usize = 65536;
pub const MAX_METADATA_NODES: usize = 65536;
pub const PHYSICAL_LIMIT: u64 = 281474976710656;
pub const LOGICAL_END: u64 = 4294967295;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Error {
    Geometry, Range, Order, LogicalOverlap, PhysicalAlias, AddressTooWide,
    MetadataAlias, MetadataPool, Hole, Depth, Budget, Encoding,
}

#[derive(Clone, Copy)]
pub struct Run { pub logical: u32, pub length: u32, pub physical: u64, pub initialized: bool }

pub enum Mapping { Hole, Written(u64), Unwritten(u64) }

pub struct ExtentSet { runs: Vec<Run>, blocks: u64, budget: usize }

pub struct SetView { pub runs: Seq<Run>, pub blocks: u64, pub budget: nat }
pub open spec fn logical_end(run: Run) -> nat { run.logical as nat + run.length as nat }
pub open spec fn physical_end(run: Run) -> nat { run.physical as nat + run.length as nat }
pub open spec fn maximum_length(run: Run) -> nat { if run.initialized { 32768nat } else { 32767nat } }
pub open spec fn interval_valid(run: Run, blocks: u64) -> bool {
    &&& 0 < run.length && logical_end(run) <= LOGICAL_END
    &&& 0 < run.physical < PHYSICAL_LIMIT && physical_end(run) <= blocks
}
pub open spec fn ordered_intervals(runs: Seq<Run>, blocks: u64) -> bool {
    &&& forall|i: int| 0 <= i < runs.len() ==> #[trigger] interval_valid(runs[i], blocks)
    &&& forall|i: int, j: int| 0 <= i < j < runs.len() ==> logical_end(runs[i]) <= runs[j].logical
}
pub open spec fn wire_runs(runs: Seq<Run>, blocks: u64) -> bool {
    &&& ordered_intervals(runs, blocks)
    &&& forall|i: int| 0 <= i < runs.len() ==> runs[i].length <= #[trigger] maximum_length(runs[i])
    &&& forall|i: int| 0 < i < runs.len() ==>
        (runs[i - 1].initialized == runs[i].initialized
         && logical_end(runs[i - 1]) == runs[i].logical
         && physical_end(runs[i - 1]) == runs[i].physical)
        ==> runs[i - 1].length == maximum_length(runs[i - 1])
}
pub open spec fn no_physical_alias(runs: Seq<Run>) -> bool {
    forall|i: int, j: int| 0 <= i < j < runs.len() ==>
        physical_end(runs[i]) <= runs[j].physical || physical_end(runs[j]) <= runs[i].physical
}
#[verifier::opaque]
pub open spec fn valid_set(v: SetView) -> bool {
    &&& v.blocks > 0 && v.runs.len() <= v.budget <= MAX_EXTENTS
    &&& wire_runs(v.runs, v.blocks) && no_physical_alias(v.runs)
}
#[verifier::opaque]
pub open spec fn mapping_at(runs: Seq<Run>, logical: nat) -> Mapping
    decreases runs.len(),
{
    if runs.len() == 0 { Mapping::Hole } else {
        let run = runs[0];
        if run.logical <= logical < logical_end(run) {
            let physical = (run.physical as nat + logical - run.logical as nat) as u64;
            if run.initialized { Mapping::Written(physical) } else { Mapping::Unwritten(physical) }
        } else { mapping_at(runs.drop_first(), logical) }
    }
}
pub open spec fn replace_map(before: Seq<Run>, after: Seq<Run>, run: Run) -> bool {
    forall|logical: nat| logical < LOGICAL_END ==> #[trigger] mapping_at(after, logical)
        == if run.logical <= logical < logical_end(run) {
            let physical = (run.physical as nat + logical - run.logical as nat) as u64;
            if run.initialized { Mapping::Written(physical) } else { Mapping::Unwritten(physical) }
        } else { mapping_at(before, logical) }
}
pub open spec fn remove_map(before: Seq<Run>, after: Seq<Run>, first: nat, end: nat) -> bool {
    forall|logical: nat| logical < LOGICAL_END ==> #[trigger] mapping_at(after, logical)
        == if first <= logical < end { Mapping::Hole } else { mapping_at(before, logical) }
}
pub open spec fn convert_map(before: Seq<Run>, after: Seq<Run>, first: nat, end: nat, initialized: bool) -> bool {
    forall|logical: nat| logical < LOGICAL_END ==> #[trigger] mapping_at(after, logical)
        == if first <= logical < end {
            match mapping_at(before, logical) {
                Mapping::Written(physical) | Mapping::Unwritten(physical) =>
                    if initialized { Mapping::Written(physical) } else { Mapping::Unwritten(physical) },
                Mapping::Hole => Mapping::Hole,
            }
        } else { mapping_at(before, logical) }
}
pub open spec fn occurrences<T>(items: Seq<T>, value: T) -> nat
    decreases items.len(),
{
    if items.len() == 0 { 0nat } else {
        occurrences(items.drop_last(), value) + if items.last() == value { 1nat } else { 0nat }
    }
}
pub open spec fn same_multiset<T>(first: Seq<T>, second: Seq<T>) -> bool {
    first.len() == second.len() && forall|value: T| #[trigger] occurrences(first, value) == occurrences(second, value)
}
pub open spec fn physically_sorted(runs: Seq<Run>) -> bool {
    forall|i: int, j: int| 0 <= i < j < runs.len() ==> runs[i].physical <= runs[j].physical
}
pub open spec fn addresses_sorted(addresses: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < addresses.len() ==> addresses[i] <= addresses[j]
}

proof fn occurrences_are_membership<T>(items: Seq<T>, value: T)
    ensures (occurrences(items, value) > 0) == items.contains(value),
    decreases items.len(),
{
    if items.len() > 0 {
        occurrences_are_membership(items.drop_last(), value);
        assert(items =~= items.drop_last().push(items.last()));
    }
}
proof fn occurrences_concatenate<T>(first: Seq<T>, second: Seq<T>, value: T)
    ensures occurrences(first + second, value) == occurrences(first, value) + occurrences(second, value),
    decreases second.len(),
{
    if second.len() == 0 { assert(first + second =~= first); }
    else {
        assert((first + second).drop_last() =~= first + second.drop_last());
        assert((first + second).last() == second.last());
        occurrences_concatenate(first, second.drop_last(), value);
    }
}
proof fn occurrences_subrange_step<T>(items: Seq<T>, first: int, end: int, value: T)
    requires 0 <= first <= end < items.len(),
    ensures occurrences(items.subrange(first, end + 1), value)
        == occurrences(items.subrange(first, end), value) + if items[end] == value { 1nat } else { 0nat },
{
    assert(items.subrange(first, end + 1).drop_last() =~= items.subrange(first, end));
    assert(items.subrange(first, end + 1).last() == items[end]);
}
proof fn mapping_concatenate(first: Seq<Run>, second: Seq<Run>, logical: nat)
    ensures mapping_at(first + second, logical)
        == if mapping_at(first, logical) is Hole { mapping_at(second, logical) } else { mapping_at(first, logical) },
    decreases first.len(),
{
    reveal(mapping_at);
    if first.len() == 0 { assert(first + second =~= second); }
    else {
        assert((first + second).drop_first() =~= first.drop_first() + second);
        mapping_concatenate(first.drop_first(), second, logical);
    }
}
proof fn mapping_absent(runs: Seq<Run>, logical: nat)
    requires forall|i: int| 0 <= i < runs.len() ==>
        !(runs[i].logical <= logical < #[trigger] logical_end(runs[i])),
    ensures mapping_at(runs, logical) is Hole,
    decreases runs.len(),
{
    reveal(mapping_at);
    if runs.len() > 0 { mapping_absent(runs.drop_first(), logical); }
}
proof fn mapping_selected_entry(runs: Seq<Run>, blocks: u64, index: int, logical: nat)
    requires ordered_intervals(runs, blocks), 0 <= index < runs.len(),
        runs[index].logical <= logical < logical_end(runs[index]),
    ensures mapping_at(runs, logical) == {
        let run = runs[index];
        let physical = (run.physical as nat + logical - run.logical as nat) as u64;
        if run.initialized { Mapping::Written(physical) } else { Mapping::Unwritten(physical) }
    },
    decreases index,
{
    reveal(mapping_at);
    if index > 0 {
        assert(logical_end(runs[0]) <= runs[index].logical);
        mapping_selected_entry(runs.drop_first(), blocks, index - 1, logical);
    }
}
proof fn mapping_has_a_covering_entry(runs: Seq<Run>, logical: nat)
    requires !(mapping_at(runs, logical) is Hole),
    ensures exists|i: int| 0 <= i < runs.len()
        && runs[i].logical <= logical < #[trigger] logical_end(runs[i])
        && mapping_at(runs, logical) == mapping_at(seq![runs[i]], logical),
    decreases runs.len(),
{
    reveal(mapping_at);
    if runs.len() > 0 {
        if runs[0].logical <= logical < logical_end(runs[0]) {
            assert(exists|i: int| 0 <= i < runs.len()
                && runs[i].logical <= logical < #[trigger] logical_end(runs[i])
                && mapping_at(runs, logical) == mapping_at(seq![runs[i]], logical)) by {
                assert(runs[0].logical <= logical < logical_end(runs[0]));
            }
        } else {
            mapping_has_a_covering_entry(runs.drop_first(), logical);
            let i = choose|i: int| 0 <= i < runs.drop_first().len()
                && runs.drop_first()[i].logical <= logical < logical_end(runs.drop_first()[i])
                && mapping_at(runs.drop_first(), logical) == mapping_at(seq![runs.drop_first()[i]], logical);
            assert(exists|j: int| 0 <= j < runs.len()
                && runs[j].logical <= logical < #[trigger] logical_end(runs[j])
                && mapping_at(runs, logical) == mapping_at(seq![runs[j]], logical)) by {
                assert(runs[i + 1] == runs.drop_first()[i]);
            }
        }
    }
}
proof fn sorted_neighbors_imply_physical_disjointness(runs: Seq<Run>)
    requires physically_sorted(runs),
        forall|i: int| 0 < i < runs.len() ==> physical_end(runs[i - 1]) <= runs[i].physical,
    ensures no_physical_alias(runs),
{
    assert forall|i: int, j: int| 0 <= i < j < runs.len()
        implies physical_end(runs[i]) <= runs[j].physical || physical_end(runs[j]) <= runs[i].physical by {
        assert(physical_end(runs[i]) <= runs[i + 1].physical);
        if i + 1 < j { assert(runs[i + 1].physical <= runs[j].physical); }
    }
}
proof fn physical_disjointness_transfers_by_multiset(before: Seq<Run>, after: Seq<Run>, blocks: u64)
    requires ordered_intervals(before, blocks), same_multiset(before, after), no_physical_alias(after),
    ensures no_physical_alias(before),
{
    assert forall|i: int, j: int| 0 <= i < j < before.len()
        implies physical_end(before[i]) <= before[j].physical || physical_end(before[j]) <= before[i].physical by {
        assert(before[i].logical < before[j].logical);
        occurrences_are_membership(before, before[i]);
        occurrences_are_membership(before, before[j]);
        occurrences_are_membership(after, before[i]);
        occurrences_are_membership(after, before[j]);
        assert(after.contains(before[i]) && after.contains(before[j]));
        let a = choose|a: int| 0 <= a < after.len() && after[a] == before[i];
        let b = choose|b: int| 0 <= b < after.len() && after[b] == before[j];
        assert(a != b);
        if a < b { assert(physical_end(after[a]) <= after[b].physical || physical_end(after[b]) <= after[a].physical); }
        else { assert(physical_end(after[b]) <= after[a].physical || physical_end(after[a]) <= after[b].physical); }
    }
}

pub open spec fn mapped_physical(mapping: Mapping) -> Option<u64> {
    match mapping { Mapping::Written(physical) | Mapping::Unwritten(physical) => Some(physical), Mapping::Hole => None }
}
proof fn disjoint_runs_map_storage_injectively(runs: Seq<Run>, blocks: u64,
    first: nat, second: nat, physical: u64)
    requires ordered_intervals(runs, blocks), no_physical_alias(runs),
        mapped_physical(mapping_at(runs, first)) == Some(physical),
        mapped_physical(mapping_at(runs, second)) == Some(physical),
    ensures first == second,
{
    mapping_has_a_covering_entry(runs, first);
    mapping_has_a_covering_entry(runs, second);
    let a = choose|a: int| 0 <= a < runs.len() && runs[a].logical <= first < logical_end(runs[a])
        && mapping_at(runs, first) == mapping_at(seq![runs[a]], first);
    let b = choose|b: int| 0 <= b < runs.len() && runs[b].logical <= second < logical_end(runs[b])
        && mapping_at(runs, second) == mapping_at(seq![runs[b]], second);
    reveal(mapping_at);
    assert(runs[a].physical <= physical < physical_end(runs[a]));
    assert(runs[b].physical <= physical < physical_end(runs[b]));
    if a < b { assert(physical_end(runs[a]) <= runs[b].physical || physical_end(runs[b]) <= runs[a].physical); }
    else if b < a { assert(physical_end(runs[b]) <= runs[a].physical || physical_end(runs[a]) <= runs[b].physical); }
    assert(a == b);
    assert(first == second);
}
proof fn logical_map_equality_preserves_nonalias(before: Seq<Run>, after: Seq<Run>, blocks: u64)
    requires ordered_intervals(before, blocks), ordered_intervals(after, blocks), no_physical_alias(after),
        forall|logical: nat| logical < LOGICAL_END ==> #[trigger] mapping_at(before, logical) == mapping_at(after, logical),
    ensures no_physical_alias(before),
{
    assert forall|i: int, j: int| 0 <= i < j < before.len()
        implies physical_end(before[i]) <= before[j].physical || physical_end(before[j]) <= before[i].physical by {
        if physical_end(before[i]) > before[j].physical && physical_end(before[j]) > before[i].physical {
            let physical = if before[i].physical > before[j].physical { before[i].physical } else { before[j].physical };
            let first = (before[i].logical as nat + physical as nat - before[i].physical as nat) as nat;
            let second = (before[j].logical as nat + physical as nat - before[j].physical as nat) as nat;
            assert(before[i].logical <= first < logical_end(before[i]));
            assert(before[j].logical <= second < logical_end(before[j]));
            assert(first < LOGICAL_END && second < LOGICAL_END);
            mapping_selected_entry(before, blocks, i, first);
            mapping_selected_entry(before, blocks, j, second);
            assert(mapped_physical(mapping_at(before, first)) == Some(physical));
            assert(mapped_physical(mapping_at(before, second)) == Some(physical));
            disjoint_runs_map_storage_injectively(after, blocks, first, second, physical);
            assert(first < logical_end(before[i]) <= before[j].logical <= second);
        }
    }
}
proof fn mapping_equivalence_survives_append(first: Seq<Run>, second: Seq<Run>, suffix: Seq<Run>)
    requires forall|logical: nat| logical < LOGICAL_END ==>
        #[trigger] mapping_at(first, logical) == mapping_at(second, logical),
    ensures forall|logical: nat| logical < LOGICAL_END ==>
        #[trigger] mapping_at(first + suffix, logical) == mapping_at(second + suffix, logical),
{
    assert forall|logical: nat| logical < LOGICAL_END implies
        #[trigger] mapping_at(first + suffix, logical) == mapping_at(second + suffix, logical) by {
        mapping_concatenate(first, suffix, logical);
        mapping_concatenate(second, suffix, logical);
    }
}
proof fn removing_a_range_distributes_over_extent_sequences(before_first: Seq<Run>, before_second: Seq<Run>,
    after_first: Seq<Run>, after_second: Seq<Run>, first: nat, end: nat)
    requires remove_map(before_first, after_first, first, end), remove_map(before_second, after_second, first, end),
    ensures remove_map(before_first + before_second, after_first + after_second, first, end),
{
    assert forall|logical: nat| logical < LOGICAL_END implies
        #[trigger] mapping_at(after_first + after_second, logical)
            == if first <= logical < end { Mapping::Hole } else { mapping_at(before_first + before_second, logical) } by {
        mapping_concatenate(before_first, before_second, logical);
        mapping_concatenate(after_first, after_second, logical);
    }
}

pub proof fn one_logical_block_has_only_one_extent(v: SetView, first: int, second: int, logical: nat)
    requires valid_set(v), 0 <= first < v.runs.len(), 0 <= second < v.runs.len(),
        v.runs[first].logical <= logical < logical_end(v.runs[first]),
        v.runs[second].logical <= logical < logical_end(v.runs[second]),
    ensures first == second,
{ reveal(valid_set); }

pub proof fn distinct_extent_runs_cannot_alias_storage(v: SetView, first: int, second: int)
    requires valid_set(v), 0 <= first < second < v.runs.len(),
    ensures physical_end(v.runs[first]) <= v.runs[second].physical
        || physical_end(v.runs[second]) <= v.runs[first].physical,
{ reveal(valid_set); }

fn interval_ok(run: Run, blocks: u64) -> (r: bool)
    ensures r == interval_valid(run, blocks),
{
    run.length != 0 && run.logical as u64 + (run.length as u64) <= LOGICAL_END
        && run.physical != 0 && run.physical < PHYSICAL_LIMIT && run.physical < blocks
        && (run.length as u64) <= blocks - run.physical
}

/// Emit maximal adjacent runs, splitting at the written/unwritten length limit.
fn emit(out: &mut Vec<Run>, input: Run, blocks: u64, budget: usize) -> (r: Result<(), Error>)
    requires blocks > 0, old(out).len() <= budget <= MAX_EXTENTS, wire_runs(old(out)@, blocks),
        interval_valid(input, blocks) ==> ordered_intervals(old(out)@ + seq![input], blocks),
    ensures final(out).len() <= budget, wire_runs(final(out)@, blocks),
        match r {
            Ok(()) => interval_valid(input, blocks)
                && (forall|logical: nat| logical < LOGICAL_END ==>
                    #[trigger] mapping_at(final(out)@, logical) == mapping_at(old(out)@ + seq![input], logical)),
            Err(_) => true,
        },
{
    let ghost before = out@;
    if !interval_ok(input, blocks) { return Err(Error::Range); }
    let maximum = if input.initialized { 32768u32 } else { 32767u32 };
    let mut used = 0u32;
    while used < input.length
        invariant used <= input.length, out.len() <= budget <= MAX_EXTENTS,
            interval_valid(input, blocks), wire_runs(out@, blocks),
            forall|logical: nat| logical < LOGICAL_END ==> #[trigger] mapping_at(out@, logical)
                == if input.logical <= logical < input.logical as nat + used as nat {
                    let physical = (input.physical as nat + logical - input.logical as nat) as u64;
                    if input.initialized { Mapping::Written(physical) } else { Mapping::Unwritten(physical) }
                } else { mapping_at(before, logical) },
            out.len() > 0 ==> logical_end(out@[out.len() as int - 1]) <= input.logical as nat + used as nat,
        decreases input.length - used,
    {
        let logical = input.logical as u64 + used as u64;
        let physical = input.physical + used as u64;
        if physical >= PHYSICAL_LIMIT { return Err(Error::AddressTooWide); }
        let remaining = input.length - used;
        if out.len() != 0 {
            let at = out.len() - 1; let mut last = out[at];
            if last.initialized == input.initialized
                && last.logical as u64 + last.length as u64 == logical
                && last.physical + last.length as u64 == physical && last.length < maximum {
                let room = maximum - last.length;
                let take = if remaining < room { remaining } else { room };
                last.length += take; out[at] = last; used += take;
                continue;
            }
        }
        if out.len() >= budget { return Err(Error::Budget); }
        let take = if remaining < maximum { remaining } else { maximum };
        out.push(Run { logical: logical as u32, length: take, physical, initialized: input.initialized });
        used += take;
    }
    Ok(())
}

fn physical_order(input: &[Run]) -> (r: Result<Vec<Run>, Error>)
    ensures match r {
        Ok(sorted) => input.len() <= MAX_EXTENTS && same_multiset(input@, sorted@) && physically_sorted(sorted@),
        Err(_) => input.len() > MAX_EXTENTS,
    },
{
    if input.len() > MAX_EXTENTS { return Err(Error::Budget); }
    let mut current = Vec::<Run>::new(); let mut i = 0usize;
    while i < input.len()
        invariant i <= input.len() <= MAX_EXTENTS, current.len() == i, current@ == input@.take(i as int),
        decreases input.len() - i,
    { current.push(input[i]); i += 1; }
    let n = current.len(); let mut width = 1usize;
    while width < n
        invariant 1 <= width, width <= if n == 0 { 1usize } else { n }, n <= MAX_EXTENTS, current.len() == n,
            same_multiset(input@, current@),
            forall|left: int, right: int| 0 <= left < right < n && left / (width as int) == right / (width as int) ==>
                current@[left].physical <= current@[right].physical,
        decreases n - width,
    {
        let mut next = Vec::<Run>::new(); let mut left = 0usize;
        while left < n
            invariant left <= n, current.len() == n, next.len() == left, width > 0,
                same_multiset(input@, current@),
                forall|i: int, j: int| 0 <= i < j < n && i / (width as int) == j / (width as int) ==>
                    current@[i].physical <= current@[j].physical,
                (left as int) % (2 * width as int) == 0 || left == n,
                forall|i: int, j: int| 0 <= i < j < next.len()
                    && i / (2 * width as int) == j / (2 * width as int) ==>
                        next@[i].physical <= next@[j].physical,
                forall|value: Run| #[trigger] occurrences(next@, value)
                    == occurrences(current@.take(left as int), value),
            decreases n - left,
        {
            let middle = if width > n - left { n } else { left + width };
            let end = if width > n - middle { n } else { middle + width };
            let mut a = left; let mut b = middle;
            while a < middle || b < end
                invariant left <= a <= middle <= b <= end <= n, current.len() == n,
                    next.len() == left + (a - left) + (b - middle),
                    same_multiset(input@, current@),
                    forall|i: int, j: int| 0 <= i < j < n && i / (width as int) == j / (width as int) ==>
                        current@[i].physical <= current@[j].physical,
                    (left as int) % (2 * width as int) == 0, end <= left + 2 * width,
                    physically_sorted(next@.subrange(left as int, next.len() as int)),
                    next.len() > left && a < middle ==> next@.last().physical <= current@[a as int].physical,
                    next.len() > left && b < end ==> next@.last().physical <= current@[b as int].physical,
                    forall|i: int, j: int| 0 <= i < j < left && i / (2 * width as int) == j / (2 * width as int) ==>
                        next@[i].physical <= next@[j].physical,
                    forall|value: Run| #[trigger] occurrences(next@, value)
                        == occurrences(current@.take(left as int), value)
                         + occurrences(current@.subrange(left as int, a as int), value)
                         + occurrences(current@.subrange(middle as int, b as int), value),
                decreases middle - a + end - b,
            {
                let ghost previous_a = a;
                let ghost previous_b = b;
                let ghost previous_output = next@;
                if b >= end || (a < middle && current[a].physical <= current[b].physical) {
                    next.push(current[a]); a += 1;
                } else { next.push(current[b]); b += 1; }
                proof {
                    assert forall|value: Run| #[trigger] occurrences(next@, value)
                        == occurrences(current@.take(left as int), value)
                         + occurrences(current@.subrange(left as int, a as int), value)
                         + occurrences(current@.subrange(middle as int, b as int), value) by {
                        if a > previous_a {
                            occurrences_subrange_step(current@, left as int, previous_a as int, value);
                        } else {
                            occurrences_subrange_step(current@, middle as int, previous_b as int, value);
                        }
                    }
                }
            }
            proof {
                assert forall|value: Run| #[trigger] occurrences(next@, value)
                    == occurrences(current@.take(end as int), value) by {
                    occurrences_concatenate(current@.take(left as int),
                        current@.subrange(left as int, middle as int), value);
                    occurrences_concatenate(current@.take(middle as int),
                        current@.subrange(middle as int, end as int), value);
                    assert(current@.take(left as int) + current@.subrange(left as int, middle as int)
                        =~= current@.take(middle as int));
                    assert(current@.take(middle as int) + current@.subrange(middle as int, end as int)
                        =~= current@.take(end as int));
                }
            }
            left = end;
        }
        current = next;
        width = if width > n / 2 { n } else { width * 2 };
    }
    Ok(current)
}

fn address_order(input: &[u64]) -> (r: Result<Vec<u64>, Error>)
    ensures match r {
        Ok(sorted) => input.len() <= MAX_METADATA_NODES && same_multiset(input@, sorted@) && addresses_sorted(sorted@),
        Err(_) => input.len() > MAX_METADATA_NODES,
    },
{
    if input.len() > MAX_METADATA_NODES { return Err(Error::Budget); }
    let mut current = Vec::<u64>::new(); let mut i = 0usize;
    while i < input.len()
        invariant i <= input.len() <= MAX_METADATA_NODES, current.len() == i, current@ == input@.take(i as int),
        decreases input.len() - i,
    { current.push(input[i]); i += 1; }
    let n = current.len(); let mut width = 1usize;
    while width < n
        invariant 1 <= width, width <= if n == 0 { 1usize } else { n }, n <= MAX_METADATA_NODES, current.len() == n,
            same_multiset(input@, current@),
            forall|left: int, right: int| 0 <= left < right < n && left / (width as int) == right / (width as int) ==>
                current@[left] <= current@[right],
        decreases n - width,
    {
        let mut next = Vec::<u64>::new(); let mut left = 0usize;
        while left < n
            invariant left <= n, current.len() == n, next.len() == left, width > 0,
                same_multiset(input@, current@),
                forall|i: int, j: int| 0 <= i < j < n && i / (width as int) == j / (width as int) ==>
                    current@[i] <= current@[j],
                (left as int) % (2 * width as int) == 0 || left == n,
                forall|i: int, j: int| 0 <= i < j < next.len()
                    && i / (2 * width as int) == j / (2 * width as int) ==>
                        next@[i] <= next@[j],
                forall|value: u64| #[trigger] occurrences(next@, value)
                    == occurrences(current@.take(left as int), value),
            decreases n - left,
        {
            let middle = if width > n - left { n } else { left + width };
            let end = if width > n - middle { n } else { middle + width };
            let mut a = left; let mut b = middle;
            while a < middle || b < end
                invariant left <= a <= middle <= b <= end <= n, current.len() == n,
                    next.len() == left + (a - left) + (b - middle),
                    same_multiset(input@, current@),
                    forall|i: int, j: int| 0 <= i < j < n && i / (width as int) == j / (width as int) ==>
                        current@[i] <= current@[j],
                    (left as int) % (2 * width as int) == 0, end <= left + 2 * width,
                    addresses_sorted(next@.subrange(left as int, next.len() as int)),
                    next.len() > left && a < middle ==> next@.last() <= current@[a as int],
                    next.len() > left && b < end ==> next@.last() <= current@[b as int],
                    forall|i: int, j: int| 0 <= i < j < left && i / (2 * width as int) == j / (2 * width as int) ==>
                        next@[i] <= next@[j],
                    forall|value: u64| #[trigger] occurrences(next@, value)
                        == occurrences(current@.take(left as int), value)
                         + occurrences(current@.subrange(left as int, a as int), value)
                         + occurrences(current@.subrange(middle as int, b as int), value),
                decreases middle - a + end - b,
            {
                let ghost previous_a = a;
                let ghost previous_b = b;
                let ghost previous_output = next@;
                if b >= end || (a < middle && current[a] <= current[b]) {
                    next.push(current[a]); a += 1;
                } else { next.push(current[b]); b += 1; }
                proof {
                    assert forall|value: u64| #[trigger] occurrences(next@, value)
                        == occurrences(current@.take(left as int), value)
                         + occurrences(current@.subrange(left as int, a as int), value)
                         + occurrences(current@.subrange(middle as int, b as int), value) by {
                        if a > previous_a {
                            occurrences_subrange_step(current@, left as int, previous_a as int, value);
                        } else {
                            occurrences_subrange_step(current@, middle as int, previous_b as int, value);
                        }
                    }
                }
            }
            proof {
                assert forall|value: u64| #[trigger] occurrences(next@, value)
                    == occurrences(current@.take(end as int), value) by {
                    occurrences_concatenate(current@.take(left as int),
                        current@.subrange(left as int, middle as int), value);
                    occurrences_concatenate(current@.take(middle as int),
                        current@.subrange(middle as int, end as int), value);
                    assert(current@.take(left as int) + current@.subrange(left as int, middle as int)
                        =~= current@.take(middle as int));
                    assert(current@.take(middle as int) + current@.subrange(middle as int, end as int)
                        =~= current@.take(end as int));
                }
            }
            left = end;
        }
        current = next;
        width = if width > n / 2 { n } else { width * 2 };
    }
    Ok(current)
}

impl ExtentSet {
    pub closed spec fn view(&self) -> SetView {
        SetView { runs: self.runs@, blocks: self.blocks, budget: self.budget as nat }
    }
    pub open spec fn wf(&self) -> bool { valid_set(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn from_sorted(input: &[Run], filesystem_blocks: u64, extent_budget: usize) -> (r: Result<Self, Error>)
        ensures match r {
            Ok(set) => set.wf() && set.view().blocks == filesystem_blocks && set.view().budget == extent_budget
                && ordered_intervals(input@, filesystem_blocks) && no_physical_alias(input@)
                && (forall|logical: nat| logical < LOGICAL_END ==>
                    #[trigger] mapping_at(set.view().runs, logical) == mapping_at(input@, logical)),
            Err(_) => true,
        },
    {
        if filesystem_blocks == 0 || extent_budget > MAX_EXTENTS || input.len() > MAX_EXTENTS {
            return Err(Error::Geometry);
        }
        let mut out = Vec::<Run>::new(); let mut end = 0u64; let mut i = 0usize;
        while i < input.len()
            invariant i <= input.len() <= MAX_EXTENTS, out.len() <= extent_budget <= MAX_EXTENTS,
                filesystem_blocks > 0, wire_runs(out@, filesystem_blocks), end <= LOGICAL_END,
                ordered_intervals(input@.take(i as int), filesystem_blocks),
                i > 0 ==> end == logical_end(input@[i as int - 1]),
                out.len() > 0 ==> logical_end(out@[out.len() as int - 1]) == end,
                forall|logical: nat| logical < LOGICAL_END ==>
                    #[trigger] mapping_at(out@, logical) == mapping_at(input@.take(i as int), logical),
            decreases input.len() - i,
        {
            let run = input[i];
            if !interval_ok(run, filesystem_blocks) { return Err(Error::Range); }
            if (run.logical as u64) < end { return Err(Error::Order); }
            match emit(&mut out, run, filesystem_blocks, extent_budget) {
                Ok(()) => {}, Err(error) => { return Err(error); }
            }
            end = run.logical as u64 + run.length as u64; i += 1;
        }
        let physical = match physical_order(&out) { Ok(physical) => physical, Err(error) => { return Err(error); } };
        i = if physical.len() == 0 { 0 } else { 1 };
        while i < physical.len()
            invariant i <= physical.len() <= MAX_EXTENTS, physical.len() > 0 ==> i > 0,
                physically_sorted(physical@), same_multiset(out@, physical@), wire_runs(out@, filesystem_blocks),
                forall|j: int| 0 < j < i ==> physical_end(physical@[j - 1]) <= physical@[j].physical,
            decreases physical.len() - i,
        {
            let previous = physical[i - 1];
            if previous.physical + previous.length as u64 > physical[i].physical {
                return Err(Error::PhysicalAlias);
            }
            i += 1;
        }
        proof {
            sorted_neighbors_imply_physical_disjointness(physical@);
            physical_disjointness_transfers_by_multiset(out@, physical@, filesystem_blocks);
            assert(input@.take(input.len() as int) =~= input@);
            logical_map_equality_preserves_nonalias(input@, out@, filesystem_blocks);
            reveal(valid_set);
        }
        Ok(ExtentSet { runs: out, blocks: filesystem_blocks, budget: extent_budget })
    }

    pub fn run_count(&self) -> (r: usize) ensures self.wf(), r == self.view().runs.len(),
    { proof { use_type_invariant(self); } self.runs.len() }
    pub fn run_at(&self, index: usize) -> (r: Option<Run>)
        ensures self.wf(), match r {
            Some(run) => index < self.view().runs.len() && run == self.view().runs[index as int],
            None => index >= self.view().runs.len(),
        },
    {
        proof { use_type_invariant(self); }
        if index >= self.runs.len() { None } else { Some(self.runs[index]) }
    }
    pub fn filesystem_blocks(&self) -> (r: u64) ensures self.wf(), r == self.view().blocks,
    { proof { use_type_invariant(self); } self.blocks }

    pub fn lookup_mapping(&self, logical: u32) -> (r: Mapping)
        ensures self.wf(), r == mapping_at(self.view().runs, logical as nat),
    {
        proof { use_type_invariant(self); reveal(valid_set); }
        let mut low = 0usize; let mut high = self.runs.len();
        while low < high
            invariant self.wf(), wire_runs(self.runs@, self.blocks), low <= high <= self.runs.len(),
                forall|j: int| 0 <= j < low ==> logical_end(self.runs@[j]) <= logical,
                forall|j: int| high <= j < self.runs.len() ==> logical < self.runs@[j].logical,
            decreases high - low,
        {
            let mid = low + (high - low) / 2;
            let run = self.runs[mid];
            if logical < run.logical { high = mid; }
            else if logical as u64 >= run.logical as u64 + run.length as u64 { low = mid + 1; }
            else {
                let physical = run.physical + (logical - run.logical) as u64;
                proof { mapping_selected_entry(self.runs@, self.blocks, mid as int, logical as nat); }
                return if run.initialized { Mapping::Written(physical) } else { Mapping::Unwritten(physical) };
            }
        }
        proof {
            assert forall|i: int| 0 <= i < self.runs.len()
                implies !(self.runs@[i].logical <= logical < #[trigger] logical_end(self.runs@[i])) by {
                if i < low { assert(logical_end(self.runs@[i]) <= logical); }
                else { assert(logical < self.runs@[i].logical); }
            }
            mapping_absent(self.runs@, logical as nat);
        }
        Mapping::Hole
    }

    pub fn insert_hole(&self, run: Run) -> (r: Result<Self, Error>)
        ensures self.wf(), match r {
            Ok(next) => next.wf() && next.view().blocks == self.view().blocks
                && next.view().budget == self.view().budget && replace_map(self.view().runs, next.view().runs, run)
                    && (forall|logical: nat| run.logical <= logical < logical_end(run) ==> #[trigger] mapping_at(self.view().runs, logical) is Hole),
            Err(_) => true,
        },
    {
        proof { use_type_invariant(self); reveal(valid_set); }

        if !interval_ok(run, self.blocks) { return Err(Error::Range); }
        let end = run.logical as u64 + run.length as u64;
        let mut i = 0usize;
        while i < self.runs.len()
            invariant self.wf(), i <= self.runs.len(),
                forall|j: int| 0 <= j < i ==> !(self.runs@[j].logical < logical_end(run)
                    && run.logical < logical_end(self.runs@[j])),
            decreases self.runs.len() - i,
        {
            let old = self.runs[i];
            if (old.logical as u64) < end && (run.logical as u64) < old.logical as u64 + old.length as u64 {
                return Err(Error::LogicalOverlap);
            }
            i += 1;
        }
        self.replace_mapping(run)
    }

    pub fn replace_mapping(&self, run: Run) -> (r: Result<Self, Error>)
        ensures self.wf(), match r {
            Ok(next) => next.wf() && next.view().blocks == self.view().blocks
                && next.view().budget == self.view().budget && replace_map(self.view().runs, next.view().runs, run),
            Err(_) => true,
        },
    {
        proof { use_type_invariant(self); reveal(valid_set); }

        if !interval_ok(run, self.blocks) { return Err(Error::Range); }
        let end = run.logical as u64 + run.length as u64;
        let cleared = match cut(&self.runs, run.logical as u64, end, self.blocks, self.budget) {
            Ok(cleared) => cleared, Err(error) => { return Err(error); }
        };
        let mut next = Vec::<Run>::new(); let mut inserted = false; let mut i = 0usize;
        while i < cleared.len()
            invariant self.wf(), i <= cleared.len(), next.len() <= self.budget <= MAX_EXTENTS,
                wire_runs(cleared@, self.blocks), wire_runs(next@, self.blocks),
                remove_map(self.runs@, cleared@, run.logical as nat, logical_end(run)),
                inserted ==> (forall|logical: nat| run.logical <= logical < logical_end(run) ==>
                    #[trigger] mapping_at(next@, logical) == mapping_at(seq![run], logical)),
                next.len() > 0 && i < cleared.len() ==> logical_end(next@[next.len() as int - 1]) <= cleared@[i as int].logical,
            decreases cleared.len() - i,
        {
            if !inserted && run.logical < cleared[i].logical {
                match emit(&mut next, run, self.blocks, self.budget) {
                    Ok(()) => {}, Err(error) => { return Err(error); }
                }
                inserted = true;
            }
            match emit(&mut next, cleared[i], self.blocks, self.budget) {
                Ok(()) => {}, Err(error) => { return Err(error); }
            }
            i += 1;
        }
        if !inserted {
            match emit(&mut next, run, self.blocks, self.budget) {
                Ok(()) => {}, Err(error) => { return Err(error); }
            }
        }
        ExtentSet::from_sorted(&next, self.blocks, self.budget)
    }

    pub fn remove_range(&self, logical: u32, length: u32) -> (r: Result<Self, Error>)
        ensures self.wf(), match r {
            Ok(next) => next.wf() && next.view().blocks == self.view().blocks
                && next.view().budget == self.view().budget && remove_map(self.view().runs, next.view().runs, logical as nat, logical as nat + length as nat),
            Err(_) => true,
        },
    {
        proof { use_type_invariant(self); reveal(valid_set); }

        let end = logical as u64 + length as u64;
        if end > LOGICAL_END { return Err(Error::Range); }
        let next = match cut(&self.runs, logical as u64, end, self.blocks, self.budget) {
            Ok(next) => next, Err(error) => { return Err(error); }
        };
        ExtentSet::from_sorted(&next, self.blocks, self.budget)
    }

    pub fn truncate_blocks(&self, exclusive_end: u64) -> (r: Result<Self, Error>)
        ensures self.wf(), match r {
            Ok(next) => next.wf() && next.view().blocks == self.view().blocks
                && next.view().budget == self.view().budget && remove_map(self.view().runs, next.view().runs, exclusive_end as nat, LOGICAL_END as nat),
            Err(_) => true,
        },
    {
        proof { use_type_invariant(self); reveal(valid_set); }

        if exclusive_end > LOGICAL_END { return Err(Error::Range); }
        let next = match cut(&self.runs, exclusive_end, LOGICAL_END, self.blocks, self.budget) {
            Ok(next) => next, Err(error) => { return Err(error); }
        };
        ExtentSet::from_sorted(&next, self.blocks, self.budget)
    }

    pub fn convert_range(&self, logical: u32, length: u32, initialized: bool) -> (r: Result<Self, Error>)
        ensures self.wf(), match r {
            Ok(next) => next.wf() && next.view().blocks == self.view().blocks
                && next.view().budget == self.view().budget && convert_map(self.view().runs, next.view().runs, logical as nat, logical as nat + length as nat, initialized)
                    && (forall|block: nat| logical as nat <= block < logical as nat + length as nat ==> !(#[trigger] mapping_at(self.view().runs, block) is Hole)),
            Err(_) => true,
        },
    {
        proof { use_type_invariant(self); reveal(valid_set); }

        let end = logical as u64 + length as u64;
        if end > LOGICAL_END { return Err(Error::Range); }
        if length == 0 { return ExtentSet::from_sorted(&self.runs, self.blocks, self.budget); }
        let mut cursor = logical as u64; let mut out = Vec::<Run>::new(); let mut i = 0usize;
        while i < self.runs.len()
            invariant self.wf(), i <= self.runs.len(), out.len() <= self.budget <= MAX_EXTENTS,
                wire_runs(self.runs@, self.blocks), wire_runs(out@, self.blocks),
                (logical as u64) <= cursor <= end, end <= LOGICAL_END,
                convert_map(self.runs@.take(i as int), out@, logical as nat, end as nat, initialized),
                forall|block: nat| logical as nat <= block < cursor ==> !(#[trigger] mapping_at(self.runs@, block) is Hole),
                out.len() > 0 && i < self.runs.len() ==> logical_end(out@[out.len() as int - 1]) <= self.runs@[i as int].logical,
            decreases self.runs.len() - i,
        {
            let old = self.runs[i]; let old_end = old.logical as u64 + old.length as u64;
            if old_end <= logical as u64 || old.logical as u64 >= end {
                match emit(&mut out, old, self.blocks, self.budget) { Ok(()) => {}, Err(e) => { return Err(e); } }
            } else {
                let first = if old.logical < logical { logical as u64 } else { old.logical as u64 };
                let last = if old_end > end { end } else { old_end };
                if first > cursor { return Err(Error::Hole); }
                if old.logical < logical {
                    let prefix = Run { length: logical - old.logical, ..old };
                    match emit(&mut out, prefix, self.blocks, self.budget) { Ok(()) => {}, Err(e) => { return Err(e); } }
                }
                let changed = Run { logical: first as u32, length: (last - first) as u32,
                    physical: old.physical + first - old.logical as u64, initialized };
                match emit(&mut out, changed, self.blocks, self.budget) { Ok(()) => {}, Err(e) => { return Err(e); } }
                if old_end > end {
                    let suffix = Run { logical: end as u32, length: (old_end - end) as u32,
                        physical: old.physical + end - old.logical as u64, initialized: old.initialized };
                    match emit(&mut out, suffix, self.blocks, self.budget) { Ok(()) => {}, Err(e) => { return Err(e); } }
                }
                cursor = last;
            }
            i += 1;
        }
        if cursor != end { return Err(Error::Hole); }
        ExtentSet::from_sorted(&out, self.blocks, self.budget)
    }
}

fn cut(input: &[Run], first: u64, end: u64, blocks: u64, budget: usize) -> (r: Result<Vec<Run>, Error>)
    requires blocks > 0, budget <= MAX_EXTENTS, wire_runs(input@, blocks), input.len() <= budget,
    ensures match r {
        Ok(out) => first <= end <= LOGICAL_END && out.len() <= budget && wire_runs(out@, blocks)
            && remove_map(input@, out@, first as nat, end as nat),
        Err(_) => true,
    },
{    if first > end || end > LOGICAL_END { return Err(Error::Range); }
    let mut out = Vec::<Run>::new(); let mut i = 0usize;
    while i < input.len()
        invariant i <= input.len() <= budget <= MAX_EXTENTS, out.len() <= budget,
            wire_runs(input@, blocks), wire_runs(out@, blocks), first <= end <= LOGICAL_END,
            remove_map(input@.take(i as int), out@, first as nat, end as nat),
            out.len() > 0 && i < input.len() ==> logical_end(out@[out.len() as int - 1]) <= input@[i as int].logical,
        decreases input.len() - i,
    {
        let old = input[i]; let old_end = old.logical as u64 + old.length as u64;
        if old_end <= first || old.logical as u64 >= end || first == end {
            match emit(&mut out, old, blocks, budget) { Ok(()) => {}, Err(e) => { return Err(e); } }
        } else {
            if (old.logical as u64) < first {
                let left = Run { length: (first - old.logical as u64) as u32, ..old };
                match emit(&mut out, left, blocks, budget) { Ok(()) => {}, Err(e) => { return Err(e); } }
            }
            if old_end > end {
                let right = Run { logical: end as u32, length: (old_end - end) as u32,
                    physical: old.physical + end - old.logical as u64, initialized: old.initialized };
                match emit(&mut out, right, blocks, budget) { Ok(()) => {}, Err(e) => { return Err(e); } }
            }
        }
        i += 1;
    }
    Ok(out)
}

pub struct BuildOptions {
    pub block_bytes: u32, pub inode: u32, pub generation: u32, pub filesystem_seed: u32,
    pub metadata_checksum: bool, pub node_budget: usize, pub byte_budget: u64,
}
pub struct NodeImage { pub block: u64, pub raw: Vec<u8> }

pub struct OptionsView {
    pub block_bytes: u32, pub inode: u32, pub generation: u32, pub filesystem_seed: u32,
    pub checksum: bool, pub node_budget: nat, pub byte_budget: u64,
}
pub open spec fn options_view(options: BuildOptions) -> OptionsView {
    OptionsView { block_bytes: options.block_bytes, inode: options.inode, generation: options.generation,
        filesystem_seed: options.filesystem_seed, checksum: options.metadata_checksum,
        node_budget: options.node_budget as nat, byte_budget: options.byte_budget }
}
pub struct NodeImageView { pub block: u64, pub raw: Seq<u8> }
pub open spec fn node_views(nodes: Seq<NodeImage>) -> Seq<NodeImageView> {
    Seq::new(nodes.len(), |i: int| NodeImageView { block: nodes[i].block, raw: nodes[i].raw@ })
}
pub open spec fn data_total(runs: Seq<Run>) -> nat
    decreases runs.len(),
{ if runs.len() == 0 { 0nat } else { data_total(runs.drop_last()) + runs.last().length as nat } }
pub proof fn extent_lengths_fit_the_logical_address_space(runs: Seq<Run>, blocks: u64)
    requires ordered_intervals(runs, blocks),
    ensures data_total(runs) <= LOGICAL_END,
        runs.len() > 0 ==> data_total(runs) <= logical_end(runs.last()),
    decreases runs.len(),
{
    if runs.len() > 0 {
        extent_lengths_fit_the_logical_address_space(runs.drop_last(), blocks);
        if runs.len() > 1 {
            assert(logical_end(runs[runs.len() as int - 2]) <= runs.last().logical);
        }
    }
}

pub open spec fn block_kind(checksum: bool, seed: u32) -> extent_node::NodeKind {
    if checksum { extent_node::NodeKind::ChecksummedBlock(seed) } else { extent_node::NodeKind::LegacyBlock }
}
pub open spec fn pool_admitted(runs: Seq<Run>, blocks: u64, pool: Seq<u64>) -> bool {
    &&& pool.len() <= MAX_METADATA_NODES && pool.no_duplicates()
    &&& (forall|i: int| 0 <= i < pool.len() ==> 0 < #[trigger] pool[i] < blocks && pool[i] < PHYSICAL_LIMIT)
    &&& (forall|i: int, j: int| 0 <= i < pool.len() && 0 <= j < runs.len() ==>
        !(runs[j].physical <= #[trigger] pool[i] < #[trigger] physical_end(runs[j])))
}
pub open spec fn decoded_leaf(raw: Seq<u8>) -> Seq<Run> {
    Seq::new(bytes::le16(raw, 2), |i: int| {
        let at = 12 + 12 * i;
        let length = bytes::le16(raw, at + 4);
        Run { logical: bytes::le32(raw, at) as u32,
            length: if length <= 32768 { length as u32 } else { (length - 32768) as u32 },
            physical: (bytes::le32(raw, at + 8) + 4294967296 * bytes::le16(raw, at + 6)) as u64,
            initialized: length <= 32768 }
    })
}
#[verifier::opaque]
pub open spec fn emitted_leaf_projection(nodes: Seq<NodeImageView>) -> Seq<Run>
    decreases nodes.len(),
{
    if nodes.len() == 0 { Seq::empty() } else {
        emitted_leaf_projection(nodes.drop_last())
            + if bytes::le16(nodes.last().raw, 6) == 0 { decoded_leaf(nodes.last().raw) } else { Seq::empty() }
    }
}
pub open spec fn references(raw: Seq<u8>) -> Seq<u64> {
    if bytes::le16(raw, 6) == 0 { Seq::empty() }
    else { Seq::new(bytes::le16(raw, 2), |i: int| extent_node::child(raw, i) as u64) }
}
#[verifier::opaque]
pub open spec fn emitted_references(nodes: Seq<NodeImageView>) -> Seq<u64>
    decreases nodes.len(),
{
    if nodes.len() == 0 { Seq::empty() }
    else { emitted_references(nodes.drop_last()) + references(nodes.last().raw) }
}
pub open spec fn stored_node_raw(nodes: Seq<NodeImageView>, address: u64) -> Seq<u8> {
    if exists|i: int| 0 <= i < nodes.len() && nodes[i].block == address {
        nodes[choose|i: int| 0 <= i < nodes.len() && nodes[i].block == address].raw
    } else { Seq::empty() }
}
#[verifier::opaque]
pub open spec fn subtree_exclusive_end(raw: Seq<u8>, nodes: Seq<NodeImageView>, depth: nat) -> nat
    decreases depth,
{
    let count = bytes::le16(raw, 2);
    if count == 0 { 0nat }
    else if depth == 0 { logical_end(decoded_leaf(raw)[count as int - 1]) }
    else { subtree_exclusive_end(stored_node_raw(nodes, extent_node::child(raw, count as int - 1) as u64),
        nodes, (depth - 1) as nat) }
}
/// Every index record binds a real earlier-emitted child of the next smaller
/// depth. Address uniqueness and one incoming reference rule out aliases and
/// disconnected cycles. Full source/bitmap admission remains separate.
pub open spec fn child_links_bound(raw: Seq<u8>, children: Seq<NodeImageView>) -> bool {
    bytes::le16(raw, 6) > 0 ==> forall|i: int| 0 <= i < bytes::le16(raw, 2) ==>
        exists|j: int| 0 <= j < children.len()
            && #[trigger] children[j].block == extent_node::child(raw, i)
            && bytes::le16(children[j].raw, 6) + 1 == bytes::le16(raw, 6)
            && bytes::le16(children[j].raw, 2) > 0
            && extent_node::key(children[j].raw, 0) == extent_node::key(raw, i)
            && subtree_exclusive_end(children[j].raw, children, (bytes::le16(raw, 6) - 1) as nat)
                <= if i + 1 < bytes::le16(raw, 2) { extent_node::key(raw, i + 1) } else { LOGICAL_END as nat }
}
pub struct PlanView {
    pub root: Seq<u8>, pub nodes: Seq<NodeImageView>, pub unused: Seq<u64>, pub runs: Seq<Run>,
    pub depth: u16, pub inode_seed: u32, pub options: OptionsView, pub pool: Seq<u64>,
    pub blocks: u64, pub extent_budget: nat, pub data_blocks: u64, pub metadata_blocks: u64,
}
#[verifier::opaque]
pub open spec fn valid_plan(v: PlanView) -> bool {
    &&& valid_set(SetView { runs: v.runs, blocks: v.blocks, budget: v.extent_budget })
    &&& crate::block_size::accepted(v.options.block_bytes as nat) && v.options.inode > 0
    &&& v.options.node_budget <= MAX_METADATA_NODES
    &&& v.inode_seed == crc::fold(crc::fold(v.options.filesystem_seed,
        bytes::encoded_le(v.options.inode)), bytes::encoded_le(v.options.generation))
    &&& pool_admitted(v.runs, v.blocks, v.pool)
    &&& v.nodes.len() <= v.pool.len() && v.nodes.len() <= v.options.node_budget
    &&& v.nodes.len() * v.options.block_bytes as nat <= v.options.byte_budget
    &&& v.unused == v.pool.subrange(v.nodes.len() as int, v.pool.len() as int)
    &&& v.root.len() == 60 && v.depth <= 5 && bytes::le16(v.root, 6) == v.depth
    &&& bytes::le16(v.root, 4) == 4 && bytes::le32(v.root, 8) == 0
    &&& extent_node::valid(extent_node::NodeView { raw: v.root, blocks: v.blocks, kind: extent_node::NodeKind::Inline })
    &&& (forall|i: int| 0 <= i < v.nodes.len() ==> {
        let node = v.nodes[i];
        &&& node.block == v.pool[i] && node.raw.len() == v.options.block_bytes
        &&& extent_node::valid(extent_node::NodeView {
            raw: node.raw, blocks: v.blocks, kind: block_kind(v.options.checksum, v.inode_seed) })
        &&& bytes::le16(node.raw, 4) == (v.options.block_bytes as nat - 12) / 12
        &&& bytes::le16(node.raw, 2) > 0 && bytes::le16(node.raw, 6) < v.depth
        &&& bytes::le32(node.raw, 8) == 0
        &&& #[trigger] child_links_bound(node.raw, v.nodes.take(i))
    })
    &&& child_links_bound(v.root, v.nodes)
    &&& (forall|i: int| 0 <= i < v.nodes.len() ==>
        #[trigger] occurrences(references(v.root) + emitted_references(v.nodes), v.nodes[i].block) == 1)
    &&& if v.depth == 0 { v.nodes.len() == 0 && decoded_leaf(v.root) == v.runs }
        else { emitted_leaf_projection(v.nodes) == v.runs }
    &&& v.data_blocks as nat == data_total(v.runs) <= LOGICAL_END
    &&& v.metadata_blocks as nat == v.nodes.len()
}
pub proof fn plan_metadata_cannot_alias_its_final_data(v: PlanView, node: int, run: int)
    requires valid_plan(v), 0 <= node < v.nodes.len(), 0 <= run < v.runs.len(),
    ensures !(v.runs[run].physical <= v.nodes[node].block < physical_end(v.runs[run])),
{ reveal(valid_plan); }
pub proof fn every_external_extent_node_has_the_inode_checksum_context(v: PlanView, index: int)
    requires valid_plan(v), v.options.checksum, 0 <= index < v.nodes.len(),
    ensures {
        let raw = v.nodes[index].raw;
        let tail = 12 + bytes::le16(raw, 4) * 12;
        &&& tail + 4 <= raw.len()
        &&& bytes::le32(raw, tail as int) == crc::fold(v.inode_seed, raw.take(tail as int)) as nat
        &&& v.inode_seed == crc::fold(crc::fold(v.options.filesystem_seed,
            bytes::encoded_le(v.options.inode)), bytes::encoded_le(v.options.generation))
    },
{
    reveal(valid_plan); reveal(extent_node::valid);
}
pub proof fn every_staged_node_has_exactly_one_tree_reference(v: PlanView, index: int)
    requires valid_plan(v), 0 <= index < v.nodes.len(),
    ensures occurrences(references(v.root) + emitted_references(v.nodes), v.nodes[index].block) == 1,
{ reveal(valid_plan); }

pub struct EditPlan {
    root: [u8; 60], nodes: Vec<NodeImage>, unused: Vec<u64>, runs: Vec<Run>,
    depth: u16, inode: u32, generation: u32, inode_seed: u32, block_bytes: u32,
    data_blocks: u64, metadata_blocks: u64,
    options: Ghost<OptionsView>, pool: Ghost<Seq<u64>>, blocks: Ghost<u64>, extent_budget: Ghost<usize>,
}
impl EditPlan {
    pub closed spec fn view(&self) -> PlanView {
        PlanView { root: self.root@, nodes: node_views(self.nodes@), unused: self.unused@,
            runs: self.runs@, depth: self.depth, inode_seed: self.inode_seed,
            options: self.options@, pool: self.pool@, blocks: self.blocks@, extent_budget: self.extent_budget@ as nat,
            data_blocks: self.data_blocks, metadata_blocks: self.metadata_blocks }
    }
    pub open spec fn wf(&self) -> bool { valid_plan(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {
        self.wf() && self.inode == self.options@.inode && self.generation == self.options@.generation
            && self.block_bytes == self.options@.block_bytes
    }
    pub fn root_bytes(&self) -> (r: &[u8; 60]) ensures self.wf(), r@ == self.view().root,
    { proof { use_type_invariant(self); } &self.root }
    pub fn tree_depth(&self) -> (r: u16) ensures self.wf(), r == self.view().depth,
    { proof { use_type_invariant(self); } self.depth }
    pub fn node_count(&self) -> (r: usize) ensures self.wf(), r == self.view().nodes.len(),
    { proof { use_type_invariant(self); } self.nodes.len() }
    pub fn node_image(&self, index: usize) -> (r: Option<&NodeImage>)
        ensures self.wf(), match r {
            Some(node) => index < self.view().nodes.len() && node.block == self.view().nodes[index as int].block
                && node.raw@ == self.view().nodes[index as int].raw,
            None => index >= self.view().nodes.len(),
        },
    {
        proof { use_type_invariant(self); }
        if index >= self.nodes.len() { None } else { Some(&self.nodes[index]) }
    }
    pub fn unused_metadata_addresses(&self) -> (r: &[u64]) ensures self.wf(), r@ == self.view().unused,
    { proof { use_type_invariant(self); } &self.unused }
    pub fn final_runs(&self) -> (r: &[Run]) ensures self.wf(), r@ == self.view().runs,
    { proof { use_type_invariant(self); } &self.runs }
    pub fn source_inode_binding(&self) -> (r: (u32, u32, u32))
        ensures self.wf(), r == (self.view().options.inode, self.view().options.generation, self.view().inode_seed),
    { proof { use_type_invariant(self); } (self.inode, self.generation, self.inode_seed) }
    pub fn allocated_block_counts(&self) -> (r: (u64, u64))
        ensures self.wf(), r == (self.view().data_blocks, self.view().metadata_blocks),
    { proof { use_type_invariant(self); } (self.data_blocks, self.metadata_blocks) }
    pub fn normalized_sectors(&self) -> (r: u64)
        ensures self.wf(), r as nat == (self.view().data_blocks as nat + self.view().metadata_blocks as nat)
            * (self.view().options.block_bytes as nat / 512),
    {
        proof { use_type_invariant(self); reveal(valid_plan); }
        (self.data_blocks + self.metadata_blocks) * (self.block_bytes as u64 / 512)
    }
}

#[derive(Clone, Copy)]
struct Link { first: u32, address: u64, depth: u16 }

pub open spec fn encoded16(value: u16) -> Seq<u8> {
    seq![(value % 256) as u8, (value / 256) as u8]
}
proof fn local_writer_frames_reads(before: Seq<u8>, offset: int, data: Seq<u8>)
    requires 0 <= offset, offset + data.len() <= before.len(),
    ensures
        forall|i: int| 0 <= i < before.len() && !(offset <= i < offset + data.len()) ==>
            #[trigger] bytes::splice(before, offset, data)[i] == before[i],
        forall|word: int| 0 <= word && word + 2 <= before.len()
            && (word + 2 <= offset || word >= offset + data.len()) ==>
                #[trigger] bytes::le16(bytes::splice(before, offset, data), word) == bytes::le16(before, word),
        forall|word: int| 0 <= word && word + 4 <= before.len()
            && (word + 4 <= offset || word >= offset + data.len()) ==>
                #[trigger] bytes::le32(bytes::splice(before, offset, data), word) == bytes::le32(before, word),
{
    assert forall|i: int| 0 <= i < before.len() && !(offset <= i < offset + data.len())
        implies #[trigger] bytes::splice(before, offset, data)[i] == before[i] by {
        bytes::splice_frame(before, offset, data, i);
    }
}

fn put16(raw: &mut [u8], offset: usize, value: u16) -> (r: bool)
    ensures final(raw).len() == old(raw).len(), r == (offset as int + 2 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, offset as int, encoded16(value)) } else { old(raw)@ },
        r ==> bytes::le16(final(raw)@, offset as int) == value,
        forall|i: int| 0 <= i < old(raw).len() && !(offset <= i < offset as int + 2)
            ==> #[trigger] final(raw)@[i] == old(raw)@[i],
        forall|word: int| 0 <= word && word + 2 <= old(raw).len()
            && (word + 2 <= offset || word >= offset as int + 2) ==>
                #[trigger] bytes::le16(final(raw)@, word) == bytes::le16(old(raw)@, word),
        forall|word: int| 0 <= word && word + 4 <= old(raw).len()
            && (word + 4 <= offset || word >= offset as int + 2) ==>
                #[trigger] bytes::le32(final(raw)@, word) == bytes::le32(old(raw)@, word),
{
    let encoded = [(value % 256) as u8, (value / 256) as u8];
    proof { vstd::arithmetic::div_mod::lemma_fundamental_div_mod(value as int, 256); }
    let ghost before = raw@;
    let success = bytes::write_bytes(raw, offset, &encoded);
    proof { if success { local_writer_frames_reads(before, offset as int, encoded@); } }
    success
}
fn put32(raw: &mut [u8], offset: usize, value: u32) -> (r: bool)
    ensures final(raw).len() == old(raw).len(), r == (offset as int + 4 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, offset as int, bytes::encoded_le(value)) } else { old(raw)@ },
        r ==> bytes::le32(final(raw)@, offset as int) == value,
        forall|i: int| 0 <= i < old(raw).len() && !(offset <= i < offset as int + 4)
            ==> #[trigger] final(raw)@[i] == old(raw)@[i],
        forall|word: int| 0 <= word && word + 2 <= old(raw).len()
            && (word + 2 <= offset || word >= offset as int + 4) ==>
                #[trigger] bytes::le16(final(raw)@, word) == bytes::le16(old(raw)@, word),
        forall|word: int| 0 <= word && word + 4 <= old(raw).len()
            && (word + 4 <= offset || word >= offset as int + 4) ==>
                #[trigger] bytes::le32(final(raw)@, word) == bytes::le32(old(raw)@, word),
{
    let ghost before = raw@;
    let success = bytes::write_le32(raw, offset, value);
    proof { if success { local_writer_frames_reads(before, offset as int, bytes::encoded_le(value)); } }
    success
}
fn zeroes(length: usize) -> (r: Result<Vec<u8>, Error>)
    ensures match r {
        Ok(raw) => length <= 65536 && raw@ == Seq::new(length as nat, |i: int| 0u8),
        Err(_) => length > 65536,
    },
{
    if length > 65536 { return Err(Error::Geometry); }
    let mut raw = Vec::<u8>::new(); let mut i = 0usize;
    while i < length
        invariant i <= length <= 65536, raw.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] raw@[j] == 0,
        decreases length - i,
    { raw.push(0); i += 1; }
    assert(raw@ =~= Seq::new(length as nat, |i: int| 0u8));
    Ok(raw)
}

fn header(raw: &mut [u8], entries: usize, maximum: usize, depth: u16) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r == (entries <= maximum && 0 < maximum <= 5460 && depth <= 5 && old(raw).len() >= 12),
        r ==> bytes::le16(final(raw)@, 0) == 0xf30a && bytes::le16(final(raw)@, 2) == entries
            && bytes::le16(final(raw)@, 4) == maximum && bytes::le16(final(raw)@, 6) == depth
            && bytes::le32(final(raw)@, 8) == 0,
        !r ==> final(raw)@ == old(raw)@,
        forall|i: int| 12 <= i < old(raw).len() ==> #[trigger] final(raw)@[i] == old(raw)@[i],
{
    if entries > maximum || maximum == 0 || maximum > 5460 || depth > 5 || raw.len() < 12 { return false; }
    put16(raw, 0, 0xf30a); put16(raw, 2, entries as u16);
    put16(raw, 4, maximum as u16); put16(raw, 6, depth); put32(raw, 8, 0); true
}

fn stamp_node(raw: &mut [u8], maximum: usize, checksum: bool, seed: u32) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        !checksum ==> r && final(raw)@ == old(raw)@,
        checksum && r ==> maximum <= 5460 && 16 + maximum as nat * 12 <= old(raw).len()
            && bytes::le32(final(raw)@, 12 + maximum as int * 12)
                == crc::fold(seed, final(raw)@.take(12 + maximum as int * 12)) as nat,
        !r ==> final(raw)@ == old(raw)@,
        checksum ==> (forall|i: int| 0 <= i < old(raw).len()
            && !(12 + maximum as int * 12 <= i < 16 + maximum as int * 12) ==>
                #[trigger] final(raw)@[i] == old(raw)@[i]),
{
    if !checksum { return true; }
    if maximum > 5460 { return false; }
    let tail = 12 + maximum * 12;
    if tail > raw.len() || raw.len() - tail < 4 { return false; }
    let value = crc::crc32c(seed, &raw[..tail]); put32(raw, tail, value)
}

fn encode_run(raw: &mut [u8], at: usize, run: Run, blocks: u64) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r ==> at as nat + 12 <= old(raw).len() && interval_valid(run, blocks)
            && run.length <= maximum_length(run)
            && crate::extent_span::accepted(final(raw)@, at as int, blocks)
            && crate::extent_span::represents(crate::extent_span::SpanView {
                logical: run.logical, length: run.length, physical: run.physical, initialized: run.initialized, blocks },
                final(raw)@, at as int),
        !r ==> final(raw)@ == old(raw)@,
        forall|i: int| 0 <= i < old(raw).len() && !(at <= i < at as int + 12)
            ==> #[trigger] final(raw)@[i] == old(raw)@[i],
{
    let state = if run.initialized { ExtentState::Written } else { ExtentState::Unwritten };
    let span = match ExtentSpan::new(run.logical, run.length, run.physical, state, blocks) {
        Some(span) => span, None => { return false; }
    };
    let encoded = match span.encode() { Some(encoded) => encoded, None => { return false; } };
    bytes::write_bytes(raw, at, &encoded)
}

fn encode_link(raw: &mut [u8], at: usize, link: Link, depth: u16) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r ==> 1 <= depth <= 5 && link.depth as nat + 1 == depth && 0 < link.address < PHYSICAL_LIMIT
            && at as nat + 12 <= old(raw).len() && bytes::le32(final(raw)@, at as int) == link.first
            && bytes::le32(final(raw)@, at as int + 4) + 4294967296 * bytes::le16(final(raw)@, at as int + 8) == link.address
            && bytes::le16(final(raw)@, at as int + 10) == 0,
        !r ==> final(raw)@ == old(raw)@,
        forall|i: int| 0 <= i < old(raw).len() && !(at <= i < at as int + 12)
            ==> #[trigger] final(raw)@[i] == old(raw)@[i],
{
    if depth == 0 || depth > 5 || link.depth > 4 || link.depth + 1 != depth
        || link.address == 0 || link.address >= PHYSICAL_LIMIT
        || at > raw.len() || raw.len() - at < 12 { return false; }
    put32(raw, at, link.first); put32(raw, at + 4, link.address as u32);
    put16(raw, at + 8, (link.address >> 32) as u16); put16(raw, at + 10, 0); true
}

fn validate_pool(set: &ExtentSet, pool: &[u64], node_budget: usize) -> (r: Result<(), Error>)
    ensures set.wf(), match r {
        Ok(()) => node_budget <= MAX_METADATA_NODES && pool_admitted(set.view().runs, set.view().blocks, pool@),
        Err(_) => true,
    },
{
    proof { use_type_invariant(set); reveal(valid_set); }
    if node_budget > MAX_METADATA_NODES || pool.len() > MAX_METADATA_NODES { return Err(Error::Budget); }
    let addresses = match address_order(pool) { Ok(addresses) => addresses, Err(e) => { return Err(e); } };
    let data = match physical_order(&set.runs) { Ok(data) => data, Err(e) => { return Err(e); } };
    let mut i = 0usize; let mut d = 0usize;
    while i < addresses.len()
        invariant i <= addresses.len(), d <= data.len(), addresses.len() <= MAX_METADATA_NODES,
        decreases addresses.len() - i,
    {
        let address = addresses[i];
        if address == 0 || address >= set.blocks { return Err(Error::MetadataPool); }
        if address >= PHYSICAL_LIMIT { return Err(Error::AddressTooWide); }
        if i > 0 && addresses[i - 1] == address { return Err(Error::MetadataAlias); }
        while d < data.len() && data[d].physical + (data[d].length as u64) <= address
            invariant d <= data.len(),
            decreases data.len() - d,
        { d += 1; }
        if d < data.len() && data[d].physical <= address { return Err(Error::MetadataAlias); }
        i += 1;
    }
    Ok(())
}

fn emit_node(nodes: &mut Vec<NodeImage>, pool: &[u64], raw: Vec<u8>, first: u32,
    depth: u16, options: &BuildOptions, blocks: u64, seed: u32) -> (r: Result<Link, Error>)
    requires old(nodes).len() <= options.node_budget <= MAX_METADATA_NODES,
        crate::block_size::accepted(options.block_bytes as nat),
    ensures match r {
        Ok(link) => final(nodes).len() == old(nodes).len() + 1
            && node_views(final(nodes)@).take(old(nodes).len() as int) == node_views(old(nodes)@)
            && link.first == first && link.depth == depth && link.address == pool[old(nodes).len() as int]
            && final(nodes)@[old(nodes).len() as int].block == link.address
            && final(nodes)@[old(nodes).len() as int].raw@ == raw@
            && extent_node::valid(extent_node::NodeView { raw: raw@, blocks, kind: block_kind(options.metadata_checksum, seed) })
            && final(nodes).len() <= options.node_budget
            && final(nodes).len() as nat * options.block_bytes as nat <= options.byte_budget,
        Err(_) => node_views(final(nodes)@) == node_views(old(nodes)@),
    },
{
    if nodes.len() >= pool.len() || nodes.len() >= options.node_budget { return Err(Error::Budget); }
    let used = nodes.len() as u64 * options.block_bytes as u64;
    if used > options.byte_budget || options.block_bytes as u64 > options.byte_budget - used {
        return Err(Error::Budget);
    }
    if raw.len() != options.block_bytes as usize { return Err(Error::Encoding); }
    let checked = {
        let checksum = if options.metadata_checksum { BlockChecksum::Crc32c(seed) } else { BlockChecksum::Legacy };
        extent_node::parse_block(&raw, blocks, checksum).is_some()
    };
    if !checked { return Err(Error::Encoding); }
    let address = pool[nodes.len()];
    nodes.push(NodeImage { block: address, raw });
    Ok(Link { first, address, depth })
}

pub fn build_tree(set: &ExtentSet, metadata_pool: &[u64], options: BuildOptions) -> (r: Result<EditPlan, Error>)
    ensures set.wf(), match r {
        Ok(plan) => plan.wf() && plan.view().runs == set.view().runs
            && plan.view().blocks == set.view().blocks && plan.view().pool == metadata_pool@
            && plan.view().options == options_view(options),
        Err(_) => true,
    },
{
    build_tree_with_depth(set, metadata_pool, options, 0)
}

/// A requested greater depth can preserve a caller's staged tree shape. With
/// zero, the result uses the minimal depth. No empty internal node is emitted.
pub fn build_tree_with_depth(set: &ExtentSet, metadata_pool: &[u64],
    options: BuildOptions, minimum_depth: u16) -> (r: Result<EditPlan, Error>)
    ensures set.wf(), match r {
        Ok(plan) => plan.wf() && plan.view().runs == set.view().runs
            && plan.view().blocks == set.view().blocks && plan.view().pool == metadata_pool@
            && plan.view().options == options_view(options) && minimum_depth <= plan.view().depth,
        Err(_) => true,
    },
{
    proof { use_type_invariant(set); reveal(valid_set); }
    if !crate::block_size::valid(options.block_bytes as usize) || options.inode == 0
        || minimum_depth > 5 || options.node_budget > MAX_METADATA_NODES { return Err(Error::Geometry); }
    if set.runs.len() == 0 && minimum_depth != 0 { return Err(Error::Depth); }
    match validate_pool(set, metadata_pool, options.node_budget) { Ok(()) => {}, Err(e) => { return Err(e); } }
    let seed = crate::inode::inode_seed(options.filesystem_seed, options.inode, options.generation);
    let maximum = (options.block_bytes as usize - 12) / 12;
    let mut root = [0u8; 60];
    let mut nodes = Vec::<NodeImage>::new();
    let depth;
    if set.runs.len() <= 4 && minimum_depth == 0 {
        if !header(&mut root, set.runs.len(), 4, 0) { return Err(Error::Encoding); }
        let mut i = 0usize;
        while i < set.runs.len()
            invariant i <= set.runs.len() <= 4,
            decreases set.runs.len() - i,
        {
            if !encode_run(&mut root, 12 + i * 12, set.runs[i], set.blocks) { return Err(Error::Encoding); }
            i += 1;
        }
        depth = 0u16;
    } else {
        let mut links = Vec::<Link>::new(); let mut start = 0usize;
        while start < set.runs.len()
            invariant start <= set.runs.len() <= MAX_EXTENTS, maximum > 0,
                nodes.len() <= options.node_budget <= MAX_METADATA_NODES,
            decreases set.runs.len() - start,
        {
            let end = if maximum > set.runs.len() - start { set.runs.len() } else { start + maximum };
            let mut raw = match zeroes(options.block_bytes as usize) { Ok(raw) => raw, Err(e) => { return Err(e); } };
            if !header(&mut raw, end - start, maximum, 0) { return Err(Error::Encoding); }
            let mut i = start;
            while i < end
                invariant start <= i <= end <= set.runs.len(), end - start <= maximum,
                decreases end - i,
            {
                if !encode_run(&mut raw, 12 + (i - start) * 12, set.runs[i], set.blocks) {
                    return Err(Error::Encoding);
                }
                i += 1;
            }
            if !stamp_node(&mut raw, maximum, options.metadata_checksum, seed) { return Err(Error::Encoding); }
            let link = match emit_node(&mut nodes, metadata_pool, raw, set.runs[start].logical,
                0, &options, set.blocks, seed) { Ok(link) => link, Err(e) => { return Err(e); } };
            links.push(link); start = end;
        }
        let mut level = 0u16;
        while links.len() > 4 || level + 1 < minimum_depth
            invariant level <= 4, links.len() > 0, maximum > 1,
                nodes.len() <= options.node_budget <= MAX_METADATA_NODES,
            decreases 5 - level,
        {
            if level >= 4 { return Err(Error::Depth); }
            let mut next = Vec::<Link>::new(); start = 0;
            while start < links.len()
                invariant start <= links.len(), maximum > 1, level < 4,
                    nodes.len() <= options.node_budget <= MAX_METADATA_NODES,
                decreases links.len() - start,
            {
                let end = if maximum > links.len() - start { links.len() } else { start + maximum };
                let mut raw = match zeroes(options.block_bytes as usize) { Ok(raw) => raw, Err(e) => { return Err(e); } };
                if !header(&mut raw, end - start, maximum, level + 1) { return Err(Error::Encoding); }
                let mut i = start;
                while i < end
                    invariant start <= i <= end <= links.len(), end - start <= maximum, level < 4,
                    decreases end - i,
                {
                    if !encode_link(&mut raw, 12 + (i - start) * 12, links[i], level + 1) {
                        return Err(Error::Encoding);
                    }
                    i += 1;
                }
                if !stamp_node(&mut raw, maximum, options.metadata_checksum, seed) { return Err(Error::Encoding); }
                let link = match emit_node(&mut nodes, metadata_pool, raw, links[start].first,
                    level + 1, &options, set.blocks, seed) { Ok(link) => link, Err(e) => { return Err(e); } };
                next.push(link); start = end;
            }
            links = next; level += 1;
        }
        depth = level + 1;
        if !header(&mut root, links.len(), 4, depth) { return Err(Error::Encoding); }
        let mut i = 0usize;
        while i < links.len()
            invariant i <= links.len() <= 4, 1 <= depth <= 5,
            decreases links.len() - i,
        {
            if !encode_link(&mut root, 12 + i * 12, links[i], depth) { return Err(Error::Encoding); }
            i += 1;
        }
    }
    if extent_node::parse_inline_root(&root, set.blocks).is_none() { return Err(Error::Encoding); }
    let mut unused = Vec::<u64>::new(); let mut i = nodes.len();
    while i < metadata_pool.len()
        invariant nodes.len() <= i <= metadata_pool.len() <= MAX_METADATA_NODES,
            unused@ == metadata_pool@.subrange(nodes.len() as int, i as int),
        decreases metadata_pool.len() - i,
    { unused.push(metadata_pool[i]); i += 1; }
    let mut runs = Vec::<Run>::new(); let mut data_blocks = 0u64; i = 0;
    while i < set.runs.len()
        invariant i <= set.runs.len() <= MAX_EXTENTS, runs.len() == i, runs@ == set.runs@.take(i as int),
            data_blocks as nat == data_total(runs@) <= LOGICAL_END,
        decreases set.runs.len() - i,
    {
        if data_blocks > LOGICAL_END - set.runs[i].length as u64 { return Err(Error::Range); }
        data_blocks += set.runs[i].length as u64; runs.push(set.runs[i]); i += 1;
    }
    let metadata_blocks = nodes.len() as u64;
    Ok(EditPlan { root, nodes, unused, runs, depth, inode: options.inode,
        generation: options.generation, inode_seed: seed, block_bytes: options.block_bytes,
        data_blocks, metadata_blocks, options: Ghost(options_view(options)),
        pool: Ghost(metadata_pool@), blocks: Ghost(set.blocks), extent_budget: Ghost(set.budget) })
}

}
