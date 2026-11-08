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
    &&& forall|i: int, j: int| #![trigger runs[i], runs[j]] 0 <= i < j < runs.len() ==> logical_end(runs[i]) <= runs[j].logical
}
pub open spec fn wire_runs(runs: Seq<Run>, blocks: u64) -> bool {
    &&& ordered_intervals(runs, blocks)
    &&& forall|i: int| 0 <= i < runs.len() ==> runs[i].length <= #[trigger] maximum_length(runs[i])
    &&& forall|i: int| #![trigger runs[i]] 0 < i < runs.len() ==>
        (runs[i - 1].initialized == runs[i].initialized
         && logical_end(runs[i - 1]) == runs[i].logical
         && physical_end(runs[i - 1]) == runs[i].physical)
        ==> runs[i - 1].length == maximum_length(runs[i - 1])
}
pub open spec fn no_physical_alias(runs: Seq<Run>) -> bool {
    forall|i: int, j: int| #![trigger runs[i], runs[j]] 0 <= i < j < runs.len() ==>
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
    forall|i: int, j: int| #![trigger runs[i], runs[j]] 0 <= i < j < runs.len() ==> runs[i].physical <= runs[j].physical
}
pub open spec fn addresses_sorted(addresses: Seq<u64>) -> bool {
    forall|i: int, j: int| #![trigger addresses[i], addresses[j]] 0 <= i < j < addresses.len() ==> addresses[i] <= addresses[j]
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
                && runs.drop_first()[i].logical <= logical < #[trigger] logical_end(runs.drop_first()[i])
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
        forall|i: int| #![trigger runs[i]] 0 < i < runs.len() ==> physical_end(runs[i - 1]) <= runs[i].physical,
    ensures no_physical_alias(runs),
{
    assert forall|i: int, j: int| #![trigger runs[i], runs[j]] 0 <= i < j < runs.len()
        implies physical_end(runs[i]) <= runs[j].physical || physical_end(runs[j]) <= runs[i].physical by {
        assert(physical_end(runs[i]) <= runs[i + 1].physical);
        if i + 1 < j { assert(runs[i + 1].physical <= runs[j].physical); }
    }
}
proof fn physical_disjointness_transfers_by_multiset(before: Seq<Run>, after: Seq<Run>, blocks: u64)
    requires ordered_intervals(before, blocks), same_multiset(before, after), no_physical_alias(after),
    ensures no_physical_alias(before),
{
    assert forall|i: int, j: int| #![trigger before[i], before[j]] 0 <= i < j < before.len()
        implies physical_end(before[i]) <= before[j].physical || physical_end(before[j]) <= before[i].physical by {
        assert(interval_valid(before[i], blocks));
        assert(interval_valid(before[j], blocks));
        assert(before[i].length > 0);
        assert(before[i].logical < logical_end(before[i]) <= before[j].logical);
        assert(before[i].logical < before[j].logical);
        occurrences_are_membership(before, before[i]);
        occurrences_are_membership(before, before[j]);
        occurrences_are_membership(after, before[i]);
        occurrences_are_membership(after, before[j]);
        assert(after.contains(before[i]) && after.contains(before[j]));
        let a = choose|a: int| 0 <= a < after.len() && #[trigger] after[a] == before[i];
        let b = choose|b: int| 0 <= b < after.len() && #[trigger] after[b] == before[j];
        assert(a != b);
        if a < b { assert(physical_end(after[a]) <= after[b].physical || physical_end(after[b]) <= after[a].physical); }
        else { assert(physical_end(after[b]) <= after[a].physical || physical_end(after[a]) <= after[b].physical); }
    }
}

pub open spec fn mapped_physical(mapping: Mapping) -> Option<u64> {
    match mapping { Mapping::Written(physical) | Mapping::Unwritten(physical) => Some(physical), Mapping::Hole => None }
}
/// A selected valid singleton has an untruncated physical coordinate. Keeping
/// this arithmetic fact separate avoids reasoning about casts through the
/// recursive mapping definition at each use.
proof fn singleton_mapping_physical_coordinate(run: Run, blocks: u64, logical: nat)
    requires interval_valid(run, blocks), run.logical <= logical < logical_end(run),
    ensures mapped_physical(mapping_at(seq![run], logical))
            == Some((run.physical as nat + logical - run.logical as nat) as u64),
        ((run.physical as nat + logical - run.logical as nat) as u64) as nat
            == run.physical as nat + logical - run.logical as nat,
        run.physical <= ((run.physical as nat + logical - run.logical as nat) as u64)
            < physical_end(run),
{
    let coordinate = (run.physical as nat + logical - run.logical as nat) as nat;
    assert(logical >= run.logical);
    assert(logical - (run.logical as nat) < run.length as nat);
    assert(run.physical <= coordinate < physical_end(run));
    assert(coordinate < blocks as nat + 1);
    assert(coordinate <= 18446744073709551615);
    assert((coordinate as u64) as nat == coordinate);
    reveal(mapping_at);
    assert(seq![run].len() == 1 && seq![run][0] == run);
}

proof fn disjoint_runs_map_storage_injectively(runs: Seq<Run>, blocks: u64,
    first: nat, second: nat, physical: u64)
    requires ordered_intervals(runs, blocks), no_physical_alias(runs),
        mapped_physical(mapping_at(runs, first)) == Some(physical),
        mapped_physical(mapping_at(runs, second)) == Some(physical),
    ensures first == second,
{
    assert(!(mapping_at(runs, first) is Hole));
    assert(!(mapping_at(runs, second) is Hole));
    mapping_has_a_covering_entry(runs, first);
    mapping_has_a_covering_entry(runs, second);
    let a = choose|a: int| 0 <= a < runs.len() && runs[a].logical <= first < #[trigger] logical_end(runs[a])
        && mapping_at(runs, first) == mapping_at(seq![runs[a]], first);
    let b = choose|b: int| 0 <= b < runs.len() && runs[b].logical <= second < #[trigger] logical_end(runs[b])
        && mapping_at(runs, second) == mapping_at(seq![runs[b]], second);
    assert(interval_valid(runs[a], blocks));
    assert(interval_valid(runs[b], blocks));
    singleton_mapping_physical_coordinate(runs[a], blocks, first);
    singleton_mapping_physical_coordinate(runs[b], blocks, second);
    assert(physical as nat == runs[a].physical as nat + first - runs[a].logical as nat);
    assert(physical as nat == runs[b].physical as nat + second - runs[b].logical as nat);
    assert(runs[a].physical <= physical < physical_end(runs[a]));
    assert(runs[b].physical <= physical < physical_end(runs[b]));
    if a < b {
        assert(physical_end(runs[a]) <= runs[b].physical || physical_end(runs[b]) <= runs[a].physical);
        assert(false);
    } else if b < a {
        assert(physical_end(runs[b]) <= runs[a].physical || physical_end(runs[a]) <= runs[b].physical);
        assert(false);
    }
    assert(a == b);
    assert(first == second);
}
proof fn logical_map_equality_preserves_nonalias(before: Seq<Run>, after: Seq<Run>, blocks: u64)
    requires ordered_intervals(before, blocks), ordered_intervals(after, blocks), no_physical_alias(after),
        forall|logical: nat| logical < LOGICAL_END ==> #[trigger] mapping_at(before, logical) == mapping_at(after, logical),
    ensures no_physical_alias(before),
{
    assert forall|i: int, j: int| #![trigger before[i], before[j]] 0 <= i < j < before.len()
        implies physical_end(before[i]) <= before[j].physical || physical_end(before[j]) <= before[i].physical by {
        if physical_end(before[i]) > before[j].physical && physical_end(before[j]) > before[i].physical {
            assert(interval_valid(before[i], blocks));
            assert(interval_valid(before[j], blocks));
            let physical = if before[i].physical > before[j].physical { before[i].physical } else { before[j].physical };
            assert(before[i].physical <= physical < physical_end(before[i]));
            assert(before[j].physical <= physical < physical_end(before[j]));
            let first = (before[i].logical as nat + physical as nat - before[i].physical as nat) as nat;
            let second = (before[j].logical as nat + physical as nat - before[j].physical as nat) as nat;
            assert(first == before[i].logical as nat + (physical as nat - before[i].physical as nat));
            assert(second == before[j].logical as nat + (physical as nat - before[j].physical as nat));
            assert(before[i].logical <= first < logical_end(before[i]));
            assert(before[j].logical <= second < logical_end(before[j]));
            assert(first < LOGICAL_END && second < LOGICAL_END);
            mapping_selected_entry(before, blocks, i, first);
            mapping_selected_entry(before, blocks, j, second);
            singleton_mapping_physical_coordinate(before[i], blocks, first);
            singleton_mapping_physical_coordinate(before[j], blocks, second);
            assert(before[i].physical as nat + first - before[i].logical as nat == physical as nat);
            assert(before[j].physical as nat + second - before[j].logical as nat == physical as nat);
            assert(mapped_physical(mapping_at(before, first)) == Some(physical));
            assert(mapped_physical(mapping_at(before, second)) == Some(physical));
            assert(mapping_at(after, first) == mapping_at(before, first));
            assert(mapping_at(after, second) == mapping_at(before, second));
            disjoint_runs_map_storage_injectively(after, blocks, first, second, physical);
            assert(first < logical_end(before[i]) <= before[j].logical <= second);
            assert(false);
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

// Proof proposals only. Insert inside extent_edit.rs's existing verus! body.
// No verifier has been run on these proposals.
proof fn fragment_occurrences_push<T>(s: Seq<T>, x: T, value: T)
    ensures occurrences(s.push(x), value)
        == occurrences(s, value) + if x == value { 1nat } else { 0nat },
{
    assert(s.push(x).drop_last() =~= s);
    assert(s.push(x).last() == x);
}
proof fn fragment_multiset_transitive<T>(a: Seq<T>, b: Seq<T>, c: Seq<T>)
    requires same_multiset(a, b), same_multiset(b, c),
    ensures same_multiset(a, c),
{
    assert forall|value: T| #[trigger] occurrences(a, value) == occurrences(c, value) by {
        assert(occurrences(a, value) == occurrences(b, value));
        assert(occurrences(b, value) == occurrences(c, value));
    }
}
proof fn fragment_same_aligned_block(base: int, width: int, index: int)
    requires 0 < width, 0 <= base, base % width == 0, base <= index < base + width,
    ensures index / width == base / width,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(base, width);
    assert(index == (base / width) * width + (index - base)) by (nonlinear_arith)
        requires base == width * (base / width) + base % width, base % width == 0;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        index, width, base / width, index - base);
}
proof fn fragment_before_aligned_block(base: int, width: int, index: int)
    requires 0 < width, 0 <= index < base, base % width == 0,
    ensures index / width != base / width,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(base, width);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(index, width);
    vstd::arithmetic::div_mod::lemma_mod_bound(index, width);
    if index / width == base / width {
        assert(index >= base) by (nonlinear_arith)
            requires base == width * (base / width) + base % width, base % width == 0,
                index == width * (index / width) + index % width, index % width >= 0,
                index / width == base / width;
    }
}
proof fn fragment_merge_geometry(left: int, width: int, n: int, middle: int, end: int)
    requires 0 < width, 0 <= left < n, left % (2 * width) == 0,
        middle == (if n < left + width { n } else { left + width }),
        end == (if n < middle + width { n } else { middle + width }),
    ensures left < middle <= end <= n, middle <= left + width, end <= left + 2 * width,
        left % width == 0,
        middle < n ==> middle == left + width && middle % width == 0,
        end < n ==> end == left + 2 * width && end % (2 * width) == 0,
{
    let q = left / (2 * width);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(left, 2 * width);
    assert(left == (2 * q) * width) by (nonlinear_arith)
        requires left == (2 * width) * q + left % (2 * width), left % (2 * width) == 0;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(left, width, 2 * q, 0);
    if middle < n {
        assert(middle == left + width);
        assert(middle == (2 * q + 1) * width) by (nonlinear_arith)
            requires left == (2 * q) * width, middle == left + width;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(middle, width, 2 * q + 1, 0);
    }
    if end < n {
        assert(middle == left + width && end == middle + width);
        assert(end == (q + 1) * (2 * width)) by (nonlinear_arith)
            requires left == (2 * q) * width, middle == left + width, end == middle + width;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(end, 2 * width, q + 1, 0);
    }
}
proof fn fragment_double_exceeds(n: int, width: int)
    requires 0 < width, width > n / 2,
    ensures n < 2 * width,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n, 2);
    vstd::arithmetic::div_mod::lemma_mod_bound(n, 2);
}

proof fn fragment_sorted_push_runs(s: Seq<Run>, x: Run)
    requires physically_sorted(s), s.len() > 0 ==> s.last().physical <= x.physical,
    ensures physically_sorted(s.push(x)),
{
    assert forall|i: int, j: int| #![trigger s.push(x)[i], s.push(x)[j]] 0 <= i < j < s.push(x).len()
        implies s.push(x)[i].physical <= s.push(x)[j].physical by {
        if j < s.len() {
            assert(s[i].physical <= s[j].physical);
        } else {
            assert(j == s.len());
            if i < s.len() - 1 { assert(s[i].physical <= s.last().physical); }
            else { assert(i == s.len() - 1); }
        }
    }
}
proof fn fragment_finish_chunk_runs(prefix: Seq<Run>, next: Seq<Run>, width: int)
    requires 0 < width, prefix.len() <= next.len() <= prefix.len() + 2 * width,
        (prefix.len() as int) % (2 * width) == 0,
        next.take(prefix.len() as int) == prefix,
        forall|i: int, j: int| #![trigger prefix[i], prefix[j]] 0 <= i < j < prefix.len()
            && i / (2 * width) == j / (2 * width) ==>
            prefix[i].physical <= prefix[j].physical,
        physically_sorted(next.subrange(prefix.len() as int, next.len() as int)),
    ensures forall|i: int, j: int| #![trigger next[i], next[j]] 0 <= i < j < next.len()
        && i / (2 * width) == j / (2 * width) ==>
        next[i].physical <= next[j].physical,
{
    assert forall|i: int, j: int| #![trigger next[i], next[j]] 0 <= i < j < next.len()
        && i / (2 * width) == j / (2 * width)
        implies next[i].physical <= next[j].physical by {
        if j < prefix.len() {
            assert(prefix[i].physical <= prefix[j].physical);
        } else if i < prefix.len() {
            fragment_before_aligned_block(prefix.len() as int, 2 * width, i);
            fragment_same_aligned_block(prefix.len() as int, 2 * width, j);
            assert(false);
        } else {
            assert(next.subrange(prefix.len() as int, next.len() as int)[i - prefix.len() as int].physical
                <= next.subrange(prefix.len() as int, next.len() as int)[j - prefix.len() as int].physical);
        }
    }
}

proof fn fragment_sorted_push_addresses(s: Seq<u64>, x: u64)
    requires addresses_sorted(s), s.len() > 0 ==> s.last() <= x,
    ensures addresses_sorted(s.push(x)),
{
    assert forall|i: int, j: int| #![trigger s.push(x)[i], s.push(x)[j]] 0 <= i < j < s.push(x).len()
        implies s.push(x)[i] <= s.push(x)[j] by {
        if j < s.len() {
            assert(s[i] <= s[j]);
        } else {
            assert(j == s.len());
            if i < s.len() - 1 { assert(s[i] <= s.last()); }
            else { assert(i == s.len() - 1); }
        }
    }
}
proof fn fragment_finish_chunk_addresses(prefix: Seq<u64>, next: Seq<u64>, width: int)
    requires 0 < width, prefix.len() <= next.len() <= prefix.len() + 2 * width,
        (prefix.len() as int) % (2 * width) == 0,
        next.take(prefix.len() as int) == prefix,
        forall|i: int, j: int| #![trigger prefix[i], prefix[j]] 0 <= i < j < prefix.len()
            && i / (2 * width) == j / (2 * width) ==>
            prefix[i] <= prefix[j],
        addresses_sorted(next.subrange(prefix.len() as int, next.len() as int)),
    ensures forall|i: int, j: int| #![trigger next[i], next[j]] 0 <= i < j < next.len()
        && i / (2 * width) == j / (2 * width) ==>
        next[i] <= next[j],
{
    assert forall|i: int, j: int| #![trigger next[i], next[j]] 0 <= i < j < next.len()
        && i / (2 * width) == j / (2 * width)
        implies next[i] <= next[j] by {
        if j < prefix.len() {
            assert(prefix[i] <= prefix[j]);
        } else if i < prefix.len() {
            fragment_before_aligned_block(prefix.len() as int, 2 * width, i);
            fragment_same_aligned_block(prefix.len() as int, 2 * width, j);
            assert(false);
        } else {
            assert(next.subrange(prefix.len() as int, next.len() as int)[i - prefix.len() as int]
                <= next.subrange(prefix.len() as int, next.len() as int)[j - prefix.len() as int]);
        }
    }
}

// Private proof helpers for emit/from_sorted. These are proposals, not checked.
// Insert inside the existing verus! block.
spec fn fragment_prefix(input: Run, used: u32) -> Run {
    Run { logical: input.logical, length: used, physical: input.physical,
        initialized: input.initialized }
}

spec fn fragment_piece(input: Run, used: u32, take: u32) -> Run {
    Run { logical: (input.logical as nat + used as nat) as u32, length: take,
        physical: (input.physical as nat + used as nat) as u64,
        initialized: input.initialized }
}

proof fn fragment_scalar_interval_bounds(run: Run, blocks: u64)
    requires interval_valid(run, blocks),
    ensures run.logical as nat + (run.length as nat) <= u64::MAX,
        run.physical as nat + (run.length as nat) <= u64::MAX,
{
    assert(run.length <= u32::MAX);
    assert(run.physical < 281474976710656);
    assert(run.physical as nat + (run.length as nat) <= 281479271677950);
    assert(281479271677950nat < u64::MAX);
}

proof fn fragment_piece_bounds(input: Run, used: u32, take: u32, blocks: u64)
    requires interval_valid(input, blocks), used < input.length,
        0 < take, used as nat + (take as nat) <= input.length,
        input.physical as nat + (used as nat) < PHYSICAL_LIMIT,
    ensures interval_valid(fragment_piece(input, used, take), blocks),
        fragment_piece(input, used, take).logical as nat == input.logical as nat + used as nat,
        fragment_piece(input, used, take).physical as nat == input.physical as nat + used as nat,
        logical_end(fragment_piece(input, used, take)) ==
            input.logical as nat + used as nat + take as nat,
        physical_end(fragment_piece(input, used, take)) ==
            input.physical as nat + used as nat + take as nat,
{
    fragment_scalar_interval_bounds(input, blocks);
    assert(input.logical as nat + (used as nat) < LOGICAL_END);
    assert(input.logical as nat + (used as nat) <= u32::MAX);
    assert(input.physical as nat + (used as nat) <= u64::MAX);
}

// This statement intentionally allows a zero-length first part. At used==0,
// emit's mapping invariant has an empty prefix without requiring it to be a
// valid on-disk extent.
proof fn fragment_adjacent_singletons_mapping(first: Run, second: Run, merged: Run)
    requires first.initialized == second.initialized,
        logical_end(first) == second.logical,
        physical_end(first) == second.physical,
        merged.logical == first.logical, merged.physical == first.physical,
        merged.initialized == first.initialized,
        merged.length as nat == first.length as nat + second.length as nat,
    ensures forall|logical: nat| logical < LOGICAL_END ==>
        #[trigger] mapping_at(seq![merged], logical)
            == mapping_at(seq![first, second], logical),
{
    assert forall|logical: nat| logical < LOGICAL_END implies
        #[trigger] mapping_at(seq![merged], logical)
            == mapping_at(seq![first, second], logical) by {
        reveal_with_fuel(mapping_at, 3);
        assert(seq![first, second].drop_first() =~= seq![second]);
        assert(seq![first].drop_first() =~= Seq::<Run>::empty());
        assert(seq![second].drop_first() =~= Seq::<Run>::empty());
        assert(seq![merged].drop_first() =~= Seq::<Run>::empty());
        if first.logical <= logical < logical_end(first) {
            assert(logical < logical_end(merged));
        } else if second.logical <= logical < logical_end(second) {
            assert(first.logical <= logical < logical_end(merged));
            assert(second.physical as nat + logical - second.logical as nat
                == first.physical as nat + logical - first.logical as nat);
        } else {
            assert(!(merged.logical <= logical < logical_end(merged)));
        }
    }
}

proof fn fragment_empty_prefix_mapping(before: Seq<Run>, input: Run)
    ensures forall|logical: nat| logical < LOGICAL_END ==>
        #[trigger] mapping_at(before + seq![fragment_prefix(input, 0)], logical)
            == mapping_at(before, logical),
{
    assert forall|logical: nat| logical < LOGICAL_END implies
        #[trigger] mapping_at(before + seq![fragment_prefix(input, 0)], logical)
            == mapping_at(before, logical) by {
        mapping_concatenate(before, seq![fragment_prefix(input, 0)], logical);
        reveal_with_fuel(mapping_at, 2);
        assert(!(input.logical <= logical < input.logical as nat));
    }
}

proof fn fragment_prefix_extension(input: Run, used: u32, take: u32, blocks: u64)
    requires interval_valid(input, blocks), used < input.length,
        0 < take, used as nat + (take as nat) <= input.length,
        input.physical as nat + (used as nat) < PHYSICAL_LIMIT,
    ensures forall|logical: nat| logical < LOGICAL_END ==>
        #[trigger] mapping_at(seq![fragment_prefix(input, (used as nat + take as nat) as u32)], logical)
            == mapping_at(seq![fragment_prefix(input, used), fragment_piece(input, used, take)], logical),
{
    fragment_piece_bounds(input, used, take, blocks);
    assert(used as nat + (take as nat) <= u32::MAX);
    fragment_adjacent_singletons_mapping(
        fragment_prefix(input, used),
        fragment_piece(input, used, take),
        fragment_prefix(input, (used as nat + take as nat) as u32),
    );
}

proof fn fragment_wire_push(before: Seq<Run>, piece: Run, blocks: u64)
    requires wire_runs(before, blocks), interval_valid(piece, blocks),
        piece.length <= maximum_length(piece),
        before.len() > 0 ==> logical_end(before.last()) <= piece.logical,
        before.len() > 0
            && before.last().initialized == piece.initialized
            && logical_end(before.last()) == piece.logical
            && physical_end(before.last()) == piece.physical
            ==> before.last().length == maximum_length(before.last()),
    ensures wire_runs(before.push(piece), blocks),
{
    let after = before.push(piece);
    assert forall|i: int| 0 <= i < after.len() implies
        #[trigger] interval_valid(after[i], blocks) by {
        if i < before.len() { assert(after[i] == before[i]); }
        else { assert(i == before.len()); assert(after[i] == piece); }
    }
    assert forall|i: int, j: int| #![trigger after[i], after[j]] 0 <= i < j < after.len() implies
        logical_end(after[i]) <= after[j].logical by {
        if j < before.len() {
            assert(after[i] == before[i]); assert(after[j] == before[j]);
        } else {
            assert(j == before.len()); assert(after[j] == piece);
            if i + 1 == before.len() {
                assert(before[i] == before.last());
            } else {
                assert(i < before.len() as int - 1);
                assert(logical_end(before[i]) <= before.last().logical);
                assert(interval_valid(before.last(), blocks));
                assert(before.last().logical <= logical_end(before.last()));
            }
        }
    }
    assert forall|i: int| 0 <= i < after.len() implies
        after[i].length <= #[trigger] maximum_length(after[i]) by {
        if i < before.len() { assert(after[i] == before[i]); }
        else { assert(after[i] == piece); }
    }
    assert forall|i: int| #![trigger after[i]] 0 < i < after.len() implies
        (after[i - 1].initialized == after[i].initialized
        && logical_end(after[i - 1]) == after[i].logical
        && physical_end(after[i - 1]) == after[i].physical)
        ==> after[i - 1].length == maximum_length(after[i - 1]) by {
        if i < before.len() {
            assert(after[i - 1] == before[i - 1]); assert(after[i] == before[i]);
        } else {
            assert(i == before.len());
            assert(after[i - 1] == before.last()); assert(after[i] == piece);
        }
    }
}

proof fn fragment_wire_extend_last_shape(before: Seq<Run>, piece: Run, merged: Run, blocks: u64)
    requires before.len() > 0, wire_runs(before, blocks),
        interval_valid(piece, blocks), interval_valid(merged, blocks),
        before.last().initialized == piece.initialized,
        logical_end(before.last()) == piece.logical,
        physical_end(before.last()) == piece.physical,
        merged.logical == before.last().logical,
        merged.physical == before.last().physical,
        merged.initialized == before.last().initialized,
        merged.length as nat == before.last().length as nat + piece.length as nat,
        merged.length <= maximum_length(merged),
    ensures wire_runs(before.update(before.len() as int - 1, merged), blocks),
{
    let at = before.len() as int - 1;
    let after = before.update(at, merged);
    let prefix = before.drop_last();
    assert(before =~= prefix + seq![before.last()]);
    assert(after =~= prefix + seq![merged]);
    assert((before + seq![piece]) =~= prefix + seq![before.last(), piece]);
    assert forall|i: int| 0 <= i < after.len() implies
        #[trigger] interval_valid(after[i], blocks) by {
        if i == at { assert(after[i] == merged); }
        else { assert(after[i] == before[i]); }
    }
    assert forall|i: int, j: int| #![trigger after[i], after[j]] 0 <= i < j < after.len() implies
        logical_end(after[i]) <= after[j].logical by {
        assert(i < at); assert(after[i] == before[i]);
        if j == at {
            assert(after[j] == merged);
            assert(logical_end(before[i]) <= before[at].logical);
        } else { assert(after[j] == before[j]); }
    }
    assert forall|i: int| 0 <= i < after.len() implies
        after[i].length <= #[trigger] maximum_length(after[i]) by {
        if i == at { assert(after[i] == merged); }
        else { assert(after[i] == before[i]); }
    }
    assert forall|i: int| #![trigger after[i]] 0 < i < after.len() implies
        (after[i - 1].initialized == after[i].initialized
        && logical_end(after[i - 1]) == after[i].logical
        && physical_end(after[i - 1]) == after[i].physical)
        ==> after[i - 1].length == maximum_length(after[i - 1]) by {
        assert(i - 1 < at); assert(after[i - 1] == before[i - 1]);
        if i == at {
            assert(after[i] == merged);
            assert(merged.logical == before[i].logical);
            assert(merged.physical == before[i].physical);
            assert(merged.initialized == before[i].initialized);
        } else { assert(after[i] == before[i]); }
    }
}


proof fn fragment_wire_extend_last_mapping(before: Seq<Run>, piece: Run, merged: Run)
    requires before.len() > 0, before.last().initialized == piece.initialized,
        logical_end(before.last()) == piece.logical, physical_end(before.last()) == piece.physical,
        merged.logical == before.last().logical, merged.physical == before.last().physical,
        merged.initialized == before.last().initialized,
        merged.length as nat == before.last().length as nat + piece.length as nat,
    ensures forall|logical: nat| logical < LOGICAL_END ==>
        #[trigger] mapping_at(before.update(before.len() as int - 1, merged), logical)
            == mapping_at(before + seq![piece], logical),
{
    let after = before.update(before.len() as int - 1, merged);
    let prefix = before.drop_last();
    assert(before =~= prefix + seq![before.last()]);
    assert(after =~= prefix + seq![merged]);
    assert(before + seq![piece] =~= prefix + seq![before.last(), piece]);
    fragment_adjacent_singletons_mapping(before.last(), piece, merged);
    assert forall|logical: nat| logical < LOGICAL_END implies
        #[trigger] mapping_at(after, logical)
            == mapping_at(before + seq![piece], logical) by {
        mapping_concatenate(prefix, seq![merged], logical);
        mapping_concatenate(prefix, seq![before.last(), piece], logical);
        assert(mapping_at(seq![merged], logical)
            == mapping_at(seq![before.last(), piece], logical));
    }
}

proof fn fragment_wire_extend_last(before: Seq<Run>, piece: Run, merged: Run, blocks: u64)
    requires before.len() > 0, wire_runs(before, blocks),
        interval_valid(piece, blocks), interval_valid(merged, blocks),
        before.last().initialized == piece.initialized,
        logical_end(before.last()) == piece.logical,
        physical_end(before.last()) == piece.physical,
        merged.logical == before.last().logical,
        merged.physical == before.last().physical,
        merged.initialized == before.last().initialized,
        merged.length as nat == before.last().length as nat + piece.length as nat,
        merged.length <= maximum_length(merged),
    ensures wire_runs(before.update(before.len() as int - 1, merged), blocks),
        forall|logical: nat| logical < LOGICAL_END ==>
            #[trigger] mapping_at(before.update(before.len() as int - 1, merged), logical)
                == mapping_at(before + seq![piece], logical),
{
    fragment_wire_extend_last_shape(before, piece, merged, blocks);
    fragment_wire_extend_last_mapping(before, piece, merged);
}

proof fn fragment_progress_after_append(
    before: Seq<Run>, old_out: Seq<Run>, after: Seq<Run>,
    input: Run, used: u32, take: u32, blocks: u64,
)
    requires interval_valid(input, blocks), used < input.length,
        0 < take, used as nat + (take as nat) <= input.length,
        input.physical as nat + (used as nat) < PHYSICAL_LIMIT,
        forall|logical: nat| logical < LOGICAL_END ==>
            #[trigger] mapping_at(old_out, logical)
                == mapping_at(before + seq![fragment_prefix(input, used)], logical),
        forall|logical: nat| logical < LOGICAL_END ==>
            #[trigger] mapping_at(after, logical)
                == mapping_at(old_out + seq![fragment_piece(input, used, take)], logical),
    ensures forall|logical: nat| logical < LOGICAL_END ==>
        #[trigger] mapping_at(after, logical)
            == mapping_at(before + seq![fragment_prefix(input, (used as nat + take as nat) as u32)], logical),
{
    mapping_equivalence_survives_append(
        old_out, before + seq![fragment_prefix(input, used)],
        seq![fragment_piece(input, used, take)]);
    fragment_prefix_extension(input, used, take, blocks);
    assert((before + seq![fragment_prefix(input, used)])
        + seq![fragment_piece(input, used, take)]
        =~= before + seq![fragment_prefix(input, used), fragment_piece(input, used, take)]);
    assert forall|logical: nat| logical < LOGICAL_END implies
        #[trigger] mapping_at(after, logical)
            == mapping_at(before + seq![fragment_prefix(input, (used as nat + take as nat) as u32)], logical) by {
        mapping_concatenate(before,
            seq![fragment_prefix(input, used), fragment_piece(input, used, take)], logical);
        mapping_concatenate(before,
            seq![fragment_prefix(input, (used as nat + take as nat) as u32)], logical);
    }
}

// Ordered prefix plus the next nonoverlapping logical extent.
proof fn fragment_ordered_push(before: Seq<Run>, run: Run, blocks: u64)
    requires ordered_intervals(before, blocks), interval_valid(run, blocks),
        before.len() > 0 ==> logical_end(before.last()) <= run.logical,
    ensures ordered_intervals(before.push(run), blocks),
{
    assert forall|i: int| 0 <= i < before.push(run).len() implies
        #[trigger] interval_valid(before.push(run)[i], blocks) by {
        if i < before.len() { assert(before.push(run)[i] == before[i]); }
        else { assert(before.push(run)[i] == run); }
    }
    assert forall|i: int, j: int| #![trigger before.push(run)[i], before.push(run)[j]] 0 <= i < j < before.push(run).len() implies
        logical_end(before.push(run)[i]) <= before.push(run)[j].logical by {
        if j < before.len() {
            assert(before.push(run)[i] == before[i]);
            assert(before.push(run)[j] == before[j]);
        } else {
            assert(before.push(run)[j] == run);
            if i + 1 == before.len() { assert(before[i] == before.last()); }
            else {
                assert(i < before.len() as int - 1);
                assert(logical_end(before[i]) <= before.last().logical);
                assert(interval_valid(before.last(), blocks));
            }
        }
    }
}

proof fn fragment_intervals_transfer_by_multiset(before: Seq<Run>, after: Seq<Run>, blocks: u64)
    requires same_multiset(before, after),
        forall|i: int| 0 <= i < before.len() ==> #[trigger] interval_valid(before[i], blocks),
    ensures forall|i: int| 0 <= i < after.len() ==> #[trigger] interval_valid(after[i], blocks),
{
    assert forall|i: int| 0 <= i < after.len() implies
        #[trigger] interval_valid(after[i], blocks) by {
        let value = after[i];
        assert(after.contains(value));
        occurrences_are_membership(after, value);
        assert(occurrences(after, value) > 0);
        assert(occurrences(before, value) == occurrences(after, value));
        occurrences_are_membership(before, value);
        assert(before.contains(value));
        let witness = choose|j: int| 0 <= j < before.len() && #[trigger] before[j] == value;
        assert(interval_valid(before[witness], blocks));
    }
}

fn emit(out: &mut Vec<Run>, input: Run, blocks: u64, budget: usize) -> (r: Result<(), Error>)
    requires blocks > 0, old(out).len() <= budget <= MAX_EXTENTS, wire_runs(old(out)@, blocks),
        interval_valid(input, blocks) ==> ordered_intervals(old(out)@ + seq![input], blocks),
    ensures final(out).len() <= budget, wire_runs(final(out)@, blocks),
        match r {
            Ok(()) => interval_valid(input, blocks)
                && final(out).len() > 0
                && logical_end(final(out)@[final(out).len() as int - 1]) == logical_end(input)
                && (forall|logical: nat| logical < LOGICAL_END ==>
                    #[trigger] mapping_at(final(out)@, logical) == mapping_at(old(out)@ + seq![input], logical)),
            Err(_) => true,
        },
{
    let ghost before = out@;
    if !interval_ok(input, blocks) { return Err(Error::Range); }
    let maximum = if input.initialized { 32768u32 } else { 32767u32 };
    let mut used = 0u32;
    proof {
        assert(ordered_intervals(before + seq![input], blocks));
        if before.len() > 0 {
            assert((before + seq![input])[before.len() as int - 1] == before.last());
            assert((before + seq![input])[before.len() as int] == input);
            assert(logical_end(before.last()) <= input.logical);
        }
        fragment_empty_prefix_mapping(before, input);
        fragment_scalar_interval_bounds(input, blocks);
    }
    while used < input.length
        invariant used <= input.length, out.len() <= budget <= MAX_EXTENTS,
            interval_valid(input, blocks), wire_runs(out@, blocks),
            ordered_intervals(before + seq![input], blocks),
            maximum == maximum_length(input),
            (out.len() == 0) == (before.len() == 0 && used == 0),
            used == 0 ==> out@ == before,
            forall|logical: nat| logical < LOGICAL_END ==> #[trigger] mapping_at(out@, logical)
                == mapping_at(before + seq![fragment_prefix(input, used)], logical),
            out.len() > 0 ==> logical_end(out@[out.len() as int - 1]) <= input.logical as nat + used as nat,
            used > 0 ==> out.len() > 0
                && logical_end(out@[out.len() as int - 1]) == input.logical as nat + used as nat,
        decreases input.length - used,
    {
        let ghost previous_out = out@;
        let ghost previous_used = used;
        proof {
            fragment_scalar_interval_bounds(input, blocks);
            assert(input.physical as nat + (used as nat) <= u64::MAX);
            assert(input.logical as nat + (used as nat) < LOGICAL_END);
        }
        let logical = input.logical as u64 + used as u64;
        let physical = input.physical + used as u64;
        if physical >= PHYSICAL_LIMIT { return Err(Error::AddressTooWide); }
        let remaining = input.length - used;
        if out.len() != 0 {
            let at = out.len() - 1; let mut last = out[at];
            proof { fragment_scalar_interval_bounds(last, blocks); }
            if last.initialized == input.initialized
                && last.logical as u64 + last.length as u64 == logical
                && last.physical + last.length as u64 == physical && last.length < maximum {
                let room = maximum - last.length;
                let take = if remaining < room { remaining } else { room };
                let ghost previous_last = last;
                proof {
                    assert(0 < take <= remaining);
                    assert(used as nat + (take as nat) <= input.length);
                    fragment_piece_bounds(input, used, take, blocks);
                    assert(last.length as nat + (take as nat) <= maximum);
                    assert(previous_out.last() == previous_last);
                }
                last.length += take;
                proof {
                    let piece = fragment_piece(input, previous_used, take);
                    assert(last.logical == previous_last.logical);
                    assert(last.physical == previous_last.physical);
                    assert(last.initialized == previous_last.initialized);
                    assert(last.length as nat == previous_last.length as nat + take as nat);
                    assert(logical_end(previous_last) == piece.logical);
                    assert(physical_end(previous_last) == piece.physical);
                    assert(logical_end(last) == logical_end(piece));
                    assert(physical_end(last) == physical_end(piece));
                    fragment_piece_bounds(input, previous_used, take, blocks);
                    assert(interval_valid(previous_last, blocks));
                    assert(0 < last.length && logical_end(last) <= LOGICAL_END);
                    assert(0 < last.physical < PHYSICAL_LIMIT && physical_end(last) <= blocks);
                    assert(interval_valid(last, blocks));
                    assert(last.length <= maximum_length(last));
                    fragment_wire_extend_last(previous_out, piece, last, blocks);
                }
                out[at] = last;
                used += take;
                proof {
                    assert(out@ =~= previous_out.update(previous_out.len() as int - 1, last));
                    fragment_progress_after_append(
                        before, previous_out, out@, input, previous_used, take, blocks);
                    assert(logical_end(out@.last()) == input.logical as nat + used as nat);
                }
                continue;
            }
            proof {
                assert(last == previous_out.last());
                assert(last.length <= maximum_length(last));
                assert(last.initialized == input.initialized
                    && logical_end(last) == logical
                    && physical_end(last) == physical
                    ==> last.length == maximum_length(last)) by {
                    if last.initialized == input.initialized
                        && logical_end(last) == logical
                        && physical_end(last) == physical {
                        assert(maximum_length(last) == maximum);
                        assert(!(last.length < maximum));
                    }
                }
            }
        }
        if out.len() >= budget { return Err(Error::Budget); }
        let take = if remaining < maximum { remaining } else { maximum };
        proof {
            assert(0 < take <= remaining);
            assert(used as nat + (take as nat) <= input.length);
            fragment_piece_bounds(input, used, take, blocks);
            let piece = fragment_piece(input, used, take);
            assert(piece.logical as nat == logical);
            assert(piece.physical == physical);
            assert(piece.length <= maximum_length(piece));
            if previous_out.len() > 0 {
                assert(logical_end(previous_out.last()) <= piece.logical);
                assert(previous_out.last().initialized == piece.initialized
                    && logical_end(previous_out.last()) == piece.logical
                    && physical_end(previous_out.last()) == piece.physical
                    ==> previous_out.last().length == maximum_length(previous_out.last()));
            }
            fragment_wire_push(previous_out, piece, blocks);
        }
        out.push(Run { logical: logical as u32, length: take, physical, initialized: input.initialized });
        used += take;
        proof {
            let piece = fragment_piece(input, previous_used, take);
            assert(out@ =~= previous_out.push(piece));
            assert(out@ =~= previous_out + seq![piece]);
            fragment_progress_after_append(
                before, previous_out, out@, input, previous_used, take, blocks);
            assert(logical_end(out@.last()) == input.logical as nat + used as nat);
        }
    }
    proof {
        assert(used == input.length);
        assert(fragment_prefix(input, used) == input);
        assert(used > 0);
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
    proof {
        assert(current@ =~= input@);
        assert(same_multiset(input@, current@));
    }
    let n = current.len(); let mut width = 1usize;
    while width < n
        invariant 1 <= width, width <= if n == 0 { 1usize } else { n }, n <= MAX_EXTENTS, current.len() == n,
            same_multiset(input@, current@),
            forall|left: int, right: int| #![trigger current@[left], current@[right]] 0 <= left < right < n && left / (width as int) == right / (width as int) ==>
                current@[left].physical <= current@[right].physical,
        decreases n - width,
    {
        let mut next = Vec::<Run>::new(); let mut left = 0usize;
        while left < n
            invariant left <= n, current.len() == n, next.len() == left, 0 < width <= n, n <= MAX_EXTENTS,
                same_multiset(input@, current@),
                forall|i: int, j: int| #![trigger current@[i], current@[j]] 0 <= i < j < n && i / (width as int) == j / (width as int) ==>
                    current@[i].physical <= current@[j].physical,
                (left as int) % (2 * width as int) == 0 || left == n,
                forall|i: int, j: int| #![trigger next@[i], next@[j]] 0 <= i < j < next.len()
                    && i / (2 * width as int) == j / (2 * width as int) ==>
                        next@[i].physical <= next@[j].physical,
                forall|value: Run| #[trigger] occurrences(next@, value)
                    == occurrences(current@.take(left as int), value),
            decreases n - left,
        {
            let middle = if width > n - left { n } else { left + width };
            let end = if width > n - middle { n } else { middle + width };
            proof {
                fragment_merge_geometry(left as int, width as int, n as int, middle as int, end as int);
            }
            let ghost completed = next@;
            let mut a = left; let mut b = middle;
            while a < middle || b < end
                invariant left <= a <= middle <= b <= end <= n, current.len() == n,
                    0 < width <= n, n <= MAX_EXTENTS,
                    left % width == 0, middle < n ==> middle % width == 0,
                    middle <= left + width, end <= middle + width,
                    completed.len() == left, next@.take(left as int) == completed,
                    next.len() == left + (a - left) + (b - middle),
                    same_multiset(input@, current@),
                    forall|i: int, j: int| #![trigger current@[i], current@[j]] 0 <= i < j < n && i / (width as int) == j / (width as int) ==>
                        current@[i].physical <= current@[j].physical,
                    (left as int) % (2 * width as int) == 0, end <= left + 2 * width,
                    physically_sorted(next@.subrange(left as int, next.len() as int)),
                    next.len() > left && a < middle ==> next@.last().physical <= current@[a as int].physical,
                    next.len() > left && b < end ==> next@.last().physical <= current@[b as int].physical,
                    forall|i: int, j: int| #![trigger next@[i], next@[j]] 0 <= i < j < left && i / (2 * width as int) == j / (2 * width as int) ==>
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
                let ghost took_left = b >= end || (a < middle
                    && current@[a as int].physical <= current@[b as int].physical);
                let ghost chosen = if took_left { current@[a as int] } else { current@[b as int] };
                if b >= end || (a < middle && current[a].physical <= current[b].physical) {
                    next.push(current[a]); a += 1;
                } else { next.push(current[b]); b += 1; }
                proof {
                    assert(next@ =~= previous_output.push(chosen));
                    let old_chunk = previous_output.subrange(left as int, previous_output.len() as int);
                    assert(next@.subrange(left as int, next.len() as int) =~= old_chunk.push(chosen));
                    if previous_output.len() > left {
                        if took_left {
                            assert(previous_output.last().physical <= current@[previous_a as int].physical);
                        } else {
                            assert(previous_output.last().physical <= current@[previous_b as int].physical);
                        }
                    }
                    fragment_sorted_push_runs(old_chunk, chosen);
                    if a < middle {
                        if took_left {
                            fragment_same_aligned_block(left as int, width as int, previous_a as int);
                            fragment_same_aligned_block(left as int, width as int, a as int);
                            assert(current@[previous_a as int].physical <= current@[a as int].physical);
                        } else {
                            assert(a == previous_a);
                            assert(current@[previous_b as int].physical <= current@[a as int].physical);
                        }
                    }
                    if b < end {
                        if took_left {
                            assert(b == previous_b);
                            assert(current@[previous_a as int].physical <= current@[b as int].physical);
                        } else {
                            assert(middle < n);
                            fragment_same_aligned_block(middle as int, width as int, previous_b as int);
                            fragment_same_aligned_block(middle as int, width as int, b as int);
                            assert(current@[previous_b as int].physical <= current@[b as int].physical);
                        }
                    }
                    assert forall|value: Run| #[trigger] occurrences(next@, value)
                        == occurrences(current@.take(left as int), value)
                         + occurrences(current@.subrange(left as int, a as int), value)
                         + occurrences(current@.subrange(middle as int, b as int), value) by {
                        fragment_occurrences_push(previous_output, chosen, value);
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
            proof {
                assert(next.len() == end);
                fragment_finish_chunk_runs(completed, next@, width as int);
                if end < n { assert(end as int % (2 * width as int) == 0); }
            }
            left = end;
        }
        proof {
            assert(current@.take(n as int) =~= current@);
            assert(same_multiset(current@, next@));
            fragment_multiset_transitive(input@, current@, next@);
        }
        let ghost old_width = width as int;
        let ghost merged = next@;
        let ghost use_whole = width > n / 2;
        current = next;
        width = if width > n / 2 { n } else { width * 2 };
        proof {
            assert forall|i: int, j: int| #![trigger current@[i], current@[j]] 0 <= i < j < n
                && i / (width as int) == j / (width as int)
                implies current@[i].physical <= current@[j].physical by {
                if use_whole {
                    fragment_double_exceeds(n as int, old_width);
                    fragment_same_aligned_block(0, 2 * old_width, i);
                    fragment_same_aligned_block(0, 2 * old_width, j);
                } else {
                    assert(width as int == 2 * old_width);
                }
            }
        }
    }
    proof {
        assert forall|i: int, j: int| #![trigger current@[i], current@[j]] 0 <= i < j < current.len()
            implies current@[i].physical <= current@[j].physical by {
            fragment_same_aligned_block(0, width as int, i);
            fragment_same_aligned_block(0, width as int, j);
        }
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
    proof {
        assert(current@ =~= input@);
        assert(same_multiset(input@, current@));
    }
    let n = current.len(); let mut width = 1usize;
    while width < n
        invariant 1 <= width, width <= if n == 0 { 1usize } else { n }, n <= MAX_METADATA_NODES, current.len() == n,
            same_multiset(input@, current@),
            forall|left: int, right: int| #![trigger current@[left], current@[right]] 0 <= left < right < n && left / (width as int) == right / (width as int) ==>
                current@[left] <= current@[right],
        decreases n - width,
    {
        let mut next = Vec::<u64>::new(); let mut left = 0usize;
        while left < n
            invariant left <= n, current.len() == n, next.len() == left, 0 < width <= n, n <= MAX_METADATA_NODES,
                same_multiset(input@, current@),
                forall|i: int, j: int| #![trigger current@[i], current@[j]] 0 <= i < j < n && i / (width as int) == j / (width as int) ==>
                    current@[i] <= current@[j],
                (left as int) % (2 * width as int) == 0 || left == n,
                forall|i: int, j: int| #![trigger next@[i], next@[j]] 0 <= i < j < next.len()
                    && i / (2 * width as int) == j / (2 * width as int) ==>
                        next@[i] <= next@[j],
                forall|value: u64| #[trigger] occurrences(next@, value)
                    == occurrences(current@.take(left as int), value),
            decreases n - left,
        {
            let middle = if width > n - left { n } else { left + width };
            let end = if width > n - middle { n } else { middle + width };
            proof {
                fragment_merge_geometry(left as int, width as int, n as int, middle as int, end as int);
            }
            let ghost completed = next@;
            let mut a = left; let mut b = middle;
            while a < middle || b < end
                invariant left <= a <= middle <= b <= end <= n, current.len() == n,
                    0 < width <= n, n <= MAX_METADATA_NODES,
                    left % width == 0, middle < n ==> middle % width == 0,
                    middle <= left + width, end <= middle + width,
                    completed.len() == left, next@.take(left as int) == completed,
                    next.len() == left + (a - left) + (b - middle),
                    same_multiset(input@, current@),
                    forall|i: int, j: int| #![trigger current@[i], current@[j]] 0 <= i < j < n && i / (width as int) == j / (width as int) ==>
                        current@[i] <= current@[j],
                    (left as int) % (2 * width as int) == 0, end <= left + 2 * width,
                    addresses_sorted(next@.subrange(left as int, next.len() as int)),
                    next.len() > left && a < middle ==> next@.last() <= current@[a as int],
                    next.len() > left && b < end ==> next@.last() <= current@[b as int],
                    forall|i: int, j: int| #![trigger next@[i], next@[j]] 0 <= i < j < left && i / (2 * width as int) == j / (2 * width as int) ==>
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
                let ghost took_left = b >= end || (a < middle
                    && current@[a as int] <= current@[b as int]);
                let ghost chosen = if took_left { current@[a as int] } else { current@[b as int] };
                if b >= end || (a < middle && current[a] <= current[b]) {
                    next.push(current[a]); a += 1;
                } else { next.push(current[b]); b += 1; }
                proof {
                    assert(next@ =~= previous_output.push(chosen));
                    let old_chunk = previous_output.subrange(left as int, previous_output.len() as int);
                    assert(next@.subrange(left as int, next.len() as int) =~= old_chunk.push(chosen));
                    if previous_output.len() > left {
                        if took_left {
                            assert(previous_output.last() <= current@[previous_a as int]);
                        } else {
                            assert(previous_output.last() <= current@[previous_b as int]);
                        }
                    }
                    fragment_sorted_push_addresses(old_chunk, chosen);
                    if a < middle {
                        if took_left {
                            fragment_same_aligned_block(left as int, width as int, previous_a as int);
                            fragment_same_aligned_block(left as int, width as int, a as int);
                            assert(current@[previous_a as int] <= current@[a as int]);
                        } else {
                            assert(a == previous_a);
                            assert(current@[previous_b as int] <= current@[a as int]);
                        }
                    }
                    if b < end {
                        if took_left {
                            assert(b == previous_b);
                            assert(current@[previous_a as int] <= current@[b as int]);
                        } else {
                            assert(middle < n);
                            fragment_same_aligned_block(middle as int, width as int, previous_b as int);
                            fragment_same_aligned_block(middle as int, width as int, b as int);
                            assert(current@[previous_b as int] <= current@[b as int]);
                        }
                    }
                    assert forall|value: u64| #[trigger] occurrences(next@, value)
                        == occurrences(current@.take(left as int), value)
                         + occurrences(current@.subrange(left as int, a as int), value)
                         + occurrences(current@.subrange(middle as int, b as int), value) by {
                        fragment_occurrences_push(previous_output, chosen, value);
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
            proof {
                assert(next.len() == end);
                fragment_finish_chunk_addresses(completed, next@, width as int);
                if end < n { assert(end as int % (2 * width as int) == 0); }
            }
            left = end;
        }
        proof {
            assert(current@.take(n as int) =~= current@);
            assert(same_multiset(current@, next@));
            fragment_multiset_transitive(input@, current@, next@);
        }
        let ghost old_width = width as int;
        let ghost merged = next@;
        let ghost use_whole = width > n / 2;
        current = next;
        width = if width > n / 2 { n } else { width * 2 };
        proof {
            assert forall|i: int, j: int| #![trigger current@[i], current@[j]] 0 <= i < j < n
                && i / (width as int) == j / (width as int)
                implies current@[i] <= current@[j] by {
                if use_whole {
                    fragment_double_exceeds(n as int, old_width);
                    fragment_same_aligned_block(0, 2 * old_width, i);
                    fragment_same_aligned_block(0, 2 * old_width, j);
                } else {
                    assert(width as int == 2 * old_width);
                }
            }
        }
    }
    proof {
        assert forall|i: int, j: int| #![trigger current@[i], current@[j]] 0 <= i < j < current.len()
            implies current@[i] <= current@[j] by {
            fragment_same_aligned_block(0, width as int, i);
            fragment_same_aligned_block(0, width as int, j);
        }
    }
    Ok(current)
}

proof fn extent_append_is_ordered(prefix: Seq<Run>, run: Run, blocks: u64)
    requires ordered_intervals(prefix, blocks), interval_valid(run, blocks),
        prefix.len() == 0 || logical_end(prefix.last()) <= run.logical,
    ensures ordered_intervals(prefix + seq![run], blocks),
{
    let next = prefix + seq![run];
    assert forall|i: int| 0 <= i < next.len() implies #[trigger] interval_valid(next[i], blocks) by {
        if i < prefix.len() { assert(next[i] == prefix[i]); }
        else { assert(i == prefix.len() && next[i] == run); }
    }
    assert forall|i: int, j: int| #![trigger next[i], next[j]] 0 <= i < j < next.len()
        implies logical_end(next[i]) <= next[j].logical by {
        if j < prefix.len() { assert(next[i] == prefix[i] && next[j] == prefix[j]); }
        else {
            assert(j == prefix.len() && next[j] == run && i < prefix.len());
            if i + 1 < prefix.len() {
                assert(logical_end(prefix[i]) <= prefix.last().logical);
                assert(interval_valid(prefix.last(), blocks));
                assert(prefix.last().logical < logical_end(prefix.last()));
            } else { assert(prefix[i] == prefix.last()); }
        }
    }
}

proof fn one_run_mapping(run: Run, logical: nat)
    ensures mapping_at(seq![run], logical) ==
        if run.logical <= logical < logical_end(run) {
            let physical = (run.physical as nat + logical - run.logical as nat) as u64;
            if run.initialized { Mapping::Written(physical) } else { Mapping::Unwritten(physical) }
        } else { Mapping::Hole },
{
    reveal_with_fuel(mapping_at, 2);
    assert(seq![run].drop_first() =~= Seq::<Run>::empty());
}

spec fn mapping_same(before: Seq<Run>, after: Seq<Run>) -> bool {
    forall|logical: nat| logical < LOGICAL_END ==>
        #[trigger] mapping_at(after, logical) == mapping_at(before, logical)
}
proof fn mapping_same_transitive(first: Seq<Run>, second: Seq<Run>, third: Seq<Run>)
    requires mapping_same(first, second), mapping_same(second, third),
    ensures mapping_same(first, third),
{
    assert forall|logical: nat| logical < LOGICAL_END
        implies #[trigger] mapping_at(third, logical) == mapping_at(first, logical) by {}
}
proof fn emitted_fragment_mapping(before: Seq<Run>, parts: Seq<Run>, prior: Seq<Run>,
    after: Seq<Run>, fragment: Run)
    requires mapping_same(before + parts, prior),
        mapping_same(prior + seq![fragment], after),
    ensures mapping_same(before + (parts + seq![fragment]), after),
{
    mapping_equivalence_survives_append(before + parts, prior, seq![fragment]);
    assert((before + parts) + seq![fragment] =~= before + (parts + seq![fragment]));
    assert forall|logical: nat| logical < LOGICAL_END
        implies #[trigger] mapping_at(after, logical) == mapping_at(before + (parts + seq![fragment]), logical) by {}
}

spec fn fragment_of_run(run: Run, begin: nat, end: nat, initialized: bool) -> Run {
    Run { logical: begin as u32, length: (end - begin) as u32,
        physical: (run.physical as nat + begin - run.logical as nat) as u64, initialized }
}
proof fn fragment_coordinate_bounds(run: Run, blocks: u64, begin: nat, end: nat, initialized: bool)
    requires interval_valid(run, blocks), run.logical <= begin < end <= logical_end(run),
    ensures {
        let fragment = fragment_of_run(run, begin, end, initialized);
        &&& fragment.logical as nat == begin && fragment.length as nat == end - begin
        &&& logical_end(fragment) == end && fragment.length > 0
        &&& fragment.physical as nat == run.physical as nat + begin - run.logical as nat
        &&& physical_end(fragment) == run.physical as nat + end - run.logical as nat
        &&& run.physical <= fragment.physical && physical_end(fragment) <= physical_end(run)
        &&& fragment.physical < PHYSICAL_LIMIT ==> interval_valid(fragment, blocks)
    },
{
    assert(begin <= LOGICAL_END && end <= LOGICAL_END);
    assert(end - begin <= (run.length as nat) <= 4294967295);
    assert(0 < run.physical as nat + begin - (run.logical as nat)
        < run.physical as nat + (run.length as nat) <= blocks);
    assert(run.physical as nat + begin - (run.logical as nat) <= 18446744073709551615);
    assert(begin as u32 == begin && (end - begin) as u32 == end - begin);
    assert(((run.physical as nat + begin - run.logical as nat) as u64) as nat
        == run.physical as nat + begin - run.logical as nat);
}

spec fn cut_run_fragments(run: Run, first: nat, end: nat) -> Seq<Run> {
    if logical_end(run) <= first || end <= run.logical || first == end { seq![run] }
    else {
        (if run.logical < first { seq![fragment_of_run(run, run.logical as nat, first, run.initialized)] }
            else { Seq::empty() })
        + (if end < logical_end(run) { seq![fragment_of_run(run, end, logical_end(run), run.initialized)] }
            else { Seq::empty() })
    }
}
proof fn cut_run_mapping(run: Run, blocks: u64, first: nat, end: nat)
    requires interval_valid(run, blocks), first <= end <= LOGICAL_END,
    ensures remove_map(seq![run], cut_run_fragments(run, first, end), first, end),
        forall|i: int| #![trigger cut_run_fragments(run, first, end)[i]] 0 <= i < cut_run_fragments(run, first, end).len() ==>
            run.logical <= cut_run_fragments(run, first, end)[i].logical
                && logical_end(cut_run_fragments(run, first, end)[i]) <= logical_end(run),
{
    if !(logical_end(run) <= first || end <= run.logical || first == end) {
        if run.logical < first { fragment_coordinate_bounds(run, blocks, run.logical as nat, first, run.initialized); }
        if end < logical_end(run) { fragment_coordinate_bounds(run, blocks, end, logical_end(run), run.initialized); }
    }
    assert forall|logical: nat| logical < LOGICAL_END
        implies #[trigger] mapping_at(cut_run_fragments(run, first, end), logical)
            == if first <= logical < end { Mapping::Hole } else { mapping_at(seq![run], logical) } by {
        one_run_mapping(run, logical);
        reveal_with_fuel(mapping_at, 3);
        if !(logical_end(run) <= first || end <= run.logical || first == end) {
            if run.logical < first {
                let left = fragment_of_run(run, run.logical as nat, first, run.initialized);
                one_run_mapping(left, logical);
            }
            if end < logical_end(run) {
                let right = fragment_of_run(run, end, logical_end(run), run.initialized);
                one_run_mapping(right, logical);
                if end <= logical < logical_end(run) {
                    assert(right.physical as nat + logical - right.logical as nat
                        == run.physical as nat + logical - run.logical as nat);
                }
            }
        }
    }
}

proof fn removal_mapping_result_transfer(input: Seq<Run>, candidate: Seq<Run>, output: Seq<Run>,
    first: nat, end: nat)
    requires remove_map(input, candidate, first, end), mapping_same(candidate, output),
    ensures remove_map(input, output, first, end),
{
    assert forall|logical: nat| logical < LOGICAL_END
        implies #[trigger] mapping_at(output, logical)
            == if first <= logical < end { Mapping::Hole } else { mapping_at(input, logical) } by {}
}

spec fn converted_run_fragments(run: Run, first: nat, end: nat, initialized: bool) -> Seq<Run> {
    if logical_end(run) <= first || end <= run.logical || first == end { seq![run] }
    else {
        let begin = if run.logical < first { first } else { run.logical as nat };
        let finish = if end < logical_end(run) { end } else { logical_end(run) };
        (if run.logical < first { seq![fragment_of_run(run, run.logical as nat, first, run.initialized)] }
            else { Seq::empty() })
        + seq![fragment_of_run(run, begin, finish, initialized)]
        + (if end < logical_end(run) { seq![fragment_of_run(run, end, logical_end(run), run.initialized)] }
            else { Seq::empty() })
    }
}
proof fn converted_run_mapping(run: Run, blocks: u64, first: nat, end: nat, initialized: bool)
    requires interval_valid(run, blocks), first <= end <= LOGICAL_END,
    ensures convert_map(seq![run], converted_run_fragments(run, first, end, initialized), first, end, initialized),
        forall|i: int| #![trigger converted_run_fragments(run, first, end, initialized)[i]] 0 <= i < converted_run_fragments(run, first, end, initialized).len() ==>
            run.logical <= converted_run_fragments(run, first, end, initialized)[i].logical
                && logical_end(converted_run_fragments(run, first, end, initialized)[i]) <= logical_end(run),
{
    if !(logical_end(run) <= first || end <= run.logical || first == end) {
        let begin = if run.logical < first { first } else { run.logical as nat };
        let finish = if end < logical_end(run) { end } else { logical_end(run) };
        fragment_coordinate_bounds(run, blocks, begin, finish, initialized);
        if run.logical < first { fragment_coordinate_bounds(run, blocks, run.logical as nat, first, run.initialized); }
        if end < logical_end(run) { fragment_coordinate_bounds(run, blocks, end, logical_end(run), run.initialized); }
    }
    assert forall|logical: nat| logical < LOGICAL_END
        implies #[trigger] mapping_at(converted_run_fragments(run, first, end, initialized), logical)
            == if first <= logical < end {
                match mapping_at(seq![run], logical) {
                    Mapping::Written(physical) | Mapping::Unwritten(physical) =>
                        if initialized { Mapping::Written(physical) } else { Mapping::Unwritten(physical) },
                    Mapping::Hole => Mapping::Hole,
                }
            } else { mapping_at(seq![run], logical) } by {
        one_run_mapping(run, logical);
        reveal_with_fuel(mapping_at, 4);
        if !(logical_end(run) <= first || end <= run.logical || first == end) {
            let begin = if run.logical < first { first } else { run.logical as nat };
            let finish = if end < logical_end(run) { end } else { logical_end(run) };
            let middle = fragment_of_run(run, begin, finish, initialized);
            one_run_mapping(middle, logical);
            if begin <= logical < finish {
                assert(middle.physical as nat + logical - middle.logical as nat
                    == run.physical as nat + logical - run.logical as nat);
            }
            if run.logical < first {
                one_run_mapping(fragment_of_run(run, run.logical as nat, first, run.initialized), logical);
            }
            if end < logical_end(run) {
                let right = fragment_of_run(run, end, logical_end(run), run.initialized);
                one_run_mapping(right, logical);
                if end <= logical < logical_end(run) {
                    assert(right.physical as nat + logical - right.logical as nat
                        == run.physical as nat + logical - run.logical as nat);
                }
            }
        }
    }
}
proof fn conversion_distributes_over_extent_sequences(before_first: Seq<Run>, before_second: Seq<Run>,
    after_first: Seq<Run>, after_second: Seq<Run>, first: nat, end: nat, initialized: bool)
    requires convert_map(before_first, after_first, first, end, initialized),
        convert_map(before_second, after_second, first, end, initialized),
    ensures convert_map(before_first + before_second, after_first + after_second, first, end, initialized),
{
    assert forall|logical: nat| logical < LOGICAL_END
        implies #[trigger] mapping_at(after_first + after_second, logical)
            == if first <= logical < end {
                match mapping_at(before_first + before_second, logical) {
                    Mapping::Written(physical) | Mapping::Unwritten(physical) =>
                        if initialized { Mapping::Written(physical) } else { Mapping::Unwritten(physical) },
                    Mapping::Hole => Mapping::Hole,
                }
            } else { mapping_at(before_first + before_second, logical) } by {
        mapping_concatenate(before_first, before_second, logical);
        mapping_concatenate(after_first, after_second, logical);
        if first <= logical < end {
            match mapping_at(before_first, logical) {
                Mapping::Hole => {},
                Mapping::Written(_) => {},
                Mapping::Unwritten(_) => {},
            }
        }
    }
}
proof fn conversion_mapping_result_transfer(input: Seq<Run>, candidate: Seq<Run>, output: Seq<Run>,
    first: nat, end: nat, initialized: bool)
    requires convert_map(input, candidate, first, end, initialized), mapping_same(candidate, output),
    ensures convert_map(input, output, first, end, initialized),
{
    assert forall|logical: nat| logical < LOGICAL_END
        implies #[trigger] mapping_at(output, logical)
            == if first <= logical < end {
                match mapping_at(input, logical) {
                    Mapping::Written(physical) | Mapping::Unwritten(physical) =>
                        if initialized { Mapping::Written(physical) } else { Mapping::Unwritten(physical) },
                    Mapping::Hole => Mapping::Hole,
                }
            } else { mapping_at(input, logical) } by {}
}


spec fn partial_replacement(base: Seq<Run>, output: Seq<Run>, run: Run, inserted: bool) -> bool {
    forall|logical: nat| logical < LOGICAL_END ==> #[trigger] mapping_at(output, logical)
        == if inserted && run.logical <= logical < logical_end(run) {
            mapping_at(seq![run], logical)
        } else { mapping_at(base, logical) }
}

proof fn removed_range_separates_entries(input: Seq<Run>, cleared: Seq<Run>, run: Run, blocks: u64)
    requires ordered_intervals(cleared, blocks), interval_valid(run, blocks),
        remove_map(input, cleared, run.logical as nat, logical_end(run)),
    ensures forall|i: int| #![trigger cleared[i]] 0 <= i < cleared.len() ==>
        logical_end(cleared[i]) <= run.logical || logical_end(run) <= cleared[i].logical,
{
    assert forall|i: int| #![trigger cleared[i]] 0 <= i < cleared.len()
        implies logical_end(cleared[i]) <= run.logical || logical_end(run) <= cleared[i].logical by {
        if !(logical_end(cleared[i]) <= run.logical || logical_end(run) <= cleared[i].logical) {
            assert(interval_valid(cleared[i], blocks));
            let point = if cleared[i].logical < run.logical { run.logical as nat }
                else { cleared[i].logical as nat };
            assert(cleared[i].logical <= point < logical_end(cleared[i]));
            assert(run.logical <= point < logical_end(run) <= LOGICAL_END);
            mapping_selected_entry(cleared, blocks, i, point);
            one_run_mapping(cleared[i], point);
            assert(mapping_at(cleared, point) is Hole);
            assert(false);
        }
    }
}
proof fn insert_into_partial_replacement(base: Seq<Run>, before: Seq<Run>, after: Seq<Run>, run: Run)
    requires partial_replacement(base, before, run, false),
        forall|logical: nat| run.logical <= logical < logical_end(run) && logical < LOGICAL_END
            ==> #[trigger] mapping_at(base, logical) is Hole,
        mapping_same(before + seq![run], after),
    ensures partial_replacement(base, after, run, true),
{
    assert forall|logical: nat| logical < LOGICAL_END
        implies #[trigger] mapping_at(after, logical)
            == if run.logical <= logical < logical_end(run) { mapping_at(seq![run], logical) }
                else { mapping_at(base, logical) } by {
        one_run_mapping(run, logical);
        mapping_concatenate(before, seq![run], logical);
        if run.logical <= logical < logical_end(run) {
            assert(mapping_at(before, logical) is Hole);
        }
    }
}
proof fn append_to_partial_replacement(base: Seq<Run>, before: Seq<Run>, after: Seq<Run>,
    run: Run, appended: Run, inserted: bool)
    requires partial_replacement(base, before, run, inserted),
        logical_end(appended) <= run.logical || logical_end(run) <= appended.logical,
        mapping_same(before + seq![appended], after),
    ensures partial_replacement(base + seq![appended], after, run, inserted),
{
    assert forall|logical: nat| logical < LOGICAL_END
        implies #[trigger] mapping_at(after, logical)
            == if inserted && run.logical <= logical < logical_end(run) {
                mapping_at(seq![run], logical)
            } else { mapping_at(base + seq![appended], logical) } by {
        one_run_mapping(appended, logical);
        mapping_concatenate(before, seq![appended], logical);
        mapping_concatenate(base, seq![appended], logical);
        if run.logical <= logical < logical_end(run) {
            assert(mapping_at(seq![appended], logical) is Hole);
        }
    }
}
proof fn finish_partial_replacement(input: Seq<Run>, cleared: Seq<Run>, output: Seq<Run>, run: Run)
    requires partial_replacement(cleared, output, run, true),
        remove_map(input, cleared, run.logical as nat, logical_end(run)),
    ensures replace_map(input, output, run),
{
    assert forall|logical: nat| logical < LOGICAL_END
        implies #[trigger] mapping_at(output, logical)
            == if run.logical <= logical < logical_end(run) {
                let physical = (run.physical as nat + logical - run.logical as nat) as u64;
                if run.initialized { Mapping::Written(physical) } else { Mapping::Unwritten(physical) }
            } else { mapping_at(input, logical) } by { one_run_mapping(run, logical); }
}
proof fn replacement_mapping_result_transfer(input: Seq<Run>, candidate: Seq<Run>, output: Seq<Run>, run: Run)
    requires replace_map(input, candidate, run), mapping_same(candidate, output),
    ensures replace_map(input, output, run),
{
    assert forall|logical: nat| logical < LOGICAL_END
        implies #[trigger] mapping_at(output, logical)
            == if run.logical <= logical < logical_end(run) {
                let physical = (run.physical as nat + logical - run.logical as nat) as u64;
                if run.initialized { Mapping::Written(physical) } else { Mapping::Unwritten(physical) }
            } else { mapping_at(input, logical) } by { one_run_mapping(run, logical); }
}


proof fn valid_set_has_ordered_intervals(view: SetView)
    requires valid_set(view),
    ensures ordered_intervals(view.runs, view.blocks),
{
    reveal(valid_set);
}

proof fn ordered_search_excludes_prefix(runs: Seq<Run>, blocks: u64, logical: nat, mid: int)
    requires ordered_intervals(runs, blocks), 0 <= mid < runs.len(),
        logical_end(runs[mid]) <= logical,
    ensures forall|j: int| #![trigger runs[j]] 0 <= j <= mid ==> logical_end(runs[j]) <= logical,
{
    assert forall|j: int| #![trigger runs[j]] 0 <= j <= mid
        implies logical_end(runs[j]) <= logical by {
        if j < mid {
            assert(logical_end(runs[j]) <= runs[mid].logical);
            assert(interval_valid(runs[mid], blocks));
            assert(runs[mid].logical < logical_end(runs[mid]));
        } else { assert(j == mid); }
    }
}
proof fn ordered_search_excludes_suffix(runs: Seq<Run>, blocks: u64, logical: nat, mid: int)
    requires ordered_intervals(runs, blocks), 0 <= mid < runs.len(), logical < runs[mid].logical,
    ensures forall|j: int| #![trigger runs[j]] mid <= j < runs.len() ==> logical < runs[j].logical,
{
    assert forall|j: int| #![trigger runs[j]] mid <= j < runs.len()
        implies logical < runs[j].logical by {
        if mid < j {
            assert(logical_end(runs[mid]) <= runs[j].logical);
            assert(interval_valid(runs[mid], blocks));
            assert(runs[mid].logical < logical_end(runs[mid]));
        } else { assert(j == mid); }
    }
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
        proof {
            assert(out@ =~= Seq::<Run>::empty());
            assert(input@.take(0) =~= Seq::<Run>::empty());
            assert forall|logical: nat| logical < LOGICAL_END implies
                #[trigger] mapping_at(out@, logical) == mapping_at(input@.take(0), logical) by {
                mapping_absent(Seq::<Run>::empty(), logical);
            }
        }
        while i < input.len()
            invariant i <= input.len() <= MAX_EXTENTS, out.len() <= extent_budget <= MAX_EXTENTS,
                filesystem_blocks > 0, wire_runs(out@, filesystem_blocks), end <= LOGICAL_END,
                ordered_intervals(input@.take(i as int), filesystem_blocks),
                i == 0 ==> end == 0,
                i > 0 ==> end == logical_end(input@[i as int - 1]),
                out.len() > 0 ==> logical_end(out@[out.len() as int - 1]) == end,
                forall|logical: nat| logical < LOGICAL_END ==>
                    #[trigger] mapping_at(out@, logical) == mapping_at(input@.take(i as int), logical),
            decreases input.len() - i,
        {
            let ghost previous_out = out@;
            let ghost validated = input@.take(i as int);
            let ghost previous_i = i;
            let run = input[i];
            if !interval_ok(run, filesystem_blocks) { return Err(Error::Range); }
            if (run.logical as u64) < end { return Err(Error::Order); }
            proof {
                if validated.len() > 0 {
                    assert(validated.last() == input@[i as int - 1]);
                    assert(logical_end(validated.last()) == end);
                }
                fragment_ordered_push(validated, run, filesystem_blocks);
                if previous_out.len() > 0 {
                    assert(logical_end(previous_out.last()) == end);
                }
                fragment_ordered_push(previous_out, run, filesystem_blocks);
                assert(previous_out.push(run) =~= previous_out + seq![run]);
                assert(ordered_intervals(previous_out + seq![run], filesystem_blocks));
                assert(input@.take(i as int + 1) =~= validated.push(run));
                fragment_scalar_interval_bounds(run, filesystem_blocks);
            }
            match emit(&mut out, run, filesystem_blocks, extent_budget) {
                Ok(()) => {}, Err(error) => { return Err(error); }
            }
            proof {
                mapping_equivalence_survives_append(previous_out, validated, seq![run]);
                assert(validated.push(run) =~= validated + seq![run]);
                assert forall|logical: nat| logical < LOGICAL_END implies
                    #[trigger] mapping_at(out@, logical)
                        == mapping_at(input@.take(previous_i as int + 1), logical) by {
                    assert(mapping_at(out@, logical) == mapping_at(previous_out + seq![run], logical));
                    assert(mapping_at(previous_out + seq![run], logical)
                        == mapping_at(validated + seq![run], logical));
                }
                assert(out.len() > 0);
                assert(logical_end(out@.last()) == logical_end(run));
            }
            end = run.logical as u64 + run.length as u64; i += 1;
        }
        proof {
            assert(input@.take(input.len() as int) =~= input@);
            assert(ordered_intervals(input@, filesystem_blocks));
            assert forall|logical: nat| logical < LOGICAL_END implies
                #[trigger] mapping_at(out@, logical) == mapping_at(input@, logical) by {
                assert(mapping_at(out@, logical) == mapping_at(input@.take(i as int), logical));
            }
        }
        let physical = match physical_order(&out) { Ok(physical) => physical, Err(error) => { return Err(error); } };
        proof {
            fragment_intervals_transfer_by_multiset(out@, physical@, filesystem_blocks);
        }
        i = if physical.len() == 0 { 0 } else { 1 };
        while i < physical.len()
            invariant i <= physical.len() <= MAX_EXTENTS, physical.len() > 0 ==> i > 0,
                physically_sorted(physical@), same_multiset(out@, physical@), wire_runs(out@, filesystem_blocks),
                forall|j: int| 0 <= j < physical.len() ==> #[trigger] interval_valid(physical@[j], filesystem_blocks),
                ordered_intervals(input@, filesystem_blocks),
                out.len() <= extent_budget <= MAX_EXTENTS, filesystem_blocks > 0,
                forall|logical: nat| logical < LOGICAL_END ==>
                    #[trigger] mapping_at(out@, logical) == mapping_at(input@, logical),
                forall|j: int| #![trigger physical@[j]] 0 < j < i ==> physical_end(physical@[j - 1]) <= physical@[j].physical,
            decreases physical.len() - i,
        {
            let ghost previous_i = i;
            let previous = physical[i - 1];
            proof {
                assert(interval_valid(previous, filesystem_blocks));
                fragment_scalar_interval_bounds(previous, filesystem_blocks);
            }
            if previous.physical + previous.length as u64 > physical[i].physical {
                return Err(Error::PhysicalAlias);
            }
            proof {
                assert(physical_end(physical@[i as int - 1]) <= physical@[i as int].physical);
                assert forall|j: int| #![trigger physical@[j]] 0 < j <= i implies
                    physical_end(physical@[j - 1]) <= physical@[j].physical by {
                    if j < i {
                        assert(physical_end(physical@[j - 1]) <= physical@[j].physical);
                    } else { assert(j == i); }
                }
            }
            i += 1;
            proof {
                assert forall|j: int| #![trigger physical@[j]] 0 < j < i implies
                    physical_end(physical@[j - 1]) <= physical@[j].physical by {
                    assert(j <= previous_i);
                }
            }
        }
        proof {
            sorted_neighbors_imply_physical_disjointness(physical@);
            physical_disjointness_transfers_by_multiset(out@, physical@, filesystem_blocks);
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
        proof { use_type_invariant(self); valid_set_has_ordered_intervals(self.view()); }
        let mut low = 0usize; let mut high = self.runs.len();
        while low < high
            invariant self.wf(), ordered_intervals(self.runs@, self.blocks), low <= high <= self.runs.len(),
                forall|j: int| #![trigger self.runs@[j]] 0 <= j < low ==> logical_end(self.runs@[j]) <= logical,
                forall|j: int| #![trigger self.runs@[j]] high <= j < self.runs.len() ==> logical < self.runs@[j].logical,
            decreases high - low,
        {
            let mid = low + (high - low) / 2;
            proof { assert(low <= mid < high); }
            let run = self.runs[mid];
            if logical < run.logical {
                proof { ordered_search_excludes_suffix(self.runs@, self.blocks, logical as nat, mid as int); }
                high = mid;
            }
            else if logical as u64 >= run.logical as u64 + run.length as u64 {
                proof { ordered_search_excludes_prefix(self.runs@, self.blocks, logical as nat, mid as int); }
                low = mid + 1;
            }
            else {
                proof {
                    assert(interval_valid(run, self.blocks));
                    singleton_mapping_physical_coordinate(run, self.blocks, logical as nat);
                    one_run_mapping(run, logical as nat);
                    assert(run.physical as nat + logical as nat - (run.logical as nat) <= 18446744073709551615);
                    mapping_selected_entry(self.runs@, self.blocks, mid as int, logical as nat);
                }
                let physical = run.physical + (logical - run.logical) as u64;
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
            invariant self.wf(), i <= self.runs.len(), interval_valid(run, self.blocks),
                end as nat == logical_end(run),
                forall|j: int| #![trigger self.runs@[j]] 0 <= j < i ==> !(self.runs@[j].logical < logical_end(run)
                    && run.logical < logical_end(self.runs@[j])),
            decreases self.runs.len() - i,
        {
            let old = self.runs[i];
            if (old.logical as u64) < end && (run.logical as u64) < old.logical as u64 + old.length as u64 {
                return Err(Error::LogicalOverlap);
            }
            proof {
                assert forall|j: int| #![trigger self.runs@[j]] 0 <= j <= i
                    implies !(self.runs@[j].logical < logical_end(run)
                        && run.logical < logical_end(self.runs@[j])) by {
                    if j < i {
                        assert(!(self.runs@[j].logical < logical_end(run)
                            && run.logical < logical_end(self.runs@[j])));
                    } else {
                        assert(j == i && self.runs@[j] == old);
                        assert(!(old.logical < logical_end(run) && run.logical < logical_end(old)));
                    }
                }
            }
            i += 1;
        }
        proof {
            assert forall|logical: nat| run.logical <= logical < logical_end(run)
                implies #[trigger] mapping_at(self.runs@, logical) is Hole by {
                assert forall|j: int| 0 <= j < self.runs.len()
                    implies !(self.runs@[j].logical <= logical < #[trigger] logical_end(self.runs@[j])) by {
                    assert(!(self.runs@[j].logical < logical_end(run)
                        && run.logical < logical_end(self.runs@[j])));
                }
                mapping_absent(self.runs@, logical);
            }
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
        proof { removed_range_separates_entries(self.runs@, cleared@, run, self.blocks); }
        let mut next = Vec::<Run>::new(); let mut inserted = false; let mut i = 0usize;
        proof {
            assert(cleared@.take(0) =~= Seq::<Run>::empty());
            assert forall|logical: nat| logical < LOGICAL_END
                implies #[trigger] mapping_at(next@, logical) == mapping_at(cleared@.take(0), logical) by {
                reveal(mapping_at);
            }
        }
        while i < cleared.len()
            invariant self.wf(), self.blocks > 0, interval_valid(run, self.blocks),
                i <= cleared.len() <= self.budget <= MAX_EXTENTS, next.len() <= self.budget,
                wire_runs(cleared@, self.blocks), wire_runs(next@, self.blocks),
                remove_map(self.runs@, cleared@, run.logical as nat, logical_end(run)),
                forall|j: int| #![trigger cleared@[j]] 0 <= j < cleared.len() ==>
                    logical_end(cleared@[j]) <= run.logical || logical_end(run) <= cleared@[j].logical,
                partial_replacement(cleared@.take(i as int), next@, run, inserted),
                !inserted && next.len() > 0 ==> logical_end(next@.last()) <= run.logical,
                !inserted ==> forall|j: int| #![trigger cleared@[j]] 0 <= j < i ==> logical_end(cleared@[j]) <= run.logical,
                inserted && i < cleared.len() ==> logical_end(run) <= cleared@[i as int].logical,
                next.len() > 0 && i < cleared.len() ==> logical_end(next@.last()) <= cleared@[i as int].logical,
            decreases cleared.len() - i,
        {
            if !inserted && run.logical < cleared[i].logical {
                let ghost before = next@;
                proof {
                    assert(logical_end(run) <= cleared@[i as int].logical);
                    extent_append_is_ordered(next@, run, self.blocks);
                    assert forall|logical: nat| run.logical <= logical < logical_end(run) && logical < LOGICAL_END
                        implies #[trigger] mapping_at(cleared@.take(i as int), logical) is Hole by {
                        assert forall|j: int| 0 <= j < i
                            implies !(cleared@[j].logical <= logical < #[trigger] logical_end(cleared@[j])) by {}
                        mapping_absent(cleared@.take(i as int), logical);
                    }
                }
                match emit(&mut next, run, self.blocks, self.budget) {
                    Ok(()) => {}, Err(error) => { return Err(error); }
                }
                proof { insert_into_partial_replacement(cleared@.take(i as int), before, next@, run); }
                inserted = true;
            }
            let ghost before = next@;
            proof {
                assert(interval_valid(cleared@[i as int], self.blocks));
                extent_append_is_ordered(next@, cleared@[i as int], self.blocks);
            }
            match emit(&mut next, cleared[i], self.blocks, self.budget) {
                Ok(()) => {}, Err(error) => { return Err(error); }
            }
            proof {
                append_to_partial_replacement(cleared@.take(i as int), before, next@,
                    run, cleared@[i as int], inserted);
                assert(cleared@.take(i as int + 1) =~= cleared@.take(i as int) + seq![cleared@[i as int]]);
                if !inserted { assert(logical_end(cleared@[i as int]) <= run.logical); }
                if i + 1 < cleared.len() {
                    assert(logical_end(cleared@[i as int]) <= cleared@[i as int + 1].logical);
                    if inserted {
                        assert(cleared@[i as int].logical < logical_end(cleared@[i as int]));
                    }
                }
            }
            i += 1;
        }
        proof { assert(cleared@.take(cleared.len() as int) =~= cleared@); }
        if !inserted {
            let ghost before = next@;
            proof {
                extent_append_is_ordered(next@, run, self.blocks);
                assert forall|logical: nat| run.logical <= logical < logical_end(run) && logical < LOGICAL_END
                    implies #[trigger] mapping_at(cleared@, logical) is Hole by {}
            }
            match emit(&mut next, run, self.blocks, self.budget) {
                Ok(()) => {}, Err(error) => { return Err(error); }
            }
            proof { insert_into_partial_replacement(cleared@, before, next@, run); }
        }
        proof { finish_partial_replacement(self.runs@, cleared@, next@, run); }
        let result = ExtentSet::from_sorted(&next, self.blocks, self.budget);
        proof {
            match &result {
                Ok(set) => {
                    assert(mapping_same(next@, set.view().runs));
                    replacement_mapping_result_transfer(self.runs@, next@, set.view().runs, run);
                },
                Err(_) => {},
            }
        }
        result
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
        let result = ExtentSet::from_sorted(&next, self.blocks, self.budget);
        proof {
            match &result {
                Ok(set) => {
                    assert(mapping_same(next@, set.view().runs));
                    removal_mapping_result_transfer(self.runs@, next@, set.view().runs,
                        logical as nat, logical as nat + length as nat);
                },
                Err(_) => {},
            }
        }
        result
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
        let result = ExtentSet::from_sorted(&next, self.blocks, self.budget);
        proof {
            match &result {
                Ok(set) => {
                    assert(mapping_same(next@, set.view().runs));
                    removal_mapping_result_transfer(self.runs@, next@, set.view().runs,
                        exclusive_end as nat, LOGICAL_END as nat);
                },
                Err(_) => {},
            }
        }
        result
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
        if length == 0 {
            let result = ExtentSet::from_sorted(&self.runs, self.blocks, self.budget);
            proof {
                match &result {
                    Ok(set) => {
                        assert forall|block: nat| block < LOGICAL_END
                            implies #[trigger] mapping_at(set.view().runs, block)
                                == if (logical as nat) <= block < end as nat {
                                    match mapping_at(self.runs@, block) {
                                        Mapping::Written(physical) | Mapping::Unwritten(physical) =>
                                            if initialized { Mapping::Written(physical) } else { Mapping::Unwritten(physical) },
                                        Mapping::Hole => Mapping::Hole,
                                    }
                                } else { mapping_at(self.runs@, block) } by {}
                    },
                    Err(_) => {},
                }
            }
            return result;
        }
        let mut cursor = logical as u64; let mut out = Vec::<Run>::new(); let mut i = 0usize;
        proof {
            assert(self.runs@.take(0) =~= Seq::<Run>::empty());
            assert forall|block: nat| block < LOGICAL_END
                implies #[trigger] mapping_at(out@, block)
                    == if (logical as nat) <= block < end as nat {
                        match mapping_at(self.runs@.take(0), block) {
                            Mapping::Written(physical) | Mapping::Unwritten(physical) =>
                                if initialized { Mapping::Written(physical) } else { Mapping::Unwritten(physical) },
                            Mapping::Hole => Mapping::Hole,
                        }
                    } else { mapping_at(self.runs@.take(0), block) } by { reveal(mapping_at); }
        }
        while i < self.runs.len()
            invariant self.wf(), self.blocks > 0, i <= self.runs.len(),
                out.len() <= self.budget <= MAX_EXTENTS,
                wire_runs(self.runs@, self.blocks), wire_runs(out@, self.blocks),
                (logical as u64) <= cursor <= end, end <= LOGICAL_END, length > 0,
                end as nat == logical as nat + length as nat,
                cursor == logical || i == self.runs.len() || cursor <= self.runs@[i as int].logical,
                convert_map(self.runs@.take(i as int), out@, logical as nat, end as nat, initialized),
                forall|block: nat| (logical as nat) <= block < cursor ==> !(#[trigger] mapping_at(self.runs@, block) is Hole),
                out.len() > 0 && i < self.runs.len() ==> logical_end(out@.last()) <= self.runs@[i as int].logical,
            decreases self.runs.len() - i,
        {
            let old = self.runs[i]; let old_end = old.logical as u64 + old.length as u64;
            let ghost before_output = out@;
            let ghost mut parts = Seq::<Run>::empty();
            proof {
                assert(interval_valid(old, self.blocks));
                assert(before_output + parts =~= before_output);
                assert(mapping_same(before_output + parts, out@));
            }
            if old_end <= logical as u64 || old.logical as u64 >= end {
                proof { extent_append_is_ordered(out@, old, self.blocks); }
                match emit(&mut out, old, self.blocks, self.budget) { Ok(()) => {}, Err(e) => { return Err(e); } }
                proof { parts = seq![old]; assert(mapping_same(before_output + parts, out@)); }
            } else {
                let first = if old.logical < logical { logical as u64 } else { old.logical as u64 };
                let last = if old_end > end { end } else { old_end };
                if first > cursor { return Err(Error::Hole); }
                proof {
                    assert(first == cursor);
                    assert(logical < end && old.logical < old_end);
                    assert(logical < old_end && old.logical < end);
                    if old.logical < logical { assert(first == logical); }
                    else { assert(first == old.logical); }
                    if old_end > end { assert(last == end); }
                    else { assert(last == old_end); }
                    assert(old.logical <= first < last <= old_end);
                }
                if old.logical < logical {
                    proof { fragment_coordinate_bounds(old, self.blocks, old.logical as nat, logical as nat, old.initialized); }
                    let prefix = Run { length: logical - old.logical, ..old };
                    let ghost prior = out@;
                    proof {
                        assert(prefix == fragment_of_run(old, old.logical as nat, logical as nat, old.initialized));
                        if interval_valid(prefix, self.blocks) { extent_append_is_ordered(out@, prefix, self.blocks); }
                    }
                    match emit(&mut out, prefix, self.blocks, self.budget) { Ok(()) => {}, Err(e) => { return Err(e); } }
                    proof {
                        emitted_fragment_mapping(before_output, parts, prior, out@, prefix);
                        parts = parts + seq![prefix];
                    }
                }
                proof {
                    fragment_coordinate_bounds(old, self.blocks, first as nat, last as nat, initialized);
                    assert(old.physical < PHYSICAL_LIMIT && first <= LOGICAL_END);
                    assert(old.physical as nat + (first as nat) <= 18446744073709551615);
                }
                let changed = Run { logical: first as u32, length: (last - first) as u32,
                    physical: old.physical + first - old.logical as u64, initialized };
                let ghost prior = out@;
                proof {
                    assert(changed == fragment_of_run(old, first as nat, last as nat, initialized));
                    assert(out.len() == 0 || logical_end(out@.last()) <= first);
                    if interval_valid(changed, self.blocks) { extent_append_is_ordered(out@, changed, self.blocks); }
                }
                match emit(&mut out, changed, self.blocks, self.budget) { Ok(()) => {}, Err(e) => { return Err(e); } }
                proof {
                    emitted_fragment_mapping(before_output, parts, prior, out@, changed);
                    parts = parts + seq![changed];
                }
                if old_end > end {
                    proof {
                        fragment_coordinate_bounds(old, self.blocks, end as nat, old_end as nat, old.initialized);
                        assert(old.physical as nat + (end as nat) <= 18446744073709551615);
                    }
                    let suffix = Run { logical: end as u32, length: (old_end - end) as u32,
                        physical: old.physical + end - old.logical as u64, initialized: old.initialized };
                    let ghost prior = out@;
                    proof {
                        assert(suffix == fragment_of_run(old, end as nat, old_end as nat, old.initialized));
                        assert(out.len() == 0 || logical_end(out@.last()) <= end);
                        if interval_valid(suffix, self.blocks) { extent_append_is_ordered(out@, suffix, self.blocks); }
                    }
                    match emit(&mut out, suffix, self.blocks, self.budget) { Ok(()) => {}, Err(e) => { return Err(e); } }
                    proof {
                        emitted_fragment_mapping(before_output, parts, prior, out@, suffix);
                        parts = parts + seq![suffix];
                    }
                }
                proof {
                    assert forall|block: nat| (logical as nat) <= block < last
                        implies !(#[trigger] mapping_at(self.runs@, block) is Hole) by {
                        if first <= block {
                            mapping_selected_entry(self.runs@, self.blocks, i as int, block);
                            one_run_mapping(old, block);
                        }
                    }
                }
                cursor = last;
            }
            proof {
                assert(parts =~= converted_run_fragments(old, logical as nat, end as nat, initialized));
                converted_run_mapping(old, self.blocks, logical as nat, end as nat, initialized);
                conversion_distributes_over_extent_sequences(self.runs@.take(i as int), seq![old],
                    before_output, parts, logical as nat, end as nat, initialized);
                assert(self.runs@.take(i as int + 1) =~= self.runs@.take(i as int) + seq![old]);
                conversion_mapping_result_transfer(self.runs@.take(i as int + 1), before_output + parts,
                    out@, logical as nat, end as nat, initialized);
                assert(out.len() == 0 || logical_end(out@.last()) <= old_end);
                if i + 1 < self.runs.len() {
                    assert(logical_end(old) <= self.runs@[i as int + 1].logical);
                }
            }
            i += 1;
        }
        if cursor != end { return Err(Error::Hole); }
        proof { assert(self.runs@.take(self.runs.len() as int) =~= self.runs@); }
        let result = ExtentSet::from_sorted(&out, self.blocks, self.budget);
        proof {
            match &result {
                Ok(set) => {
                    assert(mapping_same(out@, set.view().runs));
                    conversion_mapping_result_transfer(self.runs@, out@, set.view().runs,
                        logical as nat, end as nat, initialized);
                },
                Err(_) => {},
            }
        }
        result
    }

}

fn cut(input: &[Run], first: u64, end: u64, blocks: u64, budget: usize) -> (r: Result<Vec<Run>, Error>)
    requires blocks > 0, budget <= MAX_EXTENTS, wire_runs(input@, blocks), input.len() <= budget,
    ensures match r {
        Ok(out) => first <= end <= LOGICAL_END && out.len() <= budget && wire_runs(out@, blocks)
            && remove_map(input@, out@, first as nat, end as nat),
        Err(_) => true,
    },
{
    if first > end || end > LOGICAL_END { return Err(Error::Range); }
    let mut out = Vec::<Run>::new(); let mut i = 0usize;
    proof {
        assert(input@.take(0) =~= Seq::<Run>::empty());
        assert forall|point: nat| point < LOGICAL_END
            implies #[trigger] mapping_at(out@, point)
                == if first <= point < end { Mapping::Hole } else { mapping_at(input@.take(0), point) } by {
            reveal(mapping_at);
        }
    }
    while i < input.len()
        invariant blocks > 0, i <= input.len() <= budget <= MAX_EXTENTS, out.len() <= budget,
            wire_runs(input@, blocks), wire_runs(out@, blocks), first <= end <= LOGICAL_END,
            remove_map(input@.take(i as int), out@, first as nat, end as nat),
            out.len() > 0 && i < input.len() ==> logical_end(out@[out.len() as int - 1]) <= input@[i as int].logical,
        decreases input.len() - i,
    {
        let old = input[i]; let old_end = old.logical as u64 + old.length as u64;
        let ghost before_output = out@;
        let ghost mut parts = Seq::<Run>::empty();
        proof {
            assert(interval_valid(old, blocks));
            assert(before_output + parts =~= before_output);
            assert(mapping_same(before_output + parts, out@));
        }
        if old_end <= first || old.logical as u64 >= end || first == end {
            proof { extent_append_is_ordered(out@, old, blocks); }
            match emit(&mut out, old, blocks, budget) { Ok(()) => {}, Err(e) => { return Err(e); } }
            proof {
                parts = seq![old];
                assert(mapping_same(before_output + parts, out@));
            }
        } else {
            if (old.logical as u64) < first {
                proof { fragment_coordinate_bounds(old, blocks, old.logical as nat, first as nat, old.initialized); }
                let left = Run { length: (first - old.logical as u64) as u32, ..old };
                let ghost prior = out@;
                proof {
                    assert(left == fragment_of_run(old, old.logical as nat, first as nat, old.initialized));
                    if interval_valid(left, blocks) { extent_append_is_ordered(out@, left, blocks); }
                }
                match emit(&mut out, left, blocks, budget) { Ok(()) => {}, Err(e) => { return Err(e); } }
                proof {
                    emitted_fragment_mapping(before_output, parts, prior, out@, left);
                    parts = parts + seq![left];
                }
            }
            if old_end > end {
                proof {
                    fragment_coordinate_bounds(old, blocks, end as nat, old_end as nat, old.initialized);
                    assert(old.physical < PHYSICAL_LIMIT && end <= LOGICAL_END);
                    assert(old.physical as nat + (end as nat) <= 18446744073709551615);
                }
                let right = Run { logical: end as u32, length: (old_end - end) as u32,
                    physical: old.physical + end - old.logical as u64, initialized: old.initialized };
                let ghost prior = out@;
                proof {
                    assert(right == fragment_of_run(old, end as nat, old_end as nat, old.initialized));
                    assert(out.len() == 0 || logical_end(out@.last()) <= end);
                    if interval_valid(right, blocks) { extent_append_is_ordered(out@, right, blocks); }
                }
                match emit(&mut out, right, blocks, budget) { Ok(()) => {}, Err(e) => { return Err(e); } }
                proof {
                    emitted_fragment_mapping(before_output, parts, prior, out@, right);
                    parts = parts + seq![right];
                }
            }
        }
        proof {
            assert(parts =~= cut_run_fragments(old, first as nat, end as nat));
            cut_run_mapping(old, blocks, first as nat, end as nat);
            removing_a_range_distributes_over_extent_sequences(
                input@.take(i as int), seq![old], before_output, parts, first as nat, end as nat);
            assert(input@.take(i as int + 1) =~= input@.take(i as int) + seq![old]);
            removal_mapping_result_transfer(input@.take(i as int + 1), before_output + parts,
                out@, first as nat, end as nat);
            assert(out.len() == 0 || logical_end(out@.last()) <= logical_end(old));
            if i + 1 < input.len() {
                assert(logical_end(old) <= input@[i as int + 1].logical);
            }
        }
        i += 1;
    }
    proof { assert(input@.take(input.len() as int) =~= input@); }
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
    if runs.len() == 0 {
        assert(data_total(runs) == 0);
    } else {
        let prefix = runs.drop_last();
        assert(ordered_intervals(prefix, blocks)) by {
            assert forall|i: int| 0 <= i < prefix.len()
                implies #[trigger] interval_valid(prefix[i], blocks) by {
                assert(prefix[i] == runs[i]);
            }
            assert forall|i: int, j: int| #![trigger prefix[i], prefix[j]] 0 <= i < j < prefix.len()
                implies logical_end(prefix[i]) <= prefix[j].logical by {
                assert(prefix[i] == runs[i]);
                assert(prefix[j] == runs[j]);
            }
        }
        extent_lengths_fit_the_logical_address_space(prefix, blocks);
        assert(data_total(runs) == data_total(prefix) + runs.last().length as nat);
        if prefix.len() == 0 {
            assert(data_total(prefix) == 0);
        } else {
            assert(prefix.last() == runs[runs.len() as int - 2]);
            assert(runs.last() == runs[runs.len() as int - 1]);
            assert(logical_end(prefix.last()) <= runs.last().logical);
            assert(data_total(prefix) <= logical_end(prefix.last()));
        }
        assert(data_total(runs) <= logical_end(runs.last()));
        assert(interval_valid(runs.last(), blocks));
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
    if exists|i: int| 0 <= i < nodes.len() && #[trigger] nodes[i].block == address {
        nodes[choose|i: int| 0 <= i < nodes.len() && #[trigger] nodes[i].block == address].raw
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
#[verifier::opaque]
pub open spec fn child_link_bound_at(raw: Seq<u8>, children: Seq<NodeImageView>, i: int) -> bool {
        exists|j: int| 0 <= j < children.len()
            && #[trigger] children[j].block == extent_node::child(raw, i)
            && bytes::le16(children[j].raw, 6) + 1 == bytes::le16(raw, 6)
            && bytes::le16(children[j].raw, 2) > 0
            && extent_node::key(children[j].raw, 0) == extent_node::key(raw, i)
            && subtree_exclusive_end(children[j].raw, children, (bytes::le16(raw, 6) - 1) as nat)
                <= if i + 1 < bytes::le16(raw, 2) { extent_node::key(raw, i + 1) } else { LOGICAL_END as nat }
}
pub open spec fn child_links_bound(raw: Seq<u8>, children: Seq<NodeImageView>) -> bool {
    bytes::le16(raw, 6) > 0 ==> forall|i: int| #![trigger child_link_bound_at(raw, children, i)]
        0 <= i < bytes::le16(raw, 2) ==> child_link_bound_at(raw, children, i)
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
    &&& v.nodes.len() * (v.options.block_bytes as nat) <= v.options.byte_budget
    &&& v.unused == v.pool.subrange(v.nodes.len() as int, v.pool.len() as int)
    &&& v.root.len() == 60 && v.depth <= 5 && bytes::le16(v.root, 6) == v.depth
    &&& bytes::le16(v.root, 4) == 4 && bytes::le32(v.root, 8) == 0
    &&& extent_node::valid(extent_node::NodeView { raw: v.root, blocks: v.blocks, kind: extent_node::NodeKind::Inline })
    &&& (forall|i: int| #![trigger child_links_bound(v.nodes[i].raw, v.nodes.take(i))]
        0 <= i < v.nodes.len() ==> {
        let node = v.nodes[i];
        &&& node.block == v.pool[i] && node.raw.len() == v.options.block_bytes
        &&& extent_node::valid(extent_node::NodeView {
            raw: node.raw, blocks: v.blocks, kind: block_kind(v.options.checksum, v.inode_seed) })
        &&& bytes::le16(node.raw, 4) == (v.options.block_bytes as nat - 12) / 12
        &&& bytes::le16(node.raw, 2) > 0 && bytes::le16(node.raw, 6) < v.depth
        &&& bytes::le32(node.raw, 8) == 0
        &&& child_links_bound(node.raw, v.nodes.take(i))
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
{
    reveal(valid_plan);
    // Explicitly instantiate the deliberately selected per-node trigger.
    assert(child_links_bound(v.nodes[node].raw, v.nodes.take(node)));
    assert(v.nodes[node].block == v.pool[node]);
    assert(0 <= node < v.pool.len());
    assert(pool_admitted(v.runs, v.blocks, v.pool));
    assert(!(v.runs[run].physical <= v.pool[node] < physical_end(v.runs[run])));
}
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
    reveal(valid_plan);
    assert(child_links_bound(v.nodes[index].raw, v.nodes.take(index)));
    let raw = v.nodes[index].raw;
    let node = extent_node::NodeView {
        raw, blocks: v.blocks, kind: block_kind(v.options.checksum, v.inode_seed),
    };
    assert(extent_node::valid(node));
    assert(node.kind == extent_node::NodeKind::ChecksummedBlock(v.inode_seed));
    reveal(extent_node::valid);
    assert(extent_node::checksum_ok(node));
    let tail = 12 + bytes::le16(raw, 4) * 12;
    assert(raw.take(tail as int) =~= raw.subrange(0, tail as int));
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
        proof {
            use_type_invariant(self); reveal(valid_plan);
            assert(self.data_blocks <= LOGICAL_END);
            assert(self.metadata_blocks <= MAX_METADATA_NODES);
            assert(self.block_bytes <= 65536);
            assert(self.data_blocks as nat + (self.metadata_blocks as nat) <= 4295032831);
            assert(self.block_bytes as nat / 512 <= 128);
            assert((self.data_blocks as nat + self.metadata_blocks as nat)
                * (self.block_bytes as nat / 512) <= 549764202368) by(nonlinear_arith)
                requires self.data_blocks as nat + (self.metadata_blocks as nat) <= 4295032831,
                    self.block_bytes as nat / 512 <= 128;
        }
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
    let ghost before = raw@;
    let value = {
        let prefix = &raw[..tail];
        proof { assert(prefix@ =~= before.take(tail as int)); }
        crc::crc32c(seed, prefix)
    };
    assert(value == crc::fold(seed, before.take(tail as int)));
    let success = put32(raw, tail, value);
    proof {
        assert(success);
        assert forall|i: int| 0 <= i < tail
            implies #[trigger] raw@[i] == before[i] by {}
        assert(raw@.take(tail as int) =~= before.take(tail as int));
    }
    success
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


proof fn extent_link_address_split(address: u64)
    requires address < PHYSICAL_LIMIT,
    ensures ((address as u32) as nat)
        + 4294967296 * (((address >> 32) as u16) as nat) == address as nat,
        address >> 32 < 65536,
{
    assert((address as u32) as u64 == address % 4294967296) by(bit_vector);
    assert(address >> 32 == address / 4294967296) by(bit_vector);
    assert(address >> 32 < 65536u64) by(bit_vector)
        requires address < 281474976710656u64;
    assert(((address >> 32) as u16) as u64 == address >> 32);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(address as int, 4294967296);
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
    proof { extent_link_address_split(link.address); }
    put32(raw, at, link.first); put32(raw, at + 4, link.address as u32);
    put16(raw, at + 8, (link.address >> 32) as u16); put16(raw, at + 10, 0); true
}

// Private helpers for validate_pool. Existing helpers reused:
// occurrences_are_membership, fragment_occurrences_push,
// fragment_intervals_transfer_by_multiset, fragment_scalar_interval_bounds.
proof fn pool_multiset_membership<T>(before: Seq<T>, after: Seq<T>, value: T)
    requires same_multiset(before, after),
    ensures before.contains(value) == after.contains(value),
{
    occurrences_are_membership(before, value);
    occurrences_are_membership(after, value);
    assert(occurrences(before, value) == occurrences(after, value));
}

proof fn pool_repeated_indices_have_two_occurrences<T>(items: Seq<T>, a: int, b: int)
    requires 0 <= a < b < items.len(), items[a] == items[b],
    ensures occurrences(items, items[a]) >= 2,
    decreases items.len(),
{
    let prefix = items.drop_last();
    let value = items[a];
    assert(items =~= prefix.push(items.last()));
    assert(prefix[a] == value);
    if b < items.len() as int - 1 {
        assert(prefix[b] == value);
        pool_repeated_indices_have_two_occurrences(prefix, a, b);
        assert(occurrences(prefix, value) >= 2);
    } else {
        assert(b == items.len() as int - 1);
        assert(items.last() == value);
        assert(prefix.contains(value)) by {
            assert(0 <= a < prefix.len());
            assert(prefix[a] == value);
        }
        occurrences_are_membership(prefix, value);
        assert(occurrences(prefix, value) >= 1);
    }
    fragment_occurrences_push(prefix, items.last(), value);
}

proof fn pool_no_duplicates_bounds_occurrences<T>(items: Seq<T>, value: T)
    requires items.no_duplicates(),
    ensures occurrences(items, value) <= 1,
    decreases items.len(),
{
    if items.len() > 0 {
        let prefix = items.drop_last();
        assert(items =~= prefix.push(items.last()));
        assert(prefix.no_duplicates()) by {
            assert forall|i: int, j: int| #![trigger prefix[i], prefix[j]]
                0 <= i < prefix.len() && 0 <= j < prefix.len() && i != j
                implies prefix[i] != prefix[j] by {
                assert(items[i] != items[j]);
            }
        }
        pool_no_duplicates_bounds_occurrences(prefix, value);
        if items.last() == value {
            assert(!prefix.contains(value)) by {
                if prefix.contains(value) {
                    let at = choose|at: int| 0 <= at < prefix.len() && #[trigger] prefix[at] == value;
                    assert(prefix[at] == items[at]);
                    assert(at != items.len() as int - 1);
                    assert(items[at] != items[items.len() as int - 1]);
                    assert(items[items.len() as int - 1] == items.last());
                    assert(false);
                }
            }
            occurrences_are_membership(prefix, value);
            assert(occurrences(prefix, value) == 0);
        }
        fragment_occurrences_push(prefix, items.last(), value);
    }
}

proof fn pool_no_duplicates_transfers_by_multiset<T>(before: Seq<T>, after: Seq<T>)
    requires same_multiset(before, after), after.no_duplicates(),
    ensures before.no_duplicates(),
{
    assert forall|i: int, j: int| #![trigger before[i], before[j]]
        0 <= i < before.len() && 0 <= j < before.len() && i != j
        implies before[i] != before[j] by {
        if before[i] == before[j] {
            if i < j {
                pool_repeated_indices_have_two_occurrences(before, i, j);
            } else {
                pool_repeated_indices_have_two_occurrences(before, j, i);
                assert(before[j] == before[i]);
            }
            pool_no_duplicates_bounds_occurrences(after, before[i]);
            assert(occurrences(before, before[i]) >= 2);
            assert(occurrences(before, before[i]) == occurrences(after, before[i]));
            assert(false);
        }
    }
}

proof fn pool_sorted_strict_neighbors_have_no_duplicates(addresses: Seq<u64>)
    requires addresses_sorted(addresses),
        forall|i: int| #![trigger addresses[i]] 0 < i < addresses.len() ==> addresses[i - 1] < addresses[i],
    ensures addresses.no_duplicates(),
{
    assert forall|i: int, j: int| #![trigger addresses[i], addresses[j]] 0 <= i < j < addresses.len()
        implies addresses[i] < addresses[j] by {
        assert(0 < i + 1 < addresses.len());
        assert(addresses[i] < addresses[i + 1]);
        if i + 1 < j {
            assert(addresses[i + 1] <= addresses[j]);
        } else { assert(i + 1 == j); }
    }
    assert forall|i: int, j: int| #![trigger addresses[i], addresses[j]]
        0 <= i < addresses.len() && 0 <= j < addresses.len() && i != j
        implies addresses[i] != addresses[j] by {
        if i < j { assert(addresses[i] < addresses[j]); }
        else { assert(addresses[j] < addresses[i]); }
    }
}

proof fn pool_admission_transfers_by_multisets(
    runs: Seq<Run>, sorted_runs: Seq<Run>,
    pool: Seq<u64>, sorted_pool: Seq<u64>, blocks: u64,
)
    requires pool.len() <= MAX_METADATA_NODES,
        same_multiset(runs, sorted_runs), same_multiset(pool, sorted_pool),
        sorted_pool.no_duplicates(),
        forall|i: int| 0 <= i < sorted_pool.len() ==>
            0 < #[trigger] sorted_pool[i] < blocks && sorted_pool[i] < PHYSICAL_LIMIT,
        forall|i: int, j: int| 0 <= i < sorted_pool.len() && 0 <= j < sorted_runs.len() ==>
            !(sorted_runs[j].physical <= #[trigger] sorted_pool[i] < #[trigger] physical_end(sorted_runs[j])),
    ensures pool_admitted(runs, blocks, pool),
{
    pool_no_duplicates_transfers_by_multiset(pool, sorted_pool);
    assert forall|i: int| 0 <= i < pool.len() implies
        0 < #[trigger] pool[i] < blocks && pool[i] < PHYSICAL_LIMIT by {
        let address = pool[i];
        assert(pool.contains(address));
        pool_multiset_membership(pool, sorted_pool, address);
        assert(sorted_pool.contains(address));
        let at = choose|at: int| 0 <= at < sorted_pool.len() && #[trigger] sorted_pool[at] == address;
        assert(0 < sorted_pool[at] < blocks && sorted_pool[at] < PHYSICAL_LIMIT);
    }
    assert forall|i: int, j: int| 0 <= i < pool.len() && 0 <= j < runs.len() implies
        !(runs[j].physical <= #[trigger] pool[i] < #[trigger] physical_end(runs[j])) by {
        let address = pool[i];
        let run = runs[j];
        assert(pool.contains(address));
        assert(runs.contains(run));
        pool_multiset_membership(pool, sorted_pool, address);
        pool_multiset_membership(runs, sorted_runs, run);
        assert(sorted_pool.contains(address));
        assert(sorted_runs.contains(run));
        let a = choose|a: int| 0 <= a < sorted_pool.len() && #[trigger] sorted_pool[a] == address;
        let d = choose|d: int| 0 <= d < sorted_runs.len() && #[trigger] sorted_runs[d] == run;
        assert(!(sorted_runs[d].physical <= sorted_pool[a] < physical_end(sorted_runs[d])));
    }
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
    proof {
        fragment_intervals_transfer_by_multiset(set.runs@, data@, set.blocks);
        assert forall|j: int| 0 <= j < data.len() implies
            #[trigger] physical_end(data@[j]) <= u64::MAX by {
            assert(interval_valid(data@[j], set.blocks));
            fragment_scalar_interval_bounds(data@[j], set.blocks);
        }
    }
    let mut i = 0usize; let mut d = 0usize;
    while i < addresses.len()
        invariant
            set.wf(), wire_runs(set.runs@, set.blocks),
            node_budget <= MAX_METADATA_NODES, pool.len() <= MAX_METADATA_NODES,
            i <= addresses.len(), d <= data.len(),
            addresses.len() == pool.len() <= MAX_METADATA_NODES,
            data.len() == set.runs.len() <= MAX_EXTENTS,
            addresses_sorted(addresses@), physically_sorted(data@),
            same_multiset(pool@, addresses@), same_multiset(set.runs@, data@),
            forall|j: int| 0 <= j < data.len() ==> #[trigger] interval_valid(data@[j], set.blocks),
            forall|j: int| #![trigger data@[j]]
                0 <= j < data.len() ==> physical_end(data@[j]) <= u64::MAX,
            forall|a: int| 0 <= a < i ==>
                0 < #[trigger] addresses@[a] < set.blocks && addresses@[a] < PHYSICAL_LIMIT,
            forall|a: int| #![trigger addresses@[a]] 0 < a < i ==> addresses@[a - 1] < addresses@[a],
            forall|a: int, j: int| 0 <= a < i && 0 <= j < data.len() ==>
                !(data@[j].physical <= #[trigger] addresses@[a] < #[trigger] physical_end(data@[j])),
            i == 0 ==> d == 0,
            i > 0 ==> (forall|j: int| 0 <= j < d ==>
                #[trigger] physical_end(data@[j]) <= addresses@[i as int - 1]),
        decreases addresses.len() - i,
    {
        let address = addresses[i];
        if address == 0 || address >= set.blocks { return Err(Error::MetadataPool); }
        if address >= PHYSICAL_LIMIT { return Err(Error::AddressTooWide); }
        if i > 0 && addresses[i - 1] == address { return Err(Error::MetadataAlias); }
        proof {
            if i > 0 {
                assert(addresses@[i as int - 1] <= address);
                assert(addresses@[i as int - 1] < address);
            }
            assert forall|j: int| 0 <= j < d implies
                #[trigger] physical_end(data@[j]) <= address by {
                if i > 0 {
                    assert(physical_end(data@[j]) <= addresses@[i as int - 1]);
                    assert(addresses@[i as int - 1] <= address);
                } else { assert(d == 0); }
            }
        }
        let ghost scan_start = d;
        while d < data.len() && data[d].physical + (data[d].length as u64) <= address
            invariant
                set.wf(), wire_runs(set.runs@, set.blocks),
                node_budget <= MAX_METADATA_NODES, pool.len() <= MAX_METADATA_NODES,
                i < addresses.len(), address == addresses@[i as int],
                0 < address < set.blocks, address < PHYSICAL_LIMIT,
                scan_start <= d <= data.len(),
                addresses.len() == pool.len() <= MAX_METADATA_NODES,
                data.len() == set.runs.len() <= MAX_EXTENTS,
                addresses_sorted(addresses@), physically_sorted(data@),
                same_multiset(pool@, addresses@), same_multiset(set.runs@, data@),
                forall|j: int| 0 <= j < data.len() ==> #[trigger] interval_valid(data@[j], set.blocks),
                forall|j: int| #![trigger data@[j]]
                0 <= j < data.len() ==> physical_end(data@[j]) <= u64::MAX,
                forall|a: int| 0 <= a < i ==>
                    0 < #[trigger] addresses@[a] < set.blocks && addresses@[a] < PHYSICAL_LIMIT,
                forall|a: int| #![trigger addresses@[a]] 0 < a < i ==> addresses@[a - 1] < addresses@[a],
                i > 0 ==> addresses@[i as int - 1] < address,
                forall|a: int, j: int| 0 <= a < i && 0 <= j < data.len() ==>
                    !(data@[j].physical <= #[trigger] addresses@[a] < #[trigger] physical_end(data@[j])),
                forall|j: int| 0 <= j < d ==> #[trigger] physical_end(data@[j]) <= address,
            decreases data.len() - d,
        {
            let ghost previous_d = d;
            proof {
                assert(physical_end(data@[d as int]) <= address);
                assert forall|j: int| 0 <= j <= d implies
                    #[trigger] physical_end(data@[j]) <= address by {
                    if j < d { assert(physical_end(data@[j]) <= address); }
                    else { assert(j == d); }
                }
            }
            d += 1;
            proof {
                assert forall|j: int| 0 <= j < d implies
                    #[trigger] physical_end(data@[j]) <= address by {
                    assert(j <= previous_d);
                }
            }
        }
        if d < data.len() && data[d].physical <= address { return Err(Error::MetadataAlias); }
        proof {
            assert forall|j: int| 0 <= j < data.len() implies
                !(data@[j].physical <= address < #[trigger] physical_end(data@[j])) by {
                if j < d {
                    assert(physical_end(data@[j]) <= address);
                } else {
                    assert(d < data.len());
                    assert(address < data@[d as int].physical);
                    if d < j { assert(data@[d as int].physical <= data@[j].physical); }
                    else { assert(j == d); }
                }
            }
            assert forall|a: int| 0 <= a <= i implies
                0 < #[trigger] addresses@[a] < set.blocks && addresses@[a] < PHYSICAL_LIMIT by {
                if a < i {
                    assert(0 < addresses@[a] < set.blocks && addresses@[a] < PHYSICAL_LIMIT);
                } else { assert(a == i); assert(addresses@[a] == address); }
            }
            assert forall|a: int| #![trigger addresses@[a]] 0 < a <= i implies addresses@[a - 1] < addresses@[a] by {
                if a < i { assert(addresses@[a - 1] < addresses@[a]); }
                else { assert(a == i); assert(addresses@[a - 1] < address); }
            }
            assert forall|a: int, j: int| 0 <= a <= i && 0 <= j < data.len() implies
                !(data@[j].physical <= #[trigger] addresses@[a] < #[trigger] physical_end(data@[j])) by {
                if a < i {
                    assert(!(data@[j].physical <= addresses@[a] < physical_end(data@[j])));
                } else { assert(a == i); assert(addresses@[a] == address); }
            }
        }
        i += 1;
        proof {
            assert(addresses@[i as int - 1] == address);
            assert forall|j: int| 0 <= j < d implies
                #[trigger] physical_end(data@[j]) <= addresses@[i as int - 1] by {
                assert(physical_end(data@[j]) <= address);
            }
        }
    }
    proof {
        assert(i == addresses.len());
        pool_sorted_strict_neighbors_have_no_duplicates(addresses@);
        pool_admission_transfers_by_multisets(set.runs@, data@, pool@, addresses@, set.blocks);
        assert(set.view().runs == set.runs@);
        assert(set.view().blocks == set.blocks);
    }
    Ok(())
}

fn emit_node(nodes: &mut Vec<NodeImage>, pool: &[u64], raw: Vec<u8>, first: u32,
    depth: u16, options: &BuildOptions, blocks: u64, seed: u32) -> (r: Result<Link, Error>)
    requires old(nodes).len() <= options.node_budget <= MAX_METADATA_NODES,
        crate::block_size::accepted(options.block_bytes as nat),
    ensures match r {
        Ok(link) => old(nodes).len() < pool.len() && final(nodes).len() <= pool.len()
            && final(nodes).len() == old(nodes).len() + 1
            && node_views(final(nodes)@).take(old(nodes).len() as int) == node_views(old(nodes)@)
            && link.first == first && link.depth == depth && link.address == pool[old(nodes).len() as int]
            && final(nodes)@[old(nodes).len() as int].block == link.address
            && final(nodes)@[old(nodes).len() as int].raw@ == raw@
            && extent_node::valid(extent_node::NodeView { raw: raw@, blocks, kind: block_kind(options.metadata_checksum, seed) })
            && final(nodes).len() <= options.node_budget
            && final(nodes).len() as nat * (options.block_bytes as nat) <= options.byte_budget,
        Err(_) => node_views(final(nodes)@) == node_views(old(nodes)@),
    },
{
    if nodes.len() >= pool.len() || nodes.len() >= options.node_budget { return Err(Error::Budget); }
    proof {
        assert(options.block_bytes <= 65536);
        assert(nodes.len() as nat * (options.block_bytes as nat) <= 4294967296) by(nonlinear_arith)
            requires nodes.len() <= 65536, options.block_bytes <= 65536;
    }
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
    let ghost before = nodes@;
    let ghost raw_view = raw@;
    nodes.push(NodeImage { block: address, raw });
    proof {
        assert(node_views(nodes@).len() == node_views(before).len() + 1);
        assert forall|i: int| #![trigger node_views(nodes@)[i]] 0 <= i < before.len()
            implies node_views(nodes@)[i] == node_views(before)[i] by {
            assert(nodes@[i] == before[i]);
        }
        assert(node_views(nodes@).take(before.len() as int) =~= node_views(before));
        assert(nodes@[before.len() as int].raw@ == raw_view);
        assert(nodes.len() as nat == before.len() + 1);
        assert(nodes.len() as nat * options.block_bytes as nat
            == before.len() * options.block_bytes as nat + options.block_bytes as nat)
            by(nonlinear_arith)
                requires nodes.len() as nat == before.len() + 1;
    }
    Ok(Link { first, address, depth })
}

proof fn supported_block_capacity(bytes: u32)
    requires crate::block_size::accepted(bytes as nat),
    ensures
        1024 <= bytes <= 65536,
        1 < (bytes as nat - 12) / 12 <= 5460,
        16 + ((bytes as nat - 12) / 12) * 12 <= bytes,
{
    // accepted is an exact seven-way finite geometry definition.
    assert(bytes == 1024 || bytes == 2048 || bytes == 4096 || bytes == 8192
        || bytes == 16384 || bytes == 32768 || bytes == 65536);
}

// Proposed additive PRIVATE ghost code inside extent_edit.rs's verus! block.
// This is a constructive review candidate, not a checked proof artifact.
// It changes no executable data representation or functional body.
//
// Witness intervals refer to source RUN INDICES, not logical block addresses.
// Consequently holes between consecutive source runs are preserved exactly.
struct ExtentNodeWitness {
    first: int,
    end: int,
    children: Seq<int>,
}
spec fn distinct_node_addresses(nodes: Seq<NodeImageView>) -> bool {
    forall|i: int, j: int| 0 <= i < nodes.len() && 0 <= j < nodes.len()
        && #[trigger] nodes[i].block == #[trigger] nodes[j].block ==> i == j
}
#[verifier::opaque]
spec fn witnessed_node(
    nodes: Seq<NodeImageView>, witness: Seq<ExtentNodeWitness>, runs: Seq<Run>, i: int,
) -> bool {
    let n = nodes[i];
    let w = witness[i];
    let count = bytes::le16(n.raw, 2);
    let depth = bytes::le16(n.raw, 6);
    &&& 0 <= w.first < w.end <= runs.len()
    &&& count > 0
    &&& extent_node::key(n.raw, 0) == runs[w.first].logical
    &&& if depth == 0 {
        w.children.len() == 0
            && decoded_leaf(n.raw) == runs.subrange(w.first, w.end)
    } else {
        &&& w.children.len() == count
        &&& w.first == witness[w.children[0]].first
        &&& w.end == witness[w.children[count as int - 1]].end
        &&& forall|k: int| #![trigger witness[i].children[k]] 0 <= k < count ==> {
            let c = w.children[k];
            &&& 0 <= c < i
            &&& extent_node::child(n.raw, k) == nodes[c].block
            &&& bytes::le16(nodes[c].raw, 6) + 1 == depth
            &&& extent_node::key(n.raw, k) == runs[witness[c].first].logical
            &&& k + 1 < count ==> witness[c].end == witness[w.children[k + 1]].first
        }
    }
}
spec fn witnessed_forest(
    nodes: Seq<NodeImageView>, witness: Seq<ExtentNodeWitness>, runs: Seq<Run>,
) -> bool {
    witness.len() == nodes.len() && forall|i:int| 0<=i<nodes.len()
        ==> #[trigger] witnessed_node(nodes,witness,runs,i)
}

// The arbitrary choose in stored_node_raw is harmless only AFTER establishing
// uniqueness in the actual lookup prefix. Never assume it picks our index.
proof fn witnessed_lookup(
    nodes: Seq<NodeImageView>, index: int, limit: int,
)
    requires distinct_node_addresses(nodes), 0 <= index < limit <= nodes.len(),
    ensures stored_node_raw(nodes.take(limit), nodes[index].block) == nodes[index].raw,
{
    let prefix = nodes.take(limit);
    assert(prefix[index] == nodes[index]);
    assert(0 <= index < prefix.len());
    assert(exists|j: int| 0 <= j < prefix.len() && #[trigger] prefix[j].block == nodes[index].block) by {
        assert(0 <= index < prefix.len() && prefix[index].block == nodes[index].block);
    }
    let chosen = choose|j: int| 0 <= j < prefix.len() && #[trigger] prefix[j].block == nodes[index].block;
    assert(prefix[chosen] == nodes[chosen]);
    assert(nodes[chosen].block == nodes[index].block);
    assert(chosen == index);
}

// The context remains nodes.take(limit) throughout recursion. Using take(index)
// in the recursive call would change stored_node_raw's search context and does
// not establish the caller's subtree_exclusive_end term.
proof fn witnessed_subtree_end(
    nodes: Seq<NodeImageView>, witness: Seq<ExtentNodeWitness>, runs: Seq<Run>,
    index: int, limit: int,
)
    requires
        witnessed_forest(nodes, witness, runs), distinct_node_addresses(nodes),
        0 <= index < limit <= nodes.len(),
    ensures subtree_exclusive_end(nodes[index].raw, nodes.take(limit),
        bytes::le16(nodes[index].raw, 6)) == logical_end(runs[witness[index].end - 1]),
    decreases index,
{
    reveal(witnessed_node);
    assert(witnessed_node(nodes,witness,runs,index));
    let raw = nodes[index].raw;
    let w = witness[index];
    let count = bytes::le16(raw, 2);
    let depth = bytes::le16(raw, 6);
    assert(0 <= w.first < w.end <= runs.len());
    assert(count > 0);
    reveal_with_fuel(subtree_exclusive_end, 1);
    if depth == 0 {
        assert(decoded_leaf(raw) == runs.subrange(w.first, w.end));
        assert(decoded_leaf(raw).len() == count);
        assert(count == w.end - w.first);
        assert(decoded_leaf(raw)[count as int - 1] == runs[w.end - 1]);
    } else {
        let k = count as int - 1;
        let c = w.children[k];
        assert(0 <= c < index);
        assert(witness[c].end == w.end);
        assert(extent_node::child(raw, k) == nodes[c].block);
        assert(bytes::le16(nodes[c].raw, 6) + 1 == depth);
        witnessed_lookup(nodes, c, limit);
        witnessed_subtree_end(nodes, witness, runs, c, limit);
        assert((depth - 1) as nat == bytes::le16(nodes[c].raw, 6));
    }
}

// index == limit is intentional: a node's children live in the prefix preceding
// that node. It handles an inline root represented by a final ghost-only node.


proof fn witnessed_child_edge_coordinates(
    nodes: Seq<NodeImageView>, witness: Seq<ExtentNodeWitness>, runs: Seq<Run>,
    blocks: u64, index: int, k: int,
) -> (c: int)
    requires witnessed_forest(nodes, witness, runs), ordered_intervals(runs, blocks),
        0 <= index < nodes.len(), bytes::le16(nodes[index].raw, 6) > 0,
        0 <= k < bytes::le16(nodes[index].raw, 2),
    ensures c == witness[index].children[k], 0 <= c < index,
        extent_node::child(nodes[index].raw, k) == nodes[c].block,
        bytes::le16(nodes[c].raw, 6) + 1 == bytes::le16(nodes[index].raw, 6),
        bytes::le16(nodes[c].raw, 2) > 0,
        extent_node::key(nodes[c].raw, 0) == extent_node::key(nodes[index].raw, k),
        logical_end(runs[witness[c].end - 1])
            <= if k + 1 < bytes::le16(nodes[index].raw, 2) {
                extent_node::key(nodes[index].raw, k + 1)
            } else { LOGICAL_END as nat },
{
    reveal(witnessed_node);
    assert(witnessed_node(nodes, witness, runs, index));
    let raw = nodes[index].raw;
    let w = witness[index];
    let c = w.children[k];
    assert(0 <= c < index);
    assert(witnessed_node(nodes, witness, runs, c));
    assert(bytes::le16(nodes[c].raw, 2) > 0);
    assert(extent_node::key(nodes[c].raw, 0) == runs[witness[c].first].logical);
    assert(extent_node::key(raw, k) == runs[witness[c].first].logical);
    if k + 1 < bytes::le16(raw, 2) {
        let next = w.children[k + 1];
        assert(0 <= next < index);
        assert(witnessed_node(nodes, witness, runs, next));
        assert(witness[c].end == witness[next].first);
        assert(0 <= witness[c].end - 1 < witness[next].first < runs.len());
        assert(logical_end(runs[witness[c].end - 1]) <= runs[witness[next].first].logical);
        assert(extent_node::key(raw, k + 1) == runs[witness[next].first].logical);
    } else {
        assert(interval_valid(runs[witness[c].end - 1], blocks));
        assert(logical_end(runs[witness[c].end - 1]) <= LOGICAL_END);
    }
    c
}

proof fn witnessed_child_link_record(
    nodes: Seq<NodeImageView>, witness: Seq<ExtentNodeWitness>, runs: Seq<Run>,
    blocks: u64, index: int, limit: int, k: int,
)
    requires witnessed_forest(nodes, witness, runs), distinct_node_addresses(nodes),
        ordered_intervals(runs, blocks), 0 <= index <= limit <= nodes.len(),
        index < nodes.len(), bytes::le16(nodes[index].raw, 6) > 0,
        0 <= k < bytes::le16(nodes[index].raw, 2),
    ensures child_link_bound_at(nodes[index].raw, nodes.take(limit), k),
{
    reveal(child_link_bound_at);
    let c = witnessed_child_edge_coordinates(nodes, witness, runs, blocks, index, k);
    let raw = nodes[index].raw;
    let depth = bytes::le16(raw, 6);
    let count = bytes::le16(raw, 2);
    assert(0 <= c < limit && nodes.take(limit)[c] == nodes[c]);
    witnessed_subtree_end(nodes, witness, runs, c, limit);
    assert(bytes::le16(nodes[c].raw, 6) == (depth - 1) as nat);
    assert(exists|j: int| 0 <= j < nodes.take(limit).len()
        && #[trigger] nodes.take(limit)[j].block == extent_node::child(raw, k)
        && bytes::le16(nodes.take(limit)[j].raw, 6) + 1 == depth
        && bytes::le16(nodes.take(limit)[j].raw, 2) > 0
        && extent_node::key(nodes.take(limit)[j].raw, 0) == extent_node::key(raw, k)
        && subtree_exclusive_end(nodes.take(limit)[j].raw, nodes.take(limit), (depth - 1) as nat)
            <= if k + 1 < count { extent_node::key(raw, k + 1) } else { LOGICAL_END as nat }) by {
        assert(0 <= c < nodes.take(limit).len());
        assert(nodes.take(limit)[c].block == extent_node::child(raw, k));
        assert(subtree_exclusive_end(nodes.take(limit)[c].raw, nodes.take(limit), (depth - 1) as nat)
            == logical_end(runs[witness[c].end - 1]));
    }
}


proof fn child_links_bound_intro(raw: Seq<u8>, children: Seq<NodeImageView>)
    requires bytes::le16(raw, 6) > 0 ==> forall|i: int| #![trigger child_link_bound_at(raw, children, i)]
        0 <= i < bytes::le16(raw, 2) ==> child_link_bound_at(raw, children, i),
    ensures child_links_bound(raw, children),
{
    reveal(child_links_bound);
}

proof fn witnessed_child_links(
    nodes: Seq<NodeImageView>, witness: Seq<ExtentNodeWitness>, runs: Seq<Run>,
    blocks: u64, index: int, limit: int,
)
    requires
        witnessed_forest(nodes, witness, runs), distinct_node_addresses(nodes),
        ordered_intervals(runs, blocks), 0 <= index <= limit <= nodes.len(),
        index < nodes.len(),
    ensures child_links_bound(nodes[index].raw, nodes.take(limit)),
{
    assert(witnessed_node(nodes,witness,runs,index));
    let raw = nodes[index].raw;
    let w = witness[index];
    let depth = bytes::le16(raw, 6);
    let count = bytes::le16(raw, 2);
    if depth > 0 {
        assert forall|k: int| #![trigger child_link_bound_at(raw, nodes.take(limit), k)]
            0 <= k < count implies child_link_bound_at(raw, nodes.take(limit), k)
        by {
            witnessed_child_link_record(nodes, witness, runs, blocks, index, limit, k);
        }
    }
    child_links_bound_intro(raw, nodes.take(limit));
}

proof fn emitted_projection_push(nodes: Seq<NodeImageView>, node: NodeImageView)
    ensures emitted_leaf_projection(nodes.push(node))
        == emitted_leaf_projection(nodes)
            + if bytes::le16(node.raw, 6) == 0 { decoded_leaf(node.raw) } else { Seq::empty() },
        emitted_references(nodes.push(node)) == emitted_references(nodes) + references(node.raw),
{
    reveal_with_fuel(emitted_leaf_projection, 1);
    reveal_with_fuel(emitted_references, 1);
    assert(nodes.push(node).drop_last() =~= nodes);
    assert(nodes.push(node).last() == node);
}

// At every emission frontier holds the unparented node ADDRESSES in order.
// This is a conservation law; it proves no disconnected emitted node, duplicate
// incoming edge or silently lost child can pass the final root construction.
spec fn frontier_balance(nodes: Seq<NodeImageView>, frontier: Seq<u64>) -> bool {
    forall|i: int| #![trigger occurrences(emitted_references(nodes), nodes[i].block)] 0 <= i < nodes.len() ==>
        occurrences(emitted_references(nodes), nodes[i].block)
            + occurrences(frontier, nodes[i].block) == 1
}

proof fn zero_occurrences_without_member<T>(items: Seq<T>, value: T)
    requires !items.contains(value),
    ensures occurrences(items, value) == 0,
{
    occurrences_are_membership(items, value);
}

// One step of the same conservation law handles BOTH leaf emission (consumed
// is empty) and index emission (consumed is exactly the encoded child group).
// prefix+consumed+suffix is the mixed frontier during a level rebuild:
// already-created parents followed by not-yet-consumed old children.
proof fn frontier_replace(
    nodes: Seq<NodeImageView>, prefix: Seq<u64>, consumed: Seq<u64>, suffix: Seq<u64>,
    node: NodeImageView,
)
    requires
        frontier_balance(nodes, prefix + consumed + suffix),
        references(node.raw) == consumed,
        forall|i: int| 0 <= i < nodes.len() ==> #[trigger] nodes[i].block != node.block,
        !emitted_references(nodes).contains(node.block),
        !(prefix + consumed + suffix).contains(node.block),
    ensures frontier_balance(nodes.push(node), prefix + seq![node.block] + suffix),
{
    emitted_projection_push(nodes, node);
    assert forall|i: int| #![trigger occurrences(emitted_references(nodes.push(node)), nodes.push(node)[i].block)] 0 <= i < nodes.push(node).len()
        implies occurrences(emitted_references(nodes.push(node)), nodes.push(node)[i].block)
            + occurrences(prefix + seq![node.block] + suffix, nodes.push(node)[i].block) == 1
    by {
        let value = nodes.push(node)[i].block;
        fragment_occurrences_push(Seq::<u64>::empty(), node.block, value);
        assert(Seq::<u64>::empty().push(node.block) =~= seq![node.block]);
        assert(occurrences(Seq::<u64>::empty(), value) == 0);
        occurrences_concatenate(emitted_references(nodes), consumed, value);
        occurrences_concatenate(prefix, consumed, value);
        occurrences_concatenate(prefix + consumed, suffix, value);
        occurrences_concatenate(prefix, seq![node.block], value);
        occurrences_concatenate(prefix + seq![node.block], suffix, value);
        if i < nodes.len() {
            assert(nodes.push(node)[i] == nodes[i]);
            assert(value != node.block);
            assert(occurrences(seq![node.block], value) == 0);
            assert(occurrences(emitted_references(nodes), value)
                + occurrences(prefix + consumed + suffix, value) == 1);
        } else {
            assert(i == nodes.len());
            assert(value == node.block);
            zero_occurrences_without_member(emitted_references(nodes), value);
            zero_occurrences_without_member(prefix + consumed + suffix, value);
            vstd::seq_lib::lemma_seq_concat_contains_all_elements(prefix + consumed, suffix, value);
            vstd::seq_lib::lemma_seq_concat_contains_all_elements(prefix, consumed, value);
            assert(!prefix.contains(value) && !consumed.contains(value) && !suffix.contains(value));
            zero_occurrences_without_member(prefix, value);
            zero_occurrences_without_member(consumed, value);
            zero_occurrences_without_member(suffix, value);
            assert(occurrences(seq![value], value) == 1);
        }
    }
}




proof fn equal_sequence_prefix_entry<T>(before: Seq<T>, after: Seq<T>, length: int, index: int)
    requires 0 <= index < length <= before.len(), length <= after.len(),
        before.take(length) == after.take(length),
    ensures before[index] == after[index],
{
    assert(before.take(length)[index] == before[index]);
    assert(after.take(length)[index] == after[index]);
    assert(before.take(length)[index] == after.take(length)[index]);
}

proof fn witnessed_node_prefix_extensional(nodes: Seq<NodeImageView>, witness: Seq<ExtentNodeWitness>,
    prefix: Seq<NodeImageView>, prior: Seq<ExtentNodeWitness>, runs: Seq<Run>, i: int)
    requires witnessed_node(nodes, witness, runs, i),
        0 <= i < nodes.len(), i < witness.len(), i < prefix.len(), i < prior.len(),
        nodes.take(i + 1) == prefix.take(i + 1), witness.take(i + 1) == prior.take(i + 1),
    ensures witnessed_node(prefix, prior, runs, i),
{
    reveal(witnessed_node);
    let w = witness[i];
    let raw = nodes[i].raw;
    let count = bytes::le16(raw, 2);
    equal_sequence_prefix_entry(nodes, prefix, i + 1, i);
    equal_sequence_prefix_entry(witness, prior, i + 1, i);
    assert(prefix[i] == nodes[i] && prior[i] == witness[i]);
    if bytes::le16(raw, 6) > 0 {
        assert(0 <= w.children[0] < i);
        assert(0 <= w.children[count as int - 1] < i);
        equal_sequence_prefix_entry(witness, prior, i + 1, w.children[0]);
        equal_sequence_prefix_entry(witness, prior, i + 1, w.children[count as int - 1]);
        assert(prior[w.children[0]] == witness[w.children[0]]);
        assert(prior[w.children[count as int - 1]] == witness[w.children[count as int - 1]]);
        assert forall|k: int| #![trigger witness[i].children[k]] 0 <= k < count implies {
            let c = w.children[k];
            &&& 0 <= c < i
            &&& extent_node::child(raw, k) == prefix[c].block
            &&& bytes::le16(prefix[c].raw, 6) + 1 == bytes::le16(raw, 6)
            &&& extent_node::key(raw, k) == runs[prior[c].first].logical
            &&& k + 1 < count ==> prior[c].end == prior[w.children[k + 1]].first
        } by {
            let c = w.children[k];
            assert(0 <= c < i < prefix.len());
            equal_sequence_prefix_entry(nodes, prefix, i + 1, c);
            equal_sequence_prefix_entry(witness, prior, i + 1, c);
            assert(prefix[c] == nodes[c] && prior[c] == witness[c]);
            if k + 1 < count {
                assert(0 <= w.children[k + 1] < i < prefix.len());
                equal_sequence_prefix_entry(witness, prior, i + 1, w.children[k + 1]);
                assert(prior[w.children[k + 1]] == witness[w.children[k + 1]]);
            }
        }
    }
}
proof fn witnessed_node_survives_prefix(
    nodes: Seq<NodeImageView>, witness: Seq<ExtentNodeWitness>, runs: Seq<Run>, i: int, limit: int)
    requires witnessed_forest(nodes, witness, runs), 0 <= i < limit <= nodes.len(),
    ensures witnessed_node(nodes.take(limit), witness.take(limit), runs, i),
{
    assert(witness.len() == nodes.len());
    assert(witnessed_node(nodes, witness, runs, i));
    assert(nodes.take(limit).take(i + 1) =~= nodes.take(i + 1));
    assert(witness.take(limit).take(i + 1) =~= witness.take(i + 1));
    witnessed_node_prefix_extensional(nodes, witness, nodes.take(limit), witness.take(limit), runs, i);
}

proof fn witnessed_forest_prefix(
    nodes: Seq<NodeImageView>, witness: Seq<ExtentNodeWitness>, runs: Seq<Run>, limit: int)
    requires witnessed_forest(nodes, witness, runs), 0 <= limit <= nodes.len(),
    ensures witnessed_forest(nodes.take(limit), witness.take(limit), runs),
{
    assert(witness.len() == nodes.len());
    assert forall|i: int| #![trigger witnessed_node(nodes.take(limit), witness.take(limit), runs, i)]
        0 <= i < nodes.take(limit).len()
        implies witnessed_node(nodes.take(limit), witness.take(limit), runs, i) by {
        witnessed_node_survives_prefix(nodes, witness, runs, i, limit);
    }
}

proof fn forest_references_resolve(
    nodes: Seq<NodeImageView>, witness: Seq<ExtentNodeWitness>, runs: Seq<Run>, address: u64,
)
    requires witnessed_forest(nodes, witness, runs),
        forall|i: int| 0 <= i < nodes.len() ==> #[trigger] nodes[i].block != address,
    ensures !emitted_references(nodes).contains(address),
    decreases nodes.len(),
{
    reveal(witnessed_node);
    if nodes.len() > 0 {
        let n = nodes.len() as int - 1;
        let prefix = nodes.drop_last();
        let prior = witness.drop_last();
        witnessed_forest_prefix(nodes, witness, runs, n);
        assert(prefix =~= nodes.take(n));
        assert(prior =~= witness.take(n));
        assert forall|i: int| #![trigger prefix[i].block] 0 <= i < prefix.len()
            implies prefix[i].block != address by {
            assert(prefix[i] == nodes[i]);
        }
        forest_references_resolve(prefix, prior, runs, address);
        assert(witnessed_node(nodes,witness,runs,n));
        let raw = nodes[n].raw;
        assert(!references(raw).contains(address)) by {
            if references(raw).contains(address) {
                let k = choose|k: int| 0 <= k < references(raw).len() && #[trigger] references(raw)[k] == address;
                assert(bytes::le16(raw, 6) > 0);
                let c = witness[n].children[k];
                assert(0 <= c < n);
                assert(extent_node::child(raw, k) == nodes[c].block);
                assert(references(raw)[k] == nodes[c].block);
                assert(nodes[c].block != address);
                assert(false);
            }
        }
        reveal_with_fuel(emitted_references, 1);
        vstd::seq_lib::lemma_seq_concat_contains_all_elements(emitted_references(prefix), references(raw), address);
        assert(!(emitted_references(prefix) + references(raw)).contains(address));
    } else {
        reveal_with_fuel(emitted_references, 1);
        assert(emitted_references(nodes) =~= Seq::<u64>::empty());
        vstd::seq_lib::lemma_seq_empty_contains_nothing(address);
        assert(!Seq::<u64>::empty().contains(address));
    }
}

// Derive the canonical/nonalias portion without changing any valid_plan clause.
// The other private preconditions are the scalar/local properties retained from
// parse_* and emit_node and the completed emitted-leaf prefix invariant.
// Root is appended ONLY to this ghost forest, with reserved ghost address 0.
proof fn close_external_forest(v: PlanView, witness: Seq<ExtentNodeWitness>, frontier: Seq<u64>,
    root_witness: ExtentNodeWitness)
    requires
        1 <= v.depth <= 5,
        valid_set(SetView { runs: v.runs, blocks: v.blocks, budget: v.extent_budget }),
        crate::block_size::accepted(v.options.block_bytes as nat), v.options.inode > 0,
        v.options.node_budget <= MAX_METADATA_NODES,
        v.inode_seed == crc::fold(crc::fold(v.options.filesystem_seed,
            bytes::encoded_le(v.options.inode)), bytes::encoded_le(v.options.generation)),
        pool_admitted(v.runs, v.blocks, v.pool),
        v.nodes.len() <= v.pool.len(), v.nodes.len() <= v.options.node_budget,
        v.nodes.len() * (v.options.block_bytes as nat) <= v.options.byte_budget,
        v.unused == v.pool.subrange(v.nodes.len() as int, v.pool.len() as int),
        v.root.len() == 60, bytes::le16(v.root, 6) == v.depth,
        bytes::le16(v.root, 4) == 4, bytes::le32(v.root, 8) == 0,
        extent_node::valid(extent_node::NodeView {
            raw: v.root, blocks: v.blocks, kind: extent_node::NodeKind::Inline }),
        forall|i: int| #![trigger v.nodes[i]] 0 <= i < v.nodes.len() ==> {
            let node = v.nodes[i];
            &&& node.block == v.pool[i] && node.raw.len() == v.options.block_bytes
            &&& extent_node::valid(extent_node::NodeView {
                raw: node.raw, blocks: v.blocks, kind: block_kind(v.options.checksum, v.inode_seed) })
            &&& bytes::le16(node.raw, 4) == (v.options.block_bytes as nat - 12) / 12
            &&& bytes::le16(node.raw, 2) > 0 && bytes::le16(node.raw, 6) < v.depth
            &&& bytes::le32(node.raw, 8) == 0
        },
        emitted_leaf_projection(v.nodes) == v.runs,
        v.data_blocks as nat == data_total(v.runs) <= LOGICAL_END,
        v.metadata_blocks as nat == v.nodes.len(),
        witnessed_forest(v.nodes.push(NodeImageView { block: 0, raw: v.root }),
            witness.push(root_witness), v.runs),
        frontier_balance(v.nodes, frontier), references(v.root) == frontier,
    ensures valid_plan(v),
{
    reveal(valid_set);
    let all = v.nodes.push(NodeImageView { block: 0, raw: v.root });
    let all_witness = witness.push(root_witness);
    assert(distinct_node_addresses(all)) by {
        assert forall|i: int, j: int| 0 <= i < all.len() && 0 <= j < all.len()
            && #[trigger] all[i].block == #[trigger] all[j].block implies i == j by {
            if i < v.nodes.len() && j < v.nodes.len() {
                assert(all[i].block == v.pool[i]);
                assert(all[j].block == v.pool[j]);
                assert(v.pool.no_duplicates());
            } else if i < v.nodes.len() {
                assert(all[j].block == 0);
                assert(0 < v.pool[i]);
            } else if j < v.nodes.len() {
                assert(all[i].block == 0);
                assert(0 < v.pool[j]);
            }
        }
    }
    assert forall|i: int| #![trigger child_links_bound(v.nodes[i].raw, v.nodes.take(i))]
        0 <= i < v.nodes.len() implies {
            let node = v.nodes[i];
            &&& node.block == v.pool[i] && node.raw.len() == v.options.block_bytes
            &&& extent_node::valid(extent_node::NodeView {
                raw: node.raw, blocks: v.blocks, kind: block_kind(v.options.checksum, v.inode_seed) })
            &&& bytes::le16(node.raw, 4) == (v.options.block_bytes as nat - 12) / 12
            &&& bytes::le16(node.raw, 2) > 0 && bytes::le16(node.raw, 6) < v.depth
            &&& bytes::le32(node.raw, 8) == 0
            &&& child_links_bound(node.raw, v.nodes.take(i))
        } by {
            witnessed_child_links(all, all_witness, v.runs, v.blocks, i, i);
            assert(all[i] == v.nodes[i]);
            assert(all.take(i) =~= v.nodes.take(i));
        }
    witnessed_child_links(all, all_witness, v.runs, v.blocks,
        v.nodes.len() as int, v.nodes.len() as int);
    assert(all.take(v.nodes.len() as int) =~= v.nodes);
    assert(child_links_bound(v.root, v.nodes));
    assert forall|i: int| 0 <= i < v.nodes.len()
        implies #[trigger] occurrences(references(v.root) + emitted_references(v.nodes), v.nodes[i].block) == 1
    by {
        occurrences_concatenate(references(v.root), emitted_references(v.nodes), v.nodes[i].block);
        assert(occurrences(emitted_references(v.nodes), v.nodes[i].block)
            + occurrences(frontier, v.nodes[i].block) == 1);
    }
    reveal(valid_plan);
}

// Additional PRIVATE proof helpers for canonical-forest-proposal.rs.
// Constructive proposals only, not compiled or verified.

proof fn byte_frame_preserves_word_reads(before: Seq<u8>, after: Seq<u8>,
    first: int, end: int)
    requires before.len()==after.len(), 0<=first<=end<=before.len(),
        forall|i:int| 0<=i<before.len() && !(first<=i<end)
            ==> #[trigger] after[i]==before[i],
    ensures
        forall|word:int| 0<=word && word+2<=before.len()
            && (word+2<=first || word>=end)
            ==> #[trigger] bytes::le16(after,word)==bytes::le16(before,word),
        forall|word:int| 0<=word && word+4<=before.len()
            && (word+4<=first || word>=end)
            ==> #[trigger] bytes::le32(after,word)==bytes::le32(before,word),
{
    assert forall|word:int| 0<=word && word+2<=before.len()
        && (word+2<=first || word>=end)
        implies #[trigger] bytes::le16(after,word)==bytes::le16(before,word) by {
        assert(after[word]==before[word]);
        assert(after[word+1]==before[word+1]);
    }
    assert forall|word:int| 0<=word && word+4<=before.len()
        && (word+4<=first || word>=end)
        implies #[trigger] bytes::le32(after,word)==bytes::le32(before,word) by {
        assert(after[word]==before[word]);
        assert(after[word+1]==before[word+1]);
        assert(after[word+2]==before[word+2]);
        assert(after[word+3]==before[word+3]);
    }
}

proof fn encoded_run_is_decoded_run(raw: Seq<u8>, record: int, run: Run, blocks: u64)
    requires 0<=record<bytes::le16(raw,2),
        crate::extent_span::represents(crate::extent_span::SpanView {
            logical:run.logical,length:run.length,physical:run.physical,
            initialized:run.initialized,blocks,
        },raw,12+12*record),
    ensures decoded_leaf(raw)[record]==run,
{
    let word=bytes::le16(raw,12+12*record+4);
    assert(run.length as nat == crate::extent::length(word));
    assert(run.initialized == (word<=32768));
    assert(decoded_leaf(raw)[record].logical==run.logical);
    assert(decoded_leaf(raw)[record].length==run.length);
    assert(decoded_leaf(raw)[record].physical==run.physical);
    assert(decoded_leaf(raw)[record].initialized==run.initialized);
}

// OLD witnessed nodes retain their contracts across a push. Every child index
// is <i, so neither new node nor new witness is read when checking an old node.
proof fn witnessed_node_survives_push(
    nodes: Seq<NodeImageView>, witness: Seq<ExtentNodeWitness>, runs: Seq<Run>,
    node: NodeImageView, next: ExtentNodeWitness, i: int,
)
    requires witnessed_forest(nodes,witness,runs), 0<=i<nodes.len(),
    ensures witnessed_node(nodes.push(node),witness.push(next),runs,i),
{
    reveal(witnessed_node);
    assert(witnessed_node(nodes,witness,runs,i));
    assert(nodes.push(node)[i]==nodes[i]);
    assert(witness.push(next)[i]==witness[i]);
    let w=witness[i];
    let count=bytes::le16(nodes[i].raw,2);
    if bytes::le16(nodes[i].raw,6)>0 {
        assert forall|k:int| #![trigger witness[i].children[k]] 0<=k<count implies {
            let c=w.children[k];
            &&& 0<=c<i
            &&& extent_node::child(nodes.push(node)[i].raw,k)==nodes.push(node)[c].block
            &&& bytes::le16(nodes.push(node)[c].raw,6)+1==bytes::le16(nodes.push(node)[i].raw,6)
            &&& extent_node::key(nodes.push(node)[i].raw,k)==runs[witness.push(next)[c].first].logical
            &&& k+1<count ==> witness.push(next)[c].end==witness.push(next)[w.children[k+1]].first
        } by {
            let c=w.children[k];
            assert(0<=c<i<nodes.len());
            assert(nodes.push(node)[c]==nodes[c]);
            assert(witness.push(next)[c]==witness[c]);
            if k+1<count {
                let next_child=w.children[k+1];
                assert(0<=next_child<i);
                assert(witness.push(next)[next_child]==witness[next_child]);
            }
        }
        assert(0<=w.children[0]<i);
        assert(0<=w.children[count as int-1]<i);
        assert(witness.push(next)[w.children[0]]==witness[w.children[0]]);
        assert(witness.push(next)[w.children[count as int-1]]==witness[w.children[count as int-1]]);
    }
}

proof fn forest_append_leaf(
    nodes: Seq<NodeImageView>, witness: Seq<ExtentNodeWitness>, runs: Seq<Run>,
    node: NodeImageView, first: int, end: int,
)
    requires witnessed_forest(nodes,witness,runs), 0<=first<end<=runs.len(),
        bytes::le16(node.raw,6)==0, bytes::le16(node.raw,2)>0,
        decoded_leaf(node.raw)==runs.subrange(first,end),
        extent_node::key(node.raw,0)==runs[first].logical,
    ensures witnessed_forest(nodes.push(node),
        witness.push(ExtentNodeWitness {first,end,children:Seq::empty()}),runs),
{
    reveal(witnessed_node);
    let next=ExtentNodeWitness {first,end,children:Seq::empty()};
    assert forall|i:int| 0<=i<nodes.push(node).len()
        implies #[trigger] witnessed_node(nodes.push(node),witness.push(next),runs,i) by {
        if i<nodes.len() {
            witnessed_node_survives_push(nodes,witness,runs,node,next,i);
        } else {
            assert(i==nodes.len());
            assert(nodes.push(node)[i]==node);
            assert(witness.push(next)[i]==next);
        }
    }
}

proof fn forest_append_index(
    nodes: Seq<NodeImageView>, witness: Seq<ExtentNodeWitness>, runs: Seq<Run>,
    node: NodeImageView, children: Seq<int>,
)
    requires
        witnessed_forest(nodes,witness,runs),
        bytes::le16(node.raw,6)>0, bytes::le16(node.raw,2)==children.len(), children.len()>0,
        forall|k:int| #![trigger children[k]] 0<=k<children.len() ==> {
            let c=children[k];
            &&& 0<=c<nodes.len()
            &&& extent_node::child(node.raw,k)==nodes[c].block
            &&& bytes::le16(nodes[c].raw,6)+1==bytes::le16(node.raw,6)
            &&& extent_node::key(node.raw,k)==runs[witness[c].first].logical
            &&& k+1<children.len() ==> witness[c].end==witness[children[k+1]].first
        },
    ensures witnessed_forest(nodes.push(node),witness.push(ExtentNodeWitness {
        first:witness[children[0]].first,
        end:witness[children[children.len() as int-1]].end,
        children,
    }),runs),
{
    reveal(witnessed_node);
    let first=witness[children[0]].first;
    let end=witness[children[children.len() as int-1]].end;
    let next=ExtentNodeWitness {first,end,children};
    assert(witnessed_node(nodes,witness,runs,children[0]));
    assert(witnessed_node(nodes,witness,runs,children[children.len() as int-1]));
    // Instantiate the forest's explicit witnessed_node trigger for ALL children.
    assert forall|j:int| #![trigger children[j]] 0<=j<children.len() implies
        0<=children[j]<witness.len()
        && witness[children[j]].first<witness[children[j]].end
        && (j+1<children.len() ==> witness[children[j]].end==witness[children[j+1]].first)
    by {
        assert(witnessed_node(nodes,witness,runs,children[j]));
    }
    // Contiguous nonempty child ranges imply first<end even with many children.
    assert forall|k:int| #![trigger children[k]] 0<=k<children.len()
        implies first<=witness[children[k]].first<witness[children[k]].end<=end by {
        // The inductive range lemma below provides arbitrary-index bounds.
        contiguous_child_ranges(witness,children,k);
    }
    assert forall|i:int| 0<=i<nodes.push(node).len()
        implies #[trigger] witnessed_node(nodes.push(node),witness.push(next),runs,i) by {
        if i<nodes.len() {
            witnessed_node_survives_push(nodes,witness,runs,node,next,i);
        } else {
            assert(i==nodes.len());
            assert(nodes.push(node)[i]==node);
            assert(witness.push(next)[i]==next);
            assert forall|k:int| #![trigger children[k]] 0<=k<children.len() implies {
                let c=children[k];
                &&& 0<=c<i
                &&& extent_node::child(node.raw,k)==nodes.push(node)[c].block
                &&& bytes::le16(nodes.push(node)[c].raw,6)+1==bytes::le16(node.raw,6)
                &&& extent_node::key(node.raw,k)==runs[witness.push(next)[c].first].logical
                &&& k+1<children.len() ==> witness.push(next)[c].end==witness.push(next)[children[k+1]].first
            } by {
                let c=children[k];
                assert(nodes.push(node)[c]==nodes[c]);
                assert(witness.push(next)[c]==witness[c]);
                if k+1<children.len() {
                    assert(witness.push(next)[children[k+1]]==witness[children[k+1]]);
                }
            }
        }
    }
}

proof fn contiguous_child_ranges(witness: Seq<ExtentNodeWitness>, children: Seq<int>, k: int)
    requires
        0<=k<children.len(),
        forall|j:int| #![trigger children[j]] 0<=j<children.len() ==>
            0<=children[j]<witness.len()
            && witness[children[j]].first<witness[children[j]].end
            && (j+1<children.len() ==> witness[children[j]].end==witness[children[j+1]].first),
    ensures witness[children[0]].first<=witness[children[k]].first
        && witness[children[k]].end<=witness[children[children.len() as int-1]].end,
{
    child_ranges_first_bound(witness,children,k);
    child_ranges_last_bound(witness,children,k);
}
proof fn child_ranges_first_bound(witness: Seq<ExtentNodeWitness>, children: Seq<int>, k: int)
    requires
        0<=k<children.len(),
        forall|j:int| #![trigger children[j]] 0<=j<children.len() ==>
            0<=children[j]<witness.len()
            && witness[children[j]].first<witness[children[j]].end
            && (j+1<children.len() ==> witness[children[j]].end==witness[children[j+1]].first),
    ensures witness[children[0]].first<=witness[children[k]].first,
    decreases k,
{
    if k>0 {
        child_ranges_first_bound(witness,children,k-1);
        assert(witness[children[k-1]].first<witness[children[k-1]].end);
        assert(witness[children[k-1]].end==witness[children[k]].first);
    }
}
proof fn child_ranges_last_bound(witness: Seq<ExtentNodeWitness>, children: Seq<int>, k: int)
    requires
        0<=k<children.len(),
        forall|j:int| #![trigger children[j]] 0<=j<children.len() ==>
            0<=children[j]<witness.len()
            && witness[children[j]].first<witness[children[j]].end
            && (j+1<children.len() ==> witness[children[j]].end==witness[children[j+1]].first),
    ensures witness[children[k]].end<=witness[children[children.len() as int-1]].end,
    decreases children.len()-k,
{
    if k+1<children.len() {
        child_ranges_last_bound(witness,children,k+1);
        assert(witness[children[k]].end==witness[children[k+1]].first);
        assert(witness[children[k+1]].first<witness[children[k+1]].end);
    }
}

spec fn link_addresses(links: Seq<Link>) -> Seq<u64> {
    Seq::new(links.len(), |i: int| links[i].address)
}
spec fn frontier_description(
    nodes: Seq<NodeImageView>, witness: Seq<ExtentNodeWitness>, runs: Seq<Run>,
    links: Seq<Link>, indices: Seq<int>, level: nat, first: int, end: int,
) -> bool {
    &&& links.len() == indices.len()
    &&& if links.len() == 0 { first == end } else {
        &&& witness[indices[0]].first == first
        &&& witness[indices[indices.len() as int - 1]].end == end
    }
    &&& forall|k: int| #![trigger indices[k]] 0 <= k < links.len() ==> {
        let node = indices[k];
        &&& 0 <= node < nodes.len()
        &&& links[k].address == nodes[node].block
        &&& links[k].depth == level && bytes::le16(nodes[node].raw, 6) == level
        &&& links[k].first == runs[witness[node].first].logical
        &&& k + 1 < links.len() ==> witness[node].end == witness[indices[k + 1]].first
    }
}
spec fn node_local_facts(nodes: Seq<NodeImageView>, pool: Seq<u64>,
    options: OptionsView, blocks: u64, seed: u32, upper_depth: nat) -> bool {
    &&& nodes.len() <= pool.len() && nodes.len() <= options.node_budget
    &&& nodes.len() * (options.block_bytes as nat) <= options.byte_budget
    &&& forall|i: int| #![trigger nodes[i]] 0 <= i < nodes.len() ==> {
        let node = nodes[i];
        &&& node.block == pool[i] && node.raw.len() == options.block_bytes
        &&& extent_node::valid(extent_node::NodeView {
            raw: node.raw, blocks, kind: block_kind(options.checksum, seed) })
        &&& bytes::le16(node.raw, 4) == (options.block_bytes as nat - 12) / 12
        &&& bytes::le16(node.raw, 2) > 0 && bytes::le16(node.raw, 6) <= upper_depth
        &&& bytes::le32(node.raw, 8) == 0
    }
}



spec fn extent_builder_context(source: SetView, options: OptionsView,
    pool: Seq<u64>, maximum: nat, seed: u32) -> bool {
    &&& valid_set(source)
    &&& crate::block_size::accepted(options.block_bytes as nat) && options.inode > 0
    &&& options.node_budget <= MAX_METADATA_NODES
    &&& pool_admitted(source.runs, source.blocks, pool)
    &&& 1 < maximum <= 5460 && maximum == (options.block_bytes as nat - 12) / 12
    &&& 16 + maximum * 12 <= options.block_bytes
    &&& seed == crc::fold(crc::fold(options.filesystem_seed,
        bytes::encoded_le(options.inode)), bytes::encoded_le(options.generation))
}
#[verifier::opaque]
spec fn stored_address(nodes: Seq<NodeImageView>, address: u64) -> bool {
    exists|i: int| 0 <= i < nodes.len() && #[trigger] nodes[i].block == address
}
spec fn stored_frontier(nodes: Seq<NodeImageView>, frontier: Seq<u64>) -> bool {
    forall|k: int| #![trigger frontier[k]] 0 <= k < frontier.len() ==> stored_address(nodes, frontier[k])
}
proof fn stored_address_intro(nodes: Seq<NodeImageView>, address: u64, index: int)
    requires 0 <= index < nodes.len(), nodes[index].block == address,
    ensures stored_address(nodes, address),
{
    reveal(stored_address);
    assert(exists|i: int| 0 <= i < nodes.len() && #[trigger] nodes[i].block == address) by {
        assert(0 <= index < nodes.len() && nodes[index].block == address);
    }
}
proof fn stored_address_index(nodes: Seq<NodeImageView>, address: u64) -> (index: int)
    requires stored_address(nodes, address),
    ensures 0 <= index < nodes.len(), nodes[index].block == address,
{
    reveal(stored_address);
    choose|i: int| 0 <= i < nodes.len() && #[trigger] nodes[i].block == address
}

proof fn stored_frontier_excludes_fresh(nodes: Seq<NodeImageView>, frontier: Seq<u64>, address: u64)
    requires stored_frontier(nodes, frontier),
        forall|i: int| 0 <= i < nodes.len() ==> #[trigger] nodes[i].block != address,
    ensures !frontier.contains(address),
{
    if frontier.contains(address) {
        let k = choose|k: int| 0 <= k < frontier.len() && #[trigger] frontier[k] == address;
        let i = stored_address_index(nodes, frontier[k]);
        assert(nodes[i].block != address);
        assert(false);
    }
}
proof fn local_node_facts_push(nodes: Seq<NodeImageView>, pool: Seq<u64>, options: OptionsView,
    blocks: u64, seed: u32, depth: nat, node: NodeImageView)
    requires node_local_facts(nodes, pool, options, blocks, seed, depth),
        nodes.len() < pool.len(), nodes.len() < options.node_budget,
        (nodes.len() + 1) * (options.block_bytes as nat) <= options.byte_budget,
        node.block == pool[nodes.len() as int], node.raw.len() == options.block_bytes,
        extent_node::valid(extent_node::NodeView {
            raw: node.raw, blocks, kind: block_kind(options.checksum, seed) }),
        bytes::le16(node.raw, 4) == (options.block_bytes as nat - 12) / 12,
        bytes::le16(node.raw, 2) > 0 && bytes::le16(node.raw, 6) <= depth,
        bytes::le32(node.raw, 8) == 0,
    ensures node_local_facts(nodes.push(node), pool, options, blocks, seed, depth),
{
    assert forall|i: int| #![trigger nodes.push(node)[i]] 0 <= i < nodes.push(node).len() implies {
        let n = nodes.push(node)[i];
        &&& n.block == pool[i] && n.raw.len() == options.block_bytes
        &&& extent_node::valid(extent_node::NodeView {
            raw: n.raw, blocks, kind: block_kind(options.checksum, seed) })
        &&& bytes::le16(n.raw, 4) == (options.block_bytes as nat - 12) / 12
        &&& bytes::le16(n.raw, 2) > 0 && bytes::le16(n.raw, 6) <= depth
        &&& bytes::le32(n.raw, 8) == 0
    } by {
        if i < nodes.len() { assert(nodes.push(node)[i] == nodes[i]); }
        else { assert(i == nodes.len() && nodes.push(node)[i] == node); }
    }
}
proof fn record_write_preserves_other_records(before: Seq<u8>, after: Seq<u8>, record: int)
    requires before.len() == after.len(), 0 <= record,
        12 + 12 * record + 12 <= before.len(),
        forall|i: int| 0 <= i < before.len() && !(12 + 12 * record <= i < 24 + 12 * record)
            ==> #[trigger] after[i] == before[i],
    ensures bytes::le16(after, 0) == bytes::le16(before, 0),
        bytes::le16(after, 2) == bytes::le16(before, 2),
        bytes::le16(after, 4) == bytes::le16(before, 4),
        bytes::le16(after, 6) == bytes::le16(before, 6),
        bytes::le32(after, 8) == bytes::le32(before, 8),
        forall|j: int| 0 <= j < record && j < bytes::le16(before, 2)
            ==> #[trigger] decoded_leaf(after)[j] == decoded_leaf(before)[j],
        forall|j: int| 0 <= j < record ==> #[trigger] extent_node::key(after, j) == extent_node::key(before, j)
            && extent_node::child(after, j) == extent_node::child(before, j),
{
    reveal(extent_node::key);
    byte_frame_preserves_word_reads(before, after, 12 + 12 * record, 24 + 12 * record);
    assert forall|j: int| 0 <= j < record && j < bytes::le16(before, 2)
        implies #[trigger] decoded_leaf(after)[j] == decoded_leaf(before)[j] by {
        let at = 12 + 12 * j;
        assert(bytes::le32(after, at) == bytes::le32(before, at));
        assert(bytes::le16(after, at + 4) == bytes::le16(before, at + 4));
        assert(bytes::le16(after, at + 6) == bytes::le16(before, at + 6));
        assert(bytes::le32(after, at + 8) == bytes::le32(before, at + 8));
    }
    assert forall|j: int| 0 <= j < record
        implies #[trigger] extent_node::key(after, j) == extent_node::key(before, j)
            && extent_node::child(after, j) == extent_node::child(before, j) by {
        let at = 12 + 12 * j;
        assert(bytes::le32(after, at) == bytes::le32(before, at));
        assert(bytes::le32(after, at + 4) == bytes::le32(before, at + 4));
        assert(bytes::le16(after, at + 8) == bytes::le16(before, at + 8));
    }
}
proof fn prefix_frame_preserves_extent_description(before: Seq<u8>, after: Seq<u8>, through: int)
    requires before.len() == after.len(), 12 <= through <= before.len(),
        12 + 12 * bytes::le16(before, 2) <= through,
        forall|i: int| 0 <= i < through ==> #[trigger] after[i] == before[i],
    ensures bytes::le16(after, 0) == bytes::le16(before, 0),
        bytes::le16(after, 2) == bytes::le16(before, 2),
        bytes::le16(after, 4) == bytes::le16(before, 4),
        bytes::le16(after, 6) == bytes::le16(before, 6),
        bytes::le32(after, 8) == bytes::le32(before, 8),
        decoded_leaf(after) == decoded_leaf(before), references(after) == references(before),
        forall|j: int| #![trigger extent_node::key(after, j)] 0 <= j < bytes::le16(before, 2) ==>
            extent_node::key(after, j) == extent_node::key(before, j)
                && extent_node::child(after, j) == extent_node::child(before, j),
{
    reveal(extent_node::key);
    byte_frame_preserves_word_reads(before, after, through, before.len() as int);
    assert forall|j: int| 0 <= j < decoded_leaf(before).len()
        implies #[trigger] decoded_leaf(after)[j] == decoded_leaf(before)[j] by {
        let at = 12 + 12 * j;
        assert(bytes::le32(after, at) == bytes::le32(before, at));
        assert(bytes::le16(after, at + 4) == bytes::le16(before, at + 4));
        assert(bytes::le16(after, at + 6) == bytes::le16(before, at + 6));
        assert(bytes::le32(after, at + 8) == bytes::le32(before, at + 8));
    }
    assert(decoded_leaf(after) =~= decoded_leaf(before));
    assert forall|j: int| 0 <= j < references(before).len()
        implies #[trigger] references(after)[j] == references(before)[j] by {
        let at = 12 + 12 * j;
        assert(bytes::le32(after, at + 4) == bytes::le32(before, at + 4));
        assert(bytes::le16(after, at + 8) == bytes::le16(before, at + 8));
    }
    assert(references(after) =~= references(before));
    assert forall|j: int| #![trigger extent_node::key(after, j)] 0 <= j < bytes::le16(before, 2)
        implies extent_node::key(after, j) == extent_node::key(before, j)
            && extent_node::child(after, j) == extent_node::child(before, j) by {
        let at = 12 + 12 * j;
        assert(bytes::le32(after, at) == bytes::le32(before, at));
        assert(bytes::le32(after, at + 4) == bytes::le32(before, at + 4));
        assert(bytes::le16(after, at + 8) == bytes::le16(before, at + 8));
    }

}


spec fn complete_frontier_state(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    source: SetView, pool: Seq<u64>, opts: OptionsView, seed: u32,
    links: Seq<Link>, indices: Seq<int>, level: nat, end: int) -> bool {
    &&& witnessed_forest(nodes, forest, source.runs)
    &&& node_local_facts(nodes, pool, opts, source.blocks, seed, level)
    &&& frontier_description(nodes, forest, source.runs, links, indices, level, 0, end)
    &&& frontier_balance(nodes, link_addresses(links))
    &&& stored_frontier(nodes, link_addresses(links))
    &&& emitted_leaf_projection(nodes) == source.runs.take(end)
    &&& (end == 0) == (links.len() == 0)
}
#[verifier::opaque]
spec fn mixed_frontier_state(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    source: SetView, pool: Seq<u64>, opts: OptionsView, seed: u32,
    links: Seq<Link>, indices: Seq<int>, next: Seq<Link>, next_indices: Seq<int>,
    level: nat, start: int) -> bool {
    let mixed = link_addresses(next) + link_addresses(links).subrange(start, links.len() as int);
    &&& 0 <= start <= links.len()
    &&& witnessed_forest(nodes, forest, source.runs)
    &&& node_local_facts(nodes, pool, opts, source.blocks, seed, level + 1)
    &&& frontier_description(nodes, forest, source.runs, links, indices,
        level, 0, source.runs.len() as int)
    &&& frontier_description(nodes, forest, source.runs, next, next_indices,
        level + 1, 0, if start == 0 { 0 } else { forest[indices[start - 1]].end })
    &&& frontier_balance(nodes, mixed) && stored_frontier(nodes, mixed)
    &&& emitted_leaf_projection(nodes) == source.runs
    &&& (start == 0) == (next.len() == 0)
}
spec fn completed_extent_tree(root: Seq<u8>, nodes: Seq<NodeImageView>,
    forest: Seq<ExtentNodeWitness>, source: SetView, pool: Seq<u64>, opts: OptionsView,
    seed: u32, depth: u16, frontier: Seq<u64>, root_witness: ExtentNodeWitness) -> bool {
    &&& root.len() == 60 && depth <= 5 && bytes::le16(root, 6) == depth
    &&& bytes::le16(root, 4) == 4 && bytes::le32(root, 8) == 0
    &&& node_local_facts(nodes, pool, opts, source.blocks, seed,
        if depth == 0 { 0nat } else { (depth - 1) as nat })
    &&& if depth == 0 {
        nodes.len() == 0 && forest.len() == 0 && decoded_leaf(root) == source.runs
    } else {
        &&& witnessed_forest(nodes.push(NodeImageView { block: 0, raw: root }),
            forest.push(root_witness), source.runs)
        &&& frontier_balance(nodes, frontier) && references(root) == frontier
        &&& emitted_leaf_projection(nodes) == source.runs
    }
}



spec fn appended_leaf_witness(first: int, end: int) -> ExtentNodeWitness {
    ExtentNodeWitness { first, end, children: Seq::empty() }
}
spec fn appended_index_witness(forest: Seq<ExtentNodeWitness>, children: Seq<int>) -> ExtentNodeWitness {
    ExtentNodeWitness { first: forest[children[0]].first,
        end: forest[children[children.len() as int - 1]].end, children }
}
spec fn appendable_extent_node(node: NodeImageView, nodes: Seq<NodeImageView>,
    pool: Seq<u64>, opts: OptionsView, blocks: u64, seed: u32, depth: nat) -> bool {
    &&& nodes.len() < pool.len() && nodes.len() < opts.node_budget
    &&& (nodes.len() + 1) * opts.block_bytes as nat <= opts.byte_budget
    &&& node.block == pool[nodes.len() as int] && node.raw.len() == opts.block_bytes
    &&& extent_node::valid(extent_node::NodeView {
        raw: node.raw, blocks, kind: block_kind(opts.checksum, seed) })
    &&& bytes::le16(node.raw, 4) == (opts.block_bytes as nat - 12) / 12
    &&& bytes::le16(node.raw, 2) > 0 && bytes::le16(node.raw, 6) == depth
    &&& bytes::le32(node.raw, 8) == 0
}
proof fn appended_node_is_fresh(nodes: Seq<NodeImageView>, pool: Seq<u64>, opts: OptionsView,
    blocks: u64, seed: u32, depth: nat, node: NodeImageView)
    requires node_local_facts(nodes, pool, opts, blocks, seed, depth),
        pool.no_duplicates(), nodes.len() < pool.len(), node.block == pool[nodes.len() as int],
    ensures forall|j: int| #![trigger nodes[j].block] 0 <= j < nodes.len() ==> nodes[j].block != node.block,
{
    assert forall|j: int| #![trigger nodes[j].block] 0 <= j < nodes.len()
        implies nodes[j].block != node.block by {
        assert(nodes[j].block == pool[j]);
        assert(0 <= j < nodes.len() < pool.len());
        assert(pool[j] != pool[nodes.len() as int]);
    }
}

proof fn stored_frontier_intro(nodes: Seq<NodeImageView>, frontier: Seq<u64>)
    requires forall|k: int| #![trigger frontier[k]] 0 <= k < frontier.len()
        ==> stored_address(nodes, frontier[k]),
    ensures stored_frontier(nodes, frontier),
{
    reveal(stored_frontier);
}
proof fn stored_frontier_replacement(nodes: Seq<NodeImageView>,
    prefix: Seq<u64>, consumed: Seq<u64>, suffix: Seq<u64>, node: NodeImageView)
    requires stored_frontier(nodes, prefix + consumed + suffix),
    ensures stored_frontier(nodes.push(node), prefix + seq![node.block] + suffix),
{
    let before = prefix + consumed + suffix;
    let after = prefix + seq![node.block] + suffix;
    assert forall|k: int| #![trigger after[k]] 0 <= k < after.len()
        implies stored_address(nodes.push(node), after[k]) by {
        if k == prefix.len() {
            assert(after[k] == node.block);
            assert(nodes.push(node)[nodes.len() as int].block == after[k]);
            stored_address_intro(nodes.push(node), after[k], nodes.len() as int);
        } else {
            let old_index = if k < prefix.len() { k }
                else { prefix.len() as int + consumed.len() as int + k - prefix.len() as int - 1 };
            assert(0 <= old_index < before.len());
            assert(before[old_index] == after[k]);
            let j = stored_address_index(nodes, before[old_index]);
            assert(nodes.push(node)[j] == nodes[j]);
            stored_address_intro(nodes.push(node), after[k], j);
        }
    }
    stored_frontier_intro(nodes.push(node), after);
}

proof fn append_leaf_frontier(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    source: SetView, pool: Seq<u64>, opts: OptionsView, maximum: nat, seed: u32,
    links: Seq<Link>, indices: Seq<int>, first: int, end: int, node: NodeImageView, link: Link)
    requires extent_builder_context(source, opts, pool, maximum, seed),
        complete_frontier_state(nodes, forest, source, pool, opts, seed, links, indices, 0, first),
        0 <= first < end <= source.runs.len(),
        appendable_extent_node(node, nodes, pool, opts, source.blocks, seed, 0),
        decoded_leaf(node.raw) == source.runs.subrange(first, end),
        extent_node::key(node.raw, 0) == source.runs[first].logical,
        link.address == node.block && link.first == source.runs[first].logical && link.depth == 0,
    ensures complete_frontier_state(nodes.push(node), forest.push(appended_leaf_witness(first, end)),
        source, pool, opts, seed, links.push(link), indices.push(nodes.len() as int), 0, end),
{
    appended_node_is_fresh(nodes, pool, opts, source.blocks, seed, 0, node);
    forest_references_resolve(nodes, forest, source.runs, node.block);
    stored_frontier_excludes_fresh(nodes, link_addresses(links), node.block);
    assert(references(node.raw) =~= Seq::<u64>::empty());
    frontier_replace(nodes, link_addresses(links), Seq::empty(), Seq::empty(), node);
    stored_frontier_replacement(nodes, link_addresses(links), Seq::empty(), Seq::empty(), node);
    forest_append_leaf(nodes, forest, source.runs, node, first, end);
    local_node_facts_push(nodes, pool, opts, source.blocks, seed, 0, node);
    emitted_projection_push(nodes, node);
    assert(source.runs.take(first) + source.runs.subrange(first, end) =~= source.runs.take(end));
    let next_forest = forest.push(appended_leaf_witness(first, end));
    let next_indices = indices.push(nodes.len() as int);
    assert(link_addresses(links.push(link)) =~= link_addresses(links).push(node.block));
    assert(frontier_description(nodes.push(node), next_forest, source.runs,
        links.push(link), next_indices, 0, 0, end)) by {
        assert forall|k: int| #![trigger next_indices[k]] 0 <= k < links.push(link).len() implies {
            let index = next_indices[k];
            &&& 0 <= index < nodes.push(node).len()
            &&& links.push(link)[k].address == nodes.push(node)[index].block
            &&& links.push(link)[k].depth == 0 && bytes::le16(nodes.push(node)[index].raw, 6) == 0
            &&& links.push(link)[k].first == source.runs[next_forest[index].first].logical
            &&& k + 1 < links.push(link).len() ==> next_forest[index].end == next_forest[next_indices[k + 1]].first
        } by {
            if k < links.len() {
                assert(next_indices[k] == indices[k]);
                assert(nodes.push(node)[indices[k]] == nodes[indices[k]]);
                assert(next_forest[indices[k]] == forest[indices[k]]);
                if k + 1 == links.len() {
                    assert(forest[indices[k]].end == first);
                } else if k + 1 < links.len() {
                    assert(next_forest[indices[k + 1]] == forest[indices[k + 1]]);
                }
            } else {
                assert(k == links.len() && next_indices[k] == nodes.len());
                assert(next_forest[nodes.len() as int] == appended_leaf_witness(first, end));
            }
        }
    }
}


#[verifier::opaque]
spec fn index_record_matches(raw: Seq<u8>, links: Seq<Link>, first: int, record: int) -> bool {
    extent_node::child(raw, record) == links[first + record].address
        && extent_node::key(raw, record) == links[first + record].first
}
proof fn index_record_matches_intro(raw: Seq<u8>, links: Seq<Link>, first: int, record: int)
    requires 0 <= first + record < links.len(),
        extent_node::child(raw, record) == links[first + record].address,
        extent_node::key(raw, record) == links[first + record].first,
    ensures index_record_matches(raw, links, first, record),
{
    reveal(index_record_matches);
}
proof fn index_record_matches_fields(raw: Seq<u8>, links: Seq<Link>, first: int, record: int)
    requires index_record_matches(raw, links, first, record), 0 <= first + record < links.len(),
    ensures extent_node::child(raw, record) == links[first + record].address,
        extent_node::key(raw, record) == links[first + record].first,
{
    reveal(index_record_matches);
}
proof fn index_record_matches_frame(before: Seq<u8>, after: Seq<u8>,
    links: Seq<Link>, first: int, record: int)
    requires index_record_matches(before, links, first, record), 0 <= first + record < links.len(),
        extent_node::child(after, record) == extent_node::child(before, record),
        extent_node::key(after, record) == extent_node::key(before, record),
    ensures index_record_matches(after, links, first, record),
{
    index_record_matches_fields(before, links, first, record);
    index_record_matches_intro(after, links, first, record);
}
proof fn matched_index_records_describe_references(raw: Seq<u8>, links: Seq<Link>, first: int, end: int)
    requires 0 <= first <= end <= links.len(), bytes::le16(raw, 6) > 0,
        bytes::le16(raw, 2) == end - first,
        forall|k: int| #![trigger index_record_matches(raw, links, first, k)] 0 <= k < end - first ==>
            index_record_matches(raw, links, first, k),
    ensures references(raw) == link_addresses(links).subrange(first, end),
{
    assert forall|k: int| #![trigger references(raw)[k]] 0 <= k < references(raw).len()
        implies references(raw)[k] == link_addresses(links).subrange(first, end)[k] by {
        index_record_matches_fields(raw, links, first, k);
    }
    assert(references(raw) =~= link_addresses(links).subrange(first, end));
}


#[verifier::opaque]
spec fn parent_child_certificate_at(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    runs: Seq<Run>, node: NodeImageView, children: Seq<int>, k: int) -> bool {
    let c = children[k];
    &&& 0 <= c < nodes.len()
    &&& extent_node::child(node.raw, k) == nodes[c].block
    &&& bytes::le16(nodes[c].raw, 6) + 1 == bytes::le16(node.raw, 6)
    &&& extent_node::key(node.raw, k) == runs[forest[c].first].logical
    &&& k + 1 < children.len() ==> forest[c].end == forest[children[k + 1]].first
}
proof fn parent_child_certificate_fields(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    runs: Seq<Run>, node: NodeImageView, children: Seq<int>, k: int)
    requires 0 <= k < children.len(), parent_child_certificate_at(nodes, forest, runs, node, children, k),
    ensures {
        let c = children[k];
        &&& 0 <= c < nodes.len()
        &&& extent_node::child(node.raw, k) == nodes[c].block
        &&& bytes::le16(nodes[c].raw, 6) + 1 == bytes::le16(node.raw, 6)
        &&& extent_node::key(node.raw, k) == runs[forest[c].first].logical
        &&& k + 1 < children.len() ==> forest[c].end == forest[children[k + 1]].first
    },
{
    reveal(parent_child_certificate_at);
}
proof fn parent_child_certificate_point(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    runs: Seq<Run>, links: Seq<Link>, indices: Seq<int>, level: nat,
    first: int, end: int, node: NodeImageView, k: int)
    requires witnessed_forest(nodes, forest, runs),
        frontier_description(nodes, forest, runs, links, indices, level, 0, runs.len() as int),
        0 <= first < end <= links.len(), 0 <= k < end - first,
        bytes::le16(node.raw, 6) == level + 1,
        index_record_matches(node.raw, links, first, k),
    ensures parent_child_certificate_at(nodes, forest, runs, node, indices.subrange(first, end), k),
{
    reveal(parent_child_certificate_at);
    let children = indices.subrange(first, end);
    let c = children[k];
    assert(children[k] == indices[first + k]);
    assert(0 <= first + k < links.len());
    assert(0 <= c < nodes.len());
    witnessed_node_source_range(nodes, forest, runs, c);
    index_record_matches_fields(node.raw, links, first, k);
    assert(links[first + k].address == nodes[c].block);
    assert(bytes::le16(nodes[c].raw, 6) == level);
    assert(links[first + k].first == runs[forest[c].first].logical);
    if k + 1 < children.len() {
        assert(0 <= first + k + 1 < links.len());
        assert(children[k + 1] == indices[first + k + 1]);
        assert(forest[c].end == forest[children[k + 1]].first);
    }
}
proof fn parent_child_certificates_assemble(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    runs: Seq<Run>, node: NodeImageView, children: Seq<int>)
    requires witnessed_forest(nodes, forest, runs),
        bytes::le16(node.raw, 6) > 0, bytes::le16(node.raw, 2) == children.len(), children.len() > 0,
        forall|k: int| #![trigger parent_child_certificate_at(nodes, forest, runs, node, children, k)]
            0 <= k < children.len() ==> parent_child_certificate_at(nodes, forest, runs, node, children, k),
    ensures witnessed_forest(nodes.push(node), forest.push(appended_index_witness(forest, children)), runs),
{
    assert forall|k: int| #![trigger children[k]] 0 <= k < children.len() implies {
        let c = children[k];
        &&& 0 <= c < nodes.len()
        &&& extent_node::child(node.raw, k) == nodes[c].block
        &&& bytes::le16(nodes[c].raw, 6) + 1 == bytes::le16(node.raw, 6)
        &&& extent_node::key(node.raw, k) == runs[forest[c].first].logical
        &&& k + 1 < children.len() ==> forest[c].end == forest[children[k + 1]].first
    } by {
        parent_child_certificate_fields(nodes, forest, runs, node, children, k);
    }
    forest_append_index(nodes, forest, runs, node, children);
}

proof fn parent_children_certificate(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    runs: Seq<Run>, links: Seq<Link>, indices: Seq<int>, level: nat,
    first: int, end: int, node: NodeImageView)
    requires witnessed_forest(nodes, forest, runs),
        frontier_description(nodes, forest, runs, links, indices, level, 0, runs.len() as int),
        0 <= first < end <= links.len(),
        bytes::le16(node.raw, 6) == level + 1, bytes::le16(node.raw, 2) == end - first,
        forall|k: int| #![trigger index_record_matches(node.raw, links, first, k)] 0 <= k < end - first ==>
            index_record_matches(node.raw, links, first, k),
    ensures witnessed_forest(nodes.push(node),
        forest.push(appended_index_witness(forest, indices.subrange(first, end))), runs),
{
    let children = indices.subrange(first, end);
    assert forall|k: int| #![trigger parent_child_certificate_at(nodes, forest, runs, node, children, k)]
        0 <= k < children.len() implies parent_child_certificate_at(nodes, forest, runs, node, children, k) by {
        parent_child_certificate_point(nodes, forest, runs, links, indices, level, first, end, node, k);
    }
    parent_child_certificates_assemble(nodes, forest, runs, node, children);
}

proof fn parent_frontier_descriptions(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    runs: Seq<Run>, links: Seq<Link>, indices: Seq<int>, next: Seq<Link>, next_indices: Seq<int>,
    level: nat, first: int, end: int, node: NodeImageView, link: Link)
    requires forest.len() == nodes.len(), frontier_description(nodes, forest, runs, links, indices, level, 0, runs.len() as int),
        frontier_description(nodes, forest, runs, next, next_indices, level + 1, 0,
            if first == 0 { 0 } else { forest[indices[first - 1]].end }),
        (first == 0) == (next.len() == 0), 0 <= first < end <= links.len(),
        bytes::le16(node.raw, 6) == level + 1,
        link.address == node.block && link.first == links[first].first && link.depth == level + 1,
    ensures frontier_description(nodes.push(node),
            forest.push(appended_index_witness(forest, indices.subrange(first, end))), runs,
            next.push(link), next_indices.push(nodes.len() as int), level + 1, 0,
            forest[indices[end - 1]].end),
        frontier_description(nodes.push(node),
            forest.push(appended_index_witness(forest, indices.subrange(first, end))), runs,
            links, indices, level, 0, runs.len() as int),
{
    let children = indices.subrange(first, end);
    let next_forest = forest.push(appended_index_witness(forest, children));
    let next_ids = next_indices.push(nodes.len() as int);
    assert(frontier_description(nodes.push(node), next_forest, runs,
        next.push(link), next_ids, level + 1, 0, forest[indices[end - 1]].end)) by {
        assert forall|k: int| #![trigger next_ids[k]] 0 <= k < next.push(link).len() implies {
            let index = next_ids[k];
            &&& 0 <= index < nodes.push(node).len()
            &&& next.push(link)[k].address == nodes.push(node)[index].block
            &&& next.push(link)[k].depth == level + 1
            &&& bytes::le16(nodes.push(node)[index].raw, 6) == level + 1
            &&& next.push(link)[k].first == runs[next_forest[index].first].logical
            &&& k + 1 < next.push(link).len() ==> next_forest[index].end == next_forest[next_ids[k + 1]].first
        } by {
            if k < next.len() {
                assert(next_ids[k] == next_indices[k]);
                assert(nodes.push(node)[next_indices[k]] == nodes[next_indices[k]]);
                assert(0 <= next_indices[k] < nodes.len() == forest.len());
                assert(next_forest[next_indices[k]] == forest[next_indices[k]]);
                if k + 1 == next.len() {
                    assert(first > 0);
                    assert(forest[next_indices[k]].end == forest[indices[first - 1]].end);
                    assert(forest[indices[first - 1]].end == forest[children[0]].first);
                } else if k + 1 < next.len() {
                    assert(0 <= next_indices[k + 1] < nodes.len() == forest.len());
                    assert(next_forest[next_indices[k + 1]] == forest[next_indices[k + 1]]);
                }
            } else {
                assert(k == next.len() && next_ids[k] == nodes.len());
                assert(next_forest[nodes.len() as int] == appended_index_witness(forest, children));
            }
        }
    }
    assert(frontier_description(nodes.push(node), next_forest, runs,
        links, indices, level, 0, runs.len() as int));
}


proof fn mixed_frontier_structure_view(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    source: SetView, pool: Seq<u64>, opts: OptionsView, seed: u32,
    links: Seq<Link>, indices: Seq<int>, next: Seq<Link>, next_indices: Seq<int>,
    level: nat, first: int)
    requires mixed_frontier_state(nodes, forest, source, pool, opts, seed,
        links, indices, next, next_indices, level, first),
    ensures witnessed_forest(nodes, forest, source.runs), forest.len() == nodes.len(),
        0 <= first <= links.len(), (first == 0) == (next.len() == 0),
        frontier_description(nodes, forest, source.runs, links, indices, level, 0, source.runs.len() as int),
        frontier_description(nodes, forest, source.runs, next, next_indices, level + 1, 0,
            if first == 0 { 0 } else { forest[indices[first - 1]].end }),
{
    reveal(mixed_frontier_state);
}

proof fn parent_fresh_reference_inputs(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    source: SetView, pool: Seq<u64>, opts: OptionsView, maximum: nat, seed: u32,
    links: Seq<Link>, indices: Seq<int>, next: Seq<Link>, next_indices: Seq<int>,
    level: nat, first: int, node: NodeImageView)
    requires extent_builder_context(source, opts, pool, maximum, seed),
        mixed_frontier_state(nodes, forest, source, pool, opts, seed,
            links, indices, next, next_indices, level, first),
        appendable_extent_node(node, nodes, pool, opts, source.blocks, seed, level + 1),
    ensures frontier_balance(nodes,
            link_addresses(next) + link_addresses(links).subrange(first, links.len() as int)),
        stored_frontier(nodes,
            link_addresses(next) + link_addresses(links).subrange(first, links.len() as int)),
        forall|i: int| #![trigger nodes[i].block] 0 <= i < nodes.len() ==> nodes[i].block != node.block,
        !emitted_references(nodes).contains(node.block),
        !(link_addresses(next) + link_addresses(links).subrange(first, links.len() as int)).contains(node.block),
{
    reveal(mixed_frontier_state);
    appended_node_is_fresh(nodes, pool, opts, source.blocks, seed, level + 1, node);
    forest_references_resolve(nodes, forest, source.runs, node.block);
    stored_frontier_excludes_fresh(nodes,
        link_addresses(next) + link_addresses(links).subrange(first, links.len() as int), node.block);
}
proof fn parent_metadata_projection_push(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    source: SetView, pool: Seq<u64>, opts: OptionsView, seed: u32,
    links: Seq<Link>, indices: Seq<int>, next: Seq<Link>, next_indices: Seq<int>,
    level: nat, first: int, node: NodeImageView)
    requires mixed_frontier_state(nodes, forest, source, pool, opts, seed,
            links, indices, next, next_indices, level, first),
        appendable_extent_node(node, nodes, pool, opts, source.blocks, seed, level + 1),
    ensures node_local_facts(nodes.push(node), pool, opts, source.blocks, seed, level + 1),
        emitted_leaf_projection(nodes.push(node)) == source.runs,
{
    reveal(mixed_frontier_state);
    local_node_facts_push(nodes, pool, opts, source.blocks, seed, level + 1, node);
    emitted_projection_push(nodes, node);
}

proof fn parent_reference_transition(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    source: SetView, pool: Seq<u64>, opts: OptionsView, maximum: nat, seed: u32,
    links: Seq<Link>, indices: Seq<int>, next: Seq<Link>, next_indices: Seq<int>,
    level: nat, first: int, end: int, node: NodeImageView, link: Link)
    requires extent_builder_context(source, opts, pool, maximum, seed),
        mixed_frontier_state(nodes, forest, source, pool, opts, seed,
            links, indices, next, next_indices, level, first),
        0 <= first < end <= links.len(),
        appendable_extent_node(node, nodes, pool, opts, source.blocks, seed, level + 1),
        bytes::le16(node.raw, 2) == end - first,
        forall|k: int| #![trigger index_record_matches(node.raw, links, first, k)] 0 <= k < end - first ==>
            index_record_matches(node.raw, links, first, k),
        link.address == node.block,
    ensures node_local_facts(nodes.push(node), pool, opts, source.blocks, seed, level + 1),
        emitted_leaf_projection(nodes.push(node)) == source.runs,
        frontier_balance(nodes.push(node),
            link_addresses(next.push(link)) + link_addresses(links).subrange(end, links.len() as int)),
        stored_frontier(nodes.push(node),
            link_addresses(next.push(link)) + link_addresses(links).subrange(end, links.len() as int)),
{
    parent_fresh_reference_inputs(nodes, forest, source, pool, opts, maximum, seed,
        links, indices, next, next_indices, level, first, node);
    parent_metadata_projection_push(nodes, forest, source, pool, opts, seed,
        links, indices, next, next_indices, level, first, node);
    let prefix = link_addresses(next);
    let consumed = link_addresses(links).subrange(first, end);
    let suffix = link_addresses(links).subrange(end, links.len() as int);
    let mixed = prefix + link_addresses(links).subrange(first, links.len() as int);
    assert(mixed =~= prefix + consumed + suffix);
    matched_index_records_describe_references(node.raw, links, first, end);
    assert(references(node.raw) =~= consumed);
    frontier_replace(nodes, prefix, consumed, suffix, node);
    stored_frontier_replacement(nodes, prefix, consumed, suffix, node);
    assert(link_addresses(next.push(link)) =~= prefix.push(node.block));
    assert(prefix.push(node.block) =~= prefix + seq![node.block]);
    let resulting_frontier = link_addresses(next.push(link)) + suffix;
    assert(resulting_frontier =~= (prefix + seq![node.block]) + suffix);
    assert(resulting_frontier == prefix + seq![node.block] + suffix);
    assert(frontier_balance(nodes.push(node), resulting_frontier));
    assert(stored_frontier(nodes.push(node), resulting_frontier));
}
proof fn parent_structure_transition(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    source: SetView, pool: Seq<u64>, opts: OptionsView, seed: u32,
    links: Seq<Link>, indices: Seq<int>, next: Seq<Link>, next_indices: Seq<int>,
    level: nat, first: int, end: int, node: NodeImageView, link: Link)
    requires mixed_frontier_state(nodes, forest, source, pool, opts, seed,
            links, indices, next, next_indices, level, first),
        0 <= first < end <= links.len(),
        bytes::le16(node.raw, 6) == level + 1, bytes::le16(node.raw, 2) == end - first,
        forall|k: int| #![trigger index_record_matches(node.raw, links, first, k)] 0 <= k < end - first ==>
            index_record_matches(node.raw, links, first, k),
        link.address == node.block && link.first == links[first].first && link.depth == level + 1,
    ensures witnessed_forest(nodes.push(node),
            forest.push(appended_index_witness(forest, indices.subrange(first, end))), source.runs),
        frontier_description(nodes.push(node),
            forest.push(appended_index_witness(forest, indices.subrange(first, end))), source.runs,
            links, indices, level, 0, source.runs.len() as int),
        frontier_description(nodes.push(node),
            forest.push(appended_index_witness(forest, indices.subrange(first, end))), source.runs,
            next.push(link), next_indices.push(nodes.len() as int), level + 1, 0,
            forest.push(appended_index_witness(forest, indices.subrange(first, end)))[indices[end - 1]].end),
{
    mixed_frontier_structure_view(nodes, forest, source, pool, opts, seed,
        links, indices, next, next_indices, level, first);
    parent_children_certificate(nodes, forest, source.runs, links, indices, level, first, end, node);
    parent_frontier_descriptions(nodes, forest, source.runs, links, indices, next, next_indices,
        level, first, end, node, link);
    let children = indices.subrange(first, end);
    let next_forest = forest.push(appended_index_witness(forest, children));
    let c = indices[end - 1];
    assert(0 <= c < nodes.len() == forest.len());
    assert(next_forest[c] == forest[c]);
}
proof fn mixed_frontier_intro(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    source: SetView, pool: Seq<u64>, opts: OptionsView, seed: u32,
    links: Seq<Link>, indices: Seq<int>, next: Seq<Link>, next_indices: Seq<int>,
    level: nat, start: int)
    requires 0 <= start <= links.len(), witnessed_forest(nodes, forest, source.runs),
        node_local_facts(nodes, pool, opts, source.blocks, seed, level + 1),
        frontier_description(nodes, forest, source.runs, links, indices, level, 0, source.runs.len() as int),
        frontier_description(nodes, forest, source.runs, next, next_indices, level + 1, 0,
            if start == 0 { 0 } else { forest[indices[start - 1]].end }),
        frontier_balance(nodes, link_addresses(next) + link_addresses(links).subrange(start, links.len() as int)),
        stored_frontier(nodes, link_addresses(next) + link_addresses(links).subrange(start, links.len() as int)),
        emitted_leaf_projection(nodes) == source.runs, (start == 0) == (next.len() == 0),
    ensures mixed_frontier_state(nodes, forest, source, pool, opts, seed,
        links, indices, next, next_indices, level, start),
{
    reveal(mixed_frontier_state);
}

proof fn append_parent_frontier(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    source: SetView, pool: Seq<u64>, opts: OptionsView, maximum: nat, seed: u32,
    links: Seq<Link>, indices: Seq<int>, next: Seq<Link>, next_indices: Seq<int>,
    level: nat, first: int, end: int, node: NodeImageView, link: Link)
    requires extent_builder_context(source, opts, pool, maximum, seed),
        mixed_frontier_state(nodes, forest, source, pool, opts, seed,
            links, indices, next, next_indices, level, first),
        0 <= first < end <= links.len(),
        appendable_extent_node(node, nodes, pool, opts, source.blocks, seed, level + 1),
        bytes::le16(node.raw, 2) == end - first,
        forall|k: int| #![trigger index_record_matches(node.raw, links, first, k)] 0 <= k < end - first ==>
            index_record_matches(node.raw, links, first, k),
        link.address == node.block && link.first == links[first].first && link.depth == level + 1,
    ensures mixed_frontier_state(nodes.push(node),
        forest.push(appended_index_witness(forest, indices.subrange(first, end))),
        source, pool, opts, seed, links, indices, next.push(link),
        next_indices.push(nodes.len() as int), level, end),
{
    parent_reference_transition(nodes, forest, source, pool, opts, maximum, seed,
        links, indices, next, next_indices, level, first, end, node, link);
    parent_structure_transition(nodes, forest, source, pool, opts, seed,
        links, indices, next, next_indices, level, first, end, node, link);
    let next_forest = forest.push(appended_index_witness(forest, indices.subrange(first, end)));
    mixed_frontier_intro(nodes.push(node), next_forest, source, pool, opts, seed,
        links, indices, next.push(link), next_indices.push(nodes.len() as int), level, end);
}

proof fn empty_complete_frontier(source: SetView, pool: Seq<u64>, opts: OptionsView, seed: u32)
    ensures complete_frontier_state(Seq::<NodeImageView>::empty(), Seq::<ExtentNodeWitness>::empty(),
        source, pool, opts, seed, Seq::<Link>::empty(), Seq::<int>::empty(), 0, 0),
{
    reveal_with_fuel(emitted_leaf_projection, 1);
    reveal_with_fuel(emitted_references, 1);
    assert(source.runs.take(0) =~= Seq::<Run>::empty());
    assert(0nat * opts.block_bytes as nat == 0) by(nonlinear_arith);
}
proof fn begin_mixed_frontier(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    source: SetView, pool: Seq<u64>, opts: OptionsView, seed: u32,
    links: Seq<Link>, indices: Seq<int>, level: nat)
    requires complete_frontier_state(nodes, forest, source, pool, opts, seed, links, indices,
        level, source.runs.len() as int),
    ensures mixed_frontier_state(nodes, forest, source, pool, opts, seed, links, indices,
        Seq::<Link>::empty(), Seq::<int>::empty(), level, 0),
{
    reveal(mixed_frontier_state);
    assert(source.runs.take(source.runs.len() as int) =~= source.runs);
    assert(link_addresses(Seq::<Link>::empty()) =~= Seq::<u64>::empty());
    assert(link_addresses(links).subrange(0, links.len() as int) =~= link_addresses(links));
    assert(node_local_facts(nodes, pool, opts, source.blocks, seed, level + 1)) by {
        assert forall|i: int| #![trigger nodes[i]] 0 <= i < nodes.len() implies {
            let node = nodes[i];
            &&& node.block == pool[i] && node.raw.len() == opts.block_bytes
            &&& extent_node::valid(extent_node::NodeView {
                raw: node.raw, blocks: source.blocks, kind: block_kind(opts.checksum, seed) })
            &&& bytes::le16(node.raw, 4) == (opts.block_bytes as nat - 12) / 12
            &&& bytes::le16(node.raw, 2) > 0 && bytes::le16(node.raw, 6) <= level + 1
            &&& bytes::le32(node.raw, 8) == 0
        } by {
            assert(bytes::le16(nodes[i].raw, 6) <= level);
        }
    }
}



proof fn mixed_frontier_node_budget(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    source: SetView, pool: Seq<u64>, opts: OptionsView, seed: u32,
    links: Seq<Link>, indices: Seq<int>, next: Seq<Link>, next_indices: Seq<int>,
    level: nat, start: int)
    requires mixed_frontier_state(nodes, forest, source, pool, opts, seed,
        links, indices, next, next_indices, level, start),
    ensures nodes.len() <= opts.node_budget, forest.len() == nodes.len(),
        indices.len() == links.len(), next_indices.len() == next.len(),
{
    reveal(mixed_frontier_state);
}

proof fn valid_set_builder_bounds(source: SetView)
    requires valid_set(source),
    ensures source.blocks > 0, source.runs.len() <= source.budget <= MAX_EXTENTS,
        ordered_intervals(source.runs, source.blocks),
{
    reveal(valid_set);
}
proof fn finish_mixed_frontier(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    source: SetView, pool: Seq<u64>, opts: OptionsView, seed: u32,
    links: Seq<Link>, indices: Seq<int>, next: Seq<Link>, next_indices: Seq<int>, level: nat)
    requires source.runs.len() > 0, links.len() > 0,
        mixed_frontier_state(nodes, forest, source, pool, opts, seed,
            links, indices, next, next_indices, level, links.len() as int),
    ensures complete_frontier_state(nodes, forest, source, pool, opts, seed,
        next, next_indices, level + 1, source.runs.len() as int),
{
    reveal(mixed_frontier_state);
    assert(link_addresses(links).subrange(links.len() as int, links.len() as int)
        =~= Seq::<u64>::empty());
    assert(next.len() > 0);
    assert(source.runs.take(source.runs.len() as int) =~= source.runs);
    assert(frontier_description(nodes, forest, source.runs, links, indices,
        level, 0, source.runs.len() as int));
    assert(forest[indices[links.len() as int - 1]].end == source.runs.len());
}
proof fn close_completed_extent_tree(v: PlanView, forest: Seq<ExtentNodeWitness>,
    frontier: Seq<u64>, root_witness: ExtentNodeWitness, maximum: nat)
    requires extent_builder_context(
            SetView { runs: v.runs, blocks: v.blocks, budget: v.extent_budget },
            v.options, v.pool, maximum, v.inode_seed),
        completed_extent_tree(v.root, v.nodes, forest,
            SetView { runs: v.runs, blocks: v.blocks, budget: v.extent_budget },
            v.pool, v.options, v.inode_seed, v.depth, frontier, root_witness),
        extent_node::valid(extent_node::NodeView {
            raw: v.root, blocks: v.blocks, kind: extent_node::NodeKind::Inline }),
        v.unused == v.pool.subrange(v.nodes.len() as int, v.pool.len() as int),
        v.data_blocks as nat == data_total(v.runs) <= LOGICAL_END,
        v.metadata_blocks as nat == v.nodes.len(),
    ensures valid_plan(v),
{
    if v.depth > 0 {
        close_external_forest(v, forest, frontier, root_witness);
    } else {
        reveal(valid_plan);
        assert(v.nodes.len() == 0);
        assert(child_links_bound(v.root, v.nodes));
    }
}


proof fn complete_inline_extent_tree(root: Seq<u8>, source: SetView, pool: Seq<u64>,
    opts: OptionsView, seed: u32, frontier: Seq<u64>, root_witness: ExtentNodeWitness)
    requires root.len() == 60, bytes::le16(root, 4) == 4,
        bytes::le16(root, 6) == 0, bytes::le32(root, 8) == 0,
        decoded_leaf(root) == source.runs,
    ensures completed_extent_tree(root, Seq::<NodeImageView>::empty(), Seq::<ExtentNodeWitness>::empty(),
        source, pool, opts, seed, 0, frontier, root_witness),
{
    assert(0nat * opts.block_bytes as nat == 0) by(nonlinear_arith);
}

proof fn witnessed_node_source_range(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    runs: Seq<Run>, index: int)
    requires witnessed_forest(nodes, forest, runs), 0 <= index < nodes.len(),
    ensures 0 <= forest[index].first < forest[index].end <= runs.len(),
{
    reveal(witnessed_node);
    assert(witnessed_node(nodes, forest, runs, index));
}
proof fn witnessed_forest_source_ranges(nodes: Seq<NodeImageView>, forest: Seq<ExtentNodeWitness>,
    runs: Seq<Run>)
    requires witnessed_forest(nodes, forest, runs),
    ensures forall|i: int| #![trigger forest[i].first] 0 <= i < nodes.len() ==>
        0 <= forest[i].first < forest[i].end <= runs.len(),
{
    assert forall|i: int| #![trigger forest[i].first] 0 <= i < nodes.len()
        implies 0 <= forest[i].first < forest[i].end <= runs.len() by {
        witnessed_node_source_range(nodes, forest, runs, i);
    }
}

proof fn complete_external_extent_root(root: Seq<u8>, nodes: Seq<NodeImageView>,
    forest: Seq<ExtentNodeWitness>, source: SetView, pool: Seq<u64>, opts: OptionsView,
    seed: u32, links: Seq<Link>, indices: Seq<int>, level: nat)
    requires complete_frontier_state(nodes, forest, source, pool, opts, seed,
            links, indices, level, source.runs.len() as int),
        source.runs.len() > 0, links.len() > 0, level <= 4,
        root.len() == 60, bytes::le16(root, 2) == links.len(), bytes::le16(root, 4) == 4,
        bytes::le16(root, 6) == level + 1, bytes::le32(root, 8) == 0,
        forall|k: int| #![trigger extent_node::child(root, k)] 0 <= k < links.len() ==>
            extent_node::child(root, k) == links[k].address && extent_node::key(root, k) == links[k].first,
    ensures completed_extent_tree(root, nodes, forest, source, pool, opts, seed,
        (level + 1) as u16, link_addresses(links),
        ExtentNodeWitness { first: 0, end: source.runs.len() as int, children: indices }),
{
    assert(source.runs.take(source.runs.len() as int) =~= source.runs);
    assert(emitted_leaf_projection(nodes) == source.runs);
    witnessed_forest_source_ranges(nodes, forest, source.runs);
    let root_node = NodeImageView { block: 0, raw: root };
    assert(indices.len() == links.len() && indices.len() > 0);
    assert(forest[indices[0]].first == 0);
    assert(forest[indices[indices.len() as int - 1]].end == source.runs.len());
    assert(references(root) =~= link_addresses(links));
    assert forall|k: int| #![trigger indices[k]] 0 <= k < indices.len() implies {
        let c = indices[k];
        &&& 0 <= c < nodes.len()
        &&& extent_node::child(root, k) == nodes[c].block
        &&& bytes::le16(nodes[c].raw, 6) + 1 == bytes::le16(root, 6)
        &&& extent_node::key(root, k) == source.runs[forest[c].first].logical
        &&& k + 1 < indices.len() ==> forest[c].end == forest[indices[k + 1]].first
    } by {
        let c = indices[k];
        assert(0 <= c < nodes.len());
        assert(0 <= forest[c].first < forest[c].end <= source.runs.len());
    }
    forest_append_index(nodes, forest, source.runs, root_node, indices);
    let root_witness = ExtentNodeWitness { first: 0, end: source.runs.len() as int, children: indices };
    assert(appended_index_witness(forest, indices) == root_witness);
    assert(witnessed_forest(nodes.push(root_node), forest.push(root_witness), source.runs));
    let depth = (level + 1) as u16;
    assert(depth as nat == level + 1 && 1 <= depth <= 5);
    assert(bytes::le16(root, 6) == depth);
    assert(((level + 1) as u16 - 1) as nat == level);
    assert(node_local_facts(nodes, pool, opts, source.blocks, seed, ((level + 1) as u16 - 1) as nat));
    assert(completed_extent_tree(root, nodes, forest, source, pool, opts, seed,
        (level + 1) as u16, link_addresses(links), root_witness));
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
    proof { use_type_invariant(set); valid_set_builder_bounds(set.view()); }
    if !crate::block_size::valid(options.block_bytes as usize) || options.inode == 0
        || minimum_depth > 5 || options.node_budget > MAX_METADATA_NODES { return Err(Error::Geometry); }
    if set.runs.len() == 0 && minimum_depth != 0 { return Err(Error::Depth); }
    match validate_pool(set, metadata_pool, options.node_budget) { Ok(()) => {}, Err(e) => { return Err(e); } }
    let seed = crate::inode::inode_seed(options.filesystem_seed, options.inode, options.generation);
    proof { supported_block_capacity(options.block_bytes); }
    let maximum = (options.block_bytes as usize - 12) / 12;
    let ghost source = set.view();
    let ghost opts = options_view(options);
    let ghost pool = metadata_pool@;
    let ghost mut forest = Seq::<ExtentNodeWitness>::empty();
    let ghost mut completed_frontier = Seq::<u64>::empty();
    let ghost mut root_witness = ExtentNodeWitness { first: 0, end: 0, children: Seq::empty() };
    let mut root = [0u8; 60];
    let mut nodes = Vec::<NodeImage>::new();
    let depth;
    proof { assert(extent_builder_context(source, opts, pool, maximum as nat, seed)); }
    if set.runs.len() <= 4 && minimum_depth == 0 {
        if !header(&mut root, set.runs.len(), 4, 0) { return Err(Error::Encoding); }
        let mut i = 0usize;
        while i < set.runs.len()
            invariant set.wf(), set.view() == source, options_view(options) == opts, metadata_pool@ == pool,
                extent_builder_context(source, opts, pool, maximum as nat, seed),
                minimum_depth <= 5,
                minimum_depth == 0, i <= set.runs.len() <= 4, nodes.len() == 0, forest.len() == 0,
                bytes::le16(root@, 2) == source.runs.len(), bytes::le16(root@, 4) == 4,
                bytes::le16(root@, 6) == 0, bytes::le32(root@, 8) == 0,
                forall|j: int| 0 <= j < i ==> #[trigger] decoded_leaf(root@)[j] == source.runs[j],
            decreases set.runs.len() - i,
        {
            let ghost before = root@;
            if !encode_run(&mut root, 12 + i * 12, set.runs[i], set.blocks) { return Err(Error::Encoding); }
            proof {
                record_write_preserves_other_records(before, root@, i as int);
                encoded_run_is_decoded_run(root@, i as int, source.runs[i as int], source.blocks);
            }
            i += 1;
        }
        proof { assert(decoded_leaf(root@) =~= source.runs); }
        depth = 0u16;
        proof {
            assert(node_views(nodes@) =~= Seq::<NodeImageView>::empty());
            assert(forest =~= Seq::<ExtentNodeWitness>::empty());
            complete_inline_extent_tree(root@, source, pool, opts, seed, completed_frontier, root_witness);
        }
    } else {
        let mut links = Vec::<Link>::new(); let mut start = 0usize;
        let ghost mut indices = Seq::<int>::empty();
        proof {
            assert(node_views(nodes@) =~= Seq::<NodeImageView>::empty());
            empty_complete_frontier(source, pool, opts, seed);
            assert(complete_frontier_state(node_views(nodes@), forest, source, pool, opts,
                seed, links@, indices, 0, 0));
        }
        while start < set.runs.len()
            invariant set.wf(), set.view() == source, options_view(options) == opts, metadata_pool@ == pool,
                extent_builder_context(source, opts, pool, maximum as nat, seed),
                minimum_depth <= 5, source.runs.len() > 0,
                start <= set.runs.len() <= MAX_EXTENTS,
                complete_frontier_state(node_views(nodes@), forest, source, pool, opts,
                    seed, links@, indices, 0, start as int),
            decreases set.runs.len() - start,
        {
            let end = if maximum > set.runs.len() - start { set.runs.len() } else { start + maximum };
            let mut raw = match zeroes(options.block_bytes as usize) { Ok(raw) => raw, Err(e) => { return Err(e); } };
            if !header(&mut raw, end - start, maximum, 0) { return Err(Error::Encoding); }
            let mut i = start;
            while i < end
                invariant set.wf(), set.view() == source, options_view(options) == opts, metadata_pool@ == pool,
                extent_builder_context(source, opts, pool, maximum as nat, seed),
                minimum_depth <= 5, source.runs.len() > 0,
                    0 <= start < end <= set.runs.len() <= MAX_EXTENTS,
                    start <= i <= end, end - start <= maximum,
                    complete_frontier_state(node_views(nodes@), forest, source, pool, opts,
                        seed, links@, indices, 0, start as int),
                    raw.len() == options.block_bytes,
                    bytes::le16(raw@, 2) == end - start, bytes::le16(raw@, 4) == maximum,
                    bytes::le16(raw@, 6) == 0, bytes::le32(raw@, 8) == 0,
                    forall|j: int| 0 <= j < i - start
                        ==> #[trigger] decoded_leaf(raw@)[j] == source.runs[start as int + j],
                decreases end - i,
            {
                let ghost before = raw@;
                proof {
                    assert(12 + (i - start) as nat * 12 + 12 <= options.block_bytes);
                    assert((i - start) as nat <= 5460);
                    assert((i - start) as nat * 12 <= 65536) by(nonlinear_arith)
                        requires (i - start) as nat <= 5460;
                }
                if !encode_run(&mut raw, 12 + (i - start) * 12, set.runs[i], set.blocks) {
                    return Err(Error::Encoding);
                }
                proof {
                    record_write_preserves_other_records(before, raw@, (i - start) as int);
                    encoded_run_is_decoded_run(raw@, (i - start) as int, source.runs[i as int], source.blocks);
                }
                i += 1;
            }
            let ghost leaf_raw = raw@;
            let ghost old_nodes = node_views(nodes@);
            let ghost old_links = links@;
            proof {
                assert(decoded_leaf(leaf_raw) =~= source.runs.subrange(start as int, end as int));
            }
            if !stamp_node(&mut raw, maximum, options.metadata_checksum, seed) { return Err(Error::Encoding); }
            proof {
                prefix_frame_preserves_extent_description(leaf_raw, raw@, 12 + maximum as int * 12);
            }
            let link = match emit_node(&mut nodes, metadata_pool, raw, set.runs[start].logical,
                0, &options, set.blocks, seed) { Ok(link) => link, Err(e) => { return Err(e); } };
            let ghost node = node_views(nodes@).last();
            let ghost number = old_nodes.len() as int;
            proof {
                assert(node_views(nodes@) =~= old_nodes.push(node));
                assert(appendable_extent_node(node, old_nodes, pool, opts, source.blocks, seed, 0));
                assert(decoded_leaf(node.raw) == source.runs.subrange(start as int, end as int));
                assert(extent_node::key(node.raw, 0) == source.runs[start as int].logical) by {
                    reveal(extent_node::key);
                    assert(decoded_leaf(node.raw)[0] == source.runs[start as int]);
                }
                append_leaf_frontier(old_nodes, forest, source, pool, opts, maximum as nat, seed,
                    old_links, indices, start as int, end as int, node, link);
                forest = forest.push(appended_leaf_witness(start as int, end as int));
                indices = indices.push(number);
            }
            links.push(link);
            start = end;
        }
        let mut level = 0u16;
        while links.len() > 4 || level + 1 < minimum_depth
            invariant set.wf(), set.view() == source, options_view(options) == opts, metadata_pool@ == pool,
                extent_builder_context(source, opts, pool, maximum as nat, seed),
                minimum_depth <= 5, source.runs.len() > 0,
                level <= 4, links.len() > 0,
                complete_frontier_state(node_views(nodes@), forest, source, pool, opts,
                    seed, links@, indices, level as nat, source.runs.len() as int),
            decreases 5 - level,
        {
            if level >= 4 { return Err(Error::Depth); }
            let mut next = Vec::<Link>::new(); start = 0;
            let ghost mut next_indices = Seq::<int>::empty();
            proof {
                begin_mixed_frontier(node_views(nodes@), forest, source, pool, opts,
                    seed, links@, indices, level as nat);
                assert(mixed_frontier_state(node_views(nodes@), forest, source, pool, opts,
                    seed, links@, indices, next@, next_indices, level as nat, 0));
            }
            while start < links.len()
                invariant set.wf(), set.view() == source, options_view(options) == opts, metadata_pool@ == pool,
                extent_builder_context(source, opts, pool, maximum as nat, seed),
                minimum_depth <= 5, source.runs.len() > 0,
                    start <= links.len(), level < 4, links.len() > 0,
                    mixed_frontier_state(node_views(nodes@), forest, source, pool, opts,
                        seed, links@, indices, next@, next_indices, level as nat, start as int),
                decreases links.len() - start,
            {
                let end = if maximum > links.len() - start { links.len() } else { start + maximum };
                let mut raw = match zeroes(options.block_bytes as usize) { Ok(raw) => raw, Err(e) => { return Err(e); } };
                if !header(&mut raw, end - start, maximum, level + 1) { return Err(Error::Encoding); }
                let mut i = start;
                while i < end
                    invariant set.wf(), set.view() == source, options_view(options) == opts, metadata_pool@ == pool,
                extent_builder_context(source, opts, pool, maximum as nat, seed),
                minimum_depth <= 5, source.runs.len() > 0,
                        0 <= start < end <= links.len(), start <= i <= end,
                        end - start <= maximum, level < 4, links.len() > 0,
                        mixed_frontier_state(node_views(nodes@), forest, source, pool, opts,
                            seed, links@, indices, next@, next_indices, level as nat, start as int),
                        raw.len() == options.block_bytes,
                        bytes::le16(raw@, 2) == end - start, bytes::le16(raw@, 4) == maximum,
                        bytes::le16(raw@, 6) == level as nat + 1, bytes::le32(raw@, 8) == 0,
                        forall|j: int| #![trigger index_record_matches(raw@, links@, start as int, j)]
                            0 <= j < i as int - start as int ==> index_record_matches(raw@, links@, start as int, j),
                    decreases end - i,
                {
                    let ghost before = raw@;
                    proof {
                        assert(12 + (i - start) as nat * 12 + 12 <= options.block_bytes);
                        assert((i - start) as nat <= 5460);
                        assert((i - start) as nat * 12 <= 65536) by(nonlinear_arith)
                            requires (i - start) as nat <= 5460;
                    }
                    if !encode_link(&mut raw, 12 + (i - start) * 12, links[i], level + 1) {
                        return Err(Error::Encoding);
                    }
                    proof { record_write_preserves_other_records(before, raw@, (i - start) as int);
                        reveal(extent_node::key);
                        assert(extent_node::key(raw@, (i - start) as int) == links@[i as int].first);
                        assert(extent_node::child(raw@, (i - start) as int) == links@[i as int].address);
                        index_record_matches_intro(raw@, links@, start as int, (i - start) as int);
                        assert forall|j: int| #![trigger index_record_matches(raw@, links@, start as int, j)]
                            0 <= j <= i as int - start as int
                                implies index_record_matches(raw@, links@, start as int, j) by {
                            if j < i as int - start as int {
                                assert(extent_node::child(raw@, j) == extent_node::child(before, j));
                                assert(extent_node::key(raw@, j) == extent_node::key(before, j));
                                index_record_matches_frame(before, raw@, links@, start as int, j);
                            } else { assert(j == (i - start) as int); }
                        }
                    }
                    i += 1;
                }
                proof {
                    mixed_frontier_node_budget(node_views(nodes@), forest, source, pool, opts, seed,
                        links@, indices, next@, next_indices, level as nat, start as int);
                }
                let ghost index_raw = raw@;
                let ghost old_nodes = node_views(nodes@);
                let ghost old_next = next@;
                let ghost children = indices.subrange(start as int, end as int);
                if !stamp_node(&mut raw, maximum, options.metadata_checksum, seed) { return Err(Error::Encoding); }
                proof {
                    prefix_frame_preserves_extent_description(index_raw, raw@, 12 + maximum as int * 12);
                }
                let ghost sealed_raw = raw@;
                proof {
                    assert forall|k: int| #![trigger index_record_matches(sealed_raw, links@, start as int, k)]
                        0 <= k < end as int - start as int
                            implies index_record_matches(sealed_raw, links@, start as int, k) by {
                        assert(extent_node::key(sealed_raw, k) == extent_node::key(index_raw, k));
                        assert(extent_node::child(sealed_raw, k) == extent_node::child(index_raw, k));
                        index_record_matches_frame(index_raw, sealed_raw, links@, start as int, k);
                    }
                }
                let link = match emit_node(&mut nodes, metadata_pool, raw, links[start].first,
                    level + 1, &options, set.blocks, seed) { Ok(link) => link, Err(e) => { return Err(e); } };
                let ghost node = node_views(nodes@).last();
                let ghost number = old_nodes.len() as int;
                proof {
                    assert(node_views(nodes@) =~= old_nodes.push(node));
                    assert(appendable_extent_node(node, old_nodes, pool, opts, source.blocks, seed, level as nat + 1));
                    assert(node.raw == sealed_raw);
                    assert forall|k: int| #![trigger index_record_matches(node.raw, links@, start as int, k)]
                        0 <= k < end as int - start as int
                            implies index_record_matches(node.raw, links@, start as int, k) by {
                        assert(index_record_matches(sealed_raw, links@, start as int, k));
                    }
                    append_parent_frontier(old_nodes, forest, source, pool, opts, maximum as nat, seed,
                        links@, indices, old_next, next_indices, level as nat,
                        start as int, end as int, node, link);
                    forest = forest.push(appended_index_witness(forest, children));
                    next_indices = next_indices.push(number);
                }
                next.push(link);
                start = end;
            }
            proof {
                finish_mixed_frontier(node_views(nodes@), forest, source, pool, opts, seed,
                    links@, indices, next@, next_indices, level as nat);
                indices = next_indices;
            }
            links = next; level += 1;
        }
        depth = level + 1;
        if !header(&mut root, links.len(), 4, depth) { return Err(Error::Encoding); }
        let mut i = 0usize;
        while i < links.len()
            invariant set.wf(), set.view() == source, options_view(options) == opts, metadata_pool@ == pool,
                extent_builder_context(source, opts, pool, maximum as nat, seed),
                minimum_depth <= 5, source.runs.len() > 0,
                minimum_depth <= depth, i <= links.len() <= 4, 1 <= depth <= 5, depth as nat == level as nat + 1,
                complete_frontier_state(node_views(nodes@), forest, source, pool, opts,
                    seed, links@, indices, level as nat, source.runs.len() as int),
                bytes::le16(root@, 2) == links.len(), bytes::le16(root@, 4) == 4,
                bytes::le16(root@, 6) == depth, bytes::le32(root@, 8) == 0,
                forall|j: int| 0 <= j < i ==>
                    #[trigger] extent_node::child(root@, j) == links@[j].address
                        && extent_node::key(root@, j) == links@[j].first,
            decreases links.len() - i,
        {
            let ghost before = root@;
            if !encode_link(&mut root, 12 + i * 12, links[i], depth) { return Err(Error::Encoding); }
            proof { record_write_preserves_other_records(before, root@, i as int);
                reveal(extent_node::key);
                assert(extent_node::key(root@, i as int) == links@[i as int].first);
                assert(extent_node::child(root@, i as int) == links@[i as int].address);
                assert forall|j: int| #![trigger extent_node::child(root@, j)]
                    0 <= j <= i implies extent_node::child(root@, j) == links@[j].address
                        && extent_node::key(root@, j) == links@[j].first by {
                    if j < i {
                        assert(extent_node::child(root@, j) == extent_node::child(before, j));
                        assert(extent_node::key(root@, j) == extent_node::key(before, j));
                    } else { assert(j == i); }
                }
            }
            i += 1;
        }
        proof {
            complete_external_extent_root(root@, node_views(nodes@), forest, source, pool, opts,
                seed, links@, indices, level as nat);
            root_witness = ExtentNodeWitness { first: 0, end: source.runs.len() as int, children: indices };
            completed_frontier = link_addresses(links@);
        }
    }
    proof {
        assert(completed_extent_tree(root@, node_views(nodes@), forest, source, pool, opts,
            seed, depth, completed_frontier, root_witness));
    }
    if extent_node::parse_inline_root(&root, set.blocks).is_none() { return Err(Error::Encoding); }
    let mut unused = Vec::<u64>::new(); let mut i = nodes.len();
    while i < metadata_pool.len()
        invariant set.wf(), set.view() == source, options_view(options) == opts, metadata_pool@ == pool,
                extent_builder_context(source, opts, pool, maximum as nat, seed),
                minimum_depth <= 5,
            completed_extent_tree(root@, node_views(nodes@), forest, source, pool, opts,
                seed, depth, completed_frontier, root_witness),
            extent_node::valid(extent_node::NodeView { raw: root@, blocks: source.blocks, kind: extent_node::NodeKind::Inline }),
            minimum_depth <= depth,
            nodes.len() <= i <= metadata_pool.len() <= MAX_METADATA_NODES,
            unused@ == metadata_pool@.subrange(nodes.len() as int, i as int),
        decreases metadata_pool.len() - i,
    { unused.push(metadata_pool[i]); i += 1; }
    let mut runs = Vec::<Run>::new(); let mut data_blocks = 0u64; i = 0;
    while i < set.runs.len()
        invariant set.wf(), set.view() == source, options_view(options) == opts, metadata_pool@ == pool,
                extent_builder_context(source, opts, pool, maximum as nat, seed),
                minimum_depth <= 5,
            completed_extent_tree(root@, node_views(nodes@), forest, source, pool, opts,
                seed, depth, completed_frontier, root_witness),
            extent_node::valid(extent_node::NodeView { raw: root@, blocks: source.blocks, kind: extent_node::NodeKind::Inline }),
            minimum_depth <= depth,
            unused@ == metadata_pool@.subrange(nodes.len() as int, metadata_pool.len() as int),
            i <= set.runs.len() <= MAX_EXTENTS, runs.len() == i, runs@ == set.runs@.take(i as int),
            data_blocks as nat == data_total(runs@) <= LOGICAL_END,
        decreases set.runs.len() - i,
    {
        proof { valid_set_builder_bounds(source); assert(interval_valid(source.runs[i as int], source.blocks)); }
        if data_blocks > LOGICAL_END - set.runs[i].length as u64 { return Err(Error::Range); }
        let ghost before = runs@;
        data_blocks += set.runs[i].length as u64; runs.push(set.runs[i]);
        proof {
            assert(runs@ =~= before.push(source.runs[i as int]));
            assert(runs@.drop_last() =~= before);
            assert(runs@ =~= source.runs.take(i as int + 1));
            assert(ordered_intervals(runs@, source.blocks));
            extent_lengths_fit_the_logical_address_space(runs@, source.blocks);
        }
        i += 1;
    }
    let metadata_blocks = nodes.len() as u64;
    proof {
        assert(runs@ =~= source.runs);
        let view = PlanView {
            root: root@, nodes: node_views(nodes@), unused: unused@, runs: runs@,
            depth, inode_seed: seed, options: opts, pool, blocks: source.blocks,
            extent_budget: source.budget, data_blocks, metadata_blocks,
        };
        close_completed_extent_tree(view, forest, completed_frontier, root_witness, maximum as nat);
        assert(valid_plan(view));
    }
    Ok(EditPlan { root, nodes, unused, runs, depth, inode: options.inode,
        generation: options.generation, inode_seed: seed, block_bytes: options.block_bytes,
        data_blocks, metadata_blocks, options: Ghost(options_view(options)),
        pool: Ghost(metadata_pool@), blocks: Ghost(set.blocks), extent_budget: Ghost(set.budget) })
}

}
