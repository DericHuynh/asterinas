// SPDX-License-Identifier: MPL-2.0

//! Bounded parent-graph traversal: checked path gathering, depth assignment
//! and resolution. Paths are ghost certificates; the executable needs only
//! color/depth arrays and cursor counters, without a runtime recursion stack.

use vstd::prelude::*;
use crate::{block_claims, name_set, parent_table};

verus! {

pub const MAX_DEPTH: u32 = name_set::MAX_KEYS;

pub open spec fn active(parents: Seq<u32>, n: int) -> bool { 0 <= n < parents.len() && parents[n] != 0 }

#[verifier::opaque]
pub open spec fn shape(parents: Seq<u32>) -> bool {
    &&& 3 <= parents.len() <= block_claims::MAX_BLOCKS as nat + 1 && parents[2] == 2
    &&& forall|n: int| active(parents, n) ==> 0 < (#[trigger] parents[n]) < parents.len() && active(parents, parents[n] as int)
}

pub proof fn checked_parent_table_has_graph_shape(v: parent_table::TableView)
    requires parent_table::valid(v),
    ensures shape(v.parents),
{
    reveal(parent_table::valid); reveal(shape);
}

pub open spec fn node_rank(parents: Seq<u32>, depths: Seq<u32>, n: int) -> bool {
    active(parents, n) && if n == 2 { depths[n] == 0 }
    else { 0 < depths[n] <= MAX_DEPTH && depths[parents[n] as int] as nat + 1 == depths[n] as nat }
}

#[verifier::opaque]
pub open spec fn ranked(parents: Seq<u32>, colors: Seq<u8>, depths: Seq<u32>) -> bool {
    &&& colors.len() == parents.len() && depths.len() == parents.len() && parents.len() >= 3
    &&& colors[2] == 2 && depths[2] == 0
    &&& forall|n: int| 0 <= n < colors.len() ==> (#[trigger] colors[n]) <= 2
    &&& forall|n: int| 0 <= n < colors.len() && !active(parents, n) ==> (#[trigger] colors[n]) == 0 && depths[n] == 0
    &&& forall|n: int| 0 <= n < colors.len() && (#[trigger] colors[n]) == 2 ==> node_rank(parents, depths, n)
}

#[verifier::opaque]
pub open spec fn closed(parents: Seq<u32>, colors: Seq<u8>) -> bool {
    forall|n: int| 0 <= n < colors.len() && (#[trigger] colors[n]) == 2 ==> colors[parents[n] as int] == 2
}

#[verifier::opaque]
pub open spec fn no_pending(colors: Seq<u8>) -> bool {
    forall|n: int| 0 <= n < colors.len() ==> (#[trigger] colors[n]) == 0 || colors[n] == 2
}

#[verifier::opaque]
pub open spec fn path_chain(parents: Seq<u32>, path: Seq<u32>, start: u32, end: u32) -> bool {
    &&& active(parents, end as int) && path.no_duplicates()
    &&& if path.len() == 0 { end == start } else { path[0] == start }
    &&& forall|i: int| 0 <= i < path.len() ==> active(parents, #[trigger] path[i] as int)
        && parents[path[i] as int] == if i + 1 < path.len() { path[i + 1] } else { end }
}

#[verifier::opaque]
pub open spec fn gathered(old: Seq<u8>, now: Seq<u8>, path: Seq<u32>) -> bool {
    &&& old.len() == now.len()
    &&& forall|i: int| 0 <= i < path.len() ==> (#[trigger] path[i]) < old.len() && old[path[i] as int] == 0
    &&& forall|n: int| 0 <= n < now.len() ==> #[trigger] now[n] == if path.contains(n as u32) { 1u8 } else { old[n] }
}

#[verifier::opaque]
pub open spec fn depth_prefix(old: Seq<u32>, now: Seq<u32>, path: Seq<u32>, base: u32, done: nat) -> bool {
    &&& old.len() == now.len() && done <= path.len()
    &&& forall|i: int| 0 <= i < path.len() ==> (#[trigger] path[i]) < old.len()
        && now[path[i] as int] as int == if i < done { base as int + path.len() as int - i } else { old[path[i] as int] as int }
    &&& forall|n: int| 0 <= n < now.len() && !path.contains(n as u32) ==> #[trigger] now[n] == old[n]
}

#[verifier::opaque]
pub open spec fn resolved_prefix(old: Seq<u8>, now: Seq<u8>, path: Seq<u32>, done: nat) -> bool {
    &&& old.len() == now.len() && done <= path.len()
    &&& forall|i: int| 0 <= i < path.len() ==> (#[trigger] path[i]) < old.len() && old[path[i] as int] == 0
        && now[path[i] as int] == if i < done { 2u8 } else { 1u8 }
    &&& forall|n: int| 0 <= n < now.len() && !path.contains(n as u32) ==> #[trigger] now[n] == old[n]
}

#[verifier::opaque]
pub open spec fn path_ranked(parents: Seq<u32>, depths: Seq<u32>, path: Seq<u32>) -> bool {
    forall|i: int| 0 <= i < path.len() ==> #[trigger] node_rank(parents, depths, path[i] as int)
}

#[verifier::opaque]
pub open spec fn processed(parents: Seq<u32>, colors: Seq<u8>, count: nat) -> bool {
    forall|n: u32| n < count && active(parents, n as int) ==> (#[trigger] colors[n as int]) == 2
}

pub proof fn empty_path_is_ready(parents: Seq<u32>, colors: Seq<u8>, start: u32)
    requires shape(parents), colors.len() == parents.len(), active(parents, start as int),
    ensures path_chain(parents, Seq::empty(), start, start), gathered(colors, colors, Seq::empty()),
{
    reveal(path_chain); reveal(gathered);
}

pub proof fn path_successor(parents: Seq<u32>, path: Seq<u32>, start: u32, end: u32, index: nat)
    requires path_chain(parents, path, start, end), index < path.len(),
    ensures active(parents, path[index as int] as int),
        parents[path[index as int] as int] == if index + 1 < path.len() { path[index as int + 1] } else { end },
{
    reveal(path_chain);
}

pub proof fn gathered_path_starts_resolution(old: Seq<u8>, now: Seq<u8>, path: Seq<u32>)
    requires gathered(old, now, path), old.len() <= block_claims::MAX_BLOCKS as nat + 1,
    ensures resolved_prefix(old, now, path, 0),
{
    reveal(gathered); reveal(resolved_prefix);
    assert forall|i: int| 0 <= i < path.len() implies (#[trigger] path[i]) < old.len() && old[path[i] as int] == 0 && now[path[i] as int] == 1 by {
        assert(path.contains(path[i]));
    }
}

pub proof fn append_fresh_path_node(parents: Seq<u32>, old: Seq<u8>, now: Seq<u8>, path: Seq<u32>, start: u32, cursor: u32, next: u32)
    requires shape(parents), old.len() == parents.len(), path_chain(parents, path, start, cursor), gathered(old, now, path),
        now[cursor as int] == 0, parents[cursor as int] == next, active(parents, next as int),
    ensures path_chain(parents, path.push(cursor), start, next), gathered(old, now.update(cursor as int, 1u8), path.push(cursor)),
{
    reveal(shape); reveal(path_chain); reveal(gathered);
    assert(!path.contains(cursor)) by {
        if path.contains(cursor) {
            let i = choose|i: int| 0 <= i < path.len() && path[i] == cursor;
            assert(now[path[i] as int] == 1);
        }
    }
    assert(old[cursor as int] == 0);
    assert forall|i: int| 0 <= i < path.len() + 1 implies active(parents, #[trigger] path.push(cursor)[i] as int)
        && parents[path.push(cursor)[i] as int] == if i + 1 < path.len() + 1 { path.push(cursor)[i + 1] } else { next } by {
        if i < path.len() { assert(active(parents, path[i] as int)); }
    }
    assert forall|n: int| 0 <= n < now.len() implies #[trigger] now.update(cursor as int, 1u8)[n] ==
        if path.push(cursor).contains(n as u32) { 1u8 } else { old[n] } by {
        vstd::seq_lib::lemma_seq_contains_after_push(path, cursor, n as u32);
    }
}

pub proof fn assign_next_depth(old: Seq<u32>, now: Seq<u32>, path: Seq<u32>, base: u32, done: nat)
    requires old.len() <= block_claims::MAX_BLOCKS as nat + 1, path.no_duplicates(),
        depth_prefix(old, now, path, base, done), done < path.len(), base as nat + path.len() <= MAX_DEPTH,
    ensures depth_prefix(old, now.update(path[done as int] as int, (base as nat + path.len() - done) as u32), path, base, done + 1),
{
    reveal(depth_prefix);
    let cursor = path[done as int];
    assert(path.contains(cursor));
    assert forall|i: int| 0 <= i < path.len() implies (#[trigger] path[i]) < old.len()
        && now.update(cursor as int, (base as nat + path.len() - done) as u32)[path[i] as int] as int ==
            if i < done + 1 { base as int + path.len() as int - i } else { old[path[i] as int] as int } by {
        if i != done { assert(path[i] != cursor); }
    }
}

#[verifier::rlimit(200)]
#[verifier::spinoff_prover]
pub proof fn full_depth_assignment_has_parent_ranks(parents: Seq<u32>, old_colors: Seq<u8>, old_depths: Seq<u32>, colors: Seq<u8>, depths: Seq<u32>,
    path: Seq<u32>, start: u32, anchor: u32, base: u32)
    requires shape(parents), ranked(parents, old_colors, old_depths), closed(parents, old_colors),
        path_chain(parents, path, start, anchor), gathered(old_colors, colors, path), colors[anchor as int] == 2,
        depth_prefix(old_depths, depths, path, base, path.len()), base == old_depths[anchor as int], base as nat + path.len() <= MAX_DEPTH,
    ensures ranked(parents, colors, depths), closed(parents, colors), path_ranked(parents, depths, path),
{
    reveal(shape); reveal(ranked); reveal(closed); reveal(path_chain); reveal(gathered); reveal(depth_prefix); reveal(path_ranked);
    assert(!path.contains(anchor));
    assert(old_colors[anchor as int] == 2 && depths[anchor as int] == base);
    assert(!path.contains(2u32));
    assert forall|n: int| 0 <= n < colors.len() && (#[trigger] colors[n]) == 2 implies node_rank(parents, depths, n) by {
        assert(!path.contains(n as u32) && old_colors[n] == 2);
        assert(node_rank(parents, old_depths, n));
        assert(old_colors[parents[n] as int] == 2);
        assert(!path.contains(parents[n]));
    }
    assert forall|i: int| 0 <= i < path.len() implies #[trigger] node_rank(parents, depths, path[i] as int) by {
        let n = path[i];
        assert(n != 2 && depths[n as int] as int == base as int + path.len() as int - i);
        if i + 1 < path.len() { assert(parents[n as int] == path[i + 1]); }
        else { assert(parents[n as int] == anchor); }
    }
    assert forall|n: int| 0 <= n < colors.len() && (#[trigger] colors[n]) == 2 implies colors[parents[n] as int] == 2 by {
        assert(old_colors[n] == 2 && old_colors[parents[n] as int] == 2);
        assert(!path.contains(parents[n]));
    }
}

pub proof fn resolve_next_node(parents: Seq<u32>, old: Seq<u8>, colors: Seq<u8>, depths: Seq<u32>, path: Seq<u32>, done: nat)
    requires shape(parents), ranked(parents, colors, depths), path.no_duplicates(), path_ranked(parents, depths, path),
        resolved_prefix(old, colors, path, done), done < path.len(),
    ensures ranked(parents, colors.update(path[done as int] as int, 2u8), depths),
        resolved_prefix(old, colors.update(path[done as int] as int, 2u8), path, done + 1),
{
    reveal(shape); reveal(ranked); reveal(path_ranked); reveal(resolved_prefix);
    let cursor = path[done as int];
    assert(node_rank(parents, depths, cursor as int));
    assert forall|i: int| 0 <= i < path.len() implies (#[trigger] path[i]) < old.len() && old[path[i] as int] == 0
        && colors.update(cursor as int, 2u8)[path[i] as int] == if i < done + 1 { 2u8 } else { 1u8 } by {
        if i != done { assert(path[i] != cursor); }
    }
}

pub proof fn completed_path_restores_closed_resolution(parents: Seq<u32>, old: Seq<u8>, colors: Seq<u8>, path: Seq<u32>, start: u32, anchor: u32)
    requires shape(parents), old.len() == parents.len(), no_pending(old), closed(parents, old),
        path_chain(parents, path, start, anchor), resolved_prefix(old, colors, path, path.len()), old[anchor as int] == 2,
    ensures no_pending(colors), closed(parents, colors),
        forall|n: int| 0 <= n < old.len() && (#[trigger] old[n]) == 2 ==> colors[n] == 2,
{
    reveal(shape); reveal(no_pending); reveal(closed); reveal(path_chain); reveal(resolved_prefix);
    assert(!path.contains(anchor));
    assert forall|n: int| 0 <= n < colors.len() implies (#[trigger] colors[n]) == 0 || colors[n] == 2 by {
        if path.contains(n as u32) {
            let i = choose|i: int| 0 <= i < path.len() && path[i] == n as u32;
            assert(colors[path[i] as int] == 2);
        }
    }
    assert forall|n: int| 0 <= n < colors.len() && (#[trigger] colors[n]) == 2 implies colors[parents[n] as int] == 2 by {
        if path.contains(n as u32) {
            let i = choose|i: int| 0 <= i < path.len() && path[i] == n as u32;
            if i + 1 < path.len() { assert(parents[n] == path[i + 1]); }
            else { assert(parents[n] == anchor); }
        } else {
            assert(old[n] == 2 && old[parents[n] as int] == 2);
            assert(!path.contains(parents[n]));
        }
    }
    assert forall|n: int| 0 <= n < old.len() && (#[trigger] old[n]) == 2 implies colors[n] == 2 by {
        assert(!path.contains(n as u32));
    }
}

}
