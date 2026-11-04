// SPDX-License-Identifier: MPL-2.0

//! Finite failure-free scheduler progress; this is not a runtime fairness or
//! device-liveness claim. Each successfully completed request consumes work.

use vstd::prelude::*;
use crate::journal_program::{self, Lane, State};

verus! {

pub open spec fn prefix_cost(shape: Seq<nat>, prefix: nat, extra: nat) -> nat
    decreases prefix,
{
    if prefix == 0 { 0 } else { prefix_cost(shape, (prefix - 1) as nat, extra) + shape[prefix as int - 1] + extra }
}

pub open spec fn remaining(s: State, shape: Seq<nat>) -> nat {
    ((4 - s.bootstrap) + (prefix_cost(shape, shape.len(), 4) - prefix_cost(shape, s.commit as nat, 4) - s.commit_cursor)
        + (prefix_cost(shape, shape.len(), 1) - prefix_cost(shape, s.checkpoint as nat, 1) - s.home_cursor)
        + 2 * (shape.len() - s.retired) - s.tail_phase) as nat
}

proof fn prefix_step(shape: Seq<nat>, prefix: nat, extra: nat)
    requires prefix < shape.len(),
    ensures prefix_cost(shape, prefix + 1, extra) == prefix_cost(shape, prefix, extra) + shape[prefix as int] + extra,
{ }

proof fn prefix_monotone(shape: Seq<nat>, a: nat, b: nat, extra: nat)
    requires a <= b <= shape.len(),
    ensures prefix_cost(shape, a, extra) <= prefix_cost(shape, b, extra),
    decreases b - a,
{
    if a < b { prefix_monotone(shape, a, (b - 1) as nat, extra); prefix_step(shape, (b - 1) as nat, extra); }
}

proof fn lane_costs_are_nonnegative(s: State, shape: Seq<nat>)
    requires journal_program::wf(s, shape),
    ensures prefix_cost(shape, s.commit as nat, 4) + s.commit_cursor <= prefix_cost(shape, shape.len(), 4),
        prefix_cost(shape, s.checkpoint as nat, 1) + s.home_cursor <= prefix_cost(shape, shape.len(), 1),
        s.commit < shape.len() ==> prefix_cost(shape, s.commit as nat, 4) + s.commit_cursor < prefix_cost(shape, shape.len(), 4),
        s.checkpoint < shape.len() ==> prefix_cost(shape, s.checkpoint as nat, 1) + s.home_cursor < prefix_cost(shape, shape.len(), 1),
        2 * (shape.len() - s.retired) >= s.tail_phase,
{
    if s.commit < shape.len() {
        prefix_step(shape, s.commit as nat, 4); prefix_monotone(shape, s.commit as nat + 1, shape.len(), 4);
    }
    if s.checkpoint < shape.len() {
        prefix_step(shape, s.checkpoint as nat, 1); prefix_monotone(shape, s.checkpoint as nat + 1, shape.len(), 1);
    }
}

pub proof fn zero_work_characterizes_success(s: State, shape: Seq<nat>)
    requires journal_program::wf(s, shape), !s.pending, !s.faulted,
    ensures remaining(s, shape) == 0 <==> journal_program::finished(s, shape),
{ lane_costs_are_nonnegative(s, shape); }

pub proof fn every_successful_request_strictly_reduces_work(s: State, shape: Seq<nat>)
    requires journal_program::wf(s, shape), s.pending, !s.faulted,
    ensures remaining(journal_program::completed(s, shape, true), shape) < remaining(s, shape),
{
    journal_program::completing_a_window_request_preserves_order(s, shape, true);
    lane_costs_are_nonnegative(s, shape);
    lane_costs_are_nonnegative(journal_program::completed(s, shape, true), shape);
    match s.lane {
        Lane::Commit => { prefix_step(shape, s.commit as nat, 4); },
        Lane::Checkpoint => { prefix_step(shape, s.checkpoint as nat, 1); },
        _ => {},
    }
}

pub open spec fn selected(s: State, shape: Seq<nat>) -> Lane {
    if s.bootstrap < 4 { Lane::Bootstrap } else if s.commit < shape.len() { Lane::Commit }
    else if s.checkpoint < shape.len() { Lane::Checkpoint } else { Lane::Tail }
}

pub proof fn unfinished_work_has_an_enabled_lane(s: State, shape: Seq<nat>)
    requires journal_program::wf(s, shape), !s.pending, !s.faulted, remaining(s, shape) > 0,
        s.request as nat + remaining(s, shape) <= 18446744073709551615,
    ensures journal_program::enabled(s, selected(s, shape), shape),
        remaining(journal_program::started(s, selected(s, shape)), shape) == remaining(s, shape),
{
    zero_work_characterizes_success(s, shape);
}

proof fn initial_bound(shape: Seq<nat>, prefix: nat)
    requires journal_program::counts_valid(shape), prefix <= shape.len(),
    ensures prefix_cost(shape, prefix, 4) <= prefix * 254, prefix_cost(shape, prefix, 1) <= prefix * 251,
    decreases prefix,
{
    if prefix > 0 {
        initial_bound(shape, (prefix - 1) as nat);
        prefix_step(shape, (prefix - 1) as nat, 4);
        prefix_step(shape, (prefix - 1) as nat, 1);
        assert(shape[prefix as int - 1] <= 250);
    }
}

pub proof fn a_new_window_has_a_small_finite_work_bound(shape: Seq<nat>)
    requires journal_program::counts_valid(shape),
    ensures remaining(journal_program::initial(), shape) <= 32452,
        journal_program::initial().request as nat + remaining(journal_program::initial(), shape) <= 18446744073709551615,
{
    initial_bound(shape, shape.len());
    assert(prefix_cost(shape, shape.len(), 4) <= 16256);
    assert(prefix_cost(shape, shape.len(), 1) <= 16064);
    assert(remaining(journal_program::initial(), shape) == 4 + prefix_cost(shape, shape.len(), 4)
        + prefix_cost(shape, shape.len(), 1) + 2 * shape.len());
}

}
