// SPDX-License-Identifier: MPL-2.0

//! Per-operation persistence ledger for independently scheduled commit,
//! checkpoint and tail lanes. Completion of a write is not persistence.

use vstd::prelude::*;
use crate::{journal_program::{self, Lane, State}, journal_window::{self, Operation}};

verus! {

pub open spec fn legal(op: Operation, shape: Seq<nat>) -> bool {
    journal_window::is_write(op) && match op {
        Operation::Descriptor(t) | Operation::Commit(t) => t < shape.len(),
        Operation::Payload(t, k) | Operation::Home(t, k) => t < shape.len() && k < shape[t as int],
        Operation::Tail(k) => 0 < k <= shape.len(),
        Operation::Dirty | Operation::Activate => true,
        _ => false,
    }
}

pub open spec fn past(s: State, op: Operation, shape: Seq<nat>) -> bool {
    match op {
        Operation::Dirty => s.bootstrap > 0,
        Operation::Activate => s.bootstrap > 2,
        Operation::Descriptor(t) => t < s.commit || t == s.commit && s.commit_cursor > 0,
        Operation::Payload(t, k) => t < s.commit || t == s.commit && s.commit_cursor > k + 1,
        Operation::Commit(t) => t < s.commit || t == s.commit && s.commit_cursor > shape[t as int] + 2,
        Operation::Home(t, k) => t < s.checkpoint || t == s.checkpoint && s.home_cursor > k,
        _ => false,
    }
}

pub open spec fn bounded(s: State, op: Operation, shape: Seq<nat>) -> bool {
    match op {
        Operation::Tail(k) => k <= s.retired || k == s.tail_goal
            && (s.tail_phase == 1 || s.pending && s.lane is Tail || s.faulted),
        _ => past(s, op, shape) || (s.pending || s.faulted)
            && journal_program::position_ready(s, s.lane, shape) && op == journal_window::pending_operation(s, shape),
    }
}

pub open spec fn mandatory(s: State, op: Operation, shape: Seq<nat>) -> bool {
    past(s, op, shape) || match op { Operation::Tail(k) => k == s.retired && k > 0 || k == s.tail_goal && s.tail_phase == 1, _ => false }
}

pub open spec fn fenced(s: State, op: Operation, shape: Seq<nat>) -> bool {
    match op {
        Operation::Dirty => s.bootstrap > 1,
        Operation::Activate => s.bootstrap > 3,
        Operation::Descriptor(t) | Operation::Payload(t, _) => t < s.commit || t == s.commit && s.commit_cursor >= shape[t as int] + 2,
        Operation::Commit(t) => t < s.commit,
        Operation::Home(t, _) => t < s.checkpoint,
        Operation::Tail(k) => k <= s.retired,
        _ => false,
    }
}

pub struct Machine { pub io: State, pub issued: Set<Operation>, pub stable: Set<Operation> }
pub enum Event { Issue(Lane), Complete(bool), Persist(Operation), Abort }

pub open spec fn inv(m: Machine, shape: Seq<nat>) -> bool {
    &&& journal_program::wf(m.io, shape) && m.stable.subset_of(m.issued)
    &&& (forall|op: Operation| #[trigger] m.issued.contains(op) ==> legal(op, shape) && bounded(m.io, op, shape))
    &&& (forall|op: Operation| legal(op, shape) && mandatory(m.io, op, shape) ==> #[trigger] m.issued.contains(op))
    &&& (m.io.pending && journal_window::is_write(journal_window::pending_operation(m.io, shape))
        ==> m.issued.contains(journal_window::pending_operation(m.io, shape)))
    &&& (forall|op: Operation| m.issued.contains(op) && fenced(m.io, op, shape) ==> #[trigger] m.stable.contains(op))
}

pub open spec fn initial() -> Machine {
    Machine { io: journal_program::initial(), issued: Set::empty(), stable: Set::empty() }
}

pub open spec fn enabled(m: Machine, e: Event, shape: Seq<nat>) -> bool {
    match e {
        Event::Issue(lane) => journal_program::enabled(m.io, lane, shape),
        Event::Complete(_) => m.io.pending,
        Event::Persist(op) => m.issued.contains(op) && !m.stable.contains(op),
        Event::Abort => true,
    }
}

pub open spec fn next(m: Machine, e: Event, shape: Seq<nat>) -> Machine {
    match e {
        Event::Issue(lane) => {
            let state = journal_program::started(m.io, lane);
            let op = journal_window::pending_operation(state, shape);
            Machine { io: state, issued: if journal_window::is_write(op) { m.issued.insert(op) } else { m.issued }, ..m }
        },
        Event::Complete(success) => Machine { io: journal_program::completed(m.io, shape, success),
            stable: if success && !journal_window::is_write(journal_window::pending_operation(m.io, shape)) { m.issued } else { m.stable }, ..m },
        Event::Persist(op) => Machine { stable: m.stable.insert(op), ..m },
        Event::Abort => Machine { io: State { faulted: true, ..m.io }, ..m },
    }
}

pub proof fn initialization(shape: Seq<nat>)
    requires journal_program::counts_valid(shape),
    ensures inv(initial(), shape),
{ journal_program::initial_window_state_is_valid(shape); }

pub proof fn dispatch_never_reissues_a_write(m: Machine, lane: Lane, shape: Seq<nat>)
    requires inv(m, shape), enabled(m, Event::Issue(lane), shape),
    ensures journal_window::is_write(journal_window::pending_operation(journal_program::started(m.io, lane), shape))
        ==> !m.issued.contains(journal_window::pending_operation(journal_program::started(m.io, lane), shape)),
{
    let op = journal_window::pending_operation(journal_program::started(m.io, lane), shape);
    if m.issued.contains(op) { assert(bounded(m.io, op, shape)); }
    match lane { Lane::Bootstrap => {}, Lane::Commit => {}, Lane::Checkpoint => {}, Lane::Tail => {} }
}

proof fn one_operation_preserves_bounds(m: Machine, e: Event, shape: Seq<nat>, op: Operation)
    requires inv(m, shape), enabled(m, e, shape),
    ensures next(m, e, shape).issued.contains(op) ==> legal(op, shape) && bounded(next(m, e, shape).io, op, shape),
        legal(op, shape) && mandatory(next(m, e, shape).io, op, shape) ==> next(m, e, shape).issued.contains(op),
        next(m, e, shape).issued.contains(op) && fenced(next(m, e, shape).io, op, shape) ==> next(m, e, shape).stable.contains(op),
{
    match e {
        Event::Issue(lane) => { match lane { Lane::Bootstrap => {}, Lane::Commit => {}, Lane::Checkpoint => {}, Lane::Tail => {} } },
        Event::Complete(success) => { match m.io.lane { Lane::Bootstrap => {}, Lane::Commit => {}, Lane::Checkpoint => {}, Lane::Tail => {} } },
        _ => {},
    }
    match op {
        Operation::Dirty | Operation::Activate | Operation::Descriptor(_) | Operation::Payload(_, _)
            | Operation::Commit(_) | Operation::Home(_, _) | Operation::Tail(_) => {},
        _ => {},
    }
}

pub proof fn every_event_preserves(m: Machine, e: Event, shape: Seq<nat>)
    requires inv(m, shape), enabled(m, e, shape),
    ensures inv(next(m, e, shape), shape),
{
    let n = next(m, e, shape);
    match e {
        Event::Issue(lane) => { journal_program::starting_a_window_request_preserves_order(m.io, lane, shape); },
        Event::Complete(success) => { journal_program::completing_a_window_request_preserves_order(m.io, shape, success); },
        Event::Abort => { journal_program::aborting_keeps_the_request_and_all_committed_frontiers(m.io, shape); },
        _ => {},
    }
    assert forall|op: Operation| #[trigger] n.issued.contains(op) implies legal(op, shape) && bounded(n.io, op, shape) by {
        one_operation_preserves_bounds(m, e, shape, op);
    }
    assert forall|op: Operation| legal(op, shape) && mandatory(n.io, op, shape) implies #[trigger] n.issued.contains(op) by {
        one_operation_preserves_bounds(m, e, shape, op);
    }
    assert forall|op: Operation| n.issued.contains(op) && fenced(n.io, op, shape) implies #[trigger] n.stable.contains(op) by {
        one_operation_preserves_bounds(m, e, shape, op);
    }
}

pub proof fn commit_issue_requires_the_complete_log_stable(m: Machine, shape: Seq<nat>, t: usize)
    requires inv(m, shape), m.issued.contains(Operation::Commit(t)),
    ensures m.stable.contains(Operation::Descriptor(t)),
        forall|k: usize| k < shape[t as int] ==> #[trigger] m.stable.contains(Operation::Payload(t, k)),
{
    assert forall|k: usize| k < shape[t as int] implies #[trigger] m.stable.contains(Operation::Payload(t, k)) by {
        assert(m.issued.contains(Operation::Payload(t, k)));
    }
}

pub proof fn home_issue_requires_a_stable_commit(m: Machine, shape: Seq<nat>, t: usize, k: usize)
    requires inv(m, shape), m.issued.contains(Operation::Home(t, k)),
    ensures m.stable.contains(Operation::Commit(t)),
{ assert(m.issued.contains(Operation::Commit(t))); }

pub proof fn tail_issue_requires_the_entire_checkpoint_prefix_stable(m: Machine, shape: Seq<nat>, goal: usize)
    requires inv(m, shape), m.issued.contains(Operation::Tail(goal)),
    ensures forall|t: usize, k: usize| t < goal && k < shape[t as int] ==> #[trigger] m.stable.contains(Operation::Home(t, k)),
{
    assert forall|t: usize, k: usize| t < goal && k < shape[t as int] implies #[trigger] m.stable.contains(Operation::Home(t, k)) by {
        assert(m.issued.contains(Operation::Home(t, k)));
    }
}

pub proof fn successful_completion_has_no_late_persistence(m: Machine, shape: Seq<nat>)
    requires inv(m, shape), journal_program::finished(m.io, shape),
    ensures m.stable == m.issued,
        forall|op: Operation| !#[trigger] enabled(m, Event::Persist(op), shape),
        forall|lane: Lane| !#[trigger] enabled(m, Event::Issue(lane), shape),
{
    assert forall|op: Operation| m.issued.contains(op) implies #[trigger] m.stable.contains(op) by {
        assert(legal(op, shape) && bounded(m.io, op, shape));
    }
    assert(m.stable =~= m.issued);
}

pub open spec fn execution(states: Seq<Machine>, events: Seq<Event>, shape: Seq<nat>) -> bool {
    states.len() == events.len() + 1
        && (forall|i: int| 0 <= i < events.len() ==> #[trigger] enabled(states[i], events[i], shape))
        && (forall|i: int| 0 <= i < events.len() ==> states[i + 1] == #[trigger] next(states[i], events[i], shape))
}

proof fn at_cut(states: Seq<Machine>, events: Seq<Event>, shape: Seq<nat>, cut: nat)
    requires execution(states, events, shape), inv(states[0], shape), cut < states.len(),
    ensures inv(states[cut as int], shape),
    decreases cut,
{
    if cut > 0 {
        at_cut(states, events, shape, (cut - 1) as nat);
        every_event_preserves(states[cut as int - 1], events[cut as int - 1], shape);
    }
}

pub proof fn every_finite_lane_and_persistence_interleaving(states: Seq<Machine>, events: Seq<Event>, shape: Seq<nat>)
    requires execution(states, events, shape), inv(states[0], shape),
    ensures forall|i: int| 0 <= i < states.len() ==> #[trigger] inv(states[i], shape),
{
    assert forall|i: int| 0 <= i < states.len() implies #[trigger] inv(states[i], shape) by { at_cut(states, events, shape, i as nat); }
}

pub proof fn abort_preserves_outstanding_effects(m: Machine, shape: Seq<nat>)
    requires inv(m, shape),
    ensures next(m, Event::Abort, shape).issued == m.issued, next(m, Event::Abort, shape).stable == m.stable,
        next(m, Event::Abort, shape).io.pending == m.io.pending,
        forall|lane: Lane| !#[trigger] enabled(next(m, Event::Abort, shape), Event::Issue(lane), shape),
{ }

pub proof fn an_acknowledged_prefix_has_durable_commit_records(m: Machine, shape: Seq<nat>)
    requires inv(m, shape),
    ensures forall|t: usize| t < m.io.commit ==> #[trigger] m.stable.contains(Operation::Commit(t)),
{
    assert forall|t: usize| t < m.io.commit implies #[trigger] m.stable.contains(Operation::Commit(t)) by {
        assert(m.issued.contains(Operation::Commit(t)));
    }
}

proof fn prepend_execution(first: Machine, event: Event, states: Seq<Machine>, events: Seq<Event>, shape: Seq<nat>)
    requires execution(states, events, shape), enabled(first, event, shape), states[0] == next(first, event, shape),
    ensures execution(seq![first] + states, seq![event] + events, shape),
{
    let ss = seq![first] + states; let ee = seq![event] + events;
    assert forall|i: int| 0 <= i < ee.len() implies #[trigger] enabled(ss[i], ee[i], shape) by {
        if i > 0 { assert(enabled(states[i - 1], events[i - 1], shape)); }
    }
    assert forall|i: int| 0 <= i < ee.len() implies ss[i + 1] == #[trigger] next(ss[i], ee[i], shape) by {
        if i > 0 { assert(states[i] == next(states[i - 1], events[i - 1], shape)); }
    }
}

proof fn append_execution(states: Seq<Machine>, events: Seq<Event>, event: Event, shape: Seq<nat>)
    requires execution(states, events, shape), enabled(states.last(), event, shape),
    ensures execution(states.push(next(states.last(), event, shape)), events.push(event), shape),
{
    let ss = states.push(next(states.last(), event, shape)); let ee = events.push(event);
    assert forall|i: int| 0 <= i < ee.len() implies #[trigger] enabled(ss[i], ee[i], shape) by {
        if i < events.len() { assert(enabled(states[i], events[i], shape)); }
    }
    assert forall|i: int| 0 <= i < ee.len() implies ss[i + 1] == #[trigger] next(ss[i], ee[i], shape) by {
        if i < events.len() { assert(states[i + 1] == next(states[i], events[i], shape)); }
    }
}

pub proof fn pending_writes_have_a_finite_persistence_trace(m: Machine, shape: Seq<nat>) -> (r: (Seq<Machine>, Seq<Event>))
    requires inv(m, shape),
    ensures execution(r.0, r.1, shape), r.0[0] == m,
        r.0.last().io == m.io, r.0.last().issued == m.issued, r.0.last().stable == m.issued,
        forall|i: int| 0 <= i < r.1.len() ==> (#[trigger] r.1[i]) is Persist,
    decreases m.issued.difference(m.stable).len(),
{
    let pending = m.issued.difference(m.stable);
    if pending.is_empty() {
        assert forall|op: Operation| m.issued.contains(op) implies #[trigger] m.stable.contains(op) by { assert(!pending.contains(op)); }
        assert(m.stable =~= m.issued);
        (seq![m], Seq::empty())
    } else {
        assert(exists|op: Operation| #[trigger] pending.contains(op));
        let op = choose|op: Operation| pending.contains(op);
        let n = next(m, Event::Persist(op), shape);
        every_event_preserves(m, Event::Persist(op), shape);
        assert(n.issued.difference(n.stable) =~= pending.remove(op));
        assert(pending.remove(op).len() < pending.len());
        let (states, events) = pending_writes_have_a_finite_persistence_trace(n, shape);
        prepend_execution(m, Event::Persist(op), states, events, shape);
        let ss = seq![m] + states; let ee = seq![Event::Persist(op)] + events;
        assert(ss.last() == states.last());
        assert forall|i: int| 0 <= i < ee.len() implies (#[trigger] ee[i]) is Persist by {
            if i > 0 { assert(events[i - 1] is Persist); }
        }
        (ss, ee)
    }
}

pub proof fn every_successful_flush_has_a_finite_persistence_refinement(m: Machine, shape: Seq<nat>) -> (r: (Seq<Machine>, Seq<Event>))
    requires inv(m, shape), m.io.pending, !journal_window::is_write(journal_window::pending_operation(m.io, shape)),
    ensures execution(r.0, r.1, shape), r.0[0] == m, r.0.last() == next(m, Event::Complete(true), shape),
        r.1.len() > 0, r.1.last() == Event::Complete(true),
        forall|i: int| 0 <= i < r.1.len() - 1 ==> (#[trigger] r.1[i]) is Persist,
        r.0[r.0.len() as int - 2].stable == r.0.last().stable,
{
    let (states, events) = pending_writes_have_a_finite_persistence_trace(m, shape);
    append_execution(states, events, Event::Complete(true), shape);
    assert(next(states.last(), Event::Complete(true), shape) == next(m, Event::Complete(true), shape));
    (states.push(next(m, Event::Complete(true), shape)), events.push(Event::Complete(true)))
}

pub proof fn failure_free_window_has_a_finite_successful_execution(m: Machine, shape: Seq<nat>) -> (r: (Seq<Machine>, Seq<Event>))
    requires inv(m, shape), !m.io.pending, !m.io.faulted,
        m.io.request as nat + crate::journal_window_progress::remaining(m.io, shape) <= 18446744073709551615,
    ensures execution(r.0, r.1, shape), r.0[0] == m,
        journal_program::finished(r.0.last().io, shape), r.0.last().stable == r.0.last().issued,
        r.1.len() <= 2 * crate::journal_window_progress::remaining(m.io, shape),
        !journal_program::finished(m.io, shape) ==> r.1.len() > 0,
    decreases crate::journal_window_progress::remaining(m.io, shape),
{
    if journal_program::finished(m.io, shape) {
        successful_completion_has_no_late_persistence(m, shape);
        (seq![m], Seq::empty())
    } else {
        crate::journal_window_progress::zero_work_characterizes_success(m.io, shape);
        crate::journal_window_progress::unfinished_work_has_an_enabled_lane(m.io, shape);
        let lane = crate::journal_window_progress::selected(m.io, shape);
        let issued = next(m, Event::Issue(lane), shape);
        every_event_preserves(m, Event::Issue(lane), shape);
        let completed = next(issued, Event::Complete(true), shape);
        every_event_preserves(issued, Event::Complete(true), shape);
        crate::journal_window_progress::every_successful_request_strictly_reduces_work(issued.io, shape);
        let (states, events) = failure_free_window_has_a_finite_successful_execution(completed, shape);
        prepend_execution(issued, Event::Complete(true), states, events, shape);
        let ss = seq![issued] + states; let ee = seq![Event::Complete(true)] + events;
        prepend_execution(m, Event::Issue(lane), ss, ee, shape);
        assert((seq![m] + ss).last() == states.last());
        (seq![m] + ss, seq![Event::Issue(lane)] + ee)
    }
}

}
