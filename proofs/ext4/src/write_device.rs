// SPDX-License-Identifier: MPL-2.0

//! Per-write persistence ledger for the serial writer. A successful flush
//! persists every earlier issued write; abort does not cancel pending effects.
//! Concrete byte projection and hardware refinement are separate layers.

use vstd::prelude::*;
use crate::{write_protocol::{self, Phase, State}, write_io, recovery_io::CommandView};

verus! {

pub open spec fn total(count: nat) -> nat { 2 * count + 11 }

pub open spec fn is_write(k: nat, count: nat) -> bool {
    k == 0 || k == 2 || 4 <= k < 5 + count || k == 6 + count
        || 8 + count <= k < 8 + 2 * count || k == 9 + 2 * count
}

pub open spec fn is_fence(k: nat, count: nat) -> bool {
    k == 1 || k == 3 || k == 5 + count || k == 7 + count || k == 8 + 2 * count || k == 10 + 2 * count
}

pub open spec fn fence_after(k: nat, count: nat) -> nat {
    if k == 0 { 1 } else if k == 2 { 3 } else if 4 <= k < 5 + count { 5 + count }
    else if k == 6 + count { 7 + count } else if 8 + count <= k < 8 + 2 * count { 8 + 2 * count }
    else { 10 + 2 * count }
}

pub open spec fn at(k: nat, count: nat) -> State {
    let phase = if k == 0 { Phase::MarkDirty } else if k == 1 { Phase::DirtyFence }
        else if k == 2 { Phase::Activate } else if k == 3 { Phase::ActivationFence }
        else if k == 4 { Phase::Descriptor } else if 5 <= k < 5 + count { Phase::Payloads }
        else if k == 5 + count { Phase::LogFence } else if k == 6 + count { Phase::Commit }
        else if k == 7 + count { Phase::CommitFence } else if 8 + count <= k < 8 + 2 * count { Phase::Homes }
        else if k == 8 + 2 * count { Phase::HomeFence } else if k == 9 + 2 * count { Phase::Retire }
        else if k == 10 + 2 * count { Phase::RetirementFence } else { Phase::Done };
    let cursor = if 5 <= k < 5 + count { (k - 5) as usize }
        else if 8 + count <= k < 8 + 2 * count { (k - (8 + count)) as usize } else { 0usize };
    State { phase, cursor, request: k as u64, pending: false, faulted: false }
}

pub proof fn command_index_refines_the_executable_phase(v: write_io::Images, state: State)
    requires write_io::valid_images(v), write_protocol::wf(state, v.tx.payloads.len()),
    ensures write_io::expected(v, state) == write_io::expected(v, at(write_protocol::completed_count(state, v.tx.payloads.len()), v.tx.payloads.len())),
        !(state.phase is Done) ==> (is_fence(write_protocol::completed_count(state, v.tx.payloads.len()), v.tx.payloads.len())
            <==> write_io::expected(v, state) is Flush),
{
}

pub struct Machine { pub io: State, pub issued: Set<nat>, pub stable: Set<nat> }
pub enum Event { Issue, Complete(bool), Persist(nat), Abort }

pub open spec fn inv(m: Machine, count: nat) -> bool {
    let cursor = write_protocol::completed_count(m.io, count);
    &&& write_protocol::wf(m.io, count)
    &&& m.stable.subset_of(m.issued)
    &&& (forall|k: nat| #[trigger] m.issued.contains(k) ==> is_write(k, count) && k <= cursor)
    &&& (forall|k: nat| is_write(k, count) && k < cursor ==> #[trigger] m.issued.contains(k))
    &&& (!m.io.faulted && !m.io.pending ==> !m.issued.contains(cursor))
    &&& (m.io.pending && is_write(cursor, count) ==> m.issued.contains(cursor))
    &&& (forall|k: nat| is_write(k, count) && fence_after(k, count) < cursor ==> #[trigger] m.stable.contains(k))
}

pub open spec fn initial() -> Machine {
    Machine { io: write_protocol::initial(), issued: Set::empty(), stable: Set::empty() }
}

pub open spec fn enabled(m: Machine, event: Event) -> bool {
    match event {
        Event::Issue => !m.io.pending && !m.io.faulted && !(m.io.phase is Done),
        Event::Complete(_) => m.io.pending,
        Event::Persist(k) => m.issued.contains(k) && !m.stable.contains(k),
        Event::Abort => true,
    }
}

pub open spec fn next(m: Machine, event: Event, count: nat) -> Machine {
    let cursor = write_protocol::completed_count(m.io, count);
    match event {
        Event::Issue => Machine { io: write_protocol::started(m.io),
            issued: if is_write(cursor, count) { m.issued.insert(cursor) } else { m.issued }, ..m },
        Event::Complete(success) => Machine { io: write_protocol::completed(m.io, count, success),
            stable: if success && is_fence(cursor, count) { m.issued } else { m.stable }, ..m },
        Event::Persist(k) => Machine { stable: m.stable.insert(k), ..m },
        Event::Abort => Machine { io: State { faulted: true, ..m.io }, ..m },
    }
}

pub proof fn initialization(count: nat)
    requires 1 <= count <= 250,
    ensures inv(initial(), count),
{
    write_protocol::initialization(count);
}

proof fn fence_properties(k: nat, count: nat)
    requires 1 <= count <= 250, is_write(k, count),
    ensures k < fence_after(k, count) < total(count), is_fence(fence_after(k, count), count), !is_fence(k, count),
{
}

#[verifier::rlimit(20)]
pub proof fn every_event_preserves(m: Machine, event: Event, count: nat)
    requires inv(m, count), enabled(m, event),
    ensures inv(next(m, event, count), count),
{
    let cursor = write_protocol::completed_count(m.io, count);
    let n = next(m, event, count);
    let next_cursor = write_protocol::completed_count(n.io, count);
    match event {
        Event::Issue => {
            assert(write_protocol::wf(n.io, count));
            assert(cursor == next_cursor);
        },
        Event::Complete(success) => {
            if success && !m.io.faulted { assert(next_cursor == cursor + 1); }
            else { assert(next_cursor == cursor); }
            assert(write_protocol::wf(n.io, count));
            assert forall|k: nat| is_write(k, count) && fence_after(k, count) < next_cursor implies #[trigger] n.stable.contains(k) by {
                fence_properties(k, count);
                if fence_after(k, count) == cursor {
                    assert(success && is_fence(cursor, count));
                    assert(m.issued.contains(k));
                } else { assert(m.stable.contains(k)); }
            }
        },
        Event::Persist(k) => { },
        Event::Abort => { },
    }
}

pub open spec fn execution(states: Seq<Machine>, events: Seq<Event>, count: nat) -> bool {
    &&& states.len() == events.len() + 1
    &&& (forall|i: int| 0 <= i < events.len() ==> #[trigger] enabled(states[i], events[i]))
    &&& (forall|i: int| 0 <= i < events.len() ==> states[i + 1] == #[trigger] next(states[i], events[i], count))
}

proof fn at_cut(states: Seq<Machine>, events: Seq<Event>, count: nat, cut: nat)
    requires execution(states, events, count), inv(states[0], count), cut < states.len(),
    ensures inv(states[cut as int], count),
    decreases cut,
{
    if cut > 0 {
        at_cut(states, events, count, (cut - 1) as nat);
        every_event_preserves(states[cut as int - 1], events[cut as int - 1], count);
    }
}

pub proof fn every_finite_io_interleaving(states: Seq<Machine>, events: Seq<Event>, count: nat)
    requires execution(states, events, count), inv(states[0], count),
    ensures forall|i: int| 0 <= i < states.len() ==> #[trigger] inv(states[i], count),
{
    assert forall|i: int| 0 <= i < states.len() implies #[trigger] inv(states[i], count) by {
        at_cut(states, events, count, i as nat);
    }
}

pub proof fn commit_issue_requires_every_log_image_stable(m: Machine, count: nat)
    requires inv(m, count), m.issued.contains(6 + count),
    ensures forall|k: nat| 4 <= k < 5 + count ==> #[trigger] m.stable.contains(k),
{
}

pub proof fn home_issue_requires_a_stable_commit(m: Machine, count: nat, index: nat)
    requires inv(m, count), index < count, m.issued.contains(8 + count + index),
    ensures m.stable.contains(6 + count),
{
}

pub proof fn retirement_issue_requires_every_home_image_stable(m: Machine, count: nat)
    requires inv(m, count), m.issued.contains(9 + 2 * count),
    ensures forall|i: nat| i < count ==> #[trigger] m.stable.contains(8 + count + i),
{
}

pub proof fn successful_completion_is_durable_and_has_no_late_persistence(m: Machine, count: nat)
    requires inv(m, count), m.io.phase is Done, !m.io.pending, !m.io.faulted,
    ensures m.stable == m.issued,
        forall|k: nat| is_write(k, count) ==> #[trigger] m.stable.contains(k),
        forall|k: nat| !#[trigger] enabled(m, Event::Persist(k)),
        !enabled(m, Event::Issue), !enabled(m, Event::Complete(true)),
{
    assert forall|k: nat| is_write(k, count) implies #[trigger] m.stable.contains(k) by { fence_properties(k, count); }
    assert(m.stable =~= m.issued);
}

pub proof fn abort_is_not_cancellation(m: Machine, count: nat)
    requires inv(m, count),
    ensures next(m, Event::Abort, count).issued == m.issued, next(m, Event::Abort, count).stable == m.stable,
        next(m, Event::Abort, count).io.pending == m.io.pending, !enabled(next(m, Event::Abort, count), Event::Issue),
{
}

proof fn prepend_execution(first: Machine, event: Event, states: Seq<Machine>, events: Seq<Event>, count: nat)
    requires execution(states, events, count), enabled(first, event), states[0] == next(first, event, count),
    ensures execution(seq![first] + states, seq![event] + events, count),
{
    let ss = seq![first] + states;
    let ee = seq![event] + events;
    assert forall|i: int| 0 <= i < ee.len() implies #[trigger] enabled(ss[i], ee[i]) by {
        if i > 0 { assert(enabled(states[i - 1], events[i - 1])); }
    }
    assert forall|i: int| 0 <= i < ee.len() implies ss[i + 1] == #[trigger] next(ss[i], ee[i], count) by {
        if i > 0 { assert(states[i] == next(states[i - 1], events[i - 1], count)); }
    }
}

proof fn append_execution(states: Seq<Machine>, events: Seq<Event>, event: Event, count: nat)
    requires execution(states, events, count), enabled(states.last(), event),
    ensures execution(states.push(next(states.last(), event, count)), events.push(event), count),
{
    let ss = states.push(next(states.last(), event, count));
    let ee = events.push(event);
    assert forall|i: int| 0 <= i < ee.len() implies #[trigger] enabled(ss[i], ee[i]) by {
        if i < events.len() { assert(enabled(states[i], events[i])); }
    }
    assert forall|i: int| 0 <= i < ee.len() implies ss[i + 1] == #[trigger] next(ss[i], ee[i], count) by {
        if i < events.len() { assert(states[i + 1] == next(states[i], events[i], count)); }
    }
}

pub proof fn pending_writes_have_a_finite_persistence_trace(m: Machine, count: nat) -> (r: (Seq<Machine>, Seq<Event>))
    requires inv(m, count),
    ensures execution(r.0, r.1, count), r.0[0] == m,
        r.0.last().io == m.io, r.0.last().issued == m.issued, r.0.last().stable == m.issued,
        forall|i: int| 0 <= i < r.1.len() ==> (#[trigger] r.1[i]) is Persist,
    decreases m.issued.difference(m.stable).len(),
{
    let pending = m.issued.difference(m.stable);
    if pending.is_empty() {
        assert forall|k: nat| m.issued.contains(k) implies #[trigger] m.stable.contains(k) by {
            assert(!pending.contains(k));
        }
        assert(m.stable =~= m.issued);
        (seq![m], Seq::empty())
    } else {
        assert(exists|k: nat| #[trigger] pending.contains(k));
        let k = choose|k: nat| pending.contains(k);
        assert(enabled(m, Event::Persist(k)));
        let n = next(m, Event::Persist(k), count);
        every_event_preserves(m, Event::Persist(k), count);
        assert(n.issued.difference(n.stable) =~= pending.remove(k));
        assert(pending.remove(k).len() < pending.len());
        let (states, events) = pending_writes_have_a_finite_persistence_trace(n, count);
        prepend_execution(m, Event::Persist(k), states, events, count);
        let ss = seq![m] + states;
        let ee = seq![Event::Persist(k)] + events;
        assert(ss.last() == states.last());
        assert forall|i: int| 0 <= i < ee.len() implies (#[trigger] ee[i]) is Persist by {
            if i > 0 { assert(events[i - 1] is Persist); }
        }
        (ss, ee)
    }
}

pub proof fn a_successful_flush_has_a_finite_persistence_refinement(m: Machine, count: nat) -> (r: (Seq<Machine>, Seq<Event>))
    requires inv(m, count), m.io.pending, is_fence(write_protocol::completed_count(m.io, count), count),
    ensures execution(r.0, r.1, count), r.0[0] == m, r.0.last() == next(m, Event::Complete(true), count),
        r.1.len() > 0, r.1.last() == Event::Complete(true),
        forall|i: int| 0 <= i < r.1.len() - 1 ==> (#[trigger] r.1[i]) is Persist,
        r.0[r.0.len() as int - 2].stable == r.0.last().stable,
{
    let (states, events) = pending_writes_have_a_finite_persistence_trace(m, count);
    assert(enabled(states.last(), Event::Complete(true)));
    append_execution(states, events, Event::Complete(true), count);
    assert(next(states.last(), Event::Complete(true), count) == next(m, Event::Complete(true), count));
    (states.push(next(m, Event::Complete(true), count)), events.push(Event::Complete(true)))
}

pub proof fn failure_free_io_has_a_finite_successful_execution(m: Machine, count: nat) -> (r: (Seq<Machine>, Seq<Event>))
    requires inv(m, count), !m.io.pending, !m.io.faulted,
    ensures execution(r.0, r.1, count), r.0[0] == m,
        r.0.last().io.phase is Done, !r.0.last().io.pending, !r.0.last().io.faulted,
        r.1.len() == 2 * write_protocol::remaining(m.io, count),
    decreases write_protocol::remaining(m.io, count),
{
    if m.io.phase is Done { (seq![m], Seq::empty()) }
    else {
        assert(enabled(m, Event::Issue));
        let issued = next(m, Event::Issue, count);
        every_event_preserves(m, Event::Issue, count);
        let completed = next(issued, Event::Complete(true), count);
        every_event_preserves(issued, Event::Complete(true), count);
        write_protocol::successful_pair_preserves_and_makes_progress(m.io, count);
        let (states, events) = failure_free_io_has_a_finite_successful_execution(completed, count);
        prepend_execution(issued, Event::Complete(true), states, events, count);
        let ss = seq![issued] + states;
        let ee = seq![Event::Complete(true)] + events;
        prepend_execution(m, Event::Issue, ss, ee, count);
        (seq![m] + ss, seq![Event::Issue] + ee)
    }
}

}
