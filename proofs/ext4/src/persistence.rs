// SPDX-License-Identifier: MPL-2.0

//! Refinement of the logical transaction to per-unit submission, completion,
//! and persistence events. An atomic unit may be smaller than an ext4 block.
//! This is a device-contract model, not a proof of a particular block driver.

use vstd::prelude::*;
use crate::journal::{self, State};
use crate::redo::Disk;

verus! {

pub struct Machine {
    pub tx: State,
    pub payload_done: Set<nat>,
    pub commit_done: bool,
    pub home_issued: Set<nat>,
    pub home_done: Set<nat>,
    pub home_stable: Set<nat>,
    pub retirement_issued: bool,
    pub retirement_done: bool,
}

pub enum Event {
    SubmitPayload(nat), CompletePayload(nat), PersistPayload(nat), PrepareFence,
    SubmitCommit, CompleteCommit, PersistCommit,
    SubmitHome(nat), CompleteHome(nat), PersistHome(nat),
    SubmitRetirement, CompleteRetirement, PersistRetirement, Acknowledge, Abort,
}

pub open spec fn init(before: Disk, patch: Disk) -> Machine {
    Machine { tx: journal::init(before, patch), payload_done: Set::empty(),
        commit_done: false, home_issued: Set::empty(), home_done: Set::empty(),
        home_stable: Set::empty(), retirement_issued: false, retirement_done: false }
}

pub open spec fn inv(m: Machine) -> bool {
    &&& journal::inv(m.tx)
    &&& m.payload_done.subset_of(m.tx.issued)
    &&& (m.tx.prepared ==> m.payload_done == m.tx.patch.dom())
    &&& (m.commit_done ==> m.tx.commit_issued)
    &&& m.home_issued.subset_of(m.tx.patch.dom())
    &&& m.home_done.subset_of(m.home_issued)
    &&& m.home_stable.subset_of(m.home_issued)
    &&& (m.home_issued != Set::<nat>::empty() ==> m.tx.committed)
    &&& (m.retirement_issued ==> m.tx.committed && m.commit_done
        && m.home_issued == m.tx.patch.dom() && m.home_done == m.tx.patch.dom()
        && m.home_stable == m.tx.patch.dom() && m.tx.home == journal::target(m.tx))
    &&& (m.retirement_done ==> m.retirement_issued)
    &&& (m.tx.retired ==> m.retirement_issued)
    &&& (m.tx.acknowledged ==> m.tx.retired && m.retirement_done)
}

pub open spec fn enabled(m: Machine, e: Event) -> bool {
    match e {
        Event::SubmitPayload(u) => !m.tx.aborted && !m.tx.prepared
            && m.tx.patch.dom().contains(u) && !m.tx.issued.contains(u),
        Event::CompletePayload(u) => m.tx.issued.contains(u) && !m.payload_done.contains(u),
        Event::PersistPayload(u) => m.tx.issued.contains(u) && !m.tx.log.dom().contains(u),
        Event::PrepareFence => !m.tx.aborted && m.tx.issued == m.tx.patch.dom()
            && m.tx.log == m.tx.patch && m.payload_done == m.tx.patch.dom(),
        Event::SubmitCommit => !m.tx.aborted && m.tx.prepared && !m.tx.commit_issued,
        Event::CompleteCommit => m.tx.commit_issued && !m.commit_done,
        Event::PersistCommit => m.tx.commit_issued && !m.tx.committed,
        Event::SubmitHome(u) => m.tx.committed && m.tx.patch.dom().contains(u)
            && !m.home_issued.contains(u),
        Event::CompleteHome(u) => m.home_issued.contains(u) && !m.home_done.contains(u),
        Event::PersistHome(u) => m.home_issued.contains(u) && !m.home_stable.contains(u),
        Event::SubmitRetirement => m.tx.committed && m.commit_done && !m.retirement_issued
            && m.home_issued == m.tx.patch.dom() && m.home_done == m.tx.patch.dom()
            && m.home_stable == m.tx.patch.dom() && m.tx.home == journal::target(m.tx),
        Event::CompleteRetirement => m.retirement_issued && !m.retirement_done,
        Event::PersistRetirement => m.retirement_issued && !m.tx.retired,
        Event::Acknowledge => !m.tx.aborted && m.tx.retired && m.retirement_done,
        Event::Abort => true,
    }
}

pub open spec fn apply(m: Machine, e: Event) -> Machine {
    match e {
        Event::SubmitPayload(u) => Machine { tx: journal::issue_payload(m.tx, u), ..m },
        Event::CompletePayload(u) => Machine { payload_done: m.payload_done.insert(u), ..m },
        Event::PersistPayload(u) => Machine { tx: journal::persist_payload(m.tx, u), ..m },
        Event::PrepareFence => Machine { tx: journal::finish_prepare(m.tx), ..m },
        Event::SubmitCommit => Machine { tx: journal::issue_commit(m.tx), ..m },
        Event::CompleteCommit => Machine { commit_done: true, ..m },
        Event::PersistCommit => Machine { tx: journal::persist_commit(m.tx), ..m },
        Event::SubmitHome(u) => Machine { home_issued: m.home_issued.insert(u), ..m },
        Event::CompleteHome(u) => Machine { home_done: m.home_done.insert(u), ..m },
        Event::PersistHome(u) => Machine { tx: journal::checkpoint_unit(m.tx, u),
            home_stable: m.home_stable.insert(u), ..m },
        Event::SubmitRetirement => Machine { retirement_issued: true, ..m },
        Event::CompleteRetirement => Machine { retirement_done: true, ..m },
        Event::PersistRetirement => Machine { tx: journal::persist_retirement(m.tx), ..m },
        Event::Acknowledge => Machine { tx: journal::acknowledge(m.tx), ..m },
        Event::Abort => Machine { tx: journal::abort(m.tx), ..m },
    }
}

pub open spec fn step(m: Machine, n: Machine) -> bool {
    exists|e: Event| enabled(m, e) && n == apply(m, e)
}

pub open spec fn quiescent(m: Machine) -> bool {
    &&& m.payload_done == m.tx.issued
    &&& m.commit_done == m.tx.commit_issued
    &&& m.home_done == m.home_issued
    &&& m.retirement_done == m.retirement_issued
}

pub open spec fn reusable(m: Machine) -> bool { m.tx.retired && quiescent(m) }

pub proof fn initialization(before: Disk, patch: Disk)
    requires patch.dom().subset_of(before.dom()),
    ensures inv(init(before, patch)),
{
    journal::initial_state_is_valid(before, patch);
}

pub proof fn event_refines_logical_protocol(m: Machine, e: Event)
    requires inv(m), enabled(m, e),
    ensures journal::next(m.tx, apply(m, e).tx),
{
    match e {
        Event::SubmitPayload(u) => {
            assert(apply(m, e).tx == journal::issue_payload(m.tx, u));
        },
        Event::PersistPayload(u) => {
            assert(apply(m, e).tx == journal::persist_payload(m.tx, u));
        },
        Event::PersistHome(u) => {
            assert(m.tx.patch.dom().contains(u));
            assert(m.tx.committed);
            assert(apply(m, e).tx == journal::checkpoint_unit(m.tx, u));
        },
        _ => {},
    }
}

pub proof fn every_event_preserves(m: Machine, e: Event)
    requires inv(m), enabled(m, e),
    ensures inv(apply(m, e)),
{
    event_refines_logical_protocol(m, e);
    journal::every_step_preserves_invariant(m.tx, apply(m, e).tx);
    match e {
        Event::SubmitPayload(u) => {
            assert(!m.tx.commit_issued);
        },
        Event::SubmitHome(u) => {
            if m.retirement_issued { assert(m.home_issued.contains(u)); }
        },
        Event::PersistHome(u) => {
            if m.retirement_issued { assert(m.home_stable.contains(u)); }
        },
        _ => {},
    }
}

pub proof fn completion_is_not_persistence(before: Disk, patch: Disk, u: nat)
    requires patch.dom().subset_of(before.dom()), patch.dom().contains(u),
    ensures exists|m: Machine| inv(m) && m.payload_done.contains(u)
        && !m.tx.log.dom().contains(u) && !m.tx.prepared,
{
    initialization(before, patch);
    let a = init(before, patch);
    every_event_preserves(a, Event::SubmitPayload(u));
    let b = apply(a, Event::SubmitPayload(u));
    every_event_preserves(b, Event::CompletePayload(u));
    let c = apply(b, Event::CompletePayload(u));
    assert(c.payload_done.contains(u) && !c.tx.log.dom().contains(u) && !c.tx.prepared);
}

pub proof fn reuse_has_no_late_persistence_events(m: Machine)
    requires inv(m), reusable(m),
    ensures !enabled(m, Event::PersistCommit), !enabled(m, Event::PersistRetirement),
        forall|u: nat| !enabled(m, Event::PersistPayload(u)) && !enabled(m, Event::PersistHome(u)),
        !enabled(m, Event::CompleteCommit), !enabled(m, Event::CompleteRetirement),
        forall|u: nat| !enabled(m, Event::CompletePayload(u)) && !enabled(m, Event::CompleteHome(u)),
{
}

pub proof fn every_finite_interleaving(trace: Seq<Machine>, i: nat)
    requires trace.len() > 0, inv(trace[0]), i < trace.len(),
        forall|j: int| 0 <= j < trace.len() - 1 ==> #[trigger] step(trace[j], trace[j + 1]),
    ensures inv(trace[i as int]),
        journal::recover(journal::crash(trace[i as int].tx)) == trace[i as int].tx.before
        || journal::recover(journal::crash(trace[i as int].tx)) == journal::target(trace[i as int].tx),
    decreases i,
{
    if i > 0 {
        every_finite_interleaving(trace, (i - 1) as nat);
        let m = trace[i as int - 1];
        let n = trace[i as int];
        assert(step(trace[i as int - 1], trace[(i as int - 1) + 1]));
        let e = choose|e: Event| enabled(m, e) && n == apply(m, e);
        every_event_preserves(m, e);
    }
    journal::recovery_is_a_legal_single_transaction_cut(trace[i as int].tx);
}

pub proof fn public_success_is_durable_and_quiescent(m: Machine)
    requires inv(m), m.tx.acknowledged,
    ensures reusable(m), journal::recover(journal::crash(m.tx)) == journal::target(m.tx),
{
    journal::acknowledged_transaction_survives(m.tx);
}

pub proof fn abort_does_not_cancel_an_issued_commit(m: Machine)
    requires inv(m), enabled(m, Event::PersistCommit),
    ensures enabled(apply(m, Event::Abort), Event::PersistCommit),
        !enabled(apply(m, Event::Abort), Event::Acknowledge),
{
}

pub proof fn a_nonempty_transaction_reaches_public_success() {
    let before = Map::<nat, nat>::empty().insert(0, 7);
    let patch = Map::<nat, nat>::empty().insert(0, 11);
    initialization(before, patch);
    let a = init(before, patch);
    every_event_preserves(a, Event::SubmitPayload(0));
    let b = apply(a, Event::SubmitPayload(0));
    every_event_preserves(b, Event::CompletePayload(0));
    let c = apply(b, Event::CompletePayload(0));
    every_event_preserves(c, Event::PersistPayload(0));
    let d = apply(c, Event::PersistPayload(0));
    every_event_preserves(d, Event::PrepareFence);
    let e = apply(d, Event::PrepareFence);
    every_event_preserves(e, Event::SubmitCommit);
    let f = apply(e, Event::SubmitCommit);
    every_event_preserves(f, Event::CompleteCommit);
    let g = apply(f, Event::CompleteCommit);
    every_event_preserves(g, Event::PersistCommit);
    let h = apply(g, Event::PersistCommit);
    every_event_preserves(h, Event::SubmitHome(0));
    let i = apply(h, Event::SubmitHome(0));
    every_event_preserves(i, Event::CompleteHome(0));
    let j = apply(i, Event::CompleteHome(0));
    every_event_preserves(j, Event::PersistHome(0));
    let k = apply(j, Event::PersistHome(0));
    assert(k.tx.home == journal::target(k.tx));
    every_event_preserves(k, Event::SubmitRetirement);
    let l = apply(k, Event::SubmitRetirement);
    every_event_preserves(l, Event::CompleteRetirement);
    let m = apply(l, Event::CompleteRetirement);
    every_event_preserves(m, Event::PersistRetirement);
    let n = apply(m, Event::PersistRetirement);
    every_event_preserves(n, Event::Acknowledge);
    let done = apply(n, Event::Acknowledge);
    public_success_is_durable_and_quiescent(done);
    assert(journal::recover(journal::crash(done.tx))[0] == 11);
    assert(reusable(done));
}

}
