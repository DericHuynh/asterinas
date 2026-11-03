// SPDX-License-Identifier: MPL-2.0

//! Composition of per-unit persistence, public acknowledgements, quiescent
//! generation changes, and logical transaction histories. Raw journal-record
//! recognition and the OSTD/device implementation are not abstracted as proved.

use vstd::prelude::*;
use crate::{history, journal, persistence};
use crate::redo::Disk;
use crate::persistence::{Machine, Event};

verus! {

pub struct System {
    pub history: history::History,
    pub device: Machine,
    pub sequence: u32,
    pub first_sequence: u32,
}

pub enum Action { Io(Event), Begin(Disk) }

pub open spec fn inv(s: System) -> bool {
    &&& history::inv(s.history)
    &&& persistence::inv(s.device)
    &&& s.history.active == s.device.tx
    &&& 0 < s.first_sequence <= s.sequence < 4294967295
    &&& s.sequence as nat == s.first_sequence as nat + s.history.patches.len()
}

pub open spec fn init(before: Disk, patch: Disk, sequence: u32) -> System {
    System { history: history::init(before, patch), device: persistence::init(before, patch),
        sequence, first_sequence: sequence }
}

pub open spec fn enabled(s: System, a: Action) -> bool {
    match a {
        Action::Io(e) => persistence::enabled(s.device, e),
        // Reserve MAX for a representable next-tail sequence; never start a
        // transaction that would need MAX + 1 during durable retirement.
        Action::Begin(patch) => persistence::reusable(s.device) && s.sequence < 4294967294
            && patch.dom().subset_of(journal::target(s.device.tx).dom()),
    }
}

pub open spec fn apply(s: System, a: Action) -> System {
    match a {
        Action::Io(e) => {
            let device = persistence::apply(s.device, e);
            System { history: history::advance(s.history, device.tx), device, ..s }
        },
        Action::Begin(patch) => System {
            history: history::begin_after_retirement(s.history, patch),
            device: persistence::init(journal::target(s.device.tx), patch),
            sequence: (s.sequence + 1) as u32, ..s
        },
    }
}

pub open spec fn step(s: System, t: System) -> bool {
    exists|a: Action| #[trigger] enabled(s, a) && t == apply(s, a)
}

pub proof fn initialization(before: Disk, patch: Disk, sequence: u32)
    requires patch.dom().subset_of(before.dom()), 0 < sequence < 4294967295,
    ensures inv(init(before, patch, sequence)),
{
    history::initialization(before, patch);
    persistence::initialization(before, patch);
}

pub proof fn action_preserves(s: System, a: Action)
    requires inv(s), enabled(s, a),
    ensures inv(apply(s, a)), apply(s, a).history.acknowledged >= s.history.acknowledged,
{
    match a {
        Action::Io(e) => {
            persistence::event_refines_logical_protocol(s.device, e);
            persistence::every_event_preserves(s.device, e);
            history::advance_preserves(s.history, persistence::apply(s.device, e).tx);
        },
        Action::Begin(patch) => {
            persistence::reuse_has_no_late_persistence_events(s.device);
            persistence::initialization(journal::target(s.device.tx), patch);
            history::retirement_composes(s.history, patch);
        },
    }
}

pub proof fn every_finite_execution(trace: Seq<System>, i: nat)
    requires trace.len() > 0, inv(trace[0]), i < trace.len(),
        forall|j: int| 0 <= j < trace.len() - 1 ==> #[trigger] step(trace[j], trace[j + 1]),
    ensures inv(trace[i as int]),
        trace[i as int].history.acknowledged >= trace[0].history.acknowledged,
    decreases i,
{
    if i > 0 {
        every_finite_execution(trace, (i - 1) as nat);
        assert(step(trace[i as int - 1], trace[(i as int - 1) + 1]));
        let a = choose|a: Action| #[trigger] enabled(trace[i as int - 1], a)
            && trace[i as int] == apply(trace[i as int - 1], a);
        action_preserves(trace[i as int - 1], a);
    }
}

pub proof fn crash_at_every_interleaving_preserves_the_acknowledged_prefix(trace: Seq<System>, i: nat)
    requires trace.len() > 0, inv(trace[0]), i < trace.len(),
        forall|j: int| 0 <= j < trace.len() - 1 ==> #[trigger] step(trace[j], trace[j + 1]),
    ensures exists|k: nat| trace[i as int].history.acknowledged <= k
        <= trace[i as int].history.patches.len() + 1
        && journal::recover(journal::crash(trace[i as int].device.tx))
            == history::cut(trace[i as int].history, k),
{
    every_finite_execution(trace, i);
    history::recovery_contains_every_acknowledgement(trace[i as int].history);
}

pub proof fn every_reused_generation_is_fresh(s: System, patch: Disk)
    requires inv(s), enabled(s, Action::Begin(patch)),
    ensures apply(s, Action::Begin(patch)).sequence > s.sequence,
        apply(s, Action::Begin(patch)).sequence as nat
            == s.first_sequence as nat + s.history.patches.len() + 1,
        persistence::quiescent(s.device),
        !persistence::enabled(s.device, Event::PersistCommit),
        !persistence::enabled(s.device, Event::PersistRetirement),
{
    persistence::reuse_has_no_late_persistence_events(s.device);
}

}
