// SPDX-License-Identifier: MPL-2.0

//! Logical composition. Retirement here does not license physical slot reuse:
//! the device/refinement layer must additionally establish I/O quiescence.

use vstd::prelude::*;
use crate::journal::{self, State};
use crate::redo::{Disk, overlay};

verus! {

pub struct History {
    pub cuts: Seq<Disk>,
    pub patches: Seq<Disk>,
    pub active: State,
    pub acknowledged: nat,
}

pub open spec fn inv(h: History) -> bool {
    &&& h.cuts.len() == h.patches.len() + 1
    &&& (forall|i: int| 0 <= i < h.patches.len() ==>
        (#[trigger] h.patches[i]).dom().subset_of(h.cuts[i].dom())
        && h.cuts[i + 1] == overlay(h.cuts[i], h.patches[i]))
    &&& journal::inv(h.active)
    &&& h.active.before == h.cuts.last()
    &&& h.acknowledged <= h.patches.len() + if h.active.committed { 1nat } else { 0nat }
    &&& (h.active.acknowledged ==> h.acknowledged == h.patches.len() + 1)
}

pub open spec fn init(before: Disk, patch: Disk) -> History {
    History { cuts: seq![before], patches: Seq::empty(),
        active: journal::init(before, patch), acknowledged: 0 }
}

pub open spec fn advance(h: History, t: State) -> History {
    History { active: t,
        acknowledged: if t.acknowledged { h.patches.len() + 1 } else { h.acknowledged },
        ..h }
}

pub open spec fn begin_after_retirement(h: History, patch: Disk) -> History {
    History {
        cuts: h.cuts.push(journal::target(h.active)),
        patches: h.patches.push(h.active.patch),
        active: journal::init(journal::target(h.active), patch),
        acknowledged: h.acknowledged,
    }
}

pub open spec fn next(h: History, k: History) -> bool {
    ||| exists|t: State| journal::next(h.active, t) && k == advance(h, t)
    ||| exists|patch: Disk| h.active.retired
        && patch.dom().subset_of(journal::target(h.active).dom())
        && k == begin_after_retirement(h, patch)
}

/// The current transaction is an additional candidate cut, even if its caller
/// has not received a reply. Historical values may have been overwritten.
pub open spec fn cut(h: History, index: nat) -> Disk {
    if index < h.cuts.len() { h.cuts[index as int] }
    else { journal::target(h.active) }
}

pub proof fn initialization(before: Disk, patch: Disk)
    requires patch.dom().subset_of(before.dom()),
    ensures inv(init(before, patch)),
{
    journal::initial_state_is_valid(before, patch);
}

pub proof fn advance_preserves(h: History, t: State)
    requires inv(h), journal::next(h.active, t),
    ensures inv(advance(h, t)), advance(h, t).acknowledged >= h.acknowledged,
{
    journal::every_step_preserves_invariant(h.active, t);
    // Committed/acknowledged facts cannot be erased by an I/O or abort step.
    assert(h.active.committed ==> t.committed);
    assert(h.active.acknowledged ==> t.acknowledged);
}

pub proof fn retirement_composes(h: History, patch: Disk)
    requires inv(h), h.active.retired,
        patch.dom().subset_of(journal::target(h.active).dom()),
    ensures inv(begin_after_retirement(h, patch)),
        begin_after_retirement(h, patch).acknowledged == h.acknowledged,
{
    let k = begin_after_retirement(h, patch);
    journal::initial_state_is_valid(journal::target(h.active), patch);
    assert forall|i: int| 0 <= i < k.patches.len() implies
        (#[trigger] k.patches[i]).dom().subset_of(k.cuts[i].dom())
        && k.cuts[i + 1] == overlay(k.cuts[i], k.patches[i]) by {
        if i < h.patches.len() {
            assert(h.patches[i].dom().subset_of(h.cuts[i].dom()));
        } else {
            assert(i == h.patches.len());
            assert(h.cuts[i] == h.active.before);
        }
    }
}

pub proof fn step_preserves(h: History, k: History)
    requires inv(h), next(h, k),
    ensures inv(k), k.acknowledged >= h.acknowledged,
{
    if exists|t: State| journal::next(h.active, t) && k == advance(h, t) {
        let t = choose|t: State| journal::next(h.active, t) && k == advance(h, t);
        advance_preserves(h, t);
    } else {
        let patch = choose|patch: Disk| h.active.retired
            && patch.dom().subset_of(journal::target(h.active).dom())
            && k == begin_after_retirement(h, patch);
        retirement_composes(h, patch);
    }
}

pub proof fn every_finite_execution(trace: Seq<History>, index: nat)
    requires trace.len() > 0, inv(trace[0]), index < trace.len(),
        forall|i: int| 0 <= i < trace.len() - 1 ==> #[trigger] next(trace[i], trace[i + 1]),
    ensures inv(trace[index as int]),
        trace[index as int].acknowledged >= trace[0].acknowledged,
    decreases index,
{
    if index > 0 {
        every_finite_execution(trace, (index - 1) as nat);
        assert(0 <= index as int - 1 < trace.len() - 1);
        assert(next(trace[index as int - 1], trace[(index as int - 1) + 1]));
        step_preserves(trace[index as int - 1], trace[index as int]);
    }
}

pub proof fn recovery_contains_every_acknowledgement(h: History)
    requires inv(h),
    ensures exists|index: nat| h.acknowledged <= index <= h.patches.len() + 1
        && journal::recover(journal::crash(h.active)) == cut(h, index),
{
    journal::recovery_is_a_legal_single_transaction_cut(h.active);
    if h.active.committed {
        if !h.active.retired {
            crate::redo::complete_redo_overrides_partial_checkpoint(
                h.active.before, h.active.home, h.active.patch);
        }
        assert(journal::recover(journal::crash(h.active))
            == cut(h, h.patches.len() + 1));
    } else {
        assert(journal::recover(journal::crash(h.active))
            == cut(h, h.patches.len()));
    }
}

pub proof fn crash_at_any_finite_execution_cut(trace: Seq<History>, index: nat)
    requires trace.len() > 0, inv(trace[0]), index < trace.len(),
        forall|i: int| 0 <= i < trace.len() - 1 ==> #[trigger] next(trace[i], trace[i + 1]),
    ensures exists|cut_index: nat|
        trace[index as int].acknowledged <= cut_index
        <= trace[index as int].patches.len() + 1
        && journal::recover(journal::crash(trace[index as int].active))
            == cut(trace[index as int], cut_index),
{
    every_finite_execution(trace, index);
    recovery_contains_every_acknowledgement(trace[index as int]);
}

}
