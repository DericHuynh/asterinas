// SPDX-License-Identifier: MPL-2.0

//! Conservative serial full-data-journal ordering. Every phase denotes a
//! command/report, not physical persistence without the device refinement.

use vstd::prelude::*;

verus! {

#[derive(Clone, Copy)]
pub enum Phase {
    MarkDirty, DirtyFence, Activate, ActivationFence, Descriptor, Payloads,
    LogFence, Commit, CommitFence, Homes, HomeFence, Retire, RetirementFence, Done,
}

#[derive(Clone, Copy)]
pub struct State { pub phase: Phase, pub cursor: usize, pub request: u64, pub pending: bool, pub faulted: bool }

pub open spec fn completed_count(s: State, count: nat) -> nat {
    match s.phase {
        Phase::MarkDirty => 0, Phase::DirtyFence => 1, Phase::Activate => 2, Phase::ActivationFence => 3,
        Phase::Descriptor => 4, Phase::Payloads => 5 + s.cursor as nat, Phase::LogFence => 5 + count,
        Phase::Commit => 6 + count, Phase::CommitFence => 7 + count, Phase::Homes => 8 + count + s.cursor as nat,
        Phase::HomeFence => 8 + 2 * count, Phase::Retire => 9 + 2 * count,
        Phase::RetirementFence => 10 + 2 * count, Phase::Done => 11 + 2 * count,
    }
}

pub open spec fn wf(s: State, count: nat) -> bool {
    &&& 1 <= count <= 250
    &&& (if s.phase is Payloads || s.phase is Homes { s.cursor < count } else { s.cursor == 0 })
    &&& s.request <= 2 * count + 11
    &&& (s.pending ==> !(s.phase is Done) && s.request > 0)
    &&& (!s.faulted ==> s.request as nat == completed_count(s, count) + if s.pending { 1nat } else { 0nat })
}

pub open spec fn initial() -> State {
    State { phase: Phase::MarkDirty, cursor: 0, request: 0, pending: false, faulted: false }
}

pub open spec fn started(s: State) -> State { State { pending: true, request: (s.request + 1) as u64, ..s } }

pub open spec fn completed(s: State, count: nat, success: bool) -> State {
    if s.faulted || !success { State { pending: false, faulted: true, ..s } }
    else {
        let phase = match s.phase {
            Phase::MarkDirty => Phase::DirtyFence, Phase::DirtyFence => Phase::Activate,
            Phase::Activate => Phase::ActivationFence, Phase::ActivationFence => Phase::Descriptor,
            Phase::Descriptor => Phase::Payloads,
            Phase::Payloads => if s.cursor + 1 < count { Phase::Payloads } else { Phase::LogFence },
            Phase::LogFence => Phase::Commit, Phase::Commit => Phase::CommitFence,
            Phase::CommitFence => Phase::Homes,
            Phase::Homes => if s.cursor + 1 < count { Phase::Homes } else { Phase::HomeFence },
            Phase::HomeFence => Phase::Retire, Phase::Retire => Phase::RetirementFence,
            Phase::RetirementFence => Phase::Done, Phase::Done => Phase::Done,
        };
        let cursor = if (s.phase is Payloads || s.phase is Homes) && s.cursor + 1 < count { (s.cursor + 1) as usize } else { 0usize };
        State { phase, cursor, pending: false, ..s }
    }
}

pub(crate) fn start(s: State, count: usize) -> (r: State)
    requires wf(s, count as nat), !s.pending, !s.faulted, !(s.phase is Done),
    ensures r == started(s), wf(r, count as nat),
{
    State { pending: true, request: s.request + 1, ..s }
}

pub(crate) fn finish(s: State, count: usize, success: bool) -> (r: State)
    requires wf(s, count as nat), s.pending,
    ensures r == completed(s, count as nat, success), wf(r, count as nat),
{
    if s.faulted || !success { return State { pending: false, faulted: true, ..s }; }
    let phase = match s.phase {
        Phase::MarkDirty => Phase::DirtyFence, Phase::DirtyFence => Phase::Activate,
        Phase::Activate => Phase::ActivationFence, Phase::ActivationFence => Phase::Descriptor,
        Phase::Descriptor => Phase::Payloads,
        Phase::Payloads => if s.cursor + 1 < count { Phase::Payloads } else { Phase::LogFence },
        Phase::LogFence => Phase::Commit, Phase::Commit => Phase::CommitFence,
        Phase::CommitFence => Phase::Homes,
        Phase::Homes => if s.cursor + 1 < count { Phase::Homes } else { Phase::HomeFence },
        Phase::HomeFence => Phase::Retire, Phase::Retire => Phase::RetirementFence,
        Phase::RetirementFence => Phase::Done, Phase::Done => Phase::Done,
    };
    let cursor = match s.phase {
        Phase::Payloads | Phase::Homes => if s.cursor + 1 < count { s.cursor + 1 } else { 0 },
        _ => 0,
    };
    State { phase, cursor, pending: false, ..s }
}

pub open spec fn remaining(s: State, count: nat) -> nat { (2 * count + 11 - completed_count(s, count)) as nat }

pub proof fn initialization(count: nat)
    requires 1 <= count <= 250,
    ensures wf(initial(), count), remaining(initial(), count) == 2 * count + 11,
{
}

pub proof fn successful_pair_preserves_and_makes_progress(s: State, count: nat)
    requires wf(s, count), !s.pending, !s.faulted, !(s.phase is Done),
    ensures wf(started(s), count), wf(completed(started(s), count, true), count),
        remaining(completed(started(s), count, true), count) + 1 == remaining(s, count),
        !completed(started(s), count, true).pending, !completed(started(s), count, true).faulted,
{
}

pub closed spec fn normal_finish(s: State, count: nat) -> State
    recommends wf(s, count), !s.pending, !s.faulted,
    decreases remaining(s, count),
{
    if !wf(s, count) || s.pending || s.faulted || s.phase is Done { s }
    else { normal_finish(completed(started(s), count, true), count) }
}

pub proof fn failure_free_completion_is_finite(s: State, count: nat)
    requires wf(s, count), !s.pending, !s.faulted,
    ensures normal_finish(s, count).phase is Done, !normal_finish(s, count).pending, !normal_finish(s, count).faulted,
        normal_finish(s, count).request as nat == s.request as nat + remaining(s, count),
    decreases remaining(s, count),
{
    if !(s.phase is Done) {
        successful_pair_preserves_and_makes_progress(s, count);
        failure_free_completion_is_finite(completed(started(s), count, true), count);
    }
}

pub proof fn abort_keeps_the_pending_request(s: State, count: nat)
    requires wf(s, count),
    ensures wf(State { faulted: true, ..s }, count), (State { faulted: true, ..s }).pending == s.pending,
{
}

}
