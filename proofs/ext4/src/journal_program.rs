// SPDX-License-Identifier: MPL-2.0

//! Ordered log commits, FIFO home checkpoints and fenced prefix retirement.
//! A completion is an adapter report. Physical durability is established by
//! the separate byte-valued device model and its explicit flush contract.

use vstd::prelude::*;

verus! {

#[derive(Clone, Copy)]
pub enum Lane { Bootstrap, Commit, Checkpoint, Tail }

#[derive(Clone, Copy)]
pub struct State {
    pub bootstrap: u8, pub commit: usize, pub commit_cursor: usize,
    pub checkpoint: usize, pub home_cursor: usize, pub retired: usize,
    pub tail_goal: usize, pub tail_phase: u8, pub pending: bool,
    pub lane: Lane, pub request: u64, pub faulted: bool,
}

pub open spec fn counts_valid(counts: Seq<nat>) -> bool {
    0 < counts.len() <= 64 && forall|i: int| 0 <= i < counts.len() ==> 1 <= #[trigger] counts[i] <= 250
}

pub open spec fn position_ready(s: State, lane: Lane, counts: Seq<nat>) -> bool {
    match lane {
        Lane::Bootstrap => s.bootstrap < 4,
        Lane::Commit => s.bootstrap == 4 && s.commit < counts.len(),
        Lane::Checkpoint => s.bootstrap == 4 && s.checkpoint < s.commit,
        Lane::Tail => s.bootstrap == 4 && (s.tail_phase == 1 || s.checkpoint > s.retired),
    }
}

pub open spec fn wf(s: State, counts: Seq<nat>) -> bool {
    &&& counts_valid(counts) && s.bootstrap <= 4
    &&& s.retired <= s.checkpoint <= s.commit <= counts.len()
    &&& (if s.commit < counts.len() { s.commit_cursor <= counts[s.commit as int] + 3 } else { s.commit_cursor == 0 })
    &&& (if s.checkpoint < counts.len() { s.home_cursor <= counts[s.checkpoint as int] } else { s.home_cursor == 0 })
    &&& (s.home_cursor > 0 ==> s.checkpoint < s.commit)
    &&& s.tail_phase <= 1 && s.retired <= s.tail_goal <= s.checkpoint
    &&& (s.tail_phase == 1 ==> s.retired < s.tail_goal)
    &&& (s.tail_phase == 0 && !(s.pending && s.lane is Tail) && !s.faulted ==> s.tail_goal == s.retired)
    &&& (s.pending && s.lane is Tail && s.tail_phase == 0 ==> s.tail_goal == s.checkpoint && s.retired < s.tail_goal)
    &&& (s.pending ==> s.request > 0 && position_ready(s, s.lane, counts))
    &&& (s.bootstrap < 4 ==> s.commit == 0 && s.commit_cursor == 0 && s.checkpoint == 0 && s.home_cursor == 0
        && s.retired == 0 && s.tail_goal == 0 && s.tail_phase == 0)
}

pub open spec fn initial() -> State {
    State { bootstrap: 0, commit: 0, commit_cursor: 0, checkpoint: 0, home_cursor: 0,
        retired: 0, tail_goal: 0, tail_phase: 0, pending: false, lane: Lane::Bootstrap, request: 0, faulted: false }
}

pub open spec fn enabled(s: State, lane: Lane, counts: Seq<nat>) -> bool {
    !s.pending && !s.faulted && s.request < 18446744073709551615 && position_ready(s, lane, counts)
}

pub open spec fn started(s: State, lane: Lane) -> State {
    State { pending: true, lane, request: (s.request + 1) as u64,
        tail_goal: if lane is Tail && s.tail_phase == 0 { s.checkpoint } else { s.tail_goal }, ..s }
}

pub open spec fn completed(s: State, counts: Seq<nat>, success: bool) -> State {
    if s.faulted || !success { State { pending: false, faulted: true, ..s } }
    else {
        match s.lane {
            Lane::Bootstrap => State { bootstrap: (s.bootstrap + 1) as u8, pending: false, ..s },
            Lane::Commit => if s.commit_cursor < counts[s.commit as int] + 3 {
                State { commit_cursor: (s.commit_cursor + 1) as usize, pending: false, ..s }
            } else { State { commit: (s.commit + 1) as usize, commit_cursor: 0, pending: false, ..s } },
            Lane::Checkpoint => if s.home_cursor < counts[s.checkpoint as int] {
                State { home_cursor: (s.home_cursor + 1) as usize, pending: false, ..s }
            } else { State { checkpoint: (s.checkpoint + 1) as usize, home_cursor: 0, pending: false, ..s } },
            Lane::Tail => if s.tail_phase == 0 { State { tail_phase: 1, pending: false, ..s } }
                else { State { retired: s.tail_goal, tail_phase: 0, pending: false, ..s } },
        }
    }
}

pub open spec fn finished(s: State, counts: Seq<nat>) -> bool {
    s.bootstrap == 4 && s.commit == counts.len() && s.checkpoint == counts.len() && s.retired == counts.len()
        && s.tail_phase == 0 && !s.pending && !s.faulted
}

pub proof fn initial_window_state_is_valid(counts: Seq<nat>)
    requires counts_valid(counts),
    ensures wf(initial(), counts),
{ }

pub proof fn starting_a_window_request_preserves_order(s: State, lane: Lane, counts: Seq<nat>)
    requires wf(s, counts), enabled(s, lane, counts),
    ensures wf(started(s, lane), counts), started(s, lane).request as nat == s.request as nat + 1,
{ }

pub proof fn completing_a_window_request_preserves_order(s: State, counts: Seq<nat>, success: bool)
    requires wf(s, counts), s.pending,
    ensures wf(completed(s, counts, success), counts),
        completed(s, counts, success).commit >= s.commit,
        completed(s, counts, success).checkpoint >= s.checkpoint,
        completed(s, counts, success).retired >= s.retired,
        s.faulted || !success ==> completed(s, counts, success).faulted
            && completed(s, counts, success).commit == s.commit && completed(s, counts, success).checkpoint == s.checkpoint
            && completed(s, counts, success).retired == s.retired,
{
    match s.lane { Lane::Bootstrap => {}, Lane::Commit => {}, Lane::Checkpoint => {}, Lane::Tail => {} }
}

pub proof fn aborting_keeps_the_request_and_all_committed_frontiers(s: State, counts: Seq<nat>)
    requires wf(s, counts),
    ensures wf(State { faulted: true, ..s }, counts), (State { faulted: true, ..s }).pending == s.pending,
{ }

pub(crate) fn begin_request(s: State, lane: Lane, Ghost(counts): Ghost<Seq<nat>>) -> (r: State)
    requires wf(s, counts), enabled(s, lane, counts),
    ensures r == started(s, lane), wf(r, counts),
{
    proof { starting_a_window_request_preserves_order(s, lane, counts); }
    State { pending: true, lane, request: s.request + 1,
        tail_goal: match lane { Lane::Tail => if s.tail_phase == 0 { s.checkpoint } else { s.tail_goal }, _ => s.tail_goal }, ..s }
}

pub(crate) fn finish_request(s: State, commit_count: usize, home_count: usize, success: bool, Ghost(counts): Ghost<Seq<nat>>) -> (r: State)
    requires wf(s, counts), s.pending,
        commit_count as nat == if s.commit < counts.len() { counts[s.commit as int] } else { 0nat },
        home_count as nat == if s.checkpoint < counts.len() { counts[s.checkpoint as int] } else { 0nat },
    ensures r == completed(s, counts, success), wf(r, counts),
{
    proof { completing_a_window_request_preserves_order(s, counts, success); }
    if s.faulted || !success { return State { pending: false, faulted: true, ..s }; }
    match s.lane {
        Lane::Bootstrap => State { bootstrap: s.bootstrap + 1, pending: false, ..s },
        Lane::Commit => if s.commit_cursor < commit_count + 3 {
            State { commit_cursor: s.commit_cursor + 1, pending: false, ..s }
        } else { State { commit: s.commit + 1, commit_cursor: 0, pending: false, ..s } },
        Lane::Checkpoint => if s.home_cursor < home_count {
            State { home_cursor: s.home_cursor + 1, pending: false, ..s }
        } else { State { checkpoint: s.checkpoint + 1, home_cursor: 0, pending: false, ..s } },
        Lane::Tail => if s.tail_phase == 0 { State { tail_phase: 1, pending: false, ..s } }
            else { State { retired: s.tail_goal, tail_phase: 0, pending: false, ..s } },
    }
}

}
