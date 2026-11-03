// SPDX-License-Identifier: MPL-2.0

//! M0: one transaction, asynchronous persistence, partial checkpointing.
//! This is NOT an ext4/JBD2 decoder, a device implementation, or a proof
//! about arbitrary untrusted media. See the checked scope in ../proof-status.json.

use vstd::prelude::*;
use vstd::assert_maps_equal;
use crate::redo::{Disk, compatible, overlay, complete_redo_overrides_partial_checkpoint,
    overlay_is_idempotent};

verus! {

#[verifier::ext_equal]
pub struct State {
    pub before: Disk,
    pub patch: Disk,
    pub home: Disk,
    pub issued: Set<nat>,
    pub log: Disk,
    pub prepared: bool,
    pub commit_issued: bool,
    pub committed: bool,
    pub retired: bool,
    pub acknowledged: bool,
    pub aborted: bool,
}

#[verifier::ext_equal]
pub struct CrashImage {
    pub home: Disk,
    pub log: Disk,
    pub committed: bool,
    pub retired: bool,
}

pub open spec fn target(s: State) -> Disk {
    overlay(s.before, s.patch)
}

pub open spec fn init(before: Disk, patch: Disk) -> State {
    State {
        before, patch, home: before, issued: Set::empty(), log: Map::empty(),
        prepared: false, commit_issued: false, committed: false,
        retired: false, acknowledged: false, aborted: false,
    }
}

pub open spec fn inv(s: State) -> bool {
    &&& compatible(s.before, s.home, s.patch)
    &&& s.issued.subset_of(s.patch.dom())
    &&& s.log.dom().subset_of(s.issued)
    &&& (forall|unit: nat| s.log.dom().contains(unit)
        ==> #[trigger] s.log[unit] == s.patch[unit])
    &&& (!s.committed ==> s.home == s.before)
    &&& (s.prepared ==> s.log == s.patch && s.issued == s.patch.dom())
    &&& (s.commit_issued ==> s.prepared)
    &&& (s.committed ==> s.commit_issued)
    &&& (s.retired ==> s.committed && s.home == target(s))
    &&& (s.acknowledged ==> s.committed)
}

pub open spec fn issue_payload(s: State, unit: nat) -> State {
    State { issued: s.issued.insert(unit), ..s }
}

pub open spec fn persist_payload(s: State, unit: nat) -> State
    recommends s.patch.dom().contains(unit),
{
    State { log: s.log.insert(unit, s.patch[unit]), ..s }
}

pub open spec fn finish_prepare(s: State) -> State {
    State { prepared: true, ..s }
}

pub open spec fn issue_commit(s: State) -> State {
    State { commit_issued: true, ..s }
}

pub open spec fn persist_commit(s: State) -> State {
    State { committed: true, ..s }
}

pub open spec fn checkpoint_unit(s: State, unit: nat) -> State
    recommends s.patch.dom().contains(unit),
{
    State { home: s.home.insert(unit, s.patch[unit]), ..s }
}

pub open spec fn persist_retirement(s: State) -> State {
    State { retired: true, ..s }
}

pub open spec fn acknowledge(s: State) -> State {
    State { acknowledged: true, ..s }
}

pub open spec fn abort(s: State) -> State {
    State { aborted: true, ..s }
}

pub open spec fn next(s: State, t: State) -> bool {
    ||| t == s
    ||| exists|unit: nat| !s.aborted && !s.prepared
        && s.patch.dom().contains(unit) && t == issue_payload(s, unit)
    // Already submitted writes may persist even after an error.
    ||| exists|unit: nat| s.issued.contains(unit)
        && t == persist_payload(s, unit)
    ||| !s.aborted && s.issued == s.patch.dom() && s.log == s.patch
        && t == finish_prepare(s)
    ||| !s.aborted && s.prepared && t == issue_commit(s)
    // In particular, abort does not cancel an already issued commit.
    ||| s.commit_issued && t == persist_commit(s)
    ||| exists|unit: nat| s.committed && s.patch.dom().contains(unit)
        && t == checkpoint_unit(s, unit)
    ||| s.committed && s.home == target(s) && t == persist_retirement(s)
    ||| !s.aborted && s.committed && t == acknowledge(s)
    ||| t == abort(s)
}

pub open spec fn crash(s: State) -> CrashImage {
    CrashImage { home: s.home, log: s.log,
        committed: s.committed, retired: s.retired }
}

pub open spec fn recover(image: CrashImage) -> Disk {
    if image.retired {
        image.home
    } else if image.committed {
        overlay(image.home, image.log)
    } else {
        image.home
    }
}

pub proof fn initial_state_is_valid(before: Disk, patch: Disk)
    requires patch.dom().subset_of(before.dom()),
    ensures inv(init(before, patch)),
{
}

pub proof fn payload_issue_preserves(s: State, unit: nat)
    requires inv(s), !s.aborted, !s.prepared, s.patch.dom().contains(unit),
    ensures inv(issue_payload(s, unit)),
{
}

pub proof fn payload_persistence_preserves(s: State, unit: nat)
    requires inv(s), s.issued.contains(unit),
    ensures inv(persist_payload(s, unit)),
{
    let t = persist_payload(s, unit);
    assert(s.patch.dom().contains(unit));
    if s.prepared {
        assert_maps_equal!(t.log, s.patch, u => { });
    }
    assert forall|u: nat| persist_payload(s, unit).log.dom().contains(u)
        implies #[trigger] persist_payload(s, unit).log[u] == s.patch[u] by {
        if u != unit {
            assert(s.log.dom().contains(u));
            assert(s.log[u] == s.patch[u]);
        }
    }
}

pub proof fn prepare_preserves(s: State)
    requires inv(s), !s.aborted,
        s.issued == s.patch.dom(), s.log == s.patch,
    ensures inv(finish_prepare(s)),
{
}

pub proof fn commit_issue_preserves(s: State)
    requires inv(s), !s.aborted, s.prepared,
    ensures inv(issue_commit(s)),
{
}

pub proof fn commit_persistence_preserves(s: State)
    requires inv(s), s.commit_issued,
    ensures inv(persist_commit(s)),
{
}

pub proof fn checkpoint_preserves(s: State, unit: nat)
    requires inv(s), s.committed, s.patch.dom().contains(unit),
    ensures inv(checkpoint_unit(s, unit)),
{
    let t = checkpoint_unit(s, unit);
    assert(s.before.dom().contains(unit));
    assert(t.home.dom() =~= s.before.dom());
    assert(target(t) == target(s));
    assert forall|u: nat| s.before.dom().contains(u)
        && !s.patch.dom().contains(u)
        implies #[trigger] t.home[u] == s.before[u] by {
        assert(u != unit);
    }
    if s.retired {
        assert_maps_equal!(t.home, target(s), u => { });
    }
}

pub proof fn retirement_preserves(s: State)
    requires inv(s), s.committed, s.home == target(s),
    ensures inv(persist_retirement(s)),
{
}

pub proof fn acknowledgement_preserves(s: State)
    requires inv(s), !s.aborted, s.committed,
    ensures inv(acknowledge(s)),
{
}

pub proof fn abort_preserves(s: State)
    requires inv(s),
    ensures inv(abort(s)),
{
}

pub proof fn every_step_preserves_invariant(s: State, t: State)
    requires inv(s), next(s, t),
    ensures inv(t),
{
    if exists|u: nat| !s.aborted && !s.prepared
        && s.patch.dom().contains(u) && t == issue_payload(s, u) {
        let u = choose|u: nat| !s.aborted && !s.prepared
            && s.patch.dom().contains(u) && t == issue_payload(s, u);
        payload_issue_preserves(s, u);
    } else if exists|u: nat| s.issued.contains(u) && t == persist_payload(s, u) {
        let u = choose|u: nat| s.issued.contains(u) && t == persist_payload(s, u);
        payload_persistence_preserves(s, u);
    } else if exists|u: nat| s.committed
        && s.patch.dom().contains(u) && t == checkpoint_unit(s, u) {
        let u = choose|u: nat| s.committed
            && s.patch.dom().contains(u) && t == checkpoint_unit(s, u);
        checkpoint_preserves(s, u);
    } else {
        if t == finish_prepare(s) && !s.aborted
            && s.issued == s.patch.dom() && s.log == s.patch {
            prepare_preserves(s);
        }
        if t == issue_commit(s) && !s.aborted && s.prepared {
            commit_issue_preserves(s);
        }
        if t == persist_commit(s) && s.commit_issued {
            commit_persistence_preserves(s);
        }
        if t == persist_retirement(s) && s.committed && s.home == target(s) {
            retirement_preserves(s);
        }
        if t == acknowledge(s) && !s.aborted && s.committed {
            acknowledgement_preserves(s);
        }
        if t == abort(s) { abort_preserves(s); }
    }
}

pub proof fn recovery_is_a_legal_single_transaction_cut(s: State)
    requires inv(s),
    ensures recover(crash(s)) == s.before || recover(crash(s)) == target(s),
{
    if s.committed && !s.retired {
        complete_redo_overrides_partial_checkpoint(s.before, s.home, s.patch);
    }
}

pub proof fn acknowledged_transaction_survives(s: State)
    requires inv(s), s.acknowledged,
    ensures recover(crash(s)) == target(s),
{
    if !s.retired {
        complete_redo_overrides_partial_checkpoint(s.before, s.home, s.patch);
    }
}

pub proof fn replay_is_restartable(image: CrashImage)
    ensures overlay(overlay(image.home, image.log), image.log)
        == overlay(image.home, image.log),
{
    overlay_is_idempotent(image.home, image.log);
}


pub proof fn a_nonempty_transaction_can_commit_and_retire() {
    let before = Map::<nat, nat>::empty().insert(0, 7);
    let patch = Map::<nat, nat>::empty().insert(0, 11);
    initial_state_is_valid(before, patch);
    let s0 = init(before, patch);
    payload_issue_preserves(s0, 0);
    let s1 = issue_payload(s0, 0);
    payload_persistence_preserves(s1, 0);
    let s2 = persist_payload(s1, 0);
    prepare_preserves(s2);
    let s3 = finish_prepare(s2);
    commit_issue_preserves(s3);
    let s4 = issue_commit(s3);
    commit_persistence_preserves(s4);
    let s5 = persist_commit(s4);
    acknowledgement_preserves(s5);
    let s6 = acknowledge(s5);
    acknowledged_transaction_survives(s6);
    assert(recover(crash(s6))[0] == 11);
    checkpoint_preserves(s6, 0);
    let s7 = checkpoint_unit(s6, 0);
    assert(s7.home == target(s7));
    retirement_preserves(s7);
    let s8 = persist_retirement(s7);
    acknowledged_transaction_survives(s8);
    assert(recover(crash(s8))[0] == 11);
}

// Witnesses show why weakening the protocol is not an optimization.
pub proof fn missing_prepare_can_lose_an_acknowledged_change() {
    let before = Map::<nat, nat>::empty().insert(0, 7);
    let patch = Map::<nat, nat>::empty().insert(0, 11);
    let bad = State {
        commit_issued: true, committed: true, acknowledged: true,
        ..init(before, patch)
    };
    assert(bad.commit_issued);
    assert(!bad.prepared);
    assert(!inv(bad)) by {
        if inv(bad) {
            assert(bad.commit_issued ==> bad.prepared);
            assert(false);
        }
    }
    assert(recover(crash(bad))[0] == 7);
    assert(target(bad)[0] == 11);
}

pub proof fn premature_checkpoint_can_expose_a_partial_transaction() {
    let before = Map::<nat, nat>::empty().insert(0, 7).insert(1, 8);
    let patch = Map::<nat, nat>::empty().insert(0, 11).insert(1, 12);
    let bad = State { home: before.insert(0, 11), ..init(before, patch) };
    assert(!inv(bad)) by {
        if inv(bad) {
            assert(!bad.committed);
            assert(bad.home == bad.before);
            assert(bad.home[0] == 11);
            assert(bad.before[0] == 7);
        }
    }
    assert(recover(crash(bad))[0] == 11);
    assert(recover(crash(bad))[1] == 8);
    assert(recover(crash(bad)) != before);
    assert(recover(crash(bad)) != target(bad));
}

}
