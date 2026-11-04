// SPDX-License-Identifier: MPL-2.0

//! Serialized recovery command protocol, with immutable owned after-images.
//! Completion reports are adapter inputs, not proofs of physical persistence.
//! A kernel adapter must bind successful Flush reports to its device contract.

use vstd::prelude::*;
use crate::{bytes, frozen::FrozenBlock, journal_state, journal_superblock, layout::JournalLayout, recovery_profile, replay, scan, scan_budget, super_state, superblock};

verus! {

pub struct State {
    pub phase: u8,
    pub cursor: usize,
    pub request: u64,
    pub pending: bool,
    pub faulted: bool,
}

pub open spec fn wf(s: State, count: nat) -> bool {
    &&& count <= 4096 && s.phase <= 4 && s.cursor <= count
    &&& (s.phase == 0 ==> s.cursor < count)
    &&& (s.phase > 0 ==> s.cursor == count)
    &&& (s.pending ==> s.phase < 4 && s.request > 0)
    &&& s.request <= count + 3
    &&& (!s.faulted ==> s.request as nat == s.cursor as nat
        + (if s.phase > 0 { s.phase as nat - 1 } else { 0 }) + if s.pending { 1nat } else { 0nat })
}

pub open spec fn started(s: State) -> State {
    State { phase: s.phase, cursor: s.cursor, request: (s.request + 1) as u64, pending: true, faulted: s.faulted }
}

pub open spec fn completed(s: State, count: nat, success: bool) -> State {
    if s.faulted || !success {
        State { pending: false, faulted: true, ..s }
    } else if s.phase == 0 {
        State { cursor: (s.cursor + 1) as usize, phase: if s.cursor + 1 == count { 1 } else { 0 }, pending: false, ..s }
    } else { State { phase: (s.phase + 1) as u8, pending: false, ..s } }
}

pub enum Command<'a> { Write { block: u32, image: &'a [u8] }, Flush }
pub enum CommandView { Write { block: u32, image: Seq<u8> }, Flush }

impl<'a> Command<'a> {
    pub open spec fn view(&self) -> CommandView {
        match self { Command::Write { block, image } => CommandView::Write { block: *block, image: image@ },
            Command::Flush => CommandView::Flush }
    }
}

pub struct Recovery {
    scan: scan::Scan,
    tail: FrozenBlock,
    journal_block: u32,
    primary: Ghost<Seq<u8>>,
    partition_bytes: u64,
    state: State,
}

impl Recovery {
    pub closed spec fn state(&self) -> State { self.state }
    pub open spec fn plan(&self) -> &replay::ReplayPlan { self.scan_result().plan() }
    pub closed spec fn scan_result(&self) -> &scan::Scan { &self.scan }
    pub closed spec fn tail(&self) -> Seq<u8> { self.tail.view() }
    pub closed spec fn journal_block(&self) -> u32 { self.journal_block }
    pub closed spec fn primary(&self) -> Seq<u8> { self.primary@ }
    pub closed spec fn partition_bytes(&self) -> u64 { self.partition_bytes }

    pub fn replay_plan(&self) -> (r: &replay::ReplayPlan) ensures r == self.plan(), r.refines() {
        proof { use_type_invariant(self); }
        self.scan.replay_plan()
    }

    pub fn retirement_image(&self) -> (r: (u32, &[u8]))
        ensures r.0 == self.journal_block(), r.0 == self.plan().layout().view().start,
            r.1@ == self.tail(), r.1.len() == 4096,
    {
        proof { use_type_invariant(self); }
        (self.journal_block, self.tail.as_slice())
    }

    #[verifier::type_invariant]
    spec fn valid(self) -> bool {
        &&& self.plan().refines() && wf(self.state(), self.plan().selection().len())
        &&& self.plan().layout().view().fs_blocks as nat * 4096 <= self.partition_bytes()
        &&& self.tail().len() == 4096 && bytes::be32(self.tail(), 28) == 0
        &&& bytes::be32(self.tail(), 24) == self.scan_result().next() as nat
        &&& self.journal_block() == self.plan().layout().view().start
        &&& !self.plan().layout().allowed(self.journal_block())
        &&& (forall|p: int| 0 <= p < self.plan().selection().len() ==>
            (#[trigger] self.plan().log()[self.plan().selection()[p] as int]).block == 0 ==>
                super_state::replay_ok(self.primary(), self.plan().log()[self.plan().selection()[p] as int].image,
                    self.partition_bytes()))
    }

    pub open spec fn expected(&self) -> CommandView {
        if self.state().phase == 0 {
            let write = self.plan().log()[self.plan().selection()[self.state().cursor as int] as int];
            CommandView::Write { block: write.block, image: write.image }
        } else if self.state().phase == 2 {
            CommandView::Write { block: self.journal_block(), image: self.tail() }
        } else { CommandView::Flush }
    }

    pub(crate) fn begin(&mut self) -> (r: Option<u64>)
        ensures final(self).plan() == old(self).plan(), final(self).tail() == old(self).tail(),
            final(self).scan_result() == old(self).scan_result(),
            final(self).journal_block() == old(self).journal_block(),
            final(self).primary() == old(self).primary(), final(self).partition_bytes() == old(self).partition_bytes(),
            match r {
                Some(id) => !old(self).state().pending && !old(self).state().faulted && old(self).state().phase < 4
                    && final(self).state() == started(old(self).state()) && id == final(self).state().request,
                None => final(self).state() == old(self).state()
                    && (old(self).state().pending || old(self).state().faulted || old(self).state().phase == 4),
            },
    {
        proof { use_type_invariant(&*self); }
        if self.state.pending || self.state.faulted || self.state.phase == 4 { return None; }
        let id = self.state.request + 1;
        self.state = State { phase: self.state.phase, cursor: self.state.cursor,
            request: id, pending: true, faulted: false };
        Some(id)
    }

    pub(crate) fn command(&self) -> (r: Option<Command<'_>>)
        ensures match r {
            Some(c) => self.state().pending && c.view() == self.expected()
                && (match c.view() {
                    CommandView::Write { block, image } => image.len() == 4096
                        && block < self.plan().layout().view().fs_blocks
                        && block as nat * 4096 + 4096 <= self.partition_bytes(),
                    CommandView::Flush => true,
                }),
            None => !self.state().pending,
        },
    {
        proof { use_type_invariant(self); }
        if !self.state.pending { return None; }
        if self.state.phase == 0 {
            let plan = self.scan.replay_plan();
            assert(replay::latest(plan.log(), plan.revocations(), plan.selection()[self.state.cursor as int] as int));
            let write = plan.get(self.state.cursor).unwrap();
            Some(Command::Write { block: write.block(), image: write.image() })
        } else if self.state.phase == 2 {
            Some(Command::Write { block: self.journal_block, image: self.tail.as_slice() })
        } else { Some(Command::Flush) }
    }

    pub(crate) fn complete(&mut self, id: u64, success: bool) -> (r: bool)
        ensures final(self).plan() == old(self).plan(), final(self).tail() == old(self).tail(),
            final(self).scan_result() == old(self).scan_result(),
            final(self).journal_block() == old(self).journal_block(),
            final(self).primary() == old(self).primary(), final(self).partition_bytes() == old(self).partition_bytes(),
            r == (old(self).state().pending && id == old(self).state().request),
            final(self).state() == if r { completed(old(self).state(), old(self).plan().selection().len(), success) }
                else { old(self).state() },
    {
        proof { use_type_invariant(&*self); }
        if !self.state.pending || id != self.state.request { return false; }
        let mut phase = self.state.phase;
        let mut cursor = self.state.cursor;
        let faulted = self.state.faulted || !success;
        if !faulted {
            if phase == 0 {
                cursor += 1;
                if cursor == self.scan.replay_plan().len() { phase = 1; }
            } else { phase += 1; }
        }
        self.state = State { phase, cursor, request: self.state.request, pending: false, faulted };
        true
    }

    pub fn abort(&mut self)
        ensures final(self).plan() == old(self).plan(), final(self).tail() == old(self).tail(),
            final(self).scan_result() == old(self).scan_result(),
            final(self).journal_block() == old(self).journal_block(),
            final(self).primary() == old(self).primary(), final(self).partition_bytes() == old(self).partition_bytes(),
            final(self).state() == (State { faulted: true, ..old(self).state() }),
    {
        proof { use_type_invariant(&*self); }
        self.state = State { phase: self.state.phase, cursor: self.state.cursor,
            request: self.state.request, pending: self.state.pending, faulted: true };
    }

    pub fn finished(&self) -> (r: bool)
        ensures r == (!self.state().faulted && self.state().phase == 4 && !self.state().pending),
    { !self.state.faulted && self.state.phase == 4 && !self.state.pending }

    pub fn failed(&self) -> (r: bool) ensures r == self.state().faulted { self.state.faulted }
}

fn replay_zero_allowed(plan: &replay::ReplayPlan, primary: &[u8], partition_bytes: u64) -> (r: bool)
    requires plan.refines(),
    ensures r == (forall|p: int| 0 <= p < plan.selection().len()
        && (#[trigger] plan.log()[plan.selection()[p] as int]).block == 0 ==>
            super_state::replay_ok(primary@, plan.log()[plan.selection()[p] as int].image, partition_bytes)),
{
    let mut i = 0usize;
    while i < plan.len()
        invariant i <= plan.selection().len(), plan.refines(),
            forall|p: int| 0 <= p < i && (#[trigger] plan.log()[plan.selection()[p] as int]).block == 0 ==>
                super_state::replay_ok(primary@, plan.log()[plan.selection()[p] as int].image, partition_bytes),
        decreases plan.selection().len() - i,
    {
        assert(replay::latest(plan.log(), plan.revocations(), plan.selection()[i as int] as int));
        let write = plan.get(i).unwrap();
        if write.block() == 0 && !super_state::valid_replay(primary, write.image(), partition_bytes) {
            assert(!super_state::replay_ok(primary@, plan.log()[plan.selection()[i as int] as int].image, partition_bytes));
            return false;
        }
        i += 1;
    }
    true
}

#[verifier::rlimit(40)]
pub fn prepare(journal: &[u8], uuid: &[u8], layout: JournalLayout, primary: &[u8], partition_bytes: u64) -> (r: Option<Recovery>)
    ensures match r {
        Some(s) => s.plan().refines() && s.plan().layout().view() == layout.view()
            && s.plan().layout().view().fs_blocks as nat * 4096 <= partition_bytes
            && s.state().cursor == 0 && s.state().request == 0 && !s.state().pending && !s.state().faulted
            && bytes::be32(s.tail(), 24) == s.scan_result().next() as nat
            && s.scan_result().first() as nat == bytes::be32(journal@, 24)
            && s.scan_result().next() as nat == s.scan_result().first() as nat + s.scan_result().committed() as nat
            && s.scan_result().certificate(scan_budget::source(journal@, uuid@, &layout))
            && s.scan_result().maximal(scan_budget::source(journal@, uuid@, &layout))
            && s.scan_result().recognized(journal@, layout.view().journal_blocks, bytes::be32(journal@, 28) as u32,
                crate::crc::fold(0xffffffff, uuid@))
            && (bytes::be32(journal@, 28) == 0 ==> s.plan().log().len() == 0
                && s.plan().revocations().len() == 0 && s.plan().selection().len() == 0)
            && journal_state::preserves(journal@.subrange(0, 4096), s.tail())
            && journal_superblock::accepted(s.tail().subrange(0, 1024), uuid@, layout.view().journal_blocks)
            && s.primary() == primary@ && s.partition_bytes() == partition_bytes
            && superblock::accepted(primary@.subrange(1024, 2048), partition_bytes)
            && (bytes::be32(journal@, 28) != 0 ==> super_state::is_dirty(primary@))
            && (forall|p: int| 0 <= p < s.plan().selection().len() ==>
                (#[trigger] s.plan().log()[s.plan().selection()[p] as int]).block == 0 ==>
                    super_state::replay_ok(primary@, s.plan().log()[s.plan().selection()[p] as int].image, partition_bytes)),
        None => !recovery_profile::input_ok(journal@, uuid@, &layout, primary@, partition_bytes),
    },
{
    hide(crate::crc::fold);
    hide(superblock::accepted);
    let ghost original_layout = layout;
    let ghost can_recover = recovery_profile::input_ok(journal@, uuid@, &layout, primary@, partition_bytes);
    if primary.len() != 4096 { proof { reveal(recovery_profile::input_ok); } return None; }
    let boot = match superblock::parse(&primary[1024..2048], partition_bytes) {
        Some(boot) => boot, None => { proof { reveal(recovery_profile::input_ok); } return None; }
    };
    if boot.blocks() != layout.filesystem_blocks() {
        proof { reveal(recovery_profile::input_ok); } return None;
    }
    assert(layout.view().fs_blocks as nat * 4096 <= partition_bytes) by { reveal(superblock::accepted); }
    let block = match layout.offset(0, 18446744073709551615) {
        Some(offset) => (offset / 4096) as u32, None => {
            proof { reveal(recovery_profile::input_ok); reveal(scan_budget::admitted); }
            return None;
        }
    };
    let scan = match scan::recover(journal, uuid, layout) { Some(s) => s, None => {
        proof { reveal(recovery_profile::input_ok); } return None;
    } };
    if bytes::read_be32(journal, 28).unwrap() != 0 && !boot.needs_recovery() {
        proof { reveal(recovery_profile::input_ok); } return None;
    }
    let plan = scan.replay_plan();
    if !replay_zero_allowed(plan, primary, partition_bytes) {
        proof {
            if can_recover {
                recovery_profile::selected_superblock_targets_satisfy_the_replay_policy(journal@, uuid@,
                    &original_layout, primary@, partition_bytes, &scan);
            }
            assert(!can_recover);
        }
        return None;
    }
    let sequence = scan.next_sequence();
    let blocks = (journal.len() / 4096) as u32;
    assert(journal_state::input_ok(journal@.subrange(0, 4096), uuid@, blocks, sequence, 0)) by {
        assert(journal@.subrange(0, 4096).subrange(0, 1024) =~= journal@.subrange(0, 1024));
        assert(0 < sequence);
    }
    let tail = match journal_state::encode(&journal[..4096], uuid, blocks, sequence, 0) {
        Some(s) => s, None => { return None; }
    };
    let phase = if scan.replay_plan().len() == 0 { 1 } else { 0 };
    Some(Recovery { scan, tail, journal_block: block, primary: Ghost(primary@), partition_bytes,
        state: State { phase, cursor: 0, request: 0, pending: false, faulted: false } })
}

pub proof fn tail_write_is_after_home_flush(s: State, count: nat)
    requires wf(s, count), s.pending, s.phase == 2,
    ensures s.cursor == count, s.request as nat == count + 2 || s.faulted,
{
}

pub proof fn success_requires_both_flush_completions(s: State, count: nat)
    requires wf(s, count), !s.faulted, s.phase == 4, !s.pending,
    ensures s.cursor == count, s.request as nat == count + 3,
{
}

pub open spec fn remaining(s: State, count: nat) -> nat {
    (count - s.cursor + if s.phase == 0 { 3nat } else { (4 - s.phase) as nat }) as nat
}

pub proof fn a_successful_pair_makes_progress(s: State, count: nat)
    requires wf(s, count), !s.faulted, !s.pending, s.phase < 4,
    ensures wf(started(s), count), wf(completed(started(s), count, true), count),
        !completed(started(s), count, true).pending, !completed(started(s), count, true).faulted,
        remaining(completed(started(s), count, true), count) + 1 == remaining(s, count),
{
}

pub closed spec fn normal_finish(s: State, count: nat) -> State
    recommends wf(s, count), !s.faulted, !s.pending,
    decreases remaining(s, count),
{
    if !wf(s, count) || s.faulted || s.pending || s.phase == 4 { s }
    else { normal_finish(completed(started(s), count, true), count) }
}

pub proof fn every_failure_free_recovery_has_a_finite_completion(s: State, count: nat)
    requires wf(s, count), !s.faulted, !s.pending,
    ensures normal_finish(s, count).phase == 4,
        !normal_finish(s, count).pending, !normal_finish(s, count).faulted,
        normal_finish(s, count).request as nat == s.request as nat + remaining(s, count),
    decreases remaining(s, count),
{
    if s.phase < 4 {
        a_successful_pair_makes_progress(s, count);
        every_failure_free_recovery_has_a_finite_completion(completed(started(s), count, true), count);
    }
}

}
