// SPDX-License-Identifier: MPL-2.0

//! Repeated crash recovery preserves preparation admission. A crash projects
//! stable bytes and drops volatile cache; a new attempt requires the same
//! quiescent-start device contract. Abort alone does not provide that contract.

use vstd::prelude::*;
use crate::{bytes, crc, journal_superblock, journal_view, layout::JournalLayout, recovery_device::{self, Machine},
    recovery_profile, replay, replay_refinement::{self, Disk}, scan, scan_budget, super_state, superblock};

verus! {

pub open spec fn ready(before: Disk, uuid: Seq<u8>, layout: &JournalLayout,
    result: &scan::Scan, tail: Seq<u8>) -> bool {
    let journal = journal_view::snapshot(before, layout.view());
    &&& layout.wf() && journal_view::mapped(before, layout.view()) && before.dom().contains(0)
    &&& result.plan().refines() && result.plan().layout().view() == layout.view()
    &&& result.certificate(scan_budget::source(journal, uuid, layout))
    &&& result.maximal(scan_budget::source(journal, uuid, layout))
    &&& (bytes::be32(journal, 28) == 0 ==> result.plan().selection().len() == 0)
    &&& tail.len() == 4096 && bytes::be32(tail, 28) == 0
    &&& journal_superblock::accepted(tail.subrange(0, 1024), uuid, layout.view().journal_blocks)
}

#[verifier::opaque]
pub open spec fn context(before: Disk, uuid: Seq<u8>, layout: &JournalLayout, partition_bytes: u64,
    result: &scan::Scan, tail: Seq<u8>) -> bool {
    ready(before, uuid, layout, result, tail)
        && recovery_profile::input_ok(journal_view::snapshot(before, layout.view()), uuid, layout, before[0], partition_bytes)
}

pub proof fn every_recovery_cut_keeps_the_journal_mapped(m: Machine, before: Disk, uuid: Seq<u8>, layout: &JournalLayout,
    partition_bytes: u64, result: &scan::Scan, tail: Seq<u8>)
    requires context(before, uuid, layout, partition_bytes, result, tail),
        recovery_device::inv(m, before, result.plan(), layout.view().start, tail),
    ensures journal_view::mapped(m.stable, layout.view()),
        forall|logical: u32| 1 <= logical < layout.view().journal_blocks ==>
            (#[trigger] m.stable[(layout.view().start + logical) as u32]) == before[(layout.view().start + logical) as u32],
{
    hide(crc::fold);
    reveal(context);
    assert forall|logical: u32| 1 <= logical < layout.view().journal_blocks implies
        (#[trigger] m.stable[(layout.view().start + logical) as u32]) == before[(layout.view().start + logical) as u32] by {
        recovery_device::all_non_superblock_journal_records_are_preserved(m, before, result.plan(), layout.view().start, tail, logical);
    }
    assert forall|logical: u32| logical < layout.view().journal_blocks implies
        #[trigger] m.stable.dom().contains((layout.view().start + logical) as u32)
        && m.stable[(layout.view().start + logical) as u32].len() == 4096 by {
        assert(before.dom().contains((layout.view().start + logical) as u32));
        if logical > 0 { assert(m.stable[(layout.view().start + logical) as u32] == before[(layout.view().start + logical) as u32]); }
    }
}

pub proof fn partial_recovery_keeps_the_primary_volume_identity(m: Machine, before: Disk, uuid: Seq<u8>, layout: &JournalLayout,
    partition_bytes: u64, result: &scan::Scan, tail: Seq<u8>)
    requires context(before, uuid, layout, partition_bytes, result, tail),
        recovery_device::inv(m, before, result.plan(), layout.view().start, tail),
    ensures m.stable[0].len() == 4096 && superblock::accepted(m.stable[0].subrange(1024, 2048), partition_bytes),
        bytes::le32(m.stable[0], 1028) == layout.view().fs_blocks && m.stable[0].subrange(1128, 1144) == uuid,
        bytes::be32(journal_view::snapshot(before, layout.view()), 28) != 0 ==>
            super_state::replay_ok(before[0], m.stable[0], partition_bytes),
{
    hide(crc::fold);
    hide(superblock::accepted);
    reveal(context);
    reveal(recovery_profile::input_ok);
    let plan = result.plan();
    let journal = journal_view::snapshot(before, layout.view());
    recovery_profile::selected_superblock_targets_satisfy_the_replay_policy(journal, uuid, layout, before[0], partition_bytes, result);
    if recovery_device::target(plan, 0) {
        let p = choose|p: int| 0 <= p < plan.selection().len() && plan.log()[plan.selection()[p] as int].block == 0;
        assert(bytes::be32(journal, 28) != 0);
        assert forall|q: int| 0 <= q < plan.selection().len() implies #[trigger] plan.selection()[q] < plan.log().len() by {
            assert(replay::latest(plan.log(), plan.revocations(), plan.selection()[q] as int));
        }
        replay_refinement::selected_target_lookup(before, plan.log(), plan.selection(), p);
        assert(super_state::replay_ok(before[0], recovery_device::final_home(before, plan)[0], partition_bytes));
    } else {
        assert(m.stable[0] == before[0]);
    }
    if bytes::be32(journal, 28) != 0 {
        assert(super_state::replay_ok(before[0], m.stable[0], partition_bytes));
        super_state::replay_preserves_geometry_and_keeps_recovery(before[0], m.stable[0], partition_bytes);
    }
}

pub proof fn every_recovery_crash_snapshot_can_prepare_another_recovery(m: Machine, before: Disk, uuid: Seq<u8>, layout: &JournalLayout,
    partition_bytes: u64, result: &scan::Scan, tail: Seq<u8>)
    requires context(before, uuid, layout, partition_bytes, result, tail),
        recovery_device::inv(m, before, result.plan(), layout.view().start, tail),
    ensures recovery_profile::input_ok(journal_view::snapshot(m.stable, layout.view()), uuid, layout, m.stable[0], partition_bytes),
{
    hide(crc::fold);
    reveal(context);
    let old_journal = journal_view::snapshot(before, layout.view());
    let journal = journal_view::snapshot(m.stable, layout.view());
    every_recovery_cut_keeps_the_journal_mapped(m, before, uuid, layout, partition_bytes, result, tail);
    partial_recovery_keeps_the_primary_volume_identity(m, before, uuid, layout, partition_bytes, result, tail);
    if m.stable[layout.view().start] == before[layout.view().start] {
        assert forall|logical: u32| logical < layout.view().journal_blocks implies
            (#[trigger] before[(layout.view().start + logical) as u32]) == m.stable[(layout.view().start + logical) as u32] by { }
        journal_view::equal_journal_blocks_have_equal_snapshots(before, m.stable, layout.view());
        assert(journal == old_journal);
        if bytes::be32(journal, 28) != 0 {
            assert(recovery_profile::safe_committed_streams(scan_budget::source(journal, uuid, layout), before[0], partition_bytes)) by {
                reveal(recovery_profile::input_ok);
            }
            recovery_profile::safe_streams_survive_valid_superblock_replay(scan_budget::source(journal, uuid, layout),
                before[0], m.stable[0], partition_bytes);
        }
    } else {
        journal_view::snapshot_block_is_the_physical_image(m.stable, layout.view(), 0);
        assert(m.stable[layout.view().start] == tail);
        assert(journal.subrange(0, 1024) =~= tail.subrange(0, 1024));
        assert(scan_budget::admitted(journal, uuid, layout)) by { reveal(scan_budget::admitted); }
    }
    reveal(recovery_profile::input_ok);
}

pub proof fn a_new_scan_of_uncleared_recovery_keeps_the_same_committed_input(m: Machine, before: Disk, uuid: Seq<u8>, layout: &JournalLayout,
    partition_bytes: u64, old: &scan::Scan, tail: Seq<u8>, next: &scan::Scan)
    requires context(before, uuid, layout, partition_bytes, old, tail),
        recovery_device::inv(m, before, old.plan(), layout.view().start, tail),
        m.stable[layout.view().start] == before[layout.view().start],
        bytes::be32(journal_view::snapshot(before, layout.view()), 28) != 0,
        next.certificate(scan_budget::source(journal_view::snapshot(m.stable, layout.view()), uuid, layout)),
        next.maximal(scan_budget::source(journal_view::snapshot(m.stable, layout.view()), uuid, layout)),
    ensures old.plan().log() == next.plan().log(), old.plan().revocations() == next.plan().revocations(), old.next() == next.next(),
{
    hide(crc::fold);
    reveal(context);
    every_recovery_cut_keeps_the_journal_mapped(m, before, uuid, layout, partition_bytes, old, tail);
    assert forall|logical: u32| logical < layout.view().journal_blocks implies
        (#[trigger] before[(layout.view().start + logical) as u32]) == m.stable[(layout.view().start + logical) as u32] by { }
    journal_view::equal_journal_blocks_have_equal_snapshots(before, m.stable, layout.view());
    scan::recovered_input_is_unique_for_the_frozen_journal(old, next,
        scan_budget::source(journal_view::snapshot(before, layout.view()), uuid, layout));
}

pub struct Attempt<'a> { pub result: &'a scan::Scan, pub tail: Seq<u8>, pub cut: Machine }

pub open spec fn attempt_trace(snapshots: Seq<Disk>, attempts: Seq<Attempt<'_>>, uuid: Seq<u8>, layout: &JournalLayout) -> bool {
    &&& snapshots.len() == attempts.len() + 1
    &&& (forall|i: int| 0 <= i < attempts.len() ==> {
        &&& #[trigger] ready(snapshots[i], uuid, layout, attempts[i].result, attempts[i].tail)
        &&& recovery_device::inv(attempts[i].cut, snapshots[i], attempts[i].result.plan(), layout.view().start, attempts[i].tail)
        &&& snapshots[i + 1] == attempts[i].cut.stable
    })
}

proof fn admission_at_attempt(snapshots: Seq<Disk>, attempts: Seq<Attempt<'_>>, uuid: Seq<u8>, layout: &JournalLayout,
    partition_bytes: u64, cut: nat)
    requires attempt_trace(snapshots, attempts, uuid, layout), cut < snapshots.len(),
        recovery_profile::input_ok(journal_view::snapshot(snapshots[0], layout.view()), uuid, layout, snapshots[0][0], partition_bytes),
    ensures recovery_profile::input_ok(journal_view::snapshot(snapshots[cut as int], layout.view()), uuid, layout,
        snapshots[cut as int][0], partition_bytes),
    decreases cut,
{
    if cut > 0 {
        admission_at_attempt(snapshots, attempts, uuid, layout, partition_bytes, (cut - 1) as nat);
        let i = cut as int - 1;
        assert(ready(snapshots[i], uuid, layout, attempts[i].result, attempts[i].tail));
        assert(context(snapshots[i], uuid, layout, partition_bytes, attempts[i].result, attempts[i].tail)) by { reveal(context); }
        every_recovery_crash_snapshot_can_prepare_another_recovery(attempts[i].cut, snapshots[i], uuid, layout,
            partition_bytes, attempts[i].result, attempts[i].tail);
    }
}

pub proof fn every_finite_sequence_of_recovery_crashes_preserves_admission(snapshots: Seq<Disk>, attempts: Seq<Attempt<'_>>,
    uuid: Seq<u8>, layout: &JournalLayout, partition_bytes: u64)
    requires attempt_trace(snapshots, attempts, uuid, layout),
        recovery_profile::input_ok(journal_view::snapshot(snapshots[0], layout.view()), uuid, layout, snapshots[0][0], partition_bytes),
    ensures forall|i: int| 0 <= i < snapshots.len() ==>
        #[trigger] recovery_profile::input_ok(journal_view::snapshot(snapshots[i], layout.view()), uuid, layout, snapshots[i][0], partition_bytes),
{
    assert forall|i: int| 0 <= i < snapshots.len() implies
        #[trigger] recovery_profile::input_ok(journal_view::snapshot(snapshots[i], layout.view()), uuid, layout, snapshots[i][0], partition_bytes) by {
        admission_at_attempt(snapshots, attempts, uuid, layout, partition_bytes, i as nat);
    }
}

}
