// SPDX-License-Identifier: MPL-2.0

//! Finite repeated recovery preserves the exact byte-valued recovery target.
//! Each fresh attempt reads a quiescent snapshot after a crash/reset boundary;
//! an abort callback alone does not establish that device premise.

use vstd::prelude::*;
use crate::{bytes, crc, journal_view, journal_window::WindowView, journal_window_media::{self as media, Media},
    layout::JournalLayout, recovery_closure::{self, Attempt}, recovery_device, recovery_profile,
    replay, replay_refinement::{self as redo, Disk}, scan, scan_budget, window_provenance::*,
    window_recognition as recognition, window_recovery, window_recovery_profile, window_redo, write_recovery};

verus! {

pub open spec fn scanned(image: Disk, uuid: Seq<u8>, layout: &JournalLayout, result: &scan::Scan) -> bool {
    &&& result.plan().refines()
    &&& result.certificate(scan_budget::source(journal_view::snapshot(image, layout.view()), uuid, layout))
    &&& result.maximal(scan_budget::source(journal_view::snapshot(image, layout.view()), uuid, layout))
    &&& (bytes::be32(journal_view::snapshot(image, layout.view()), 28) == 0 ==> result.plan().selection().len() == 0)
}

pub open spec fn target(image: Disk, result: &scan::Scan) -> Disk { redo::selected(image, result.plan().log(), result.plan().selection()) }

proof fn selection_indices(plan: &replay::ReplayPlan)
    requires plan.refines(),
    ensures redo::indices_valid(plan.log(), plan.selection()),
{
    assert forall|p: int| 0 <= p < plan.selection().len() implies (#[trigger] plan.selection()[p]) < plan.log().len() by {
        assert(replay::latest(plan.log(), plan.revocations(), plan.selection()[p] as int));
    }
}

proof fn scans_of_the_same_snapshot_have_the_same_recovery_target(image: Disk, uuid: Seq<u8>, layout: &JournalLayout, a: &scan::Scan, b: &scan::Scan)
    requires scanned(image, uuid, layout, a), scanned(image, uuid, layout, b), redo::all_targets_exist(image, a.plan().log()),
    ensures target(image, a) == target(image, b),
{
    if bytes::be32(journal_view::snapshot(image, layout.view()), 28) == 0 {
        reveal(redo::selected);
    } else {
        scan::recovered_input_is_unique_for_the_frozen_journal(a, b, scan_budget::source(journal_view::snapshot(image, layout.view()), uuid, layout));
        redo::executable_selection_equals_chronological_redo(image, a.plan());
        redo::executable_selection_equals_chronological_redo(image, b.plan());
    }
}

proof fn a_recovery_cut_preserves_the_next_scans_exact_target(cut: recovery_device::Machine, before: Disk, uuid: Seq<u8>, layout: &JournalLayout,
    partition_bytes: u64, old: &scan::Scan, tail: Seq<u8>, next: &scan::Scan, block: u32)
    requires recovery_closure::context(before, uuid, layout, partition_bytes, old, tail),
        recovery_device::inv(cut, before, old.plan(), layout.view().start, tail), scanned(cut.stable, uuid, layout, next),
        before.dom().contains(block), block != layout.view().start,
    ensures target(cut.stable, next)[block] == target(before, old)[block],
{
    hide(crc::fold);
    reveal(recovery_closure::context);
    let journal = layout.view().start;
    let old_journal = journal_view::snapshot(before, layout.view());
    let new_journal = journal_view::snapshot(cut.stable, layout.view());
    recovery_closure::every_recovery_cut_keeps_the_journal_mapped(cut, before, uuid, layout, partition_bytes, old, tail);
    if cut.stable[journal] == before[journal] {
        if bytes::be32(old_journal, 28) != 0 {
            recovery_closure::a_new_scan_of_uncleared_recovery_keeps_the_same_committed_input(cut, before, uuid, layout, partition_bytes, old, tail, next);
            recovery_device::uncleared_tail_leaves_a_restartable_partial_replay(cut, before, old.plan(), journal, tail);
            assert(redo::all_targets_exist(cut.stable, next.plan().log()));
            redo::executable_selection_equals_chronological_redo(cut.stable, old.plan());
            redo::executable_selection_equals_chronological_redo(cut.stable, next.plan());
            redo::executable_selection_equals_chronological_redo(before, old.plan());
        } else {
            assert forall|logical: u32| logical < layout.view().journal_blocks implies
                (#[trigger] before[(journal + logical) as u32]) == cut.stable[(journal + logical) as u32] by { }
            journal_view::equal_journal_blocks_have_equal_snapshots(before, cut.stable, layout.view());
            assert(next.plan().selection().len() == 0 && old.plan().selection().len() == 0);
            assert(!recovery_device::target(old.plan(), block));
            assert(cut.stable[block] == before[block]);
            reveal(redo::selected);
        }
    } else {
        assert(cut.stable[journal] == tail && cut.io.phase >= 2);
        journal_view::snapshot_block_is_the_physical_image(cut.stable, layout.view(), 0);
        assert(bytes::be32(new_journal, 28) == bytes::be32(tail, 28));
        assert(next.plan().selection().len() == 0);
        assert(target(cut.stable, next) == cut.stable) by { reveal(redo::selected); }
        if recovery_device::target(old.plan(), block) {
            assert(cut.stable[block] == recovery_device::final_home(before, old.plan())[block]);
        } else {
            selection_indices(old.plan());
            assert forall|p: int| 0 <= p < old.plan().selection().len() implies (#[trigger] old.plan().log()[old.plan().selection()[p] as int]).block != block by { }
            redo::selected_frame(before, old.plan().log(), old.plan().selection(), block);
            assert(cut.stable[block] == before[block]);
        }
    }
}

proof fn attempt_domains(images: Seq<Disk>, attempts: Seq<Attempt<'_>>, uuid: Seq<u8>, layout: &JournalLayout, cut: nat)
    requires recovery_closure::attempt_trace(images, attempts, uuid, layout), cut < images.len(),
    ensures images[cut as int].dom() == images[0].dom(),
    decreases cut,
{
    if cut > 0 {
        attempt_domains(images, attempts, uuid, layout, (cut - 1) as nat);
        assert(recovery_closure::ready(images[cut as int - 1], uuid, layout, attempts[cut as int - 1].result, attempts[cut as int - 1].tail));
        assert(recovery_device::inv(attempts[cut as int - 1].cut, images[cut as int - 1], attempts[cut as int - 1].result.plan(), layout.view().start, attempts[cut as int - 1].tail));
        assert(images[cut as int] == attempts[cut as int - 1].cut.stable);
    }
}

proof fn target_at_attempt(images: Seq<Disk>, attempts: Seq<Attempt<'_>>, uuid: Seq<u8>, layout: &JournalLayout, partition_bytes: u64,
    initial_scan: &scan::Scan, next_scan: &scan::Scan, cut: nat, block: u32)
    requires recovery_closure::attempt_trace(images, attempts, uuid, layout), cut < images.len(),
        scanned(images[0], uuid, layout, initial_scan), redo::all_targets_exist(images[0], initial_scan.plan().log()),
        scanned(images[cut as int], uuid, layout, next_scan), images[0].dom().contains(block), block != layout.view().start,
        forall|i: int| 0 <= i < images.len() ==> #[trigger] recovery_profile::input_ok(journal_view::snapshot(images[i], layout.view()), uuid, layout, images[i][0], partition_bytes),
    ensures target(images[cut as int], next_scan)[block] == target(images[0], initial_scan)[block],
    decreases cut,
{
    if cut == 0 {
        scans_of_the_same_snapshot_have_the_same_recovery_target(images[0], uuid, layout, initial_scan, next_scan);
    } else {
        let i = cut as int - 1;
        assert(recovery_closure::ready(images[i], uuid, layout, attempts[i].result, attempts[i].tail));
        assert(scanned(images[i], uuid, layout, attempts[i].result));
        target_at_attempt(images, attempts, uuid, layout, partition_bytes, initial_scan, attempts[i].result, (cut - 1) as nat, block);
        assert(recovery_profile::input_ok(journal_view::snapshot(images[i], layout.view()), uuid, layout, images[i][0], partition_bytes));
        assert(recovery_closure::context(images[i], uuid, layout, partition_bytes, attempts[i].result, attempts[i].tail)) by { reveal(recovery_closure::context); }
        attempt_domains(images, attempts, uuid, layout, (cut - 1) as nat);
        a_recovery_cut_preserves_the_next_scans_exact_target(attempts[i].cut, images[i], uuid, layout, partition_bytes, attempts[i].result, attempts[i].tail, next_scan, block);
    }
}

pub proof fn every_finite_recovery_crash_history_preserves_the_window_recovery_target(m: Media, initial: Disk, v: WindowView, layout: &JournalLayout,
    images: Seq<Disk>, attempts: Seq<Attempt<'_>>, first_scan: &scan::Scan, last_scan: &scan::Scan, block: u32)
    requires context(initial, v), media::inv(m, v), layout.wf(), layout.view() == v.layout,
        images[0] == media::disk(m, initial, v), recovery_closure::attempt_trace(images, attempts, v.uuid, layout),
        write_recovery::returned(first_scan, recognition::actual_source(m, initial, v, layout)),
        scanned(images.last(), v.uuid, layout, last_scan), window_redo::home_block(initial, v, block),
    ensures target(images.last(), last_scan)[block] == window_recovery::recovered_prefix(m, initial, v)[block],
{
    window_recovery_profile::all_finite_recovery_attempts_after_a_window_crash_preserve_admission(m, initial, v, layout, images, attempts);
    window_recovery::every_returned_actual_scan_has_exactly_the_durable_replay_suffix(m, initial, v, layout, first_scan);
    window_recovery::scanning_and_replaying_every_window_cut_gives_the_exact_complete_durable_prefix(m, initial, v, layout, first_scan, block);
    media::every_media_cut_preserves_the_device_domain(m, initial, v);
    assert(scanned(images[0], v.uuid, layout, first_scan));
    target_at_attempt(images, attempts, v.uuid, layout, v.partition_bytes, first_scan, last_scan, (images.len() - 1) as nat, block);
}

pub proof fn successful_recovery_after_any_finite_crash_history_has_exact_window_prefix_bytes(m: Media, initial: Disk, v: WindowView,
    layout: &JournalLayout, images: Seq<Disk>, attempts: Seq<Attempt<'_>>, first_scan: &scan::Scan, last_scan: &scan::Scan,
    recovery: recovery_device::Machine, tail: Seq<u8>, block: u32)
    requires context(initial, v), media::inv(m, v), layout.wf(), layout.view() == v.layout,
        images[0] == media::disk(m, initial, v), recovery_closure::attempt_trace(images, attempts, v.uuid, layout),
        write_recovery::returned(first_scan, recognition::actual_source(m, initial, v, layout)),
        scanned(images.last(), v.uuid, layout, last_scan), window_redo::home_block(initial, v, block),
        recovery_device::inv(recovery, images.last(), last_scan.plan(), v.layout.start, tail),
        recovery.io.phase == 4, !recovery.io.pending, !recovery.io.faulted,
    ensures recovery.stable[block] == window_recovery::recovered_prefix(m, initial, v)[block],
{
    every_finite_recovery_crash_history_preserves_the_window_recovery_target(m, initial, v, layout, images, attempts, first_scan, last_scan, block);
    recovery_device::success_image_equals_linux_redo(recovery, images.last(), last_scan.plan(), v.layout.start, tail);
    redo::executable_selection_equals_chronological_redo(images.last(), last_scan.plan());
    assert(block != v.layout.start);
}

}
