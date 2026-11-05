// SPDX-License-Identifier: MPL-2.0

//! Conditional durability/crash closure for the entire xattr patch set.
//! The primary's precommit recovery marker is framed separately from its
//! journalled allocation counters and EXT_ATTR feature promotion.

use vstd::prelude::*;
use crate::{disk_image, layout::JournalLayout, patch_set, replay_refinement::{self, Disk},
    transaction::{self, TransactionView}, transaction_refinement, write_device::{self, Machine},
    write_io::Images, write_media, write_recognition, write_recovery, writer_admission::{self, AdmissionView}, transaction::ImageView};

verus! {

pub open spec fn admitted(patches: Seq<ImageView>, a: AdmissionView, images: Images) -> bool {
    writer_admission::valid(a, images) && images.tx.original == patches
}
proof fn one_target(before: Disk, tx: TransactionView, i: int)
    requires transaction::wf(tx), replay_refinement::all_targets_exist(before, transaction_refinement::log(tx)), 0 <= i < tx.original.len(),
    ensures before.dom().contains(tx.original[i].block),
        replay_refinement::chronological(before, transaction_refinement::log(tx), Seq::empty())[tx.original[i].block] == tx.original[i].image,
{
    let log = transaction_refinement::log(tx); let block = tx.original[i].block;
    replay_refinement::chronological_lookup(before, log, Seq::empty(), block);
    replay_refinement::last_eligible_characterizes_latest(log, Seq::empty(), block);
    if let Some(j) = replay_refinement::last_eligible(log, Seq::empty(), block) {
        if i < j { assert(tx.original[i].block != tx.original[j as int].block); }
        if j < i { assert(tx.original[i].block != tx.original[j as int].block); }
        assert(j == i);
    } else { assert(crate::replay::blocked(block, log[i].sequence, Seq::empty())); }
}

pub proof fn completed_xattr_transactions_have_every_exact_durable_home_and_a_retired_log(patches: Seq<ImageView>, a: AdmissionView, images: Images, machine: Machine)
    requires admitted(patches, a, images), write_device::inv(machine, images.tx.payloads.len()), machine.io.phase is Done, !machine.io.pending, !machine.io.faulted,
    ensures write_media::disk(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images)[images.journal_block] == images.tail,
        forall|i: int| 0 <= i < patches.len() ==> #[trigger]
            write_media::disk(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images)[patches[i].block] == patches[i].image,
{
    crate::writer_image::an_admitted_source_supplies_the_physical_writer_context(a, images);
    write_recognition::successful_writer_completion_has_exact_durable_home_bytes_and_retired_tail(machine,
        disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images);
}

pub proof fn every_recovered_nonprimary_xattr_home_uses_the_same_commit_decision(patches: Seq<ImageView>, a: AdmissionView,
    images: Images, machine: Machine, layout: &JournalLayout, scan: &crate::scan::Scan, recovery: crate::recovery_device::Machine, tail: Seq<u8>, i: int)
    requires admitted(patches, a, images), write_device::inv(machine, images.tx.payloads.len()), layout.wf(), layout.view() == images.tx.layout,
        write_recovery::returned(scan, write_recovery::source(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images, layout)),
        crate::recovery_device::inv(recovery, write_media::disk(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images), scan.plan(), images.journal_block, tail),
        recovery.io.phase == 4, !recovery.io.faulted, !recovery.io.pending, 0 <= i < patches.len(), patches[i].block != 0,
    ensures recovery.stable[patches[i].block] == if machine.stable.contains(6 + images.tx.payloads.len()) { patches[i].image }
        else { disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks)[patches[i].block] },
{
    hide(crate::crc::fold);
    let before = disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks); let block = patches[i].block;
    crate::writer_image::an_admitted_source_supplies_the_physical_writer_context(a, images);
    write_recovery::original_targets_exist(before, images);
    assert(crate::write_io::valid_images(images)) by { reveal(writer_admission::valid); }
    reveal(crate::write_io::valid_images);
    assert(transaction::wf(images.tx));
    one_target(before, images.tx, i);
    assert(!(images.tx.layout.start <= block < images.tx.layout.start as int + images.tx.layout.journal_blocks)) by {
        assert(crate::replay::payload_for_layout(images.tx.tags[i], images.tx.payloads[i], images.tx.sequence, images.tx.seed, images.tx.layout));
        reveal(crate::replay::payload_for_layout);
    }
    write_recovery::successful_recovery_of_every_writer_cut_has_before_or_after_home_bytes(machine, before, images, layout, scan, recovery, tail, block);
}

proof fn primary_facts(a: AdmissionView, images: Images)
    requires writer_admission::valid(a, images),
    ensures write_recognition::context(disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images),
        crate::write_io::valid_images(images), write_media::targets_exist(disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images), transaction::wf(images.tx), images.journal_block > 1,
        disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks).dom().contains(0),
        disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks)[0] == a.boot.source.subrange(0, 4096),
        crate::super_state::preserves(disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks)[0], images.dirty),
{
    hide(crate::crc::fold);
    crate::writer_image::an_admitted_source_supplies_the_physical_writer_context(a, images);
    reveal(writer_admission::valid); reveal(crate::write_io::valid_images);
}
proof fn plan_indices(plan: &crate::replay::ReplayPlan)
    requires plan.refines(),
    ensures replay_refinement::indices_valid(plan.log(), plan.selection()),
{
    assert forall|p: int| 0 <= p < plan.selection().len() implies #[trigger] plan.selection()[p] < plan.log().len() by {
        assert(crate::replay::latest(plan.log(), plan.revocations(), plan.selection()[p] as int));
    }
}
proof fn activation_precedes_a_stable_commit(machine: Machine, count: nat)
    requires write_device::inv(machine, count), machine.stable.contains(6 + count),
    ensures machine.stable.contains(2),
{
    assert(machine.issued.contains(6 + count));
    assert(6 + count <= crate::write_protocol::completed_count(machine.io, count));
    assert(write_device::is_write(2, count) && write_device::fence_after(2, count) < crate::write_protocol::completed_count(machine.io, count));
}

#[verifier::rlimit(40)]
pub proof fn every_recovered_primary_xattr_home_has_old_counters_or_the_exact_committed_image(patches: Seq<ImageView>, a: AdmissionView,
    images: Images, machine: Machine, layout: &JournalLayout, scan: &crate::scan::Scan, recovery: crate::recovery_device::Machine, tail: Seq<u8>, i: int)
    requires admitted(patches, a, images), write_device::inv(machine, images.tx.payloads.len()), layout.wf(), layout.view() == images.tx.layout,
        write_recovery::returned(scan, write_recovery::source(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images, layout)),
        crate::recovery_device::inv(recovery, write_media::disk(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images), scan.plan(), images.journal_block, tail),
        recovery.io.phase == 4, !recovery.io.faulted, !recovery.io.pending, 0 <= i < patches.len(), patches[i].block == 0,
    ensures if machine.stable.contains(6 + images.tx.payloads.len()) { recovery.stable[0] == patches[i].image }
        else { crate::super_state::preserves(a.boot.source.subrange(0, 4096), recovery.stable[0]) },
{
    hide(crate::crc::fold);
    hide(replay_refinement::selected); hide(replay_refinement::chronological);
    hide(transaction::wf); hide(crate::write_io::valid_images);
    hide(write_recovery::returned); hide(write_recognition::context);
    hide(write_device::inv); hide(crate::recovery_device::inv); hide(write_media::apply);
    let before = disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks);
    let media = write_media::disk(machine, before, images); let count = images.tx.payloads.len();
    primary_facts(a, images);
    write_recovery::snapshot_state(machine, before, images, layout);
    write_recovery::every_returned_writer_scan_is_empty_or_the_complete_transaction(machine, before, images, layout, scan);
    crate::recovery_device::success_image_equals_linux_redo(recovery, media, scan.plan(), images.journal_block, tail);
    replay_refinement::executable_selection_equals_chronological_redo(media, scan.plan());
    write_media::apply_preserves_domain(before, images, machine.stable, write_device::total(count));
    plan_indices(scan.plan());
    replay_refinement::selected_domain(media, scan.plan().log(), scan.plan().selection());
    assert(recovery.stable[0] == replay_refinement::selected(media, scan.plan().log(), scan.plan().selection())[0]);
    if !machine.stable.contains(6 + count) {
        assert(replay_refinement::selected(media, scan.plan().log(), scan.plan().selection()) == media) by { reveal(replay_refinement::selected); }
        write_recognition::before_a_durable_commit_no_checkpoint_image_can_be_stable(machine, count);
        crate::write_media::before_checkpoint_block_zero_is_only_the_recovery_flag_image(machine, before, images);
        if machine.stable.contains(0) { assert(crate::super_state::preserves(before[0], images.dirty)); }
        else { assert(crate::super_state::preserves(before[0], before[0])); }

    } else if write_recovery::source(machine, before, images, layout).start != 0 {
        assert(scan.plan().log() == transaction_refinement::log(images.tx));
        assert(scan.plan().revocations() =~= Seq::<crate::replay::Revocation>::empty());
        one_target(media, images.tx, i);
    } else {
        activation_precedes_a_stable_commit(machine, count);
        assert(machine.stable.contains(9 + 2 * count));
        write_recognition::clearing_the_journal_tail_requires_durable_home_afterimages(machine, before, images);
        assert(replay_refinement::selected(media, scan.plan().log(), scan.plan().selection()) == media) by { reveal(replay_refinement::selected); }
    }
}

pub proof fn every_writer_cut_recovers_all_xattr_metadata_together(patches: Seq<ImageView>, a: AdmissionView,
    images: Images, machine: Machine, layout: &JournalLayout, scan: &crate::scan::Scan, recovery: crate::recovery_device::Machine, tail: Seq<u8>)
    requires admitted(patches, a, images), write_device::inv(machine, images.tx.payloads.len()), layout.wf(), layout.view() == images.tx.layout,
        write_recovery::returned(scan, write_recovery::source(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images, layout)),
        crate::recovery_device::inv(recovery, write_media::disk(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images), scan.plan(), images.journal_block, tail),
        recovery.io.phase == 4, !recovery.io.faulted, !recovery.io.pending,
    ensures forall|i: int| 0 <= i < patches.len() ==> (if machine.stable.contains(6 + images.tx.payloads.len()) {
            #[trigger] recovery.stable[patches[i].block] == patches[i].image
        } else if patches[i].block == 0 { crate::super_state::preserves(a.boot.source.subrange(0, 4096), recovery.stable[0]) }
        else { recovery.stable[patches[i].block] == disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks)[patches[i].block] }),
{
    assert forall|i: int| 0 <= i < patches.len() implies (if machine.stable.contains(6 + images.tx.payloads.len()) {
            #[trigger] recovery.stable[patches[i].block] == patches[i].image
        } else if patches[i].block == 0 { crate::super_state::preserves(a.boot.source.subrange(0, 4096), recovery.stable[0]) }
        else { recovery.stable[patches[i].block] == disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks)[patches[i].block] }) by {
        if patches[i].block == 0 { every_recovered_primary_xattr_home_has_old_counters_or_the_exact_committed_image(patches, a, images, machine, layout, scan, recovery, tail, i); }
        else { every_recovered_nonprimary_xattr_home_uses_the_same_commit_decision(patches, a, images, machine, layout, scan, recovery, tail, i); }
    }
}

}
