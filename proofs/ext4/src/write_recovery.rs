// SPDX-License-Identifier: MPL-2.0

//! The actual scanner and selected replay recover every single-writer cut's
//! complete nonjournal home image. Block zero has a separate recovery-bit and
//! immutable-volume-identity policy. The device contract remains explicit.

use vstd::prelude::*;
use crate::{bytes, crc, journal_view, layout::JournalLayout, recovery_device,
    replay, replay_refinement::{self, Disk}, scan, scan_budget, scan_trace::Source,
    transaction_refinement, write_device::{self, Machine}, write_io, write_media, write_recognition};

verus! {

pub open spec fn source(m: Machine, before: Disk, v: write_io::Images, layout: &JournalLayout) -> Source {
    scan_budget::source(journal_view::snapshot(write_media::disk(m, before, v), v.tx.layout), v.tx.uuid, layout)
}

pub open spec fn returned(result: &scan::Scan, source: Source) -> bool {
    &&& result.plan().refines() && result.plan().layout().view() == source.layout
    &&& result.first() == source.first
    &&& result.certificate(source) && result.maximal(source)
    &&& result.recognized(source.journal, source.blocks, source.start, source.seed)
    &&& (source.start == 0 ==> result.plan().log().len() == 0
        && result.plan().revocations().len() == 0 && result.plan().selection().len() == 0)
}

pub open spec fn home_block(before: Disk, v: write_io::Images, block: u32) -> bool {
    before.dom().contains(block) && block != 0
        && !(v.tx.layout.start <= block < v.tx.layout.start as int + v.tx.layout.journal_blocks)
}

pub(crate) proof fn snapshot_state(m: Machine, before: Disk, v: write_io::Images, layout: &JournalLayout)
    requires write_recognition::context(before, v), write_device::inv(m, v.tx.payloads.len()),
        layout.wf(), layout.view() == v.tx.layout,
    ensures source(m, before, v, layout).start == 0 ==>
            m.stable.contains(9 + 2 * v.tx.payloads.len()) || !m.stable.contains(2),
        source(m, before, v, layout).start != 0 ==> source(m, before, v, layout) == write_recognition::source(m, before, v),
{
    write_recognition::ordinary_context_implies_transport_context(before, v);
    snapshot_state_transport(m, before, v, layout)
}

pub(crate) proof fn snapshot_state_transport(m: Machine, before: Disk, v: write_io::Images, layout: &JournalLayout)
    requires write_recognition::transport_context(before, v), write_device::inv(m, v.tx.payloads.len()),
        layout.wf(), layout.view() == v.tx.layout,
    ensures source(m, before, v, layout).start == 0 ==>
            m.stable.contains(9 + 2 * v.tx.payloads.len()) || !m.stable.contains(2),
        source(m, before, v, layout).start != 0 ==> source(m, before, v, layout) == write_recognition::source(m, before, v),
{
    hide(crc::fold);
    reveal(write_io::transport_images);
    let media = write_media::disk(m, before, v);
    let journal = journal_view::snapshot(media, v.tx.layout);
    write_media::apply_preserves_initialized_journal_mapping_transport(before, v, m.stable, write_device::total(v.tx.payloads.len()));
    write_media::journal_superblock_is_one_of_the_ordered_state_images_transport(m, before, v);
    journal_view::snapshot_block_is_the_physical_image(media, v.tx.layout, 0);
    journal_view::snapshot_block_is_the_physical_image(before, v.tx.layout, 0);
    if !m.stable.contains(9 + 2 * v.tx.payloads.len()) && m.stable.contains(2) {
        write_recognition::an_active_journal_snapshot_has_the_prepared_sequence_uuid_and_checksum_transport(m, before, v);
    }
}

pub proof fn original_targets_exist(before: Disk, v: write_io::Images)
    requires write_recognition::context(before, v),
    ensures replay_refinement::all_targets_exist(before, transaction_refinement::log(v.tx)),
{
    write_recognition::ordinary_context_implies_transport_context(before, v);
    original_targets_exist_transport(before, v)
}

pub proof fn original_targets_exist_transport(before: Disk, v: write_io::Images)
    requires write_recognition::transport_context(before, v),
    ensures replay_refinement::all_targets_exist(before, transaction_refinement::log(v.tx)),
{
    hide(crc::fold);
    reveal(write_io::transport_images);
    assert forall|i: int| 0 <= i < v.tx.original.len() implies
        #[trigger] before.dom().contains(v.tx.original[i].block) by {
        let k = 8 + v.tx.payloads.len() + i as nat;
        assert(write_device::is_write(k, v.tx.payloads.len()));
        assert(write_media::address(v, k) == v.tx.original[i].block);
    }
}

proof fn unrelated_home_blocks_are_framed(m: Machine, before: Disk, v: write_io::Images, block: u32)
    requires write_recognition::context(before, v), home_block(before, v, block),
        forall|i: int| 0 <= i < v.tx.original.len() ==> (#[trigger] v.tx.original[i]).block != block,
    ensures write_media::disk(m, before, v)[block] == before[block],
{
    write_recognition::ordinary_context_implies_transport_context(before, v);
    unrelated_home_blocks_are_framed_transport(m, before, v, block)
}

proof fn unrelated_home_blocks_are_framed_transport(m: Machine, before: Disk, v: write_io::Images, block: u32)
    requires write_recognition::transport_context(before, v), home_block(before, v, block),
        forall|i: int| 0 <= i < v.tx.original.len() ==> (#[trigger] v.tx.original[i]).block != block,
    ensures write_media::disk(m, before, v)[block] == before[block],
{
    hide(crc::fold);
    reveal(write_io::transport_images);
    let count = v.tx.payloads.len();
    assert forall|k: nat| k < write_device::total(count) && write_device::is_write(k, count) && m.stable.contains(k)
        implies #[trigger] write_media::address(v, k) != block by {
        if 8 + count <= k < 8 + 2 * count {
            let i = (k - (8 + count)) as int;
            assert(v.tx.original[i].block != block);
        }
    }
    write_media::apply_frames_every_unwritten_block(before, v, m.stable, write_device::total(count), block);
}

pub proof fn every_returned_writer_scan_is_empty_or_the_complete_transaction(m: Machine, before: Disk, v: write_io::Images,
    layout: &JournalLayout, result: &scan::Scan)
    requires write_recognition::context(before, v), write_device::inv(m, v.tx.payloads.len()),
        layout.wf(), layout.view() == v.tx.layout, returned(result, source(m, before, v, layout)),
    ensures result.plan().refines(), result.plan().revocations().len() == 0,
        source(m, before, v, layout).start == 0 ==> result.plan().selection().len() == 0,
        !m.stable.contains(6 + v.tx.payloads.len()) ==> result.plan().log().len() == 0 && result.plan().selection().len() == 0,
        source(m, before, v, layout).start != 0 && m.stable.contains(6 + v.tx.payloads.len()) ==>
            result.plan().log() == transaction_refinement::log(v.tx),
        replay_refinement::all_targets_exist(write_media::disk(m, before, v), result.plan().log()),
{
    write_recognition::ordinary_context_implies_transport_context(before, v);
    every_returned_writer_scan_is_empty_or_the_complete_transaction_transport(m, before, v, layout, result)
}

pub proof fn every_returned_writer_scan_is_empty_or_the_complete_transaction_transport(m: Machine, before: Disk, v: write_io::Images,
    layout: &JournalLayout, result: &scan::Scan)
    requires write_recognition::transport_context(before, v), write_device::inv(m, v.tx.payloads.len()),
        layout.wf(), layout.view() == v.tx.layout, returned(result, source(m, before, v, layout)),
    ensures result.plan().refines(), result.plan().revocations().len() == 0,
        source(m, before, v, layout).start == 0 ==> result.plan().selection().len() == 0,
        !m.stable.contains(6 + v.tx.payloads.len()) ==> result.plan().log().len() == 0 && result.plan().selection().len() == 0,
        source(m, before, v, layout).start != 0 && m.stable.contains(6 + v.tx.payloads.len()) ==>
            result.plan().log() == transaction_refinement::log(v.tx),
        replay_refinement::all_targets_exist(write_media::disk(m, before, v), result.plan().log()),
{
    hide(crc::fold);
    reveal(write_io::transport_images);
    snapshot_state_transport(m, before, v, layout);
    original_targets_exist_transport(before, v);
    write_media::apply_preserves_domain(before, v, m.stable, write_device::total(v.tx.payloads.len()));
    if source(m, before, v, layout).start != 0 {
        if m.stable.contains(6 + v.tx.payloads.len()) {
            write_recognition::a_persisted_commit_has_the_complete_encoded_log_transport(m, before, v);
            transaction_refinement::successful_scan_of_encoded_transaction_recovers_every_original(v.tx,
                write_recognition::source(m, before, v), result);
        } else {
            write_recognition::recovery_without_a_persisted_commit_cannot_publish_a_transaction_transport(m, before, v, result);
        }
    }
}

proof fn no_last_image_means_no_original_target(before: Disk, v: write_io::Images, block: u32)
    requires write_recognition::context(before, v),
        replay_refinement::last_eligible(transaction_refinement::log(v.tx), Seq::empty(), block) is None,
    ensures forall|i: int| 0 <= i < v.tx.original.len() ==> (#[trigger] v.tx.original[i]).block != block,
{
    write_recognition::ordinary_context_implies_transport_context(before, v);
    no_last_image_means_no_original_target_transport(before, v, block)
}

proof fn no_last_image_means_no_original_target_transport(before: Disk, v: write_io::Images, block: u32)
    requires write_recognition::transport_context(before, v),
        replay_refinement::last_eligible(transaction_refinement::log(v.tx), Seq::empty(), block) is None,
    ensures forall|i: int| 0 <= i < v.tx.original.len() ==> (#[trigger] v.tx.original[i]).block != block,
{
    let log = transaction_refinement::log(v.tx);
    replay_refinement::last_eligible_characterizes_latest(log, Seq::empty(), block);
    assert forall|i: int| 0 <= i < v.tx.original.len() implies (#[trigger] v.tx.original[i]).block != block by {
        assert(log[i].block == v.tx.original[i].block);
        if log[i].block == block { assert(replay::blocked(block, log[i].sequence, Seq::empty())); }
    }
}

pub proof fn complete_redo_overrides_any_partial_writer_homes(m: Machine, before: Disk, v: write_io::Images, block: u32)
    requires write_recognition::context(before, v), home_block(before, v, block),
    ensures replay_refinement::chronological(write_media::disk(m, before, v), transaction_refinement::log(v.tx), Seq::empty())[block]
        == replay_refinement::chronological(before, transaction_refinement::log(v.tx), Seq::empty())[block],
{
    write_recognition::ordinary_context_implies_transport_context(before, v);
    complete_redo_overrides_any_partial_writer_homes_transport(m, before, v, block)
}

pub proof fn complete_redo_overrides_any_partial_writer_homes_transport(m: Machine, before: Disk, v: write_io::Images, block: u32)
    requires write_recognition::transport_context(before, v), home_block(before, v, block),
    ensures replay_refinement::chronological(write_media::disk(m, before, v), transaction_refinement::log(v.tx), Seq::empty())[block]
        == replay_refinement::chronological(before, transaction_refinement::log(v.tx), Seq::empty())[block],
{
    hide(crc::fold);
    hide(replay_refinement::chronological);
    hide(replay_refinement::last_eligible);
    let media = write_media::disk(m, before, v);
    let log = transaction_refinement::log(v.tx);
    original_targets_exist_transport(before, v);
    write_media::apply_preserves_domain(before, v, m.stable, write_device::total(v.tx.payloads.len()));
    replay_refinement::chronological_lookup(before, log, Seq::empty(), block);
    replay_refinement::chronological_lookup(media, log, Seq::empty(), block);
    if replay_refinement::last_eligible(log, Seq::empty(), block) is None {
        no_last_image_means_no_original_target_transport(before, v, block);
        unrelated_home_blocks_are_framed_transport(m, before, v, block);
    }
}

pub proof fn a_retired_writer_has_complete_home_after_bytes(m: Machine, before: Disk, v: write_io::Images, block: u32)
    requires write_recognition::context(before, v), write_device::inv(m, v.tx.payloads.len()),
        m.stable.contains(9 + 2 * v.tx.payloads.len()), home_block(before, v, block),
    ensures write_media::disk(m, before, v)[block]
        == replay_refinement::chronological(before, transaction_refinement::log(v.tx), Seq::empty())[block],
{
    write_recognition::ordinary_context_implies_transport_context(before, v);
    a_retired_writer_has_complete_home_after_bytes_transport(m, before, v, block)
}

pub proof fn a_retired_writer_has_complete_home_after_bytes_transport(m: Machine, before: Disk, v: write_io::Images, block: u32)
    requires write_recognition::transport_context(before, v), write_device::inv(m, v.tx.payloads.len()),
        m.stable.contains(9 + 2 * v.tx.payloads.len()), home_block(before, v, block),
    ensures write_media::disk(m, before, v)[block]
        == replay_refinement::chronological(before, transaction_refinement::log(v.tx), Seq::empty())[block],
{
    hide(crc::fold);
    hide(replay_refinement::chronological);
    hide(replay_refinement::last_eligible);
    reveal(write_io::transport_images);
    let log = transaction_refinement::log(v.tx);
    original_targets_exist_transport(before, v);
    write_recognition::clearing_the_journal_tail_requires_durable_home_afterimages_transport(m, before, v);
    replay_refinement::chronological_lookup(before, log, Seq::empty(), block);
    replay_refinement::last_eligible_characterizes_latest(log, Seq::empty(), block);
    if let Some(i) = replay_refinement::last_eligible(log, Seq::empty(), block) {
        assert(log[i as int].block == block);
    } else {
        no_last_image_means_no_original_target_transport(before, v, block);
        unrelated_home_blocks_are_framed_transport(m, before, v, block);
    }
}

pub proof fn replaying_every_writer_cut_gives_a_complete_before_or_after_home_image(m: Machine, before: Disk,
    v: write_io::Images, layout: &JournalLayout, result: &scan::Scan, block: u32)
    requires write_recognition::context(before, v), write_device::inv(m, v.tx.payloads.len()),
        layout.wf(), layout.view() == v.tx.layout, returned(result, source(m, before, v, layout)),
        home_block(before, v, block),
    ensures replay_refinement::selected(write_media::disk(m, before, v), result.plan().log(), result.plan().selection())[block]
        == if m.stable.contains(6 + v.tx.payloads.len()) {
            replay_refinement::chronological(before, transaction_refinement::log(v.tx), Seq::empty())[block]
        } else { before[block] },
{
    write_recognition::ordinary_context_implies_transport_context(before, v);
    replaying_every_writer_cut_gives_a_complete_before_or_after_home_image_transport(m, before, v, layout, result, block)
}

pub proof fn replaying_every_writer_cut_gives_a_complete_before_or_after_home_image_transport(m: Machine, before: Disk,
    v: write_io::Images, layout: &JournalLayout, result: &scan::Scan, block: u32)
    requires write_recognition::transport_context(before, v), write_device::inv(m, v.tx.payloads.len()),
        layout.wf(), layout.view() == v.tx.layout, returned(result, source(m, before, v, layout)),
        home_block(before, v, block),
    ensures replay_refinement::selected(write_media::disk(m, before, v), result.plan().log(), result.plan().selection())[block]
        == if m.stable.contains(6 + v.tx.payloads.len()) {
            replay_refinement::chronological(before, transaction_refinement::log(v.tx), Seq::empty())[block]
        } else { before[block] },
{
    hide(crc::fold);
    hide(crate::transaction::wf);
    hide(returned);
    hide(replay_refinement::chronological);
    hide(replay_refinement::selected);
    hide(write_media::apply);
    reveal(write_io::transport_images);
    let media = write_media::disk(m, before, v);
    let log = transaction_refinement::log(v.tx);
    let count = v.tx.payloads.len();
    snapshot_state_transport(m, before, v, layout);
    write_media::apply_preserves_domain(before, v, m.stable, write_device::total(count));
    every_returned_writer_scan_is_empty_or_the_complete_transaction_transport(m, before, v, layout, result);
    replay_refinement::executable_selection_equals_chronological_redo(media, result.plan());
    if !m.stable.contains(6 + count) {
        assert(replay_refinement::selected(media, result.plan().log(), result.plan().selection()) == media) by {
            reveal(replay_refinement::selected);
        }
        write_recognition::before_a_durable_commit_the_home_image_is_unchanged_except_recovery_marking_transport(m, before, v, block);
    } else {
        if source(m, before, v, layout).start != 0 {
            assert(result.plan().log() == log);
            assert(result.plan().revocations() =~= Seq::<replay::Revocation>::empty());
            complete_redo_overrides_any_partial_writer_homes_transport(m, before, v, block);
        } else {
            assert(replay_refinement::selected(media, result.plan().log(), result.plan().selection()) == media) by {
                reveal(replay_refinement::selected);
            }
            assert(m.stable.contains(9 + 2 * count)) by {
                assert(m.issued.contains(6 + count));
                assert(6 + count <= crate::write_protocol::completed_count(m.io, count));
                assert(m.stable.contains(2));
            }
            a_retired_writer_has_complete_home_after_bytes_transport(m, before, v, block);
        }
    }
}

pub proof fn successful_recovery_of_every_writer_cut_has_before_or_after_home_bytes(m: Machine, before: Disk,
    v: write_io::Images, layout: &JournalLayout, result: &scan::Scan, recovery: recovery_device::Machine,
    tail: Seq<u8>, block: u32)
    requires write_recognition::context(before, v), write_device::inv(m, v.tx.payloads.len()),
        layout.wf(), layout.view() == v.tx.layout, returned(result, source(m, before, v, layout)),
        home_block(before, v, block),
        recovery_device::inv(recovery, write_media::disk(m, before, v), result.plan(), v.journal_block, tail),
        recovery.io.phase == 4, !recovery.io.faulted, !recovery.io.pending,
    ensures recovery.stable[block] == if m.stable.contains(6 + v.tx.payloads.len()) {
        replay_refinement::chronological(before, transaction_refinement::log(v.tx), Seq::empty())[block]
    } else { before[block] },
{
    write_recognition::ordinary_context_implies_transport_context(before, v);
    successful_recovery_of_every_writer_cut_has_before_or_after_home_bytes_transport(m, before, v, layout, result, recovery, tail, block)
}

pub proof fn successful_recovery_of_every_writer_cut_has_before_or_after_home_bytes_transport(m: Machine, before: Disk,
    v: write_io::Images, layout: &JournalLayout, result: &scan::Scan, recovery: recovery_device::Machine,
    tail: Seq<u8>, block: u32)
    requires write_recognition::transport_context(before, v), write_device::inv(m, v.tx.payloads.len()),
        layout.wf(), layout.view() == v.tx.layout, returned(result, source(m, before, v, layout)),
        home_block(before, v, block),
        recovery_device::inv(recovery, write_media::disk(m, before, v), result.plan(), v.journal_block, tail),
        recovery.io.phase == 4, !recovery.io.faulted, !recovery.io.pending,
    ensures recovery.stable[block] == if m.stable.contains(6 + v.tx.payloads.len()) {
        replay_refinement::chronological(before, transaction_refinement::log(v.tx), Seq::empty())[block]
    } else { before[block] },
{
    replaying_every_writer_cut_gives_a_complete_before_or_after_home_image_transport(m, before, v, layout, result, block);
    recovery_device::success_image_equals_linux_redo(recovery, write_media::disk(m, before, v), result.plan(), v.journal_block, tail);
    replay_refinement::executable_selection_equals_chronological_redo(write_media::disk(m, before, v), result.plan());
    reveal(write_io::transport_images);
    assert(block != v.journal_block);
}

}
