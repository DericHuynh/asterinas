// SPDX-License-Identifier: MPL-2.0

//! Fresh commit recognition is derived from atomic issued bytes and fences.
//! This links the writer ledger and physical media to canonical JBD2 recovery.

use vstd::prelude::*;
use crate::{bytes, epoch, freshness, jbd2, journal_superblock, journal_view, replay_refinement::Disk, ring, scan, super_state, superblock,
    scan_trace::Source, transaction, transaction_refinement, write_device::{self, Machine}, write_io, write_media};

verus! {

pub open spec fn context(before: Disk, v: write_io::Images) -> bool {
    &&& write_io::valid_images(v) && write_media::targets_exist(before, v)
    &&& journal_view::mapped(before, v.tx.layout)
    &&& journal_view::snapshot(before, v.tx.layout) == v.initial_journal
    &&& before.dom().contains(0) && before[0] == v.initial_primary
}

pub open spec fn transport_context(before: Disk, v: write_io::Images) -> bool {
    &&& write_io::transport_images(v) && write_media::targets_exist(before, v)
    &&& journal_view::mapped(before, v.tx.layout)
    &&& journal_view::snapshot(before, v.tx.layout) == v.initial_journal
    &&& before.dom().contains(0) && before[0] == v.initial_primary
}

pub proof fn ordinary_context_implies_transport_context(before: Disk, v: write_io::Images)
    requires context(before, v),
    ensures transport_context(before, v),
{
    write_io::valid_images_implies_transport_images(v);
}


pub open spec fn source(m: Machine, before: Disk, v: write_io::Images) -> Source {
    Source { journal: journal_view::snapshot(write_media::disk(m, before, v), v.tx.layout),
        blocks: v.tx.layout.journal_blocks, start: 1, first: v.tx.sequence, uuid: v.tx.uuid, seed: v.tx.seed, layout: v.tx.layout }
}

proof fn initial_epoch(before: Disk, v: write_io::Images)
    requires context(before, v),
    ensures transaction::wf(v.tx), v.journal_block == v.tx.layout.start,
        epoch::newer(journal_view::snapshot(before, v.tx.layout), bytes::be32(v.initial_journal, 24) as u32, v.tx.sequence),
{
    ordinary_context_implies_transport_context(before, v);
    initial_epoch_transport(before, v)
}

proof fn initial_epoch_transport(before: Disk, v: write_io::Images)
    requires transport_context(before, v),
    ensures transaction::wf(v.tx), v.journal_block == v.tx.layout.start,
        epoch::newer(journal_view::snapshot(before, v.tx.layout), bytes::be32(v.initial_journal, 24) as u32, v.tx.sequence),
{
    reveal(write_io::transport_images);
}

pub proof fn every_fresh_commit_header_is_the_persisted_commit_record(m: Machine, before: Disk, v: write_io::Images, logical: u32)
    requires context(before, v), 1 <= logical < v.tx.layout.journal_blocks,
        freshness::commit_header(write_media::disk(m, before, v)[(v.tx.layout.start + logical) as u32], v.tx.sequence),
    ensures logical as nat == v.tx.payloads.len() + 2, m.stable.contains(6 + v.tx.payloads.len()),
{
    ordinary_context_implies_transport_context(before, v);
    every_fresh_commit_header_is_the_persisted_commit_record_transport(m, before, v, logical)
}

pub proof fn every_fresh_commit_header_is_the_persisted_commit_record_transport(m: Machine, before: Disk, v: write_io::Images, logical: u32)
    requires transport_context(before, v), 1 <= logical < v.tx.layout.journal_blocks,
        freshness::commit_header(write_media::disk(m, before, v)[(v.tx.layout.start + logical) as u32], v.tx.sequence),
    ensures logical as nat == v.tx.payloads.len() + 2, m.stable.contains(6 + v.tx.payloads.len()),
{
    initial_epoch_transport(before, v);
    let count = v.tx.payloads.len();
    let block = (v.tx.layout.start + logical) as u32;
    freshness::an_old_journal_block_cannot_have_a_current_or_later_header(before, v.tx.layout,
        bytes::be32(v.initial_journal, 24) as u32, v.tx.sequence, logical, v.tx.sequence);
    if logical == 1 {
        write_media::journal_record_bytes_follow_the_issued_snapshot_transport(m, before, v, 4);
    } else if 2 <= logical < count + 2 {
        let index = logical as int - 2;
        write_media::journal_record_bytes_follow_the_issued_snapshot_transport(m, before, v, 5 + index as nat);
        freshness::an_encoded_payload_cannot_be_a_metadata_header(v.tx, index, v.tx.sequence);
    } else if logical as nat == count + 2 {
        write_media::journal_record_bytes_follow_the_issued_snapshot_transport(m, before, v, 6 + count);
    } else {
        assert(before.dom().contains(block));
        write_media::untouched_journal_blocks_retain_their_initial_bytes_transport(m, before, v, logical);
    }
}

#[verifier::rlimit(30)]
pub proof fn a_persisted_commit_has_the_complete_encoded_log(m: Machine, before: Disk, v: write_io::Images)
    requires context(before, v), write_device::inv(m, v.tx.payloads.len()), m.stable.contains(6 + v.tx.payloads.len()),
    ensures transaction_refinement::committed_records_present(v.tx, source(m, before, v)),
{
    ordinary_context_implies_transport_context(before, v);
    a_persisted_commit_has_the_complete_encoded_log_transport(m, before, v)
}

#[verifier::rlimit(30)]
pub proof fn a_persisted_commit_has_the_complete_encoded_log_transport(m: Machine, before: Disk, v: write_io::Images)
    requires transport_context(before, v), write_device::inv(m, v.tx.payloads.len()), m.stable.contains(6 + v.tx.payloads.len()),
    ensures transaction_refinement::committed_records_present(v.tx, source(m, before, v)),
{
    initial_epoch_transport(before, v);
    let count = v.tx.payloads.len();
    let media = write_media::disk(m, before, v);
    write_media::apply_preserves_initialized_journal_mapping_transport(before, v, m.stable, write_device::total(count));
    assert(m.issued.contains(6 + count));
    write_device::commit_issue_requires_every_log_image_stable(m, count);
    write_media::journal_record_bytes_follow_the_issued_snapshot_transport(m, before, v, 4);
    journal_view::scanned_block_is_the_reserved_ring_image(media, v.tx.layout, 1, 0);
    write_media::journal_record_bytes_follow_the_issued_snapshot_transport(m, before, v, 6 + count);
    journal_view::scanned_block_is_the_reserved_ring_image(media, v.tx.layout, 1, (count + 1) as u32);
    assert forall|i: int| 0 <= i < count implies
        #[trigger] scan::block_at(source(m, before, v).journal, v.tx.layout.journal_blocks, 1, (i + 1) as u32) == v.tx.payloads[i] by {
        assert(m.stable.contains(5 + i as nat));
        write_media::journal_record_bytes_follow_the_issued_snapshot_transport(m, before, v, 5 + i as nat);
        journal_view::scanned_block_is_the_reserved_ring_image(media, v.tx.layout, 1, (i + 1) as u32);
    }
    let next = (count + 3) as u32;
    assert(before.dom().contains((v.journal_block + next) as u32));
    write_media::untouched_journal_blocks_retain_their_initial_bytes_transport(m, before, v, next);
    journal_view::scanned_block_is_the_reserved_ring_image(media, v.tx.layout, 1, (count + 2) as u32);
    freshness::an_old_journal_block_cannot_have_a_current_or_later_header(before, v.tx.layout,
        bytes::be32(v.initial_journal, 24) as u32, v.tx.sequence, next, (v.tx.sequence + 1) as u32);
}

pub proof fn recognizing_a_fresh_commit_replays_every_encoded_original(m: Machine, before: Disk,
    v: write_io::Images, logical: u32, result: &scan::Scan)
    requires context(before, v), write_device::inv(m, v.tx.payloads.len()),
        1 <= logical < v.tx.layout.journal_blocks,
        freshness::commit_header(write_media::disk(m, before, v)[(v.tx.layout.start + logical) as u32], v.tx.sequence),
        result.certificate(source(m, before, v)), result.maximal(source(m, before, v)),
    ensures result.plan().log() == transaction_refinement::log(v.tx), result.plan().revocations().len() == 0,
        result.next() as nat == v.tx.sequence as nat + 1,
{
    ordinary_context_implies_transport_context(before, v);
    recognizing_a_fresh_commit_replays_every_encoded_original_transport(m, before, v, logical, result)
}

pub proof fn recognizing_a_fresh_commit_replays_every_encoded_original_transport(m: Machine, before: Disk,
    v: write_io::Images, logical: u32, result: &scan::Scan)
    requires transport_context(before, v), write_device::inv(m, v.tx.payloads.len()),
        1 <= logical < v.tx.layout.journal_blocks,
        freshness::commit_header(write_media::disk(m, before, v)[(v.tx.layout.start + logical) as u32], v.tx.sequence),
        result.certificate(source(m, before, v)), result.maximal(source(m, before, v)),
    ensures result.plan().log() == transaction_refinement::log(v.tx), result.plan().revocations().len() == 0,
        result.next() as nat == v.tx.sequence as nat + 1,
{
    every_fresh_commit_header_is_the_persisted_commit_record_transport(m, before, v, logical);
    a_persisted_commit_has_the_complete_encoded_log_transport(m, before, v);
    initial_epoch_transport(before, v);
    transaction_refinement::successful_scan_of_encoded_transaction_recovers_every_original(v.tx, source(m, before, v), result);
}

pub proof fn clearing_the_journal_tail_requires_durable_home_afterimages(m: Machine, before: Disk, v: write_io::Images)
    requires context(before, v), write_device::inv(m, v.tx.payloads.len()), m.stable.contains(9 + 2 * v.tx.payloads.len()),
    ensures write_media::disk(m, before, v)[v.journal_block] == v.tail,
        forall|i: int| 0 <= i < v.tx.original.len() ==> #[trigger]
            write_media::disk(m, before, v)[v.tx.original[i].block] == v.tx.original[i].image,
{
    ordinary_context_implies_transport_context(before, v);
    clearing_the_journal_tail_requires_durable_home_afterimages_transport(m, before, v)
}

pub proof fn clearing_the_journal_tail_requires_durable_home_afterimages_transport(m: Machine, before: Disk, v: write_io::Images)
    requires transport_context(before, v), write_device::inv(m, v.tx.payloads.len()), m.stable.contains(9 + 2 * v.tx.payloads.len()),
    ensures write_media::disk(m, before, v)[v.journal_block] == v.tail,
        forall|i: int| 0 <= i < v.tx.original.len() ==> #[trigger]
            write_media::disk(m, before, v)[v.tx.original[i].block] == v.tx.original[i].image,
{
    initial_epoch_transport(before, v);
    let count = v.tx.payloads.len();
    assert(m.issued.contains(9 + 2 * count));
    write_device::retirement_issue_requires_every_home_image_stable(m, count);
    write_media::journal_superblock_is_one_of_the_ordered_state_images_transport(m, before, v);
    assert forall|i: int| 0 <= i < v.tx.original.len() implies #[trigger]
        write_media::disk(m, before, v)[v.tx.original[i].block] == v.tx.original[i].image by {
        assert(m.stable.contains(8 + count + i as nat));
        write_media::a_stable_home_write_has_its_exact_afterimage_transport(m, before, v, i as nat);
    }
}

pub proof fn successful_writer_completion_has_exact_durable_home_bytes_and_retired_tail(m: Machine, before: Disk, v: write_io::Images)
    requires context(before, v), write_device::inv(m, v.tx.payloads.len()), m.io.phase is Done, !m.io.pending, !m.io.faulted,
    ensures write_media::disk(m, before, v)[v.journal_block] == v.tail,
        forall|i: int| 0 <= i < v.tx.original.len() ==> #[trigger]
            write_media::disk(m, before, v)[v.tx.original[i].block] == v.tx.original[i].image,
        forall|k: nat| !#[trigger] write_device::enabled(m, write_device::Event::Persist(k)),
{
    ordinary_context_implies_transport_context(before, v);
    successful_writer_completion_has_exact_durable_home_bytes_and_retired_tail_transport(m, before, v)
}

pub proof fn successful_writer_completion_has_exact_durable_home_bytes_and_retired_tail_transport(m: Machine, before: Disk, v: write_io::Images)
    requires transport_context(before, v), write_device::inv(m, v.tx.payloads.len()), m.io.phase is Done, !m.io.pending, !m.io.faulted,
    ensures write_media::disk(m, before, v)[v.journal_block] == v.tail,
        forall|i: int| 0 <= i < v.tx.original.len() ==> #[trigger]
            write_media::disk(m, before, v)[v.tx.original[i].block] == v.tx.original[i].image,
        forall|k: nat| !#[trigger] write_device::enabled(m, write_device::Event::Persist(k)),
{
    initial_epoch_transport(before, v);
    write_device::successful_completion_is_durable_and_has_no_late_persistence(m, v.tx.payloads.len());
    assert(m.stable.contains(9 + 2 * v.tx.payloads.len()));
    clearing_the_journal_tail_requires_durable_home_afterimages_transport(m, before, v);
}

pub proof fn before_a_durable_commit_no_checkpoint_image_can_be_stable(m: Machine, count: nat)
    requires write_device::inv(m, count), !m.stable.contains(6 + count),
    ensures forall|i: nat| i < count ==> !#[trigger] m.stable.contains(8 + count + i),
{
    assert forall|i: nat| i < count implies !#[trigger] m.stable.contains(8 + count + i) by {
        if m.stable.contains(8 + count + i) {
            assert(m.issued.contains(8 + count + i));
            write_device::home_issue_requires_a_stable_commit(m, count, i);
        }
    }
}

pub proof fn before_a_durable_commit_the_home_image_is_unchanged_except_recovery_marking(m: Machine, before: Disk,
    v: write_io::Images, block: u32)
    requires context(before, v), write_device::inv(m, v.tx.payloads.len()), !m.stable.contains(6 + v.tx.payloads.len()),
        before.dom().contains(block), block != 0,
        block < v.tx.layout.start || block >= v.tx.layout.start as int + v.tx.layout.journal_blocks,
    ensures write_media::disk(m, before, v)[block] == before[block],
        super_state::preserves(before[0], write_media::disk(m, before, v)[0]),
{
    ordinary_context_implies_transport_context(before, v);
    before_a_durable_commit_the_home_image_is_unchanged_except_recovery_marking_transport(m, before, v, block)
}

pub proof fn before_a_durable_commit_the_home_image_is_unchanged_except_recovery_marking_transport(m: Machine, before: Disk,
    v: write_io::Images, block: u32)
    requires transport_context(before, v), write_device::inv(m, v.tx.payloads.len()), !m.stable.contains(6 + v.tx.payloads.len()),
        before.dom().contains(block), block != 0,
        block < v.tx.layout.start || block >= v.tx.layout.start as int + v.tx.layout.journal_blocks,
    ensures write_media::disk(m, before, v)[block] == before[block],
        super_state::preserves(before[0], write_media::disk(m, before, v)[0]),
{
    initial_epoch_transport(before, v);
    let count = v.tx.payloads.len();
    before_a_durable_commit_no_checkpoint_image_can_be_stable(m, count);
    assert forall|k: nat| k < write_device::total(count) && write_device::is_write(k, count) && m.stable.contains(k)
        implies #[trigger] write_media::address(v, k) != block by {
        if 8 + count <= k < 8 + 2 * count { assert(!m.stable.contains(k)); }
    }
    write_media::apply_frames_every_unwritten_block(before, v, m.stable, write_device::total(count), block);
    write_media::before_checkpoint_block_zero_is_only_the_recovery_flag_image_transport(m, before, v);
    reveal(write_io::transport_images);
    if !m.stable.contains(0) { assert(super_state::preserves(before[0], before[0])); }
}

pub proof fn recovery_without_a_persisted_commit_cannot_publish_a_transaction(m: Machine, before: Disk,
    v: write_io::Images, result: &scan::Scan)
    requires context(before, v), write_device::inv(m, v.tx.payloads.len()), !m.stable.contains(6 + v.tx.payloads.len()),
        result.first() == v.tx.sequence, result.plan().refines(),
        result.recognized(source(m, before, v).journal, v.tx.layout.journal_blocks, 1, v.tx.seed),
    ensures result.committed() == 0, result.plan().log().len() == 0, result.plan().revocations().len() == 0,
        result.plan().selection().len() == 0,
{
    ordinary_context_implies_transport_context(before, v);
    recovery_without_a_persisted_commit_cannot_publish_a_transaction_transport(m, before, v, result)
}

pub proof fn recovery_without_a_persisted_commit_cannot_publish_a_transaction_transport(m: Machine, before: Disk,
    v: write_io::Images, result: &scan::Scan)
    requires transport_context(before, v), write_device::inv(m, v.tx.payloads.len()), !m.stable.contains(6 + v.tx.payloads.len()),
        result.first() == v.tx.sequence, result.plan().refines(),
        result.recognized(source(m, before, v).journal, v.tx.layout.journal_blocks, 1, v.tx.seed),
    ensures result.committed() == 0, result.plan().log().len() == 0, result.plan().revocations().len() == 0,
        result.plan().selection().len() == 0,
{
    initial_epoch_transport(before, v);
    let media = write_media::disk(m, before, v);
    write_media::apply_preserves_initialized_journal_mapping_transport(before, v, m.stable, write_device::total(v.tx.payloads.len()));
    if result.committed() > 0 {
        assert(result.commit_positions().dom().contains(v.tx.sequence));
        let ordinal = result.commit_positions()[v.tx.sequence];
        assert(jbd2::commit_ok(scan::block_at(source(m, before, v).journal, v.tx.layout.journal_blocks, 1, ordinal), v.tx.sequence, v.tx.seed));
        let logical = (ordinal + 1) as u32;
        journal_view::scanned_block_is_the_reserved_ring_image(media, v.tx.layout, 1, ordinal);
        assert(ring::position(1, v.tx.layout.journal_blocks, 1, ordinal) == logical as nat);
        every_fresh_commit_header_is_the_persisted_commit_record_transport(m, before, v, logical);
    }
    if result.plan().log().len() > 0 {
        let id = result.plan().log()[0].sequence;
        assert(result.commit_positions().dom().contains(id));
    }
    if result.plan().revocations().len() > 0 {
        let id = result.plan().revocations()[0].sequence;
        assert(result.commit_positions().dom().contains(id));
    }
}

#[verifier::rlimit(20)]
pub proof fn journal_activation_always_has_a_valid_recovery_marked_superblock(m: Machine, before: Disk, v: write_io::Images)
    requires context(before, v), write_device::inv(m, v.tx.payloads.len()), m.stable.contains(2),
    ensures write_media::disk(m, before, v)[0].len() == 4096,
        super_state::is_dirty(write_media::disk(m, before, v)[0]),
        superblock::accepted(write_media::disk(m, before, v)[0].subrange(1024, 2048), v.partition_bytes),
{
    initial_epoch(before, v);
    let count = v.tx.payloads.len();
    assert(m.issued.contains(2));
    assert(2 <= crate::write_protocol::completed_count(m.io, count));
    assert(m.stable.contains(0));
    if exists|i: int| 0 <= i < count && v.tx.original[i].block == 0 && m.stable.contains(8 + count + i as nat) {
        let i = choose|i: int| 0 <= i < count && v.tx.original[i].block == 0 && m.stable.contains(8 + count + i as nat);
        write_media::a_stable_home_write_has_its_exact_afterimage(m, before, v, i as nat);
        assert(v.tx.tags[i].block == v.tx.original[i].block);
        assert(super_state::replay_ok(v.tx.primary, v.tx.original[i].image, v.tx.partition_bytes));
        reveal(write_io::valid_images);
    } else {
        assert forall|i: nat| i < count && v.tx.original[i as int].block == 0
            implies !#[trigger] m.stable.contains(8 + count + i) by { }
        write_media::without_a_stable_home_target_zero_only_dirty_marking_changes_block_zero(m, before, v);
        reveal(write_io::valid_images);
    }
}

pub proof fn an_active_journal_snapshot_has_the_prepared_sequence_uuid_and_checksum(m: Machine, before: Disk, v: write_io::Images)
    requires context(before, v), write_device::inv(m, v.tx.payloads.len()), m.stable.contains(2),
        !m.stable.contains(9 + 2 * v.tx.payloads.len()),
    ensures journal_superblock::accepted(source(m, before, v).journal.subrange(0, 1024), v.tx.uuid, v.tx.layout.journal_blocks),
        bytes::be32(source(m, before, v).journal, 24) == v.tx.sequence,
        bytes::be32(source(m, before, v).journal, 28) == 1,
{
    ordinary_context_implies_transport_context(before, v);
    an_active_journal_snapshot_has_the_prepared_sequence_uuid_and_checksum_transport(m, before, v)
}

pub proof fn an_active_journal_snapshot_has_the_prepared_sequence_uuid_and_checksum_transport(m: Machine, before: Disk, v: write_io::Images)
    requires transport_context(before, v), write_device::inv(m, v.tx.payloads.len()), m.stable.contains(2),
        !m.stable.contains(9 + 2 * v.tx.payloads.len()),
    ensures journal_superblock::accepted(source(m, before, v).journal.subrange(0, 1024), v.tx.uuid, v.tx.layout.journal_blocks),
        bytes::be32(source(m, before, v).journal, 24) == v.tx.sequence,
        bytes::be32(source(m, before, v).journal, 28) == 1,
{
    initial_epoch_transport(before, v);
    write_media::journal_superblock_is_one_of_the_ordered_state_images_transport(m, before, v);
    let media = write_media::disk(m, before, v);
    write_media::apply_preserves_initialized_journal_mapping_transport(before, v, m.stable, write_device::total(v.tx.payloads.len()));
    journal_view::snapshot_block_is_the_physical_image(media, v.tx.layout, 0);
    assert(source(m, before, v).journal.subrange(0, 4096) == v.activation);
    assert(source(m, before, v).journal.subrange(0, 1024) =~= v.activation.subrange(0, 1024));
    reveal(write_io::transport_images);
}

pub proof fn every_writer_primary_image_retains_the_validated_volume_identity(m: Machine, before: Disk, v: write_io::Images)
    requires context(before, v), write_device::inv(m, v.tx.payloads.len()),
    ensures write_media::disk(m, before, v)[0].len() == 4096,
        superblock::accepted(write_media::disk(m, before, v)[0].subrange(1024, 2048), v.partition_bytes),
        bytes::le32(write_media::disk(m, before, v)[0], 1028) == v.tx.layout.fs_blocks,
        write_media::disk(m, before, v)[0].subrange(1128, 1144) == v.initial_primary.subrange(1128, 1144),
        m.stable.contains(2) ==> super_state::replay_ok(v.dirty, write_media::disk(m, before, v)[0], v.partition_bytes),
{
    hide(crate::crc::fold);
    reveal(write_io::valid_images);
    let count = v.tx.payloads.len();
    let media = write_media::disk(m, before, v);
    super_state::recovery_flag_image_preserves_uuid_and_boot_bytes(v.initial_primary, v.dirty);
    assert(bytes::le32(v.dirty, 1028) == bytes::le32(v.initial_primary, 1028));
    if exists|i: int| 0 <= i < count && v.tx.original[i].block == 0 && m.stable.contains(8 + count + i as nat) {
        let i = choose|i: int| 0 <= i < count && v.tx.original[i].block == 0 && m.stable.contains(8 + count + i as nat);
        write_media::a_stable_home_write_has_its_exact_afterimage(m, before, v, i as nat);
        assert(v.tx.tags[i].block == 0);
        assert(super_state::replay_ok(v.dirty, media[0], v.partition_bytes));
        super_state::replay_preserves_geometry_and_keeps_recovery(v.dirty, media[0], v.partition_bytes);
    } else {
        assert forall|i: nat| i < count && v.tx.original[i as int].block == 0
            implies !#[trigger] m.stable.contains(8 + count + i) by { }
        write_media::without_a_stable_home_target_zero_only_dirty_marking_changes_block_zero(m, before, v);
        if m.stable.contains(2) {
            assert(m.issued.contains(2));
            assert(2 <= crate::write_protocol::completed_count(m.io, count));
            assert(m.stable.contains(0));
            assert(media[0] == v.dirty);
            assert(super_state::replay_ok(v.dirty, v.dirty, v.partition_bytes));
        }
    }
}


/// A successful commit flush reports the exact encoded transaction durable.
/// This uses the explicit ledger flush contract, not ordinary write completion.
pub proof fn acknowledged_commit_has_the_complete_durable_log_transport(m: Machine, before: Disk, v: write_io::Images)
    requires transport_context(before, v), write_device::inv(m, v.tx.payloads.len()),
        crate::write_protocol::completed_count(m.io, v.tx.payloads.len()) > 7 + v.tx.payloads.len(),
    ensures m.stable.contains(6 + v.tx.payloads.len()),
        transaction_refinement::committed_records_present(v.tx, source(m, before, v)),
{
    initial_epoch_transport(before, v);
    let count = v.tx.payloads.len();
    assert(write_device::is_write(6 + count, count));
    assert(write_device::fence_after(6 + count, count) == 7 + count);
    a_persisted_commit_has_the_complete_encoded_log_transport(m, before, v);
}

/// With no primary payload, every physical primary is exactly the retained
/// initial image or its encoded recovery marker. All feature bits are retained.
pub proof fn every_transport_primary_is_initial_or_dirty(m: Machine, before: Disk, v: write_io::Images)
    requires transport_context(before, v), write_device::inv(m, v.tx.payloads.len()),
        forall|i: int| 0 <= i < v.tx.original.len() ==> (#[trigger] v.tx.original[i]).block != 0,
    ensures write_media::disk(m, before, v).dom().contains(0),
        write_media::disk(m, before, v)[0] == if m.stable.contains(0) { v.dirty } else { v.initial_primary },
        write_media::disk(m, before, v)[0].len() == 4096,
        super_state::preserves(v.initial_primary, write_media::disk(m, before, v)[0]),
        m.stable.contains(2) ==> write_media::disk(m, before, v)[0] == v.dirty,
{
    hide(crate::crc::fold);
    reveal(write_io::transport_images);
    let count = v.tx.payloads.len();
    assert forall|i: nat| i < count && v.tx.original[i as int].block == 0
        implies !#[trigger] m.stable.contains(8 + count + i) by { }
    write_media::without_a_stable_home_target_zero_only_dirty_marking_changes_block_zero_transport(m, before, v);
    if !m.stable.contains(0) { assert(super_state::preserves(v.initial_primary, v.initial_primary)); }
    if m.stable.contains(2) {
        assert(m.issued.contains(2));
        assert(2 <= crate::write_protocol::completed_count(m.io, count));
        assert(m.stable.contains(0));
    }
}

}
