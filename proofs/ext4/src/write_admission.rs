// SPDX-License-Identifier: MPL-2.0

//! Recovery admission follows the shape of every possible writer snapshot,
//! including snapshots with only some payloads persisted. Header provenance,
//! rather than a checksum identity premise, bounds the recognized stream.

use vstd::prelude::*;
use crate::{bytes, crc, descriptor, freshness, jbd2, journal_superblock, journal_view,
    layout::JournalLayout, recovery_profile, replay_refinement::Disk, revoke, ring, scan, scan_budget, super_state,
    scan_trace::{self, Record, Source}, transaction::{self, TransactionView},
    transaction_refinement, write_device::{self, Machine}, write_io, write_media, write_recognition};

verus! {

#[verifier::opaque]
pub open spec fn shaped(tx: TransactionView, source: Source) -> bool {
    &&& transaction::wf(tx) && transaction_refinement::source_fields(tx, source)
    &&& source.journal.len() == source.blocks as nat * 4096
    &&& (forall|ordinal: u32, sequence: u32| ordinal < source.blocks - 1 && tx.sequence <= sequence
        && #[trigger] jbd2::header_ok(scan::block_at(source.journal, source.blocks, 1, ordinal), sequence) ==>
        sequence == tx.sequence
        && (ordinal == 0 && scan::block_at(source.journal, source.blocks, 1, ordinal) == tx.descriptor
            || ordinal as nat == tx.payloads.len() + 1
                && scan::block_at(source.journal, source.blocks, 1, ordinal) == tx.commit))
}

proof fn record_header(record: Record, source: Source)
    requires scan_trace::record_ok(record, source),
    ensures record.start < record.end <= source.blocks - 1,
        jbd2::header_ok(scan::block_at(source.journal, source.blocks, source.start, record.start), record.sequence),
        bytes::be32(scan::block_at(source.journal, source.blocks, source.start, record.start), 4) == record.kind,
        record.kind == 2 ==> record.end == record.start + 1 && record.writes.len() == 0 && record.revocations.len() == 0,
{
    reveal(scan_trace::record_ok);
}

proof fn first_record(tx: TransactionView, source: Source, record: Record)
    requires shaped(tx, source), scan_trace::record_ok(record, source), record.start == 0, record.sequence == tx.sequence,
    ensures record.kind == 1, record.writes.len() == tx.payloads.len(), record.revocations.len() == 0,
        record.end as nat == tx.payloads.len() + 1,
{
    reveal(shaped);
    record_header(record, source);
    reveal(scan_trace::record_ok);
    descriptor::descriptor_length_is_unique(tx.descriptor, record.writes.len(), tx.tags.len(), tx.layout.fs_blocks);
}

proof fn prefix_shape(tx: TransactionView, source: Source, records: Seq<Record>)
    requires shaped(tx, source), scan_trace::well_formed(records, source),
    ensures records.len() <= 2,
        records.len() > 0 ==> records[0].kind == 1 && records[0].writes.len() == tx.payloads.len() && records[0].revocations.len() == 0,
        records.len() == 2 ==> records[1].kind == 2 && records[1].writes.len() == 0 && records[1].revocations.len() == 0,
        scan_trace::end(records) as nat == if records.len() == 0 { 0nat } else { tx.payloads.len() + records.len() },
        scan_trace::next_sequence(records, source.first) == tx.sequence as nat + if records.len() == 2 { 1nat } else { 0nat },
{
    hide(crc::fold);
    hide(transaction::wf);
    reveal(shaped);
    assert(0 < tx.payloads.len() <= 250 && 0 < tx.sequence < 4294967295
        && bytes::be32(tx.commit, 4) == 2) by { reveal(transaction::wf); }
    reveal(scan_trace::well_formed);
    if records.len() > 0 {
        first_record(tx, source, records[0]);
        if records.len() > 1 {
            record_header(records[1], source);
            assert(records[1].sequence == tx.sequence);
            assert(records[1].start as nat == tx.payloads.len() + 1);
            assert(records[1].kind == 2);
            assert(records[1].end as nat == tx.payloads.len() + 2);
            if records.len() > 2 {
                record_header(records[2], source);
                assert(records[2].sequence as nat == tx.sequence as nat + 1);
                assert(false);
            }
            assert(records[1].writes.len() == 0 && records[1].revocations.len() == 0);
        }
    }
}

proof fn short_trace_entry_count(records: Seq<Record>)
    requires records.len() <= 2,
    ensures scan_budget::entries(records) ==
        (if records.len() > 0 { records[0].writes.len() + records[0].revocations.len() } else { 0nat })
        + (if records.len() == 2 { records[1].writes.len() + records[1].revocations.len() } else { 0nat }),
{
    reveal_with_fuel(scan_trace::writes, 3);
    reveal_with_fuel(scan_trace::revocations, 3);
}

pub proof fn a_shaped_journal_has_only_small_recognized_prefixes(tx: TransactionView, source: Source, records: Seq<Record>)
    requires shaped(tx, source), scan_trace::well_formed(records, source),
    ensures records.len() <= 2, scan_budget::entries(records) == if records.len() == 0 { 0nat } else { tx.payloads.len() },
        records.len() > 0 ==> records[0].kind == 1,
        records.len() == 2 ==> records[1].kind == 2,
        scan_trace::end(records) as nat == if records.len() == 0 { 0nat } else { tx.payloads.len() + records.len() },
        scan_trace::next_sequence(records, source.first) == tx.sequence as nat + if records.len() == 2 { 1nat } else { 0nat },
{
    prefix_shape(tx, source, records);
    short_trace_entry_count(records);
}

pub proof fn a_shaped_writer_journal_fits_scan_limits(tx: TransactionView, source: Source)
    requires shaped(tx, source),
    ensures scan_budget::within_limits(source),
{
    hide(crc::fold);
    reveal(shaped);
    reveal(scan_budget::within_limits);
    assert forall|records: Seq<Record>| #[trigger] scan_trace::well_formed(records, source) implies {
        let end = scan_trace::end(records);
        let sequence = scan_trace::next_sequence(records, source.first);
        let raw = scan::block_at(source.journal, source.blocks, source.start, end);
        &&& scan_budget::entries(records) <= 4096
        &&& (end == source.blocks - 1 ==> sequence == 4294967295)
        &&& (end < source.blocks - 1 && sequence < 4294967295 ==> {
            &&& (forall|count: nat| descriptor::base(raw, source.uuid, sequence as u32, source.seed)
                && #[trigger] descriptor::candidate(raw, count, source.layout.fs_blocks) ==>
                end as nat + 1 + count <= source.blocks - 1 && scan_budget::entries(records) + count <= 4096)
            &&& (revoke::header(raw, sequence as u32, source.seed)
                && revoke::targets_bounded(raw, revoke::count(raw), source.layout.fs_blocks) ==>
                scan_budget::entries(records) + revoke::count(raw) <= 4096
                && (forall|i: int| 0 <= i < revoke::count(raw) ==> #[trigger]
                    scan_budget::target_allowed(source.layout, bytes::be32(raw, 16 + 4 * i) as u32)))
        })
    } by {
        a_shaped_journal_has_only_small_recognized_prefixes(tx, source, records);
        let end = scan_trace::end(records);
        let sequence = scan_trace::next_sequence(records, source.first);
        let raw = scan::block_at(source.journal, source.blocks, 1, end);
        assert(end < source.blocks - 1);
        assert forall|count: nat| descriptor::base(raw, source.uuid, sequence as u32, source.seed)
            && #[trigger] descriptor::candidate(raw, count, source.layout.fs_blocks) implies
            end as nat + 1 + count <= source.blocks - 1 && scan_budget::entries(records) + count <= 4096 by {
            assert(jbd2::header_ok(raw, sequence as u32));
            assert(sequence == tx.sequence && raw == tx.descriptor && end == 0);
            descriptor::descriptor_length_is_unique(raw, count, tx.tags.len(), source.layout.fs_blocks);
            assert(records.len() == 0);
        }
        if revoke::header(raw, sequence as u32, source.seed) {
            assert(jbd2::header_ok(raw, sequence as u32));
            assert(false);
        }
    }
}

pub proof fn every_fresh_header_is_an_issued_metadata_image(m: Machine, before: Disk, v: write_io::Images,
    logical: u32, candidate: u32)
    requires write_recognition::context(before, v), 1 <= logical < v.tx.layout.journal_blocks,
        v.tx.sequence <= candidate,
        jbd2::header_ok(write_media::disk(m, before, v)[(v.tx.layout.start + logical) as u32], candidate),
    ensures candidate == v.tx.sequence,
        logical == 1 && write_media::disk(m, before, v)[(v.tx.layout.start + logical) as u32] == v.tx.descriptor
        || logical as nat == v.tx.payloads.len() + 2
            && write_media::disk(m, before, v)[(v.tx.layout.start + logical) as u32] == v.tx.commit,
{
    hide(crc::fold);
    reveal(write_io::valid_images);
    let count = v.tx.payloads.len();
    freshness::an_old_journal_block_cannot_have_a_current_or_later_header(before, v.tx.layout,
        bytes::be32(v.initial_journal, 24) as u32, v.tx.sequence, logical, candidate);
    if logical == 1 {
        write_media::journal_record_bytes_follow_the_issued_snapshot(m, before, v, 4);
    } else if 2 <= logical < count + 2 {
        let index = logical as int - 2;
        write_media::journal_record_bytes_follow_the_issued_snapshot(m, before, v, 5 + index as nat);
        freshness::an_encoded_payload_cannot_be_a_metadata_header(v.tx, index, candidate);
    } else if logical as nat == count + 2 {
        write_media::journal_record_bytes_follow_the_issued_snapshot(m, before, v, 6 + count);
    } else {
        write_media::untouched_journal_blocks_retain_their_initial_bytes(m, before, v, logical);
    }
}

pub proof fn every_writer_media_has_a_shaped_active_stream(m: Machine, before: Disk, v: write_io::Images)
    requires write_recognition::context(before, v),
    ensures shaped(v.tx, write_recognition::source(m, before, v)),
{
    hide(crc::fold);
    reveal(write_io::valid_images);
    let source = write_recognition::source(m, before, v);
    let media = write_media::disk(m, before, v);
    write_media::apply_preserves_initialized_journal_mapping(before, v, m.stable, write_device::total(v.tx.payloads.len()));
    assert forall|ordinal: u32, sequence: u32| ordinal < source.blocks - 1 && v.tx.sequence <= sequence
        && #[trigger] jbd2::header_ok(scan::block_at(source.journal, source.blocks, 1, ordinal), sequence) implies
        sequence == v.tx.sequence
        && (ordinal == 0 && scan::block_at(source.journal, source.blocks, 1, ordinal) == v.tx.descriptor
            || ordinal as nat == v.tx.payloads.len() + 1
                && scan::block_at(source.journal, source.blocks, 1, ordinal) == v.tx.commit) by {
        journal_view::scanned_block_is_the_reserved_ring_image(media, v.tx.layout, 1, ordinal);
        assert(ring::position(1, source.blocks, 1, ordinal) == ordinal as nat + 1);
        every_fresh_header_is_an_issued_metadata_image(m, before, v, (ordinal + 1) as u32, sequence);
    }
    reveal(shaped);
}

pub proof fn every_writer_crash_snapshot_is_admitted(m: Machine, before: Disk, v: write_io::Images, layout: &JournalLayout)
    requires write_recognition::context(before, v), layout.wf(), layout.view() == v.tx.layout,
    ensures scan_budget::admitted(journal_view::snapshot(write_media::disk(m, before, v), v.tx.layout), v.tx.uuid, layout),
{
    hide(crc::fold);
    reveal(write_io::valid_images);
    let media = write_media::disk(m, before, v);
    let journal = journal_view::snapshot(media, v.tx.layout);
    write_media::apply_preserves_initialized_journal_mapping(before, v, m.stable, write_device::total(v.tx.payloads.len()));
    write_media::journal_superblock_is_one_of_the_ordered_state_images(m, before, v);
    journal_view::snapshot_block_is_the_physical_image(media, v.tx.layout, 0);
    if m.stable.contains(9 + 2 * v.tx.payloads.len()) {
        assert(journal.subrange(0, 1024) =~= v.tail.subrange(0, 1024));
    } else if m.stable.contains(2) {
        assert(journal.subrange(0, 1024) =~= v.activation.subrange(0, 1024));
        every_writer_media_has_a_shaped_active_stream(m, before, v);
        a_shaped_writer_journal_fits_scan_limits(v.tx, write_recognition::source(m, before, v));
        assert(scan_budget::source(journal, v.tx.uuid, layout) == write_recognition::source(m, before, v));
    } else {
        journal_view::snapshot_block_is_the_physical_image(before, v.tx.layout, 0);
        assert(journal.subrange(0, 1024) =~= v.initial_journal.subrange(0, 1024));
    }
    reveal(scan_budget::admitted);
}

pub proof fn every_committed_writer_stream_satisfies_the_superblock_replay_policy(m: Machine, before: Disk, v: write_io::Images)
    requires write_recognition::context(before, v), write_device::inv(m, v.tx.payloads.len()), m.stable.contains(2),
    ensures recovery_profile::safe_committed_streams(write_recognition::source(m, before, v),
        write_media::disk(m, before, v)[0], v.partition_bytes),
{
    hide(crc::fold);
    hide(transaction::wf);
    reveal(write_io::valid_images);
    let media = write_media::disk(m, before, v);
    let source = write_recognition::source(m, before, v);
    every_writer_media_has_a_shaped_active_stream(m, before, v);
    write_recognition::every_writer_primary_image_retains_the_validated_volume_identity(m, before, v);
    write_media::apply_preserves_initialized_journal_mapping(before, v, m.stable, write_device::total(v.tx.payloads.len()));
    reveal(recovery_profile::safe_committed_streams);
    assert forall|records: Seq<Record>| #[trigger] scan_trace::well_formed(records, source)
        && (records.len() == 0 || records.last().kind == 2) implies
        (forall|i: int| 0 <= i < scan_trace::writes(records).len()
            && (#[trigger] scan_trace::writes(records)[i]).block == 0 ==>
                super_state::replay_ok(media[0], scan_trace::writes(records)[i].image, v.partition_bytes)) by {
        a_shaped_journal_has_only_small_recognized_prefixes(v.tx, source, records);
        if records.len() == 0 {
            assert(records =~= Seq::<Record>::empty());
            scan_trace::empty_records(source);
        } else {
            assert(records.len() == 2);
            assert(scan_trace::record_ok(records[1], source)) by { reveal(scan_trace::well_formed); }
            record_header(records[1], source);
            let ordinal = records[1].start;
            assert(records[1].sequence == v.tx.sequence) by {
                reveal(scan_trace::well_formed);
                assert(records[0].kind == 1);
            }
            journal_view::scanned_block_is_the_reserved_ring_image(media, v.tx.layout, 1, ordinal);
            assert(ring::position(1, source.blocks, 1, ordinal) == ordinal as nat + 1);
            assert(freshness::commit_header(media[(v.tx.layout.start + ordinal + 1) as u32], v.tx.sequence));
            write_recognition::every_fresh_commit_header_is_the_persisted_commit_record(m, before, v, (ordinal + 1) as u32);
            write_recognition::a_persisted_commit_has_the_complete_encoded_log(m, before, v);
            transaction_refinement::encoded_transaction_has_a_complete_committed_certificate(v.tx, source);
            assert(records =~= transaction_refinement::records(v.tx)) by {
                assert forall|i: int| 0 <= i < records.len() implies
                    #[trigger] records[i] == transaction_refinement::records(v.tx)[i] by {
                    scan_trace::well_formed_prefixes_agree_at_every_common_position(records,
                        transaction_refinement::records(v.tx), source, i as nat);
                }
            }
            assert forall|i: int| 0 <= i < scan_trace::writes(records).len()
                && (#[trigger] scan_trace::writes(records)[i]).block == 0 implies
                super_state::replay_ok(media[0], scan_trace::writes(records)[i].image, v.partition_bytes) by {
                assert(super_state::replay_ok(v.dirty, v.tx.original[i].image, v.partition_bytes)) by {
                    reveal(transaction::wf);
                    assert(v.tx.tags[i].block == 0);
                }
                super_state::replay_policy_is_stable_under_another_valid_replay(v.dirty, media[0], v.tx.original[i].image, v.partition_bytes);
            }
        }
    }
}

pub proof fn every_writer_crash_snapshot_can_prepare_recovery(m: Machine, before: Disk, v: write_io::Images, layout: &JournalLayout)
    requires write_recognition::context(before, v), write_device::inv(m, v.tx.payloads.len()),
        layout.wf(), layout.view() == v.tx.layout,
    ensures recovery_profile::input_ok(journal_view::snapshot(write_media::disk(m, before, v), v.tx.layout),
        v.tx.uuid, layout, write_media::disk(m, before, v)[0], v.partition_bytes),
{
    hide(crc::fold);
    reveal(write_io::valid_images);
    let media = write_media::disk(m, before, v);
    let journal = journal_view::snapshot(media, v.tx.layout);
    every_writer_crash_snapshot_is_admitted(m, before, v, layout);
    write_recognition::every_writer_primary_image_retains_the_validated_volume_identity(m, before, v);
    write_media::apply_preserves_initialized_journal_mapping(before, v, m.stable, write_device::total(v.tx.payloads.len()));
    write_media::journal_superblock_is_one_of_the_ordered_state_images(m, before, v);
    journal_view::snapshot_block_is_the_physical_image(media, v.tx.layout, 0);
    if bytes::be32(journal, 28) != 0 {
        journal_view::snapshot_block_is_the_physical_image(before, v.tx.layout, 0);
        assert(m.stable.contains(2) && !m.stable.contains(9 + 2 * v.tx.payloads.len()));
        write_recognition::an_active_journal_snapshot_has_the_prepared_sequence_uuid_and_checksum(m, before, v);
        assert(scan_budget::source(journal, v.tx.uuid, layout) == write_recognition::source(m, before, v));
        every_committed_writer_stream_satisfies_the_superblock_replay_policy(m, before, v);
    }
    reveal(recovery_profile::input_ok);
}

}
