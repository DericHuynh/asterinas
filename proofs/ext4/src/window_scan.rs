// SPDX-License-Identifier: MPL-2.0

//! Physical reserved-window bytes refine the actual scanner's input source.

use vstd::prelude::*;
use crate::{crc, journal_view, journal_window::{self as window, Operation, WindowView},
    journal_window_device as device, journal_window_media::{self as media, Media}, replay_refinement::Disk,
    ring, scan, scan_trace::Source, window_provenance::{self as provenance, context}, window_snapshot, window_stream::{self as stream}};

verus! {

pub open spec fn source(m: Media, initial: Disk, v: WindowView, first: nat) -> Source {
    Source { journal: journal_view::snapshot(media::disk(m, initial, v), v.layout), blocks: v.layout.journal_blocks,
        start: stream::boundary(v, first) as u32, first: (v.first as nat + first) as u32,
        uuid: v.uuid, seed: crc::fold(0xffffffff, v.uuid), layout: v.layout }
}

proof fn a_nonwrapping_logical_position_identifies_its_ordinal(start: u32, blocks: u32, ordinal: u32, logical: u32)
    requires 1 <= start <= logical < blocks, ordinal < blocks - 1, ring::position(1, blocks, start, ordinal) == logical as nat,
    ensures start as nat + ordinal == logical,
{ }

pub proof fn every_physical_window_cut_has_a_shaped_scanner_source(m: Media, initial: Disk, v: WindowView, first: nat)
    requires context(initial, v), media::inv(m, v), first < v.txs.len(),
    ensures stream::shaped(v, source(m, initial, v, first), first),
{
    hide(crc::fold);
    window_snapshot::every_window_crash_keeps_the_initialized_journal_mapping(m, initial, v);
    stream::reserved_boundaries_match_the_exact_payload_prefixes(v, first);
    window::window_entry(v, first as int);
    let s = source(m, initial, v, first);
    assert(stream::fields(v, s, first));
    assert forall|ordinal: u32, candidate: u32| ordinal < s.blocks - 1 && s.first <= candidate
        && #[trigger] crate::jbd2::header_ok(scan::block_at(s.journal, s.blocks, s.start, ordinal), candidate)
        implies exists|t: nat| stream::metadata(v, s, first, ordinal, candidate, t) by {
        let logical = ring::position(1, s.blocks, s.start, ordinal) as u32;
        ring::reservations_never_include_the_superblock(1, s.blocks, s.start, ordinal);
        journal_view::scanned_block_is_the_reserved_ring_image(media::disk(m, initial, v), v.layout, s.start, ordinal);
        provenance::a_fresh_metadata_header_is_an_issued_descriptor_or_commit(m, initial, v, logical, candidate);
        let op = choose|op: Operation| m.ledger.stable.contains(op) && (op is Descriptor || op is Commit)
            && device::legal(op, window::counts(v)) && media::address(v, op) as nat == v.layout.start as nat + logical
            && media::disk(m, initial, v)[(v.layout.start + logical) as u32] == media::image(v, op)
            && v.txs[media::log_index(op)].tx.sequence == candidate;
        let t = media::log_index(op) as nat;
        window::window_entry(v, t as int);
        assert(first <= t < v.txs.len());
        stream::reserved_boundaries_match_the_exact_payload_prefixes(v, t);
        stream::offset_bounds(v, first, t);
        media::log_location(v, op);
        assert(s.start <= logical);
        a_nonwrapping_logical_position_identifies_its_ordinal(s.start, s.blocks, ordinal, logical);
        assert(stream::metadata(v, s, first, ordinal, candidate, t));
    }
    assert(stream::shaped(v, s, first)) by { reveal(stream::shaped); }
}

pub proof fn a_reserved_record_is_the_exact_scanned_physical_block(m: Media, initial: Disk, v: WindowView, first: nat, op: Operation)
    requires context(initial, v), media::inv(m, v), first <= media::log_index(op) < v.txs.len(),
        device::legal(op, window::counts(v)), media::is_log(op),
    ensures scan::block_at(source(m, initial, v, first).journal, v.layout.journal_blocks, source(m, initial, v, first).start,
        (stream::offset(v, first, media::log_index(op) as nat) as nat + media::log_offset(v, op)) as u32)
        == media::disk(m, initial, v)[media::address(v, op)],
{
    hide(crc::fold);
    window_snapshot::every_window_crash_keeps_the_initialized_journal_mapping(m, initial, v);
    let t = media::log_index(op) as nat;
    stream::offset_bounds(v, first, t);
    stream::reserved_boundaries_match_the_exact_payload_prefixes(v, t);
    stream::reserved_boundaries_match_the_exact_payload_prefixes(v, first);
    media::log_location(v, op);
    let s = source(m, initial, v, first);
    let ordinal = (stream::offset(v, first, t) as nat + media::log_offset(v, op)) as u32;
    assert(ordinal as nat == stream::offset(v, first, t) as nat + media::log_offset(v, op));
    assert(ordinal < s.blocks - 1);
    journal_view::scanned_block_is_the_reserved_ring_image(media::disk(m, initial, v), v.layout, s.start, ordinal);
    assert(s.start as nat + ordinal < s.blocks);
    assert((v.layout.start as nat + ring::position(1, s.blocks, s.start, ordinal)) as u32 == media::address(v, op));
}

pub proof fn a_durable_transaction_has_its_complete_encoded_scanner_images(m: Media, initial: Disk, v: WindowView, first: nat, t: usize)
    requires context(initial, v), media::inv(m, v), first <= t < provenance::durable(m, v),
    ensures scan::block_at(source(m, initial, v, first).journal, v.layout.journal_blocks, source(m, initial, v, first).start,
            stream::offset(v, first, t as nat)) == v.txs[t as int].tx.descriptor,
        scan::block_at(source(m, initial, v, first).journal, v.layout.journal_blocks, source(m, initial, v, first).start,
            (stream::offset(v, first, t as nat) as nat + window::counts(v)[t as int] + 1) as u32) == v.txs[t as int].tx.commit,
        forall|k: usize| k < window::counts(v)[t as int] ==> #[trigger]
            scan::block_at(source(m, initial, v, first).journal, v.layout.journal_blocks, source(m, initial, v, first).start,
                (stream::offset(v, first, t as nat) as nat + 1 + k) as u32) == v.txs[t as int].tx.payloads[k as int],
{
    provenance::stable_commit_records_are_exactly_a_contiguous_prefix(m, v);
    assert(m.ledger.stable.contains(Operation::Commit(t)));
    device::commit_issue_requires_the_complete_log_stable(m.ledger, window::counts(v), t);
    a_reserved_record_is_the_exact_scanned_physical_block(m, initial, v, first, Operation::Descriptor(t));
    media::a_stable_log_record_has_exact_bytes(m, initial, v, Operation::Descriptor(t));
    a_reserved_record_is_the_exact_scanned_physical_block(m, initial, v, first, Operation::Commit(t));
    media::a_stable_log_record_has_exact_bytes(m, initial, v, Operation::Commit(t));
    assert forall|k: usize| k < window::counts(v)[t as int] implies #[trigger]
        scan::block_at(source(m, initial, v, first).journal, v.layout.journal_blocks, source(m, initial, v, first).start,
            (stream::offset(v, first, t as nat) as nat + 1 + k) as u32) == v.txs[t as int].tx.payloads[k as int] by {
        a_reserved_record_is_the_exact_scanned_physical_block(m, initial, v, first, Operation::Payload(t, k));
        media::a_stable_log_record_has_exact_bytes(m, initial, v, Operation::Payload(t, k));
    }
}

}
