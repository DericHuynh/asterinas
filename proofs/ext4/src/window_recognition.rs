// SPDX-License-Identifier: MPL-2.0

//! The actual maximal JBD2 scan returns exactly the complete durable suffix
//! after the physically visible tail. Uncommitted descriptor suffixes do not
//! acquire authority merely by satisfying a checksum predicate.

use vstd::prelude::*;
use crate::{bytes, crc, jbd2, journal_view, journal_window::{self as window, Operation, WindowView},
    journal_window_media::{self as media, Media}, layout::JournalLayout, replay, replay_refinement::Disk,
    ring, scan, scan_budget, scan_stop, scan_trace::{self, Record}, window_provenance::{self as provenance, *},
    window_records as records, window_scan as physical, window_snapshot as snapshot, window_stream as stream, write_recovery};

verus! {

pub open spec fn actual_source(m: Media, initial: Disk, v: WindowView, layout: &JournalLayout) -> scan_trace::Source {
    scan_budget::source(journal_view::snapshot(media::disk(m, initial, v), v.layout), v.uuid, layout)
}

pub proof fn an_active_actual_source_is_the_physical_reserved_suffix(m: Media, initial: Disk, v: WindowView, layout: &JournalLayout, first: nat)
    requires context(initial, v), media::inv(m, v), layout.wf(), layout.view() == v.layout,
        snapshot::head(m, v) == Some(first), first < v.txs.len(),
    ensures actual_source(m, initial, v, layout) == physical::source(m, initial, v, first), first <= provenance::durable(m, v),
{
    hide(crc::fold);
    snapshot::every_actual_journal_header_retains_its_validated_identity(m, initial, v);
    snapshot::every_actual_header_is_initial_or_an_ordered_prefix_image(m, initial, v);
    stream::reserved_boundaries_match_the_exact_payload_prefixes(v, first);
    window::window_entry(v, first as int);
}

pub proof fn every_window_crash_snapshot_is_admitted_by_scan(m: Media, initial: Disk, v: WindowView, layout: &JournalLayout)
    requires context(initial, v), media::inv(m, v), layout.wf(), layout.view() == v.layout,
    ensures scan_budget::admitted(journal_view::snapshot(media::disk(m, initial, v), v.layout), v.uuid, layout),
{
    hide(crc::fold);
    snapshot::every_actual_journal_header_retains_its_validated_identity(m, initial, v);
    let journal = journal_view::snapshot(media::disk(m, initial, v), v.layout);
    match snapshot::head(m, v) {
        Some(first) => {
            snapshot::every_actual_header_is_initial_or_an_ordered_prefix_image(m, initial, v);
            if first < v.txs.len() {
                an_active_actual_source_is_the_physical_reserved_suffix(m, initial, v, layout, first);
                physical::every_physical_window_cut_has_a_shaped_scanner_source(m, initial, v, first);
                stream::every_shaped_window_is_admitted_by_the_actual_scanner(v, physical::source(m, initial, v, first), first);
                assert(scan_budget::within_limits(actual_source(m, initial, v, layout)));
                window::window_entry(v, first as int); reveal(window::positioned_valid);
                assert(v.first as nat + first < 4294967295);
                assert(bytes::be32(journal, 24) < 4294967295);
            }
        },
        None => {},
    }
    assert(scan_budget::admitted(journal_view::snapshot(media::disk(m, initial, v), v.layout), v.uuid, layout)) by { reveal(scan_budget::admitted); }
}

proof fn a_recognized_commit_must_belong_to_the_durable_prefix(m: Media, initial: Disk, v: WindowView, first: nat, ordinal: u32, sequence: u32)
    requires context(initial, v), media::inv(m, v), first < v.txs.len(), ordinal < v.layout.journal_blocks - 1,
        physical::source(m, initial, v, first).first <= sequence,
        jbd2::commit_ok(scan::block_at(physical::source(m, initial, v, first).journal, v.layout.journal_blocks,
            physical::source(m, initial, v, first).start, ordinal), sequence, physical::source(m, initial, v, first).seed),
    ensures (sequence as nat) < v.first as nat + provenance::durable(m, v),
{
    hide(crc::fold);
    let s = physical::source(m, initial, v, first);
    stream::reserved_boundaries_match_the_exact_payload_prefixes(v, first);
    window::window_entry(v, first as int);
    snapshot::every_window_crash_keeps_the_initialized_journal_mapping(m, initial, v);
    journal_view::scanned_block_is_the_reserved_ring_image(media::disk(m, initial, v), v.layout, s.start, ordinal);
    ring::reservations_never_include_the_superblock(1, s.blocks, s.start, ordinal);
    let logical = ring::position(1, s.blocks, s.start, ordinal) as u32;
    provenance::a_fresh_metadata_header_is_an_issued_descriptor_or_commit(m, initial, v, logical, sequence);
    let op = choose|op: Operation| m.ledger.stable.contains(op) && (op is Descriptor || op is Commit)
        && crate::journal_window_device::legal(op, window::counts(v)) && media::address(v, op) as nat == v.layout.start as nat + logical
        && media::disk(m, initial, v)[(v.layout.start + logical) as u32] == media::image(v, op)
        && v.txs[media::log_index(op)].tx.sequence == sequence;
    let t = media::log_index(op) as nat;
    stream::metadata_fields(v, t);
    assert(op is Commit);
    provenance::stable_commit_records_are_exactly_a_contiguous_prefix(m, v);
}

pub proof fn every_committed_recognized_stream_stops_within_the_durable_prefix(m: Media, initial: Disk, v: WindowView, first: nat, rs: Seq<Record>)
    requires context(initial, v), media::inv(m, v), first < v.txs.len(), first <= provenance::durable(m, v),
        scan_trace::well_formed(rs, physical::source(m, initial, v, first)), rs.len() == 0 || rs.last().kind == 2,
    ensures rs.len() % 2 == 0, first + rs.len() / 2 <= provenance::durable(m, v),
{
    hide(crc::fold);
    let s = physical::source(m, initial, v, first);
    physical::every_physical_window_cut_has_a_shaped_scanner_source(m, initial, v, first);
    stream::every_recognized_prefix_has_the_reserved_transaction_shape(v, s, first, rs);
    reveal(scan_trace::well_formed);
    if rs.len() > 0 {
        assert(stream::record_shape(v, first, rs.len() as int - 1, rs.last()));
        stream::record_facts(v, first, rs.len() as int - 1, rs.last());
        assert(scan_trace::record_ok(rs.last(), s));
        stream::record_header(rs.last(), s);
        assert(rs.len() % 2 == 0) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(rs.len() as int - 1, 2);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(rs.len() as int, 2);
        }
        reveal(scan_trace::record_ok);
        a_recognized_commit_must_belong_to_the_durable_prefix(m, initial, v, first, rs.last().start, rs.last().sequence);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(rs.len() as int - 1, 2);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(rs.len() as int, 2);
    }
}

pub proof fn every_durable_suffix_has_a_complete_canonical_certificate(m: Media, initial: Disk, v: WindowView, first: nat, end: nat)
    requires context(initial, v), media::inv(m, v), first < v.txs.len(), first <= end <= provenance::durable(m, v),
    ensures scan_trace::committed_prefix(records::records(v, first, end), physical::source(m, initial, v, first), records::log(v, first, end), Seq::empty()),
        records::records(v, first, end).len() == 2 * (end - first),
        scan_trace::next_sequence(records::records(v, first, end), physical::source(m, initial, v, first).first) == v.first as nat + end,
{
    physical::every_physical_window_cut_has_a_shaped_scanner_source(m, initial, v, first);
    provenance::stable_commit_records_are_exactly_a_contiguous_prefix(m, v);
    let s = physical::source(m, initial, v, first);
    assert(stream::fields(v, s, first)) by { reveal(stream::shaped); }
    assert forall|t: nat| first <= t < end implies #[trigger] records::transaction_present(v, s, first, t) by {
        physical::a_durable_transaction_has_its_complete_encoded_scanner_images(m, initial, v, first, t as usize);
        assert forall|i: int| 0 <= i < window::counts(v)[t as int] implies #[trigger]
            scan::block_at(s.journal, s.blocks, s.start, (stream::offset(v, first, t) as nat + 1 + i) as u32) == v.txs[t as int].tx.payloads[i] by {
            assert(i == i as usize);
        }
    }
    records::complete_encoded_transactions_form_a_committed_scan_prefix(v, s, first, end);
}

pub proof fn every_committed_stream_contains_exact_original_afterimages(m: Media, initial: Disk, v: WindowView, first: nat, rs: Seq<Record>)
    requires context(initial, v), media::inv(m, v), first < v.txs.len(), first <= provenance::durable(m, v),
        scan_trace::well_formed(rs, physical::source(m, initial, v, first)), rs.len() == 0 || rs.last().kind == 2,
    ensures rs == records::records(v, first, first + rs.len() / 2),
        scan_trace::writes(rs) == records::log(v, first, first + rs.len() / 2), scan_trace::revocations(rs).len() == 0,
{
    hide(crc::fold);
    every_committed_recognized_stream_stops_within_the_durable_prefix(m, initial, v, first, rs);
    let end = first + rs.len() / 2;
    every_durable_suffix_has_a_complete_canonical_certificate(m, initial, v, first, end);
    let canonical = records::records(v, first, end);
    let s = physical::source(m, initial, v, first);
    assert(canonical.len() == rs.len()) by { vstd::arithmetic::div_mod::lemma_fundamental_div_mod(rs.len() as int, 2); }
    assert(rs =~= canonical) by {
        assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == canonical[i] by {
            scan_trace::well_formed_prefixes_agree_at_every_common_position(rs, canonical, s, i as nat);
        }
    }
}

pub proof fn the_actual_maximal_scan_returns_exactly_the_unretired_durable_suffix(m: Media, initial: Disk, v: WindowView,
    layout: &JournalLayout, result: &scan::Scan, first: nat)
    requires context(initial, v), media::inv(m, v), layout.wf(), layout.view() == v.layout,
        snapshot::head(m, v) == Some(first), first < v.txs.len(),
        write_recovery::returned(result, actual_source(m, initial, v, layout)),
    ensures result.plan().log() == records::log(v, first, provenance::durable(m, v)), result.plan().revocations().len() == 0,
        result.next() as nat == v.first as nat + provenance::durable(m, v),
        result.committed() as nat + first == provenance::durable(m, v),
{
    hide(crc::fold);
    an_active_actual_source_is_the_physical_reserved_suffix(m, initial, v, layout, first);
    let s = physical::source(m, initial, v, first);
    every_committed_stream_contains_exact_original_afterimages(m, initial, v, first, result.records());
    every_durable_suffix_has_a_complete_canonical_certificate(m, initial, v, first, provenance::durable(m, v));
    let canonical = records::records(v, first, provenance::durable(m, v));
    stream::reserved_boundaries_match_the_exact_payload_prefixes(v, first);
    if result.termination() is Clean { reveal(scan_stop::at_boundary); assert(s.start == 0); }
    scan_stop::every_recognized_prefix_is_a_prefix_of_a_stopped_stream(canonical, result.scanned(), result.termination(), s, result.next());
    if result.records().len() < canonical.len() {
        let i = canonical.len() as int - 1;
        assert(canonical[i].kind == 2);
        assert(result.scanned()[i] == canonical[i]);
        assert(result.scanned()[i].kind != 2);
    }
    every_committed_recognized_stream_stops_within_the_durable_prefix(m, initial, v, first, result.records());
    assert(result.records().len() == canonical.len());
}

}
