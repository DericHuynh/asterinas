// SPDX-License-Identifier: MPL-2.0

//! Exact complete-prefix recovery at every concurrent-window crash cut.
//! Block zero is included relative to the physically persisted recovery mark;
//! driver reset/quiescence, mount admission and operation authority are separate.

use vstd::prelude::*;
use crate::{bytes, crc, journal_view, journal_window::WindowView, journal_window_media::{self as media, Media},
    layout::JournalLayout, recovery_device, replay_refinement::{self as redo, Disk}, scan,
    window_provenance::{self as provenance, context}, window_recognition as recognition, window_records as records,
    window_redo as checkpoint, window_snapshot as snapshot, write_recovery};

verus! {

pub open spec fn retired(m: Media, v: WindowView) -> nat { match snapshot::head(m, v) { Some(k) => k, None => 0nat } }
pub open spec fn suffix(m: Media, v: WindowView) -> Seq<crate::replay::WriteView> { records::log(v, retired(m, v), provenance::durable(m, v)) }
pub open spec fn recovered_prefix(m: Media, initial: Disk, v: WindowView) -> Disk {
    redo::chronological(checkpoint::baseline(m, initial, v), records::log(v, 0, provenance::durable(m, v)), Seq::empty())
}

pub proof fn every_returned_actual_scan_has_exactly_the_durable_replay_suffix(m: Media, initial: Disk, v: WindowView,
    layout: &JournalLayout, result: &scan::Scan)
    requires context(initial, v), media::inv(m, v), layout.wf(), layout.view() == v.layout,
        write_recovery::returned(result, recognition::actual_source(m, initial, v, layout)),
    ensures result.plan().log() == suffix(m, v), result.plan().revocations().len() == 0,
        m.ledger.io.commit <= provenance::durable(m, v) <= v.txs.len(), retired(m, v) <= provenance::durable(m, v),
        redo::all_targets_exist(media::disk(m, initial, v), result.plan().log()),
{
    hide(crc::fold);
    snapshot::every_actual_header_is_initial_or_an_ordered_prefix_image(m, initial, v);
    snapshot::every_actual_journal_header_retains_its_validated_identity(m, initial, v);
    let journal = journal_view::snapshot(media::disk(m, initial, v), v.layout);
    match snapshot::head(m, v) {
        Some(first) => {
            if first < v.txs.len() { recognition::the_actual_maximal_scan_returns_exactly_the_unretired_durable_suffix(m, initial, v, layout, result, first); }
            else {
                assert(first == v.txs.len() && provenance::durable(m, v) == first);
                assert(bytes::be32(journal, 28) == 0);
                assert(suffix(m, v) =~= Seq::empty());
            }
        },
        None => {
            assert(provenance::durable(m, v) == 0);
            assert(bytes::be32(journal, 28) == 0);
            assert(suffix(m, v) =~= Seq::empty());
        },
    }
    checkpoint::every_window_log_target_exists_in_the_initial_device(initial, v, retired(m, v), provenance::durable(m, v));
    media::every_media_cut_preserves_the_device_domain(m, initial, v);
}

pub proof fn scanning_and_replaying_every_window_cut_gives_the_exact_complete_durable_prefix(m: Media, initial: Disk, v: WindowView,
    layout: &JournalLayout, result: &scan::Scan, block: u32)
    requires context(initial, v), media::inv(m, v), layout.wf(), layout.view() == v.layout,
        write_recovery::returned(result, recognition::actual_source(m, initial, v, layout)), checkpoint::home_block(initial, v, block),
    ensures redo::selected(media::disk(m, initial, v), result.plan().log(), result.plan().selection())[block] == recovered_prefix(m, initial, v)[block],
{
    hide(crc::fold);
    every_returned_actual_scan_has_exactly_the_durable_replay_suffix(m, initial, v, layout, result);
    snapshot::every_actual_header_is_initial_or_an_ordered_prefix_image(m, initial, v);
    let q = retired(m, v);
    assert forall|t: usize, k: usize| t < q && k < crate::journal_window::counts(v)[t as int]
        implies #[trigger] m.ledger.stable.contains(crate::journal_window::Operation::Home(t, k)) by {
        match snapshot::head(m, v) { Some(first) => { assert(first == q); }, None => { assert(q == 0); } }
    }
    checkpoint::redo_of_the_unretired_suffix_covers_every_partial_home_checkpoint(m, initial, v, q, block);
    redo::executable_selection_equals_chronological_redo(media::disk(m, initial, v), result.plan());
    assert(result.plan().revocations() =~= Seq::empty());
}

pub proof fn successful_actual_recovery_from_every_window_cut_has_exact_prefix_bytes(m: Media, initial: Disk, v: WindowView,
    layout: &JournalLayout, result: &scan::Scan, recovery: recovery_device::Machine, tail: Seq<u8>, block: u32)
    requires context(initial, v), media::inv(m, v), layout.wf(), layout.view() == v.layout,
        write_recovery::returned(result, recognition::actual_source(m, initial, v, layout)), checkpoint::home_block(initial, v, block),
        recovery_device::inv(recovery, media::disk(m, initial, v), result.plan(), v.layout.start, tail),
        recovery.io.phase == 4, !recovery.io.pending, !recovery.io.faulted,
    ensures recovery.stable[block] == recovered_prefix(m, initial, v)[block],
{
    scanning_and_replaying_every_window_cut_gives_the_exact_complete_durable_prefix(m, initial, v, layout, result, block);
    recovery_device::success_image_equals_linux_redo(recovery, media::disk(m, initial, v), result.plan(), v.layout.start, tail);
    redo::executable_selection_equals_chronological_redo(media::disk(m, initial, v), result.plan());
    assert(block != v.layout.start);
}

pub proof fn every_finite_lane_and_cache_interleaving_recovers_a_complete_acknowledged_prefix(states: Seq<Media>, events: Seq<crate::journal_window_device::Event>,
    initial: Disk, v: WindowView, layout: &JournalLayout, cut: nat, result: &scan::Scan, block: u32)
    requires context(initial, v), layout.wf(), layout.view() == v.layout, states[0] == media::initial(), media::execution(states, events, v), cut < states.len(),
        write_recovery::returned(result, recognition::actual_source(states[cut as int], initial, v, layout)), checkpoint::home_block(initial, v, block),
    ensures states[cut as int].ledger.io.commit <= provenance::durable(states[cut as int], v),
        redo::selected(media::disk(states[cut as int], initial, v), result.plan().log(), result.plan().selection())[block]
            == recovered_prefix(states[cut as int], initial, v)[block],
{
    media::initialization(v);
    media::every_finite_byte_persistence_interleaving_preserves_order(states, events, v);
    provenance::stable_commit_records_are_exactly_a_contiguous_prefix(states[cut as int], v);
    scanning_and_replaying_every_window_cut_gives_the_exact_complete_durable_prefix(states[cut as int], initial, v, layout, result, block);
}

}
