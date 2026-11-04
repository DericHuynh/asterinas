// SPDX-License-Identifier: MPL-2.0

//! Recovery preparation is closed over every window crash cut and arbitrary
//! finite subsequent recovery attempts under the same quiescent-start contract.

use vstd::prelude::*;
use crate::{bytes, crc, journal_view, journal_window::{self as window, WindowView}, journal_window_media::{self as media, Media},
    layout::JournalLayout, recovery_closure, recovery_device, recovery_profile, replay_refinement::Disk,
    scan, scan_budget, scan_trace, super_state, window_provenance::{self as provenance, context},
    window_recognition as recognition, window_records as records, window_snapshot as snapshot};

verus! {

proof fn every_logged_primary_image_satisfies_the_original_replay_policy(v: WindowView, first: nat, end: nat)
    requires window::valid(v), first <= end <= v.txs.len(),
    ensures forall|i: int| 0 <= i < records::log(v, first, end).len() && (#[trigger] records::log(v, first, end)[i]).block == 0
        ==> super_state::replay_ok(v.dirty, records::log(v, first, end)[i].image, v.partition_bytes),
{
    hide(crc::fold);
    assert forall|i: int| 0 <= i < records::log(v, first, end).len() && (#[trigger] records::log(v, first, end)[i]).block == 0
        implies super_state::replay_ok(v.dirty, records::log(v, first, end)[i].image, v.partition_bytes) by {
        records::every_log_entry_has_the_exact_original_transaction_source(v, first, end, i);
        let (t, k) = choose|t: nat, k: int| first <= t < end && 0 <= k < window::counts(v)[t as int]
            && records::log(v, first, end)[i] == crate::transaction_refinement::log(v.txs[t as int].tx)[k];
        window::window_entry(v, t as int); reveal(window::positioned_valid);
        assert(v.txs[t as int].tx.tags[k].block == 0);
        assert(super_state::replay_ok(v.dirty, v.txs[t as int].tx.original[k].image, v.partition_bytes));
    }
}

pub proof fn every_committed_window_stream_is_safe_for_the_actual_primary(m: Media, initial: Disk, v: WindowView,
    layout: &JournalLayout, first: nat)
    requires context(initial, v), media::inv(m, v), layout.wf(), layout.view() == v.layout,
        snapshot::head(m, v) == Some(first), first < v.txs.len(),
    ensures recovery_profile::safe_committed_streams(recognition::actual_source(m, initial, v, layout), media::disk(m, initial, v)[0], v.partition_bytes),
{
    hide(crc::fold);
    recognition::an_active_actual_source_is_the_physical_reserved_suffix(m, initial, v, layout, first);
    snapshot::every_primary_image_preserves_identity_and_active_recovery_policy(m, initial, v);
    let source = recognition::actual_source(m, initial, v, layout);
    let primary = media::disk(m, initial, v)[0];
    assert forall|rs: Seq<scan_trace::Record>| #[trigger] scan_trace::well_formed(rs, source)
        && (rs.len() == 0 || rs.last().kind == 2) implies
        (forall|i: int| 0 <= i < scan_trace::writes(rs).len() && (#[trigger] scan_trace::writes(rs)[i]).block == 0
            ==> super_state::replay_ok(primary, scan_trace::writes(rs)[i].image, v.partition_bytes)) by {
        recognition::every_committed_recognized_stream_stops_within_the_durable_prefix(m, initial, v, first, rs);
        recognition::every_committed_stream_contains_exact_original_afterimages(m, initial, v, first, rs);
        provenance::stable_commit_records_are_exactly_a_contiguous_prefix(m, v);
        let end = first + rs.len() / 2;
        every_logged_primary_image_satisfies_the_original_replay_policy(v, first, end);
        assert forall|i: int| 0 <= i < scan_trace::writes(rs).len() && (#[trigger] scan_trace::writes(rs)[i]).block == 0
            implies super_state::replay_ok(primary, scan_trace::writes(rs)[i].image, v.partition_bytes) by {
            super_state::replay_policy_is_stable_under_another_valid_replay(v.dirty, primary, scan_trace::writes(rs)[i].image, v.partition_bytes);
        }
    }
    assert(recovery_profile::safe_committed_streams(source, primary, v.partition_bytes)) by { reveal(recovery_profile::safe_committed_streams); }
}

pub proof fn every_window_crash_snapshot_can_prepare_actual_recovery(m: Media, initial: Disk, v: WindowView, layout: &JournalLayout)
    requires context(initial, v), media::inv(m, v), layout.wf(), layout.view() == v.layout,
    ensures recovery_profile::input_ok(journal_view::snapshot(media::disk(m, initial, v), v.layout), v.uuid, layout,
        media::disk(m, initial, v)[0], v.partition_bytes),
{
    hide(crc::fold);
    recognition::every_window_crash_snapshot_is_admitted_by_scan(m, initial, v, layout);
    snapshot::every_actual_journal_header_retains_its_validated_identity(m, initial, v);
    snapshot::every_primary_image_preserves_identity_and_active_recovery_policy(m, initial, v);
    let journal = journal_view::snapshot(media::disk(m, initial, v), v.layout);
    if bytes::be32(journal, 28) != 0 {
        match snapshot::head(m, v) {
            Some(first) => {
                snapshot::every_actual_header_is_initial_or_an_ordered_prefix_image(m, initial, v);
                assert(first < v.txs.len());
                every_committed_window_stream_is_safe_for_the_actual_primary(m, initial, v, layout, first);
                assert(super_state::is_dirty(media::disk(m, initial, v)[0]));
            },
            None => { assert(false); },
        }
    }
    assert(recovery_profile::input_ok(journal, v.uuid, layout, media::disk(m, initial, v)[0], v.partition_bytes)) by { reveal(recovery_profile::input_ok); }
}

pub proof fn recovery_from_a_window_cut_can_crash_and_be_prepared_again(m: Media, initial: Disk, v: WindowView,
    layout: &JournalLayout, result: &scan::Scan, recovery: recovery_device::Machine, tail: Seq<u8>)
    requires context(initial, v), media::inv(m, v), layout.wf(), layout.view() == v.layout,
        recovery_closure::ready(media::disk(m, initial, v), v.uuid, layout, result, tail),
        recovery_device::inv(recovery, media::disk(m, initial, v), result.plan(), v.layout.start, tail),
    ensures recovery_profile::input_ok(journal_view::snapshot(recovery.stable, v.layout), v.uuid, layout, recovery.stable[0], v.partition_bytes),
{
    every_window_crash_snapshot_can_prepare_actual_recovery(m, initial, v, layout);
    assert(recovery_closure::context(media::disk(m, initial, v), v.uuid, layout, v.partition_bytes, result, tail)) by {
        reveal(recovery_closure::context);
    }
    recovery_closure::every_recovery_crash_snapshot_can_prepare_another_recovery(recovery, media::disk(m, initial, v), v.uuid, layout, v.partition_bytes, result, tail);
}

pub proof fn all_finite_window_crash_cuts_can_prepare_actual_recovery(states: Seq<Media>, events: Seq<crate::journal_window_device::Event>,
    initial: Disk, v: WindowView, layout: &JournalLayout)
    requires context(initial, v), layout.wf(), layout.view() == v.layout, states[0] == media::initial(), media::execution(states, events, v),
    ensures forall|i: int| 0 <= i < states.len() ==> #[trigger] recovery_profile::input_ok(
        journal_view::snapshot(media::disk(states[i], initial, v), v.layout), v.uuid, layout, media::disk(states[i], initial, v)[0], v.partition_bytes),
{
    media::initialization(v);
    media::every_finite_byte_persistence_interleaving_preserves_order(states, events, v);
    assert forall|i: int| 0 <= i < states.len() implies #[trigger] recovery_profile::input_ok(
        journal_view::snapshot(media::disk(states[i], initial, v), v.layout), v.uuid, layout, media::disk(states[i], initial, v)[0], v.partition_bytes) by {
        every_window_crash_snapshot_can_prepare_actual_recovery(states[i], initial, v, layout);
    }
}

pub proof fn all_finite_recovery_attempts_after_a_window_crash_preserve_admission(m: Media, initial: Disk, v: WindowView, layout: &JournalLayout,
    images: Seq<Disk>, attempts: Seq<recovery_closure::Attempt<'_>>)
    requires context(initial, v), media::inv(m, v), layout.wf(), layout.view() == v.layout,
        images[0] == media::disk(m, initial, v), recovery_closure::attempt_trace(images, attempts, v.uuid, layout),
    ensures forall|i: int| 0 <= i < images.len() ==> #[trigger] recovery_profile::input_ok(
        journal_view::snapshot(images[i], v.layout), v.uuid, layout, images[i][0], v.partition_bytes),
{
    every_window_crash_snapshot_can_prepare_actual_recovery(m, initial, v, layout);
    recovery_closure::every_finite_sequence_of_recovery_crashes_preserves_admission(images, attempts, v.uuid, layout, v.partition_bytes);
}

}
