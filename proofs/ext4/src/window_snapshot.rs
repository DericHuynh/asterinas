// SPDX-License-Identifier: MPL-2.0

//! Actual journal-header and primary-superblock sources at every window cut.
//! Prefix retirement may be physically visible before its callback is reported.

use vstd::prelude::*;
use crate::{bytes, crc, journal_superblock, journal_view, journal_window::{self as window, Operation, WindowView},
    journal_window_device as device, journal_window_media::{self as media, Media}, replay_refinement::Disk,
    super_state, superblock, window_provenance::{self as provenance, context}, window_stream};

verus! {

pub open spec fn head(m: Media, v: WindowView) -> Option<nat> {
    match provenance::last_at(m.writes, m.ledger.stable, v, v.layout.start, m.writes.len()) {
        Some(Operation::Activate) => Some(0nat), Some(Operation::Tail(k)) => Some(k as nat), _ => None,
    }
}

pub proof fn every_window_crash_keeps_the_initialized_journal_mapping(m: Media, initial: Disk, v: WindowView)
    requires context(initial, v), media::inv(m, v),
    ensures journal_view::mapped(media::disk(m, initial, v), v.layout),
{
    hide(crc::fold);
    assert forall|logical: u32| logical < v.layout.journal_blocks implies
        #[trigger] media::disk(m, initial, v).dom().contains((v.layout.start + logical) as u32)
        && media::disk(m, initial, v)[(v.layout.start + logical) as u32].len() == 4096 by {
        let block = (v.layout.start + logical) as u32;
        journal_view::a_mapped_logical_block_has_complete_physical_bytes(initial, v.layout, logical);
        assert(initial.dom().contains(block) && initial[block].len() == 4096);
        provenance::every_block_is_initial_or_its_last_issued_stable_image(m, initial, v, block);
        match provenance::last_at(m.writes, m.ledger.stable, v, block, m.writes.len()) {
            Some(op) => { window::every_window_command_is_partition_bounded(v, op); },
            None => {},
        }
        media::every_media_cut_preserves_the_device_domain(m, initial, v);
    }
}

pub proof fn every_actual_header_is_initial_or_an_ordered_prefix_image(m: Media, initial: Disk, v: WindowView)
    requires context(initial, v), media::inv(m, v),
    ensures match head(m, v) {
        None => media::disk(m, initial, v)[v.layout.start] == v.initial_journal.subrange(0, 4096)
            && !m.ledger.stable.contains(Operation::Activate) && provenance::durable(m, v) == 0 && m.ledger.io.retired == 0,
        Some(k) => k <= m.ledger.io.checkpoint <= m.ledger.io.commit <= provenance::durable(m, v) <= v.txs.len()
            && m.ledger.io.retired <= k && media::disk(m, initial, v)[v.layout.start] == v.tails[k as int]
            && (k == 0 ==> m.ledger.stable.contains(Operation::Activate))
            && (k > 0 ==> m.ledger.stable.contains(Operation::Tail(k as usize))),
    },
        match head(m, v) { Some(k) => (forall|t: usize, j: usize| t < k && j < window::counts(v)[t as int] ==> #[trigger] m.ledger.stable.contains(Operation::Home(t, j))), None => true },
{
    hide(crc::fold);
    window::a_window_retains_its_geometry_and_bounded_counts(v);
    provenance::stable_commit_records_are_exactly_a_contiguous_prefix(m, v);
    let block = v.layout.start;
    journal_view::a_mapped_logical_block_has_complete_physical_bytes(initial, v.layout, 0);
    assert(initial.dom().contains(block));
    journal_view::snapshot_block_is_the_physical_image(initial, v.layout, 0);
    provenance::every_block_is_initial_or_its_last_issued_stable_image(m, initial, v, block);
    match provenance::last_at(m.writes, m.ledger.stable, v, block, m.writes.len()) {
        None => {
            provenance::an_absent_last_image_means_no_stable_write(m, v, block);
            assert(media::address(v, Operation::Activate) == block);
            if provenance::durable(m, v) > 0 {
                assert(m.ledger.stable.contains(Operation::Commit(0)));
                provenance::every_nonbootstrap_write_requires_durable_activation(m, v, Operation::Commit(0));
            }
            if m.ledger.io.retired > 0 { assert(m.ledger.stable.contains(Operation::Tail(m.ledger.io.retired))); }
            assert(!m.ledger.stable.contains(Operation::Activate));
            assert(provenance::durable(m, v) == 0 && m.ledger.io.retired == 0);
            assert(media::disk(m, initial, v)[block] == v.initial_journal.subrange(0, 4096));
        },
        Some(op) => {
            match op {
                Operation::Home(t, j) => { media::home_location(v, t, j); },
                Operation::Descriptor(_) | Operation::Payload(_, _) | Operation::Commit(_) => { media::log_location(v, op); },
                Operation::Activate => {
                    if m.ledger.io.retired > 0 {
                        assert(m.ledger.stable.contains(Operation::Tail(m.ledger.io.retired)));
                        provenance::every_other_stable_alias_is_older(m, v, block, op, Operation::Tail(m.ledger.io.retired));
                    }
                },
                Operation::Tail(k) => {
                    assert(device::bounded(m.ledger.io, op, window::counts(v)));
                    device::tail_issue_requires_the_entire_checkpoint_prefix_stable(m.ledger, window::counts(v), k);
                    if m.ledger.io.retired > k {
                        assert(m.ledger.stable.contains(Operation::Tail(m.ledger.io.retired)));
                        provenance::every_other_stable_alias_is_older(m, v, block, op, Operation::Tail(m.ledger.io.retired));
                    }
                },
                _ => {},
            }
            assert(op is Activate || op is Tail);
            if let Some(k) = head(m, v) {
                assert(k <= m.ledger.io.checkpoint);
                assert(m.ledger.io.retired <= k);
                assert(media::disk(m, initial, v)[block] == v.tails[k as int]);
                assert forall|t: usize, j: usize| t < k && j < window::counts(v)[t as int] implies #[trigger] m.ledger.stable.contains(Operation::Home(t, j)) by {
                    if k > 0 { device::tail_issue_requires_the_entire_checkpoint_prefix_stable(m.ledger, window::counts(v), k as usize); }
                }
            }
        },
    }
}

pub proof fn every_actual_journal_header_retains_its_validated_identity(m: Media, initial: Disk, v: WindowView)
    requires context(initial, v), media::inv(m, v),
    ensures journal_superblock::accepted(journal_view::snapshot(media::disk(m, initial, v), v.layout).subrange(0, 1024), v.uuid, v.layout.journal_blocks),
        match head(m, v) {
            None => bytes::be32(journal_view::snapshot(media::disk(m, initial, v), v.layout), 28) == 0,
            Some(k) => bytes::be32(journal_view::snapshot(media::disk(m, initial, v), v.layout), 24) == v.first as nat + k
                && bytes::be32(journal_view::snapshot(media::disk(m, initial, v), v.layout), 28)
                    == if k == v.txs.len() { 0nat } else { window_stream::boundary(v, k) }
                && bytes::be32(journal_view::snapshot(media::disk(m, initial, v), v.layout), 40) == 17,
        },
{
    hide(crc::fold);
    hide(journal_superblock::accepted);
    every_window_crash_keeps_the_initialized_journal_mapping(m, initial, v);
    every_actual_header_is_initial_or_an_ordered_prefix_image(m, initial, v);
    journal_view::snapshot_block_is_the_physical_image(media::disk(m, initial, v), v.layout, 0);
    let journal = journal_view::snapshot(media::disk(m, initial, v), v.layout);
    assert(journal.subrange(0, 1024) =~= media::disk(m, initial, v)[v.layout.start].subrange(0, 1024));
    match head(m, v) {
        None => {
            reveal(window::valid);
            assert(journal.subrange(0, 1024) =~= v.initial_journal.subrange(0, 1024));
        },
        Some(k) => {
            window::window_header(v, k as int);
            assert(window::header_image(v.tails[k as int], v.initial_journal, v.uuid, v.layout.journal_blocks,
                (v.first as nat + k) as u32, window::tail_start(v, k as int)));
            assert(v.tails[k as int].len() == 4096);
            assert(journal_superblock::accepted(v.tails[k as int].subrange(0, 1024), v.uuid, v.layout.journal_blocks));
            assert(journal.subrange(0, 1024) == v.tails[k as int].subrange(0, 1024));
            if k < v.txs.len() { window_stream::reserved_boundaries_match_the_exact_payload_prefixes(v, k); }
            reveal(window::valid);
        },
    }
}

pub proof fn every_primary_image_preserves_identity_and_active_recovery_policy(m: Media, initial: Disk, v: WindowView)
    requires context(initial, v), media::inv(m, v),
    ensures media::disk(m, initial, v)[0].len() == 4096,
        superblock::accepted(media::disk(m, initial, v)[0].subrange(1024, 2048), v.partition_bytes),
        bytes::le32(media::disk(m, initial, v)[0], 1028) == v.layout.fs_blocks,
        media::disk(m, initial, v)[0].subrange(1128, 1144) == v.initial_primary.subrange(1128, 1144),
        head(m, v) is Some ==> super_state::replay_ok(v.dirty, media::disk(m, initial, v)[0], v.partition_bytes),
{
    hide(crc::fold);
    hide(superblock::accepted);
    reveal(window::valid);
    provenance::every_block_is_initial_or_its_last_issued_stable_image(m, initial, v, 0);
    match provenance::last_at(m.writes, m.ledger.stable, v, 0, m.writes.len()) {
        None => {
            if head(m, v) is Some {
                every_actual_header_is_initial_or_an_ordered_prefix_image(m, initial, v);
                if let Some(k) = head(m, v) {
                    if k > 0 { provenance::every_nonbootstrap_write_requires_durable_activation(m, v, Operation::Tail(k as usize)); }
                    provenance::every_nonbootstrap_write_requires_durable_activation(m, v, Operation::Activate);
                }
                provenance::an_absent_last_image_means_no_stable_write(m, v, 0);
                assert(m.ledger.stable.contains(Operation::Dirty));
                assert(media::address(v, Operation::Dirty) != 0);
            }
        },
        Some(op) => {
            match op {
                Operation::Dirty => {
                    super_state::recovery_flag_image_preserves_uuid_and_boot_bytes(v.initial_primary, v.dirty);
                    assert(super_state::replay_ok(v.dirty, v.dirty, v.partition_bytes));
                },
                Operation::Home(t, j) => {
                    window::window_entry(v, t as int); reveal(window::positioned_valid);
                    let tx = v.txs[t as int].tx;
                    assert(tx.tags[j as int].block == 0);
                    assert(super_state::replay_ok(v.dirty, tx.original[j as int].image, v.partition_bytes));
                    super_state::replay_preserves_geometry_and_keeps_recovery(v.dirty, tx.original[j as int].image, v.partition_bytes);
                    super_state::recovery_flag_image_preserves_uuid_and_boot_bytes(v.initial_primary, v.dirty);
                },
                Operation::Descriptor(_) | Operation::Payload(_, _) | Operation::Commit(_) => { media::log_location(v, op); },
                _ => {},
            }
            assert(op is Dirty || op is Home);
            assert(super_state::replay_ok(v.dirty, media::disk(m, initial, v)[0], v.partition_bytes));
        },
    }
}

}
