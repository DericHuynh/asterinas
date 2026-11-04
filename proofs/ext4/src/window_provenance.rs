// SPDX-License-Identifier: MPL-2.0

//! Exact byte origins at arbitrary persistence cuts of the reserved window.
//! This identifies headers by their issued bytes, never by CRC injectivity.

use vstd::prelude::*;
use crate::{bytes, crc, epoch, freshness, jbd2, journal_view, journal_window::{self as window, Operation, WindowView},
    journal_window_device as device, journal_window_media::{self as media, Media}, replay_refinement::Disk};

verus! {

broadcast use {vstd::seq_lib::lemma_seq_contains, Seq::to_set_ensures};

pub open spec fn context(initial: Disk, v: WindowView) -> bool {
    &&& window::valid(v) && media::targets_exist(initial, v)
    &&& journal_view::mapped(initial, v.layout) && journal_view::snapshot(initial, v.layout) == v.initial_journal
    &&& initial.dom().contains(0) && initial[0] == v.initial_primary
}

pub open spec fn last_at(writes: Seq<Operation>, stable: Set<Operation>, v: WindowView, block: u32, limit: nat) -> Option<Operation>
    decreases limit,
{
    if limit == 0 { None } else {
        let op = writes[limit as int - 1];
        if stable.contains(op) && media::address(v, op) == block { Some(op) }
        else { last_at(writes, stable, v, block, (limit - 1) as nat) }
    }
}

proof fn apply_lookup(initial: Disk, writes: Seq<Operation>, stable: Set<Operation>, v: WindowView, block: u32, limit: nat)
    requires limit <= writes.len(), initial.dom().contains(block),
    ensures media::apply(initial, v, writes, stable, limit).dom().contains(block),
        match last_at(writes, stable, v, block, limit) {
            Some(op) => stable.contains(op) && media::address(v, op) == block
                && (exists|i: int| 0 <= i < limit && #[trigger] writes[i] == op)
                && media::apply(initial, v, writes, stable, limit)[block] == media::image(v, op),
            None => media::apply(initial, v, writes, stable, limit)[block] == initial[block],
        },
    decreases limit,
{
    if limit > 0 {
        apply_lookup(initial, writes, stable, v, block, (limit - 1) as nat);
        if stable.contains(writes[limit as int - 1]) && media::address(v, writes[limit as int - 1]) == block {
            assert(exists|i: int| 0 <= i < limit && #[trigger] writes[i] == writes[limit as int - 1]);
        }
    }
}

pub proof fn every_block_is_initial_or_its_last_issued_stable_image(m: Media, initial: Disk, v: WindowView, block: u32)
    requires media::inv(m, v), initial.dom().contains(block),
    ensures media::disk(m, initial, v).dom().contains(block),
        match last_at(m.writes, m.ledger.stable, v, block, m.writes.len()) {
        Some(op) => m.ledger.stable.contains(op) && m.ledger.issued.contains(op)
            && device::legal(op, window::counts(v)) && media::address(v, op) == block
            && media::disk(m, initial, v)[block] == media::image(v, op),
        None => media::disk(m, initial, v)[block] == initial[block],
    },
{
    apply_lookup(initial, m.writes, m.ledger.stable, v, block, m.writes.len());
    if let Some(op) = last_at(m.writes, m.ledger.stable, v, block, m.writes.len()) {
        let i = choose|i: int| 0 <= i < m.writes.len() && m.writes[i] == op;
        assert(m.writes.to_set().contains(m.writes[i]));
    }
}

pub proof fn an_unpersisted_log_slot_keeps_its_exact_original_bytes(m: Media, initial: Disk, v: WindowView, op: Operation)
    requires context(initial, v), media::inv(m, v), device::legal(op, window::counts(v)), media::is_log(op),
    ensures media::disk(m, initial, v)[media::address(v, op)]
        == if m.ledger.stable.contains(op) { media::image(v, op) } else { initial[media::address(v, op)] },
{
    if m.ledger.stable.contains(op) { media::a_stable_log_record_has_exact_bytes(m, initial, v, op); }
    else {
        assert forall|other: Operation| m.ledger.stable.contains(other) implies #[trigger] media::address(v, other) != media::address(v, op) by {
            if media::address(v, other) == media::address(v, op) {
                assert(device::legal(other, window::counts(v)));
                media::only_home_versions_and_tail_headers_can_alias(v, op, other);
            }
        }
        assert(initial.dom().contains(media::address(v, op)));
        media::blocks_without_a_stable_write_retain_their_initial_bytes(m, initial, v, media::address(v, op));
    }
}

pub proof fn a_fresh_metadata_header_is_an_issued_descriptor_or_commit(m: Media, initial: Disk, v: WindowView, logical: u32, sequence: u32)
    requires context(initial, v), media::inv(m, v), 1 <= logical < v.layout.journal_blocks, v.first <= sequence,
        jbd2::header_ok(media::disk(m, initial, v)[(v.layout.start + logical) as u32], sequence),
    ensures exists|op: Operation| m.ledger.stable.contains(op) && (op is Descriptor || op is Commit)
        && device::legal(op, window::counts(v)) && media::address(v, op) as nat == v.layout.start as nat + logical
        && media::disk(m, initial, v)[(v.layout.start + logical) as u32] == media::image(v, op)
        && v.txs[media::log_index(op)].tx.sequence == sequence,
{
    hide(crc::fold);
    window::a_window_retains_its_geometry_and_bounded_counts(v);
    let block = (v.layout.start + logical) as u32;
    assert(initial.dom().contains(block));
    every_block_is_initial_or_its_last_issued_stable_image(m, initial, v, block);
    match last_at(m.writes, m.ledger.stable, v, block, m.writes.len()) {
        None => {
            assert(epoch::newer(v.initial_journal, bytes::be32(v.initial_journal, 24) as u32, v.first)) by { reveal(window::valid); }
            freshness::an_old_journal_block_cannot_have_a_current_or_later_header(initial, v.layout,
                bytes::be32(v.initial_journal, 24) as u32, v.first, logical, sequence);
        },
        Some(op) => {
            match op {
                Operation::Home(t, k) => { media::home_location(v, t, k); },
                Operation::Payload(t, k) => {
                    window::window_entry(v, t as int); reveal(window::positioned_valid);
                    freshness::an_encoded_payload_cannot_be_a_metadata_header(v.txs[t as int].tx, k as int, sequence);
                },
                Operation::Descriptor(t) | Operation::Commit(t) => {
                    window::window_entry(v, t as int); reveal(window::positioned_valid);
                },
                _ => {},
            }
            assert(op is Descriptor || op is Commit);
            assert(v.txs[media::log_index(op)].tx.sequence == sequence);
            assert(exists|candidate: Operation| m.ledger.stable.contains(candidate) && (candidate is Descriptor || candidate is Commit)
                && device::legal(candidate, window::counts(v)) && media::address(v, candidate) as nat == v.layout.start as nat + logical
                && media::disk(m, initial, v)[block] == media::image(v, candidate)
                && v.txs[media::log_index(candidate)].tx.sequence == sequence);
        },
    }
}

pub open spec fn durable(m: Media, v: WindowView) -> nat {
    m.ledger.io.commit as nat + if m.ledger.io.commit < v.txs.len() && m.ledger.stable.contains(Operation::Commit(m.ledger.io.commit)) { 1nat } else { 0nat }
}

pub proof fn stable_commit_records_are_exactly_a_contiguous_prefix(m: Media, v: WindowView)
    requires window::valid(v), media::inv(m, v),
    ensures m.ledger.io.commit <= durable(m, v) <= v.txs.len(),
        forall|t: usize| t < v.txs.len() ==> (#[trigger] m.ledger.stable.contains(Operation::Commit(t)) <==> t < durable(m, v)),
        forall|t: usize, k: usize| m.ledger.issued.contains(Operation::Home(t, k)) ==> t < m.ledger.io.commit,
{
    device::an_acknowledged_prefix_has_durable_commit_records(m.ledger, window::counts(v));
    assert forall|t: usize| t < v.txs.len() implies (#[trigger] m.ledger.stable.contains(Operation::Commit(t)) <==> t < durable(m, v)) by {
        if m.ledger.stable.contains(Operation::Commit(t)) {
            assert(device::bounded(m.ledger.io, Operation::Commit(t), window::counts(v)));
        }
    }
    assert forall|t: usize, k: usize| m.ledger.issued.contains(Operation::Home(t, k)) implies t < m.ledger.io.commit by {
        device::home_issue_requires_a_stable_commit(m.ledger, window::counts(v), t, k);
        assert(device::bounded(m.ledger.io, Operation::Home(t, k), window::counts(v)));
    }
}

proof fn absent_prefix(writes: Seq<Operation>, stable: Set<Operation>, v: WindowView, block: u32, limit: nat)
    requires limit <= writes.len(), last_at(writes, stable, v, block, limit) is None,
    ensures forall|i: int| 0 <= i < limit && #[trigger] stable.contains(writes[i]) ==> media::address(v, writes[i]) != block,
    decreases limit,
{
    if limit > 0 { absent_prefix(writes, stable, v, block, (limit - 1) as nat); }
}

pub proof fn an_absent_last_image_means_no_stable_write(m: Media, v: WindowView, block: u32)
    requires media::inv(m, v), last_at(m.writes, m.ledger.stable, v, block, m.writes.len()) is None,
    ensures forall|op: Operation| m.ledger.stable.contains(op) ==> #[trigger] media::address(v, op) != block,
{
    absent_prefix(m.writes, m.ledger.stable, v, block, m.writes.len());
    assert forall|op: Operation| m.ledger.stable.contains(op) implies #[trigger] media::address(v, op) != block by {
        assert(m.writes.contains(op));
        let i = choose|i: int| 0 <= i < m.writes.len() && m.writes[i] == op;
        assert(m.ledger.stable.contains(m.writes[i]));
    }
}

proof fn locate_last(writes: Seq<Operation>, stable: Set<Operation>, v: WindowView, block: u32, limit: nat, op: Operation)
    requires limit <= writes.len(), last_at(writes, stable, v, block, limit) == Some(op),
    ensures exists|i: int| 0 <= i < limit && writes[i] == op && stable.contains(op) && media::address(v, op) == block
        && (forall|j: int| i < j < limit && #[trigger] stable.contains(writes[j]) ==> media::address(v, writes[j]) != block),
    decreases limit,
{
    if stable.contains(writes[limit as int - 1]) && media::address(v, writes[limit as int - 1]) == block {
        let i = limit as int - 1;
        assert(writes[i] == op);
    } else {
        locate_last(writes, stable, v, block, (limit - 1) as nat, op);
        let i = choose|i: int| 0 <= i < limit - 1 && writes[i] == op && stable.contains(op) && media::address(v, op) == block
            && (forall|j: int| i < j < limit - 1 && #[trigger] stable.contains(writes[j]) ==> media::address(v, writes[j]) != block);
        assert forall|j: int| i < j < limit && #[trigger] stable.contains(writes[j]) implies media::address(v, writes[j]) != block by {
            if j < limit - 1 { assert(media::address(v, writes[j]) != block); }
        }
    }
}

pub proof fn every_other_stable_alias_is_older(m: Media, v: WindowView, block: u32, op: Operation, other: Operation)
    requires media::inv(m, v), last_at(m.writes, m.ledger.stable, v, block, m.writes.len()) == Some(op),
        m.ledger.stable.contains(other), media::address(v, other) == block, other != op,
    ensures media::precedes(other, op),
{
    locate_last(m.writes, m.ledger.stable, v, block, m.writes.len(), op);
    let i = choose|i: int| 0 <= i < m.writes.len() && m.writes[i] == op && m.ledger.stable.contains(op) && media::address(v, op) == block
        && (forall|j: int| i < j < m.writes.len() && #[trigger] m.ledger.stable.contains(m.writes[j]) ==> media::address(v, m.writes[j]) != block);
    assert(m.writes.contains(other));
    let j = choose|j: int| 0 <= j < m.writes.len() && m.writes[j] == other;
    if i < j { assert(media::address(v, m.writes[j]) != block); }
    assert(j < i);
    assert(media::precedes(m.writes[j], m.writes[i]));
}

pub proof fn every_nonbootstrap_write_requires_durable_activation(m: Media, v: WindowView, op: Operation)
    requires media::inv(m, v), m.ledger.issued.contains(op), !(op is Dirty),
    ensures m.ledger.stable.contains(Operation::Dirty), !(op is Activate) ==> m.ledger.stable.contains(Operation::Activate),
{
    assert(device::legal(op, window::counts(v)) && device::bounded(m.ledger.io, op, window::counts(v)));
    match op {
        Operation::Activate => {}, Operation::Descriptor(_) | Operation::Payload(_, _) | Operation::Commit(_)
            | Operation::Home(_, _) | Operation::Tail(_) => { assert(m.ledger.io.bootstrap == 4); }, _ => {},
    }
    assert(m.ledger.issued.contains(Operation::Dirty));
    if !(op is Activate) { assert(m.ledger.issued.contains(Operation::Activate)); }
}

}
