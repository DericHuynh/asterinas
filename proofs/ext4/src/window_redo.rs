// SPDX-License-Identifier: MPL-2.0

//! Byte-valued redo closure over partial FIFO checkpoints. Every physically
//! retired home prefix is complete; newer partial homes are covered by redo.

use vstd::prelude::*;
use crate::{crc, journal_window::{self as window, Operation, WindowView}, journal_window_device as device,
    journal_window_media::{self as media, Media}, replay, replay_refinement::{self as redo, Disk},
    transaction_refinement, window_provenance::{self as provenance, context}, window_records as records};

verus! {

pub open spec fn home_block(initial: Disk, v: WindowView, block: u32) -> bool {
    initial.dom().contains(block) && !(v.layout.start <= block < v.layout.start as nat + v.layout.journal_blocks)
}

pub open spec fn baseline(m: Media, initial: Disk, v: WindowView) -> Disk {
    if m.ledger.stable.contains(Operation::Dirty) { initial.insert(0, v.dirty) } else { initial }
}

proof fn baseline_domain(m: Media, initial: Disk, v: WindowView)
    requires context(initial, v),
    ensures baseline(m, initial, v).dom() == initial.dom(),
{ }

pub proof fn every_window_log_target_exists_in_the_initial_device(initial: Disk, v: WindowView, first: nat, end: nat)
    requires context(initial, v), first <= end <= v.txs.len(),
    ensures redo::all_targets_exist(initial, records::log(v, first, end)),
{
    hide(crc::fold);
    assert forall|i: int| 0 <= i < records::log(v, first, end).len() implies #[trigger] initial.dom().contains(records::log(v, first, end)[i].block) by {
        records::every_log_entry_has_the_exact_original_transaction_source(v, first, end, i);
        let (t, k) = choose|t: nat, k: int| first <= t < end && 0 <= k < window::counts(v)[t as int]
            && records::log(v, first, end)[i] == transaction_refinement::log(v.txs[t as int].tx)[k];
        window::window_entry(v, t as int); reveal(window::positioned_valid);
        let op = Operation::Home(t as usize, k as usize);
        assert(device::legal(op, window::counts(v)));
        assert(initial.dom().contains(media::address(v, op)));
    }
}

proof fn log_sequence_bounds(v: WindowView, first: nat, end: nat, i: int)
    requires window::valid(v), first <= end <= v.txs.len(), 0 <= i < records::log(v, first, end).len(),
    ensures v.first as nat + first <= (records::log(v, first, end)[i].sequence as nat) < v.first as nat + end,
{
    records::every_log_entry_has_the_exact_original_transaction_source(v, first, end, i);
    let (t, k) = choose|t: nat, k: int| first <= t < end && 0 <= k < window::counts(v)[t as int]
        && records::log(v, first, end)[i] == transaction_refinement::log(v.txs[t as int].tx)[k];
    window::window_entry(v, t as int);
}

proof fn log_sequences_are_ordered(v: WindowView, first: nat, end: nat, i: int, j: int)
    requires window::valid(v), first <= end <= v.txs.len(), 0 <= i <= j < records::log(v, first, end).len(),
    ensures records::log(v, first, end)[i].sequence <= records::log(v, first, end)[j].sequence,
    decreases end - first,
{
    let prefix = records::log(v, first, (end - 1) as nat);
    if j < prefix.len() { log_sequences_are_ordered(v, first, (end - 1) as nat, i, j); }
    else {
        if i < prefix.len() { log_sequence_bounds(v, first, (end - 1) as nat, i); }
        window::window_entry(v, end as int - 1);
    }
}

proof fn the_latest_target_has_the_greatest_sequence(v: WindowView, first: nat, end: nat, block: u32, last: nat, other: int)
    requires window::valid(v), first <= end <= v.txs.len(),
        redo::last_eligible(records::log(v, first, end), Seq::empty(), block) == Some(last),
        0 <= other < records::log(v, first, end).len(), records::log(v, first, end)[other].block == block,
    ensures records::log(v, first, end)[other].sequence <= records::log(v, first, end)[last as int].sequence,
{
    let log = records::log(v, first, end);
    redo::last_eligible_characterizes_latest(log, Seq::empty(), block);
    if last < other { assert(log[other].block != block || replay::blocked(block, log[other].sequence, Seq::empty())); }
    log_sequences_are_ordered(v, first, end, other, last as int);
}

proof fn no_latest_target_means_no_log_target(v: WindowView, first: nat, end: nat, block: u32)
    requires redo::last_eligible(records::log(v, first, end), Seq::empty(), block) is None,
    ensures forall|i: int| 0 <= i < records::log(v, first, end).len() ==> (#[trigger] records::log(v, first, end)[i]).block != block,
{
    redo::last_eligible_characterizes_latest(records::log(v, first, end), Seq::empty(), block);
}

proof fn a_home_write_without_an_unretired_target_belongs_to_the_retired_prefix(m: Media, v: WindowView, retired: nat, block: u32, t: usize, k: usize)
    requires window::valid(v), media::inv(m, v), retired <= provenance::durable(m, v),
        m.ledger.issued.contains(Operation::Home(t, k)), media::address(v, Operation::Home(t, k)) == block,
        forall|i: int| 0 <= i < records::log(v, retired, provenance::durable(m, v)).len() ==> (#[trigger] records::log(v, retired, provenance::durable(m, v))[i]).block != block,
    ensures t < retired,
{
    provenance::stable_commit_records_are_exactly_a_contiguous_prefix(m, v);
    if t >= retired {
        records::every_original_payload_occurs_in_its_transaction_log(v, retired, provenance::durable(m, v), t as nat, k as int);
        let i = choose|i: int| 0 <= i < records::log(v, retired, provenance::durable(m, v)).len()
            && #[trigger] records::log(v, retired, provenance::durable(m, v))[i] == transaction_refinement::log(v.txs[t as int].tx)[k as int];
        assert(records::log(v, retired, provenance::durable(m, v))[i].block == block);
    }
}

proof fn a_stable_home_image_is_the_only_possible_nonjournal_write(m: Media, initial: Disk, v: WindowView, block: u32, op: Operation)
    requires context(initial, v), media::inv(m, v), home_block(initial, v, block),
        provenance::last_at(m.writes, m.ledger.stable, v, block, m.writes.len()) == Some(op),
    ensures op is Home || op is Dirty && block == 0, m.ledger.stable.contains(op), media::address(v, op) == block,
{
    hide(crc::fold);
    provenance::every_block_is_initial_or_its_last_issued_stable_image(m, initial, v, block);
    match op {
        Operation::Descriptor(_) | Operation::Payload(_, _) | Operation::Commit(_) => { media::log_location(v, op); },
        _ => {},
    }
    window::a_window_retains_its_geometry_and_bounded_counts(v);
}

pub proof fn a_retired_only_home_block_has_its_exact_prefix_image(m: Media, initial: Disk, v: WindowView, retired: nat, block: u32)
    requires context(initial, v), media::inv(m, v), home_block(initial, v, block), retired <= provenance::durable(m, v),
        forall|t: usize, k: usize| t < retired && k < window::counts(v)[t as int] ==> #[trigger] m.ledger.stable.contains(Operation::Home(t, k)),
        forall|i: int| 0 <= i < records::log(v, retired, provenance::durable(m, v)).len() ==> (#[trigger] records::log(v, retired, provenance::durable(m, v))[i]).block != block,
    ensures media::disk(m, initial, v)[block] == redo::chronological(baseline(m, initial, v), records::log(v, 0, retired), Seq::empty())[block],
{
    hide(crc::fold);
    provenance::stable_commit_records_are_exactly_a_contiguous_prefix(m, v);
    every_window_log_target_exists_in_the_initial_device(initial, v, 0, retired);
    let prefix = records::log(v, 0, retired);
    baseline_domain(m, initial, v);
    assert(redo::all_targets_exist(baseline(m, initial, v), prefix));
    redo::chronological_lookup(baseline(m, initial, v), prefix, Seq::empty(), block);
    provenance::every_block_is_initial_or_its_last_issued_stable_image(m, initial, v, block);
    match redo::last_eligible(prefix, Seq::empty(), block) {
        Some(last) => {
            redo::last_eligible_characterizes_latest(prefix, Seq::empty(), block);
            records::every_log_entry_has_the_exact_original_transaction_source(v, 0, retired, last as int);
            let (t, k) = choose|t: nat, k: int| 0 <= t < retired && 0 <= k < window::counts(v)[t as int]
                && prefix[last as int] == transaction_refinement::log(v.txs[t as int].tx)[k];
            let latest = Operation::Home(t as usize, k as usize);
            assert(m.ledger.stable.contains(latest));
            match provenance::last_at(m.writes, m.ledger.stable, v, block, m.writes.len()) {
                None => {
                    provenance::an_absent_last_image_means_no_stable_write(m, v, block);
                    assert(media::address(v, latest) == block);
                },
                Some(op) => {
                    a_stable_home_image_is_the_only_possible_nonjournal_write(m, initial, v, block, op);
                    if let Operation::Home(u, l) = op {
                        a_home_write_without_an_unretired_target_belongs_to_the_retired_prefix(m, v, retired, block, u, l);
                        records::every_original_payload_occurs_in_its_transaction_log(v, 0, retired, u as nat, l as int);
                        let i = choose|i: int| 0 <= i < prefix.len() && #[trigger] prefix[i] == transaction_refinement::log(v.txs[u as int].tx)[l as int];
                        the_latest_target_has_the_greatest_sequence(v, 0, retired, block, last, i);
                        window::window_entry(v, t as int); window::window_entry(v, u as int);
                        assert(u <= t);
                        if op != latest { provenance::every_other_stable_alias_is_older(m, v, block, op, latest); }
                        assert(op == latest);
                    } else {
                        assert(op is Dirty);
                        provenance::every_other_stable_alias_is_older(m, v, block, op, latest);
                        assert(false);
                    }
                },
            }
        },
        None => {
            no_latest_target_means_no_log_target(v, 0, retired, block);
            if let Some(op) = provenance::last_at(m.writes, m.ledger.stable, v, block, m.writes.len()) {
                a_stable_home_image_is_the_only_possible_nonjournal_write(m, initial, v, block, op);
                if let Operation::Home(t, k) = op {
                    a_home_write_without_an_unretired_target_belongs_to_the_retired_prefix(m, v, retired, block, t, k);
                    records::every_original_payload_occurs_in_its_transaction_log(v, 0, retired, t as nat, k as int);
                    let i = choose|i: int| 0 <= i < prefix.len() && #[trigger] prefix[i] == transaction_refinement::log(v.txs[t as int].tx)[k as int];
                    assert(prefix[i].block == block);
                } else {
                    assert(op is Dirty && block == 0);
                    assert(baseline(m, initial, v)[block] == v.dirty);
                }
            } else {
                if block == 0 && m.ledger.stable.contains(Operation::Dirty) {
                    provenance::an_absent_last_image_means_no_stable_write(m, v, block);
                    assert(media::address(v, Operation::Dirty) == block);
                }
                assert(baseline(m, initial, v)[block] == initial[block]);
            }
        },
    }
}

proof fn chronological_concatenation(initial: Disk, left: Seq<replay::WriteView>, right: Seq<replay::WriteView>)
    ensures redo::chronological(initial, left + right, Seq::empty())
        == redo::chronological(redo::chronological(initial, left, Seq::empty()), right, Seq::empty()),
    decreases right.len(),
{
    if right.len() > 0 {
        chronological_concatenation(initial, left, right.drop_last());
        assert((left + right).drop_last() =~= left + right.drop_last());
    } else { assert(left + right =~= left); }
}

pub proof fn redo_of_the_unretired_suffix_covers_every_partial_home_checkpoint(m: Media, initial: Disk, v: WindowView, retired: nat, block: u32)
    requires context(initial, v), media::inv(m, v), home_block(initial, v, block), retired <= provenance::durable(m, v),
        forall|t: usize, k: usize| t < retired && k < window::counts(v)[t as int] ==> #[trigger] m.ledger.stable.contains(Operation::Home(t, k)),
    ensures redo::chronological(media::disk(m, initial, v), records::log(v, retired, provenance::durable(m, v)), Seq::empty())[block]
        == redo::chronological(baseline(m, initial, v), records::log(v, 0, provenance::durable(m, v)), Seq::empty())[block],
{
    hide(crc::fold);
    provenance::stable_commit_records_are_exactly_a_contiguous_prefix(m, v);
    let end = provenance::durable(m, v);
    let prefix = records::log(v, 0, retired); let suffix = records::log(v, retired, end);
    every_window_log_target_exists_in_the_initial_device(initial, v, 0, retired);
    every_window_log_target_exists_in_the_initial_device(initial, v, retired, end);
    let media_disk = media::disk(m, initial, v);
    media::every_media_cut_preserves_the_device_domain(m, initial, v);
    assert(redo::all_targets_exist(media_disk, suffix));
    baseline_domain(m, initial, v);
    let base = baseline(m, initial, v);
    assert(redo::all_targets_exist(base, prefix) && redo::all_targets_exist(base, suffix));
    redo::chronological_lookup(base, prefix, Seq::empty(), block);
    let old_prefix = redo::chronological(base, prefix, Seq::empty());
    assert(redo::all_targets_exist(old_prefix, suffix));
    redo::chronological_lookup(media_disk, suffix, Seq::empty(), block);
    redo::chronological_lookup(old_prefix, suffix, Seq::empty(), block);
    if redo::last_eligible(suffix, Seq::empty(), block) is None {
        no_latest_target_means_no_log_target(v, retired, end, block);
        a_retired_only_home_block_has_its_exact_prefix_image(m, initial, v, retired, block);
    }
    chronological_concatenation(base, prefix, suffix);
    records::adjacent_transaction_logs_compose_exactly(v, 0, retired, end);
}

}
