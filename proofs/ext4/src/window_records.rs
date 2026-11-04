// SPDX-License-Identifier: MPL-2.0

//! Canonical multi-transaction record certificates and exact chronological
//! after-images, relative to a physically persisted journal-tail prefix.

use vstd::prelude::*;
use crate::{crc, jbd2, journal_window::{self as window, WindowView}, replay::{self, WriteView},
    scan, scan_trace::{self, Record, Source}, transaction, transaction_refinement, window_stream as stream};

verus! {

pub open spec fn log(v: WindowView, first: nat, end: nat) -> Seq<WriteView>
    decreases end,
{
    if end <= first { Seq::empty() }
    else { log(v, first, (end - 1) as nat) + transaction_refinement::log(v.txs[end as int - 1].tx) }
}

pub open spec fn descriptor_record(v: WindowView, first: nat, t: nat) -> Record {
    let p = stream::offset(v, first, t);
    Record { start: p, end: (p as nat + window::counts(v)[t as int] + 1) as u32,
        sequence: v.txs[t as int].tx.sequence, kind: 1, writes: transaction_refinement::log(v.txs[t as int].tx),
        revocations: Seq::empty(), revoke_origins: Seq::empty(),
        origins: Seq::new(window::counts(v)[t as int], |i: int| scan::Origin {
            descriptor: p, payload: (p as nat + 1 + i) as u32, index: i as nat, count: window::counts(v)[t as int] }) }
}

pub open spec fn commit_record(v: WindowView, first: nat, t: nat) -> Record {
    let p = stream::offset(v, first, t);
    Record { start: (p as nat + window::counts(v)[t as int] + 1) as u32,
        end: stream::offset(v, first, t + 1), sequence: v.txs[t as int].tx.sequence, kind: 2,
        writes: Seq::empty(), revocations: Seq::empty(), origins: Seq::empty(), revoke_origins: Seq::empty() }
}

pub open spec fn records(v: WindowView, first: nat, end: nat) -> Seq<Record>
    decreases end,
{
    if end <= first { Seq::empty() } else {
        records(v, first, (end - 1) as nat).push(descriptor_record(v, first, (end - 1) as nat)).push(commit_record(v, first, (end - 1) as nat))
    }
}

pub open spec fn transaction_present(v: WindowView, s: Source, first: nat, t: nat) -> bool {
    let p = stream::offset(v, first, t);
    &&& scan::block_at(s.journal, s.blocks, s.start, p) == v.txs[t as int].tx.descriptor
    &&& (forall|i: int| 0 <= i < window::counts(v)[t as int] ==> #[trigger]
        scan::block_at(s.journal, s.blocks, s.start, (p as nat + 1 + i) as u32) == v.txs[t as int].tx.payloads[i])
    &&& scan::block_at(s.journal, s.blocks, s.start, (p as nat + window::counts(v)[t as int] + 1) as u32) == v.txs[t as int].tx.commit
}

proof fn a_present_transaction_forms_exact_descriptor_and_commit_records(v: WindowView, s: Source, first: nat, t: nat)
    requires window::valid(v), stream::fields(v, s, first), first <= t < v.txs.len(), transaction_present(v, s, first, t),
    ensures scan_trace::record_ok(descriptor_record(v, first, t), s), scan_trace::record_ok(commit_record(v, first, t), s),
        descriptor_record(v, first, t).start == stream::offset(v, first, t),
        descriptor_record(v, first, t).end == commit_record(v, first, t).start,
        commit_record(v, first, t).end == stream::offset(v, first, t + 1),
{
    hide(crc::fold);
    window::window_entry(v, t as int); reveal(window::positioned_valid);
    stream::offset_bounds(v, first, t); stream::offset_bounds(v, first, t + 1); stream::credit_step(v, t);
    let tx = v.txs[t as int].tx;
    let r = descriptor_record(v, first, t);
    assert(tx.seed == s.seed);
    assert forall|i: int| 0 <= i < tx.original.len() implies #[trigger]
        scan::origin_ok(s.journal, s.blocks, s.start, s.uuid, s.seed, s.layout, r.writes[i], r.origins[i]) by {
        assert(tx.tags[i].block == tx.original[i].block);
        assert(scan::block_at(s.journal, s.blocks, s.start, (r.start as nat + 1 + i) as u32) == tx.payloads[i]);
        reveal(scan::origin_ok);
    }
    assert(scan_trace::record_ok(r, s)) by { reveal(scan_trace::record_ok); }
    assert(scan_trace::record_ok(commit_record(v, first, t), s)) by { reveal(scan_trace::record_ok); }
}

pub proof fn complete_encoded_transactions_form_a_committed_scan_prefix(v: WindowView, s: Source, first: nat, end: nat)
    requires window::valid(v), stream::fields(v, s, first), first <= end <= v.txs.len(),
        forall|t: nat| first <= t < end ==> #[trigger] transaction_present(v, s, first, t),
    ensures scan_trace::committed_prefix(records(v, first, end), s, log(v, first, end), Seq::empty()),
        records(v, first, end).len() == 2 * (end - first),
        scan_trace::end(records(v, first, end)) == stream::offset(v, first, end),
        scan_trace::next_sequence(records(v, first, end), s.first) == v.first as nat + end,
    decreases end - first,
{
    hide(crc::fold);
    if end == first {
        scan_trace::empty_records(s);
        stream::offset_bounds(v, first, first);
    } else {
        let t = (end - 1) as nat;
        complete_encoded_transactions_form_a_committed_scan_prefix(v, s, first, t);
        a_present_transaction_forms_exact_descriptor_and_commit_records(v, s, first, t);
        window::window_entry(v, t as int);
        let prev = records(v, first, t);
        let d = descriptor_record(v, first, t); let c = commit_record(v, first, t);
        scan_trace::append_record(prev, d, s);
        scan_trace::append_record(prev.push(d), c, s);
        assert(records(v, first, end) == prev.push(d).push(c));
    }
}

pub proof fn adjacent_transaction_logs_compose_exactly(v: WindowView, first: nat, middle: nat, end: nat)
    requires first <= middle <= end <= v.txs.len(),
    ensures log(v, first, end) == log(v, first, middle) + log(v, middle, end),
    decreases end - middle,
{
    if end > middle {
        adjacent_transaction_logs_compose_exactly(v, first, middle, (end - 1) as nat);
        assert(log(v, first, end) =~= log(v, first, middle) + log(v, middle, end));
    }
}

pub proof fn every_log_entry_has_the_exact_original_transaction_source(v: WindowView, first: nat, end: nat, i: int)
    requires first <= end <= v.txs.len(), 0 <= i < log(v, first, end).len(),
    ensures exists|t: nat, k: int| first <= t < end && 0 <= k < window::counts(v)[t as int]
        && log(v, first, end)[i] == transaction_refinement::log(v.txs[t as int].tx)[k],
    decreases end - first,
{
    let prefix = log(v, first, (end - 1) as nat);
    if i < prefix.len() {
        every_log_entry_has_the_exact_original_transaction_source(v, first, (end - 1) as nat, i);
        let (t, k) = choose|t: nat, k: int| first <= t < end - 1 && 0 <= k < window::counts(v)[t as int]
            && prefix[i] == transaction_refinement::log(v.txs[t as int].tx)[k];
    } else {
        let t = (end - 1) as nat; let k = i - prefix.len() as int;
        assert(log(v, first, end)[i] == transaction_refinement::log(v.txs[t as int].tx)[k]);
    }
}

pub proof fn every_original_payload_occurs_in_its_transaction_log(v: WindowView, first: nat, end: nat, t: nat, k: int)
    requires first <= t < end <= v.txs.len(), 0 <= k < window::counts(v)[t as int],
    ensures exists|i: int| 0 <= i < log(v, first, end).len()
        && #[trigger] log(v, first, end)[i] == transaction_refinement::log(v.txs[t as int].tx)[k],
    decreases end - t,
{
    let prefix = log(v, first, (end - 1) as nat);
    if t < end - 1 {
        every_original_payload_occurs_in_its_transaction_log(v, first, (end - 1) as nat, t, k);
        let i = choose|i: int| 0 <= i < prefix.len() && #[trigger] prefix[i] == transaction_refinement::log(v.txs[t as int].tx)[k];
        assert(log(v, first, end)[i] == transaction_refinement::log(v.txs[t as int].tx)[k]);
    } else {
        let i = prefix.len() as int + k;
        assert(0 <= i < log(v, first, end).len());
        assert(log(v, first, end)[i] == transaction_refinement::log(v.txs[t as int].tx)[k]);
    }
}

}
