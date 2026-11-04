// SPDX-License-Identifier: MPL-2.0

//! Byte-valued refinement of the reserved-window persistence ledger. Atomic
//! 4 KiB persistence and a quiescent initial snapshot are device premises.

use vstd::{assert_maps_equal, prelude::*};
use crate::{journal_program::{self, Lane}, journal_window::{self, Operation, WindowView},
    journal_window_device::{self as device, Event}, recovery_io::CommandView, replay_refinement::Disk};

verus! {

broadcast use {vstd::seq_lib::lemma_seq_contains, vstd::seq_lib::lemma_seq_empty_contains_nothing,
    vstd::seq_lib::lemma_seq_contains_after_push, Seq::to_set_ensures};

pub open spec fn address(v: WindowView, op: Operation) -> u32 {
    match journal_window::expected(v, op) { CommandView::Write { block, image } => block, _ => 0 }
}
pub open spec fn image(v: WindowView, op: Operation) -> Seq<u8> {
    match journal_window::expected(v, op) { CommandView::Write { block, image } => image, _ => Seq::empty() }
}
pub open spec fn is_log(op: Operation) -> bool {
    op is Descriptor || op is Payload || op is Commit
}
pub open spec fn log_index(op: Operation) -> int {
    match op { Operation::Descriptor(t) | Operation::Payload(t, _) | Operation::Commit(t) => t as int, _ => 0 }
}
pub open spec fn log_offset(v: WindowView, op: Operation) -> nat {
    match op { Operation::Payload(_, k) => 1 + k as nat, Operation::Commit(t) => 1 + journal_window::counts(v)[t as int], _ => 0 }
}
pub open spec fn precedes(a: Operation, b: Operation) -> bool {
    match (a, b) {
        (Operation::Dirty, Operation::Home(_, _)) | (Operation::Activate, Operation::Tail(_)) => true,
        (Operation::Home(t, _), Operation::Home(u, _)) => t < u,
        (Operation::Tail(t), Operation::Tail(u)) => t < u,
        _ => false,
    }
}

pub(crate) proof fn log_spans_are_ordered(v: WindowView, i: int, j: int)
    requires journal_window::valid(v), 0 <= i < j < v.txs.len(),
    ensures v.txs[i].source.first as nat + v.txs[i].source.blocks <= v.txs[j].source.first,
    decreases j - i,
{
    journal_window::window_entry(v, j);
    if j > i + 1 {
        log_spans_are_ordered(v, i, j - 1);
        journal_window::window_entry(v, j - 1);
        reveal(journal_window::positioned_valid);
    }
}

pub(crate) proof fn log_location(v: WindowView, op: Operation)
    requires journal_window::valid(v), device::legal(op, journal_window::counts(v)), is_log(op),
    ensures 0 <= log_index(op) < v.txs.len(),
        log_offset(v, op) < v.txs[log_index(op)].source.blocks,
        address(v, op) as nat == v.layout.start as nat + v.txs[log_index(op)].source.first as nat + log_offset(v, op),
        v.layout.start < address(v, op) < v.layout.start as nat + v.layout.journal_blocks,
{
    hide(crate::crc::fold);
    journal_window::a_window_retains_its_geometry_and_bounded_counts(v);
    journal_window::window_entry(v, log_index(op));
    reveal(journal_window::positioned_valid);
}

pub(crate) proof fn home_location(v: WindowView, t: usize, k: usize)
    requires journal_window::valid(v), device::legal(Operation::Home(t, k), journal_window::counts(v)),
    ensures !(v.layout.start <= address(v, Operation::Home(t, k)) < v.layout.start as nat + v.layout.journal_blocks),
{
    hide(crate::crc::fold);
    journal_window::window_entry(v, t as int);
    reveal(journal_window::positioned_valid);
    let tx = v.txs[t as int].tx;
    assert(crate::replay::payload_for_layout(tx.tags[k as int], tx.payloads[k as int], tx.sequence, tx.seed, tx.layout));
}

pub proof fn only_home_versions_and_tail_headers_can_alias(v: WindowView, a: Operation, b: Operation)
    requires journal_window::valid(v), device::legal(a, journal_window::counts(v)), device::legal(b, journal_window::counts(v)),
        a != b, address(v, a) == address(v, b),
    ensures precedes(a, b) || precedes(b, a),
{
    hide(crate::crc::fold);
    journal_window::a_window_retains_its_geometry_and_bounded_counts(v);
    if is_log(a) { log_location(v, a); }
    if is_log(b) { log_location(v, b); }
    if is_log(a) && is_log(b) {
        let i = log_index(a); let j = log_index(b);
        if i < j { log_spans_are_ordered(v, i, j); }
        if j < i { log_spans_are_ordered(v, j, i); }
        assert(i == j);
        match (a, b) {
            (Operation::Descriptor(_), _) | (Operation::Commit(_), _) | (Operation::Payload(_, _), _) => {},
            _ => {},
        }
    }
    match a { Operation::Home(t, k) => { home_location(v, t, k); }, _ => {} }
    match b { Operation::Home(t, k) => { home_location(v, t, k); }, _ => {} }
    if let (Operation::Home(t, k), Operation::Home(u, l)) = (a, b) {
        if t == u {
            journal_window::window_entry(v, t as int);
            reveal(journal_window::positioned_valid);
            let tx = v.txs[t as int].tx;
            if k < l { assert(tx.original[k as int].block != tx.original[l as int].block); }
            if l < k { assert(tx.original[l as int].block != tx.original[k as int].block); }
        }
    }
}

pub proof fn dispatch_fences_every_older_write_to_the_same_address(m: device::Machine, lane: Lane, v: WindowView, older: Operation)
    requires journal_window::valid(v), device::inv(m, journal_window::counts(v)),
        device::enabled(m, Event::Issue(lane), journal_window::counts(v)), m.issued.contains(older),
        journal_window::is_write(journal_window::pending_operation(journal_program::started(m.io, lane), journal_window::counts(v))),
        address(v, older) == address(v, journal_window::pending_operation(journal_program::started(m.io, lane), journal_window::counts(v))),
    ensures m.stable.contains(older), precedes(older, journal_window::pending_operation(journal_program::started(m.io, lane), journal_window::counts(v))),
{
    let shape = journal_window::counts(v);
    let newer = journal_window::pending_operation(journal_program::started(m.io, lane), shape);
    journal_program::starting_a_window_request_preserves_order(m.io, lane, shape);
    device::dispatch_never_reissues_a_write(m, lane, shape);
    assert(device::legal(newer, shape));
    only_home_versions_and_tail_headers_can_alias(v, older, newer);
    assert(device::bounded(m.io, older, shape));
    match newer {
        Operation::Home(_, _) | Operation::Tail(_) => {},
        _ => {},
    }
    assert(device::fenced(m.io, older, shape));
}

pub struct Media { pub ledger: device::Machine, pub writes: Seq<Operation> }

pub open spec fn inv(m: Media, v: WindowView) -> bool {
    &&& device::inv(m.ledger, journal_window::counts(v))
    &&& m.writes.no_duplicates() && m.writes.to_set() == m.ledger.issued
    &&& (forall|i: int, j: int| 0 <= i < j < m.writes.len() && address(v, m.writes[i]) == address(v, m.writes[j])
        ==> #[trigger] precedes(m.writes[i], m.writes[j]) && m.ledger.stable.contains(m.writes[i]))
}

proof fn assemble_invariant(m: Media, v: WindowView)
    requires device::inv(m.ledger, journal_window::counts(v)), m.writes.no_duplicates(),
        m.writes.to_set() == m.ledger.issued,
        forall|i: int, j: int| 0 <= i < j < m.writes.len() && address(v, m.writes[i]) == address(v, m.writes[j])
            ==> #[trigger] precedes(m.writes[i], m.writes[j]) && m.ledger.stable.contains(m.writes[i]),
    ensures inv(m, v),
{ }

pub open spec fn initial() -> Media { Media { ledger: device::initial(), writes: Seq::empty() } }
pub open spec fn next(m: Media, e: Event, v: WindowView) -> Media {
    let ledger = device::next(m.ledger, e, journal_window::counts(v));
    let writes = match e { Event::Issue(_) => {
        let op = journal_window::pending_operation(ledger.io, journal_window::counts(v));
        if journal_window::is_write(op) { m.writes.push(op) } else { m.writes }
    }, _ => m.writes };
    Media { ledger, writes }
}

pub proof fn initialization(v: WindowView)
    requires journal_window::valid(v),
    ensures inv(initial(), v),
{
    journal_window::a_window_retains_its_geometry_and_bounded_counts(v);
    device::initialization(journal_window::counts(v));
    Seq::<Operation>::empty().to_set_ensures();
    assert(initial().writes.no_duplicates());
    assert(initial().writes.to_set() =~= Set::<Operation>::empty());
    assert(initial().writes.to_set() == initial().ledger.issued);
    assert(device::inv(initial().ledger, journal_window::counts(v)));
}

pub proof fn every_event_preserves(m: Media, e: Event, v: WindowView)
    requires journal_window::valid(v), inv(m, v), device::enabled(m.ledger, e, journal_window::counts(v)),
    ensures inv(next(m, e, v), v),
{
    let n = next(m, e, v);
    m.writes.to_set_ensures();
    n.writes.to_set_ensures();
    device::every_event_preserves(m.ledger, e, journal_window::counts(v));
    assert(m.ledger.stable.subset_of(n.ledger.stable));
    match e {
        Event::Issue(lane) => {
            let op = journal_window::pending_operation(n.ledger.io, journal_window::counts(v));
            if journal_window::is_write(op) {
                device::dispatch_never_reissues_a_write(m.ledger, lane, journal_window::counts(v));
                m.writes.lemma_push_to_set_commute(op);
                assert(m.writes.push(op).to_set() =~= m.writes.to_set().insert(op));
                assert forall|i: int, j: int| 0 <= i < j < n.writes.len() && address(v, n.writes[i]) == address(v, n.writes[j])
                    implies #[trigger] precedes(n.writes[i], n.writes[j]) && n.ledger.stable.contains(n.writes[i]) by {
                    if j == m.writes.len() {
                        assert(m.ledger.issued.contains(m.writes[i]));
                        dispatch_fences_every_older_write_to_the_same_address(m.ledger, lane, v, m.writes[i]);
                    } else { assert(precedes(m.writes[i], m.writes[j])); }
                }
            }
        },
        _ => {},
    }
    assert(n.writes.no_duplicates());
    assert(n.writes.to_set() == n.ledger.issued);
    assert(device::inv(n.ledger, journal_window::counts(v)));
    assert forall|i: int, j: int| 0 <= i < j < n.writes.len() && address(v, n.writes[i]) == address(v, n.writes[j])
        implies #[trigger] precedes(n.writes[i], n.writes[j]) && n.ledger.stable.contains(n.writes[i]) by {
        if j < m.writes.len() { assert(precedes(m.writes[i], m.writes[j])); }
    }
    assemble_invariant(n, v);
}

pub open spec fn targets_exist(before: Disk, v: WindowView) -> bool {
    forall|op: Operation| device::legal(op, journal_window::counts(v)) ==> #[trigger] before.dom().contains(address(v, op))
}

pub open spec fn apply(before: Disk, v: WindowView, writes: Seq<Operation>, stable: Set<Operation>, limit: nat) -> Disk
    decreases limit,
{
    if limit == 0 { before } else {
        let op = writes[limit as int - 1];
        let previous = apply(before, v, writes, stable, (limit - 1) as nat);
        if stable.contains(op) { previous.insert(address(v, op), image(v, op)) } else { previous }
    }
}
pub open spec fn disk(m: Media, before: Disk, v: WindowView) -> Disk {
    apply(before, v, m.writes, m.ledger.stable, m.writes.len())
}

proof fn absent_token_keeps_a_prefix(before: Disk, v: WindowView, writes: Seq<Operation>, stable: Set<Operation>, op: Operation, limit: nat)
    requires limit <= writes.len(), forall|i: int| 0 <= i < limit ==> #[trigger] writes[i] != op,
    ensures apply(before, v, writes, stable.insert(op), limit) == apply(before, v, writes, stable, limit),
    decreases limit,
{
    if limit > 0 { absent_token_keeps_a_prefix(before, v, writes, stable, op, (limit - 1) as nat); }
}

proof fn persisting_one_write(before: Disk, v: WindowView, writes: Seq<Operation>, stable: Set<Operation>, index: nat, limit: nat)
    requires index < limit <= writes.len(), writes.no_duplicates(), !stable.contains(writes[index as int]),
        forall|j: int| index < j < limit && stable.contains(writes[j]) ==> #[trigger] address(v, writes[j]) != address(v, writes[index as int]),
    ensures apply(before, v, writes, stable.insert(writes[index as int]), limit)
        == apply(before, v, writes, stable, limit).insert(address(v, writes[index as int]), image(v, writes[index as int])),
    decreases limit,
{
    let op = writes[index as int]; let last = limit as int - 1;
    if index == last {
        assert forall|i: int| 0 <= i < last implies #[trigger] writes[i] != op by { }
        absent_token_keeps_a_prefix(before, v, writes, stable, op, (limit - 1) as nat);
    } else {
        persisting_one_write(before, v, writes, stable, index, (limit - 1) as nat);
        if stable.contains(writes[last]) {
            let prefix = apply(before, v, writes, stable, (limit - 1) as nat);
            assert_maps_equal!(prefix.insert(address(v, op), image(v, op)).insert(address(v, writes[last]), image(v, writes[last])),
                prefix.insert(address(v, writes[last]), image(v, writes[last])).insert(address(v, op), image(v, op)), block => {});
        }
    }
}

pub proof fn each_persistence_event_changes_exactly_its_issued_block(m: Media, before: Disk, v: WindowView, op: Operation)
    requires journal_window::valid(v), inv(m, v), device::enabled(m.ledger, Event::Persist(op), journal_window::counts(v)),
    ensures disk(next(m, Event::Persist(op), v), before, v) == disk(m, before, v).insert(address(v, op), image(v, op)),
        journal_window::command_bounded(v, journal_window::expected(v, op)), image(v, op).len() == 4096,
{
    assert(m.writes.contains(op));
    let index = choose|i: int| 0 <= i < m.writes.len() && m.writes[i] == op;
    assert forall|j: int| index < j < m.writes.len() && m.ledger.stable.contains(m.writes[j])
        implies #[trigger] address(v, m.writes[j]) != address(v, op) by {
        if address(v, m.writes[j]) == address(v, op) {
            assert(precedes(m.writes[index], m.writes[j]));
            assert(m.ledger.stable.contains(m.writes[index]));
        }
    }
    persisting_one_write(before, v, m.writes, m.ledger.stable, index as nat, m.writes.len());
    journal_window::every_window_command_is_partition_bounded(v, op);
}

pub proof fn successful_completion_has_no_unstable_overwrite(m: Media, before: Disk, v: WindowView)
    requires journal_window::valid(v), inv(m, v), journal_program::finished(m.ledger.io, journal_window::counts(v)),
    ensures m.ledger.stable == m.ledger.issued,
        forall|op: Operation| !#[trigger] device::enabled(m.ledger, Event::Persist(op), journal_window::counts(v)),
{
    device::successful_completion_has_no_late_persistence(m.ledger, journal_window::counts(v));
}

proof fn last_stable_write_determines_the_bytes(before: Disk, v: WindowView, writes: Seq<Operation>, stable: Set<Operation>, index: nat, limit: nat)
    requires index < limit <= writes.len(), stable.contains(writes[index as int]),
        forall|j: int| index < j < limit && stable.contains(writes[j]) ==> #[trigger] address(v, writes[j]) != address(v, writes[index as int]),
    ensures apply(before, v, writes, stable, limit)[address(v, writes[index as int])] == image(v, writes[index as int]),
    decreases limit,
{
    if index < limit - 1 {
        last_stable_write_determines_the_bytes(before, v, writes, stable, index, (limit - 1) as nat);
        if stable.contains(writes[limit as int - 1]) { assert(address(v, writes[limit as int - 1]) != address(v, writes[index as int])); }
    }
}

pub(crate) proof fn a_stable_log_record_has_exact_bytes(m: Media, initial: Disk, v: WindowView, op: Operation)
    requires inv(m, v), is_log(op), m.ledger.stable.contains(op),
    ensures disk(m, initial, v)[address(v, op)] == image(v, op),
{
    m.writes.to_set_ensures();
    assert(m.writes.contains(op));
    let index = choose|i: int| 0 <= i < m.writes.len() && m.writes[i] == op;
    assert forall|j: int| index < j < m.writes.len() && m.ledger.stable.contains(m.writes[j])
        implies #[trigger] address(v, m.writes[j]) != address(v, op) by {
        if address(v, m.writes[j]) == address(v, op) { assert(precedes(op, m.writes[j])); }
    }
    last_stable_write_determines_the_bytes(initial, v, m.writes, m.ledger.stable, index as nat, m.writes.len());
}

pub proof fn every_acknowledged_transaction_has_exact_durable_log_bytes(m: Media, initial: Disk, v: WindowView, t: usize)
    requires journal_window::valid(v), inv(m, v), t < m.ledger.io.commit,
    ensures disk(m, initial, v)[address(v, Operation::Descriptor(t))] == v.txs[t as int].tx.descriptor,
        disk(m, initial, v)[address(v, Operation::Commit(t))] == v.txs[t as int].tx.commit,
        forall|k: usize| k < journal_window::counts(v)[t as int] ==> disk(m, initial, v)[address(v, Operation::Payload(t, k))] == (#[trigger] v.txs[t as int].tx.payloads[k as int]),
{
    let shape = journal_window::counts(v);
    device::an_acknowledged_prefix_has_durable_commit_records(m.ledger, shape);
    device::commit_issue_requires_the_complete_log_stable(m.ledger, shape, t);
    a_stable_log_record_has_exact_bytes(m, initial, v, Operation::Descriptor(t));
    a_stable_log_record_has_exact_bytes(m, initial, v, Operation::Commit(t));
    assert forall|k: usize| k < shape[t as int] implies disk(m, initial, v)[address(v, Operation::Payload(t, k))] == (#[trigger] v.txs[t as int].tx.payloads[k as int]) by {
        a_stable_log_record_has_exact_bytes(m, initial, v, Operation::Payload(t, k));
    }
}

pub proof fn completed_checkpoint_has_the_latest_exact_home_bytes(m: Media, initial: Disk, v: WindowView, t: usize, k: usize)
    requires journal_window::valid(v), inv(m, v), journal_program::finished(m.ledger.io, journal_window::counts(v)),
        device::legal(Operation::Home(t, k), journal_window::counts(v)),
        forall|u: usize, l: usize| t < u < v.txs.len() && l < journal_window::counts(v)[u as int]
            ==> (#[trigger] v.txs[u as int].tx.original[l as int]).block != v.txs[t as int].tx.original[k as int].block,
    ensures disk(m, initial, v)[v.txs[t as int].tx.original[k as int].block] == v.txs[t as int].tx.original[k as int].image,
{
    let op = Operation::Home(t, k);
    assert(m.ledger.issued.contains(op));
    device::successful_completion_has_no_late_persistence(m.ledger, journal_window::counts(v));
    m.writes.to_set_ensures();
    let index = choose|i: int| 0 <= i < m.writes.len() && m.writes[i] == op;
    assert forall|j: int| index < j < m.writes.len() && m.ledger.stable.contains(m.writes[j])
        implies #[trigger] address(v, m.writes[j]) != address(v, op) by {
        if address(v, m.writes[j]) == address(v, op) {
            assert(precedes(op, m.writes[j]));
            assert(m.ledger.issued.contains(m.writes[j]));
            match m.writes[j] {
                Operation::Home(u, l) => { assert(v.txs[u as int].tx.original[l as int].block != v.txs[t as int].tx.original[k as int].block); },
                _ => {},
            }
        }
    }
    last_stable_write_determines_the_bytes(initial, v, m.writes, m.ledger.stable, index as nat, m.writes.len());
}

pub proof fn completed_retirement_has_the_exact_clean_tail(m: Media, initial: Disk, v: WindowView)
    requires journal_window::valid(v), inv(m, v), journal_program::finished(m.ledger.io, journal_window::counts(v)),
    ensures disk(m, initial, v)[v.layout.start] == v.tails[v.txs.len() as int],
        crate::bytes::be32(disk(m, initial, v)[v.layout.start], 28) == 0,
        crate::bytes::be32(disk(m, initial, v)[v.layout.start], 24) == v.first as nat + v.txs.len(),
{
    journal_window::a_window_retains_its_geometry_and_bounded_counts(v);
    let op = Operation::Tail(v.txs.len() as usize);
    assert(m.ledger.issued.contains(op));
    device::successful_completion_has_no_late_persistence(m.ledger, journal_window::counts(v));
    m.writes.to_set_ensures();
    let index = choose|i: int| 0 <= i < m.writes.len() && m.writes[i] == op;
    assert forall|j: int| index < j < m.writes.len() && m.ledger.stable.contains(m.writes[j])
        implies #[trigger] address(v, m.writes[j]) != address(v, op) by {
        if address(v, m.writes[j]) == address(v, op) { assert(precedes(op, m.writes[j])); assert(m.ledger.issued.contains(m.writes[j])); }
    }
    last_stable_write_determines_the_bytes(initial, v, m.writes, m.ledger.stable, index as nat, m.writes.len());
    journal_window::window_header(v, v.txs.len() as int);
    reveal(journal_window::valid);
}

pub open spec fn execution(states: Seq<Media>, events: Seq<Event>, v: WindowView) -> bool {
    states.len() == events.len() + 1
        && (forall|i: int| 0 <= i < events.len() ==> #[trigger] device::enabled(states[i].ledger, events[i], journal_window::counts(v)))
        && (forall|i: int| 0 <= i < events.len() ==> states[i + 1] == #[trigger] next(states[i], events[i], v))
}

proof fn media_at_cut(states: Seq<Media>, events: Seq<Event>, v: WindowView, cut: nat)
    requires journal_window::valid(v), execution(states, events, v), inv(states[0], v), cut < states.len(),
    ensures inv(states[cut as int], v),
    decreases cut,
{
    if cut > 0 {
        media_at_cut(states, events, v, (cut - 1) as nat);
        every_event_preserves(states[cut as int - 1], events[cut as int - 1], v);
    }
}

pub proof fn every_finite_byte_persistence_interleaving_preserves_order(states: Seq<Media>, events: Seq<Event>, v: WindowView)
    requires journal_window::valid(v), execution(states, events, v), inv(states[0], v),
    ensures forall|i: int| 0 <= i < states.len() ==> #[trigger] inv(states[i], v),
{
    assert forall|i: int| 0 <= i < states.len() implies #[trigger] inv(states[i], v) by { media_at_cut(states, events, v, i as nat); }
}

pub proof fn a_flush_refines_finitely_many_issued_atomic_writes(m: Media, v: WindowView) -> (r: (Seq<Media>, Seq<Event>))
    requires journal_window::valid(v), inv(m, v), m.ledger.io.pending,
        !journal_window::is_write(journal_window::pending_operation(m.ledger.io, journal_window::counts(v))),
    ensures execution(r.0, r.1, v), r.0[0] == m, r.0.last() == next(m, Event::Complete(true), v),
        r.1.len() > 0, r.1.last() == Event::Complete(true),
        forall|i: int| 0 <= i < r.1.len() - 1 ==> (#[trigger] r.1[i]) is Persist,
        r.0[r.0.len() as int - 2].ledger.stable == r.0.last().ledger.stable,
        forall|i: int| 0 <= i < r.0.len() ==> #[trigger] inv(r.0[i], v),
{
    let (ledgers, events) = device::every_successful_flush_has_a_finite_persistence_refinement(m.ledger, journal_window::counts(v));
    let states = Seq::new(ledgers.len(), |i: int| Media { ledger: ledgers[i], writes: m.writes });
    assert forall|i: int| 0 <= i < events.len() implies #[trigger] device::enabled(states[i].ledger, events[i], journal_window::counts(v)) by {
        assert(device::enabled(ledgers[i], events[i], journal_window::counts(v)));
    }
    assert forall|i: int| 0 <= i < events.len() implies states[i + 1] == #[trigger] next(states[i], events[i], v) by {
        if i < events.len() - 1 { assert(events[i] is Persist); } else { assert(events[i] is Complete); }
        assert(ledgers[i + 1] == device::next(ledgers[i], events[i], journal_window::counts(v)));
    }
    assert(execution(states, events, v));
    every_finite_byte_persistence_interleaving_preserves_order(states, events, v);
    (states, events)
}

proof fn apply_preserves_domain(m: Media, initial: Disk, v: WindowView, limit: nat)
    requires inv(m, v), targets_exist(initial, v), limit <= m.writes.len(),
    ensures apply(initial, v, m.writes, m.ledger.stable, limit).dom() == initial.dom(),
    decreases limit,
{
    if limit > 0 {
        apply_preserves_domain(m, initial, v, (limit - 1) as nat);
        assert(m.ledger.issued.contains(m.writes[limit as int - 1]));
        assert(initial.dom().contains(address(v, m.writes[limit as int - 1])));
    }
}

pub proof fn every_media_cut_preserves_the_device_domain(m: Media, initial: Disk, v: WindowView)
    requires inv(m, v), targets_exist(initial, v),
    ensures disk(m, initial, v).dom() == initial.dom(),
{ apply_preserves_domain(m, initial, v, m.writes.len()); }

proof fn apply_frames_block(m: Media, initial: Disk, v: WindowView, block: u32, limit: nat)
    requires initial.dom().contains(block), limit <= m.writes.len(),
        forall|i: int| 0 <= i < limit && m.ledger.stable.contains(m.writes[i]) ==> #[trigger] address(v, m.writes[i]) != block,
    ensures apply(initial, v, m.writes, m.ledger.stable, limit)[block] == initial[block],
    decreases limit,
{
    if limit > 0 {
        apply_frames_block(m, initial, v, block, (limit - 1) as nat);
        if m.ledger.stable.contains(m.writes[limit as int - 1]) { assert(address(v, m.writes[limit as int - 1]) != block); }
    }
}

pub proof fn blocks_without_a_stable_write_retain_their_initial_bytes(m: Media, initial: Disk, v: WindowView, block: u32)
    requires initial.dom().contains(block), inv(m, v),
        forall|op: Operation| m.ledger.stable.contains(op) ==> #[trigger] address(v, op) != block,
    ensures disk(m, initial, v)[block] == initial[block],
{
    assert forall|i: int| 0 <= i < m.writes.len() && m.ledger.stable.contains(m.writes[i]) implies #[trigger] address(v, m.writes[i]) != block by { }
    apply_frames_block(m, initial, v, block, m.writes.len());
}

proof fn equal_prefixes_have_equal_images(initial: Disk, v: WindowView, left: Seq<Operation>, right: Seq<Operation>, stable: Set<Operation>, limit: nat)
    requires limit <= left.len(), limit <= right.len(), forall|i: int| 0 <= i < limit ==> (#[trigger] left[i]) == right[i],
    ensures apply(initial, v, left, stable, limit) == apply(initial, v, right, stable, limit),
    decreases limit,
{
    if limit > 0 { equal_prefixes_have_equal_images(initial, v, left, right, stable, (limit - 1) as nat); }
}

pub proof fn submission_abort_and_write_reports_do_not_persist_bytes(m: Media, initial: Disk, v: WindowView, e: Event)
    requires journal_window::valid(v), inv(m, v), device::enabled(m.ledger, e, journal_window::counts(v)),
        match e { Event::Issue(_) | Event::Abort | Event::Complete(false) => true,
            Event::Complete(true) => journal_window::is_write(journal_window::pending_operation(m.ledger.io, journal_window::counts(v))), _ => false },
    ensures disk(next(m, e, v), initial, v) == disk(m, initial, v),
{
    match e {
        Event::Issue(lane) => {
            let n = next(m, e, v);
            let op = journal_window::pending_operation(n.ledger.io, journal_window::counts(v));
            if journal_window::is_write(op) {
                device::dispatch_never_reissues_a_write(m.ledger, lane, journal_window::counts(v));
                equal_prefixes_have_equal_images(initial, v, n.writes, m.writes, m.ledger.stable, m.writes.len());
            }
        },
        _ => {},
    }
}

proof fn prepend_media_execution(first: Media, event: Event, states: Seq<Media>, events: Seq<Event>, v: WindowView)
    requires execution(states, events, v), device::enabled(first.ledger, event, journal_window::counts(v)), states[0] == next(first, event, v),
    ensures execution(seq![first] + states, seq![event] + events, v),
{
    let ss = seq![first] + states; let ee = seq![event] + events;
    assert forall|i: int| 0 <= i < ee.len() implies #[trigger] device::enabled(ss[i].ledger, ee[i], journal_window::counts(v)) by {
        if i > 0 { assert(device::enabled(states[i - 1].ledger, events[i - 1], journal_window::counts(v))); }
    }
    assert forall|i: int| 0 <= i < ee.len() implies ss[i + 1] == #[trigger] next(ss[i], ee[i], v) by {
        if i > 0 { assert(states[i] == next(states[i - 1], events[i - 1], v)); }
    }
}

pub proof fn a_window_has_a_finite_successful_byte_model_execution(m: Media, v: WindowView) -> (r: (Seq<Media>, Seq<Event>))
    requires journal_window::valid(v), inv(m, v), !m.ledger.io.pending, !m.ledger.io.faulted,
        m.ledger.io.request as nat + crate::journal_window_progress::remaining(m.ledger.io, journal_window::counts(v)) <= 18446744073709551615,
    ensures execution(r.0, r.1, v), r.0[0] == m,
        journal_program::finished(r.0.last().ledger.io, journal_window::counts(v)),
        r.0.last().ledger.stable == r.0.last().ledger.issued,
        r.1.len() <= 2 * crate::journal_window_progress::remaining(m.ledger.io, journal_window::counts(v)),
        !journal_program::finished(m.ledger.io, journal_window::counts(v)) ==> r.1.len() > 0,
        inv(r.0.last(), v),
    decreases crate::journal_window_progress::remaining(m.ledger.io, journal_window::counts(v)),
{
    let shape = journal_window::counts(v);
    if journal_program::finished(m.ledger.io, shape) {
        device::successful_completion_has_no_late_persistence(m.ledger, shape);
        (seq![m], Seq::empty())
    } else {
        crate::journal_window_progress::zero_work_characterizes_success(m.ledger.io, shape);
        crate::journal_window_progress::unfinished_work_has_an_enabled_lane(m.ledger.io, shape);
        let lane = crate::journal_window_progress::selected(m.ledger.io, shape);
        let issued = next(m, Event::Issue(lane), v);
        every_event_preserves(m, Event::Issue(lane), v);
        let completed = next(issued, Event::Complete(true), v);
        every_event_preserves(issued, Event::Complete(true), v);
        crate::journal_window_progress::every_successful_request_strictly_reduces_work(issued.ledger.io, shape);
        let (states, events) = a_window_has_a_finite_successful_byte_model_execution(completed, v);
        prepend_media_execution(issued, Event::Complete(true), states, events, v);
        let ss = seq![issued] + states; let ee = seq![Event::Complete(true)] + events;
        prepend_media_execution(m, Event::Issue(lane), ss, ee, v);
        assert((seq![m] + ss).last() == states.last());
        (seq![m] + ss, seq![Event::Issue(lane)] + ee)
    }
}

pub proof fn every_new_window_has_a_nonempty_successful_media_execution(v: WindowView)
    requires journal_window::valid(v),
    ensures exists|states: Seq<Media>, events: Seq<Event>| execution(states, events, v)
        && states[0] == initial() && events.len() > 0
        && journal_program::finished(states.last().ledger.io, journal_window::counts(v)) && inv(states.last(), v),
{
    initialization(v);
    crate::journal_window_progress::a_new_window_has_a_small_finite_work_bound(journal_window::counts(v));
    let (states, events) = a_window_has_a_finite_successful_byte_model_execution(initial(), v);
    assert(events.len() > 0);
}

}
