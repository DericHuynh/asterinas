// SPDX-License-Identifier: MPL-2.0

//! Shape and resource bounds of arbitrary recognized prefixes of a reserved
//! multi-transaction JBD2 window, including an uncommitted descriptor suffix.

use vstd::prelude::*;
use crate::{bytes, crc, descriptor, jbd2, journal_window::{self as window, WindowView},
    revoke, scan, scan_budget, scan_trace::{self, Record, Source}};

verus! {

pub open spec fn credits(v: WindowView, prefix: nat) -> nat { window::entries(v.txs.take(prefix as int)) }
pub open spec fn boundary(v: WindowView, prefix: nat) -> nat { 1 + credits(v, prefix) + 2 * prefix }
pub open spec fn offset(v: WindowView, first: nat, tx: nat) -> u32 { (boundary(v, tx) as int - boundary(v, first)) as u32 }

pub(crate) proof fn credit_step(v: WindowView, prefix: nat)
    requires prefix < v.txs.len(),
    ensures credits(v, prefix + 1) == credits(v, prefix) + window::counts(v)[prefix as int],
{
    assert(v.txs.take(prefix as int + 1) =~= v.txs.take(prefix as int).push(v.txs[prefix as int]));
    window::entries_push(v.txs.take(prefix as int), v.txs[prefix as int]);
}

proof fn credit_monotone(v: WindowView, a: nat, b: nat)
    requires a <= b <= v.txs.len(),
    ensures credits(v, a) <= credits(v, b),
    decreases b - a,
{
    if a < b { credit_monotone(v, a, (b - 1) as nat); credit_step(v, (b - 1) as nat); }
}

pub proof fn reserved_boundaries_match_the_exact_payload_prefixes(v: WindowView, prefix: nat)
    requires window::valid(v), prefix <= v.txs.len(),
    ensures 1 <= boundary(v, prefix) < v.layout.journal_blocks,
        credits(v, prefix) <= window::entries(v.txs) <= 4096,
        prefix < v.txs.len() ==> boundary(v, prefix) == v.txs[prefix as int].source.first,
        prefix == v.txs.len() ==> boundary(v, prefix) == v.txs.last().source.first as nat + v.txs.last().source.blocks,
    decreases prefix,
{
    hide(crc::fold);
    window::a_window_retains_its_geometry_and_bounded_counts(v);
    assert(v.txs.take(v.txs.len() as int) =~= v.txs);
    credit_monotone(v, prefix, v.txs.len());
    if prefix == 0 {
        assert(v.txs.take(0) =~= Seq::empty());
        assert(credits(v, 0) == 0) by { reveal(window::entries); }
        window::window_entry(v, 0);
        reveal(window::positioned_valid);
    } else {
        reserved_boundaries_match_the_exact_payload_prefixes(v, (prefix - 1) as nat);
        credit_step(v, (prefix - 1) as nat);
        window::window_entry(v, prefix as int - 1);
        reveal(window::positioned_valid);
        if prefix < v.txs.len() { window::window_entry(v, prefix as int); }
    }
}

pub(crate) proof fn offset_bounds(v: WindowView, first: nat, tx: nat)
    requires window::valid(v), first <= tx <= v.txs.len(),
    ensures offset(v, first, tx) as nat == boundary(v, tx) - boundary(v, first),
        boundary(v, first) + offset(v, first, tx) == boundary(v, tx),
        offset(v, first, tx) < v.layout.journal_blocks - 1,
{
    reserved_boundaries_match_the_exact_payload_prefixes(v, first);
    reserved_boundaries_match_the_exact_payload_prefixes(v, tx);
    credit_monotone(v, first, tx);
}

pub open spec fn fields(v: WindowView, s: Source, first: nat) -> bool {
    &&& first < v.txs.len() && s.layout == v.layout && s.blocks == v.layout.journal_blocks
    &&& s.start as nat == boundary(v, first) && s.first as nat == v.first as nat + first
    &&& s.uuid == v.uuid && s.seed == crc::fold(0xffffffff, v.uuid)
    &&& s.journal.len() == s.blocks as nat * 4096
}

pub open spec fn metadata(v: WindowView, s: Source, first: nat, ordinal: u32, sequence: u32, t: nat) -> bool {
    let raw = scan::block_at(s.journal, s.blocks, s.start, ordinal);
    &&& first <= t < v.txs.len() && sequence as nat == v.first as nat + t
    &&& (ordinal == offset(v, first, t) && raw == v.txs[t as int].tx.descriptor
        || ordinal as nat == offset(v, first, t) as nat + window::counts(v)[t as int] + 1 && raw == v.txs[t as int].tx.commit)
}

#[verifier::opaque]
pub open spec fn shaped(v: WindowView, s: Source, first: nat) -> bool {
    &&& window::valid(v) && fields(v, s, first)
    &&& (forall|ordinal: u32, sequence: u32| ordinal < s.blocks - 1 && s.first <= sequence
        && #[trigger] jbd2::header_ok(scan::block_at(s.journal, s.blocks, s.start, ordinal), sequence)
        ==> exists|t: nat| metadata(v, s, first, ordinal, sequence, t))
}

pub(crate) proof fn metadata_fields(v: WindowView, t: nat)
    requires window::valid(v), t < v.txs.len(),
    ensures v.txs[t as int].tx.layout == v.layout,
        v.txs[t as int].tx.original.len() == v.txs[t as int].tx.tags.len() == v.txs[t as int].tx.payloads.len(),
        0 < window::counts(v)[t as int] <= 250,
        descriptor::base(v.txs[t as int].tx.descriptor, v.uuid, v.txs[t as int].tx.sequence, v.txs[t as int].tx.seed),
        descriptor::candidate(v.txs[t as int].tx.descriptor, v.txs[t as int].tx.tags.len(), v.layout.fs_blocks),
        bytes::be32(v.txs[t as int].tx.descriptor, 4) == 1,
        bytes::be32(v.txs[t as int].tx.commit, 4) == 2,
        v.txs[t as int].tx.sequence as nat == v.first as nat + t,
{
    hide(crc::fold);
    window::window_entry(v, t as int);
    reveal(window::positioned_valid);
}

pub(crate) proof fn record_header(record: Record, s: Source)
    requires scan_trace::record_ok(record, s),
    ensures record.start < record.end <= s.blocks - 1,
        jbd2::header_ok(scan::block_at(s.journal, s.blocks, s.start, record.start), record.sequence),
        bytes::be32(scan::block_at(s.journal, s.blocks, s.start, record.start), 4) == record.kind,
        record.kind == 1 ==> descriptor::candidate(scan::block_at(s.journal, s.blocks, s.start, record.start), record.writes.len(), s.layout.fs_blocks)
            && record.end as nat == record.start as nat + 1 + record.writes.len() && record.revocations.len() == 0,
        record.kind == 2 ==> record.end == record.start + 1 && record.writes.len() == 0 && record.revocations.len() == 0,
{ reveal(scan_trace::record_ok); }

pub open spec fn cursor(v: WindowView, first: nat, t: nat, payload: bool) -> nat {
    offset(v, first, t) as nat + if payload { window::counts(v)[t as int] + 1 } else { 0nat }
}

proof fn one_record_at_a_cursor(v: WindowView, s: Source, first: nat, t: nat, payload: bool, r: Record)
    requires shaped(v, s, first), first <= t <= v.txs.len(), payload ==> t < v.txs.len(),
        scan_trace::record_ok(r, s), r.start as nat == cursor(v, first, t, payload), r.sequence as nat == v.first as nat + t,
    ensures t < v.txs.len(), r.kind == if payload { 2u32 } else { 1u32 },
        r.writes.len() == if payload { 0nat } else { window::counts(v)[t as int] }, r.revocations.len() == 0,
        r.end as nat == if payload { offset(v, first, t + 1) as nat }
            else { offset(v, first, t) as nat + window::counts(v)[t as int] + 1 },
{
    hide(crc::fold);
    hide(descriptor::candidate);
    reveal(shaped);
    record_header(r, s);
    assert(exists|u: nat| metadata(v, s, first, r.start, r.sequence, u));
    let u = choose|u: nat| metadata(v, s, first, r.start, r.sequence, u);
    assert(u == t);
    metadata_fields(v, t);
    let tx = v.txs[t as int].tx;
    offset_bounds(v, first, t);
    offset_bounds(v, first, t + 1);
    credit_step(v, t);
    if !payload {
        descriptor::descriptor_length_is_unique(tx.descriptor, r.writes.len(), tx.tags.len(), v.layout.fs_blocks);
    }
}

#[verifier::opaque]
pub open spec fn record_shape(v: WindowView, first: nat, index: int, r: Record) -> bool {
    let t = first + (index / 2) as nat;
    let payload = index % 2 == 1;
    &&& t < v.txs.len() && r.sequence as nat == v.first as nat + t
    &&& r.kind == if payload { 2u32 } else { 1u32 }
    &&& r.start as nat == cursor(v, first, t, payload)
    &&& r.end as nat == if payload { offset(v, first, t + 1) as nat }
        else { offset(v, first, t) as nat + window::counts(v)[t as int] + 1 }
    &&& r.writes.len() == if payload { 0nat } else { window::counts(v)[t as int] }
    &&& r.revocations.len() == 0
}

pub(crate) proof fn record_facts(v: WindowView, first: nat, index: int, r: Record)
    requires record_shape(v, first, index, r),
    ensures (first + (index / 2) as nat) < v.txs.len(), r.sequence as nat == v.first as nat + first + (index / 2) as nat,
        r.kind == if index % 2 == 1 { 2u32 } else { 1u32 },
        r.writes.len() == if index % 2 == 1 { 0nat } else { window::counts(v)[(first + (index / 2) as nat) as int] }, r.revocations.len() == 0,
{ reveal(record_shape); }

proof fn assemble_record_shape(v: WindowView, first: nat, index: int, r: Record)
    requires 0 <= index, (first + (index / 2) as nat) < v.txs.len(),
        r.sequence as nat == v.first as nat + first + (index / 2) as nat,
        r.kind == if index % 2 == 1 { 2u32 } else { 1u32 },
        r.start as nat == cursor(v, first, first + (index / 2) as nat, index % 2 == 1),
        r.end as nat == if index % 2 == 1 { offset(v, first, first + (index / 2) as nat + 1) as nat }
            else { offset(v, first, first + (index / 2) as nat) as nat + window::counts(v)[(first + (index / 2) as nat) as int] + 1 },
        r.writes.len() == if index % 2 == 1 { 0nat } else { window::counts(v)[(first + (index / 2) as nat) as int] }, r.revocations.len() == 0,
    ensures record_shape(v, first, index, r),
{ reveal(record_shape); }

pub proof fn every_recognized_prefix_has_the_reserved_transaction_shape(v: WindowView, s: Source, first: nat, records: Seq<Record>)
    requires shaped(v, s, first), scan_trace::well_formed(records, s),
    ensures records.len() <= 2 * (v.txs.len() - first),
        forall|i: int| 0 <= i < records.len() ==> #[trigger] record_shape(v, first, i, records[i]),
        scan_trace::next_sequence(records, s.first) == v.first as nat + first + records.len() / 2,
        scan_trace::end(records) as nat == cursor(v, first, first + records.len() / 2, records.len() % 2 == 1),
    decreases records.len(),
{
    hide(crc::fold);
    reveal(shaped);
    reveal(scan_trace::well_formed);
    if records.len() == 0 {
        offset_bounds(v, first, first);
    } else {
        let prev = records.drop_last();
        assert(prev =~= records.take(records.len() as int - 1));
        scan_trace::prefix_preserves_well_formedness(records, (records.len() - 1) as nat, s);
        every_recognized_prefix_has_the_reserved_transaction_shape(v, s, first, prev);
        let n = prev.len();
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, 2);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int + 1, 2);
        let t = first + n / 2;
        let payload = n % 2 == 1;
        assert(records.last().sequence as nat == v.first as nat + t);
        assert(records.last().start as nat == cursor(v, first, t, payload));
        one_record_at_a_cursor(v, s, first, t, payload, records.last());
        assemble_record_shape(v, first, n as int, records.last());
        assert(record_shape(v, first, n as int, records.last()));
        assert forall|i: int| 0 <= i < records.len() implies #[trigger] record_shape(v, first, i, records[i]) by {
            if i < n { assert(record_shape(v, first, i, prev[i])); }
        }
        if !payload {
            assert((n + 1) / 2 == n / 2 && (n + 1) % 2 == 1);
        } else {
            assert((n + 1) / 2 == n / 2 + 1 && (n + 1) % 2 == 0);
        }
    }
}

pub proof fn recognized_entries_are_the_exact_reserved_payload_prefix(v: WindowView, s: Source, first: nat, records: Seq<Record>)
    requires shaped(v, s, first), scan_trace::well_formed(records, s),
    ensures scan_budget::entries(records) == credits(v, first + (records.len() + 1) / 2) - credits(v, first),
        scan_budget::entries(records) <= 4096,
    decreases records.len(),
{
    hide(crc::fold);
    reveal(shaped);
    every_recognized_prefix_has_the_reserved_transaction_shape(v, s, first, records);
    if records.len() == 0 { reveal(scan_trace::writes); reveal(scan_trace::revocations); }
    else {
        let prev = records.drop_last();
        assert(prev =~= records.take(records.len() as int - 1));
        scan_trace::prefix_preserves_well_formedness(records, (records.len() - 1) as nat, s);
        recognized_entries_are_the_exact_reserved_payload_prefix(v, s, first, prev);
        assert(record_shape(v, first, prev.len() as int, records.last()));
        record_facts(v, first, prev.len() as int, records.last());
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(prev.len() as int, 2);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(prev.len() as int + 1, 2);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(prev.len() as int + 2, 2);
        if prev.len() % 2 == 0 { credit_step(v, first + prev.len() / 2); }
        reveal(scan_trace::writes); reveal(scan_trace::revocations);
    }
    assert(first + (records.len() + 1) / 2 <= v.txs.len());
    reserved_boundaries_match_the_exact_payload_prefixes(v, first + (records.len() + 1) / 2);
}


proof fn prefix_end_is_in_bounds(v: WindowView, s: Source, first: nat, records: Seq<Record>)
    requires shaped(v, s, first), scan_trace::well_formed(records, s),
    ensures scan_trace::end(records) < s.blocks - 1,
{
    reveal(shaped);
    every_recognized_prefix_has_the_reserved_transaction_shape(v, s, first, records);
    let t = first + records.len() / 2;
    offset_bounds(v, first, t);
    if records.len() % 2 == 1 { credit_step(v, t); offset_bounds(v, first, t + 1); }
}

proof fn next_descriptor_budget(v: WindowView, s: Source, first: nat, records: Seq<Record>, count: nat)
    requires shaped(v, s, first), scan_trace::well_formed(records, s),
        scan_trace::next_sequence(records, s.first) < 4294967295,
        descriptor::base(scan::block_at(s.journal, s.blocks, s.start, scan_trace::end(records)), s.uuid,
            scan_trace::next_sequence(records, s.first) as u32, s.seed),
        descriptor::candidate(scan::block_at(s.journal, s.blocks, s.start, scan_trace::end(records)), count, s.layout.fs_blocks),
    ensures scan_trace::end(records) as nat + 1 + count <= s.blocks - 1, scan_budget::entries(records) + count <= 4096,
{
    hide(crc::fold);
    hide(descriptor::candidate);
    reveal(shaped);
    every_recognized_prefix_has_the_reserved_transaction_shape(v, s, first, records);
    recognized_entries_are_the_exact_reserved_payload_prefix(v, s, first, records);
    prefix_end_is_in_bounds(v, s, first, records);
    let end = scan_trace::end(records);
    let sequence = scan_trace::next_sequence(records, s.first);
    let raw = scan::block_at(s.journal, s.blocks, s.start, end);
    let t = first + records.len() / 2;
    assert(jbd2::header_ok(raw, sequence as u32));
    let u = choose|u: nat| #[trigger] metadata(v, s, first, end, sequence as u32, u);
    assert(u == t && t < v.txs.len());
    metadata_fields(v, t);
    assert(raw == v.txs[t as int].tx.descriptor);
    assert(records.len() % 2 == 0);
    descriptor::descriptor_length_is_unique(raw, count, v.txs[t as int].tx.tags.len(), s.layout.fs_blocks);
    credit_step(v, t);
    offset_bounds(v, first, t + 1);
    reserved_boundaries_match_the_exact_payload_prefixes(v, t + 1);
}

proof fn no_revoke_header(v: WindowView, s: Source, first: nat, ordinal: u32, sequence: u32)
    requires shaped(v, s, first), ordinal < s.blocks - 1, s.first <= sequence,
    ensures !revoke::header(scan::block_at(s.journal, s.blocks, s.start, ordinal), sequence, s.seed),
{
    hide(crc::fold);
    reveal(shaped);
    let raw = scan::block_at(s.journal, s.blocks, s.start, ordinal);
    if revoke::header(raw, sequence, s.seed) {
        assert(jbd2::header_ok(raw, sequence));
        let u = choose|u: nat| #[trigger] metadata(v, s, first, ordinal, sequence, u);
        metadata_fields(v, u);
    }
}

pub proof fn every_shaped_window_is_admitted_by_the_actual_scanner(v: WindowView, s: Source, first: nat)
    requires shaped(v, s, first),
    ensures scan_budget::within_limits(s),
{
    hide(crc::fold);
    hide(descriptor::candidate);
    hide(descriptor::base);
    reveal(shaped);
    reserved_boundaries_match_the_exact_payload_prefixes(v, first);
    window::window_entry(v, first as int);
    reveal(window::positioned_valid);
    reveal(scan_budget::within_limits);
    assert forall|records: Seq<Record>| #[trigger] scan_trace::well_formed(records, s) implies {
        let end = scan_trace::end(records);
        let sequence = scan_trace::next_sequence(records, s.first);
        let raw = scan::block_at(s.journal, s.blocks, s.start, end);
        &&& scan_budget::entries(records) <= 4096
        &&& (end == s.blocks - 1 ==> sequence == 4294967295)
        &&& (end < s.blocks - 1 && sequence < 4294967295 ==> {
            &&& (forall|count: nat| descriptor::base(raw, s.uuid, sequence as u32, s.seed)
                && #[trigger] descriptor::candidate(raw, count, s.layout.fs_blocks) ==>
                    end as nat + 1 + count <= s.blocks - 1 && scan_budget::entries(records) + count <= 4096)
            &&& (revoke::header(raw, sequence as u32, s.seed) && revoke::targets_bounded(raw, revoke::count(raw), s.layout.fs_blocks) ==>
                scan_budget::entries(records) + revoke::count(raw) <= 4096
                && (forall|i: int| 0 <= i < revoke::count(raw) ==> #[trigger]
                    scan_budget::target_allowed(s.layout, bytes::be32(raw, 16 + 4 * i) as u32)))
        })
    } by {
        every_recognized_prefix_has_the_reserved_transaction_shape(v, s, first, records);
        recognized_entries_are_the_exact_reserved_payload_prefix(v, s, first, records);
        prefix_end_is_in_bounds(v, s, first, records);
        let end = scan_trace::end(records);
        let sequence = scan_trace::next_sequence(records, s.first);
        let raw = scan::block_at(s.journal, s.blocks, s.start, end);
        if sequence < 4294967295 {
            assert forall|count: nat| descriptor::base(raw, s.uuid, sequence as u32, s.seed)
                && #[trigger] descriptor::candidate(raw, count, s.layout.fs_blocks) implies
                end as nat + 1 + count <= s.blocks - 1 && scan_budget::entries(records) + count <= 4096 by {
                next_descriptor_budget(v, s, first, records, count);
            }
            no_revoke_header(v, s, first, end, sequence as u32);
        }
    }
}

}
