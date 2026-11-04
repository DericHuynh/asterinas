// SPDX-License-Identifier: MPL-2.0

//! Exact record coverage of a recognized journal prefix. Each descriptor owns
//! all of its tags and payload positions; adjacent records leave no gaps.

use vstd::prelude::*;
use crate::{bytes, descriptor, jbd2, layout::LayoutView, replay::{self, Revocation, WriteView}, revoke, scan::{self, Origin, RevokeOrigin}};

verus! {

pub struct Source {
    pub journal: Seq<u8>, pub blocks: u32, pub start: u32, pub first: u32,
    pub uuid: Seq<u8>, pub seed: u32, pub layout: LayoutView,
}

pub struct Record {
    pub start: u32, pub end: u32, pub sequence: u32, pub kind: u32,
    pub writes: Seq<WriteView>, pub revocations: Seq<Revocation>,
    pub origins: Seq<Origin>, pub revoke_origins: Seq<RevokeOrigin>,
}

#[verifier::opaque]
pub open spec fn record_ok(record: Record, source: Source) -> bool {
    let raw = scan::block_at(source.journal, source.blocks, source.start, record.start);
    &&& record.start < record.end <= source.blocks - 1 && 0 < record.sequence < 4294967295
    &&& record.writes.len() == record.origins.len() && record.revocations.len() == record.revoke_origins.len()
    &&& (if record.kind == 1 {
        &&& 1 <= record.writes.len() <= 250 && record.revocations.len() == 0
        &&& record.end as nat == record.start as nat + 1 + record.writes.len()
        &&& descriptor::base(raw, source.uuid, record.sequence, source.seed)
        &&& descriptor::candidate(raw, record.writes.len(), source.layout.fs_blocks)
        &&& (forall|i: int| 0 <= i < record.writes.len() ==>
            (#[trigger] record.writes[i]).sequence == record.sequence
            && record.origins[i].descriptor == record.start && record.origins[i].index == i
            && record.origins[i].count == record.writes.len()
            && scan::origin_ok(source.journal, source.blocks, source.start, source.uuid,
                source.seed, source.layout, record.writes[i], record.origins[i]))
    } else if record.kind == 5 {
        &&& record.writes.len() == 0 && record.revocations.len() <= 1019
        &&& record.end == record.start + 1
        &&& revoke::header(raw, record.sequence, source.seed)
        &&& record.revocations.len() == revoke::count(raw)
        &&& revoke::targets_bounded(raw, revoke::count(raw), source.layout.fs_blocks)
        &&& (forall|i: int| 0 <= i < record.revocations.len() ==>
            (#[trigger] record.revocations[i]).sequence == record.sequence
            && record.revoke_origins[i].record == record.start && record.revoke_origins[i].index == i
            && scan::revoke_origin_ok(source.journal, source.blocks, source.start, source.seed,
                record.revocations[i], record.revoke_origins[i]))
    } else {
        &&& record.kind == 2 && record.writes.len() == 0 && record.revocations.len() == 0
        &&& record.end == record.start + 1
        &&& jbd2::commit_ok(raw, record.sequence, source.seed)
    })
}

pub open spec fn end(records: Seq<Record>) -> u32 {
    if records.len() == 0 { 0 } else { records.last().end }
}

pub open spec fn next_sequence(records: Seq<Record>, first: u32) -> nat {
    if records.len() == 0 { first as nat }
    else { records.last().sequence as nat + if records.last().kind == 2 { 1nat } else { 0nat } }
}

#[verifier::opaque]
pub open spec fn writes(records: Seq<Record>) -> Seq<WriteView>
    decreases records.len(),
{
    if records.len() == 0 { Seq::empty() } else { writes(records.drop_last()) + records.last().writes }
}

#[verifier::opaque]
pub open spec fn revocations(records: Seq<Record>) -> Seq<Revocation>
    decreases records.len(),
{
    if records.len() == 0 { Seq::empty() } else { revocations(records.drop_last()) + records.last().revocations }
}

#[verifier::opaque]
pub open spec fn well_formed(records: Seq<Record>, source: Source) -> bool {
    &&& (forall|i: int| 0 <= i < records.len() ==> #[trigger] record_ok(records[i], source))
    &&& (records.len() > 0 ==> records[0].start == 0 && records[0].sequence == source.first)
    &&& (forall|i: int| 0 < i < records.len() ==>
        (#[trigger] records[i]).start == records[i - 1].end
        && records[i].sequence as nat == records[i - 1].sequence as nat
            + if records[i - 1].kind == 2 { 1nat } else { 0nat })
}

pub open spec fn committed_prefix(records: Seq<Record>, source: Source, log: Seq<WriteView>, revokes: Seq<Revocation>) -> bool {
    &&& well_formed(records, source)
    &&& (records.len() == 0 || records.last().kind == 2)
    &&& writes(records) == log && revocations(records) == revokes
}

pub proof fn append_record(records: Seq<Record>, record: Record, source: Source)
    requires well_formed(records, source), record_ok(record, source),
        record.start == end(records), record.sequence as nat == next_sequence(records, source.first),
    ensures well_formed(records.push(record), source), end(records.push(record)) == record.end,
        writes(records.push(record)) == writes(records) + record.writes,
        revocations(records.push(record)) == revocations(records) + record.revocations,
{
    reveal(well_formed);
    reveal(writes);
    reveal(revocations);
    assert(records.push(record).drop_last() =~= records);
    assert forall|i: int| 0 <= i < records.len() + 1 implies #[trigger] record_ok(records.push(record)[i], source) by {
        if i < records.len() { assert(records.push(record)[i] == records[i]); }
    }
    assert forall|i: int| 0 < i < records.len() + 1 implies
        (#[trigger] records.push(record)[i]).start == records.push(record)[i - 1].end
        && records.push(record)[i].sequence as nat == records.push(record)[i - 1].sequence as nat
            + if records.push(record)[i - 1].kind == 2 { 1nat } else { 0nat } by {
        if i < records.len() { assert(records.push(record)[i] == records[i]); }
    }
}

pub proof fn prefix_preserves_well_formedness(records: Seq<Record>, count: nat, source: Source)
    requires well_formed(records, source), count <= records.len(),
    ensures well_formed(records.take(count as int), source),
{
    reveal(well_formed);
    assert forall|i: int| 0 <= i < count implies #[trigger] record_ok(records.take(count as int)[i], source) by {
        assert(records.take(count as int)[i] == records[i]);
    }
    assert forall|i: int| 0 < i < count implies
        (#[trigger] records.take(count as int)[i]).start == records.take(count as int)[i - 1].end
        && records.take(count as int)[i].sequence as nat == records.take(count as int)[i - 1].sequence as nat
            + if records.take(count as int)[i - 1].kind == 2 { 1nat } else { 0nat } by {
        assert(records.take(count as int)[i] == records[i]);
        assert(records.take(count as int)[i - 1] == records[i - 1]);
    }
}

pub proof fn empty_records(source: Source)
    ensures well_formed(Seq::empty(), source), writes(Seq::empty()) == Seq::<WriteView>::empty(),
        revocations(Seq::empty()) == Seq::<Revocation>::empty(),
{
    reveal(well_formed);
    reveal(writes);
    reveal(revocations);
}

pub proof fn every_prefix_block_is_covered(records: Seq<Record>, source: Source, ordinal: u32)
    requires well_formed(records, source), ordinal < end(records),
    ensures exists|i: int| 0 <= i < records.len() && (#[trigger] records[i]).start <= ordinal < records[i].end,
    decreases records.len(),
{
    reveal(well_formed);
    assert(records.len() > 0);
    if ordinal >= records.last().start {
        assert(records[records.len() as int - 1].start <= ordinal < records[records.len() as int - 1].end);
    } else {
        assert(records.len() > 1);
        assert(ordinal < end(records.drop_last()));
        assert(records.drop_last() =~= records.take(records.len() as int - 1));
        prefix_preserves_well_formedness(records, (records.len() - 1) as nat, source);
        every_prefix_block_is_covered(records.drop_last(), source, ordinal);
        let i = choose|i: int| 0 <= i < records.drop_last().len()
            && (#[trigger] records.drop_last()[i]).start <= ordinal < records.drop_last()[i].end;
        assert(records[i] == records.drop_last()[i]);
    }
}

pub proof fn distinct_record_ranges_do_not_overlap(records: Seq<Record>, source: Source, i: int, j: int)
    requires well_formed(records, source), 0 <= i < j < records.len(),
    ensures records[i].end <= records[j].start,
    decreases j - i,
{
    reveal(well_formed);
    if i + 1 < j {
        distinct_record_ranges_do_not_overlap(records, source, i, j - 1);
        assert(record_ok(records[j - 1], source));
        reveal(record_ok);
    }
}

pub open spec fn descriptor_write(record: Record, source: Source, i: int) -> WriteView {
    let raw = scan::block_at(source.journal, source.blocks, source.start, record.start);
    let payload = scan::block_at(source.journal, source.blocks, source.start, (record.start as int + 1 + i) as u32);
    let flags = bytes::be32(raw, descriptor::offset(i) + 4) as u32;
    WriteView { block: bytes::be32(raw, descriptor::offset(i)) as u32, sequence: record.sequence,
        image: replay::restored(payload, flags % 2 == 1) }
}

pub proof fn every_descriptor_tag_is_represented(record: Record, source: Source, declared: nat)
    requires record_ok(record, source), record.kind == 1,
        descriptor::candidate(scan::block_at(source.journal, source.blocks, source.start, record.start),
            declared, source.layout.fs_blocks),
    ensures record.writes.len() == declared,
        forall|i: int| 0 <= i < declared ==> (#[trigger] record.writes[i]) == descriptor_write(record, source, i),
{
    reveal(record_ok);
    let raw = scan::block_at(source.journal, source.blocks, source.start, record.start);
    descriptor::descriptor_length_is_unique(raw, record.writes.len(), declared, source.layout.fs_blocks);
    assert forall|i: int| 0 <= i < declared implies
        (#[trigger] record.writes[i]) == descriptor_write(record, source, i) by {
        assert(scan::origin_ok(source.journal, source.blocks, source.start, source.uuid, source.seed,
            source.layout, record.writes[i], record.origins[i]));
        reveal(scan::origin_ok);
    }
}

pub proof fn decoding_one_record_is_deterministic(a: Record, b: Record, source: Source)
    requires record_ok(a, source), record_ok(b, source), a.start == b.start, a.sequence == b.sequence,
    ensures a == b,
{
    reveal(record_ok);
    let raw = scan::block_at(source.journal, source.blocks, source.start, a.start);
    assert(a.kind == b.kind);
    if a.kind == 1 {
        every_descriptor_tag_is_represented(a, source, a.writes.len());
        every_descriptor_tag_is_represented(b, source, a.writes.len());
        assert(a.writes =~= b.writes) by {
            assert forall|i: int| 0 <= i < a.writes.len() implies #[trigger] a.writes[i] == b.writes[i] by {
                assert(a.writes[i] == descriptor_write(a, source, i));
                assert(b.writes[i] == descriptor_write(b, source, i));
            }
        }
        assert(a.origins =~= b.origins) by {
            assert forall|i: int| 0 <= i < a.origins.len() implies #[trigger] a.origins[i] == b.origins[i] by {
                assert(scan::origin_ok(source.journal, source.blocks, source.start, source.uuid, source.seed,
                    source.layout, a.writes[i], a.origins[i]));
                assert(scan::origin_ok(source.journal, source.blocks, source.start, source.uuid, source.seed,
                    source.layout, b.writes[i], b.origins[i]));
                reveal(scan::origin_ok);
            }
        }
    } else if a.kind == 5 {
        assert(a.revocations =~= b.revocations) by {
            assert forall|i: int| 0 <= i < a.revocations.len() implies #[trigger] a.revocations[i] == b.revocations[i] by {
                assert(scan::revoke_origin_ok(source.journal, source.blocks, source.start, source.seed,
                    a.revocations[i], a.revoke_origins[i]));
                assert(scan::revoke_origin_ok(source.journal, source.blocks, source.start, source.seed,
                    b.revocations[i], b.revoke_origins[i]));
                reveal(scan::revoke_origin_ok);
            }
        }
        assert(a.revoke_origins =~= b.revoke_origins) by {
            assert forall|i: int| 0 <= i < a.revoke_origins.len() implies #[trigger] a.revoke_origins[i] == b.revoke_origins[i] by {
                assert(a.revocations[i].sequence == a.sequence);
                assert(b.revocations[i].sequence == b.sequence);
                assert(a.revoke_origins[i].record == a.start && a.revoke_origins[i].index == i);
                assert(b.revoke_origins[i].record == b.start && b.revoke_origins[i].index == i);
            }
        }
    }
    assert(a.revocations =~= b.revocations);
    assert(a.revoke_origins =~= b.revoke_origins);
    assert(a.writes =~= b.writes);
    assert(a.origins =~= b.origins);
}

pub proof fn well_formed_prefixes_agree_at_every_common_position(a: Seq<Record>, b: Seq<Record>, source: Source, i: nat)
    requires well_formed(a, source), well_formed(b, source), i < a.len(), i < b.len(),
    ensures a[i as int] == b[i as int],
    decreases i,
{
    reveal(well_formed);
    if i > 0 { well_formed_prefixes_agree_at_every_common_position(a, b, source, (i - 1) as nat); }
    decoding_one_record_is_deterministic(a[i as int], b[i as int], source);
}

}
