// SPDX-License-Identifier: MPL-2.0

//! An exact reason for terminating the canonical journal record prefix.
//! A checksum failure is a failed recognition predicate, not authentication.

use vstd::prelude::*;
use crate::{bytes, descriptor, jbd2, replay, revoke, scan, scan_trace::{self, Record, Source}};

verus! {

pub enum Stop {
    Clean,
    Header { ordinal: u32 },
    Descriptor { ordinal: u32 },
    Revoke { ordinal: u32 },
    Commit { ordinal: u32 },
    Payload { ordinal: u32, count: nat, index: nat, tag: jbd2::Tag },
    Exhausted,
}

#[verifier::opaque]
pub open spec fn at_boundary(stop: Stop, records: Seq<Record>, source: Source, sequence: u32) -> bool {
    let ordinal = scan_trace::end(records);
    let raw = scan::block_at(source.journal, source.blocks, source.start, ordinal);
    &&& (match stop {
        Stop::Clean => source.start == 0 && records.len() == 0 && sequence == source.first,
        Stop::Exhausted => sequence == 4294967295,
        Stop::Header { ordinal: p } => p == ordinal && p < source.blocks - 1 && !jbd2::header_ok(raw, sequence),
        Stop::Descriptor { ordinal: p } => p == ordinal && p < source.blocks - 1
            && bytes::be32(raw, 4) == 1
            && (!descriptor::base(raw, source.uuid, sequence, source.seed)
                || !(exists|n: nat| #[trigger] descriptor::candidate(raw, n, source.layout.fs_blocks))),
        Stop::Revoke { ordinal: p } => p == ordinal && p < source.blocks - 1
            && bytes::be32(raw, 4) == 5
            && (!revoke::header(raw, sequence, source.seed)
                || !revoke::targets_bounded(raw, revoke::count(raw), source.layout.fs_blocks)),
        Stop::Commit { ordinal: p } => p == ordinal && p < source.blocks - 1
            && bytes::be32(raw, 4) == 2 && !jbd2::commit_ok(raw, sequence, source.seed),
        Stop::Payload { ordinal: p, count, index, tag } => {
            let payload = scan::block_at(source.journal, source.blocks, source.start, (p as int + 1 + index) as u32);
            &&& p == ordinal && index < count <= 250 && p as int + 1 + index < source.blocks - 1
            &&& descriptor::base(raw, source.uuid, sequence, source.seed)
            &&& descriptor::candidate(raw, count, source.layout.fs_blocks)
            &&& tag.block as nat == bytes::be32(raw, descriptor::offset(index as int))
            &&& tag.flags as nat == bytes::be32(raw, descriptor::offset(index as int) + 4)
            &&& tag.checksum as nat == bytes::be32(raw, descriptor::offset(index as int) + 12)
            &&& !replay::payload_for_layout(tag, payload, sequence, source.seed, source.layout)
        },
    })
}

pub proof fn a_stopped_prefix_has_no_further_valid_record(stop: Stop, records: Seq<Record>, source: Source,
    sequence: u32, record: Record)
    requires at_boundary(stop, records, source, sequence), !(stop is Clean),
        record.start == scan_trace::end(records), record.sequence == sequence,
    ensures !scan_trace::record_ok(record, source),
{
    reveal(at_boundary);
    if scan_trace::record_ok(record, source) {
        reveal(scan_trace::record_ok);
        let raw = scan::block_at(source.journal, source.blocks, source.start, record.start);
        match stop {
            Stop::Payload { ordinal, count, index, tag } => {
                assert(record.kind == 1);
                scan_trace::every_descriptor_tag_is_represented(record, source, count);
                assert(scan::origin_ok(source.journal, source.blocks, source.start, source.uuid, source.seed,
                    source.layout, record.writes[index as int], record.origins[index as int]));
                reveal(scan::origin_ok);
                assert(record.origins[index as int].payload as int == ordinal as int + 1 + index);
                let decoded = jbd2::Tag { block: bytes::be32(raw, descriptor::offset(index as int)) as u32,
                    flags: bytes::be32(raw, descriptor::offset(index as int) + 4) as u32,
                    checksum: bytes::be32(raw, descriptor::offset(index as int) + 12) as u32 };
                assert(tag == decoded);
                assert(false);
            },
            Stop::Header { .. } => { assert(false); },
            Stop::Descriptor { .. } => {
                assert(record.kind == 1);
                assert(descriptor::candidate(raw, record.writes.len(), source.layout.fs_blocks));
                assert(exists|n: nat| #[trigger] descriptor::candidate(raw, n, source.layout.fs_blocks));
                assert(false);
            },
            Stop::Revoke { .. } => { assert(false); },
            Stop::Commit { .. } => { assert(false); },
            Stop::Clean => { assert(false); },
            Stop::Exhausted => { assert(false); },
        }
    }
}

pub proof fn maximal_canonical_prefix_is_unique(a: Seq<Record>, b: Seq<Record>, sa: Stop, sb: Stop,
    source: Source, na: u32, nb: u32)
    requires scan_trace::well_formed(a, source), scan_trace::well_formed(b, source), source.start != 0,
        na as nat == scan_trace::next_sequence(a, source.first), nb as nat == scan_trace::next_sequence(b, source.first),
        at_boundary(sa, a, source, na), at_boundary(sb, b, source, nb),
    ensures a == b, na == nb,
{
    reveal(at_boundary);
    if a.len() < b.len() {
        reveal(scan_trace::well_formed);
        let i = a.len() as int;
        if i > 0 { scan_trace::well_formed_prefixes_agree_at_every_common_position(a, b, source, (i - 1) as nat); }
        assert(b[i].start == scan_trace::end(a) && b[i].sequence == na);
        a_stopped_prefix_has_no_further_valid_record(sa, a, source, na, b[i]);
    } else if b.len() < a.len() {
        reveal(scan_trace::well_formed);
        let i = b.len() as int;
        if i > 0 { scan_trace::well_formed_prefixes_agree_at_every_common_position(a, b, source, (i - 1) as nat); }
        assert(a[i].start == scan_trace::end(b) && a[i].sequence == nb);
        a_stopped_prefix_has_no_further_valid_record(sb, b, source, nb, a[i]);
    }
    assert(a =~= b) by {
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i] == b[i] by {
            scan_trace::well_formed_prefixes_agree_at_every_common_position(a, b, source, i as nat);
        }
    }
}

pub proof fn every_recognized_prefix_is_a_prefix_of_a_stopped_stream(prefix: Seq<Record>, stopped: Seq<Record>,
    stop: Stop, source: Source, next: u32)
    requires scan_trace::well_formed(prefix, source), scan_trace::well_formed(stopped, source),
        !(stop is Clean), at_boundary(stop, stopped, source, next),
        next as nat == scan_trace::next_sequence(stopped, source.first),
    ensures prefix.len() <= stopped.len(), stopped.take(prefix.len() as int) == prefix,
{
    if prefix.len() > stopped.len() {
        reveal(scan_trace::well_formed);
        let i = stopped.len() as int;
        if i > 0 {
            scan_trace::well_formed_prefixes_agree_at_every_common_position(prefix, stopped, source, (i - 1) as nat);
        }
        assert(prefix[i].start == scan_trace::end(stopped) && prefix[i].sequence == next);
        a_stopped_prefix_has_no_further_valid_record(stop, stopped, source, next, prefix[i]);
    }
    assert(stopped.take(prefix.len() as int) =~= prefix) by {
        assert forall|i: int| 0 <= i < prefix.len() implies #[trigger] prefix[i] == stopped[i] by {
            scan_trace::well_formed_prefixes_agree_at_every_common_position(prefix, stopped, source, i as nat);
        }
    }
}

}
