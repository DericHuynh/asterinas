// SPDX-License-Identifier: MPL-2.0

//! Resource admission for active canonical streams. These predicates bound
//! every recognized prefix and its next record, including incomplete tails.

use vstd::prelude::*;
use crate::{bytes, crc, descriptor, journal_superblock, layout::{JournalLayout, LayoutView}, revoke, scan,
    scan_trace::{self, Record, Source}};

verus! {

pub open spec fn entries(records: Seq<Record>) -> nat {
    scan_trace::writes(records).len() + scan_trace::revocations(records).len()
}

pub open spec fn target_allowed(layout: LayoutView, target: u32) -> bool {
    target < layout.fs_blocks && !(layout.start <= target < layout.start as int + layout.journal_blocks)
}

#[verifier::opaque]
pub open spec fn within_limits(source: Source) -> bool {
    &&& 1024 <= source.blocks <= 32768 && source.layout.journal_blocks == source.blocks
    &&& source.journal.len() == source.blocks as nat * 4096 && 1 <= source.start < source.blocks
    &&& 0 < source.first < 4294967295
    &&& (forall|records: Seq<Record>| #[trigger] scan_trace::well_formed(records, source) ==> {
        let end = scan_trace::end(records);
        let sequence = scan_trace::next_sequence(records, source.first);
        let raw = scan::block_at(source.journal, source.blocks, source.start, end);
        &&& entries(records) <= 4096
        &&& (end == source.blocks - 1 ==> sequence == 4294967295)
        &&& (end < source.blocks - 1 && sequence < 4294967295 ==> {
            &&& (forall|count: nat| descriptor::base(raw, source.uuid, sequence as u32, source.seed)
                && #[trigger] descriptor::candidate(raw, count, source.layout.fs_blocks) ==>
                    end as nat + 1 + count <= source.blocks - 1 && entries(records) + count <= 4096)
            &&& (revoke::header(raw, sequence as u32, source.seed)
                && revoke::targets_bounded(raw, revoke::count(raw), source.layout.fs_blocks) ==>
                entries(records) + revoke::count(raw) <= 4096
                && (forall|i: int| 0 <= i < revoke::count(raw) ==> #[trigger]
                    target_allowed(source.layout, bytes::be32(raw, 16 + 4 * i) as u32)))
        })
    })
}

pub open spec fn source(journal: Seq<u8>, uuid: Seq<u8>, layout: &JournalLayout) -> Source {
    Source { journal, blocks: layout.view().journal_blocks, start: bytes::be32(journal, 28) as u32,
        first: bytes::be32(journal, 24) as u32, uuid, seed: crc::fold(0xffffffff, uuid), layout: layout.view() }
}

#[verifier::opaque]
pub open spec fn admitted(journal: Seq<u8>, uuid: Seq<u8>, layout: &JournalLayout) -> bool {
    &&& layout.wf() && journal.len() == layout.view().journal_blocks as nat * 4096
    &&& journal_superblock::accepted(journal.subrange(0, 1024), uuid, layout.view().journal_blocks)
    &&& (bytes::be32(journal, 28) == 0 || bytes::be32(journal, 40) == 17
        && bytes::be32(journal, 24) < 4294967295 && within_limits(source(journal, uuid, layout)))
}

pub proof fn prefix_is_bounded(records: Seq<Record>, source: Source)
    requires within_limits(source), scan_trace::well_formed(records, source),
    ensures entries(records) <= 4096,
        scan_trace::end(records) == source.blocks - 1 ==> scan_trace::next_sequence(records, source.first) == 4294967295,
{
    reveal(within_limits);
}

pub proof fn next_descriptor_has_room_and_credits(records: Seq<Record>, source: Source, sequence: u32, count: nat)
    requires within_limits(source), scan_trace::well_formed(records, source),
        scan_trace::end(records) < source.blocks - 1, sequence as nat == scan_trace::next_sequence(records, source.first),
        sequence < 4294967295,
        descriptor::base(scan::block_at(source.journal, source.blocks, source.start, scan_trace::end(records)), source.uuid, sequence, source.seed),
        descriptor::candidate(scan::block_at(source.journal, source.blocks, source.start, scan_trace::end(records)), count, source.layout.fs_blocks),
    ensures scan_trace::end(records) as nat + 1 + count <= source.blocks - 1, entries(records) + count <= 4096,
{
    reveal(within_limits);
}

pub proof fn next_revoke_has_credits_and_permitted_targets(records: Seq<Record>, source: Source, sequence: u32)
    requires within_limits(source), scan_trace::well_formed(records, source),
        scan_trace::end(records) < source.blocks - 1, sequence as nat == scan_trace::next_sequence(records, source.first),
        sequence < 4294967295,
        revoke::header(scan::block_at(source.journal, source.blocks, source.start, scan_trace::end(records)), sequence, source.seed),
        revoke::targets_bounded(scan::block_at(source.journal, source.blocks, source.start, scan_trace::end(records)),
            revoke::count(scan::block_at(source.journal, source.blocks, source.start, scan_trace::end(records))), source.layout.fs_blocks),
    ensures entries(records) + revoke::count(scan::block_at(source.journal, source.blocks, source.start, scan_trace::end(records))) <= 4096,
        forall|i: int| 0 <= i < revoke::count(scan::block_at(source.journal, source.blocks, source.start, scan_trace::end(records))) ==>
            #[trigger] target_allowed(source.layout, bytes::be32(scan::block_at(source.journal, source.blocks, source.start, scan_trace::end(records)), 16 + 4 * i) as u32),
{
    reveal(within_limits);
}

}
