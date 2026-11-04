// SPDX-License-Identifier: MPL-2.0

//! A sufficient recovery preparation profile. A committed stream's block-zero
//! writes must preserve the checked primary superblock's immutable fields.
//! This local check does not authorize the recovered filesystem namespace.

use vstd::prelude::*;
use crate::{bytes, crc, layout::JournalLayout, replay, scan, scan_budget,
    scan_trace::{self, Record, Source}, super_state, superblock};

verus! {

#[verifier::opaque]
pub open spec fn safe_committed_streams(source: Source, primary: Seq<u8>, partition_bytes: u64) -> bool {
    forall|records: Seq<Record>| #[trigger] scan_trace::well_formed(records, source)
        && (records.len() == 0 || records.last().kind == 2) ==>
        (forall|i: int| 0 <= i < scan_trace::writes(records).len()
            && (#[trigger] scan_trace::writes(records)[i]).block == 0 ==>
                super_state::replay_ok(primary, scan_trace::writes(records)[i].image, partition_bytes))
}

#[verifier::opaque]
pub open spec fn input_ok(journal: Seq<u8>, uuid: Seq<u8>, layout: &JournalLayout,
    primary: Seq<u8>, partition_bytes: u64) -> bool {
    &&& scan_budget::admitted(journal, uuid, layout)
    &&& primary.len() == 4096 && superblock::accepted(primary.subrange(1024, 2048), partition_bytes)
    &&& bytes::le32(primary, 1028) == layout.view().fs_blocks
    &&& (bytes::be32(journal, 28) != 0 ==> super_state::is_dirty(primary)
        && safe_committed_streams(scan_budget::source(journal, uuid, layout), primary, partition_bytes))
}

pub proof fn selected_superblock_targets_satisfy_the_replay_policy(journal: Seq<u8>, uuid: Seq<u8>, layout: &JournalLayout,
    primary: Seq<u8>, partition_bytes: u64, result: &scan::Scan)
    requires input_ok(journal, uuid, layout, primary, partition_bytes),
        result.plan().refines(), result.certificate(scan_budget::source(journal, uuid, layout)),
        bytes::be32(journal, 28) == 0 ==> result.plan().selection().len() == 0,
    ensures forall|p: int| 0 <= p < result.plan().selection().len()
        && (#[trigger] result.plan().log()[result.plan().selection()[p] as int]).block == 0 ==>
            super_state::replay_ok(primary, result.plan().log()[result.plan().selection()[p] as int].image, partition_bytes),
{
    hide(crc::fold);
    hide(superblock::accepted);
    reveal(input_ok);
    if bytes::be32(journal, 28) != 0 {
        reveal(safe_committed_streams);
        let records = result.records();
        assert(scan_trace::well_formed(records, scan_budget::source(journal, uuid, layout)));
        assert forall|p: int| 0 <= p < result.plan().selection().len()
            && (#[trigger] result.plan().log()[result.plan().selection()[p] as int]).block == 0 implies
            super_state::replay_ok(primary, result.plan().log()[result.plan().selection()[p] as int].image, partition_bytes) by {
            let index = result.plan().selection()[p] as int;
            assert(replay::latest(result.plan().log(), result.plan().revocations(), index));
            assert(0 <= index < scan_trace::writes(records).len());
            assert(scan_trace::writes(records)[index].block == 0);
        }
    }
}

pub proof fn safe_streams_survive_valid_superblock_replay(source: Source, before: Seq<u8>, after: Seq<u8>, partition_bytes: u64)
    requires safe_committed_streams(source, before, partition_bytes), super_state::replay_ok(before, after, partition_bytes),
    ensures safe_committed_streams(source, after, partition_bytes),
{
    hide(crc::fold);
    reveal(safe_committed_streams);
    assert forall|records: Seq<Record>| #[trigger] scan_trace::well_formed(records, source)
        && (records.len() == 0 || records.last().kind == 2) implies
        (forall|i: int| 0 <= i < scan_trace::writes(records).len()
            && (#[trigger] scan_trace::writes(records)[i]).block == 0 ==>
                super_state::replay_ok(after, scan_trace::writes(records)[i].image, partition_bytes)) by {
        assert forall|i: int| 0 <= i < scan_trace::writes(records).len()
            && (#[trigger] scan_trace::writes(records)[i]).block == 0 implies
            super_state::replay_ok(after, scan_trace::writes(records)[i].image, partition_bytes) by {
            super_state::replay_policy_is_stable_under_another_valid_replay(before, after, scan_trace::writes(records)[i].image, partition_bytes);
        }
    }
}

}
