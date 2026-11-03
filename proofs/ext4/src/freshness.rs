// SPDX-License-Identifier: MPL-2.0

//! Fresh header recognition follows byte provenance and epoch bounds. CRC
//! equality is never used as a collision-free identity test in these proofs.

use vstd::prelude::*;
use crate::{bytes, epoch, jbd2, journal_view, layout::LayoutView, replay, replay_refinement::Disk,
    transaction::{self, TransactionView}};

verus! {

pub open spec fn commit_header(image: Seq<u8>, sequence: u32) -> bool {
    jbd2::header_ok(image, sequence) && bytes::be32(image, 4) == 2
}

pub proof fn an_old_journal_block_cannot_have_a_current_or_later_header(before: Disk, layout: LayoutView,
    minimum: u32, sequence: u32, logical: u32, candidate: u32)
    requires journal_view::mapped(before, layout),
        epoch::newer(journal_view::snapshot(before, layout), minimum, sequence),
        1 <= logical < layout.journal_blocks, sequence <= candidate,
    ensures !jbd2::header_ok(before[(layout.start + logical) as u32], candidate),
{
    journal_view::snapshot_block_is_the_physical_image(before, layout, logical);
    let snapshot = journal_view::snapshot(before, layout);
    let raw = before[(layout.start + logical) as u32];
    if jbd2::header_ok(raw, candidate) {
        assert(bytes::be32(snapshot, logical as int * 4096) == bytes::be32(raw, 0));
        assert(bytes::be32(snapshot, logical as int * 4096 + 4) == bytes::be32(raw, 4));
        assert(bytes::be32(snapshot, logical as int * 4096 + 8) == bytes::be32(raw, 8));
        assert(epoch::header_id(snapshot, logical as int, candidate));
        assert(candidate < sequence);
    }
}

pub proof fn an_encoded_payload_cannot_be_a_metadata_header(tx: TransactionView, index: int, sequence: u32)
    requires transaction::wf(tx), 0 <= index < tx.payloads.len(),
    ensures !jbd2::header_ok(tx.payloads[index], sequence),
{
    assert(replay::payload_for_layout(tx.tags[index], tx.payloads[index], tx.sequence, tx.seed, tx.layout));
    assert(bytes::be32(tx.payloads[index], 0) != 0xc03b3998);
}

pub enum JournalImage {
    Original { logical: u32 }, Descriptor, Payload { index: nat }, Commit,
}

pub open spec fn denotes(version: JournalImage, image: Seq<u8>, before: Disk, tx: TransactionView) -> bool {
    match version {
        JournalImage::Original { logical } => 1 <= logical < tx.layout.journal_blocks
            && image == before[(tx.layout.start + logical) as u32],
        JournalImage::Descriptor => image == tx.descriptor,
        JournalImage::Payload { index } => index < tx.payloads.len() && image == tx.payloads[index as int],
        JournalImage::Commit => image == tx.commit,
    }
}

pub proof fn only_the_issued_commit_image_can_recognize_a_fresh_commit(version: JournalImage, image: Seq<u8>,
    before: Disk, tx: TransactionView, minimum: u32)
    requires transaction::wf(tx), journal_view::mapped(before, tx.layout),
        epoch::newer(journal_view::snapshot(before, tx.layout), minimum, tx.sequence),
        denotes(version, image, before, tx), commit_header(image, tx.sequence),
    ensures version is Commit, image == tx.commit,
{
    match version {
        JournalImage::Original { logical } => {
            an_old_journal_block_cannot_have_a_current_or_later_header(before, tx.layout, minimum, tx.sequence, logical, tx.sequence);
        },
        JournalImage::Descriptor => { },
        JournalImage::Payload { index } => { an_encoded_payload_cannot_be_a_metadata_header(tx, index as int, tx.sequence); },
        JournalImage::Commit => { },
    }
}

}
