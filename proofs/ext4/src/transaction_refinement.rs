// SPDX-License-Identifier: MPL-2.0

//! Encoded bytes refine exact scan certificates. The concrete journal-map
//! witness establishes that the relation is satisfiable without a checksum
//! oracle. Physical persistence of a writer remains a separate refinement.

use vstd::prelude::*;
use crate::{jbd2, journal_view, replay::{self, WriteView}, replay_refinement::Disk, scan, scan_stop,
    scan_trace::{self, Record, Source}, transaction::{self, TransactionView}};

verus! {

pub open spec fn log(tx: TransactionView) -> Seq<WriteView> {
    Seq::new(tx.original.len(), |i: int| WriteView { block: tx.original[i].block, sequence: tx.sequence, image: tx.original[i].image })
}

pub open spec fn descriptor_record(tx: TransactionView) -> Record {
    Record { start: 0, end: (tx.original.len() + 1) as u32, sequence: tx.sequence, kind: 1,
        writes: log(tx), revocations: Seq::empty(), revoke_origins: Seq::empty(),
        origins: Seq::new(tx.original.len(), |i: int| scan::Origin { descriptor: 0, payload: (i + 1) as u32,
            index: i as nat, count: tx.original.len() }) }
}

pub open spec fn commit_record(tx: TransactionView) -> Record {
    Record { start: (tx.original.len() + 1) as u32, end: (tx.original.len() + 2) as u32,
        sequence: tx.sequence, kind: 2, writes: Seq::empty(), revocations: Seq::empty(), origins: Seq::empty(), revoke_origins: Seq::empty() }
}

pub open spec fn records(tx: TransactionView) -> Seq<Record> { seq![descriptor_record(tx), commit_record(tx)] }

pub open spec fn source_fields(tx: TransactionView, source: Source) -> bool {
    source.layout == tx.layout && source.blocks == tx.layout.journal_blocks && source.start == 1
        && source.first == tx.sequence && source.uuid == tx.uuid && source.seed == tx.seed
}

pub open spec fn payload_records_present(tx: TransactionView, source: Source) -> bool {
    &&& source_fields(tx, source)
    &&& scan::block_at(source.journal, source.blocks, 1, 0) == tx.descriptor
    &&& (forall|i: int| 0 <= i < tx.payloads.len() ==>
        #[trigger] scan::block_at(source.journal, source.blocks, 1, (i + 1) as u32) == tx.payloads[i])
}

pub open spec fn committed_records_present(tx: TransactionView, source: Source) -> bool {
    &&& payload_records_present(tx, source)
    &&& scan::block_at(source.journal, source.blocks, 1, (tx.original.len() + 1) as u32) == tx.commit
    &&& !jbd2::header_ok(scan::block_at(source.journal, source.blocks, 1, (tx.original.len() + 2) as u32), (tx.sequence + 1) as u32)
}

pub proof fn payload_images_form_one_exact_descriptor_record(tx: TransactionView, source: Source)
    requires transaction::wf(tx), payload_records_present(tx, source),
    ensures scan_trace::record_ok(descriptor_record(tx), source),
{
    let record = descriptor_record(tx);
    assert forall|i: int| 0 <= i < tx.original.len() implies
        #[trigger] scan::origin_ok(source.journal, source.blocks, 1, source.uuid, source.seed, source.layout,
            record.writes[i], record.origins[i]) by {
        assert(tx.tags[i].block == tx.original[i].block);
        assert(scan::block_at(source.journal, source.blocks, 1, (i + 1) as u32) == tx.payloads[i]);
        reveal(scan::origin_ok);
    }
    assert(scan_trace::record_ok(record, source)) by { reveal(scan_trace::record_ok); }
}

pub proof fn encoded_transaction_has_a_complete_committed_certificate(tx: TransactionView, source: Source)
    requires transaction::wf(tx), committed_records_present(tx, source),
    ensures scan_trace::committed_prefix(records(tx), source, log(tx), Seq::empty()),
        scan_trace::next_sequence(records(tx), source.first) == tx.sequence as nat + 1,
        scan_stop::at_boundary(scan_stop::Stop::Header { ordinal: (tx.original.len() + 2) as u32 },
            records(tx), source, (tx.sequence + 1) as u32),
{
    payload_images_form_one_exact_descriptor_record(tx, source);
    let descriptor = descriptor_record(tx);
    let commit = commit_record(tx);
    assert(scan_trace::record_ok(commit, source)) by { reveal(scan_trace::record_ok); }
    scan_trace::empty_records(source);
    scan_trace::append_record(Seq::empty(), descriptor, source);
    let first = Seq::<Record>::empty().push(descriptor);
    scan_trace::append_record(first, commit, source);
    assert(first.push(commit) =~= records(tx));
    assert(scan_trace::writes(records(tx)) =~= log(tx));
    assert(scan_trace::revocations(records(tx)) =~= Seq::<replay::Revocation>::empty());
    assert(scan_stop::at_boundary(scan_stop::Stop::Header { ordinal: (tx.original.len() + 2) as u32 },
        records(tx), source, (tx.sequence + 1) as u32)) by { reveal(scan_stop::at_boundary); }
}

pub open spec fn journal_addresses(tx: TransactionView) -> Seq<u32> {
    Seq::new(tx.layout.journal_blocks as nat, |i: int| (tx.layout.start as int + i) as u32)
}

pub open spec fn journal_image(tx: TransactionView, superblock: Seq<u8>) -> Disk {
    Map::new(journal_addresses(tx).to_set(), |block: u32| {
        let logical = block as int - tx.layout.start;
        if logical == 0 { superblock }
        else if logical == 1 { tx.descriptor }
        else if 2 <= logical < tx.payloads.len() + 2 { tx.payloads[logical - 2] }
        else if logical == tx.payloads.len() + 2 { tx.commit }
        else { Seq::new(4096, |i: int| 0u8) }
    })
}

pub open spec fn assembled_source(tx: TransactionView, superblock: Seq<u8>) -> Source {
    Source { journal: journal_view::snapshot(journal_image(tx, superblock), tx.layout),
        blocks: tx.layout.journal_blocks, start: 1, first: tx.sequence, layout: tx.layout, uuid: tx.uuid, seed: tx.seed }
}

#[verifier::rlimit(40)]
pub proof fn complete_encoded_journal_has_a_concrete_disk_witness(tx: TransactionView, superblock: Seq<u8>)
    requires transaction::wf(tx), superblock.len() == 4096,
    ensures journal_view::mapped(journal_image(tx, superblock), tx.layout),
        committed_records_present(tx, assembled_source(tx, superblock)),
{
    let disk = journal_image(tx, superblock);
    assert forall|logical: u32| logical < tx.layout.journal_blocks implies
        #[trigger] disk.dom().contains((tx.layout.start + logical) as u32)
            && disk[(tx.layout.start + logical) as u32].len() == 4096 by {
        assert(journal_addresses(tx)[logical as int] == (tx.layout.start + logical) as u32);
        assert(journal_addresses(tx).contains((tx.layout.start + logical) as u32));
        if 2 <= logical < tx.payloads.len() + 2 {
            assert(replay::payload_for_layout(tx.tags[logical as int - 2], tx.payloads[logical as int - 2], tx.sequence, tx.seed, tx.layout));
        }
    }
    journal_view::scanned_block_is_the_reserved_ring_image(disk, tx.layout, 1, 0);
    journal_view::scanned_block_is_the_reserved_ring_image(disk, tx.layout, 1, (tx.payloads.len() + 1) as u32);
    journal_view::scanned_block_is_the_reserved_ring_image(disk, tx.layout, 1, (tx.payloads.len() + 2) as u32);
    let source = assembled_source(tx, superblock);
    assert forall|i: int| 0 <= i < tx.payloads.len() implies
        #[trigger] scan::block_at(source.journal, source.blocks, 1, (i + 1) as u32) == tx.payloads[i] by {
        journal_view::scanned_block_is_the_reserved_ring_image(disk, tx.layout, 1, (i + 1) as u32);
    }
}

pub proof fn successful_scan_of_encoded_transaction_recovers_every_original(tx: TransactionView, source: Source, result: &scan::Scan)
    requires transaction::wf(tx), committed_records_present(tx, source), result.certificate(source), result.maximal(source),
    ensures result.plan().log() == log(tx), result.plan().revocations().len() == 0, result.next() as nat == tx.sequence as nat + 1,
{
    encoded_transaction_has_a_complete_committed_certificate(tx, source);
    scan_stop::maximal_canonical_prefix_is_unique(result.scanned(), records(tx), result.termination(),
        scan_stop::Stop::Header { ordinal: (tx.original.len() + 2) as u32 }, source, result.next(), (tx.sequence + 1) as u32);
    assert(result.scanned() == records(tx));
    if result.records().len() < 2 {
        assert(result.scanned()[1].kind != 2);
    }
    assert(result.records() == records(tx));
}

}
