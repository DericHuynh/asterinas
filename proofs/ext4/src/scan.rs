// SPDX-License-Identifier: MPL-2.0

//! Bounded scanning of a frozen internal-journal snapshot. Only committed
//! transaction prefixes enter the replay plan; an incomplete tail is dropped.
//! Byte recognition is not authentication or a device-persistence guarantee.

use vstd::prelude::*;
use crate::{bytes, crc, descriptor, jbd2, journal_superblock, layout::{JournalLayout, LayoutView}, replay, revoke, ring, scan_budget, scan_stop, scan_trace};

verus! {

pub open spec fn block_at(journal: Seq<u8>, blocks: u32, start: u32, ordinal: u32) -> Seq<u8> {
    let logical = ring::position(1, blocks, start, ordinal);
    journal.subrange((logical * 4096) as int, ((logical + 1) * 4096) as int)
}

pub struct Origin { pub descriptor: u32, pub payload: u32, pub index: nat, pub count: nat }
pub struct RevokeOrigin { pub record: u32, pub index: nat }

#[verifier::opaque]
pub open spec fn origin_ok(journal: Seq<u8>, blocks: u32, start: u32, uuid: Seq<u8>, seed: u32,
    layout: LayoutView, write: replay::WriteView, origin: Origin) -> bool {
    let desc = block_at(journal, blocks, start, origin.descriptor);
    let payload = block_at(journal, blocks, start, origin.payload);
    let tag = jbd2::Tag {
        block: bytes::be32(desc, descriptor::offset(origin.index as int)) as u32,
        flags: bytes::be32(desc, descriptor::offset(origin.index as int) + 4) as u32,
        checksum: bytes::be32(desc, descriptor::offset(origin.index as int) + 12) as u32,
    };
    &&& origin.descriptor < origin.payload < blocks - 1
    &&& origin.index < origin.count <= 250
    &&& origin.payload as nat == origin.descriptor as nat + 1 + origin.index
    &&& descriptor::base(desc, uuid, write.sequence, seed)
    &&& descriptor::candidate(desc, origin.count, layout.fs_blocks)
    &&& replay::payload_for_layout(tag, payload, write.sequence, seed, layout)
    &&& write.block == tag.block && write.image == replay::restored(payload, tag.flags % 2 == 1)
}

#[verifier::opaque]
pub open spec fn revoke_origin_ok(journal: Seq<u8>, blocks: u32, start: u32, seed: u32,
    revocation: replay::Revocation, origin: RevokeOrigin) -> bool {
    let record = block_at(journal, blocks, start, origin.record);
    &&& origin.record < blocks - 1
    &&& revoke::header(record, revocation.sequence, seed)
    &&& origin.index < revoke::count(record)
    &&& revocation.block as nat == bytes::be32(record, 16 + 4 * origin.index as int)
}

fn read_block(journal: &[u8], blocks: u32, start: u32, ordinal: u32) -> (r: &[u8])
    requires 1024 <= blocks <= 32768, journal.len() as nat == blocks as nat * 4096,
        1 <= start < blocks, ordinal < blocks - 1,
    ensures r@ == block_at(journal@, blocks, start, ordinal), r.len() == 4096,
{
    let logical = ring::slot(1, blocks, start, ordinal).unwrap();
    let offset = logical as usize * 4096;
    &journal[offset..offset + 4096]
}

fn targets_allowed(targets: &[u32], layout: &JournalLayout) -> (r: bool)
    requires layout.wf(),
    ensures r == (forall|i: int| 0 <= i < targets.len() ==> #[trigger] scan_budget::target_allowed(layout.view(), targets@[i])),
{
    let mut i = 0usize;
    while i < targets.len()
        invariant i <= targets.len(), layout.wf(),
            forall|j: int| 0 <= j < i ==> #[trigger] scan_budget::target_allowed(layout.view(), targets@[j]),
        decreases targets.len() - i,
    {
        if !layout.allows_target(targets[i]) {
            assert(!scan_budget::target_allowed(layout.view(), targets@[i as int]));
            return false;
        }
        i += 1;
    }
    true
}

pub struct Scan {
    plan: replay::ReplayPlan,
    first: u32,
    next: u32,
    committed: u32,
    consumed: u32,
    commit_positions: Ghost<Map<u32, u32>>,
    origins: Ghost<Seq<Origin>>,
    revoke_origins: Ghost<Seq<RevokeOrigin>>,
    records: Ghost<Seq<scan_trace::Record>>,
    scanned: Ghost<Seq<scan_trace::Record>>,
    termination: Ghost<scan_stop::Stop>,
}

impl Scan {
    pub closed spec fn first(&self) -> u32 { self.first }
    pub closed spec fn next(&self) -> u32 { self.next }
    pub closed spec fn committed(&self) -> u32 { self.committed }
    pub closed spec fn consumed(&self) -> u32 { self.consumed }
    pub closed spec fn commit_positions(&self) -> Map<u32, u32> { self.commit_positions@ }
    pub closed spec fn plan(&self) -> &replay::ReplayPlan { &self.plan }
    pub closed spec fn origins(&self) -> Seq<Origin> { self.origins@ }
    pub closed spec fn revoke_origins(&self) -> Seq<RevokeOrigin> { self.revoke_origins@ }
    pub closed spec fn records(&self) -> Seq<scan_trace::Record> { self.records@ }
    pub closed spec fn scanned(&self) -> Seq<scan_trace::Record> { self.scanned@ }
    pub closed spec fn termination(&self) -> scan_stop::Stop { self.termination@ }

    pub open spec fn maximal(&self, source: scan_trace::Source) -> bool {
        &&& scan_trace::well_formed(self.scanned(), source)
        &&& self.records().len() <= self.scanned().len()
        &&& self.scanned().take(self.records().len() as int) == self.records()
        &&& (forall|i: int| self.records().len() <= i < self.scanned().len() ==>
            (#[trigger] self.scanned()[i]).kind != 2 && self.scanned()[i].sequence == self.next())
        &&& scan_trace::end(self.scanned()) <= self.consumed()
        &&& scan_trace::next_sequence(self.scanned(), source.first) == self.next() as nat
        &&& scan_stop::at_boundary(self.termination(), self.scanned(), source, self.next())
    }

    pub open spec fn certificate(&self, source: scan_trace::Source) -> bool {
        &&& scan_trace::committed_prefix(self.records(), source, self.plan().log(), self.plan().revocations())
        &&& scan_trace::end(self.records()) <= self.consumed()
        &&& scan_trace::next_sequence(self.records(), source.first) == self.next() as nat
    }

    pub open spec fn provenance(&self, journal: Seq<u8>, blocks: u32, start: u32, uuid: Seq<u8>, seed: u32) -> bool {
        &&& self.origins().len() == self.plan().log().len()
        &&& self.revoke_origins().len() == self.plan().revocations().len()
        &&& (forall|i: int| 0 <= i < self.origins().len() ==>
            origin_ok(journal, blocks, start, uuid, seed, self.plan().layout().view(), self.plan().log()[i], #[trigger] self.origins()[i])
            && self.origins()[i].payload < self.commit_positions()[self.plan().log()[i].sequence])
        &&& (forall|i: int| 0 <= i < self.revoke_origins().len() ==>
            revoke_origin_ok(journal, blocks, start, seed, self.plan().revocations()[i], #[trigger] self.revoke_origins()[i])
            && self.revoke_origins()[i].record < self.commit_positions()[self.plan().revocations()[i].sequence])
    }

    pub open spec fn recognized(&self, journal: Seq<u8>, blocks: u32, start: u32, seed: u32) -> bool {
        &&& self.next() as nat == self.first() as nat + self.committed() as nat
        &&& (forall|id: u32| #[trigger] self.commit_positions().dom().contains(id)
            <==> self.first() <= id < self.next())
        &&& (forall|id: u32| self.commit_positions().dom().contains(id) ==>
            (#[trigger] self.commit_positions()[id]) < self.consumed()
            && self.commit_positions()[id] < blocks - 1
            && jbd2::commit_ok(block_at(journal, blocks, start, self.commit_positions()[id]), id, seed))
        &&& (forall|i: int| 0 <= i < self.plan().log().len() ==>
            #[trigger] self.commit_positions().dom().contains(self.plan().log()[i].sequence))
        &&& (forall|i: int| 0 <= i < self.plan().revocations().len() ==>
            #[trigger] self.commit_positions().dom().contains(self.plan().revocations()[i].sequence))
    }

    pub fn replay_plan(&self) -> (r: &replay::ReplayPlan) ensures r == self.plan() { &self.plan }
    pub fn next_sequence(&self) -> (r: u32) ensures r == self.next() { self.next }
    pub fn committed_transactions(&self) -> (r: u32) ensures r == self.committed() { self.committed }
}

#[verifier::rlimit(100)]
#[verifier::spinoff_prover]
pub fn recover(journal: &[u8], uuid: &[u8], layout: JournalLayout) -> (r: Option<Scan>)
    ensures match r {
        Some(s) => s.plan().refines() && s.plan().layout().view() == layout.view()
            && layout.wf() && journal.len() as nat == layout.view().journal_blocks as nat * 4096
            && journal_superblock::accepted(journal@.subrange(0, 1024), uuid@, layout.view().journal_blocks)
            && s.first() as nat == bytes::be32(journal@, 24)
            && (bytes::be32(journal@, 28) == 0 ==> s.committed() == 0 && s.plan().selection().len() == 0)
            && s.recognized(journal@, layout.view().journal_blocks, bytes::be32(journal@, 28) as u32,
                crc::fold(0xffffffff, uuid@))
            && s.provenance(journal@, layout.view().journal_blocks, bytes::be32(journal@, 28) as u32,
                uuid@, crc::fold(0xffffffff, uuid@))
            && s.certificate(scan_trace::Source { journal: journal@, blocks: layout.view().journal_blocks,
                start: bytes::be32(journal@, 28) as u32, first: s.first(), uuid: uuid@,
                seed: crc::fold(0xffffffff, uuid@), layout: layout.view() })
            && s.maximal(scan_trace::Source { journal: journal@, blocks: layout.view().journal_blocks,
                start: bytes::be32(journal@, 28) as u32, first: s.first(), uuid: uuid@,
                seed: crc::fold(0xffffffff, uuid@), layout: layout.view() }),
        None => !scan_budget::admitted(journal@, uuid@, &layout),
    },
{
    hide(crc::fold);
    let ghost can_scan = scan_budget::admitted(journal@, uuid@, &layout);
    if !layout.valid() { proof { reveal(scan_budget::admitted); } return None; }
    let blocks = layout.blocks();
    if journal.len() as u64 != blocks as u64 * 4096 { proof { reveal(scan_budget::admitted); } return None; }
    let info = match journal_superblock::parse(&journal[0..1024], uuid, blocks) {
        Some(info) => info, None => { proof { reveal(scan_budget::admitted); } return None; }
    };
    let first = info.sequence;
    let seed = info.uuid_seed;
    if info.start == 0 {
        let ghost initial = scan_trace::Source { journal: journal@, blocks,
            start: 0, first, uuid: uuid@, seed, layout: layout.view() };
        proof {
            scan_trace::empty_records(initial);
            assert(scan_stop::at_boundary(scan_stop::Stop::Clean, Seq::empty(), initial, first)) by { reveal(scan_stop::at_boundary); }
        }
        let writes = Vec::new();
        let revocations = Vec::new();
        let plan = replay::build(layout, writes, revocations, 1, 1).unwrap();
        assert(plan.log() =~= Seq::<replay::WriteView>::empty());
        assert(plan.revocations() =~= Seq::<replay::Revocation>::empty());
        let result = Scan { plan, first, next: first, committed: 0, consumed: 0,
            commit_positions: Ghost(Map::empty()), origins: Ghost(Seq::empty()), revoke_origins: Ghost(Seq::empty()),
            records: Ghost(Seq::empty()), scanned: Ghost(Seq::empty()), termination: Ghost(scan_stop::Stop::Clean) };
        assert(scan_trace::well_formed(result.scanned(), initial));
        assert(result.records().len() <= result.scanned().len());
        assert(result.scanned().take(result.records().len() as int) =~= result.records());
        assert(scan_trace::end(result.scanned()) <= result.consumed());
        assert(scan_trace::next_sequence(result.scanned(), initial.first) == result.next() as nat);
        assert(scan_stop::at_boundary(result.termination(), result.scanned(), initial, result.next()));
        assert(result.maximal(initial));
        return Some(result);
    }
    if !info.csum_v3 || first == 4294967295 { proof { reveal(scan_budget::admitted); } return None; }
    let start = info.start;
    let mut writes: Vec<replay::RecoveredWrite> = Vec::new();
    let mut revocations: Vec<replay::Revocation> = Vec::new();
    let mut committed_writes = 0usize;
    let mut committed_revocations = 0usize;
    let mut sequence = first;
    let mut committed = 0u32;
    let mut visited = 0u32;
    let mut stop = false;
    let ghost mut positions: Map<u32, u32> = Map::empty();
    let ghost mut origins: Seq<Origin> = Seq::empty();
    let ghost mut revoke_origins: Seq<RevokeOrigin> = Seq::empty();
    let ghost source = scan_trace::Source { journal: journal@, blocks, start, first, uuid: uuid@, seed, layout: layout.view() };
    assert(can_scan ==> scan_budget::within_limits(source)) by { reveal(scan_budget::admitted); }
    assert(can_scan ==> info.revoke) by { reveal(scan_budget::admitted); }
    let ghost mut records: Seq<scan_trace::Record> = Seq::empty();
    let ghost mut committed_records: Seq<scan_trace::Record> = Seq::empty();
    let ghost mut termination = scan_stop::Stop::Clean;
    proof { scan_trace::empty_records(source); }
    while !stop && visited < blocks - 1
        invariant layout.wf(), layout.view().journal_blocks == blocks, 1024 <= blocks <= 32768,
            source == (scan_trace::Source { journal: journal@, blocks, start, first, uuid: uuid@, seed, layout: layout.view() }),
            can_scan == scan_budget::admitted(journal@, uuid@, &layout),
            can_scan ==> scan_budget::within_limits(source),
            can_scan ==> info.revoke,
            journal.len() as nat == blocks as nat * 4096, 1 <= start < blocks,
            bytes::be32(journal@, 28) == start as nat,
            0 < first <= sequence, sequence as nat == first as nat + committed as nat,
            committed <= visited <= blocks - 1, writes.len() + revocations.len() <= 4096,
            committed_writes <= writes.len(), committed_revocations <= revocations.len(),
            origins.len() == writes.len(), revoke_origins.len() == revocations.len(),
            scan_trace::well_formed(records, source), scan_trace::well_formed(committed_records, source),
            committed_records.len() <= records.len(), records.take(committed_records.len() as int) == committed_records,
            forall|i: int| committed_records.len() <= i < records.len() ==>
                (#[trigger] records[i]).kind != 2 && records[i].sequence == sequence,
            scan_trace::end(records) <= visited,
            stop ==> scan_stop::at_boundary(termination, records, source, sequence),
            committed_records.len() == 0 || committed_records.last().kind == 2,
            scan_trace::end(committed_records) <= visited,
            scan_trace::next_sequence(committed_records, first) == sequence as nat,
            scan_trace::writes(committed_records) == replay::images(writes@).take(committed_writes as int),
            scan_trace::revocations(committed_records) == revocations@.take(committed_revocations as int),
            !stop ==> scan_trace::end(records) == visited,
            scan_trace::next_sequence(records, first) == sequence as nat,
            !stop ==> scan_trace::writes(records) == replay::images(writes@),
            !stop ==> scan_trace::revocations(records) == revocations@,
            forall|i: int| 0 <= i < origins.len() ==>
                origin_ok(journal@, blocks, start, uuid@, seed, layout.view(), writes@[i].view(), #[trigger] origins[i]) && origins[i].payload < visited,
            forall|i: int| 0 <= i < revoke_origins.len() ==>
                revoke_origin_ok(journal@, blocks, start, seed, revocations@[i], #[trigger] revoke_origins[i]) && revoke_origins[i].record < visited,
            forall|i: int| 0 <= i < committed_writes ==> positions.dom().contains((#[trigger] writes@[i].view()).sequence)
                && origins[i].payload < positions[writes@[i].view().sequence],
            forall|i: int| committed_writes <= i < writes.len() ==> (#[trigger] writes@[i].view()).sequence == sequence,
            forall|i: int| 0 <= i < committed_revocations ==> positions.dom().contains((#[trigger] revocations@[i]).sequence)
                && revoke_origins[i].record < positions[revocations@[i].sequence],
            forall|i: int| committed_revocations <= i < revocations.len() ==> (#[trigger] revocations@[i]).sequence == sequence,
            forall|id: u32| #[trigger] positions.dom().contains(id) <==> first <= id < sequence,
            forall|id: u32| positions.dom().contains(id) ==> (#[trigger] positions[id]) < visited
                && jbd2::commit_ok(block_at(journal@, blocks, start, positions[id]), id, seed),
            forall|i: int| 0 <= i < writes.len() ==> layout.allowed((#[trigger] writes@[i].view()).block)
                && writes@[i].view().image.len() == 4096 && first <= writes@[i].view().sequence <= sequence,
            forall|i: int| 0 <= i < committed_writes ==> (#[trigger] writes@[i].view()).sequence < sequence,
            forall|i: int| 0 < i < writes.len() ==> (#[trigger] writes@[i].view()).sequence >= writes@[i - 1].view().sequence,
            forall|i: int| 0 <= i < revocations.len() ==> layout.allowed((#[trigger] revocations@[i]).block)
                && first <= revocations@[i].sequence <= sequence,
            forall|i: int| 0 <= i < committed_revocations ==> (#[trigger] revocations@[i]).sequence < sequence,
            sequence == 4294967295 ==> stop,
        decreases blocks - 1 - visited,
    {
        let ordinal = visited;
        let ghost before_writes = writes@;
        let ghost before_revocations = revocations@;
        let raw = read_block(journal, blocks, start, visited);
        visited += 1;
        let header = match jbd2::parse_header(raw, sequence) {
            Some(header) => header, None => {
                proof {
                    termination = scan_stop::Stop::Header { ordinal };
                    assert(scan_stop::at_boundary(termination, records, source, sequence)) by { reveal(scan_stop::at_boundary); }
                }
                stop = true; continue;
            }
        };
        if header.kind == 1 {
            let desc = match descriptor::parse(raw, uuid, sequence, layout.filesystem_blocks(), seed) {
                Some(desc) => desc, None => {
                    proof {
                        termination = scan_stop::Stop::Descriptor { ordinal };
                        assert(scan_stop::at_boundary(termination, records, source, sequence)) by { reveal(scan_stop::at_boundary); }
                    }
                    stop = true; continue;
                }
            };
            let tags = desc.tags();
            if tags.len() as u32 > blocks - 1 - visited
                || tags.len() > 4096 - writes.len() - revocations.len() {
                proof {
                    if can_scan { scan_budget::next_descriptor_has_room_and_credits(records, source, sequence, tags.len() as nat); }
                    assert(!can_scan);
                }
                return None;
            }
            let mut i = 0usize;
            while i < tags.len() && !stop
                invariant i <= tags.len() <= 250,
                    scan_trace::end(records) == ordinal,
                    before_writes.len() + revocations.len() + tags.len() <= 4096,
                    source == (scan_trace::Source { journal: journal@, blocks, start, first, uuid: uuid@, seed, layout: layout.view() }),
                    stop ==> scan_stop::at_boundary(termination, records, source, sequence),
                    before_writes.len() <= writes.len(), writes@.take(before_writes.len() as int) == before_writes,
                    !stop ==> writes.len() == before_writes.len() + i,
                    forall|j: int| before_writes.len() <= j < writes.len() ==>
                        (#[trigger] origins[j]).descriptor == ordinal && origins[j].index == j - before_writes.len()
                        && origins[j].count == tags.len() && writes@[j].view().sequence == sequence,
                    layout.wf(), blocks == layout.view().journal_blocks, 1024 <= blocks <= 32768,
                    journal.len() as nat == blocks as nat * 4096, 1 <= start < blocks,
                    bytes::be32(journal@, 28) == start as nat,
                    visited <= blocks - 1, tags.len() - i <= blocks - 1 - visited,
                    visited as nat == ordinal as nat + 1 + i as nat, committed < visited,
                    0 < first <= sequence < 4294967295,
                    writes.len() + revocations.len() <= 4096,
                    committed_writes <= writes.len(),
                    origins.len() == writes.len(),
                    forall|j: int| 0 <= j < origins.len() ==>
                        origin_ok(journal@, blocks, start, uuid@, seed, layout.view(), writes@[j].view(), #[trigger] origins[j]) && origins[j].payload < visited,
                    forall|j: int| 0 <= j < committed_writes ==> positions.dom().contains((#[trigger] writes@[j].view()).sequence)
                && origins[j].payload < positions[writes@[j].view().sequence],
                    forall|j: int| committed_writes <= j < writes.len() ==> (#[trigger] writes@[j].view()).sequence == sequence,
                    raw@ == block_at(journal@, blocks, start, ordinal),
                    descriptor::base(raw@, uuid@, sequence, seed),
                    descriptor::candidate(raw@, tags.len() as nat, layout.view().fs_blocks),
                    descriptor::represents(raw@, tags@),
                    forall|j: int| 0 <= j < committed_writes ==> (#[trigger] writes@[j].view()).sequence < sequence,
                    forall|j: int| 0 <= j < writes.len() ==> layout.allowed((#[trigger] writes@[j].view()).block)
                        && writes@[j].view().image.len() == 4096 && first <= writes@[j].view().sequence <= sequence,
                    forall|j: int| 0 < j < writes.len() ==> (#[trigger] writes@[j].view()).sequence >= writes@[j - 1].view().sequence,
                decreases tags.len() - i,
            {
                let payload_ordinal = visited;
                let payload = read_block(journal, blocks, start, visited);
                visited += 1;
                match replay::decode_payload(&tags[i], payload, sequence, seed, &layout) {
                    Some(write) => {
                        let ghost previous_writes = writes@;
                        let ghost previous_origins = origins;
                        proof {
                            let origin = Origin { descriptor: ordinal, payload: payload_ordinal,
                                index: i as nat, count: tags.len() as nat };
                            assert(origin_ok(journal@, blocks, start, uuid@, seed, layout.view(), write.view(), origin)) by { reveal(origin_ok); }
                            origins = origins.push(origin);
                        }
                        writes.push(write);
                        proof {
                            assert forall|j: int| 0 <= j < committed_writes implies
                                positions.dom().contains((#[trigger] writes@[j].view()).sequence)
                                && origins[j].payload < positions[writes@[j].view().sequence] by {
                                assert(writes@[j] == previous_writes[j]);
                                assert(origins[j] == previous_origins[j]);
                                assert(positions.dom().contains(previous_writes[j].view().sequence)
                                    && previous_origins[j].payload < positions[previous_writes[j].view().sequence]);
                            }
                        }
                    },
                    None => {
                        proof {
                            termination = scan_stop::Stop::Payload { ordinal, count: tags.len() as nat, index: i as nat, tag: tags@[i as int] };
                            assert(scan_stop::at_boundary(termination, records, source, sequence)) by { reveal(scan_stop::at_boundary); }
                        }
                        stop = true;
                    },
                }
                i += 1;
            }
            if !stop {
                proof {
                    let record = scan_trace::Record { start: ordinal, end: visited, sequence, kind: 1,
                        writes: replay::images(writes@).subrange(before_writes.len() as int, writes.len() as int),
                        origins: origins.subrange(before_writes.len() as int, writes.len() as int),
                        revocations: Seq::empty(), revoke_origins: Seq::empty() };
                    assert(scan_trace::record_ok(record, source)) by { reveal(scan_trace::record_ok); }
                    scan_trace::append_record(records, record, source);
                    records = records.push(record);
                }
            }
        } else if header.kind == 5 {
            if !info.revoke { proof { assert(!can_scan); } return None; }
            let revoked = match revoke::parse(raw, sequence, layout.filesystem_blocks(), seed) {
                Some(records) => records, None => {
                    proof {
                        termination = scan_stop::Stop::Revoke { ordinal };
                        assert(scan_stop::at_boundary(termination, records, source, sequence)) by { reveal(scan_stop::at_boundary); }
                    }
                    stop = true; continue;
                }
            };
            let targets = revoked.blocks();
            if targets.len() > 4096 - writes.len() - revocations.len() || !targets_allowed(targets, &layout) {
                proof {
                    if can_scan {
                        scan_budget::next_revoke_has_credits_and_permitted_targets(records, source, sequence);
                        assert forall|i: int| 0 <= i < targets.len() implies #[trigger] scan_budget::target_allowed(source.layout, targets@[i]) by {
                            assert(scan_budget::target_allowed(source.layout, bytes::be32(raw@, 16 + 4 * i) as u32));
                            assert(targets@[i] as nat == bytes::be32(raw@, 16 + 4 * i));
                        }
                    }
                    assert(!can_scan);
                }
                return None;
            }
            let mut i = 0usize;
            while i < targets.len()
                invariant i <= targets.len() <= 1019, writes.len() + revocations.len() <= 4096,
                    0 < start, bytes::be32(journal@, 28) == start as nat,
                    before_revocations.len() + writes.len() + targets.len() <= 4096,
                    forall|j: int| 0 <= j < targets.len() ==> #[trigger] scan_budget::target_allowed(layout.view(), targets@[j]),
                    before_revocations.len() <= revocations.len(),
                    revocations@.take(before_revocations.len() as int) == before_revocations,
                    revocations.len() == before_revocations.len() + i,
                    forall|j: int| before_revocations.len() <= j < revocations.len() ==>
                        (#[trigger] revoke_origins[j]).record == ordinal
                        && revoke_origins[j].index == j - before_revocations.len() && revocations@[j].sequence == sequence,
                    committed_revocations <= revocations.len(),
                    revoke_origins.len() == revocations.len(),
                    forall|j: int| 0 <= j < revoke_origins.len() ==>
                        revoke_origin_ok(journal@, blocks, start, seed, revocations@[j], #[trigger] revoke_origins[j]) && revoke_origins[j].record < visited,
                    forall|j: int| 0 <= j < committed_revocations ==> positions.dom().contains((#[trigger] revocations@[j]).sequence)
                && revoke_origins[j].record < positions[revocations@[j].sequence],
                    forall|j: int| committed_revocations <= j < revocations.len() ==> (#[trigger] revocations@[j]).sequence == sequence,
                    raw@ == block_at(journal@, blocks, start, ordinal), ordinal < blocks - 1, ordinal < visited,
                    revoke::header(raw@, sequence, seed), revoke::count(raw@) == targets.len(),
                    revoke::targets_bounded(raw@, revoke::count(raw@), layout.view().fs_blocks),
                    forall|j: int| 0 <= j < targets.len() ==> (#[trigger] targets@[j]) as nat == bytes::be32(raw@, 16 + 4 * j),
                    forall|j: int| 0 <= j < committed_revocations ==> (#[trigger] revocations@[j]).sequence < sequence,
                    layout.wf(), 0 < first <= sequence,
                    forall|j: int| 0 <= j < revocations.len() ==> layout.allowed((#[trigger] revocations@[j]).block)
                        && first <= revocations@[j].sequence <= sequence,
                decreases targets.len() - i,
            {
                assert(scan_budget::target_allowed(layout.view(), targets@[i as int]));
                assert(layout.allowed(targets@[i as int]));
                let ghost previous_revocations = revocations@;
                let ghost previous_origins = revoke_origins;
                proof {
                    let origin = RevokeOrigin { record: ordinal, index: i as nat };
                    assert(revoke_origin_ok(journal@, blocks, start, seed,
                        replay::Revocation { block: targets@[i as int], sequence }, origin)) by { reveal(revoke_origin_ok); }
                    revoke_origins = revoke_origins.push(origin);
                }
                revocations.push(replay::Revocation { block: targets[i], sequence });
                proof {
                    assert forall|j: int| 0 <= j < committed_revocations implies
                        positions.dom().contains((#[trigger] revocations@[j]).sequence)
                        && revoke_origins[j].record < positions[revocations@[j].sequence] by {
                        assert(revocations@[j] == previous_revocations[j]);
                        assert(revoke_origins[j] == previous_origins[j]);
                        assert(positions.dom().contains(previous_revocations[j].sequence)
                            && previous_origins[j].record < positions[previous_revocations[j].sequence]);
                    }
                }
                i += 1;
            }
            proof {
                let record = scan_trace::Record { start: ordinal, end: visited, sequence, kind: 5,
                    writes: Seq::empty(), origins: Seq::empty(),
                    revocations: revocations@.subrange(before_revocations.len() as int, revocations.len() as int),
                    revoke_origins: revoke_origins.subrange(before_revocations.len() as int, revocations.len() as int) };
                assert(scan_trace::record_ok(record, source)) by { reveal(scan_trace::record_ok); }
                scan_trace::append_record(records, record, source);
                records = records.push(record);
            }
        } else if header.kind == 2 {
            if !jbd2::valid_commit(raw, sequence, seed) {
                proof {
                    termination = scan_stop::Stop::Commit { ordinal };
                    assert(scan_stop::at_boundary(termination, records, source, sequence)) by { reveal(scan_stop::at_boundary); }
                }
                stop = true; continue;
            }
            proof {
                let record = scan_trace::Record { start: ordinal, end: visited, sequence, kind: 2,
                    writes: Seq::empty(), origins: Seq::empty(), revocations: Seq::empty(), revoke_origins: Seq::empty() };
                assert(scan_trace::record_ok(record, source)) by { reveal(scan_trace::record_ok); }
                scan_trace::append_record(records, record, source);
                records = records.push(record);
                committed_records = records;
                let previous_positions = positions;
                positions = positions.insert(sequence, ordinal);
                assert forall|id: u32| #[trigger] positions.dom().contains(id) <==> first <= id <= sequence by { }
                assert forall|id: u32| positions.dom().contains(id) implies (#[trigger] positions[id]) < visited
                    && jbd2::commit_ok(block_at(journal@, blocks, start, positions[id]), id, seed) by {
                    if id != sequence { assert(positions[id] < ordinal); }
                }
                assert forall|j: int| 0 <= j < writes.len() implies
                    positions.dom().contains((#[trigger] writes@[j].view()).sequence)
                && origins[j].payload < positions[writes@[j].view().sequence] by {
                    if j < committed_writes {
                        assert(writes@[j].view().sequence < sequence);
                        assert(origins[j].payload < previous_positions[writes@[j].view().sequence]);
                    } else {
                        assert(writes@[j].view().sequence == sequence);
                        assert(origins[j].payload < ordinal);
                    }
                }
                assert forall|j: int| 0 <= j < revocations.len() implies
                    positions.dom().contains((#[trigger] revocations@[j]).sequence)
                && revoke_origins[j].record < positions[revocations@[j].sequence] by {
                    if j < committed_revocations {
                        assert(revocations@[j].sequence < sequence);
                        assert(revoke_origins[j].record < previous_positions[revocations@[j].sequence]);
                    } else {
                        assert(revocations@[j].sequence == sequence);
                        assert(revoke_origins[j].record < ordinal);
                    }
                }
            }
            committed_writes = writes.len();
            committed_revocations = revocations.len();
            committed += 1;
            sequence += 1;
            if sequence == 4294967295 {
                proof {
                    termination = scan_stop::Stop::Exhausted;
                    assert(scan_stop::at_boundary(termination, records, source, sequence)) by { reveal(scan_stop::at_boundary); }
                }
                stop = true;
            }
        } else { assert(false); return None; }
    }
    if !stop {
        proof {
            if can_scan { scan_budget::prefix_is_bounded(records, source); assert(false); }
        }
        return None;
    }
    while writes.len() > committed_writes
        invariant committed_writes <= writes.len(),
            scan_trace::writes(committed_records) == replay::images(writes@).take(committed_writes as int),
            origins.len() == writes.len(),
            forall|i: int| 0 <= i < origins.len() ==>
                origin_ok(journal@, blocks, start, uuid@, seed, layout.view(), writes@[i].view(), #[trigger] origins[i]),
            forall|i: int| 0 <= i < committed_writes ==> positions.dom().contains((#[trigger] writes@[i].view()).sequence)
                && origins[i].payload < positions[writes@[i].view().sequence],
            forall|i: int| 0 <= i < writes.len() ==> layout.allowed((#[trigger] writes@[i].view()).block)
                && writes@[i].view().image.len() == 4096 && first <= writes@[i].view().sequence <= sequence,
            forall|i: int| 0 <= i < committed_writes ==> (#[trigger] writes@[i].view()).sequence < sequence,
            forall|i: int| 0 < i < writes.len() ==> (#[trigger] writes@[i].view()).sequence >= writes@[i - 1].view().sequence,
        decreases writes.len() - committed_writes,
    {
        let ghost previous_writes = writes@;
        let ghost previous_origins = origins;
        writes.pop();
        proof {
            origins = origins.drop_last();
            assert forall|i: int| 0 <= i < committed_writes implies positions.dom().contains((#[trigger] writes@[i].view()).sequence)
                && origins[i].payload < positions[writes@[i].view().sequence] by {
                assert(writes@[i] == previous_writes[i]);
                assert(origins[i] == previous_origins[i]);
                assert(positions.dom().contains(previous_writes[i].view().sequence)
                    && previous_origins[i].payload < positions[previous_writes[i].view().sequence]);
            }
        }
    }
    while revocations.len() > committed_revocations
        invariant committed_revocations <= revocations.len(),
            scan_trace::revocations(committed_records) == revocations@.take(committed_revocations as int),
            revoke_origins.len() == revocations.len(),
            forall|i: int| 0 <= i < revoke_origins.len() ==>
                revoke_origin_ok(journal@, blocks, start, seed, revocations@[i], #[trigger] revoke_origins[i]),
            forall|i: int| 0 <= i < committed_revocations ==> positions.dom().contains((#[trigger] revocations@[i]).sequence)
                && revoke_origins[i].record < positions[revocations@[i].sequence],
            forall|i: int| 0 <= i < revocations.len() ==> layout.allowed((#[trigger] revocations@[i]).block)
                && first <= revocations@[i].sequence <= sequence,
            forall|i: int| 0 <= i < committed_revocations ==> (#[trigger] revocations@[i]).sequence < sequence,
        decreases revocations.len() - committed_revocations,
    {
        let ghost previous_revocations = revocations@;
        let ghost previous_origins = revoke_origins;
        revocations.pop();
        proof {
            revoke_origins = revoke_origins.drop_last();
            assert forall|i: int| 0 <= i < committed_revocations implies positions.dom().contains((#[trigger] revocations@[i]).sequence)
                && revoke_origins[i].record < positions[revocations@[i].sequence] by {
                assert(revocations@[i] == previous_revocations[i]);
                assert(revoke_origins[i] == previous_origins[i]);
                assert(positions.dom().contains(previous_revocations[i].sequence)
                    && previous_origins[i].record < positions[previous_revocations[i].sequence]);
            }
        }
    }
    let last = if committed == 0 { first } else { sequence - 1 };
    proof {
        assert(replay::images(writes@).take(committed_writes as int) =~= replay::images(writes@));
        assert(revocations@.take(committed_revocations as int) =~= revocations@);
        assert(scan_trace::writes(committed_records) == replay::images(writes@));
        assert(scan_trace::revocations(committed_records) == revocations@);
    }
    let ghost old_layout = layout;
    assert(replay::input_ok(replay::images(writes@), revocations@, &layout, first, last));
    let plan = match replay::build(layout, writes, revocations, first, last) {
        Some(plan) => plan, None => { return None; }
    };
    proof {
        assert(plan.layout().view() == old_layout.view());
        assert(scan_trace::committed_prefix(committed_records, source, plan.log(), plan.revocations()));
        assert(origins.len() == plan.log().len());
        assert(revoke_origins.len() == plan.revocations().len());
        assert forall|i: int| 0 <= i < origins.len() implies #[trigger]
            origin_ok(journal@, blocks, start, uuid@, seed, plan.layout().view(), plan.log()[i], origins[i]) by {
            assert(origin_ok(journal@, blocks, start, uuid@, seed, old_layout.view(), plan.log()[i], origins[i]));
        }
        assert forall|i: int| 0 <= i < revoke_origins.len() implies #[trigger]
            revoke_origin_ok(journal@, blocks, start, seed, plan.revocations()[i], revoke_origins[i]) by {
            assert(revoke_origin_ok(journal@, blocks, start, seed, plan.revocations()[i], revoke_origins[i]));
        }
    }
    let result = Scan { plan, first, next: sequence, committed, consumed: visited, commit_positions: Ghost(positions),
        origins: Ghost(origins), revoke_origins: Ghost(revoke_origins), records: Ghost(committed_records),
        scanned: Ghost(records), termination: Ghost(termination) };
    assert(result.certificate(source));
    assert(result.maximal(source));
    Some(result)
}

pub proof fn recovered_input_is_unique_for_the_frozen_journal(a: &Scan, b: &Scan, source: scan_trace::Source)
    requires source.start != 0, a.certificate(source), a.maximal(source), b.certificate(source), b.maximal(source),
    ensures a.plan().log() == b.plan().log(), a.plan().revocations() == b.plan().revocations(), a.next() == b.next(),
{
    scan_stop::maximal_canonical_prefix_is_unique(a.scanned(), b.scanned(), a.termination(), b.termination(),
        source, a.next(), b.next());
    if a.records().len() < b.records().len() {
        let i = b.records().len() as int - 1;
        assert(b.records()[i].kind == 2);
        assert(b.scanned()[i] == b.records()[i]);
        assert(a.scanned()[i].kind != 2);
    } else if b.records().len() < a.records().len() {
        let i = a.records().len() as int - 1;
        assert(a.records()[i].kind == 2);
        assert(a.scanned()[i] == a.records()[i]);
        assert(b.scanned()[i].kind != 2);
    }
    assert(a.records() == b.records());
}

}
