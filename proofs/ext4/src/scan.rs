// SPDX-License-Identifier: MPL-2.0

//! Bounded scanning of a frozen internal-journal snapshot. Only committed
//! transaction prefixes enter the replay plan; an incomplete tail is dropped.
//! Byte recognition is not authentication or a device-persistence guarantee.

use vstd::prelude::*;
use crate::{bytes, crc, descriptor, jbd2, journal_superblock, layout::{JournalLayout, LayoutView}, replay, revoke, ring};

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

pub struct Scan {
    plan: replay::ReplayPlan,
    first: u32,
    next: u32,
    committed: u32,
    consumed: u32,
    commit_positions: Ghost<Map<u32, u32>>,
    origins: Ghost<Seq<Origin>>,
    revoke_origins: Ghost<Seq<RevokeOrigin>>,
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

#[verifier::rlimit(50)]
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
                uuid@, crc::fold(0xffffffff, uuid@)),
        None => true,
    },
{
    if !layout.valid() { return None; }
    let blocks = layout.blocks();
    if journal.len() as u64 != blocks as u64 * 4096 { return None; }
    let info = match journal_superblock::parse(&journal[0..1024], uuid, blocks) {
        Some(info) => info, None => { return None; }
    };
    let first = info.sequence;
    let seed = info.uuid_seed;
    if info.start == 0 {
        let writes = Vec::new();
        let revocations = Vec::new();
        let plan = replay::build(layout, writes, revocations, 1, 1).unwrap();
        return Some(Scan { plan, first, next: first, committed: 0, consumed: 0,
            commit_positions: Ghost(Map::empty()), origins: Ghost(Seq::empty()), revoke_origins: Ghost(Seq::empty()) });
    }
    if !info.csum_v3 || first == 4294967295 { return None; }
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
    while !stop && visited < blocks - 1
        invariant layout.wf(), layout.view().journal_blocks == blocks, 1024 <= blocks <= 32768,
            journal.len() as nat == blocks as nat * 4096, 1 <= start < blocks,
            0 < first <= sequence, sequence as nat == first as nat + committed as nat,
            committed <= visited <= blocks - 1, writes.len() + revocations.len() <= 4096,
            committed_writes <= writes.len(), committed_revocations <= revocations.len(),
            origins.len() == writes.len(), revoke_origins.len() == revocations.len(),
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
        let raw = read_block(journal, blocks, start, visited);
        visited += 1;
        let header = match jbd2::parse_header(raw, sequence) {
            Some(header) => header, None => { stop = true; continue; }
        };
        if header.kind == 1 {
            let desc = match descriptor::parse(raw, uuid, sequence, layout.filesystem_blocks(), seed) {
                Some(desc) => desc, None => { stop = true; continue; }
            };
            let tags = desc.tags();
            if tags.len() as u32 > blocks - 1 - visited { return None; }
            let mut i = 0usize;
            while i < tags.len() && !stop
                invariant i <= tags.len() <= 250,
                    layout.wf(), blocks == layout.view().journal_blocks, 1024 <= blocks <= 32768,
                    journal.len() as nat == blocks as nat * 4096, 1 <= start < blocks,
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
                if writes.len() + revocations.len() == 4096 { return None; }
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
                    None => { stop = true; },
                }
                i += 1;
            }
        } else if header.kind == 5 {
            if !info.revoke { return None; }
            let records = match revoke::parse(raw, sequence, layout.filesystem_blocks(), seed) {
                Some(records) => records, None => { stop = true; continue; }
            };
            let targets = records.blocks();
            let mut i = 0usize;
            while i < targets.len()
                invariant i <= targets.len() <= 1019, writes.len() + revocations.len() <= 4096,
                    committed_revocations <= revocations.len(),
                    revoke_origins.len() == revocations.len(),
                    forall|j: int| 0 <= j < revoke_origins.len() ==>
                        revoke_origin_ok(journal@, blocks, start, seed, revocations@[j], #[trigger] revoke_origins[j]) && revoke_origins[j].record < visited,
                    forall|j: int| 0 <= j < committed_revocations ==> positions.dom().contains((#[trigger] revocations@[j]).sequence)
                && revoke_origins[j].record < positions[revocations@[j].sequence],
                    forall|j: int| committed_revocations <= j < revocations.len() ==> (#[trigger] revocations@[j]).sequence == sequence,
                    raw@ == block_at(journal@, blocks, start, ordinal), ordinal < blocks - 1, ordinal < visited,
                    revoke::header(raw@, sequence, seed), revoke::count(raw@) == targets.len(),
                    forall|j: int| 0 <= j < targets.len() ==> (#[trigger] targets@[j]) as nat == bytes::be32(raw@, 16 + 4 * j),
                    forall|j: int| 0 <= j < committed_revocations ==> (#[trigger] revocations@[j]).sequence < sequence,
                    layout.wf(), 0 < first <= sequence,
                    forall|j: int| 0 <= j < revocations.len() ==> layout.allowed((#[trigger] revocations@[j]).block)
                        && first <= revocations@[j].sequence <= sequence,
                decreases targets.len() - i,
            {
                if writes.len() + revocations.len() == 4096 || !layout.allows_target(targets[i]) { return None; }
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
        } else if header.kind == 2 {
            if !jbd2::valid_commit(raw, sequence, seed) { stop = true; continue; }
            proof {
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
            if sequence == 4294967295 { stop = true; }
        } else { stop = true; }
    }
    if !stop { return None; } // A fully occupied ring has no proved stopping boundary.
    while writes.len() > committed_writes
        invariant committed_writes <= writes.len(),
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
    let ghost old_layout = layout;
    let plan = match replay::build(layout, writes, revocations, first, last) {
        Some(plan) => plan, None => { return None; }
    };
    proof {
        assert(plan.layout().view() == old_layout.view());
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
    Some(Scan { plan, first, next: sequence, committed, consumed: visited, commit_positions: Ghost(positions),
        origins: Ghost(origins), revoke_origins: Ghost(revoke_origins) })
}

}
