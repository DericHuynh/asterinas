// SPDX-License-Identifier: MPL-2.0

//! Composition of physical successful writer generations and a final crash cut.
//! A new generation is prepared against its predecessor's actual durable disk.
//! Sequence selection remains header-based; no consecutive-ID premise is used.

use vstd::prelude::*;
use crate::{crc, layout::{JournalLayout, LayoutView}, recovery_device, replay_refinement::{self, Disk}, scan,
    transaction_refinement, write_device::{self, Machine}, write_io, write_media, write_recognition, write_recovery};

verus! {

#[verifier::opaque]
pub open spec fn logical(initial: Disk, images: Seq<write_io::Images>) -> Disk
    decreases images.len(),
{
    if images.len() == 0 { initial }
    else { replay_refinement::chronological(logical(initial, images.drop_last()),
        transaction_refinement::log(images.last().tx), Seq::empty()) }
}

pub open spec fn home_region(layout: LayoutView, block: u32) -> bool {
    block != 0 && !(layout.start <= block < layout.start as int + layout.journal_blocks)
}

#[verifier::opaque]
pub open spec fn completed(initial: Disk, layout: LayoutView, uuid: Seq<u8>, partition_bytes: u64,
    images: Seq<write_io::Images>, media: Seq<Disk>, machines: Seq<Machine>) -> bool {
    &&& media.len() == images.len() + 1 && machines.len() == images.len() && media[0] == initial
    &&& (forall|i: int| 0 <= i < images.len() ==> {
        &&& #[trigger] write_recognition::context(media[i], images[i])
        &&& images[i].tx.layout == layout && images[i].tx.uuid == uuid && images[i].partition_bytes == partition_bytes
        &&& write_device::inv(machines[i], images[i].tx.payloads.len())
        &&& machines[i].io.phase is Done && !machines[i].io.pending && !machines[i].io.faulted
        &&& media[i + 1] == write_media::disk(machines[i], media[i], images[i])
    })
}

pub proof fn initialization(initial: Disk, layout: LayoutView, uuid: Seq<u8>, partition_bytes: u64)
    ensures completed(initial, layout, uuid, partition_bytes, Seq::empty(), seq![initial], Seq::empty()),
{
    reveal(completed);
}

pub proof fn append_successful_generation(initial: Disk, layout: LayoutView, uuid: Seq<u8>, partition_bytes: u64,
    images: Seq<write_io::Images>, media: Seq<Disk>, machines: Seq<Machine>, v: write_io::Images, m: Machine)
    requires completed(initial, layout, uuid, partition_bytes, images, media, machines),
        write_recognition::context(media.last(), v), v.tx.layout == layout, v.tx.uuid == uuid, v.partition_bytes == partition_bytes,
        write_device::inv(m, v.tx.payloads.len()), m.io.phase is Done, !m.io.pending, !m.io.faulted,
    ensures completed(initial, layout, uuid, partition_bytes, images.push(v),
        media.push(write_media::disk(m, media.last(), v)), machines.push(m)),
{
    reveal(completed);
    assert forall|i: int| 0 <= i < images.len() + 1 implies {
        &&& #[trigger] write_recognition::context(media.push(write_media::disk(m, media.last(), v))[i], images.push(v)[i])
        &&& images.push(v)[i].tx.layout == layout && images.push(v)[i].tx.uuid == uuid
            && images.push(v)[i].partition_bytes == partition_bytes
        &&& write_device::inv(machines.push(m)[i], images.push(v)[i].tx.payloads.len())
        &&& machines.push(m)[i].io.phase is Done && !machines.push(m)[i].io.pending && !machines.push(m)[i].io.faulted
        &&& media.push(write_media::disk(m, media.last(), v))[i + 1]
            == write_media::disk(machines.push(m)[i], media.push(write_media::disk(m, media.last(), v))[i], images.push(v)[i])
    } by {
        if i < images.len() { assert(write_recognition::context(media[i], images[i])); }
    }
}

pub proof fn every_completed_cut_has_exact_acknowledged_home_bytes(initial: Disk, layout: LayoutView,
    uuid: Seq<u8>, partition_bytes: u64, images: Seq<write_io::Images>, media: Seq<Disk>, machines: Seq<Machine>, cut: nat, block: u32)
    requires completed(initial, layout, uuid, partition_bytes, images, media, machines), cut <= images.len(),
        initial.dom().contains(block), home_region(layout, block),
    ensures media[cut as int].dom() == initial.dom(), logical(initial, images.take(cut as int)).dom() == initial.dom(),
        media[cut as int][block] == logical(initial, images.take(cut as int))[block],
    decreases cut,
{
    hide(crc::fold);
    hide(replay_refinement::chronological);
    reveal(completed);
    if cut == 0 {
        assert(images.take(0) =~= Seq::<write_io::Images>::empty());
        reveal(logical);
    } else {
        every_completed_cut_has_exact_acknowledged_home_bytes(initial, layout, uuid, partition_bytes,
            images, media, machines, (cut - 1) as nat, block);
        let i = cut as int - 1;
        let v = images[i];
        let m = machines[i];
        let previous = logical(initial, images.take(i));
        let after = logical(initial, images.take(cut as int));
        let log = transaction_refinement::log(v.tx);
        assert(write_recognition::context(media[i], v));
        write_device::successful_completion_is_durable_and_has_no_late_persistence(m, v.tx.payloads.len());
        assert(m.stable.contains(9 + 2 * v.tx.payloads.len()));
        write_recovery::a_retired_writer_has_complete_home_after_bytes(m, media[i], v, block);
        write_media::apply_preserves_domain(media[i], v, m.stable, write_device::total(v.tx.payloads.len()));
        write_recovery::original_targets_exist(media[i], v);
        assert(replay_refinement::all_targets_exist(previous, log));
        replay_refinement::chronological_lookup(media[i], log, Seq::empty(), block);
        replay_refinement::chronological_lookup(previous, log, Seq::empty(), block);
        assert(after == replay_refinement::chronological(previous, log, Seq::empty())) by {
            assert(images.take(cut as int).drop_last() =~= images.take(i));
            assert(images.take(cut as int).last() == v);
            reveal(logical);
        }
    }
}

pub proof fn completed_generations_cannot_persist_again(initial: Disk, layout: LayoutView, uuid: Seq<u8>, partition_bytes: u64,
    images: Seq<write_io::Images>, media: Seq<Disk>, machines: Seq<Machine>)
    requires completed(initial, layout, uuid, partition_bytes, images, media, machines),
    ensures forall|i: int, k: nat| 0 <= i < machines.len() ==>
        !#[trigger] write_device::enabled(machines[i], write_device::Event::Persist(k)),
{
    reveal(completed);
    assert forall|i: int, k: nat| 0 <= i < machines.len() implies
        !#[trigger] write_device::enabled(machines[i], write_device::Event::Persist(k)) by {
        assert(write_recognition::context(media[i], images[i]));
        write_device::successful_completion_is_durable_and_has_no_late_persistence(machines[i], images[i].tx.payloads.len());
    }
}

pub proof fn recovery_after_a_physical_history_includes_every_acknowledgement(initial: Disk, layout: &JournalLayout,
    uuid: Seq<u8>, partition_bytes: u64, images: Seq<write_io::Images>, media: Seq<Disk>, machines: Seq<Machine>,
    v: write_io::Images, m: Machine, result: &scan::Scan, recovery: recovery_device::Machine, tail: Seq<u8>, block: u32)
    requires completed(initial, layout.view(), uuid, partition_bytes, images, media, machines), layout.wf(),
        write_recognition::context(media.last(), v), v.tx.layout == layout.view(), v.tx.uuid == uuid, v.partition_bytes == partition_bytes,
        write_device::inv(m, v.tx.payloads.len()), write_recovery::returned(result, write_recovery::source(m, media.last(), v, layout)),
        recovery_device::inv(recovery, write_media::disk(m, media.last(), v), result.plan(), v.journal_block, tail),
        recovery.io.phase == 4, !recovery.io.pending, !recovery.io.faulted,
        initial.dom().contains(block), home_region(layout.view(), block),
    ensures recovery.stable[block] == if m.stable.contains(6 + v.tx.payloads.len()) {
        replay_refinement::chronological(logical(initial, images), transaction_refinement::log(v.tx), Seq::empty())[block]
    } else { logical(initial, images)[block] },
{
    hide(crc::fold);
    hide(replay_refinement::chronological);
    reveal(completed);
    every_completed_cut_has_exact_acknowledged_home_bytes(initial, layout.view(), uuid, partition_bytes,
        images, media, machines, images.len(), block);
    assert(images.take(images.len() as int) =~= images);
    write_recovery::successful_recovery_of_every_writer_cut_has_before_or_after_home_bytes(m, media.last(), v,
        layout, result, recovery, tail, block);
    if m.stable.contains(6 + v.tx.payloads.len()) {
        let log = transaction_refinement::log(v.tx);
        write_recovery::original_targets_exist(media.last(), v);
        assert(replay_refinement::all_targets_exist(logical(initial, images), log));
        replay_refinement::chronological_lookup(media.last(), log, Seq::empty(), block);
        replay_refinement::chronological_lookup(logical(initial, images), log, Seq::empty(), block);
    }
}

}
