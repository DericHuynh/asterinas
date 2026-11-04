// SPDX-License-Identifier: MPL-2.0

//! Concurrent file-block lifetime specification: compatible read pins,
//! exclusive per-block CPU writers, generation changes and initialized
//! publication. This is not an OSTD lock/loan implementation or a device
//! persistence model. Extent-tree, DMA and journal-version refinement is open.

use vstd::prelude::*;
use crate::ownership::Owner;

verus! {

pub enum Exposure { Private, Unwritten, Published }
pub struct Slot { pub owner: Option<Owner>, pub epoch: nat, pub initialized: bool, pub exposure: Exposure, pub bytes: Seq<u8> }
pub struct ReadPin { pub volume: nat, pub block: u64, pub epoch: nat, pub owner: Owner, pub actor: nat }
#[verifier::ext_equal]
pub struct WriteLease { pub block: u64, pub volume: nat, pub actor: nat, pub serial: nat, pub epoch: nat }
pub struct State {
    pub volume: nat, pub blocks: u64, pub block_bytes: u32, pub slots: Map<u64, Slot>, pub readers: Map<nat, ReadPin>,
    pub writers: Map<u64, WriteLease>, pub next_pin: nat, pub next_writer: nat,
}

pub open spec fn valid_block_size(bytes: u32) -> bool {
    crate::block_size::accepted(bytes as nat)
}

pub open spec fn zeros(bytes: u32) -> Seq<u8> { Seq::new(bytes as nat, |i: int| 0u8) }

pub open spec fn slot_valid(slot: Slot, block_bytes: u32) -> bool {
    &&& slot.bytes.len() == block_bytes
    &&& (slot.owner.is_none() ==> !slot.initialized && slot.exposure == Exposure::Private)
    &&& (slot.exposure != Exposure::Private ==> slot.owner.is_some())
    &&& (slot.exposure == Exposure::Published ==> slot.initialized)
}

pub open spec fn allocated(s: State, block: u64) -> bool {
    s.slots.dom().contains(block) && s.slots[block].owner.is_some()
}

pub open spec fn no_readers(s: State, block: u64) -> bool {
    forall|id: nat| s.readers.dom().contains(id) ==> (#[trigger] s.readers[id]).block != block
}

pub open spec fn writer(s: State, block: u64, lease: WriteLease) -> bool {
    &&& allocated(s, block) && s.writers.dom().contains(block) && s.writers[block] == lease
    &&& lease.block == block && lease.actor > 0 && lease.volume == s.volume && lease.epoch == s.slots[block].epoch && lease.serial < s.next_writer
}

pub open spec fn pin_valid(s: State, pin: ReadPin) -> bool {
    &&& pin.volume == s.volume && pin.actor > 0 && allocated(s, pin.block)
    &&& s.slots[pin.block].owner == Some(pin.owner) && s.slots[pin.block].epoch == pin.epoch
    &&& s.slots[pin.block].initialized && s.slots[pin.block].exposure == Exposure::Published
    &&& !s.writers.dom().contains(pin.block)
}

#[verifier::opaque]
pub open spec fn inv(s: State) -> bool {
    &&& s.blocks > 0 && valid_block_size(s.block_bytes)
    &&& (forall|block: u64| #[trigger] s.slots.dom().contains(block) ==> block < s.blocks && slot_valid(s.slots[block], s.block_bytes))
    &&& (forall|id: nat| #[trigger] s.readers.dom().contains(id) ==> id < s.next_pin && pin_valid(s, s.readers[id]))
    &&& (forall|block: u64| #[trigger] s.writers.dom().contains(block) ==> writer(s, block, s.writers[block]) && no_readers(s, block))
}

pub enum Event {
    Allocate(u64, Owner), ClaimWrite(u64, nat), ReleaseWrite(u64, WriteLease), Zero(u64, WriteLease), Write(u64, WriteLease, Seq<u8>),
    PublishUnwritten(u64, WriteLease), PublishInitialized(u64, WriteLease), Withdraw(u64, WriteLease), Free(u64),
    PinRead(u64, nat, Owner, nat, nat), Unpin(nat, nat),
}

pub open spec fn enabled(s: State, event: Event) -> bool {
    match event {
        Event::Allocate(b, owner) => s.slots.dom().contains(b) && owner.inode > 0 && s.slots[b].owner.is_none()
            && !s.writers.dom().contains(b) && no_readers(s, b),
        Event::ClaimWrite(b, actor) => allocated(s, b) && actor > 0 && !s.writers.dom().contains(b) && no_readers(s, b),
        Event::ReleaseWrite(b, actor) | Event::Zero(b, actor) | Event::Withdraw(b, actor) => writer(s, b, actor),
        Event::Write(b, actor, bytes) => writer(s, b, actor) && s.slots[b].initialized && bytes.len() == s.block_bytes,
        Event::PublishUnwritten(b, actor) => writer(s, b, actor) && s.slots[b].exposure == Exposure::Private,
        Event::PublishInitialized(b, actor) => writer(s, b, actor) && s.slots[b].initialized,
        Event::Free(b) => allocated(s, b) && s.slots[b].exposure == Exposure::Private && !s.writers.dom().contains(b) && no_readers(s, b),
        Event::PinRead(b, actor, owner, epoch, volume) => volume == s.volume && allocated(s, b) && s.slots[b].owner == Some(owner) && s.slots[b].exposure == Exposure::Published && s.slots[b].epoch == epoch
            && actor > 0 && !s.writers.dom().contains(b),
        Event::Unpin(id, actor) => s.readers.dom().contains(id) && s.readers[id].actor == actor,
    }
}

pub open spec fn replace_slot(s: State, block: u64, slot: Slot) -> State { State { slots: s.slots.insert(block, slot), ..s } }

pub open spec fn next(s: State, event: Event) -> State {
    match event {
        Event::Allocate(b, owner) => replace_slot(s, b, Slot { owner: Some(owner), epoch: s.slots[b].epoch + 1,
            initialized: false, exposure: Exposure::Private, bytes: s.slots[b].bytes }),
        Event::ClaimWrite(b, actor) => State { writers: s.writers.insert(b,
            WriteLease { block: b, volume: s.volume, actor, serial: s.next_writer, epoch: s.slots[b].epoch }), next_writer: s.next_writer + 1, ..s },
        Event::ReleaseWrite(b, _) => State { writers: s.writers.remove(b), ..s },
        Event::Zero(b, _) => replace_slot(s, b, Slot { initialized: true, bytes: zeros(s.block_bytes), ..s.slots[b] }),
        Event::Write(b, _, bytes) => replace_slot(s, b, Slot { bytes, ..s.slots[b] }),
        Event::PublishUnwritten(b, _) => replace_slot(s, b, Slot { exposure: Exposure::Unwritten, ..s.slots[b] }),
        Event::PublishInitialized(b, _) => replace_slot(s, b, Slot { exposure: Exposure::Published, ..s.slots[b] }),
        Event::Withdraw(b, _) => replace_slot(s, b, Slot { exposure: Exposure::Private, ..s.slots[b] }),
        Event::Free(b) => replace_slot(s, b, Slot { owner: None, initialized: false, exposure: Exposure::Private, epoch: s.slots[b].epoch + 1, ..s.slots[b] }),
        Event::PinRead(b, actor, owner, epoch, volume) => State { readers: s.readers.insert(s.next_pin,
            ReadPin { volume, block: b, epoch, owner, actor }), next_pin: s.next_pin + 1, ..s },
        Event::Unpin(id, _) => State { readers: s.readers.remove(id), ..s },
    }
}

proof fn slot_properties(s: State, block: u64)
    requires inv(s), s.slots.dom().contains(block),
    ensures block < s.blocks, slot_valid(s.slots[block], s.block_bytes),
{
    reveal(inv);
}

proof fn reader_properties(s: State, id: nat)
    requires inv(s), s.readers.dom().contains(id),
    ensures id < s.next_pin, pin_valid(s, s.readers[id]),
{
    reveal(inv);
}

proof fn writer_properties(s: State, block: u64)
    requires inv(s), s.writers.dom().contains(block),
    ensures writer(s, block, s.writers[block]), no_readers(s, block),
{
    reveal(inv);
}

proof fn isolated_slot_update(s: State, b: u64, slot: Slot)
    requires inv(s), s.slots.dom().contains(b), no_readers(s, b), slot_valid(slot, s.block_bytes),
        s.writers.dom().contains(b) ==> slot.owner.is_some() && slot.epoch == s.slots[b].epoch,
    ensures inv(replace_slot(s, b, slot)),
{
    reveal(inv);
    let t = replace_slot(s, b, slot);
    assert(t.slots.dom() =~= s.slots.dom());
    assert forall|block: u64| #[trigger] t.slots.dom().contains(block) implies block < t.blocks && slot_valid(t.slots[block], t.block_bytes) by {
        if block != b { assert(t.slots[block] == s.slots[block]); }
        slot_properties(s, block);
    }
    assert forall|id: nat| #[trigger] t.readers.dom().contains(id) implies id < t.next_pin && pin_valid(t, t.readers[id]) by {
        reader_properties(s, id);
        assert(s.readers[id].block != b);
    }
    assert forall|block: u64| #[trigger] t.writers.dom().contains(block) implies writer(t, block, t.writers[block]) && no_readers(t, block) by {
        writer_properties(s, block);
    }
}

pub proof fn every_event_preserves(s: State, event: Event)
    requires inv(s), enabled(s, event),
    ensures inv(next(s, event)), next(s, event).slots.dom() == s.slots.dom(),
        next(s, event).volume == s.volume, next(s, event).blocks == s.blocks, next(s, event).block_bytes == s.block_bytes,
        next(s, event).next_pin >= s.next_pin, next(s, event).next_writer >= s.next_writer,
{
    reveal(inv);
    let t = next(s, event);
    match event {
        Event::Allocate(b, _) | Event::Zero(b, _) | Event::Write(b, _, _)
            | Event::PublishUnwritten(b, _) | Event::PublishInitialized(b, _) | Event::Withdraw(b, _) | Event::Free(b) => {
            slot_properties(s, b);
            if s.writers.dom().contains(b) { writer_properties(s, b); }
            assert(no_readers(s, b));
            isolated_slot_update(s, b, t.slots[b]);
            assert(t == replace_slot(s, b, t.slots[b]));
        },
        Event::ClaimWrite(b, actor) => {
            assert forall|id: nat| #[trigger] t.readers.dom().contains(id) implies id < t.next_pin && pin_valid(t, t.readers[id]) by {
                reader_properties(s, id);
                assert(s.readers[id].block != b);
            }
            assert forall|block: u64| #[trigger] t.writers.dom().contains(block) implies writer(t, block, t.writers[block]) && no_readers(t, block) by {
                if block != b { writer_properties(s, block); }
            }
        },
        Event::ReleaseWrite(_, _) => {
            assert forall|id: nat| #[trigger] t.readers.dom().contains(id) implies id < t.next_pin && pin_valid(t, t.readers[id]) by {
                reader_properties(s, id);
            }
            assert forall|block: u64| #[trigger] t.writers.dom().contains(block) implies writer(t, block, t.writers[block]) && no_readers(t, block) by {
                writer_properties(s, block);
            }
        },
        Event::PinRead(b, actor, owner, epoch, volume) => {
            slot_properties(s, b);
            if s.readers.dom().contains(s.next_pin) { reader_properties(s, s.next_pin); }
            assert(!s.readers.dom().contains(s.next_pin));
            assert forall|id: nat| #[trigger] t.readers.dom().contains(id) implies id < t.next_pin && pin_valid(t, t.readers[id]) by {
                if id != s.next_pin { reader_properties(s, id); }
            }
            assert forall|block: u64| #[trigger] t.writers.dom().contains(block) implies writer(t, block, t.writers[block]) && no_readers(t, block) by {
                writer_properties(s, block);
                assert(block != b);
                assert forall|id: nat| t.readers.dom().contains(id) implies (#[trigger] t.readers[id]).block != block by {
                    if id != s.next_pin { assert(s.readers[id].block != block); }
                }
            }
        },
        Event::Unpin(_, _) => {
            assert forall|block: u64| #[trigger] t.writers.dom().contains(block) implies writer(t, block, t.writers[block]) && no_readers(t, block) by {
                writer_properties(s, block);
            }
        },
    }
}

pub proof fn a_reader_excludes_cpu_write_and_reuse(s: State, id: nat, actor: nat)
    requires inv(s), s.readers.dom().contains(id),
    ensures !enabled(s, Event::ClaimWrite(s.readers[id].block, actor)),
        !enabled(s, Event::Free(s.readers[id].block)),
        s.slots[s.readers[id].block].owner == Some(s.readers[id].owner),
        s.slots[s.readers[id].block].epoch == s.readers[id].epoch,
{
    reveal(inv);
    reader_properties(s, id);
}

pub proof fn unwritten_and_private_blocks_do_not_grant_a_read_pin(s: State, block: u64, actor: nat, owner: Owner, epoch: nat)
    requires s.slots.dom().contains(block), s.slots[block].exposure != Exposure::Published,
    ensures !enabled(s, Event::PinRead(block, actor, owner, epoch, s.volume)),
{
}

pub proof fn a_stale_allocation_epoch_cannot_pin(s: State, block: u64, actor: nat, owner: Owner, epoch: nat)
    requires s.slots.dom().contains(block), epoch != s.slots[block].epoch,
    ensures !enabled(s, Event::PinRead(block, actor, owner, epoch, s.volume)),
{
}

pub proof fn a_foreign_volume_request_cannot_pin(s: State, block: u64, actor: nat, owner: Owner, epoch: nat, volume: nat)
    requires volume != s.volume,
    ensures !enabled(s, Event::PinRead(block, actor, owner, epoch, volume)),
{
}

pub proof fn a_writer_lease_cannot_authorize_another_block_or_volume(s: State, block: u64, lease: WriteLease)
    requires lease.block != block || lease.volume != s.volume,
    ensures !writer(s, block, lease),
{
}

pub proof fn writer_leases_for_one_block_are_identical(s: State, block: u64, a: WriteLease, b: WriteLease)
    requires writer(s, block, a), writer(s, block, b),
    ensures a == b,
{
}

pub proof fn release_and_reacquisition_reject_the_old_writer_lease(s: State, block: u64, lease: WriteLease)
    requires inv(s), writer(s, block, lease),
    ensures {
        let released = next(s, Event::ReleaseWrite(block, lease));
        let reacquired = next(released, Event::ClaimWrite(block, lease.actor));
        &&& enabled(released, Event::ClaimWrite(block, lease.actor)) && inv(reacquired)
        &&& !writer(reacquired, block, lease)
        &&& reacquired.writers[block].serial > lease.serial
    },
{
    writer_properties(s, block);
    every_event_preserves(s, Event::ReleaseWrite(block, lease));
    let released = next(s, Event::ReleaseWrite(block, lease));
    every_event_preserves(released, Event::ClaimWrite(block, lease.actor));
}

pub proof fn released_pin_ids_never_return(s: State, event: Event, id: nat)
    requires inv(s), enabled(s, event), id < s.next_pin, !s.readers.dom().contains(id),
    ensures id < next(s, event).next_pin, !next(s, event).readers.dom().contains(id),
{
    every_event_preserves(s, event);
}

pub proof fn initialization_transition_zeroes_previous_contents(s: State, event: Event, block: u64)
    requires enabled(s, event), s.slots.dom().contains(block), !s.slots[block].initialized,
        next(s, event).slots[block].initialized,
    ensures next(s, event).slots[block].bytes == zeros(s.block_bytes),
{
    match event {
        Event::Zero(b, _) => { if b != block { assert(next(s, event).slots[block] == s.slots[block]); } },
        _ => { },
    }
}

pub proof fn allocation_after_free_cannot_publish_previous_bytes(s: State, block: u64, owner: Owner, actor: nat, epoch: nat)
    requires inv(s), enabled(s, Event::Free(block)), owner.inode > 0,
    ensures {
        let freed = next(s, Event::Free(block));
        let allocated = next(freed, Event::Allocate(block, owner));
        &&& enabled(freed, Event::Allocate(block, owner)) && inv(allocated)
        &&& allocated.slots[block].epoch == s.slots[block].epoch + 2
        &&& allocated.slots[block].bytes == s.slots[block].bytes
        &&& !allocated.slots[block].initialized && allocated.slots[block].exposure == Exposure::Private
        &&& !enabled(allocated, Event::PinRead(block, actor, owner, epoch, s.volume))
    },
{
    every_event_preserves(s, Event::Free(block));
    every_event_preserves(next(s, Event::Free(block)), Event::Allocate(block, owner));
}

pub proof fn disjoint_writes_commute(s: State, b: u64, c: u64, a: WriteLease, d: WriteLease, x: Seq<u8>, y: Seq<u8>)
    requires inv(s), b != c, enabled(s, Event::Write(b, a, x)), enabled(s, Event::Write(c, d, y)),
    ensures enabled(next(s, Event::Write(b, a, x)), Event::Write(c, d, y)),
        enabled(next(s, Event::Write(c, d, y)), Event::Write(b, a, x)),
        next(next(s, Event::Write(b, a, x)), Event::Write(c, d, y)) == next(next(s, Event::Write(c, d, y)), Event::Write(b, a, x)),
        inv(next(next(s, Event::Write(b, a, x)), Event::Write(c, d, y))),
{
    every_event_preserves(s, Event::Write(b, a, x));
    every_event_preserves(next(s, Event::Write(b, a, x)), Event::Write(c, d, y));
    assert(next(next(s, Event::Write(b, a, x)), Event::Write(c, d, y)).slots
        =~= next(next(s, Event::Write(c, d, y)), Event::Write(b, a, x)).slots);
}

pub open spec fn execution(states: Seq<State>, events: Seq<Event>) -> bool {
    &&& states.len() == events.len() + 1
    &&& forall|i: int| 0 <= i < events.len() ==> enabled(states[i], #[trigger] events[i]) && states[i + 1] == next(states[i], events[i])
}

proof fn at_cut(states: Seq<State>, events: Seq<Event>, cut: nat)
    requires execution(states, events), inv(states[0]), cut < states.len(),
    ensures inv(states[cut as int]),
    decreases cut,
{
    if cut > 0 {
        assert(0 <= cut as int - 1 < events.len());
        assert(enabled(states[cut as int - 1], events[cut as int - 1])
            && states[cut as int] == next(states[cut as int - 1], events[cut as int - 1]));
        at_cut(states, events, (cut - 1) as nat);
        every_event_preserves(states[cut as int - 1], events[cut as int - 1]);
    }
}

proof fn retired_at_cut(states: Seq<State>, events: Seq<Event>, id: nat, cut: nat)
    requires execution(states, events), inv(states[0]), cut < states.len(),
        id < states[0].next_pin, !states[0].readers.dom().contains(id),
    ensures id < states[cut as int].next_pin, !states[cut as int].readers.dom().contains(id),
    decreases cut,
{
    if cut > 0 {
        assert(0 <= cut as int - 1 < events.len());
        assert(enabled(states[cut as int - 1], events[cut as int - 1])
            && states[cut as int] == next(states[cut as int - 1], events[cut as int - 1]));
        retired_at_cut(states, events, id, (cut - 1) as nat);
        at_cut(states, events, (cut - 1) as nat);
        released_pin_ids_never_return(states[cut as int - 1], events[cut as int - 1], id);
    }
}

pub proof fn retired_read_pins_stay_retired_in_every_interleaving(states: Seq<State>, events: Seq<Event>, id: nat)
    requires execution(states, events), inv(states[0]), id < states[0].next_pin, !states[0].readers.dom().contains(id),
    ensures forall|i: int| 0 <= i < states.len() ==> id < #[trigger] states[i].next_pin,
        forall|i: int| 0 <= i < states.len() ==> !#[trigger] states[i].readers.dom().contains(id),
{
    assert forall|i: int| 0 <= i < states.len() implies id < #[trigger] states[i].next_pin by {
        retired_at_cut(states, events, id, i as nat);
    }
    assert forall|i: int| 0 <= i < states.len() implies !#[trigger] states[i].readers.dom().contains(id) by {
        retired_at_cut(states, events, id, i as nat);
    }
}

pub proof fn every_finite_interleaving_preserves_block_lifetimes(states: Seq<State>, events: Seq<Event>)
    requires execution(states, events), inv(states[0]),
    ensures forall|i: int| 0 <= i < states.len() ==> #[trigger] inv(states[i]),
{
    assert forall|i: int| 0 <= i < states.len() implies #[trigger] inv(states[i]) by { at_cut(states, events, i as nat); }
}

pub proof fn two_distinct_readers_can_coexist(s: State, block: u64, owner: Owner, epoch: nat, a: nat, b: nat)
    requires inv(s), a != b, enabled(s, Event::PinRead(block, a, owner, epoch, s.volume)), enabled(s, Event::PinRead(block, b, owner, epoch, s.volume)),
    ensures {
        let first = next(s, Event::PinRead(block, a, owner, epoch, s.volume));
        let both = next(first, Event::PinRead(block, b, owner, epoch, s.volume));
        &&& enabled(first, Event::PinRead(block, b, owner, epoch, s.volume)) && inv(both)
        &&& both.readers.dom().contains(s.next_pin) && both.readers.dom().contains(s.next_pin + 1)
        &&& both.readers[s.next_pin].actor == a && both.readers[s.next_pin + 1].actor == b
    },
{
    every_event_preserves(s, Event::PinRead(block, a, owner, epoch, s.volume));
    every_event_preserves(next(s, Event::PinRead(block, a, owner, epoch, s.volume)), Event::PinRead(block, b, owner, epoch, s.volume));
}

pub proof fn nonempty_concurrent_read_example(block_bytes: u32)
    requires valid_block_size(block_bytes),
{
    let owner = Owner { inode: 12, generation: 1 };
    let s = State { volume: 17, blocks: 8, block_bytes, slots: Map::empty().insert(3,
        Slot { owner: Some(owner), epoch: 4, initialized: true, exposure: Exposure::Published, bytes: zeros(block_bytes) }),
        readers: Map::empty(), writers: Map::empty(), next_pin: 0, next_writer: 0 };
    assert(inv(s)) by { reveal(inv); }
    two_distinct_readers_can_coexist(s, 3, owner, 4, 10, 11);
}

pub proof fn two_distinct_blocks_can_have_different_writers(s: State, b: u64, c: u64, a: nat, d: nat)
    requires inv(s), b != c, a != d, enabled(s, Event::ClaimWrite(b, a)), enabled(s, Event::ClaimWrite(c, d)),
    ensures {
        let first = next(s, Event::ClaimWrite(b, a));
        let both = next(first, Event::ClaimWrite(c, d));
        &&& enabled(first, Event::ClaimWrite(c, d)) && inv(both)
        &&& writer(both, b, both.writers[b]) && writer(both, c, both.writers[c])
        &&& both.writers[b].actor == a && both.writers[c].actor == d
        &&& both.writers[b].serial != both.writers[c].serial
    },
{
    every_event_preserves(s, Event::ClaimWrite(b, a));
    every_event_preserves(next(s, Event::ClaimWrite(b, a)), Event::ClaimWrite(c, d));
}

pub proof fn nonempty_concurrent_write_example(block_bytes: u32)
    requires valid_block_size(block_bytes),
{
    let owner = Owner { inode: 12, generation: 1 };
    let slot = Slot { owner: Some(owner), epoch: 4, initialized: true, exposure: Exposure::Published, bytes: zeros(block_bytes) };
    let s = State { volume: 17, blocks: 8, block_bytes, slots: Map::empty().insert(3, slot).insert(4, slot),
        readers: Map::empty(), writers: Map::empty(), next_pin: 0, next_writer: 0 };
    assert(inv(s)) by { reveal(inv); }
    two_distinct_blocks_can_have_different_writers(s, 3, 4, 10, 11);
    let both = next(next(s, Event::ClaimWrite(3, 10)), Event::ClaimWrite(4, 11));
    disjoint_writes_commute(both, 3, 4, both.writers[3], both.writers[4], zeros(block_bytes), Seq::new(block_bytes as nat, |i: int| 1u8));
}

}
