// SPDX-License-Identifier: MPL-2.0

//! BIGALLOC cluster bitmap and per-inode partial-cluster lifecycle.
//! One physical cluster is assigned to one inode generation and one aligned
//! logical cluster. A bounded bitmap window can be tracked without allocating
//! a per-block state array for every free cluster. This is allocator bookkeeping,
//! not a device lease, namespace permit, or proof of completed physical I/O.

use vstd::prelude::*;
use crate::{meta_bg::{self, Geometry}, recovery_request::Completion};

verus! {

pub const MAX_TRACKED_CLUSTERS: usize = 65536;
pub const MAX_LIVE_BLOCKS: u64 = 1048576;
pub const MAX_PENDING: usize = 64;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Owner { pub inode: u32, pub generation: u32 }

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    Geometry, Bitmap, Capacity, Outside, Busy, Owner, Stale, State,
    Uninitialized, Overflow, Checkpoint, InitializationFailed, Quiescence,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ReadDecision { Zero, Initialized(u64) }

struct PendingRange { id: u64, start: u32, length: u32, faulted: bool }

struct Slot {
    // 0=initially unavailable; 1=free; 2=reserved; 3=owned; 4=retired.
    phase: u8,
    generation: u64,
    owner: Owner,
    logical_start: u32,
    pins: u32,
    mapped: Vec<u8>, // 0=hole, 1=unwritten, 2=written.
    initialized: Vec<bool>,
    pending: Vec<PendingRange>,
}

#[derive(Debug)]
pub struct Key {
    domain: u64, cluster: u64, generation: u64,
    owner: Owner, logical_start: u32,
}

#[derive(Debug)]
pub struct Initialization {
    domain: u64, cluster: u64, generation: u64, request: u64,
    start: u32, length: u32, physical: u64,
}

#[derive(Debug)]
pub struct ReadPin { domain: u64, cluster: u64, generation: u64 }

#[derive(Debug)]
pub struct Retirement { domain: u64, cluster: u64, generation: u64 }

pub struct Ledger { state: LedgerState }

// Private mutation state has no type invariant or custom destructor. Only a
// complete checked transition is published through the sealed Ledger wrapper.
struct LedgerState {
    geometry: Geometry,
    domain: u64,
    first_cluster: u64,
    first_bit: u32,
    slots: Vec<Slot>,
    bitmap: Vec<u8>,
    live_blocks: u64,
    next_request: u64,
}

#[verifier::ext_equal]
pub struct PendingView { pub id: u64, pub start: u32, pub length: u32, pub faulted: bool }

#[verifier::ext_equal]
pub struct SlotView {
    pub phase: u8, pub generation: u64, pub owner: Owner, pub logical_start: u32,
    pub pins: u32, pub mapped: Seq<u8>, pub initialized: Seq<bool>, pub pending: Seq<PendingView>,
}

#[verifier::ext_equal]
pub struct LedgerView {
    pub geometry: Geometry, pub domain: u64, pub first_cluster: u64, pub first_bit: u32,
    pub slots: Seq<SlotView>, pub bitmap: Seq<u8>, pub live_blocks: u64, pub next_request: u64,
}

#[verifier::ext_equal]
pub struct KeyView {
    pub domain: u64, pub cluster: u64, pub generation: u64,
    pub owner: Owner, pub logical_start: u32,
}

#[verifier::ext_equal]
pub struct CommandView {
    pub domain: u64, pub cluster: u64, pub generation: u64, pub request: u64,
    pub start: u32, pub length: u32, pub physical: u64,
}

#[verifier::ext_equal]
pub struct TicketView { pub domain: u64, pub cluster: u64, pub generation: u64 }

impl PendingRange {
    spec fn view(&self) -> PendingView {
        PendingView { id: self.id, start: self.start, length: self.length, faulted: self.faulted }
    }
}

impl Slot {
    spec fn view(&self) -> SlotView {
        SlotView { phase: self.phase, generation: self.generation, owner: self.owner,
            logical_start: self.logical_start, pins: self.pins, mapped: self.mapped@,
            initialized: self.initialized@,
            pending: pending_views(self.pending@) }
    }
}

spec fn pending_views(pending: Seq<PendingRange>) -> Seq<PendingView> {
    Seq::new(pending.len(), |i: int| pending[i].view())
}

spec fn slot_views(slots: Seq<Slot>) -> Seq<SlotView> {
    Seq::new(slots.len(), |i: int| slots[i].view())
}

proof fn slot_views_update(slots: Seq<Slot>, index: int, slot: Slot)
    requires 0 <= index < slots.len(),
    ensures slot_views(slots.update(index, slot)) == slot_views(slots).update(index, slot.view()),
{
    assert(slot_views(slots.update(index, slot)) =~= slot_views(slots).update(index, slot.view()));
}

proof fn pending_views_update(pending: Seq<PendingRange>, index: int, item: PendingRange)
    requires 0 <= index < pending.len(),
    ensures pending_views(pending.update(index, item)) == pending_views(pending).update(index, item.view()),
{
    assert(pending_views(pending.update(index, item)) =~= pending_views(pending).update(index, item.view()));
}

proof fn pending_views_push(pending: Seq<PendingRange>, item: PendingRange)
    ensures pending_views(pending.push(item)) == pending_views(pending).push(item.view()),
{
    assert(pending_views(pending.push(item)) =~= pending_views(pending).push(item.view()));
}

proof fn pending_views_remove(pending: Seq<PendingRange>, index: int)
    requires 0 <= index < pending.len(),
    ensures pending_views(pending.remove(index)) == pending_views(pending).remove(index),
{
    assert(pending_views(pending.remove(index)) =~= pending_views(pending).remove(index));
}

pub open spec fn active(slot: SlotView) -> bool { 2 <= slot.phase <= 4 }

pub open spec fn occupied_count(slots: Seq<SlotView>) -> nat
    decreases slots.len(),
{
    if slots.len() == 0 { 0 }
    else { occupied_count(slots.drop_last()) + if active(slots.last()) { 1nat } else { 0nat } }
}

pub proof fn no_active_count_is_zero(slots: Seq<SlotView>)
    requires forall|i: int| 0 <= i < slots.len() ==> !active(#[trigger] slots[i]),
    ensures occupied_count(slots) == 0,
    decreases slots.len(),
{
    if slots.len() > 0 { no_active_count_is_zero(slots.drop_last()); }
}

pub proof fn occupied_count_update(slots: Seq<SlotView>, index: int, slot: SlotView)
    requires 0 <= index < slots.len(),
    ensures occupied_count(slots.update(index, slot)) + (if active(slots[index]) { 1nat } else { 0nat })
        == occupied_count(slots) + (if active(slot) { 1nat } else { 0nat }),
    decreases slots.len(),
{
    if index < slots.len() - 1 {
        occupied_count_update(slots.drop_last(), index, slot);
        assert(slots.update(index, slot).drop_last() =~= slots.drop_last().update(index, slot));
    } else {
        assert(slots.update(index, slot).drop_last() =~= slots.drop_last());
    }
}

pub open spec fn bitmap_bit(raw: Seq<u8>, index: u32) -> bool {
    let byte = (index / 8) as int;
    byte >= raw.len() || (raw[byte] >> ((index % 8) as u8)) & 1u8 != 0
}

pub open spec fn free_count(raw: Seq<u8>, bits: nat) -> nat
    decreases bits,
{
    if bits == 0 { 0nat }
    else { free_count(raw, (bits - 1) as nat) + if bitmap_bit(raw, (bits - 1) as u32) { 0nat } else { 1nat } }
}

pub open spec fn ranges_overlap(a: u32, alen: u32, b: u32, blen: u32) -> bool {
    (a as nat) < b as nat + blen && (b as nat) < a as nat + alen
}

pub open spec fn range_valid(v: LedgerView, index: int, start: u32, length: u32) -> bool {
    &&& 0 <= index < v.slots.len() && length > 0
    &&& start < v.geometry.cluster_ratio && length as nat <= v.geometry.cluster_ratio as nat - start
    &&& v.slots[index].logical_start as nat + start + length <= 4294967295
}

pub open spec fn pending_overlap(v: LedgerView, index: int, start: u32, length: u32) -> bool {
    index < 0 || index >= v.slots.len() || exists|i: int| 0 <= i < v.slots[index].pending.len()
        && ranges_overlap(start, length, (#[trigger] v.slots[index].pending[i]).start, v.slots[index].pending[i].length)
}

pub open spec fn slot_valid(slot: SlotView, ratio: u32, next_request: u64) -> bool {
    &&& slot.phase <= 4
    &&& if active(slot) {
        &&& slot.generation > 0 && slot.owner.inode > 0
        &&& slot.logical_start < 4294967295 && ratio > 0 && slot.logical_start % ratio == 0
        &&& slot.mapped.len() == ratio && slot.initialized.len() == ratio
        &&& (forall|i: int| 0 <= i < ratio ==> (#[trigger] slot.mapped[i]) <= 2
            && (slot.mapped[i] == 2 ==> slot.initialized[i])
            && (slot.mapped[i] != 0 ==> slot.logical_start as nat + i < 4294967295))
        &&& slot.pending.len() <= MAX_PENDING
        &&& (forall|i: int| 0 <= i < slot.pending.len() ==> {
            let p = #[trigger] slot.pending[i];
            &&& 0 < p.id < next_request && p.length > 0
            &&& p.start < ratio && p.length as nat <= ratio as nat - p.start
            &&& slot.logical_start as nat + p.start + p.length <= 4294967295
            &&& (forall|j: int| p.start <= j < p.start as nat + p.length ==> (#[trigger] slot.mapped[j]) != 2)
            &&& (forall|j: int| p.start <= j < p.start as nat + p.length ==> (#[trigger] slot.initialized[j]) == false)
        })
        &&& (forall|i: int, j: int| 0 <= i < j < slot.pending.len() ==>
            (#[trigger] slot.pending[i]).id != (#[trigger] slot.pending[j]).id
                && !ranges_overlap(slot.pending[i].start, slot.pending[i].length, slot.pending[j].start, slot.pending[j].length))
        &&& (slot.pins > 0 ==> slot.phase == 3 && slot.pending.len() == 0)
        &&& (slot.phase == 2 ==> forall|i: int| 0 <= i < ratio ==> (#[trigger] slot.mapped[i]) == 0)
        &&& (slot.phase == 4 ==> slot.pins == 0 && slot.pending.len() == 0
            && forall|i: int| 0 <= i < ratio ==> (#[trigger] slot.mapped[i]) == 0)
    } else {
        slot.owner.inode == 0 && slot.owner.generation == 0 && slot.logical_start == 0
            && slot.pins == 0 && slot.mapped.len() == 0 && slot.initialized.len() == 0 && slot.pending.len() == 0
    }
}

proof fn slot_init_false_valid(slot: SlotView, ratio: u32, next_request: u64, index: int)
    requires
        slot_valid(slot, ratio, next_request),
        active(slot),
        0 <= index < ratio,
        slot.mapped[index] != 2,
    ensures
        slot_valid(SlotView {
            initialized: slot.initialized.update(index, false), ..slot
        }, ratio, next_request),
{
    let next = SlotView { initialized: slot.initialized.update(index, false), ..slot };
    assert(next.mapped == slot.mapped);
    assert(next.pending == slot.pending);
    assert(next.initialized.len() == ratio);
    assert forall|j: int| 0 <= j < ratio implies
        (#[trigger] next.mapped[j]) <= 2
            && (next.mapped[j] == 2 ==> next.initialized[j])
            && (next.mapped[j] != 0 ==> next.logical_start as nat + j < 4294967295) by {
        assert(slot.mapped[j] <= 2);
        assert(slot.mapped[j] == 2 ==> slot.initialized[j]);
        assert(slot.mapped[j] != 0 ==> slot.logical_start as nat + j < 4294967295);
        if j == index {
            assert(slot.mapped[j] != 2);
        } else {
            assert(next.initialized[j] == slot.initialized[j]);
        }
    }
    assert forall|k: int| 0 <= k < next.pending.len() implies {
        let p = #[trigger] next.pending[k];
        &&& 0 < p.id < next_request && p.length > 0
        &&& p.start < ratio && p.length as nat <= ratio as nat - p.start
        &&& next.logical_start as nat + p.start + p.length <= 4294967295
        &&& (forall|j: int| p.start <= j < p.start as nat + p.length ==>
            (#[trigger] next.mapped[j]) != 2)
        &&& (forall|j: int| p.start <= j < p.start as nat + p.length ==>
            (#[trigger] next.initialized[j]) == false)
    } by {
        let p = next.pending[k];
        assert(p == slot.pending[k]);
        assert(0 < p.id < next_request && p.length > 0);
        assert(p.start < ratio && p.length as nat <= ratio as nat - p.start);
        assert(slot.logical_start as nat + p.start + p.length <= 4294967295);
        assert forall|j: int| p.start <= j < p.start as nat + p.length implies
            (#[trigger] next.mapped[j]) != 2 by {
            assert(0 <= j < ratio);
            assert(slot.mapped[j] != 2);
        }
        assert forall|j: int| p.start <= j < p.start as nat + p.length implies
            (#[trigger] next.initialized[j]) == false by {
            assert(0 <= j < ratio);
            if j == index {
                assert(next.initialized[j] == false);
            } else {
                assert(slot.initialized[j] == false);
                assert(next.initialized[j] == slot.initialized[j]);
            }
        }
    }
    assert(slot_valid(next, ratio, next_request));
}

proof fn slot_init_true_valid(slot: SlotView, ratio: u32, next_request: u64, index: int)
    requires
        slot_valid(slot, ratio, next_request),
        active(slot),
        0 <= index < ratio,
        forall|k: int| 0 <= k < slot.pending.len() ==>
            !((#[trigger] slot.pending[k]).start <= index
                < slot.pending[k].start as nat + slot.pending[k].length),
    ensures
        slot_valid(SlotView {
            initialized: slot.initialized.update(index, true), ..slot
        }, ratio, next_request),
{
    let next = SlotView { initialized: slot.initialized.update(index, true), ..slot };
    assert(next.mapped == slot.mapped);
    assert(next.pending == slot.pending);
    assert(next.initialized.len() == ratio);
    assert forall|j: int| 0 <= j < ratio implies
        (#[trigger] next.mapped[j]) <= 2
            && (next.mapped[j] == 2 ==> next.initialized[j])
            && (next.mapped[j] != 0 ==> next.logical_start as nat + j < 4294967295) by {
        assert(slot.mapped[j] <= 2);
        assert(slot.mapped[j] == 2 ==> slot.initialized[j]);
        assert(slot.mapped[j] != 0 ==> slot.logical_start as nat + j < 4294967295);
        if j == index {
            assert(next.initialized[j] == true);
        } else {
            assert(next.initialized[j] == slot.initialized[j]);
        }
    }
    assert forall|k: int| 0 <= k < next.pending.len() implies {
        let p = #[trigger] next.pending[k];
        &&& 0 < p.id < next_request && p.length > 0
        &&& p.start < ratio && p.length as nat <= ratio as nat - p.start
        &&& next.logical_start as nat + p.start + p.length <= 4294967295
        &&& (forall|j: int| p.start <= j < p.start as nat + p.length ==>
            (#[trigger] next.mapped[j]) != 2)
        &&& (forall|j: int| p.start <= j < p.start as nat + p.length ==>
            (#[trigger] next.initialized[j]) == false)
    } by {
        let p = next.pending[k];
        assert(p == slot.pending[k]);
        assert(0 < p.id < next_request && p.length > 0);
        assert(p.start < ratio && p.length as nat <= ratio as nat - p.start);
        assert(slot.logical_start as nat + p.start + p.length <= 4294967295);
        assert(!(slot.pending[k].start <= index
            < slot.pending[k].start as nat + slot.pending[k].length));
        assert forall|j: int| p.start <= j < p.start as nat + p.length implies
            (#[trigger] next.mapped[j]) != 2 by {
            assert(0 <= j < ratio);
            assert(slot.mapped[j] != 2);
        }
        assert forall|j: int| p.start <= j < p.start as nat + p.length implies
            (#[trigger] next.initialized[j]) == false by {
            assert(0 <= j < ratio);
            assert(j != index);
            assert(slot.initialized[j] == false);
            assert(next.initialized[j] == slot.initialized[j]);
        }
    }
    assert(slot_valid(next, ratio, next_request));
}

proof fn slot_mapped_valid(
    slot: SlotView, ratio: u32, next_request: u64, index: int, value: u8,
)
    requires
        slot_valid(slot, ratio, next_request),
        slot.phase == 3,
        0 <= index < ratio,
        value <= 2,
        value == 2 ==> slot.initialized[index],
        value != 0 ==> slot.logical_start as nat + index < 4294967295,
        value == 2 ==> (forall|k: int| 0 <= k < slot.pending.len() ==>
            !((#[trigger] slot.pending[k]).start <= index
                < slot.pending[k].start as nat + slot.pending[k].length)),
    ensures
        slot_valid(SlotView { mapped: slot.mapped.update(index, value), ..slot },
            ratio, next_request),
{
    let next = SlotView { mapped: slot.mapped.update(index, value), ..slot };
    assert(active(slot));
    assert(next.initialized == slot.initialized);
    assert(next.pending == slot.pending);
    assert(next.mapped.len() == ratio);
    assert forall|j: int| 0 <= j < ratio implies
        (#[trigger] next.mapped[j]) <= 2
            && (next.mapped[j] == 2 ==> next.initialized[j])
            && (next.mapped[j] != 0 ==> next.logical_start as nat + j < 4294967295) by {
        if j == index {
            assert(next.mapped[j] == value);
        } else {
            assert(next.mapped[j] == slot.mapped[j]);
            assert(slot.mapped[j] <= 2);
            assert(slot.mapped[j] == 2 ==> slot.initialized[j]);
            assert(slot.mapped[j] != 0 ==> slot.logical_start as nat + j < 4294967295);
        }
    }
    assert forall|k: int| 0 <= k < next.pending.len() implies {
        let p = #[trigger] next.pending[k];
        &&& 0 < p.id < next_request && p.length > 0
        &&& p.start < ratio && p.length as nat <= ratio as nat - p.start
        &&& next.logical_start as nat + p.start + p.length <= 4294967295
        &&& (forall|j: int| p.start <= j < p.start as nat + p.length ==>
            (#[trigger] next.mapped[j]) != 2)
        &&& (forall|j: int| p.start <= j < p.start as nat + p.length ==>
            (#[trigger] next.initialized[j]) == false)
    } by {
        let p = next.pending[k];
        assert(p == slot.pending[k]);
        assert(0 < p.id < next_request && p.length > 0);
        assert(p.start < ratio && p.length as nat <= ratio as nat - p.start);
        assert(slot.logical_start as nat + p.start + p.length <= 4294967295);
        assert forall|j: int| p.start <= j < p.start as nat + p.length implies
            (#[trigger] next.mapped[j]) != 2 by {
            assert(0 <= j < ratio);
            if j == index {
                if value == 2 {
                    assert(!(slot.pending[k].start <= index
                        < slot.pending[k].start as nat + slot.pending[k].length));
                    assert(false);
                }
                assert(next.mapped[j] == value);
            } else {
                assert(slot.mapped[j] != 2);
                assert(next.mapped[j] == slot.mapped[j]);
            }
        }
        assert forall|j: int| p.start <= j < p.start as nat + p.length implies
            (#[trigger] next.initialized[j]) == false by {
            assert(0 <= j < ratio);
            assert(slot.initialized[j] == false);
        }
    }
    assert(slot_valid(next, ratio, next_request));
}

proof fn slot_pending_fault_valid(
    slot: SlotView, ratio: u32, next_request: u64, at: int, faulted: bool,
)
    requires
        slot_valid(slot, ratio, next_request),
        0 <= at < slot.pending.len(),
    ensures
        slot_valid(SlotView {
            pending: slot.pending.update(at, PendingView { faulted, ..slot.pending[at] }),
            ..slot
        }, ratio, next_request),
{
    let next = SlotView {
        pending: slot.pending.update(at, PendingView { faulted, ..slot.pending[at] }),
        ..slot
    };
    assert(slot.pending.len() > 0);
    assert(active(slot));
    assert(slot.pins == 0);
    assert(slot.phase != 4);
    assert(next.pending.len() == slot.pending.len());
    assert forall|k: int| 0 <= k < next.pending.len() implies
        (#[trigger] next.pending[k]).id == slot.pending[k].id
            && next.pending[k].start == slot.pending[k].start
            && next.pending[k].length == slot.pending[k].length by {
        if k == at {
            assert(next.pending[k] == (PendingView { faulted, ..slot.pending[k] }));
        } else {
            assert(next.pending[k] == slot.pending[k]);
        }
    }
    assert forall|k: int| 0 <= k < next.pending.len() implies {
        let p = #[trigger] next.pending[k];
        &&& 0 < p.id < next_request && p.length > 0
        &&& p.start < ratio && p.length as nat <= ratio as nat - p.start
        &&& next.logical_start as nat + p.start + p.length <= 4294967295
        &&& (forall|j: int| p.start <= j < p.start as nat + p.length ==>
            (#[trigger] next.mapped[j]) != 2)
        &&& (forall|j: int| p.start <= j < p.start as nat + p.length ==>
            (#[trigger] next.initialized[j]) == false)
    } by {
        let p = next.pending[k];
        let old = slot.pending[k];
        assert(p.id == old.id && p.start == old.start && p.length == old.length);
        assert(0 < old.id < next_request && old.length > 0);
        assert(old.start < ratio && old.length as nat <= ratio as nat - old.start);
        assert(slot.logical_start as nat + old.start + old.length <= 4294967295);
        assert forall|j: int| p.start <= j < p.start as nat + p.length implies
            (#[trigger] next.mapped[j]) != 2 by {
            assert(old.start <= j < old.start as nat + old.length);
            assert(slot.mapped[j] != 2);
        }
        assert forall|j: int| p.start <= j < p.start as nat + p.length implies
            (#[trigger] next.initialized[j]) == false by {
            assert(old.start <= j < old.start as nat + old.length);
            assert(slot.initialized[j] == false);
        }
    }
    assert forall|i: int, j: int| 0 <= i < j < next.pending.len() implies
        (#[trigger] next.pending[i]).id != (#[trigger] next.pending[j]).id
            && !ranges_overlap(next.pending[i].start, next.pending[i].length,
                next.pending[j].start, next.pending[j].length) by {
        assert(0 <= i < j < slot.pending.len());
        assert(slot.pending[i].id != slot.pending[j].id
            && !ranges_overlap(slot.pending[i].start, slot.pending[i].length,
                slot.pending[j].start, slot.pending[j].length));
        assert(next.pending[i].id == slot.pending[i].id
            && next.pending[i].start == slot.pending[i].start
            && next.pending[i].length == slot.pending[i].length);
        assert(next.pending[j].id == slot.pending[j].id
            && next.pending[j].start == slot.pending[j].start
            && next.pending[j].length == slot.pending[j].length);
    }
    assert(slot_valid(next, ratio, next_request));
}

proof fn slot_pending_remove_valid(slot: SlotView, ratio: u32, next_request: u64, at: int)
    requires
        slot_valid(slot, ratio, next_request),
        0 <= at < slot.pending.len(),
    ensures
        slot_valid(SlotView { pending: slot.pending.remove(at), ..slot }, ratio, next_request),
        forall|k: int| 0 <= k < slot.pending.remove(at).len() ==>
            !ranges_overlap(slot.pending[at].start, slot.pending[at].length,
                (#[trigger] slot.pending.remove(at)[k]).start,
                slot.pending.remove(at)[k].length),
{
    let next = SlotView { pending: slot.pending.remove(at), ..slot };
    let removed = slot.pending[at];
    assert(slot.pending.len() > 0);
    assert(active(slot));
    assert(slot.pins == 0);
    assert(slot.phase != 4);
    assert(next.pending.len() == slot.pending.len() - 1);
    assert forall|k: int| 0 <= k < next.pending.len() implies
        (#[trigger] next.pending[k]) == slot.pending[if k < at { k } else { k + 1 }] by {
        if k < at {
            assert(next.pending[k] == slot.pending[k]);
        } else {
            assert(next.pending[k] == slot.pending[k + 1]);
        }
    }
    assert forall|k: int| 0 <= k < next.pending.len() implies {
        let p = #[trigger] next.pending[k];
        &&& 0 < p.id < next_request && p.length > 0
        &&& p.start < ratio && p.length as nat <= ratio as nat - p.start
        &&& next.logical_start as nat + p.start + p.length <= 4294967295
        &&& (forall|j: int| p.start <= j < p.start as nat + p.length ==>
            (#[trigger] next.mapped[j]) != 2)
        &&& (forall|j: int| p.start <= j < p.start as nat + p.length ==>
            (#[trigger] next.initialized[j]) == false)
    } by {
        let source = if k < at { k } else { k + 1 };
        assert(0 <= source < slot.pending.len());
        let p = next.pending[k];
        assert(p == slot.pending[source]);
        assert(0 < slot.pending[source].id < next_request && slot.pending[source].length > 0);
        assert(slot.pending[source].start < ratio
            && slot.pending[source].length as nat <= ratio as nat - slot.pending[source].start);
        assert(slot.logical_start as nat + slot.pending[source].start
            + slot.pending[source].length <= 4294967295);
        assert forall|j: int| p.start <= j < p.start as nat + p.length implies
            (#[trigger] next.mapped[j]) != 2 by {
            assert(slot.pending[source].start <= j
                < slot.pending[source].start as nat + slot.pending[source].length);
            assert(slot.mapped[j] != 2);
        }
        assert forall|j: int| p.start <= j < p.start as nat + p.length implies
            (#[trigger] next.initialized[j]) == false by {
            assert(slot.pending[source].start <= j
                < slot.pending[source].start as nat + slot.pending[source].length);
            assert(slot.initialized[j] == false);
        }
    }
    assert forall|i: int, j: int| 0 <= i < j < next.pending.len() implies
        (#[trigger] next.pending[i]).id != (#[trigger] next.pending[j]).id
            && !ranges_overlap(next.pending[i].start, next.pending[i].length,
                next.pending[j].start, next.pending[j].length) by {
        let old_i = if i < at { i } else { i + 1 };
        let old_j = if j < at { j } else { j + 1 };
        assert(0 <= old_i < old_j < slot.pending.len());
        assert(next.pending[i] == slot.pending[old_i]);
        assert(next.pending[j] == slot.pending[old_j]);
        assert(slot.pending[old_i].id != slot.pending[old_j].id
            && !ranges_overlap(slot.pending[old_i].start, slot.pending[old_i].length,
                slot.pending[old_j].start, slot.pending[old_j].length));
    }
    assert forall|k: int| 0 <= k < next.pending.len() implies
        !ranges_overlap(removed.start, removed.length,
            (#[trigger] next.pending[k]).start, next.pending[k].length) by {
        let source = if k < at { k } else { k + 1 };
        assert(0 <= source < slot.pending.len() && source != at);
        assert(next.pending[k] == slot.pending[source]);
        if source < at {
            assert(!ranges_overlap(slot.pending[source].start, slot.pending[source].length,
                slot.pending[at].start, slot.pending[at].length));
            assert(ranges_overlap(removed.start, removed.length,
                slot.pending[source].start, slot.pending[source].length)
                == ranges_overlap(slot.pending[source].start, slot.pending[source].length,
                    removed.start, removed.length));
        } else {
            assert(at < source);
            assert(!ranges_overlap(slot.pending[at].start, slot.pending[at].length,
                slot.pending[source].start, slot.pending[source].length));
        }
    }
    assert(slot_valid(next, ratio, next_request));
}

proof fn slot_pending_push_valid(
    slot: SlotView, ratio: u32, old_next: u64, new_next: u64, start: u32, length: u32,
)
    requires
        slot_valid(slot, ratio, old_next),
        2 <= slot.phase <= 3,
        slot.pins == 0,
        slot.pending.len() < MAX_PENDING,
        old_next > 0,
        new_next as nat == old_next as nat + 1,
        length > 0,
        start < ratio,
        length as nat <= ratio as nat - start,
        slot.logical_start as nat + start + length <= 4294967295,
        forall|k: int| 0 <= k < slot.pending.len() ==>
            !ranges_overlap(start, length,
                (#[trigger] slot.pending[k]).start, slot.pending[k].length),
        forall|j: int| start <= j < start as nat + length ==>
            (#[trigger] slot.mapped[j]) != 2,
        forall|j: int| start <= j < start as nat + length ==>
            (#[trigger] slot.initialized[j]) == false,
    ensures
        slot_valid(SlotView {
            pending: slot.pending.push(PendingView { id: old_next, start, length, faulted: false }),
            ..slot
        }, ratio, new_next),
{
    let fresh = PendingView { id: old_next, start, length, faulted: false };
    let next = SlotView { pending: slot.pending.push(fresh), ..slot };
    assert(active(slot));
    assert(new_next > old_next);
    assert(next.pending.len() == slot.pending.len() + 1);
    assert(next.pending.len() <= MAX_PENDING);
    assert forall|k: int| 0 <= k < next.pending.len() implies {
        let p = #[trigger] next.pending[k];
        &&& 0 < p.id < new_next && p.length > 0
        &&& p.start < ratio && p.length as nat <= ratio as nat - p.start
        &&& next.logical_start as nat + p.start + p.length <= 4294967295
        &&& (forall|j: int| p.start <= j < p.start as nat + p.length ==>
            (#[trigger] next.mapped[j]) != 2)
        &&& (forall|j: int| p.start <= j < p.start as nat + p.length ==>
            (#[trigger] next.initialized[j]) == false)
    } by {
        let p = next.pending[k];
        if k < slot.pending.len() {
            assert(p == slot.pending[k]);
            assert(0 < slot.pending[k].id < old_next && slot.pending[k].length > 0);
            assert(slot.pending[k].start < ratio
                && slot.pending[k].length as nat <= ratio as nat - slot.pending[k].start);
            assert(slot.logical_start as nat + slot.pending[k].start
                + slot.pending[k].length <= 4294967295);
            assert forall|j: int| p.start <= j < p.start as nat + p.length implies
                (#[trigger] next.mapped[j]) != 2 by {
                assert(slot.pending[k].start <= j
                    < slot.pending[k].start as nat + slot.pending[k].length);
                assert(slot.mapped[j] != 2);
            }
            assert forall|j: int| p.start <= j < p.start as nat + p.length implies
                (#[trigger] next.initialized[j]) == false by {
                assert(slot.pending[k].start <= j
                    < slot.pending[k].start as nat + slot.pending[k].length);
                assert(slot.initialized[j] == false);
            }
        } else {
            assert(k == slot.pending.len());
            assert(p == fresh);
            assert(0 < p.id < new_next && p.length > 0);
            assert(p.start < ratio && p.length as nat <= ratio as nat - p.start);
            assert(next.logical_start as nat + p.start + p.length <= 4294967295);
            assert forall|j: int| p.start <= j < p.start as nat + p.length implies
                (#[trigger] next.mapped[j]) != 2 by {
                assert(start <= j < start as nat + length);
                assert(slot.mapped[j] != 2);
            }
            assert forall|j: int| p.start <= j < p.start as nat + p.length implies
                (#[trigger] next.initialized[j]) == false by {
                assert(start <= j < start as nat + length);
                assert(slot.initialized[j] == false);
            }
        }
    }
    assert forall|i: int, j: int| 0 <= i < j < next.pending.len() implies
        (#[trigger] next.pending[i]).id != (#[trigger] next.pending[j]).id
            && !ranges_overlap(next.pending[i].start, next.pending[i].length,
                next.pending[j].start, next.pending[j].length) by {
        assert(0 <= i < slot.pending.len());
        assert(next.pending[i] == slot.pending[i]);
        if j < slot.pending.len() {
            assert(next.pending[j] == slot.pending[j]);
            assert(slot.pending[i].id != slot.pending[j].id
                && !ranges_overlap(slot.pending[i].start, slot.pending[i].length,
                    slot.pending[j].start, slot.pending[j].length));
        } else {
            assert(j == slot.pending.len());
            assert(next.pending[j] == fresh);
            assert(0 < slot.pending[i].id < old_next);
            assert(!ranges_overlap(start, length, slot.pending[i].start, slot.pending[i].length));
            assert(ranges_overlap(slot.pending[i].start, slot.pending[i].length, start, length)
                == ranges_overlap(start, length, slot.pending[i].start, slot.pending[i].length));
        }
    }
    assert(slot_valid(next, ratio, new_next));
}

pub open spec fn valid(v: LedgerView) -> bool {
    &&& meta_bg::valid(v.geometry) && v.domain > 0 && v.next_request > 0
    &&& 0 < v.slots.len() <= MAX_TRACKED_CLUSTERS
    &&& v.bitmap.len() == v.geometry.block_bytes
    &&& v.first_bit as nat + v.slots.len() <= v.bitmap.len() * 8
    &&& v.first_cluster as nat + v.slots.len() <= 18446744073709551615
    &&& v.live_blocks <= MAX_LIVE_BLOCKS
    &&& v.live_blocks as nat == occupied_count(v.slots) * v.geometry.cluster_ratio
    &&& (forall|i: int| 0 <= i < v.slots.len() ==> {
        let slot = #[trigger] v.slots[i];
        &&& slot_valid(slot, v.geometry.cluster_ratio, v.next_request)
        &&& (slot.phase == 0) == bitmap_bit(v.bitmap, (v.first_bit as int + i) as u32)
        &&& (slot.phase != 0 ==> v.geometry.first_data <= (v.first_cluster as nat + i) * v.geometry.cluster_ratio
            && (v.first_cluster as nat + i + 1) * v.geometry.cluster_ratio <= v.geometry.blocks)
    })
    &&& (forall|i: int, j: int| 0 <= i < j < v.slots.len()
        && active(v.slots[i]) && active(v.slots[j]) ==>
        (#[trigger] v.slots[i]).owner != (#[trigger] v.slots[j]).owner
            || v.slots[i].logical_start != v.slots[j].logical_start)
}

proof fn same_ownership_update_valid(v: LedgerView, index: int, slot: SlotView)
    requires valid(v), 0 <= index < v.slots.len(),
        slot_valid(slot, v.geometry.cluster_ratio, v.next_request),
        slot.phase == v.slots[index].phase, slot.generation == v.slots[index].generation,
        slot.owner == v.slots[index].owner, slot.logical_start == v.slots[index].logical_start,
    ensures valid(LedgerView { slots: v.slots.update(index, slot), ..v }),
{
    occupied_count_update(v.slots, index, slot);
    let next = LedgerView { slots: v.slots.update(index, slot), ..v };
    assert forall|i: int| 0 <= i < next.slots.len() implies {
        let item = #[trigger] next.slots[i];
        &&& slot_valid(item, next.geometry.cluster_ratio, next.next_request)
        &&& (item.phase == 0) == bitmap_bit(next.bitmap, (next.first_bit as int + i) as u32)
        &&& (item.phase != 0 ==> next.geometry.first_data <= (next.first_cluster as nat + i) * next.geometry.cluster_ratio
            && (next.first_cluster as nat + i + 1) * next.geometry.cluster_ratio <= next.geometry.blocks)
    } by {
        if i == index { assert(next.slots[i].phase == v.slots[i].phase); }
        else { assert(next.slots[i] == v.slots[i]); }
    }
    assert forall|i: int, j: int| 0 <= i < j < next.slots.len()
        && active(next.slots[i]) && active(next.slots[j]) implies
        (#[trigger] next.slots[i]).owner != (#[trigger] next.slots[j]).owner
            || next.slots[i].logical_start != next.slots[j].logical_start by {
        assert(next.slots[i].phase == v.slots[i].phase);
        assert(next.slots[j].phase == v.slots[j].phase);
        assert(next.slots[i].owner == v.slots[i].owner);
        assert(next.slots[j].owner == v.slots[j].owner);
        assert(next.slots[i].logical_start == v.slots[i].logical_start);
        assert(next.slots[j].logical_start == v.slots[j].logical_start);
    }
}

proof fn next_request_monotone_valid(v: LedgerView, next_request: u64)
    requires valid(v), next_request >= v.next_request,
    ensures valid(LedgerView { next_request, ..v }),
{
    assert forall|i: int| 0 <= i < v.slots.len() implies slot_valid(#[trigger] v.slots[i], v.geometry.cluster_ratio, next_request) by {
        assert(slot_valid(v.slots[i], v.geometry.cluster_ratio, v.next_request));
    }
}

proof fn reserve_update_valid(v: LedgerView, index: int, slot: SlotView)
    requires valid(v), 0 <= index < v.slots.len(), v.slots[index].phase == 1,
        slot.phase == 2, slot_valid(slot, v.geometry.cluster_ratio, v.next_request),
        v.live_blocks as nat + v.geometry.cluster_ratio <= MAX_LIVE_BLOCKS,
        forall|i: int| 0 <= i < v.slots.len() && active(v.slots[i]) ==>
            (#[trigger] v.slots[i]).owner != slot.owner || v.slots[i].logical_start != slot.logical_start,
    ensures valid(LedgerView { slots: v.slots.update(index, slot),
        live_blocks: (v.live_blocks + v.geometry.cluster_ratio) as u64, ..v }),
{
    let next = LedgerView { slots: v.slots.update(index, slot),
        live_blocks: (v.live_blocks + v.geometry.cluster_ratio) as u64, ..v };
    occupied_count_update(v.slots, index, slot);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(v.geometry.cluster_ratio as int,
        occupied_count(v.slots) as int, 1);
    assert(next.live_blocks as nat == occupied_count(next.slots) * next.geometry.cluster_ratio);
    assert forall|i: int| 0 <= i < next.slots.len() implies {
        let item = #[trigger] next.slots[i];
        &&& slot_valid(item, next.geometry.cluster_ratio, next.next_request)
        &&& (item.phase == 0) == bitmap_bit(next.bitmap, (next.first_bit as int + i) as u32)
        &&& (item.phase != 0 ==> next.geometry.first_data <= (next.first_cluster as nat + i) * next.geometry.cluster_ratio
            && (next.first_cluster as nat + i + 1) * next.geometry.cluster_ratio <= next.geometry.blocks)
    } by { if i != index { assert(next.slots[i] == v.slots[i]); } }
    assert forall|i: int, j: int| 0 <= i < j < next.slots.len()
        && active(next.slots[i]) && active(next.slots[j]) implies
        (#[trigger] next.slots[i]).owner != (#[trigger] next.slots[j]).owner
            || next.slots[i].logical_start != next.slots[j].logical_start by {
        if i == index { assert(v.slots[j].owner != slot.owner || v.slots[j].logical_start != slot.logical_start); }
        else if j == index { assert(v.slots[i].owner != slot.owner || v.slots[i].logical_start != slot.logical_start); }
    }
}

proof fn release_update_valid(v: LedgerView, index: int, slot: SlotView)
    requires valid(v), 0 <= index < v.slots.len(), active(v.slots[index]),
        slot.phase == 1, slot_valid(slot, v.geometry.cluster_ratio, v.next_request),
        v.live_blocks >= v.geometry.cluster_ratio,
    ensures valid(LedgerView { slots: v.slots.update(index, slot),
        live_blocks: (v.live_blocks - v.geometry.cluster_ratio) as u64, ..v }),
{
    let next = LedgerView { slots: v.slots.update(index, slot),
        live_blocks: (v.live_blocks - v.geometry.cluster_ratio) as u64, ..v };
    occupied_count_update(v.slots, index, slot);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(v.geometry.cluster_ratio as int,
        occupied_count(next.slots) as int, 1);
    assert(next.live_blocks as nat == occupied_count(next.slots) * next.geometry.cluster_ratio);
    assert forall|i: int| 0 <= i < next.slots.len() implies {
        let item = #[trigger] next.slots[i];
        &&& slot_valid(item, next.geometry.cluster_ratio, next.next_request)
        &&& (item.phase == 0) == bitmap_bit(next.bitmap, (next.first_bit as int + i) as u32)
        &&& (item.phase != 0 ==> next.geometry.first_data <= (next.first_cluster as nat + i) * next.geometry.cluster_ratio
            && (next.first_cluster as nat + i + 1) * next.geometry.cluster_ratio <= next.geometry.blocks)
    } by { if i != index { assert(next.slots[i] == v.slots[i]); } }
    assert forall|i: int, j: int| 0 <= i < j < next.slots.len()
        && active(next.slots[i]) && active(next.slots[j]) implies
        (#[trigger] next.slots[i]).owner != (#[trigger] next.slots[j]).owner
            || next.slots[i].logical_start != next.slots[j].logical_start by {
        assert(i != index && j != index);
    }
}

pub open spec fn key_matches(v: LedgerView, key: KeyView, index: int) -> bool {
    &&& 0 <= index < v.slots.len() && key.domain == v.domain
    &&& key.cluster as nat == v.first_cluster as nat + index
    &&& key.generation == v.slots[index].generation && key.owner == v.slots[index].owner
    &&& key.logical_start == v.slots[index].logical_start
    &&& 2 <= v.slots[index].phase <= 3
}

pub open spec fn static_fields_equal(a: LedgerView, b: LedgerView) -> bool {
    a.geometry == b.geometry && a.domain == b.domain && a.first_cluster == b.first_cluster
        && a.first_bit == b.first_bit && a.bitmap == b.bitmap
}

pub open spec fn only_slot_changed(a: LedgerView, b: LedgerView, index: int) -> bool {
    &&& static_fields_equal(a, b) && a.slots.len() == b.slots.len()
    &&& forall|i: int| 0 <= i < a.slots.len() && i != index ==> (#[trigger] a.slots[i]) == (#[trigger] b.slots[i])
}

pub proof fn failed_pending_range_remains_unexposed(v: LedgerView, command: CommandView, index: int, pending: int)
    requires valid(v), command_matches(v, command, index, pending), v.slots[index].pending[pending].faulted,
    ensures v.slots[index].pins == 0,
        forall|j: int| command.start <= j < command.start as nat + command.length ==>
            (#[trigger] v.slots[index].mapped[j]) != 2 && (#[trigger] v.slots[index].initialized[j]) == false,
{
    assert(slot_valid(v.slots[index], v.geometry.cluster_ratio, v.next_request));
    let item = v.slots[index].pending[pending];
    assert(item.start == command.start && item.length == command.length);
    assert forall|j: int| command.start <= j < command.start as nat + command.length implies
        (#[trigger] v.slots[index].mapped[j]) != 2 && (#[trigger] v.slots[index].initialized[j]) == false by {
        assert(item.start <= j < item.start as nat + item.length);
        assert(0 <= j < v.geometry.cluster_ratio);
    }
}

pub proof fn a_retired_partial_cluster_is_unmapped_and_unpinned(v: LedgerView, index: int)
    requires valid(v), 0 <= index < v.slots.len(), v.slots[index].phase == 4,
    ensures v.slots[index].pins == 0, v.slots[index].pending.len() == 0,
        forall|j: int| 0 <= j < v.geometry.cluster_ratio ==> (#[trigger] v.slots[index].mapped[j]) == 0,
{
}

pub proof fn changing_a_slot_without_changing_its_phase_preserves_accounting(a: LedgerView, b: LedgerView, index: int)
    requires only_slot_changed(a, b, index), 0 <= index < a.slots.len(),
        active(a.slots[index]) == active(b.slots[index]),
    ensures occupied_count(a.slots) == occupied_count(b.slots),
{
    assert(b.slots =~= a.slots.update(index, b.slots[index]));
    occupied_count_update(a.slots, index, b.slots[index]);
}

proof fn pending_range_excludes_point(v: LedgerView, index: int, start: u32, length: u32, point: int)
    requires 0 <= index < v.slots.len(), !pending_overlap(v, index, start, length),
        start <= point < start as nat + length,
    ensures forall|k: int| 0 <= k < v.slots[index].pending.len() ==>
        !((#[trigger] v.slots[index].pending[k]).start <= point
            < v.slots[index].pending[k].start as nat + v.slots[index].pending[k].length),
{
    assert forall|k: int| 0 <= k < v.slots[index].pending.len() implies
        !((#[trigger] v.slots[index].pending[k]).start <= point
            < v.slots[index].pending[k].start as nat + v.slots[index].pending[k].length) by {
        let item = v.slots[index].pending[k];
        if item.start <= point < item.start as nat + item.length {
            assert(ranges_overlap(start, length, item.start, item.length));
            assert(pending_overlap(v, index, start, length));
            assert(false);
        }
    }
}

pub open spec fn key_index(v: LedgerView, key: KeyView) -> int { key.cluster as int - v.first_cluster as int }

pub open spec fn command_matches(v: LedgerView, command: CommandView, index: int, pending: int) -> bool {
    &&& 0 <= index < v.slots.len() && command.domain == v.domain
    &&& command.cluster as nat == v.first_cluster as nat + index
    &&& command.generation == v.slots[index].generation && 2 <= v.slots[index].phase <= 3
    &&& 0 <= pending < v.slots[index].pending.len()
    &&& v.slots[index].pending[pending].id == command.request
    &&& v.slots[index].pending[pending].start == command.start
    &&& v.slots[index].pending[pending].length == command.length
    &&& command.physical as nat == command.cluster as nat * v.geometry.cluster_ratio + command.start
}

pub open spec fn unchanged_allocation(a: LedgerView, b: LedgerView, index: int) -> bool {
    only_slot_changed(a, b, index) && a.live_blocks == b.live_blocks && a.next_request == b.next_request
}

pub open spec fn range_set(old: Seq<u8>, new: Seq<u8>, start: u32, length: u32, value: u8) -> bool {
    new.len() == old.len() && forall|i: int| 0 <= i < old.len() ==>
        (#[trigger] new[i]) == if start <= i < start as nat + length { value } else { old[i] }
}

pub open spec fn init_set(old: Seq<bool>, new: Seq<bool>, start: u32, length: u32, value: bool) -> bool {
    new.len() == old.len() && forall|i: int| 0 <= i < old.len() ==>
        (#[trigger] new[i]) == if start <= i < start as nat + length { value } else { old[i] }
}

pub open spec fn allocation_bitmap(v: LedgerView, raw: Seq<u8>) -> bool {
    raw.len() == v.bitmap.len() && forall|i: int| 0 <= i < raw.len() * 8 ==>
        (#[trigger] bitmap_bit(raw, i as u32)) == if v.first_bit <= i < v.first_bit as nat + v.slots.len() {
            v.slots[i - v.first_bit as int].phase != 1
        } else { bitmap_bit(v.bitmap, i as u32) }
}

fn bit(raw: &[u8], index: u32) -> (r: bool)
    ensures r == bitmap_bit(raw@, index),
{
    let byte = (index / 8) as usize;
    if byte >= raw.len() { return true; }
    (raw[byte] >> ((index % 8) as u8)) & 1u8 != 0
}

pub open spec fn byte_bit(byte: u8, bit: u8) -> bool { (byte >> bit) & 1u8 != 0 }

fn put_bit(byte: u8, bit: u8, set: bool) -> (r: u8)
    ensures forall|j: u8| j < 8 ==> (#[trigger] byte_bit(r, j)) == if j == bit { set } else { byte_bit(byte, j) },
{
    if bit >= 8 { return byte; }
    let mask = 1u8 << bit;
    let result = if set { byte | mask } else { byte & !mask };
    proof {
        assert forall|j: u8| j < 8 implies (#[trigger] byte_bit(result, j)) == if j == bit { set } else { byte_bit(byte, j) } by {
            assert(((((if set { byte | (1u8 << bit) } else { byte & !(1u8 << bit) }) >> j) & 1u8) != 0)
                == (if j == bit { set } else { (byte >> j) & 1u8 != 0 })) by (bit_vector)
                requires bit < 8, j < 8;
        }
    }
    result
}

fn same_owner(a: Owner, b: Owner) -> (r: bool)
    ensures r == (a == b),
{ a.inode == b.inode && a.generation == b.generation }

proof fn product_below_limit(a: u64, b: u64)
    requires b > 0, a as int <= 18446744073709551615int / b as int,
    ensures a as nat * b as nat <= 18446744073709551615,
{
    let ghost bound = 18446744073709551615int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(bound, b as int);
    vstd::arithmetic::div_mod::lemma_mod_bound(bound, b as int);
    vstd::arithmetic::mul::lemma_mul_inequality(a as int, bound / (b as int), b as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(b as int, bound / (b as int));
}

fn overlaps(a: u32, alen: u32, b: u32, blen: u32) -> (r: bool)
    ensures r == ranges_overlap(a, alen, b, blen),
{
    (a as u64) < b as u64 + blen as u64 && (b as u64) < a as u64 + alen as u64
}

impl Key {
    pub closed spec fn view(&self) -> KeyView {
        KeyView { domain: self.domain, cluster: self.cluster, generation: self.generation,
            owner: self.owner, logical_start: self.logical_start }
    }
    pub fn owner(&self) -> (r: Owner) ensures r == self.view().owner,
    { self.owner }
    pub fn cluster(&self) -> (r: u64) ensures r == self.view().cluster,
    { self.cluster }
    pub fn generation(&self) -> (r: u64) ensures r == self.view().generation,
    { self.generation }
    pub fn logical_start(&self) -> (r: u32) ensures r == self.view().logical_start,
    { self.logical_start }
}

impl Initialization {
    pub closed spec fn view(&self) -> CommandView {
        CommandView { domain: self.domain, cluster: self.cluster, generation: self.generation,
            request: self.request, start: self.start, length: self.length, physical: self.physical }
    }
    pub fn physical_start(&self) -> (r: u64) ensures r == self.view().physical,
    { self.physical }
    pub fn blocks(&self) -> (r: u32) ensures r == self.view().length,
    { self.length }
    pub fn request_id(&self) -> (r: u64) ensures r == self.view().request,
    { self.request }
}

impl ReadPin {
    pub closed spec fn view(&self) -> TicketView {
        TicketView { domain: self.domain, cluster: self.cluster, generation: self.generation }
    }
}

impl Retirement {
    pub closed spec fn view(&self) -> TicketView {
        TicketView { domain: self.domain, cluster: self.cluster, generation: self.generation }
    }
}

impl Ledger {
    pub closed spec fn view(&self) -> LedgerView { self.state.view() }
    pub closed spec fn wf(&self) -> bool { valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn from_bitmap(geometry: Geometry, domain: u64, group: u32, raw: &[u8],
        free_clusters: u32, first_bit: u32, count: u32) -> (r: Result<Self, Error>)
        ensures match r { Ok(ledger) => ledger.wf() && ledger.view().geometry == geometry
            && ledger.view().domain == domain && ledger.view().bitmap == raw@
            && group < geometry.groups
            && ledger.view().first_cluster as nat == meta_bg::first_block(geometry, group)
                / geometry.cluster_ratio as nat + first_bit
            && free_clusters as nat == free_count(raw@, (raw.len() as nat * 8) as nat)
            && ledger.view().first_bit == first_bit && ledger.view().slots.len() == count
            && ledger.view().live_blocks == 0 && ledger.view().next_request == 1,
            Err(_) => true },
    {
        match LedgerState::from_bitmap(geometry, domain, group, raw, free_clusters, first_bit, count) {
            Ok(state) => Ok(Ledger { state }),
            Err(error) => Err(error),
        }
    }

    pub fn reserve(self, cluster: u64, owner: Owner, logical_start: u32)
        -> (r: (Self, Result<Key, Error>))
        ensures r.0.wf(), match r.1 {
            Ok(key) => {
                let i = key_index(self.view(), key.view());
                &&& key.view().cluster == cluster && key.view().owner == owner && key.view().logical_start == logical_start
                &&& key_matches(r.0.view(), key.view(), i)
                &&& self.view().slots[i].phase == 1 && r.0.view().slots[i].phase == 2
                &&& key.view().generation as nat == self.view().slots[i].generation as nat + 1
                &&& only_slot_changed(self.view(), r.0.view(), i)
                &&& r.0.view().next_request == self.view().next_request
                &&& r.0.view().live_blocks as nat == self.view().live_blocks as nat + self.view().geometry.cluster_ratio
            },
            Err(_) => r.0.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); }
        let Ledger { mut state } = self;
        let result = state.reserve(cluster, owner, logical_start);
        (Ledger { state }, result)
    }

    pub fn commit_reservation(self, key: &Key) -> (r: (Self, Result<(), Error>))
        ensures r.0.wf(), match r.1 {
            Ok(()) => {
                let i = key_index(self.view(), key.view());
                &&& key_matches(self.view(), key.view(), i) && self.view().slots[i].phase == 2
                &&& unchanged_allocation(self.view(), r.0.view(), i)
                &&& r.0.view().slots[i] == (SlotView { phase: 3, ..self.view().slots[i] })
            }, Err(_) => r.0.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); }
        let Ledger { mut state } = self;
        let result = state.commit_reservation(key);
        (Ledger { state }, result)
    }

    pub fn cancel_reservation(self, key: Key) -> (r: (Self, Result<(), (Key, Error)>))
        ensures r.0.wf(), match r.1 {
            Ok(()) => {
                let i = key_index(self.view(), key.view());
                &&& key_matches(self.view(), key.view(), i) && self.view().slots[i].phase == 2
                &&& self.view().slots[i].pins == 0 && self.view().slots[i].pending.len() == 0
                &&& only_slot_changed(self.view(), r.0.view(), i)
                &&& r.0.view().slots[i].phase == 1
                && r.0.view().slots[i].generation == self.view().slots[i].generation && r.0.view().next_request == self.view().next_request
                &&& r.0.view().live_blocks as nat + self.view().geometry.cluster_ratio == self.view().live_blocks
            }, Err((returned, _)) => returned.view() == key.view() && r.0.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); }
        let Ledger { mut state } = self;
        let result = state.cancel_reservation(key);
        (Ledger { state }, result)
    }

    pub fn begin_initialization(self, key: &Key, start: u32, length: u32)
        -> (r: (Self, Result<Initialization, Error>))
        ensures r.0.wf(), match r.1 {
            Ok(command) => {
                let i = key_index(self.view(), key.view());
                let slot = self.view().slots[i];
                &&& key_matches(self.view(), key.view(), i) && range_valid(self.view(), i, start, length)
                &&& slot.pins == 0 && !pending_overlap(self.view(), i, start, length)
                &&& command.view() == (CommandView { domain: self.view().domain, cluster: key.view().cluster,
                    generation: key.view().generation, request: self.view().next_request, start, length,
                    physical: (key.view().cluster as nat * self.view().geometry.cluster_ratio + start) as u64 })
                &&& only_slot_changed(self.view(), r.0.view(), i)
                &&& r.0.view().live_blocks == self.view().live_blocks
                &&& r.0.view().next_request as nat == self.view().next_request as nat + 1
                &&& r.0.view().slots[i] == (SlotView { pending: slot.pending.push(PendingView {
                    id: command.view().request, start, length, faulted: false }),
                    initialized: r.0.view().slots[i].initialized, ..slot })
                &&& init_set(slot.initialized, r.0.view().slots[i].initialized, start, length, false)
            }, Err(_) => r.0.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); }
        let Ledger { mut state } = self;
        let result = state.begin_initialization(key, start, length);
        (Ledger { state }, result)
    }

    pub fn complete_initialization(self, command: Initialization, completion: Completion)
        -> (r: (Self, Result<(), (Initialization, Error)>))
        ensures r.0.wf(), match r.1 {
            Ok(()) => exists|i: int, at: int| (#[trigger] command_matches(self.view(), command.view(), i, at))
                && !self.view().slots[i].pending[at].faulted
                && completion is Succeeded
                && unchanged_allocation(self.view(), r.0.view(), i)
                && r.0.view().slots[i].pending == self.view().slots[i].pending.remove(at)
                && r.0.view().slots[i].mapped == self.view().slots[i].mapped
                && init_set(self.view().slots[i].initialized, r.0.view().slots[i].initialized,
                    command.view().start, command.view().length, true),
            Err((returned, error)) => returned.view() == command.view()
                && if error is InitializationFailed {
                    completion is Failed
                    && exists|i: int, at: int| (#[trigger] command_matches(self.view(), command.view(), i, at))
                        && !self.view().slots[i].pending[at].faulted
                        && unchanged_allocation(self.view(), r.0.view(), i)
                        && r.0.view().slots[i] == (SlotView {
                            pending: self.view().slots[i].pending.update(at,
                                PendingView { faulted: true, ..self.view().slots[i].pending[at] }),
                            ..self.view().slots[i] })
                } else { r.0.view() == self.view() },
        },
    {
        proof { use_type_invariant(&self); }
        let Ledger { mut state } = self;
        let result = state.complete_initialization(command, completion);
        (Ledger { state }, result)
    }

    pub fn discard_initialization_after_reset(self, command: Initialization, quiescent: bool)
        -> (r: (Self, Result<(), (Initialization, Error)>))
        ensures r.0.wf(), match r.1 {
            Ok(()) => quiescent && exists|i: int, at: int| (#[trigger] command_matches(self.view(), command.view(), i, at))
                && unchanged_allocation(self.view(), r.0.view(), i)
                && r.0.view().slots[i] == (SlotView {
                    pending: self.view().slots[i].pending.remove(at),
                    ..self.view().slots[i] }),
            Err((returned, _)) => returned.view() == command.view() && r.0.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); }
        let Ledger { mut state } = self;
        let result = state.discard_initialization_after_reset(command, quiescent);
        (Ledger { state }, result)
    }

    pub fn map_range(self, key: &Key, start: u32, length: u32, written: bool)
        -> (r: (Self, Result<(), Error>))
        ensures r.0.wf(), match r.1 {
            Ok(()) => {
                let i = key_index(self.view(), key.view());
                &&& key_matches(self.view(), key.view(), i) && self.view().slots[i].phase == 3
                &&& self.view().slots[i].pins == 0 && !pending_overlap(self.view(), i, start, length)
                &&& range_valid(self.view(), i, start, length)
                &&& (forall|j: int| start <= j < start as nat + length ==>
                    (#[trigger] self.view().slots[i].mapped[j]) == 0 && (!written || self.view().slots[i].initialized[j]))
                &&& unchanged_allocation(self.view(), r.0.view(), i)
                &&& range_set(self.view().slots[i].mapped, r.0.view().slots[i].mapped, start, length, if written { 2 } else { 1 })
                &&& r.0.view().slots[i].initialized == self.view().slots[i].initialized
                &&& r.0.view().slots[i].pending == self.view().slots[i].pending
            }, Err(_) => r.0.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); }
        let Ledger { mut state } = self;
        let result = state.map_range(key, start, length, written);
        (Ledger { state }, result)
    }

    pub fn convert_written(self, key: &Key, start: u32, length: u32) -> (r: (Self, Result<(), Error>))
        ensures r.0.wf(), match r.1 {
            Ok(()) => {
                let i = key_index(self.view(), key.view());
                &&& key_matches(self.view(), key.view(), i) && self.view().slots[i].phase == 3
                &&& self.view().slots[i].pins == 0 && !pending_overlap(self.view(), i, start, length)
                &&& range_valid(self.view(), i, start, length)
                &&& (forall|j: int| start <= j < start as nat + length ==>
                    (#[trigger] self.view().slots[i].mapped[j]) == 1 && self.view().slots[i].initialized[j])
                &&& unchanged_allocation(self.view(), r.0.view(), i)
                &&& range_set(self.view().slots[i].mapped, r.0.view().slots[i].mapped, start, length, 2)
                &&& r.0.view().slots[i].initialized == self.view().slots[i].initialized
                &&& r.0.view().slots[i].pending == self.view().slots[i].pending
            }, Err(_) => r.0.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); }
        let Ledger { mut state } = self;
        let result = state.convert_written(key, start, length);
        (Ledger { state }, result)
    }

    pub fn unmap_range(self, key: &Key, start: u32, length: u32) -> (r: (Self, Result<(), Error>))
        ensures r.0.wf(), match r.1 {
            Ok(()) => {
                let i = key_index(self.view(), key.view());
                &&& key_matches(self.view(), key.view(), i) && self.view().slots[i].phase == 3
                &&& self.view().slots[i].pins == 0 && !pending_overlap(self.view(), i, start, length)
                &&& range_valid(self.view(), i, start, length)
                &&& unchanged_allocation(self.view(), r.0.view(), i)
                &&& range_set(self.view().slots[i].mapped, r.0.view().slots[i].mapped, start, length, 0)
                &&& init_set(self.view().slots[i].initialized, r.0.view().slots[i].initialized, start, length, false)
                &&& r.0.view().slots[i].pending == self.view().slots[i].pending
            }, Err(_) => r.0.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); }
        let Ledger { mut state } = self;
        let result = state.unmap_range(key, start, length);
        (Ledger { state }, result)
    }

    pub fn read_block(&self, key: &Key, logical: u32) -> (r: Result<ReadDecision, Error>)
        ensures self.wf(), match r {
            Ok(decision) => {
                let i = key_index(self.view(), key.view());
                let offset = logical as int - key.view().logical_start as int;
                &&& key_matches(self.view(), key.view(), i) && self.view().slots[i].phase == 3
                &&& 0 <= offset < self.view().geometry.cluster_ratio && logical < 4294967295
                &&& match decision {
                    ReadDecision::Zero => self.view().slots[i].mapped[offset] <= 1,
                    ReadDecision::Initialized(block) => self.view().slots[i].mapped[offset] == 2
                        && self.view().slots[i].initialized[offset]
                        && block as nat == key.view().cluster as nat * self.view().geometry.cluster_ratio + offset
                        && self.view().geometry.first_data <= block < self.view().geometry.blocks,
                }
            }, Err(_) => true,
        },
    {
        proof { use_type_invariant(&*self); }
        self.state.read_block(key, logical)
    }

    pub fn pin(self, key: &Key) -> (r: (Self, Result<ReadPin, Error>))
        ensures r.0.wf(), match r.1 {
            Ok(pin) => {
                let i = key_index(self.view(), key.view());
                &&& key_matches(self.view(), key.view(), i) && self.view().slots[i].phase == 3
                &&& self.view().slots[i].pending.len() == 0
                &&& pin.view() == (TicketView { domain: key.view().domain, cluster: key.view().cluster, generation: key.view().generation })
                &&& unchanged_allocation(self.view(), r.0.view(), i)
                &&& r.0.view().slots[i] == (SlotView { pins: (self.view().slots[i].pins + 1) as u32, ..self.view().slots[i] })
            }, Err(_) => r.0.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); }
        let Ledger { mut state } = self;
        let result = state.pin(key);
        (Ledger { state }, result)
    }

    pub fn unpin(self, pin: ReadPin) -> (r: (Self, Result<(), (ReadPin, Error)>))
        ensures r.0.wf(), match r.1 {
            Ok(()) => exists|i: int| 0 <= i < self.view().slots.len()
                && pin.view().domain == self.view().domain
                && pin.view().cluster as int == self.view().first_cluster as int + i
                && pin.view().generation == (#[trigger] self.view().slots[i]).generation
                && self.view().slots[i].pins > 0
                && unchanged_allocation(self.view(), r.0.view(), i)
                && r.0.view().slots[i] == (SlotView { pins: (self.view().slots[i].pins - 1) as u32, ..self.view().slots[i] }),
            Err((returned, _)) => returned.view() == pin.view() && r.0.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); }
        let Ledger { mut state } = self;
        let result = state.unpin(pin);
        (Ledger { state }, result)
    }

    pub fn retire(self, key: Key) -> (r: (Self, Result<Retirement, (Key, Error)>))
        ensures r.0.wf(), match r.1 {
            Ok(ticket) => {
                let i = key_index(self.view(), key.view());
                &&& key_matches(self.view(), key.view(), i) && self.view().slots[i].phase == 3
                &&& self.view().slots[i].pins == 0 && self.view().slots[i].pending.len() == 0
                &&& (forall|j: int| 0 <= j < self.view().geometry.cluster_ratio ==> (#[trigger] self.view().slots[i].mapped[j]) == 0)
                &&& ticket.view() == (TicketView { domain: key.view().domain, cluster: key.view().cluster, generation: key.view().generation })
                &&& unchanged_allocation(self.view(), r.0.view(), i)
                &&& r.0.view().slots[i] == (SlotView { phase: 4, ..self.view().slots[i] })
            }, Err((returned, _)) => returned.view() == key.view() && r.0.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); }
        let Ledger { mut state } = self;
        let result = state.retire(key);
        (Ledger { state }, result)
    }

    pub fn reclaim_after_checkpoint(self, retired: Retirement, succeeded: bool)
        -> (r: (Self, Result<(), (Retirement, Error)>))
        ensures r.0.wf(), match r.1 {
            Ok(()) => succeeded && exists|i: int| 0 <= i < self.view().slots.len()
                && retired.view().domain == self.view().domain
                && retired.view().cluster as int == self.view().first_cluster as int + i
                && retired.view().generation == (#[trigger] self.view().slots[i]).generation
                && self.view().slots[i].phase == 4
                && self.view().slots[i].pins == 0 && self.view().slots[i].pending.len() == 0
                && only_slot_changed(self.view(), r.0.view(), i)
                && r.0.view().slots[i].phase == 1
                && r.0.view().slots[i].generation == self.view().slots[i].generation
                && r.0.view().next_request == self.view().next_request
                && r.0.view().live_blocks as nat + self.view().geometry.cluster_ratio == self.view().live_blocks,
            Err((returned, _)) => returned.view() == retired.view() && r.0.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); }
        let Ledger { mut state } = self;
        let result = state.reclaim_after_checkpoint(retired, succeeded);
        (Ledger { state }, result)
    }

    pub fn bitmap_bytes(&self) -> (r: Vec<u8>)
        ensures self.wf(), allocation_bitmap(self.view(), r@),
    {
        proof { use_type_invariant(&*self); }
        self.state.bitmap_bytes()
    }
}

impl LedgerState {
    spec fn view(&self) -> LedgerView {
        LedgerView { geometry: self.geometry, domain: self.domain, first_cluster: self.first_cluster,
            first_bit: self.first_bit, slots: slot_views(self.slots@),
            bitmap: self.bitmap@, live_blocks: self.live_blocks, next_request: self.next_request }
    }
    spec fn wf(&self) -> bool { valid(self.view()) }

    /// Import actual cluster bitmap bytes. Already allocated clusters remain
    /// unavailable until a separate source-inode ownership import is supplied.
    /// The domain is a caller-managed allocator generation, not a global lease.
    fn from_bitmap(geometry: Geometry, domain: u64, group: u32, raw: &[u8],
        free_clusters: u32, first_bit: u32, count: u32) -> (r: Result<Self, Error>)
        ensures match r { Ok(ledger) => ledger.wf() && ledger.view().geometry == geometry
            && ledger.view().domain == domain && ledger.view().bitmap == raw@
            && group < geometry.groups
            && ledger.view().first_cluster as nat == meta_bg::first_block(geometry, group)
                / geometry.cluster_ratio as nat + first_bit
            && free_clusters as nat == free_count(raw@, (raw.len() as nat * 8) as nat)
            && ledger.view().first_bit == first_bit && ledger.view().slots.len() == count
            && ledger.view().live_blocks == 0 && ledger.view().next_request == 1,
            Err(_) => true },
    {
        if !meta_bg::is_valid(geometry) || domain == 0 || raw.len() != geometry.block_bytes as usize {
            return Err(Error::Geometry);
        }
        let start = match meta_bg::group_first(geometry, group) {
            Some(start) => start, None => { return Err(Error::Outside); },
        };
        let remaining = geometry.blocks - start;
        let blocks = if remaining < geometry.blocks_per_group as u64 {
            remaining
        } else { geometry.blocks_per_group as u64 };
        let ratio = geometry.cluster_ratio as u64;
        // Linux rejects BIGALLOC with nonzero first_data_block; retain the
        // physical-coordinate premise here before interpreting bitmap bits.
        if start % ratio != 0 { return Err(Error::Geometry); }
        let valid = blocks / ratio + if blocks % ratio == 0 { 0u64 } else { 1u64 };
        if valid > geometry.block_bytes as u64 * 8 || valid > 4294967295 || count == 0 || (count as usize) > MAX_TRACKED_CLUSTERS
            || (first_bit as u64) > valid || (count as u64) > valid - first_bit as u64 {
            return Err(Error::Capacity);
        }
        let first_cluster = start / ratio;
        let mut index = 0u32;
        let mut free = 0u32;
        while index < geometry.block_bytes * 8
            invariant index <= geometry.block_bytes * 8, geometry.block_bytes <= 65536,
                free <= index, ratio > 0, free as nat == free_count(raw@, index as nat),
                forall|j: int| 0 <= j < index && !(#[trigger] bitmap_bit(raw@, j as u32)) ==>
                    j < valid && geometry.first_data <= (first_cluster as nat + j) * ratio
                        && (first_cluster as nat + j + 1) * ratio <= geometry.blocks,
            decreases geometry.block_bytes * 8 - index,
        {
            let set = bit(raw, index);
            if (index as u64) >= valid {
                if !set { return Err(Error::Bitmap); }
            } else if !set {
                if first_cluster > 18446744073709551615u64 - index as u64 { return Err(Error::Overflow); }
                let cluster = first_cluster + index as u64;
                if cluster > 18446744073709551615u64 / ratio { return Err(Error::Overflow); }
                proof { product_below_limit(cluster, ratio); }
                let physical = cluster * ratio;
                if physical < geometry.first_data || physical >= geometry.blocks
                    || ratio > geometry.blocks - physical { return Err(Error::Bitmap); }
                proof {
                    assert((first_cluster as int + index as int + 1) * ratio as int <= geometry.blocks) by (nonlinear_arith)
                        requires physical as int == (first_cluster as int + index as int) * ratio as int,
                            physical < geometry.blocks, ratio as int <= geometry.blocks as int - physical as int;
                }
                free += 1;
            }
            index += 1;
        }
        if free != free_clusters { return Err(Error::Bitmap); }
        let mut bitmap = Vec::new();
        let mut byte = 0usize;
        while byte < raw.len()
            invariant byte <= raw.len(), bitmap@ == raw@.take(byte as int),
            decreases raw.len() - byte,
        {
            bitmap.push(raw[byte]); byte += 1;
        }
        let mut slots = Vec::<Slot>::new();
        let mut ordinal = 0u32;
        while ordinal < count
            invariant ordinal <= count, slots.len() == ordinal,
                first_bit as u64 + count <= valid, valid <= geometry.block_bytes as nat * 8,
                geometry.block_bytes <= 65536, raw.len() == geometry.block_bytes,
                ratio == geometry.cluster_ratio, ratio > 0,
                forall|j: int| 0 <= j < geometry.block_bytes as nat * 8 && !(#[trigger] bitmap_bit(raw@, j as u32)) ==>
                    j < valid && geometry.first_data <= (first_cluster as nat + j) * ratio
                        && (first_cluster as nat + j + 1) * ratio <= geometry.blocks,
                forall|j: int| 0 <= j < slots.len() ==> {
                    let slot = (#[trigger] slots@[j]).view();
                    &&& slot_valid(slot, geometry.cluster_ratio, 1)
                    &&& !active(slot)
                    &&& (slot.phase == 0) == bitmap_bit(raw@, (first_bit as int + j) as u32)
                    &&& (slot.phase != 0 ==> geometry.first_data <= (first_cluster as nat + first_bit + j) * ratio
                        && (first_cluster as nat + first_bit + j + 1) * ratio <= geometry.blocks)
                },
            decreases count - ordinal,
        {
            let set = bit(raw, first_bit + ordinal);
            slots.push(Slot {
                phase: if set { 0 } else { 1 }, generation: 0,
                owner: Owner { inode: 0, generation: 0 }, logical_start: 0, pins: 0,
                mapped: Vec::new(), initialized: Vec::new(), pending: Vec::new(),
            });
            ordinal += 1;
        }
        if first_cluster > 18446744073709551615u64 - first_bit as u64 { return Err(Error::Overflow); }
        let window_first = first_cluster + first_bit as u64;
        if count as u64 > 18446744073709551615u64 - window_first { return Err(Error::Overflow); }
        proof {
            no_active_count_is_zero(Seq::new(slots.len() as nat, |j: int| slots@[j].view()));
        }
        Ok(LedgerState { geometry, domain, first_cluster: window_first,
            first_bit, slots, bitmap, live_blocks: 0, next_request: 1 })
    }

    fn index(&self, key: &Key) -> (r: Result<usize, Error>)
        requires self.wf(),
        ensures match r { Ok(index) => key_matches(self.view(), key.view(), index as int)
            && index < self.slots.len()
            && self.slots@[index as int].mapped.len() == self.geometry.cluster_ratio
            && self.slots@[index as int].initialized.len() == self.geometry.cluster_ratio,
            Err(_) => true },
    {
        if key.domain != self.domain || key.cluster < self.first_cluster { return Err(Error::Owner); }
        let index = key.cluster - self.first_cluster;
        if index >= self.slots.len() as u64 { return Err(Error::Outside); }
        let index = index as usize;
        let slot = &self.slots[index];
        if slot.generation != key.generation || !same_owner(slot.owner, key.owner)
            || slot.logical_start != key.logical_start { return Err(Error::Stale); }
        if slot.phase != 2 && slot.phase != 3 { return Err(Error::State); }
        if slot.mapped.len() != self.geometry.cluster_ratio as usize
            || slot.initialized.len() != slot.mapped.len() { return Err(Error::State); }
        Ok(index)
    }

    fn range(&self, index: usize, start: u32, length: u32) -> (r: bool)
        requires self.wf(),
        ensures r == range_valid(self.view(), index as int, start, length),
    {
        index < self.slots.len() && length > 0
            && start < self.geometry.cluster_ratio && length <= self.geometry.cluster_ratio - start
            && self.slots[index].logical_start as u64 + start as u64 + (length as u64) <= 4294967295
    }

    fn pending_overlap(&self, index: usize, start: u32, length: u32) -> (r: bool)
        requires self.wf(),
        ensures r == pending_overlap(self.view(), index as int, start, length),
    {
        if index >= self.slots.len() { return true; }
        let pending = &self.slots[index].pending;
        let mut i = 0usize;
        while i < pending.len()
            invariant index < self.slots.len(), self.wf(), i <= pending.len(),
                pending@ == self.slots@[index as int].pending@,
                forall|j: int| 0 <= j < i ==> !ranges_overlap(start, length,
                    (#[trigger] pending@[j]).start, pending@[j].length),
            decreases pending.len() - i,
        {
            if overlaps(start, length, pending[i].start, pending[i].length) {
                assert(self.view().slots[index as int].pending[i as int].start == pending@[i as int].start);
                assert(self.view().slots[index as int].pending[i as int].length == pending@[i as int].length);
                assert(pending_overlap(self.view(), index as int, start, length));
                return true;
            }
            i += 1;
        }
        false
    }

    fn reserve(&mut self, cluster: u64, owner: Owner, logical_start: u32)
        -> (r: Result<Key, Error>)
        requires self.wf(),
        ensures final(self).wf(), match r {
            Ok(key) => {
                let i = key_index(old(self).view(), key.view());
                &&& key.view().cluster == cluster && key.view().owner == owner && key.view().logical_start == logical_start
                &&& key_matches(final(self).view(), key.view(), i)
                &&& old(self).view().slots[i].phase == 1 && final(self).view().slots[i].phase == 2
                &&& key.view().generation as nat == old(self).view().slots[i].generation as nat + 1
                &&& only_slot_changed(old(self).view(), final(self).view(), i)
                &&& final(self).view().next_request == old(self).view().next_request
                &&& final(self).view().live_blocks as nat == old(self).view().live_blocks as nat + old(self).view().geometry.cluster_ratio
            },
            Err(_) => final(self).view() == old(self).view(),
        },
    {
        let ghost before = self.view();
        if !meta_bg::is_valid(self.geometry) || owner.inode == 0
            || logical_start == 4294967295 || logical_start % self.geometry.cluster_ratio != 0 {
            return Err(Error::Geometry);
        }
        if cluster < self.first_cluster || cluster - self.first_cluster >= self.slots.len() as u64 {
            return Err(Error::Outside);
        }
        let index = (cluster - self.first_cluster) as usize;
        if self.slots[index].phase != 1 { return Err(Error::Busy); }
        if self.slots[index].generation == 18446744073709551615 { return Err(Error::Overflow); }
        // A partial cluster belongs to exactly one inode generation and one
        // logical cluster, including reservations and checkpoint-retired slots.
        let mut other = 0usize;
        while other < self.slots.len()
            invariant other <= self.slots.len(), self.view() == before, self.wf(),
                forall|j: int| 0 <= j < other && active(before.slots[j]) ==>
                    (#[trigger] before.slots[j]).owner != owner || before.slots[j].logical_start != logical_start,
            decreases self.slots.len() - other,
        {
            if self.slots[other].phase >= 2 && same_owner(self.slots[other].owner, owner)
                && self.slots[other].logical_start == logical_start {
                return Err(Error::Busy);
            }
            other += 1;
        }
        let ratio = self.geometry.cluster_ratio as u64;
        if self.live_blocks > MAX_LIVE_BLOCKS || ratio > MAX_LIVE_BLOCKS - self.live_blocks {
            return Err(Error::Capacity);
        }
        if cluster > 18446744073709551615u64 / ratio { return Err(Error::Overflow); }
        proof { product_below_limit(cluster, ratio); }
        let physical = cluster * ratio;
        if physical < self.geometry.first_data || physical >= self.geometry.blocks
            || ratio > self.geometry.blocks - physical { return Err(Error::Outside); }
        let mut mapped = Vec::new();
        let mut initialized = Vec::new();
        let mut i = 0u32;
        while i < self.geometry.cluster_ratio
            invariant i <= self.geometry.cluster_ratio, mapped.len() == i, initialized.len() == i,
                self.view() == before, self.wf(),
                forall|j: int| 0 <= j < i ==> (#[trigger] mapped@[j]) == 0,
                forall|j: int| 0 <= j < i ==> (#[trigger] initialized@[j]) == false,
            decreases self.geometry.cluster_ratio - i,
        {
            let ghost prior_mapped = mapped@;
            let ghost prior_initialized = initialized@;
            mapped.push(0u8); initialized.push(false);
            assert forall|j: int| 0 <= j < i as int + 1 implies (#[trigger] mapped@[j]) == 0 by {
                if j < i { assert(prior_mapped[j] == 0); }
            }
            assert forall|j: int| 0 <= j < i as int + 1 implies (#[trigger] initialized@[j]) == false by {
                if j < i { assert(prior_initialized[j] == false); }
            }
            i += 1;
        }
        let generation = self.slots[index].generation + 1;
        self.slots[index] = Slot { phase: 2, generation, owner, logical_start, pins: 0,
            mapped, initialized, pending: Vec::new() };
        self.live_blocks += ratio;
        proof {
            assert(self.view().slots =~= before.slots.update(index as int, self.view().slots[index as int]));
            occupied_count_update(before.slots, index as int, self.view().slots[index as int]);
            assert(slot_valid(self.view().slots[index as int], self.geometry.cluster_ratio, self.next_request));
            reserve_update_valid(before, index as int, self.view().slots[index as int]);
        }
        Ok(Key { domain: self.domain, cluster, generation, owner, logical_start })
    }

    /// Commit allocator ownership only. JBD2 commit durability is separate.
    fn commit_reservation(&mut self, key: &Key) -> (r: Result<(), Error>)
        requires self.wf(),
        ensures final(self).wf(), match r {
            Ok(()) => {
                let i = key_index(old(self).view(), key.view());
                &&& key_matches(old(self).view(), key.view(), i) && old(self).view().slots[i].phase == 2
                &&& unchanged_allocation(old(self).view(), final(self).view(), i)
                &&& final(self).view().slots[i] == (SlotView { phase: 3, ..old(self).view().slots[i] })
            }, Err(_) => final(self).view() == old(self).view(),
        },
    {
        let ghost before = self.view();
        let index = match self.index(key) { Ok(index) => index, Err(error) => { return Err(error); } };
        if self.slots[index].phase != 2 { return Err(Error::State); }
        self.slots[index].phase = 3;
        proof {
            assert(self.view().slots =~= before.slots.update(index as int, self.view().slots[index as int]));
            occupied_count_update(before.slots, index as int, self.view().slots[index as int]);
        }
        Ok(())
    }

    fn cancel_reservation(&mut self, key: Key) -> (r: Result<(), (Key, Error)>)
        requires self.wf(),
        ensures final(self).wf(), match r {
            Ok(()) => {
                let i = key_index(old(self).view(), key.view());
                &&& key_matches(old(self).view(), key.view(), i) && old(self).view().slots[i].phase == 2
                &&& old(self).view().slots[i].pins == 0 && old(self).view().slots[i].pending.len() == 0
                &&& only_slot_changed(old(self).view(), final(self).view(), i)
                &&& final(self).view().slots[i].phase == 1
                && final(self).view().slots[i].generation == old(self).view().slots[i].generation && final(self).view().next_request == old(self).view().next_request
                &&& final(self).view().live_blocks as nat + old(self).view().geometry.cluster_ratio == old(self).view().live_blocks
            }, Err((returned, _)) => returned.view() == key.view() && final(self).view() == old(self).view(),
        },
    {
        let ghost before = self.view();
        let index = match self.index(&key) { Ok(index) => index, Err(error) => { return Err((key, error)); } };
        if self.slots[index].phase != 2 || self.slots[index].pins != 0
            || self.slots[index].pending.len() != 0 { return Err((key, Error::Busy)); }
        let ratio = self.geometry.cluster_ratio as u64;
        if self.live_blocks < ratio { return Err((key, Error::State)); }
        self.slots[index].phase = 1;
        self.slots[index].owner = Owner { inode: 0, generation: 0 };
        self.slots[index].logical_start = 0;
        self.slots[index].mapped = Vec::new();
        self.slots[index].initialized = Vec::new();
        self.live_blocks -= ratio;
        proof {
            assert(self.view().slots =~= before.slots.update(index as int, self.view().slots[index as int]));
            occupied_count_update(before.slots, index as int, self.view().slots[index as int]);
            assert(slot_valid(self.view().slots[index as int], self.geometry.cluster_ratio, self.next_request));
            release_update_valid(before, index as int, self.view().slots[index as int]);
        }
        Ok(())
    }

    /// Issue initialization for previously unreadable blocks. Its success
    /// callback must later refine actual CortenMM/OSTD zero/write completion.
    fn begin_initialization(&mut self, key: &Key, start: u32, length: u32)
        -> (r: Result<Initialization, Error>)
        requires self.wf(),
        ensures final(self).wf(), match r {
            Ok(command) => {
                let i = key_index(old(self).view(), key.view());
                let slot = old(self).view().slots[i];
                &&& key_matches(old(self).view(), key.view(), i) && range_valid(old(self).view(), i, start, length)
                &&& slot.pins == 0 && !pending_overlap(old(self).view(), i, start, length)
                &&& command.view() == (CommandView { domain: old(self).view().domain, cluster: key.view().cluster,
                    generation: key.view().generation, request: old(self).view().next_request, start, length,
                    physical: (key.view().cluster as nat * old(self).view().geometry.cluster_ratio + start) as u64 })
                &&& only_slot_changed(old(self).view(), final(self).view(), i)
                &&& final(self).view().live_blocks == old(self).view().live_blocks
                &&& final(self).view().next_request as nat == old(self).view().next_request as nat + 1
                &&& final(self).view().slots[i] == (SlotView { pending: slot.pending.push(PendingView {
                    id: command.view().request, start, length, faulted: false }),
                    initialized: final(self).view().slots[i].initialized, ..slot })
                &&& init_set(slot.initialized, final(self).view().slots[i].initialized, start, length, false)
            }, Err(_) => final(self).view() == old(self).view(),
        },
    {
        let ghost before = self.view();
        let index = match self.index(key) { Ok(index) => index, Err(error) => { return Err(error); } };
        if !self.range(index, start, length) { return Err(Error::Outside); }
        if self.slots[index].pins != 0 || self.pending_overlap(index, start, length) {
            return Err(Error::Busy);
        }
        if self.slots[index].pending.len() >= MAX_PENDING { return Err(Error::Capacity); }
        if self.next_request == 18446744073709551615 { return Err(Error::Overflow); }
        let mut i = start;
        while i < start + length
            invariant index < self.slots.len(), index < before.slots.len(),
                start <= i <= start + length, start + length <= self.geometry.cluster_ratio,
                self.slots@[index as int].mapped.len() == self.geometry.cluster_ratio,
                self.slots@[index as int].initialized.len() == self.geometry.cluster_ratio,
                before.slots[index as int].mapped.len() == self.geometry.cluster_ratio,
                before.slots[index as int].initialized.len() == self.geometry.cluster_ratio,
                self.view() == before, self.wf(),
                forall|j: int| start <= j < i ==> (#[trigger] before.slots[index as int].mapped[j]) != 2,
            decreases start + length - i,
        {
            if self.slots[index].mapped[i as usize] == 2 { return Err(Error::Busy); }
            i += 1;
        }
        let ratio = self.geometry.cluster_ratio as u64;
        if key.cluster > 18446744073709551615u64 / ratio { return Err(Error::Overflow); }
        proof { product_below_limit(key.cluster, ratio); }
        let base = key.cluster * ratio;
        if (start as u64) > 18446744073709551615u64 - base { return Err(Error::Overflow); }
        let request = self.next_request;
        // New I/O invalidates any earlier initialization certificate for this
        // unreadable range. A failed/restarted write cannot reuse that old
        // certificate after reset; only a new successful callback restores it.
        i = start;
        while i < start + length
            invariant index < self.slots.len(), index < before.slots.len(),
                start <= i <= start + length, start + length <= self.geometry.cluster_ratio,
                self.slots@[index as int].mapped.len() == self.geometry.cluster_ratio,
                self.slots@[index as int].initialized.len() == self.geometry.cluster_ratio,
                before.slots[index as int].mapped.len() == self.geometry.cluster_ratio,
                before.slots[index as int].initialized.len() == self.geometry.cluster_ratio,
                key_matches(before, key.view(), index as int), range_valid(before, index as int, start, length),
                before.slots[index as int].pins == 0, before.slots[index as int].pending.len() < MAX_PENDING,
                before.next_request < 18446744073709551615,
                !pending_overlap(before, index as int, start, length),
                self.wf(), unchanged_allocation(before, self.view(), index as int),
                self.view().slots[index as int].phase == before.slots[index as int].phase,
                self.view().slots[index as int].generation == before.slots[index as int].generation,
                self.view().slots[index as int].owner == before.slots[index as int].owner,
                self.view().slots[index as int].logical_start == before.slots[index as int].logical_start,
                self.view().slots[index as int].pins == before.slots[index as int].pins,
                self.view().slots[index as int].mapped == before.slots[index as int].mapped,
                self.view().slots[index as int].pending == before.slots[index as int].pending,
                forall|j: int| start <= j < start as nat + length ==> (#[trigger] before.slots[index as int].mapped[j]) != 2,
                init_set(before.slots[index as int].initialized, self.view().slots[index as int].initialized,
                    start, (i - start) as u32, false),
            decreases start + length - i,
        {
            let ghost step_before = self.view();
            let ghost native_before = self.slots@;
            self.slots[index].initialized.set(i as usize, false);
            proof {
                assert(self.slots@ =~= native_before.update(index as int, self.slots@[index as int]));
                slot_views_update(native_before, index as int, self.slots@[index as int]);
                slot_init_false_valid(step_before.slots[index as int], self.geometry.cluster_ratio, self.next_request, i as int);
                assert(slot_valid(self.view().slots[index as int], self.geometry.cluster_ratio, self.next_request));
                same_ownership_update_valid(step_before, index as int, self.view().slots[index as int]);
                assert(only_slot_changed(step_before, self.view(), index as int));
                assert(only_slot_changed(before, self.view(), index as int));
                changing_a_slot_without_changing_its_phase_preserves_accounting(before, self.view(), index as int);
            }
            i += 1;
        }
        let ghost before_request = self.view();
        let ghost prior_pending = self.slots@[index as int].pending@;
        let ghost native_before = self.slots@;
        self.next_request += 1;
        proof { next_request_monotone_valid(before_request, self.next_request); }
        let ghost after_request = self.view();
        self.slots[index].pending.push(PendingRange { id: request, start, length, faulted: false });
        proof {
            pending_views_push(prior_pending, PendingRange { id: request, start, length, faulted: false });
            slot_pending_push_valid(before_request.slots[index as int], self.geometry.cluster_ratio,
                request, self.next_request, start, length);
            assert(self.view().slots[index as int] == (SlotView {
                pending: before_request.slots[index as int].pending.push(PendingView { id: request, start, length, faulted: false }),
                ..before_request.slots[index as int] }));
            assert(self.slots@ =~= native_before.update(index as int, self.slots@[index as int]));
            slot_views_update(native_before, index as int, self.slots@[index as int]);
            same_ownership_update_valid(after_request, index as int, self.view().slots[index as int]);
            assert(self.view().slots =~= before.slots.update(index as int, self.view().slots[index as int]));
            occupied_count_update(before.slots, index as int, self.view().slots[index as int]);
        }
        Ok(Initialization { domain: self.domain, cluster: key.cluster, generation: key.generation,
            request, start, length, physical: base + start as u64 })
    }

    fn complete_initialization(&mut self, command: Initialization, completion: Completion)
        -> (r: Result<(), (Initialization, Error)>)
        requires self.wf(),
        ensures final(self).wf(), match r {
            Ok(()) => exists|i: int, at: int| (#[trigger] command_matches(old(self).view(), command.view(), i, at))
                && !old(self).view().slots[i].pending[at].faulted
                && completion is Succeeded
                && unchanged_allocation(old(self).view(), final(self).view(), i)
                && final(self).view().slots[i].pending == old(self).view().slots[i].pending.remove(at)
                && final(self).view().slots[i].mapped == old(self).view().slots[i].mapped
                && init_set(old(self).view().slots[i].initialized, final(self).view().slots[i].initialized,
                    command.view().start, command.view().length, true),
            Err((returned, error)) => returned.view() == command.view()
                && if error is InitializationFailed {
                    completion is Failed
                    && exists|i: int, at: int| (#[trigger] command_matches(old(self).view(), command.view(), i, at))
                        && !old(self).view().slots[i].pending[at].faulted
                        && unchanged_allocation(old(self).view(), final(self).view(), i)
                        && final(self).view().slots[i] == (SlotView {
                            pending: old(self).view().slots[i].pending.update(at,
                                PendingView { faulted: true, ..old(self).view().slots[i].pending[at] }),
                            ..old(self).view().slots[i] })
                } else { final(self).view() == old(self).view() },
        },
    {
        let ghost before = self.view();
        if command.domain != self.domain || command.cluster < self.first_cluster
            || command.cluster - self.first_cluster >= self.slots.len() as u64 { return Err((command, Error::Stale)); }
        let index = (command.cluster - self.first_cluster) as usize;
        if self.slots[index].generation != command.generation
            || (self.slots[index].phase != 2 && self.slots[index].phase != 3)
            || !self.range(index, command.start, command.length)
            || self.slots[index].initialized.len() != self.geometry.cluster_ratio as usize {
            return Err((command, Error::Stale));
        }
        let ratio = self.geometry.cluster_ratio as u64;
        if command.physical / ratio != command.cluster || command.physical % ratio != command.start as u64 {
            return Err((command, Error::Stale));
        }
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(command.physical as int, ratio as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(ratio as int, command.cluster as int);
            assert(command.physical as nat == command.cluster as nat * self.geometry.cluster_ratio + command.start);
        }
        let mut at = 0usize;
        while at < self.slots[index].pending.len()
            invariant index < self.slots.len(), index < before.slots.len(),
                at <= self.slots[index as int].pending.len(), self.view() == before, self.wf(),
                command.physical as nat == command.cluster as nat * self.geometry.cluster_ratio + command.start,
                forall|j: int| 0 <= j < at ==> (#[trigger] before.slots[index as int].pending[j]).id != command.request,
            decreases self.slots[index as int].pending.len() - at,
        {
            if self.slots[index].pending[at].id == command.request { break; }
            at += 1;
        }
        if at == self.slots[index].pending.len()
            || self.slots[index].pending[at].start != command.start
            || self.slots[index].pending[at].length != command.length { return Err((command, Error::Stale)); }
        assert(2 <= self.slots@[index as int].phase <= 3);
        assert(command_matches(before, command.view(), index as int, at as int));

        // A failed callback does not establish completion or cancellation.
        // The consumed command must survive until an adapter proves quiescence.
        if self.slots[index].pending[at].faulted {
            return Err((command, Error::Quiescence));
        }
        let succeeded = match completion {
            Completion::Succeeded => true,
            Completion::Failed => false,
        };
        if !succeeded {
            let ghost prior_pending = self.slots@[index as int].pending@;
            self.slots[index].pending[at].faulted = true;
            proof {
                assert(self.slots@[index as int].pending@ =~= prior_pending.update(at as int,
                    self.slots@[index as int].pending@[at as int]));
                pending_views_update(prior_pending, at as int, self.slots@[index as int].pending@[at as int]);
                assert(self.view().slots[index as int] == (SlotView {
                    pending: before.slots[index as int].pending.update(at as int,
                        PendingView { faulted: true, ..before.slots[index as int].pending[at as int] }),
                    ..before.slots[index as int] }));
                slot_pending_fault_valid(before.slots[index as int], self.geometry.cluster_ratio, self.next_request, at as int, true);
                assert(slot_valid(self.view().slots[index as int], self.geometry.cluster_ratio, self.next_request));
                same_ownership_update_valid(before, index as int, self.view().slots[index as int]);
                assert(self.view().slots =~= before.slots.update(index as int, self.view().slots[index as int]));
                occupied_count_update(before.slots, index as int, self.view().slots[index as int]);
            }
            return Err((command, Error::InitializationFailed));
        }
        let ghost prior_pending = self.slots@[index as int].pending@;
        self.slots[index].pending.remove(at);
        proof {
            pending_views_remove(prior_pending, at as int);
            slot_pending_remove_valid(before.slots[index as int], self.geometry.cluster_ratio, self.next_request, at as int);
            assert(self.view().slots[index as int] == (SlotView {
                pending: before.slots[index as int].pending.remove(at as int), ..before.slots[index as int] }));
            assert(slot_valid(self.view().slots[index as int], self.geometry.cluster_ratio, self.next_request));
            same_ownership_update_valid(before, index as int, self.view().slots[index as int]);
            assert(!pending_overlap(self.view(), index as int, command.start, command.length));
            assert(self.view().slots =~= before.slots.update(index as int, self.view().slots[index as int]));
            occupied_count_update(before.slots, index as int, self.view().slots[index as int]);
        }
        if succeeded {
            let mut i = command.start;
            while i < command.start + command.length
                invariant index < self.slots.len(), index < before.slots.len(),
                command.start <= i <= command.start + command.length,
                    command.start + command.length <= self.geometry.cluster_ratio,
                    self.slots@[index as int].mapped.len() == self.geometry.cluster_ratio,
                    self.slots@[index as int].initialized.len() == self.geometry.cluster_ratio,
                    before.slots[index as int].mapped.len() == self.geometry.cluster_ratio,
                    before.slots[index as int].initialized.len() == self.geometry.cluster_ratio,
                    self.wf(), unchanged_allocation(before, self.view(), index as int),
                    command_matches(before, command.view(), index as int, at as int),
                    !pending_overlap(self.view(), index as int, command.start, command.length),
                    !before.slots[index as int].pending[at as int].faulted,
                    self.view().slots[index as int].phase == before.slots[index as int].phase,
                    self.view().slots[index as int].generation == before.slots[index as int].generation,
                    self.view().slots[index as int].owner == before.slots[index as int].owner,
                    self.view().slots[index as int].logical_start == before.slots[index as int].logical_start,
                    self.view().slots[index as int].pins == before.slots[index as int].pins,
                    self.view().slots[index as int].mapped == before.slots[index as int].mapped,
                    self.view().slots[index as int].pending == before.slots[index as int].pending.remove(at as int),
                    init_set(before.slots[index as int].initialized, self.view().slots[index as int].initialized,
                        command.start, (i - command.start) as u32, true),
                decreases command.start + command.length - i,
            {
                let ghost step_before = self.view();
                let ghost native_before = self.slots@;
                self.slots[index].initialized.set(i as usize, true);
                proof {
                assert(self.slots@ =~= native_before.update(index as int, self.slots@[index as int]));
                slot_views_update(native_before, index as int, self.slots@[index as int]);
                pending_range_excludes_point(step_before, index as int, command.start, command.length, i as int);
                slot_init_true_valid(step_before.slots[index as int], self.geometry.cluster_ratio, self.next_request, i as int);
                assert(slot_valid(self.view().slots[index as int], self.geometry.cluster_ratio, self.next_request));
                same_ownership_update_valid(step_before, index as int, self.view().slots[index as int]);
                assert(only_slot_changed(step_before, self.view(), index as int));
                assert(only_slot_changed(before, self.view(), index as int));
                changing_a_slot_without_changing_its_phase_preserves_accounting(before, self.view(), index as int);
            }
                i += 1;
            }
        }
        proof {
            assert(self.view().slots =~= before.slots.update(index as int, self.view().slots[index as int]));
            occupied_count_update(before.slots, index as int, self.view().slots[index as int]);
        }
        Ok(())
    }

    /// A failure callback does not cancel an issued write. The outstanding
    /// range can be discarded only after an adapter-established quiescent reset.
    fn discard_initialization_after_reset(&mut self, command: Initialization, quiescent: bool)
        -> (r: Result<(), (Initialization, Error)>)
        requires self.wf(),
        ensures final(self).wf(), match r {
            Ok(()) => quiescent && exists|i: int, at: int| (#[trigger] command_matches(old(self).view(), command.view(), i, at))
                && unchanged_allocation(old(self).view(), final(self).view(), i)
                && final(self).view().slots[i] == (SlotView {
                    pending: old(self).view().slots[i].pending.remove(at),
                    ..old(self).view().slots[i] }),
            Err((returned, _)) => returned.view() == command.view() && final(self).view() == old(self).view(),
        },
    {
        let ghost before = self.view();
        if !quiescent { return Err((command, Error::Quiescence)); }
        if command.domain != self.domain || command.cluster < self.first_cluster
            || command.cluster - self.first_cluster >= self.slots.len() as u64 {
            return Err((command, Error::Stale));
        }
        let index = (command.cluster - self.first_cluster) as usize;
        if self.slots[index].generation != command.generation { return Err((command, Error::Stale)); }
        let ratio = self.geometry.cluster_ratio as u64;
        if command.physical / ratio != command.cluster || command.physical % ratio != command.start as u64 {
            return Err((command, Error::Stale));
        }
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(command.physical as int, ratio as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(ratio as int, command.cluster as int);
            assert(command.physical as nat == command.cluster as nat * self.geometry.cluster_ratio + command.start);
        }
        let mut at = 0usize;
        while at < self.slots[index].pending.len()
            invariant index < self.slots.len(), index < before.slots.len(),
                at <= self.slots[index as int].pending.len(), self.view() == before, self.wf(),
                command.physical as nat == command.cluster as nat * self.geometry.cluster_ratio + command.start,
                forall|j: int| 0 <= j < at ==> (#[trigger] before.slots[index as int].pending[j]).id != command.request,
            decreases self.slots[index as int].pending.len() - at,
        {
            if self.slots[index].pending[at].id == command.request { break; }
            at += 1;
        }
        if at == self.slots[index].pending.len()
            || self.slots[index].pending[at].start != command.start
            || self.slots[index].pending[at].length != command.length {
            return Err((command, Error::Stale));
        }
        assert(2 <= self.slots@[index as int].phase <= 3);
        assert(command_matches(before, command.view(), index as int, at as int));

        let ghost prior_pending = self.slots@[index as int].pending@;
        self.slots[index].pending.remove(at);
        proof {
            pending_views_remove(prior_pending, at as int);
            slot_pending_remove_valid(before.slots[index as int], self.geometry.cluster_ratio, self.next_request, at as int);
            assert(self.view().slots[index as int] == (SlotView {
                pending: before.slots[index as int].pending.remove(at as int), ..before.slots[index as int] }));
            assert(slot_valid(self.view().slots[index as int], self.geometry.cluster_ratio, self.next_request));
            same_ownership_update_valid(before, index as int, self.view().slots[index as int]);
            assert(self.view().slots =~= before.slots.update(index as int, self.view().slots[index as int]));
            occupied_count_update(before.slots, index as int, self.view().slots[index as int]);
        }
        Ok(())
    }

    fn map_range(&mut self, key: &Key, start: u32, length: u32, written: bool)
        -> (r: Result<(), Error>)
        requires self.wf(),
        ensures final(self).wf(), match r {
            Ok(()) => {
                let i = key_index(old(self).view(), key.view());
                &&& key_matches(old(self).view(), key.view(), i) && old(self).view().slots[i].phase == 3
                &&& old(self).view().slots[i].pins == 0 && !pending_overlap(old(self).view(), i, start, length)
                &&& range_valid(old(self).view(), i, start, length)
                &&& (forall|j: int| start <= j < start as nat + length ==>
                    (#[trigger] old(self).view().slots[i].mapped[j]) == 0 && (!written || old(self).view().slots[i].initialized[j]))
                &&& unchanged_allocation(old(self).view(), final(self).view(), i)
                &&& range_set(old(self).view().slots[i].mapped, final(self).view().slots[i].mapped, start, length, if written { 2 } else { 1 })
                &&& final(self).view().slots[i].initialized == old(self).view().slots[i].initialized
                &&& final(self).view().slots[i].pending == old(self).view().slots[i].pending
            }, Err(_) => final(self).view() == old(self).view(),
        },
    {
        let ghost before = self.view();
        let index = match self.index(key) { Ok(index) => index, Err(error) => { return Err(error); } };
        if self.slots[index].phase != 3 || !self.range(index, start, length) { return Err(Error::Outside); }
        if self.slots[index].pins != 0 || self.pending_overlap(index, start, length) { return Err(Error::Busy); }
        let mut i = start;
        while i < start + length
            invariant index < self.slots.len(), index < before.slots.len(),
                start <= i <= start + length, start + length <= self.geometry.cluster_ratio,
                self.slots@[index as int].mapped.len() == self.geometry.cluster_ratio,
                self.slots@[index as int].initialized.len() == self.geometry.cluster_ratio,
                before.slots[index as int].mapped.len() == self.geometry.cluster_ratio,
                before.slots[index as int].initialized.len() == self.geometry.cluster_ratio,
                self.view() == before, self.wf(),
                forall|j: int| start <= j < i ==> (#[trigger] before.slots[index as int].mapped[j]) == 0
                    && (!written || before.slots[index as int].initialized[j]),
            decreases start + length - i,
        {
            if self.slots[index].mapped[i as usize] != 0 { return Err(Error::Busy); }
            if written && !self.slots[index].initialized[i as usize] { return Err(Error::Uninitialized); }
            i += 1;
        }
        i = start;
        while i < start + length
            invariant index < self.slots.len(), index < before.slots.len(),
                start <= i <= start + length, start + length <= self.geometry.cluster_ratio,
                self.slots@[index as int].mapped.len() == self.geometry.cluster_ratio,
                self.slots@[index as int].initialized.len() == self.geometry.cluster_ratio,
                before.slots[index as int].mapped.len() == self.geometry.cluster_ratio,
                before.slots[index as int].initialized.len() == self.geometry.cluster_ratio,
                key_matches(before, key.view(), index as int), range_valid(before, index as int, start, length),
                !pending_overlap(before, index as int, start, length),
                before.slots[index as int].phase == 3,
                forall|j: int| start <= j < start as nat + length ==> (#[trigger] before.slots[index as int].mapped[j]) == 0
                    && (!written || before.slots[index as int].initialized[j]),
                self.wf(), unchanged_allocation(before, self.view(), index as int),
                self.view().slots[index as int].phase == before.slots[index as int].phase,
                self.view().slots[index as int].generation == before.slots[index as int].generation,
                self.view().slots[index as int].owner == before.slots[index as int].owner,
                self.view().slots[index as int].logical_start == before.slots[index as int].logical_start,
                self.view().slots[index as int].pins == before.slots[index as int].pins,
                self.view().slots[index as int].pending == before.slots[index as int].pending,
                range_set(before.slots[index as int].mapped, self.view().slots[index as int].mapped,
                    start, (i - start) as u32, if written { 2 } else { 1 }),
                self.view().slots[index as int].initialized == before.slots[index as int].initialized,
            decreases start + length - i,
        {
            let ghost step_before = self.view();
            let ghost native_before = self.slots@;
            self.slots[index].mapped.set(i as usize, if written { 2u8 } else { 1u8 });
            proof {
                assert(self.slots@ =~= native_before.update(index as int, self.slots@[index as int]));
                slot_views_update(native_before, index as int, self.slots@[index as int]);
                pending_range_excludes_point(before, index as int, start, length, i as int);
                slot_mapped_valid(step_before.slots[index as int], self.geometry.cluster_ratio, self.next_request,
                    i as int, if written { 2u8 } else { 1u8 });
                assert(slot_valid(self.view().slots[index as int], self.geometry.cluster_ratio, self.next_request));
                same_ownership_update_valid(step_before, index as int, self.view().slots[index as int]);
                assert(only_slot_changed(step_before, self.view(), index as int));
                assert(only_slot_changed(before, self.view(), index as int));
                changing_a_slot_without_changing_its_phase_preserves_accounting(before, self.view(), index as int);
            }
            i += 1;
        }
        proof {
            assert(self.view().slots =~= before.slots.update(index as int, self.view().slots[index as int]));
            occupied_count_update(before.slots, index as int, self.view().slots[index as int]);
        }
        Ok(())
    }

    fn convert_written(&mut self, key: &Key, start: u32, length: u32) -> (r: Result<(), Error>)
        requires self.wf(),
        ensures final(self).wf(), match r {
            Ok(()) => {
                let i = key_index(old(self).view(), key.view());
                &&& key_matches(old(self).view(), key.view(), i) && old(self).view().slots[i].phase == 3
                &&& old(self).view().slots[i].pins == 0 && !pending_overlap(old(self).view(), i, start, length)
                &&& range_valid(old(self).view(), i, start, length)
                &&& (forall|j: int| start <= j < start as nat + length ==>
                    (#[trigger] old(self).view().slots[i].mapped[j]) == 1 && old(self).view().slots[i].initialized[j])
                &&& unchanged_allocation(old(self).view(), final(self).view(), i)
                &&& range_set(old(self).view().slots[i].mapped, final(self).view().slots[i].mapped, start, length, 2)
                &&& final(self).view().slots[i].initialized == old(self).view().slots[i].initialized
                &&& final(self).view().slots[i].pending == old(self).view().slots[i].pending
            }, Err(_) => final(self).view() == old(self).view(),
        },
    {
        let ghost before = self.view();
        let index = match self.index(key) { Ok(index) => index, Err(error) => { return Err(error); } };
        if self.slots[index].phase != 3 || !self.range(index, start, length) { return Err(Error::Outside); }
        if self.slots[index].pins != 0 || self.pending_overlap(index, start, length) { return Err(Error::Busy); }
        let mut i = start;
        while i < start + length
            invariant index < self.slots.len(), index < before.slots.len(),
                start <= i <= start + length, start + length <= self.geometry.cluster_ratio,
                self.slots@[index as int].mapped.len() == self.geometry.cluster_ratio,
                self.slots@[index as int].initialized.len() == self.geometry.cluster_ratio,
                before.slots[index as int].mapped.len() == self.geometry.cluster_ratio,
                before.slots[index as int].initialized.len() == self.geometry.cluster_ratio,
                self.view() == before, self.wf(),
                forall|j: int| start <= j < i ==> (#[trigger] before.slots[index as int].mapped[j]) == 1
                    && before.slots[index as int].initialized[j],
            decreases start + length - i,
        {
            if self.slots[index].mapped[i as usize] != 1 { return Err(Error::State); }
            if !self.slots[index].initialized[i as usize] { return Err(Error::Uninitialized); }
            i += 1;
        }
        i = start;
        while i < start + length
            invariant index < self.slots.len(), index < before.slots.len(),
                start <= i <= start + length, start + length <= self.geometry.cluster_ratio,
                self.slots@[index as int].mapped.len() == self.geometry.cluster_ratio,
                self.slots@[index as int].initialized.len() == self.geometry.cluster_ratio,
                before.slots[index as int].mapped.len() == self.geometry.cluster_ratio,
                before.slots[index as int].initialized.len() == self.geometry.cluster_ratio,
                key_matches(before, key.view(), index as int), range_valid(before, index as int, start, length),
                !pending_overlap(before, index as int, start, length),
                before.slots[index as int].phase == 3,
                forall|j: int| start <= j < start as nat + length ==> (#[trigger] before.slots[index as int].mapped[j]) == 1
                    && before.slots[index as int].initialized[j],
                self.wf(), unchanged_allocation(before, self.view(), index as int),
                self.view().slots[index as int].phase == before.slots[index as int].phase,
                self.view().slots[index as int].generation == before.slots[index as int].generation,
                self.view().slots[index as int].owner == before.slots[index as int].owner,
                self.view().slots[index as int].logical_start == before.slots[index as int].logical_start,
                self.view().slots[index as int].pins == before.slots[index as int].pins,
                self.view().slots[index as int].pending == before.slots[index as int].pending,
                range_set(before.slots[index as int].mapped, self.view().slots[index as int].mapped,
                    start, (i - start) as u32, 2),
                self.view().slots[index as int].initialized == before.slots[index as int].initialized,
            decreases start + length - i,
        {
            let ghost step_before = self.view();
            let ghost native_before = self.slots@;
            self.slots[index].mapped.set(i as usize, 2u8);
            proof {
                assert(self.slots@ =~= native_before.update(index as int, self.slots@[index as int]));
                slot_views_update(native_before, index as int, self.slots@[index as int]);
                pending_range_excludes_point(before, index as int, start, length, i as int);
                slot_mapped_valid(step_before.slots[index as int], self.geometry.cluster_ratio, self.next_request,
                    i as int, 2u8);
                assert(slot_valid(self.view().slots[index as int], self.geometry.cluster_ratio, self.next_request));
                same_ownership_update_valid(step_before, index as int, self.view().slots[index as int]);
                assert(only_slot_changed(step_before, self.view(), index as int));
                assert(only_slot_changed(before, self.view(), index as int));
                changing_a_slot_without_changing_its_phase_preserves_accounting(before, self.view(), index as int);
            }
            i += 1;
        }
        proof {
            assert(self.view().slots =~= before.slots.update(index as int, self.view().slots[index as int]));
            occupied_count_update(before.slots, index as int, self.view().slots[index as int]);
        }
        Ok(())
    }

    /// Partial unmapping retains the physical cluster while any other range
    /// in this inode's logical cluster remains mapped.
    fn unmap_range(&mut self, key: &Key, start: u32, length: u32) -> (r: Result<(), Error>)
        requires self.wf(),
        ensures final(self).wf(), match r {
            Ok(()) => {
                let i = key_index(old(self).view(), key.view());
                &&& key_matches(old(self).view(), key.view(), i) && old(self).view().slots[i].phase == 3
                &&& old(self).view().slots[i].pins == 0 && !pending_overlap(old(self).view(), i, start, length)
                &&& range_valid(old(self).view(), i, start, length)
                &&& unchanged_allocation(old(self).view(), final(self).view(), i)
                &&& range_set(old(self).view().slots[i].mapped, final(self).view().slots[i].mapped, start, length, 0)
                &&& init_set(old(self).view().slots[i].initialized, final(self).view().slots[i].initialized, start, length, false)
                &&& final(self).view().slots[i].pending == old(self).view().slots[i].pending
            }, Err(_) => final(self).view() == old(self).view(),
        },
    {
        let ghost before = self.view();
        let index = match self.index(key) { Ok(index) => index, Err(error) => { return Err(error); } };
        if self.slots[index].phase != 3 || !self.range(index, start, length) { return Err(Error::Outside); }
        if self.slots[index].pins != 0 || self.pending_overlap(index, start, length) { return Err(Error::Busy); }
        let mut i = start;
        while i < start + length
            invariant index < self.slots.len(), index < before.slots.len(),
                start <= i <= start + length, start + length <= self.geometry.cluster_ratio,
                self.slots@[index as int].mapped.len() == self.geometry.cluster_ratio,
                self.slots@[index as int].initialized.len() == self.geometry.cluster_ratio,
                before.slots[index as int].mapped.len() == self.geometry.cluster_ratio,
                before.slots[index as int].initialized.len() == self.geometry.cluster_ratio,
                key_matches(before, key.view(), index as int), range_valid(before, index as int, start, length),
                !pending_overlap(before, index as int, start, length),
                before.slots[index as int].phase == 3,
                self.wf(), unchanged_allocation(before, self.view(), index as int),
                self.view().slots[index as int].phase == before.slots[index as int].phase,
                self.view().slots[index as int].generation == before.slots[index as int].generation,
                self.view().slots[index as int].owner == before.slots[index as int].owner,
                self.view().slots[index as int].logical_start == before.slots[index as int].logical_start,
                self.view().slots[index as int].pins == before.slots[index as int].pins,
                self.view().slots[index as int].pending == before.slots[index as int].pending,
                range_set(before.slots[index as int].mapped, self.view().slots[index as int].mapped,
                    start, (i - start) as u32, 0),
                init_set(before.slots[index as int].initialized, self.view().slots[index as int].initialized,
                    start, (i - start) as u32, false),
            decreases start + length - i,
        {
            let ghost step_before = self.view();
            let ghost native_before = self.slots@;
            self.slots[index].mapped.set(i as usize, 0u8);
            self.slots[index].initialized.set(i as usize, false);
            proof {
                assert(self.slots@ =~= native_before.update(index as int, self.slots@[index as int]));
                slot_views_update(native_before, index as int, self.slots@[index as int]);
                slot_mapped_valid(step_before.slots[index as int], self.geometry.cluster_ratio, self.next_request, i as int, 0);
                let cleared = SlotView { mapped: step_before.slots[index as int].mapped.update(i as int, 0), ..step_before.slots[index as int] };
                slot_init_false_valid(cleared, self.geometry.cluster_ratio, self.next_request, i as int);
                assert(slot_valid(self.view().slots[index as int], self.geometry.cluster_ratio, self.next_request));
                same_ownership_update_valid(step_before, index as int, self.view().slots[index as int]);
                assert(only_slot_changed(step_before, self.view(), index as int));
                assert(only_slot_changed(before, self.view(), index as int));
                changing_a_slot_without_changing_its_phase_preserves_accounting(before, self.view(), index as int);
            }
            i += 1;
        }
        proof {
            assert(self.view().slots =~= before.slots.update(index as int, self.view().slots[index as int]));
            occupied_count_update(before.slots, index as int, self.view().slots[index as int]);
        }
        Ok(())
    }

    fn read_block(&self, key: &Key, logical: u32) -> (r: Result<ReadDecision, Error>)
        requires self.wf(),
        ensures self.wf(), match r {
            Ok(decision) => {
                let i = key_index(self.view(), key.view());
                let offset = logical as int - key.view().logical_start as int;
                &&& key_matches(self.view(), key.view(), i) && self.view().slots[i].phase == 3
                &&& 0 <= offset < self.view().geometry.cluster_ratio && logical < 4294967295
                &&& match decision {
                    ReadDecision::Zero => self.view().slots[i].mapped[offset] <= 1,
                    ReadDecision::Initialized(block) => self.view().slots[i].mapped[offset] == 2
                        && self.view().slots[i].initialized[offset]
                        && block as nat == key.view().cluster as nat * self.view().geometry.cluster_ratio + offset
                        && self.view().geometry.first_data <= block < self.view().geometry.blocks,
                }
            }, Err(_) => true,
        },
    {
        let ghost before = self.view();
        let index = match self.index(key) { Ok(index) => index, Err(error) => { return Err(error); } };
        if self.slots[index].phase != 3 || logical == 4294967295 || logical < key.logical_start
            || logical - key.logical_start >= self.geometry.cluster_ratio { return Err(Error::Outside); }
        let offset = logical - key.logical_start;
        let mapped = self.slots[index].mapped[offset as usize];
        if mapped == 0 || mapped == 1 { return Ok(ReadDecision::Zero); }
        if mapped != 2 || !self.slots[index].initialized[offset as usize] { return Err(Error::Uninitialized); }
        let ratio = self.geometry.cluster_ratio as u64;
        if ratio == 0 || key.cluster > 18446744073709551615u64 / ratio { return Err(Error::Overflow); }
        proof { product_below_limit(key.cluster, ratio); }
        let base = key.cluster * ratio;
        if base >= self.geometry.blocks || (offset as u64) >= self.geometry.blocks - base { return Err(Error::Outside); }
        Ok(ReadDecision::Initialized(base + offset as u64))
    }

    fn pin(&mut self, key: &Key) -> (r: Result<ReadPin, Error>)
        requires self.wf(),
        ensures final(self).wf(), match r {
            Ok(pin) => {
                let i = key_index(old(self).view(), key.view());
                &&& key_matches(old(self).view(), key.view(), i) && old(self).view().slots[i].phase == 3
                &&& old(self).view().slots[i].pending.len() == 0
                &&& pin.view() == (TicketView { domain: key.view().domain, cluster: key.view().cluster, generation: key.view().generation })
                &&& unchanged_allocation(old(self).view(), final(self).view(), i)
                &&& final(self).view().slots[i] == (SlotView { pins: (old(self).view().slots[i].pins + 1) as u32, ..old(self).view().slots[i] })
            }, Err(_) => final(self).view() == old(self).view(),
        },
    {
        let ghost before = self.view();
        let index = match self.index(key) { Ok(index) => index, Err(error) => { return Err(error); } };
        if self.slots[index].phase != 3 || self.slots[index].pending.len() != 0 { return Err(Error::Busy); }
        if self.slots[index].pins == 4294967295 { return Err(Error::Overflow); }
        self.slots[index].pins += 1;
        proof {
            assert(self.view().slots =~= before.slots.update(index as int, self.view().slots[index as int]));
            occupied_count_update(before.slots, index as int, self.view().slots[index as int]);
        }
        Ok(ReadPin { domain: self.domain, cluster: key.cluster, generation: key.generation })
    }

    fn unpin(&mut self, pin: ReadPin) -> (r: Result<(), (ReadPin, Error)>)
        requires self.wf(),
        ensures final(self).wf(), match r {
            Ok(()) => exists|i: int| 0 <= i < old(self).view().slots.len()
                && pin.view().domain == old(self).view().domain
                && pin.view().cluster as int == old(self).view().first_cluster as int + i
                && pin.view().generation == (#[trigger] old(self).view().slots[i]).generation
                && old(self).view().slots[i].pins > 0
                && unchanged_allocation(old(self).view(), final(self).view(), i)
                && final(self).view().slots[i] == (SlotView { pins: (old(self).view().slots[i].pins - 1) as u32, ..old(self).view().slots[i] }),
            Err((returned, _)) => returned.view() == pin.view() && final(self).view() == old(self).view(),
        },
    {
        let ghost before = self.view();
        if pin.domain != self.domain || pin.cluster < self.first_cluster
            || pin.cluster - self.first_cluster >= self.slots.len() as u64 { return Err((pin, Error::Stale)); }
        let index = (pin.cluster - self.first_cluster) as usize;
        if self.slots[index].generation != pin.generation || self.slots[index].pins == 0 { return Err((pin, Error::Stale)); }
        self.slots[index].pins -= 1;
        proof {
            assert(self.view().slots =~= before.slots.update(index as int, self.view().slots[index as int]));
            occupied_count_update(before.slots, index as int, self.view().slots[index as int]);
        }
        Ok(())
    }

    fn retire(&mut self, key: Key) -> (r: Result<Retirement, (Key, Error)>)
        requires self.wf(),
        ensures final(self).wf(), match r {
            Ok(ticket) => {
                let i = key_index(old(self).view(), key.view());
                &&& key_matches(old(self).view(), key.view(), i) && old(self).view().slots[i].phase == 3
                &&& old(self).view().slots[i].pins == 0 && old(self).view().slots[i].pending.len() == 0
                &&& (forall|j: int| 0 <= j < old(self).view().geometry.cluster_ratio ==> (#[trigger] old(self).view().slots[i].mapped[j]) == 0)
                &&& ticket.view() == (TicketView { domain: key.view().domain, cluster: key.view().cluster, generation: key.view().generation })
                &&& unchanged_allocation(old(self).view(), final(self).view(), i)
                &&& final(self).view().slots[i] == (SlotView { phase: 4, ..old(self).view().slots[i] })
            }, Err((returned, _)) => returned.view() == key.view() && final(self).view() == old(self).view(),
        },
    {
        let ghost before = self.view();
        let index = match self.index(&key) { Ok(index) => index, Err(error) => { return Err((key, error)); } };
        if self.slots[index].phase != 3 || self.slots[index].pins != 0
            || self.slots[index].pending.len() != 0 { return Err((key, Error::Busy)); }
        let mut i = 0usize;
        while i < self.slots[index].mapped.len()
            invariant index < self.slots.len(), index < before.slots.len(),
                i <= self.slots[index as int].mapped.len(), self.view() == before, self.wf(),
                forall|j: int| 0 <= j < i ==> (#[trigger] before.slots[index as int].mapped[j]) == 0,
            decreases self.slots[index as int].mapped.len() - i,
        {
            if self.slots[index].mapped[i] != 0 { return Err((key, Error::Busy)); }
            i += 1;
        }
        self.slots[index].phase = 4;
        proof {
            assert(self.view().slots =~= before.slots.update(index as int, self.view().slots[index as int]));
            occupied_count_update(before.slots, index as int, self.view().slots[index as int]);
        }
        Ok(Retirement { domain: self.domain, cluster: key.cluster, generation: key.generation })
    }

    /// Reuse waits for the outer journal checkpoint/revoke and I/O-quiescence
    /// contract. A failed acknowledgement leaves the allocated bitmap bit set.
    fn reclaim_after_checkpoint(&mut self, retired: Retirement, succeeded: bool)
        -> (r: Result<(), (Retirement, Error)>)
        requires self.wf(),
        ensures final(self).wf(), match r {
            Ok(()) => succeeded && exists|i: int| 0 <= i < old(self).view().slots.len()
                && retired.view().domain == old(self).view().domain
                && retired.view().cluster as int == old(self).view().first_cluster as int + i
                && retired.view().generation == (#[trigger] old(self).view().slots[i]).generation
                && old(self).view().slots[i].phase == 4
                && old(self).view().slots[i].pins == 0 && old(self).view().slots[i].pending.len() == 0
                && only_slot_changed(old(self).view(), final(self).view(), i)
                && final(self).view().slots[i].phase == 1
                && final(self).view().slots[i].generation == old(self).view().slots[i].generation
                && final(self).view().next_request == old(self).view().next_request
                && final(self).view().live_blocks as nat + old(self).view().geometry.cluster_ratio == old(self).view().live_blocks,
            Err((returned, _)) => returned.view() == retired.view() && final(self).view() == old(self).view(),
        },
    {
        let ghost before = self.view();
        if retired.domain != self.domain || retired.cluster < self.first_cluster
            || retired.cluster - self.first_cluster >= self.slots.len() as u64 { return Err((retired, Error::Stale)); }
        let index = (retired.cluster - self.first_cluster) as usize;
        if self.slots[index].phase != 4 || self.slots[index].generation != retired.generation
            || self.slots[index].pins != 0 || self.slots[index].pending.len() != 0 {
            return Err((retired, Error::Stale));
        }
        if !succeeded { return Err((retired, Error::Checkpoint)); }
        let ratio = self.geometry.cluster_ratio as u64;
        if self.live_blocks < ratio { return Err((retired, Error::State)); }
        self.slots[index].phase = 1;
        self.slots[index].owner = Owner { inode: 0, generation: 0 };
        self.slots[index].logical_start = 0;
        self.slots[index].mapped = Vec::new();
        self.slots[index].initialized = Vec::new();
        self.live_blocks -= ratio;
        proof {
            assert(self.view().slots =~= before.slots.update(index as int, self.view().slots[index as int]));
            occupied_count_update(before.slots, index as int, self.view().slots[index as int]);
            assert(slot_valid(self.view().slots[index as int], self.geometry.cluster_ratio, self.next_request));
            release_update_valid(before, index as int, self.view().slots[index as int]);
        }
        Ok(())
    }

    fn bitmap_bytes(&self) -> (r: Vec<u8>)
        requires self.wf(),
        ensures self.wf(), allocation_bitmap(self.view(), r@),
    {
        let ghost before = self.view();
        let mut raw = Vec::new();
        let mut i = 0usize;
        while i < self.bitmap.len()
            invariant i <= self.bitmap.len(), raw@ == before.bitmap.take(i as int), self.wf(), self.view() == before,
            decreases self.bitmap.len() - i,
        {
            raw.push(self.bitmap[i]); i += 1;
        }
        i = 0;
        while i < self.slots.len()
            invariant i <= self.slots.len(), raw.len() == self.bitmap.len(), self.wf(), self.view() == before,
                forall|j: int| 0 <= j < raw.len() * 8 ==> (#[trigger] bitmap_bit(raw@, j as u32))
                    == if before.first_bit <= j < before.first_bit as nat + i {
                        before.slots[j - before.first_bit as int].phase != 1
                    } else { bitmap_bit(before.bitmap, j as u32) },
            decreases self.slots.len() - i,
        {
            let index = self.first_bit as u64 + i as u64;
            let byte = (index / 8) as usize;
            assert(index < raw.len() as nat * 8);
            assert(byte < raw.len());
            if byte < raw.len() {
                let old = raw[byte];
                let next = put_bit(old, (index % 8) as u8, self.slots[i].phase != 1);
                let ghost previous = raw@;
                raw.set(byte, next);
                proof {
                    assert forall|j: int| 0 <= j < raw.len() * 8 implies (#[trigger] bitmap_bit(raw@, j as u32))
                        == if j == index { before.slots[i as int].phase != 1 }
                            else { bitmap_bit(previous, j as u32) } by {
                        assert(0 <= j < 524288);
                        assert((j as u32) as int == j);
                        assert((j as u32) / 8 == j / 8);
                        assert((j as u32) % 8 == j % 8);
                        if j / 8 == byte {
                            assert(0 <= j % 8 < 8);
                            assert(previous[byte as int] == old);
                            assert(raw@[byte as int] == next);
                            assert(byte_bit(next, (j % 8) as u8)
                                == if (j % 8) as u8 == (index % 8) as u8 {
                                    before.slots[i as int].phase != 1
                                } else { byte_bit(old, (j % 8) as u8) });
                            if j % 8 == index % 8 {
                                assert(j == index) by (nonlinear_arith)
                                    requires j >= 0, index >= 0, j / 8 == byte,
                                        index / 8 == byte, j % 8 == index % 8;
                            }
                        } else {
                            assert(raw@[(j / 8) as int] == previous[(j / 8) as int]);
                        }
                    }
                }
            }
            i += 1;
        }
        raw
    }
}

}
