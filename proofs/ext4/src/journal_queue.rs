// SPDX-License-Identifier: MPL-2.0

//! Shared log-space reservations and immutable candidate versions. A sealed
//! version keeps its credits: checkpoint retirement and physical I/O authority
//! require the later journal/device adapter. No disk slots are recycled here.

use vstd::prelude::*;
use crate::{edit_handles::{self, EditView, FrozenBatch, Part, Running}, edit_schedule,
    layout::{JournalLayout, LayoutView}, transaction::ImageView};

verus! {

pub const MAX_VERSIONS: usize = 64;
pub const MAX_SERIAL: u64 = 18446744073709551615;

pub struct FrozenView {
    pub serial: u64, pub first: u32, pub blocks: u32, pub images: Seq<ImageView>, pub layout: LayoutView,
}
pub struct RunningView { pub serial: u64, pub first: u32, pub edits: Seq<EditView> }
pub struct QueueView { pub frozen: Seq<FrozenView>, pub running: Option<RunningView>, pub used: u32, pub next_serial: u64 }

#[verifier::opaque]
pub open spec fn occupied(records: Seq<FrozenView>) -> nat
    decreases records.len(),
{
    if records.len() == 0 { 0nat } else { occupied(records.drop_last()) + records.last().blocks as nat }
}

pub open spec fn capacity(layout: &JournalLayout) -> nat {
    if layout.view().journal_blocks >= 2 { (layout.view().journal_blocks - 2) as nat } else { 0nat }
}

pub open spec fn frozen_valid(record: FrozenView, layout: &JournalLayout) -> bool {
    &&& record.layout == layout.view() && 0 < record.serial && 0 < record.images.len() <= edit_handles::MAX_CREDITS
    &&& edit_handles::batch_valid(record.images, layout)
    &&& record.blocks as nat == record.images.len() + 2
    &&& 0 < record.first && record.first as nat + record.blocks < layout.view().journal_blocks
}

pub open spec fn running_valid(record: RunningView, layout: &JournalLayout) -> bool {
    &&& 0 < record.serial && 0 < record.edits.len() <= edit_handles::MAX_CREDITS
    &&& (forall|i: int| 0 <= i < record.edits.len() ==> layout.allowed((#[trigger] record.edits[i]).target))
    &&& (forall|i: int, j: int| 0 <= i < j < record.edits.len() ==>
        (#[trigger] record.edits[i]).target < (#[trigger] record.edits[j]).target)
}

#[verifier::opaque]
pub open spec fn inv(v: QueueView, layout: &JournalLayout) -> bool {
    &&& layout.wf() && v.frozen.len() <= MAX_VERSIONS && 0 < v.next_serial
    &&& (forall|i: int| 0 <= i < v.frozen.len() ==> #[trigger] frozen_valid(v.frozen[i], layout)
        && v.frozen[i].serial < v.next_serial && v.frozen[i].first as nat == 1 + occupied(v.frozen.take(i)))
    &&& (forall|i: int, j: int| 0 <= i < j < v.frozen.len() ==> (#[trigger] v.frozen[i]).serial < (#[trigger] v.frozen[j]).serial)
    &&& occupied(v.frozen) <= capacity(layout)
    &&& (match v.running {
        Some(running) => v.frozen.len() < MAX_VERSIONS && running_valid(running, layout)
            && running.serial < v.next_serial && running.first as nat == 1 + occupied(v.frozen)
            && (forall|i: int| 0 <= i < v.frozen.len() ==> (#[trigger] v.frozen[i]).serial < running.serial)
            && v.used as nat == occupied(v.frozen) + running.edits.len() + 2,
        None => v.used as nat == occupied(v.frozen),
    })
    &&& v.used <= capacity(layout)
}

pub enum Event { Reserve(Seq<u32>), Edit(edit_schedule::Event), Seal, Cancel }

pub open spec fn enabled(v: QueueView, event: Event, layout: &JournalLayout) -> bool {
    match event {
        Event::Reserve(targets) => v.running.is_none() && v.frozen.len() < MAX_VERSIONS && v.next_serial < MAX_SERIAL
            && edit_handles::admissible_targets(targets, layout) && v.used as nat + targets.len() + 2 <= capacity(layout),
        Event::Edit(edit) => match v.running { Some(running) => edit_schedule::enabled(running.edits, edit), None => false },
        Event::Seal => match v.running { Some(running) => edit_handles::ready(running.edits), None => false },
        Event::Cancel => v.running.is_some(),
    }
}

pub open spec fn step(v: QueueView, event: Event, layout: &JournalLayout) -> QueueView {
    match event {
        Event::Reserve(targets) => QueueView { running: Some(RunningView { serial: v.next_serial, first: (v.used as nat + 1) as u32,
            edits: Seq::new(targets.len(), |i: int| EditView { target: targets[i], stage: edit_handles::StageView {
                status: edit_handles::Status::Unused, image: None } }) }),
            used: (v.used as nat + targets.len() + 2) as u32, next_serial: (v.next_serial + 1) as u64, ..v },
        Event::Edit(edit) => match v.running {
            Some(running) => QueueView { running: Some(RunningView { edits: edit_schedule::next(running.edits, edit), ..running }), ..v },
            None => v,
        },
        Event::Seal => match v.running {
            Some(running) => {
                let images = edit_handles::selected(running.edits);
                QueueView { frozen: if images.len() == 0 { v.frozen } else { v.frozen.push(FrozenView {
                    serial: running.serial, first: running.first, blocks: (images.len() + 2) as u32, images, layout: layout.view() }) },
                    running: None, used: (occupied(v.frozen) + if images.len() == 0 { 0nat } else { images.len() + 2 }) as u32, ..v }
            },
            None => v,
        },
        Event::Cancel => QueueView { running: None, used: occupied(v.frozen) as u32, ..v },
    }
}

proof fn occupied_push(records: Seq<FrozenView>, record: FrozenView)
    ensures occupied(records.push(record)) == occupied(records) + record.blocks as nat,
{
    assert(records.push(record).drop_last() =~= records);
    reveal(occupied);
}

proof fn unchanged_frozen_records_keep_their_admission(v: QueueView, after: QueueView, layout: &JournalLayout)
    requires inv(v, layout), after.frozen == v.frozen, after.next_serial >= v.next_serial,
    ensures after.frozen.len() <= MAX_VERSIONS, 0 < after.next_serial,
        occupied(after.frozen) <= capacity(layout),
        forall|i: int| 0 <= i < after.frozen.len() ==> #[trigger] frozen_valid(after.frozen[i], layout)
            && after.frozen[i].serial < after.next_serial
            && after.frozen[i].first as nat == 1 + occupied(after.frozen.take(i)),
        forall|i: int, j: int| 0 <= i < j < after.frozen.len() ==> (#[trigger] after.frozen[i]).serial < (#[trigger] after.frozen[j]).serial,
{
    reveal(inv);
    assert forall|i: int| 0 <= i < after.frozen.len() implies #[trigger] frozen_valid(after.frozen[i], layout)
        && after.frozen[i].serial < after.next_serial
        && after.frozen[i].first as nat == 1 + occupied(after.frozen.take(i)) by {
        assert(after.frozen[i] == v.frozen[i]);
        assert(frozen_valid(v.frozen[i], layout));
    }
    assert forall|i: int, j: int| 0 <= i < j < after.frozen.len() implies (#[trigger] after.frozen[i]).serial < (#[trigger] after.frozen[j]).serial by {
        assert(after.frozen[i] == v.frozen[i] && after.frozen[j] == v.frozen[j]);
    }
}

pub proof fn editing_preserves_the_shared_reservations(v: QueueView, edits: Seq<EditView>, layout: &JournalLayout)
    requires inv(v, layout), v.running.is_some(), edits.len() == v.running.unwrap().edits.len(),
        forall|i: int| 0 <= i < edits.len() ==> (#[trigger] edits[i]).target == v.running.unwrap().edits[i].target,
    ensures inv(QueueView { running: Some(RunningView { edits, ..v.running.unwrap() }), ..v }, layout),
{
    reveal(inv);
    let old = v.running.unwrap();
    assert forall|i: int| 0 <= i < edits.len() implies layout.allowed((#[trigger] edits[i]).target) by {
        assert(edits[i].target == old.edits[i].target);
    }
    assert forall|i: int, j: int| 0 <= i < j < edits.len() implies (#[trigger] edits[i]).target < (#[trigger] edits[j]).target by {
        assert(edits[i].target == old.edits[i].target && edits[j].target == old.edits[j].target);
    }
}

pub proof fn every_queue_event_preserves_credits_and_versions(v: QueueView, event: Event, layout: &JournalLayout)
    requires inv(v, layout), enabled(v, event, layout),
    ensures inv(step(v, event, layout), layout),
        step(v, event, layout).next_serial >= v.next_serial,
        step(v, event, layout).frozen.len() >= v.frozen.len(),
        forall|i: int| 0 <= i < v.frozen.len() ==> (#[trigger] step(v, event, layout).frozen[i]) == v.frozen[i],
{
    reveal(inv);
    let after = step(v, event, layout);
    match event {
        Event::Reserve(targets) => {
            assert(after.used as nat == v.used as nat + targets.len() + 2);
            assert(after.next_serial as nat == v.next_serial as nat + 1);
            let running = after.running.unwrap();
            assert forall|i: int| 0 <= i < targets.len() implies layout.allowed((#[trigger] running.edits[i]).target) by {
                assert(running.edits[i].target == targets[i]);
            }
            assert forall|i: int, j: int| 0 <= i < j < targets.len() implies
                (#[trigger] running.edits[i]).target < (#[trigger] running.edits[j]).target by {
                assert(running.edits[i].target == targets[i] && running.edits[j].target == targets[j]);
            }
            assert(running_valid(running, layout));
            assert(after.running.unwrap().first as nat == 1 + occupied(after.frozen));
            assert forall|i: int| 0 <= i < after.frozen.len() implies (#[trigger] after.frozen[i]).serial < running.serial by {
                assert(after.frozen[i] == v.frozen[i]);
                assert(frozen_valid(v.frozen[i], layout));
                assert(v.frozen[i].serial < v.next_serial);
            }
            unchanged_frozen_records_keep_their_admission(v, after, layout);
            assert(after.used <= capacity(layout));
            assert(inv(after, layout));
        },
        Event::Edit(edit) => {
            let running = v.running.unwrap();
            let edits = edit_schedule::next(running.edits, edit);
            assert forall|i: int| 0 <= i < edits.len() implies (#[trigger] edits[i]).target == running.edits[i].target by {
                if i == edit.position { assert(edits[i].target == running.edits[i].target); }
            }
            editing_preserves_the_shared_reservations(v, edits, layout);
            assert(inv(after, layout));
        },
        Event::Seal => {
            let running = v.running.unwrap();
            edit_handles::closed_selection_has_bounded_disjoint_reserved_images(running.edits, layout);
            let images = edit_handles::selected(running.edits);
            if images.len() > 0 {
                let record = after.frozen.last();
                assert(frozen_valid(record, layout));
                occupied_push(v.frozen, record);
                assert(after.frozen =~= v.frozen.push(record));
                assert(after.frozen.drop_last() =~= v.frozen);
                assert forall|i: int| 0 <= i < after.frozen.len() implies #[trigger] frozen_valid(after.frozen[i], layout)
                    && after.frozen[i].serial < after.next_serial
                    && after.frozen[i].first as nat == 1 + occupied(after.frozen.take(i)) by {
                    if i < v.frozen.len() {
                        assert(after.frozen[i] == v.frozen[i]);
                        assert(after.frozen.take(i) =~= v.frozen.take(i));
                        assert(frozen_valid(v.frozen[i], layout));
                    } else {
                        assert(i == v.frozen.len() && after.frozen[i] == record);
                        assert(after.frozen.take(i) =~= v.frozen);
                    }
                }
                assert forall|i: int, j: int| 0 <= i < j < after.frozen.len() implies
                    (#[trigger] after.frozen[i]).serial < (#[trigger] after.frozen[j]).serial by {
                    if j < v.frozen.len() { assert(after.frozen[i] == v.frozen[i] && after.frozen[j] == v.frozen[j]); }
                    else { assert(after.frozen[i] == v.frozen[i] && after.frozen[j] == record); }
                }
            } else {
                unchanged_frozen_records_keep_their_admission(v, after, layout);
            }
            assert(after.running.is_none());
            assert(after.used as nat == occupied(after.frozen));
            assert(after.used <= capacity(layout));
            assert(inv(after, layout));
        },
        Event::Cancel => {
            assert(occupied(v.frozen) <= capacity(layout) <= 32766);
            assert(after.used as nat == occupied(v.frozen));
            unchanged_frozen_records_keep_their_admission(v, after, layout);
            assert(after.running.is_none());
            assert(after.used <= capacity(layout));
            assert(inv(after, layout));
        },
    }
}

pub struct FrozenVersion { serial: u64, first: u32, blocks: u32, batch: FrozenBatch }

impl FrozenVersion {
    pub closed spec fn view(&self) -> FrozenView {
        FrozenView { serial: self.serial, first: self.first, blocks: self.blocks,
            images: self.batch.frozen_view(), layout: self.batch.frozen_layout() }
    }
    spec fn wf(&self) -> bool {
        self.batch.wf() && self.serial > 0 && 0 < self.batch.frozen_view().len() <= 250
            && self.blocks as nat == self.batch.frozen_view().len() + 2
            && 0 < self.first && self.first as nat + self.blocks < self.batch.frozen_layout().journal_blocks
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn reservation(&self) -> (r: (u64, u32, u32))
        ensures r == (self.view().serial, self.view().first, self.view().blocks), r.0 > 0 && r.1 > 0 && 3 <= r.2 <= 252,
            r.2 as nat == self.view().images.len() + 2, r.1 as nat + r.2 < self.view().layout.journal_blocks,
    { proof { use_type_invariant(self); } (self.serial, self.first, self.blocks) }

    pub fn image_count(&self) -> (r: usize) ensures r == self.view().images.len(), 0 < r <= 250 {
        proof { use_type_invariant(self); }
        self.batch.frozen_count()
    }

    pub fn journal_layout(&self) -> (r: JournalLayout)
        ensures r.wf(), r.view() == self.view().layout,
    { self.batch.reserved_layout().duplicate() }

    pub fn image_at(&self, index: usize) -> (r: Option<(u32, &[u8])>)
        ensures match r {
            Some((target, bytes)) => index < self.view().images.len() && target == self.view().images[index as int].block
                && bytes@ == self.view().images[index as int].image,
            None => index >= self.view().images.len(),
        },
    { self.batch.image_at(index) }

    pub fn log_slot(&self, index: u32) -> (r: Option<u32>)
        ensures match r {
            Some(block) => index < self.view().blocks && block as nat == self.view().layout.start as nat + self.view().first as nat + index
                && self.view().layout.start < block < self.view().layout.start as nat + self.view().layout.journal_blocks,
            None => index >= self.view().blocks,
        },
    {
        proof { use_type_invariant(self); }
        if index >= self.blocks { return None; }
        let layout = self.batch.reserved_layout();
        proof { assert(layout.wf()); }
        Some(layout.physical_start() + self.first + index)
    }
}

pub open spec fn frozen_views(records: Seq<FrozenVersion>) -> Seq<FrozenView> { Seq::new(records.len(), |i: int| records[i].view()) }

pub struct Queue { layout: JournalLayout, frozen: Vec<FrozenVersion>, running: Option<Running>, serial: u64, used: u32, next_serial: u64 }
pub enum Seal { Frozen(u64), Empty(u64), NotReady, NoRunning, Invalid }

impl Queue {
    pub closed spec fn view(&self) -> QueueView {
        QueueView { frozen: frozen_views(self.frozen@), running: match self.running {
            Some(running) => Some(RunningView { serial: self.serial, first: (1 + occupied(frozen_views(self.frozen@))) as u32, edits: running.edit_view() }), None => None },
            used: self.used, next_serial: self.next_serial }
    }
    pub closed spec fn mapping(&self) -> &JournalLayout { &self.layout }
    pub closed spec fn wf(&self) -> bool {
        inv(self.view(), &self.layout) && match self.running { Some(running) => running.wf() && running.layout_view() == self.layout.view(), None => true }
    }
    pub fn new(layout: JournalLayout) -> (r: Option<Self>)
        ensures match r {
            Some(queue) => queue.wf() && queue.mapping().view() == layout.view()
                && queue.view() == (QueueView { frozen: Seq::empty(), running: None, used: 0, next_serial: 1 }),
            None => !layout.wf(),
        },
    {
        if !layout.valid() { return None; }
        assert(occupied(Seq::empty()) == 0) by { reveal(occupied); }
        assert(inv(QueueView { frozen: Seq::empty(), running: None, used: 0, next_serial: 1 }, &layout)) by { reveal(inv); }
        assert(frozen_views(Seq::<FrozenVersion>::empty()) =~= Seq::<FrozenView>::empty());
        let queue = Queue { layout, frozen: Vec::new(), running: None, serial: 0, used: 0, next_serial: 1 };
        assert(queue.wf());
        Some(queue)
    }

    pub fn accounting(&self) -> (r: (u32, u32, usize, bool))
        ensures r.0 == self.view().used, r.1 as nat == capacity(self.mapping()),
            self.wf() ==> r.0 <= r.1, r.2 == self.view().frozen.len(), r.3 == self.view().running.is_some(),
    {
        proof { if self.wf() { reveal(inv); } }
        let blocks = self.layout.blocks();
        (self.used, if blocks >= 2 { blocks - 2 } else { 0 }, self.frozen.len(), self.running.is_some())
    }

    pub fn frozen_versions(&self) -> (r: &[FrozenVersion])
        ensures frozen_views(r@) == self.view().frozen,
    { &self.frozen[..] }

    pub fn borrow_work(&mut self, at: usize) -> (r: Option<(&[FrozenVersion], Part<'_>, Part<'_>)>)
        ensures final(self).mapping().view() == old(self).mapping().view(),
            final(self).view().frozen == old(self).view().frozen,
            final(self).view().used == old(self).view().used, final(self).view().next_serial == old(self).view().next_serial,
            old(self).wf() ==> final(self).wf(),
            match r {
                Some((frozen, left, right)) => old(self).view().running.is_some()
                    && frozen_views(frozen@) == old(self).view().frozen && left.wf() && right.wf()
                    && at <= old(self).view().running.unwrap().edits.len()
                    && left.part_view() == old(self).view().running.unwrap().edits.take(at as int)
                    && right.part_view() == old(self).view().running.unwrap().edits.skip(at as int)
                    && final(self).view().running.is_some()
                    && final(self).view().running.unwrap().edits == left.future_view() + right.future_view(),
                None => final(self).view() == old(self).view(),
            },
    {
        proof { if self.wf() { reveal(inv); } }
        let ghost before = self.view();
        let ghost was_valid = self.wf();
        let frozen = &self.frozen[..];
        let running = match self.running.as_mut() { Some(running) => running, None => { return None; } };
        match running.borrow_parts(at) {
            Some((left, right)) => {
                proof {
                    if was_valid {
                        editing_preserves_the_shared_reservations(before, left.future_view() + right.future_view(), &self.layout);
                    }
                }
                Some((frozen, left, right))
            },
            None => None,
        }
    }

    pub fn reserve(&mut self, targets: &[u32]) -> (r: bool)
        ensures final(self).mapping().view() == old(self).mapping().view(),
            old(self).wf() ==> final(self).wf()
                && r == enabled(old(self).view(), Event::Reserve(targets@), old(self).mapping())
                && final(self).view() == if r { step(old(self).view(), Event::Reserve(targets@), old(self).mapping()) } else { old(self).view() },
            !r ==> final(self).view() == old(self).view(),
    {
        proof { if self.wf() { reveal(inv); } }
        if !self.layout.valid() || self.used > self.layout.blocks() - 2 || self.next_serial == 0 { return false; }
        if self.running.is_some() || self.frozen.len() >= MAX_VERSIONS || self.next_serial == MAX_SERIAL
            || targets.len() == 0 || targets.len() > 250 || targets.len() as u64 + 2 > (self.layout.blocks() - 2 - self.used) as u64 { return false; }
        let running = match edit_handles::reserve(targets, self.layout.duplicate()) { Some(running) => running, None => { return false; } };
        let ghost before = self.view();
        proof { if self.wf() { every_queue_event_preserves_credits_and_versions(before, Event::Reserve(targets@), &self.layout); } }
        self.serial = self.next_serial;
        self.next_serial += 1;
        self.used += targets.len() as u32 + 2;
        self.running = Some(running);
        true
    }

    pub fn cancel(&mut self) -> (r: Option<u64>)
        ensures final(self).mapping().view() == old(self).mapping().view(), old(self).wf() ==> final(self).wf() && match r {
            Some(serial) => old(self).view().running.is_some() && serial == old(self).view().running.unwrap().serial
                && final(self).view() == step(old(self).view(), Event::Cancel, old(self).mapping()),
            None => old(self).view().running.is_none() && final(self).view() == old(self).view(),
        },
    {
        proof { if self.wf() { reveal(inv); } }
        let credits = match self.running.as_ref() { Some(running) => running.reserved_count() as u32 + 2, None => { return None; } };
        if credits > self.used { return None; }
        proof { if self.wf() { every_queue_event_preserves_credits_and_versions(self.view(), Event::Cancel, &self.layout); } }
        let _ = self.running.take();
        let serial = self.serial;
        self.used -= credits;
        self.serial = 0;
        Some(serial)
    }

    pub fn seal(&mut self) -> (r: Seal)
        ensures final(self).mapping().view() == old(self).mapping().view(), old(self).wf() ==> final(self).wf() && match r {
            Seal::Frozen(serial) => enabled(old(self).view(), Event::Seal, old(self).mapping())
                && serial == old(self).view().running.unwrap().serial
                && edit_handles::selected(old(self).view().running.unwrap().edits).len() > 0
                && final(self).view() == step(old(self).view(), Event::Seal, old(self).mapping()),
            Seal::Empty(serial) => enabled(old(self).view(), Event::Seal, old(self).mapping())
                && serial == old(self).view().running.unwrap().serial
                && edit_handles::selected(old(self).view().running.unwrap().edits).len() == 0
                && final(self).view() == step(old(self).view(), Event::Seal, old(self).mapping()),
            Seal::NotReady => old(self).view().running.is_some() && !enabled(old(self).view(), Event::Seal, old(self).mapping())
                && final(self).view() == old(self).view(),
            Seal::NoRunning => old(self).view().running.is_none() && final(self).view() == old(self).view(),
            Seal::Invalid => false,
        },
    {
        proof { if self.wf() { reveal(inv); } }
        let ghost before = self.view();
        let ghost was_valid = self.wf();
        if !self.layout.valid() || self.used > self.layout.blocks() - 2 || self.serial == 0 {
            if self.running.is_none() { return Seal::NoRunning; }
            return Seal::Invalid;
        }
        let running = match self.running.take() { Some(running) => running, None => { return Seal::NoRunning; } };
        let reserved = running.reserved_count() as u32 + 2;
        if reserved > self.used { self.running = Some(running); return Seal::Invalid; }
        let base = self.used - reserved;
        let serial = self.serial;
        let frozen = match running.freeze() {
            Ok(frozen) => frozen,
            Err(running) => { self.running = Some(running); return Seal::NotReady; },
        };
        let count = frozen.frozen_count();
        proof { if was_valid { every_queue_event_preserves_credits_and_versions(before, Event::Seal, &self.layout); } }
        self.serial = 0;
        if count == 0 { self.used = base; return Seal::Empty(serial); }
        let blocks = count as u32 + 2;
        let layout = frozen.reserved_layout();
        if layout.physical_start() != self.layout.physical_start() || layout.blocks() != self.layout.blocks()
            || layout.filesystem_blocks() != self.layout.filesystem_blocks() {
            self.used = base;
            return Seal::Invalid;
        }
        assert(edit_handles::batch_valid(frozen.frozen_view(), &self.layout));
        let record = FrozenVersion { serial, first: base + 1, blocks, batch: frozen };
        let ghost previous = frozen_views(self.frozen@);
        self.frozen.push(record);
        assert(frozen_views(self.frozen@) =~= previous.push(record.view()));
        self.used = base + blocks;
        Seal::Frozen(serial)
    }
}

}
