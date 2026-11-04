// SPDX-License-Identifier: MPL-2.0

//! Borrowed disjoint transaction edit handles. Target credits are reserved
//! before editing; freeze consumes the running batch after every slot closes.
//! These are candidate after-images, not VFS, mount or device authority.

use vstd::prelude::*;
use crate::{frozen::FrozenBlock, layout::{JournalLayout, LayoutView}, transaction::{self, AfterImage, Encoded, ImageView}};

verus! {

pub const MAX_CREDITS: usize = 250;

#[derive(Clone, Copy)]
pub enum Status { Unused, Open, Closed, Aborted }

pub struct Stage { status: Status, image: Option<AfterImage> }
pub struct StageView { pub status: Status, pub image: Option<ImageView> }
pub struct EditView { pub target: u32, pub stage: StageView }

pub enum Action { Open, Stage(Seq<u8>), Close, Abort }

pub open spec fn slot_enabled(edit: EditView, action: Action) -> bool {
    match action {
        Action::Open => edit.stage.status == Status::Unused,
        Action::Stage(bytes) => edit.stage.status == Status::Open && bytes.len() == 4096,
        Action::Close | Action::Abort => edit.stage.status == Status::Open,
    }
}

pub open spec fn slot_next(edit: EditView, action: Action) -> EditView {
    EditView { target: edit.target, stage: match action {
        Action::Open => StageView { status: Status::Open, ..edit.stage },
        Action::Stage(bytes) => StageView { status: Status::Open, image: Some(ImageView { block: edit.target, image: bytes }) },
        Action::Close => StageView { status: Status::Closed, ..edit.stage },
        Action::Abort => StageView { status: Status::Aborted, image: None },
    } }
}

impl Stage {
    pub closed spec fn stage_view(&self) -> StageView {
        StageView { status: self.status, image: match self.image { Some(image) => Some(image.view()), None => None } }
    }
    spec fn wf(&self) -> bool {
        &&& (self.status == Status::Unused || self.status == Status::Aborted ==> self.image.is_none())
        &&& match self.image { Some(image) => image.view().image.len() == 4096, None => true }
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
}

pub open spec fn sorted(targets: Seq<u32>) -> bool {
    targets.len() <= MAX_CREDITS && forall|i: int, j: int| 0 <= i < j < targets.len() ==> #[trigger] targets[i] < #[trigger] targets[j]
}

pub open spec fn views(targets: Seq<u32>, stages: Seq<Stage>) -> Seq<EditView> {
    let count = if targets.len() < stages.len() { targets.len() } else { stages.len() };
    Seq::new(count, |i: int| EditView { target: targets[i], stage: stages[i].stage_view() })
}

pub open spec fn ready(edits: Seq<EditView>) -> bool {
    forall|i: int| 0 <= i < edits.len() ==> (#[trigger] edits[i]).stage.status == Status::Closed
        && match edits[i].stage.image { Some(image) => image.block == edits[i].target && image.image.len() == 4096, None => true }
}

#[verifier::opaque]
pub open spec fn selected(edits: Seq<EditView>) -> Seq<ImageView>
    decreases edits.len(),
{
    if edits.len() == 0 { Seq::empty() } else {
        selected(edits.drop_last()) + match edits.last().stage.image { Some(image) => seq![image], None => Seq::empty() }
    }
}


pub open spec fn batch_valid(images: Seq<ImageView>, layout: &JournalLayout) -> bool {
    &&& layout.wf() && images.len() <= MAX_CREDITS
    &&& forall|i: int| 0 <= i < images.len() ==> (#[trigger] images[i]).image.len() == 4096 && layout.allowed(images[i].block)
    &&& forall|i: int, j: int| 0 <= i < j < images.len() ==> (#[trigger] images[i]).block < (#[trigger] images[j]).block
}

proof fn selected_source_position(edits: Seq<EditView>, index: int) -> (r: int)
    requires ready(edits), 0 <= index < selected(edits).len(),
    ensures 0 <= r < edits.len(), edits[r].stage.image == Some(selected(edits)[index]), selected(edits)[index].block == edits[r].target,
    decreases edits.len(),
{
    reveal(selected);
    let prefix = edits.drop_last();
    assert(ready(prefix));
    match edits.last().stage.image {
        Some(image) => {
            if index < selected(prefix).len() { selected_source_position(prefix, index) }
            else { edits.len() as int - 1 }
        },
        None => selected_source_position(prefix, index),
    }
}

pub proof fn closed_selection_has_bounded_disjoint_reserved_images(edits: Seq<EditView>, layout: &JournalLayout)
    requires layout.wf(), edits.len() <= MAX_CREDITS, ready(edits),
        forall|i: int| 0 <= i < edits.len() ==> layout.allowed((#[trigger] edits[i]).target),
        forall|i: int, j: int| 0 <= i < j < edits.len() ==> (#[trigger] edits[i]).target < (#[trigger] edits[j]).target,
    ensures selected(edits).len() <= edits.len(), batch_valid(selected(edits), layout),
    decreases edits.len(),
{
    reveal(selected);
    if edits.len() > 0 {
        let prefix = edits.drop_last();
        assert(ready(prefix));
        closed_selection_has_bounded_disjoint_reserved_images(prefix, layout);
    }
    assert forall|i: int| 0 <= i < selected(edits).len() implies (#[trigger] selected(edits)[i]).image.len() == 4096
        && layout.allowed(selected(edits)[i].block) by {
        let at = selected_source_position(edits, i);
        assert(edits[at].stage.image == Some(selected(edits)[i]));
    }
    assert forall|i: int, j: int| 0 <= i < j < selected(edits).len() implies (#[trigger] selected(edits)[i]).block < (#[trigger] selected(edits)[j]).block by {
        let prefix = edits.drop_last();
        if j < selected(prefix).len() { assert(batch_valid(selected(prefix), layout)); }
        else {
            let at = selected_source_position(prefix, i);
            assert(selected(edits)[j].block == edits.last().target);
            assert(edits[at].target < edits[edits.len() as int - 1].target);
        }
    }
}

proof fn selected_prefix_step(edits: Seq<EditView>, count: int)
    requires 0 <= count < edits.len(),
    ensures selected(edits.take(count + 1)) == selected(edits.take(count))
        + match edits[count].stage.image { Some(image) => seq![image], None => Seq::empty() },
{
    assert(edits.take(count + 1).drop_last() =~= edits.take(count));
    reveal(selected);
}

struct Plan { targets: Vec<u32>, layout: JournalLayout }
struct Keys<'s> { values: &'s [u32] }

impl Plan {
    spec fn wf(&self) -> bool {
        &&& 0 < self.targets.len() <= MAX_CREDITS && sorted(self.targets@) && self.layout.wf()
        &&& forall|i: int| 0 <= i < self.targets.len() ==> self.layout.allowed(#[trigger] self.targets@[i])
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
}

impl<'s> Keys<'s> {
    spec fn wf(&self) -> bool { sorted(self.values@) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
}

pub struct Running { plan: Plan, stages: Vec<Stage> }
pub struct Part<'s> { keys: Keys<'s>, stages: &'s mut [Stage] }
pub struct Handle<'s> { key: u32, slot: &'s mut Stage }
pub struct FrozenBatch { images: Vec<AfterImage>, layout: JournalLayout }


// Range indexing supplies the fixed final lengths as well as the split's
// value relation; no local library specification is introduced here.
fn split_storage(slice: &mut [Stage], at: usize) -> (r: (&mut [Stage], &mut [Stage]))
    requires at <= slice.len(),
    ensures r.0@ == old(slice)@.take(at as int), r.1@ == old(slice)@.skip(at as int),
        final(r.0)@.len() == at, final(r.1)@.len() == old(slice).len() - at,
        final(slice)@ == final(r.0)@ + final(r.1)@, final(slice).len() == old(slice).len(),
{
    let (left, right) = slice.split_at_mut(at);
    (&mut left[..], &mut right[..])
}

fn split_storage_vec(vec: &mut Vec<Stage>, at: usize) -> (r: (&mut [Stage], &mut [Stage]))
    requires at <= vec.len(),
    ensures r.0@ == old(vec)@.take(at as int), r.1@ == old(vec)@.skip(at as int),
        final(r.0)@.len() == at, final(r.1)@.len() == old(vec).len() - at,
        final(vec)@ == final(r.0)@ + final(r.1)@, final(vec).len() == old(vec).len(),
{
    split_storage(vec.as_mut_slice(), at)
}

impl Running {
    pub closed spec fn edit_view(&self) -> Seq<EditView> { views(self.plan.targets@, self.stages@) }
    pub closed spec fn layout_view(&self) -> LayoutView { self.plan.layout.view() }
    pub closed spec fn credits(&self) -> nat { self.plan.targets.len() as nat }
    pub closed spec fn wf(&self) -> bool { self.plan.wf() && self.plan.targets.len() == self.stages.len() }

    pub fn reserved_count(&self) -> (r: usize) ensures r == self.credits(), 0 < r <= MAX_CREDITS, self.wf() ==> r == self.edit_view().len() {
        proof { use_type_invariant(&self.plan); }
        self.plan.targets.len()
    }

    pub fn borrow_parts(&mut self, at: usize) -> (r: Option<(Part<'_>, Part<'_>)>)
        ensures old(self).wf() ==> final(self).wf(), final(self).layout_view() == old(self).layout_view(),
            final(self).credits() == old(self).credits(), match r {
            Some((left, right)) => old(self).wf() && at <= old(self).edit_view().len() && left.wf() && right.wf()
                && left.part_view() == old(self).edit_view().take(at as int)
                && right.part_view() == old(self).edit_view().skip(at as int)
                && final(self).edit_view() == left.future_view() + right.future_view(),
            None => (!old(self).wf() || at > old(self).credits()) && final(self).edit_view() == old(self).edit_view(),
        },
    {
        proof { use_type_invariant(&self.plan); }
        if self.plan.targets.len() != self.stages.len() || at > self.plan.targets.len() { return None; }
        let (left_keys, right_keys) = self.plan.targets.as_slice().split_at(at);
        let (left_stages, right_stages) = split_storage_vec(&mut self.stages, at);
        Some((Part { keys: Keys { values: left_keys }, stages: left_stages }, Part { keys: Keys { values: right_keys }, stages: right_stages }))
    }
}


impl Running {
    pub closed spec fn can_freeze(&self) -> bool { self.wf() && ready(self.edit_view()) }

    pub fn freeze(mut self) -> (r: Result<FrozenBatch, Self>)
        ensures match r {
            Ok(frozen) => self.can_freeze() && frozen.wf() && frozen.frozen_view() == selected(self.edit_view())
                && frozen.frozen_layout() == self.layout_view(),
            Err(running) => !self.can_freeze() && running.edit_view() == self.edit_view()
                && running.layout_view() == self.layout_view() && running.credits() == self.credits(),
        },
    {
        proof { use_type_invariant(&self.plan); }
        if self.plan.targets.len() != self.stages.len() { return Err(self); }
        let ghost before = self.edit_view();
        let mut index = 0usize;
        while index < self.stages.len()
            invariant self.wf(), before == self.edit_view(), index <= self.stages.len(),
                forall|i: int| 0 <= i < index ==> (#[trigger] before[i]).stage.status == Status::Closed
                    && match before[i].stage.image { Some(image) => image.block == before[i].target && image.image.len() == 4096, None => true },
            decreases self.stages.len() - index,
        {
            assert(before[index as int].stage == self.stages@[index as int].stage_view());
            assert(before[index as int].target == self.plan.targets@[index as int]);
            match self.stages[index].status {
                Status::Closed => {},
                _ => {
                    assert(!ready(before)) by {
                        if ready(before) { assert(before[index as int].stage.status == Status::Closed); }
                    }
                    return Err(self);
                }
            }
            match &self.stages[index].image {
                Some(image) => {
                    if image.block() != self.plan.targets[index] {
                        assert(!ready(before)) by {
                            if ready(before) { assert(before[index as int].stage.image.unwrap().block == before[index as int].target); }
                        }
                        return Err(self);
                    }
                },
                None => {},
            }
            index += 1;
        }
        assert(ready(before));
        let ghost keys = self.plan.targets@;
        let ghost layout = self.plan.layout.view();
        assert forall|i: int, j: int| 0 <= i < j < before.len() implies (#[trigger] before[i]).target < (#[trigger] before[j]).target by {
            assert(before[i].target == keys[i] && before[j].target == keys[j]);
        }
        proof { closed_selection_has_bounded_disjoint_reserved_images(before, &self.plan.layout); }
        let mut reverse: Vec<AfterImage> = Vec::new();
        assert(before.take(self.stages.len() as int) == before);
        assert(transaction::images(reverse@) == Seq::<ImageView>::empty());
        while self.stages.len() > 0
            invariant self.plan.wf(), self.plan.targets@ == keys, self.plan.layout.view() == layout,
                self.stages.len() <= before.len() == keys.len(), ready(before), batch_valid(selected(before), &self.plan.layout),
                forall|i: int| 0 <= i < self.stages.len() ==> (#[trigger] self.stages@[i]).stage_view() == before[i].stage,
                selected(before) == selected(before.take(self.stages.len() as int)) + transaction::images(reverse@).reverse(),
            decreases self.stages.len(),
        {
            let count = self.stages.len();
            let stage = self.stages.pop().unwrap();
            let ghost previous = transaction::images(reverse@);
            proof { selected_prefix_step(before, count as int - 1); }
            let Stage { status: _, image } = stage;
            match image { Some(image) => reverse.push(image), None => {} }
            proof {
                assert(transaction::images(reverse@).reverse() =~= match before[count as int - 1].stage.image {
                    Some(image) => seq![image] + previous.reverse(), None => previous.reverse(),
                });
            }
        }
        assert(selected(Seq::empty()) == Seq::<ImageView>::empty()) by { reveal(selected); }
        assert(before.take(0) == Seq::<EditView>::empty());
        assert(selected(before) == transaction::images(reverse@).reverse());
        let ghost previous_elements = reverse@;
        let ghost previous_images = transaction::images(reverse@);
        reverse.reverse();
        assert(transaction::images(reverse@) =~= previous_images.reverse());
        assert(transaction::images(reverse@) == selected(before));
        let Plan { targets: _, layout } = self.plan;
        Ok(FrozenBatch { images: reverse, layout })
    }
}

impl FrozenBatch {
    pub closed spec fn frozen_view(&self) -> Seq<ImageView> { transaction::images(self.images@) }
    pub closed spec fn frozen_layout(&self) -> LayoutView { self.layout.view() }
    pub closed spec fn wf(&self) -> bool { batch_valid(self.frozen_view(), &self.layout) }
    pub closed spec fn can_encode(&self, uuid: Seq<u8>, sequence: u32, primary: Seq<u8>, partition_bytes: u64) -> bool {
        transaction::input_ok(self.frozen_view(), uuid, sequence, &self.layout, primary, partition_bytes)
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn frozen_count(&self) -> (r: usize) ensures self.wf(), r == self.frozen_view().len(), r <= MAX_CREDITS {
        proof { use_type_invariant(self); }
        self.images.len()
    }

    pub fn into_images(self) -> (r: Vec<AfterImage>)
        ensures self.wf(), transaction::images(r@) == self.frozen_view(),
    {
        proof { use_type_invariant(&self); }
        self.images
    }

    pub fn reserved_layout(&self) -> (r: &JournalLayout)
        ensures self.wf(), r.wf(), r.view() == self.frozen_layout(),
    {
        proof { use_type_invariant(self); }
        &self.layout
    }

    pub fn encode(self, uuid: &[u8], sequence: u32, primary: &[u8], partition_bytes: u64) -> (r: Option<Encoded>)
        ensures self.wf(), match r {
            Some(tx) => transaction::wf(tx.view()) && tx.view().original == self.frozen_view() && tx.view().layout == self.frozen_layout(),
            None => !self.can_encode(uuid@, sequence, primary@, partition_bytes),
        },
    {
        proof { use_type_invariant(&self); }
        transaction::encode(self.images, uuid, sequence, &self.layout, primary, partition_bytes)
    }
}

impl<'s> Part<'s> {
    pub closed spec fn part_view(&self) -> Seq<EditView> { views(self.keys.values@, self.stages@) }
    #[verifier::prophetic]
    pub closed spec fn future_view(&self) -> Seq<EditView> { views(self.keys.values@, final(self.stages)@) }
    pub closed spec fn part_credits(&self) -> nat { self.keys.values.len() as nat }
    pub closed spec fn wf(&self) -> bool { self.keys.wf() && self.keys.values.len() == self.stages.len() }

    pub fn part_count(&self) -> (r: usize) ensures r == self.part_credits(), r <= MAX_CREDITS, self.wf() ==> r == self.part_view().len() {
        proof { use_type_invariant(&self.keys); }
        self.keys.values.len()
    }

    pub fn release(self)
        ensures self.future_view() == self.part_view(),
    {
        let Part { keys: _, stages: _ } = self;
    }

    pub fn partition(&mut self, at: usize) -> (r: Option<(Part<'_>, Part<'_>)>)
        ensures final(self).future_view() == old(self).future_view(),
            old(self).wf() ==> final(self).wf(), match r {
            Some((left, right)) => old(self).wf() && at <= old(self).part_view().len() && left.wf() && right.wf()
                && left.part_view() == old(self).part_view().take(at as int)
                && right.part_view() == old(self).part_view().skip(at as int)
                && final(self).part_view() == left.future_view() + right.future_view(),
            None => (!old(self).wf() || at > old(self).part_credits()) && final(self).part_view() == old(self).part_view(),
        },
    {
        proof { use_type_invariant(&self.keys); }
        if self.keys.values.len() != self.stages.len() || at > self.keys.values.len() { return None; }
        let (left_keys, right_keys) = self.keys.values.split_at(at);
        let (left_stages, right_stages) = split_storage(self.stages, at);
        Some((Part { keys: Keys { values: left_keys }, stages: left_stages }, Part { keys: Keys { values: right_keys }, stages: right_stages }))
    }

    pub fn handle_at(&mut self, index: usize) -> (r: Option<Handle<'_>>)
        ensures final(self).future_view() == old(self).future_view(),
            old(self).wf() ==> final(self).wf(), match r {
            Some(handle) => old(self).wf() && index < old(self).part_view().len()
                && old(self).part_view()[index as int].stage.status == Status::Unused
                && handle.handle_view() == (EditView { stage: StageView { status: Status::Open,
                    ..old(self).part_view()[index as int].stage }, ..old(self).part_view()[index as int] })
                && final(self).part_view() == old(self).part_view().update(index as int, handle.future_edit()),
            None => (!old(self).wf() || index >= old(self).part_view().len() || old(self).part_view()[index as int].stage.status != Status::Unused)
                && final(self).part_view() == old(self).part_view(),
        },
    {
        proof { use_type_invariant(&self.keys); }
        if self.keys.values.len() != self.stages.len() || index >= self.keys.values.len() { return None; }
        let key = self.keys.values[index];
        open_slot(&mut self.stages[index], key)
    }
}


fn open_slot(slot: &mut Stage, key: u32) -> (r: Option<Handle<'_>>)
    ensures match r {
        Some(handle) => old(slot).stage_view().status == Status::Unused
            && slot_enabled(EditView { target: key, stage: old(slot).stage_view() }, Action::Open)
            && handle.handle_view() == slot_next(EditView { target: key, stage: old(slot).stage_view() }, Action::Open)
            && handle.handle_view() == (EditView { target: key, stage: StageView { status: Status::Open,
                ..old(slot).stage_view() } })
            && final(slot).stage_view() == handle.future_edit().stage,
        None => old(slot).stage_view().status != Status::Unused && final(slot).stage_view() == old(slot).stage_view(),
    },
    no_unwind
{
    proof { use_type_invariant(&*slot); }
    match slot.status { Status::Unused => {}, _ => { return None; } }
    slot.status = Status::Open;
    Some(Handle { key, slot })
}

impl<'s> Handle<'s> {
    pub closed spec fn handle_view(&self) -> EditView { EditView { target: self.key, stage: self.slot.stage_view() } }
    #[verifier::prophetic]
    pub closed spec fn future_edit(&self) -> EditView { EditView { target: self.key, stage: final(self.slot).stage_view() } }

    pub fn target(&self) -> (r: u32) ensures r == self.handle_view().target { self.key }

    pub fn stage(&mut self, bytes: &[u8]) -> (r: bool)
        ensures r == (old(self).handle_view().stage.status == Status::Open && bytes.len() == 4096),
            final(self).future_edit() == old(self).future_edit(),
            r == slot_enabled(old(self).handle_view(), Action::Stage(bytes@)),
            r ==> final(self).handle_view() == slot_next(old(self).handle_view(), Action::Stage(bytes@)),
            final(self).handle_view().target == old(self).handle_view().target,
            if r {
                old(self).handle_view().stage.status == Status::Open && bytes.len() == 4096
                    && final(self).handle_view() == (EditView { stage: StageView { status: Status::Open,
                        image: Some(ImageView { block: old(self).handle_view().target, image: bytes@ }) }, ..old(self).handle_view() })
            } else { final(self).handle_view() == old(self).handle_view() },
    {
        match self.slot.status { Status::Open => {}, _ => { return false; } }
        let image = match AfterImage::capture(self.key, bytes) { Some(image) => image, None => { return false; } };
        self.slot.image = Some(image);
        true
    }

    pub fn close(self) -> (r: bool)
        ensures r == (self.handle_view().stage.status == Status::Open),
            r == slot_enabled(self.handle_view(), Action::Close),
            r ==> self.future_edit() == slot_next(self.handle_view(), Action::Close),
            if r { self.handle_view().stage.status == Status::Open
            && self.future_edit() == (EditView { stage: StageView { status: Status::Closed,
                ..self.handle_view().stage }, ..self.handle_view() }) }
            else { self.future_edit() == self.handle_view() },
    {
        proof { use_type_invariant(&*self.slot); }
        match self.slot.status { Status::Open => {}, _ => { return false; } }
        self.slot.status = Status::Closed;
        true
    }

    pub fn abort(self) -> (r: bool)
        ensures r == (self.handle_view().stage.status == Status::Open),
            r == slot_enabled(self.handle_view(), Action::Abort),
            r ==> self.future_edit() == slot_next(self.handle_view(), Action::Abort),
            if r { self.future_edit() == (EditView { target: self.handle_view().target,
                stage: StageView { status: Status::Aborted, image: None } }) }
            else { self.future_edit() == self.handle_view() },
    {
        match self.slot.status { Status::Open => {}, _ => { return false; } }
        self.slot.image = None;
        self.slot.status = Status::Aborted;
        true
    }
}

pub open spec fn admissible_targets(targets: Seq<u32>, layout: &JournalLayout) -> bool {
    sorted(targets) && targets.len() > 0 && layout.wf()
        && forall|i: int| 0 <= i < targets.len() ==> layout.allowed(#[trigger] targets[i])
}

pub fn reserve(targets: &[u32], layout: JournalLayout) -> (r: Option<Running>)
    ensures match r {
        Some(running) => running.wf() && running.layout_view() == layout.view()
            && admissible_targets(targets@, &layout)
            && running.edit_view() == Seq::new(targets.len() as nat, |i: int| EditView { target: targets@[i],
                stage: StageView { status: Status::Unused, image: None } }),
        None => !admissible_targets(targets@, &layout),
    },
{
    if targets.len() == 0 || targets.len() > MAX_CREDITS || !layout.valid() { return None; }
    let mut keys: Vec<u32> = Vec::new();
    let mut stages: Vec<Stage> = Vec::new();
    let mut index = 0usize;
    while index < targets.len()
        invariant index <= targets.len() <= MAX_CREDITS, targets.len() > 0, layout.wf(),
            keys@ == targets@.take(index as int), stages.len() == index, sorted(keys@),
            forall|i: int| 0 <= i < index ==> layout.allowed(#[trigger] keys@[i]),
            forall|i: int| 0 <= i < index ==> (#[trigger] stages@[i]).stage_view() ==
                (StageView { status: Status::Unused, image: None }),
        decreases targets.len() - index,
    {
        let target = targets[index];
        if (index > 0 && targets[index - 1] >= target) || !layout.allows_target(target) { return None; }
        proof {
            assert forall|i: int| 0 <= i < index implies #[trigger] keys@[i] < target by {
                if i < index as int - 1 { assert(keys@[i] < keys@[index as int - 1]); }
            }
        }
        stages.push(Stage { status: Status::Unused, image: None });
        keys.push(target);
        index += 1;
    }
    assert(keys@ =~= targets@);
    Some(Running { plan: Plan { targets: keys, layout }, stages })
}

}
