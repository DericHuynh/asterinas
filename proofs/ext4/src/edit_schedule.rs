// SPDX-License-Identifier: MPL-2.0

//! Finite interleavings of the exact slot transitions implemented by the
//! borrowed edit handles. This is candidate-batch isolation, not global log
//! reservation, runtime scheduler progress or concurrent physical persistence.

use vstd::prelude::*;
use crate::{edit_handles::{self, Action, EditView, StageView, Status}, layout::JournalLayout};

verus! {

pub struct Event { pub position: int, pub action: Action }

pub open spec fn slot_valid(edit: EditView) -> bool {
    &&& (edit.stage.status == Status::Unused || edit.stage.status == Status::Aborted ==> edit.stage.image.is_none())
    &&& match edit.stage.image { Some(image) => image.block == edit.target && image.image.len() == 4096, None => true }
}

pub open spec fn inv(edits: Seq<EditView>) -> bool {
    &&& 0 < edits.len() <= edit_handles::MAX_CREDITS
    &&& forall|i: int| 0 <= i < edits.len() ==> slot_valid(#[trigger] edits[i])
    &&& forall|i: int, j: int| 0 <= i < j < edits.len() ==> (#[trigger] edits[i]).target < (#[trigger] edits[j]).target
}

pub open spec fn enabled(edits: Seq<EditView>, event: Event) -> bool {
    0 <= event.position < edits.len() && edit_handles::slot_enabled(edits[event.position], event.action)
}

pub open spec fn next(edits: Seq<EditView>, event: Event) -> Seq<EditView> {
    edits.update(event.position, edit_handles::slot_next(edits[event.position], event.action))
}

pub proof fn a_slot_transition_preserves_its_target_and_image_domain(edit: EditView, action: Action)
    requires slot_valid(edit), edit_handles::slot_enabled(edit, action),
    ensures slot_valid(edit_handles::slot_next(edit, action)), edit_handles::slot_next(edit, action).target == edit.target,
{
    match action { Action::Open => {}, Action::Stage(_) => {}, Action::Close => {}, Action::Abort => {} }
}

pub proof fn every_edit_event_preserves_reservations_and_isolation(edits: Seq<EditView>, event: Event)
    requires inv(edits), enabled(edits, event),
    ensures inv(next(edits, event)), next(edits, event).len() == edits.len(),
        forall|i: int| 0 <= i < edits.len() ==> (#[trigger] next(edits, event)[i]).target == edits[i].target,
        forall|i: int| 0 <= i < edits.len() && i != event.position ==> (#[trigger] next(edits, event)[i]) == edits[i],
{
    a_slot_transition_preserves_its_target_and_image_domain(edits[event.position], event.action);
    let after = next(edits, event);
    assert forall|i: int| 0 <= i < after.len() implies slot_valid(#[trigger] after[i]) by {
        if i != event.position { assert(after[i] == edits[i]); }
    }
    assert forall|i: int, j: int| 0 <= i < j < after.len() implies (#[trigger] after[i]).target < (#[trigger] after[j]).target by {
        assert(after[i].target == edits[i].target && after[j].target == edits[j].target);
    }
}

pub proof fn distinct_slot_events_commute(edits: Seq<EditView>, left: Event, right: Event)
    requires inv(edits), enabled(edits, left), enabled(edits, right), left.position != right.position,
    ensures enabled(next(edits, left), right), enabled(next(edits, right), left),
        next(next(edits, left), right) == next(next(edits, right), left),
{
    assert(next(next(edits, left), right) =~= next(next(edits, right), left));
}

pub open spec fn retired(edit: EditView) -> bool { edit.stage.status == Status::Closed || edit.stage.status == Status::Aborted }

pub proof fn retired_slots_cannot_change_or_reopen(edits: Seq<EditView>, event: Event, position: int)
    requires inv(edits), enabled(edits, event), 0 <= position < edits.len(), retired(edits[position]),
    ensures next(edits, event)[position] == edits[position], !edit_handles::slot_enabled(edits[position], Action::Open),
{
    assert(event.position != position) by {
        if event.position == position {
            match event.action { Action::Open => {}, Action::Stage(_) => {}, Action::Close => {}, Action::Abort => {} }
        }
    }
}

pub open spec fn execution(states: Seq<Seq<EditView>>, events: Seq<Event>) -> bool {
    &&& states.len() == events.len() + 1
    &&& inv(states[0])
    &&& forall|i: int| 0 <= i < events.len() ==> enabled(states[i], #[trigger] events[i]) && states[i + 1] == next(states[i], events[i])
}

pub proof fn every_finite_edit_interleaving_preserves_invariants(states: Seq<Seq<EditView>>, events: Seq<Event>)
    requires execution(states, events),
    ensures inv(states.last()), states.last().len() == states[0].len(),
        forall|i: int| 0 <= i < states[0].len() ==> (#[trigger] states.last()[i]).target == states[0][i].target,
        forall|i: int| 0 <= i < states[0].len() && retired(states[0][i]) ==> (#[trigger] states.last()[i]) == states[0][i],
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = states.drop_last();
        let prior_events = events.drop_last();
        assert(execution(prefix, prior_events));
        every_finite_edit_interleaving_preserves_invariants(prefix, prior_events);
        let before = prefix.last();
        let event = events.last();
        every_edit_event_preserves_reservations_and_isolation(before, event);
        assert forall|i: int| 0 <= i < states[0].len() && retired(states[0][i]) implies (#[trigger] states.last()[i]) == states[0][i] by {
            retired_slots_cannot_change_or_reopen(before, event, i);
        }
    }
}

pub proof fn frozen_selection_retains_only_reserved_targets(edits: Seq<EditView>, layout: &JournalLayout)
    requires inv(edits), edit_handles::ready(edits), layout.wf(),
        forall|i: int| 0 <= i < edits.len() ==> layout.allowed((#[trigger] edits[i]).target),
    ensures edit_handles::batch_valid(edit_handles::selected(edits), layout),
{
    edit_handles::closed_selection_has_bounded_disjoint_reserved_images(edits, layout);
}

pub proof fn an_open_or_aborted_slot_blocks_freezing(edits: Seq<EditView>, position: int)
    requires inv(edits), 0 <= position < edits.len(), edits[position].stage.status != Status::Closed,
    ensures !edit_handles::ready(edits),
{
    if edit_handles::ready(edits) { assert(edits[position].stage.status == Status::Closed); }
}

pub proof fn nonempty_two_worker_close_and_freeze_example()
    ensures exists|edits: Seq<EditView>| inv(edits) && edits.len() == 2 && edit_handles::ready(edits)
        && edit_handles::selected(edits).len() == 2,
{
    let a = EditView { target: 3, stage: StageView { status: Status::Unused, image: None } };
    let b = EditView { target: 4, stage: StageView { status: Status::Unused, image: None } };
    let start = seq![a, b];
    assert(inv(start));
    let open_a = Event { position: 0, action: Action::Open };
    let open_b = Event { position: 1, action: Action::Open };
    distinct_slot_events_commute(start, open_a, open_b);
    let opened = next(next(start, open_a), open_b);
    every_edit_event_preserves_reservations_and_isolation(start, open_a);
    every_edit_event_preserves_reservations_and_isolation(next(start, open_a), open_b);
    let stage_a = Event { position: 0, action: Action::Stage(Seq::new(4096, |i: int| 0x31u8)) };
    let stage_b = Event { position: 1, action: Action::Stage(Seq::new(4096, |i: int| 0x32u8)) };
    distinct_slot_events_commute(opened, stage_a, stage_b);
    let staged = next(next(opened, stage_a), stage_b);
    every_edit_event_preserves_reservations_and_isolation(opened, stage_a);
    every_edit_event_preserves_reservations_and_isolation(next(opened, stage_a), stage_b);
    let close_a = Event { position: 0, action: Action::Close };
    let close_b = Event { position: 1, action: Action::Close };
    distinct_slot_events_commute(staged, close_a, close_b);
    let closed = next(next(staged, close_a), close_b);
    every_edit_event_preserves_reservations_and_isolation(staged, close_a);
    every_edit_event_preserves_reservations_and_isolation(next(staged, close_a), close_b);
    assert(edit_handles::ready(closed));
    reveal_with_fuel(edit_handles::selected, 3);
    assert(closed.drop_last() == seq![closed[0]]);
    assert(closed.drop_last().drop_last() == Seq::<EditView>::empty());
    assert(edit_handles::selected(closed).len() == 2);
    assert(inv(closed) && closed.len() == 2 && edit_handles::ready(closed) && edit_handles::selected(closed).len() == 2);
}

}
