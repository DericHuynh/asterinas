// SPDX-License-Identifier: MPL-2.0

//! All finite interleavings of the executable reservation queue transitions.
//! Log-space isolation and immutable bytes do not imply durable commitment.

use vstd::prelude::*;
use crate::{edit_handles::{self, Action, EditView}, edit_schedule,
    journal_queue::{self, Event, FrozenView, QueueView}, layout::JournalLayout, transaction::ImageView};

verus! {

proof fn occupied_prefix_is_monotone(records: Seq<FrozenView>, first: nat, last: nat)
    requires first <= last <= records.len(),
    ensures journal_queue::occupied(records.take(first as int)) <= journal_queue::occupied(records.take(last as int)),
    decreases last,
{
    if first < last {
        occupied_prefix_is_monotone(records, first, (last - 1) as nat);
        assert(records.take(last as int).drop_last() =~= records.take(last as int - 1));
        assert(records.take(last as int).last() == records[last as int - 1]);
        reveal(journal_queue::occupied);
    }
}

pub proof fn sealed_versions_reserve_disjoint_physical_log_slots(v: QueueView, layout: &JournalLayout, older: int, newer: int, a: u32, b: u32)
    requires journal_queue::inv(v, layout), 0 <= older < newer < v.frozen.len(),
        a < v.frozen[older].blocks, b < v.frozen[newer].blocks,
    ensures v.frozen[older].first as nat + v.frozen[older].blocks <= v.frozen[newer].first,
        layout.view().start as nat + v.frozen[older].first as nat + a
            < layout.view().start as nat + v.frozen[newer].first as nat + b,
{
    reveal(journal_queue::inv);
    assert(journal_queue::frozen_valid(v.frozen[older], layout));
    assert(journal_queue::frozen_valid(v.frozen[newer], layout));
    occupied_prefix_is_monotone(v.frozen, (older + 1) as nat, newer as nat);
    assert(v.frozen.take(older + 1).drop_last() =~= v.frozen.take(older));
    assert(v.frozen.take(older + 1).last() == v.frozen[older]);
    reveal(journal_queue::occupied);
}

pub open spec fn execution(states: Seq<QueueView>, events: Seq<Event>, layout: &JournalLayout) -> bool {
    &&& states.len() == events.len() + 1 && journal_queue::inv(states[0], layout)
    &&& (forall|i: int| 0 <= i < events.len() ==> #[trigger] journal_queue::enabled(states[i], events[i], layout)
        && states[i + 1] == journal_queue::step(states[i], events[i], layout))
}

proof fn a_cut_preserves_the_original_versions(states: Seq<QueueView>, events: Seq<Event>, layout: &JournalLayout, cut: nat)
    requires execution(states, events, layout), cut < states.len(),
    ensures journal_queue::inv(states[cut as int], layout), states[cut as int].next_serial >= states[0].next_serial,
        states[cut as int].frozen.len() >= states[0].frozen.len(),
        forall|i: int| 0 <= i < states[0].frozen.len() ==> (#[trigger] states[cut as int].frozen[i]) == states[0].frozen[i],
    decreases cut,
{
    if cut > 0 {
        a_cut_preserves_the_original_versions(states, events, layout, (cut - 1) as nat);
        let previous = states[cut as int - 1];
        let event = events[cut as int - 1];
        assert(journal_queue::enabled(previous, event, layout));
        journal_queue::every_queue_event_preserves_credits_and_versions(previous, event, layout);
        assert forall|i: int| 0 <= i < states[0].frozen.len() implies (#[trigger] states[cut as int].frozen[i]) == states[0].frozen[i] by {
            assert(previous.frozen[i] == states[0].frozen[i]);
        }
    }
}

pub proof fn every_finite_queue_interleaving_keeps_reservations_and_frozen_bytes(states: Seq<QueueView>, events: Seq<Event>, layout: &JournalLayout)
    requires execution(states, events, layout),
    ensures forall|cut: int| 0 <= cut < states.len() ==> #[trigger] journal_queue::inv(states[cut], layout),
        forall|cut: int| 0 <= cut < states.len() ==> (#[trigger] states[cut]).next_serial >= states[0].next_serial,
        forall|cut: int| 0 <= cut < states.len() ==> (#[trigger] states[cut]).frozen.len() >= states[0].frozen.len(),
        forall|cut: int, i: int| 0 <= cut < states.len() && 0 <= i < states[0].frozen.len()
            ==> (#[trigger] states[cut].frozen[i]) == states[0].frozen[i],
{
    assert forall|cut: int| 0 <= cut < states.len() implies #[trigger] journal_queue::inv(states[cut], layout) by {
        a_cut_preserves_the_original_versions(states, events, layout, cut as nat);
    }
    assert forall|cut: int| 0 <= cut < states.len() implies (#[trigger] states[cut]).next_serial >= states[0].next_serial by {
        a_cut_preserves_the_original_versions(states, events, layout, cut as nat);
    }
    assert forall|cut: int| 0 <= cut < states.len() implies (#[trigger] states[cut]).frozen.len() >= states[0].frozen.len() by {
        a_cut_preserves_the_original_versions(states, events, layout, cut as nat);
    }
    assert forall|cut: int, i: int| 0 <= cut < states.len() && 0 <= i < states[0].frozen.len()
        implies (#[trigger] states[cut].frozen[i]) == states[0].frozen[i] by {
        a_cut_preserves_the_original_versions(states, events, layout, cut as nat);
    }
}

pub proof fn cancellation_cannot_resurrect_its_reservation_serial(states: Seq<QueueView>, events: Seq<Event>, layout: &JournalLayout, retired: u64)
    requires execution(states, events, layout), states[0].running.is_some(), retired == states[0].running.unwrap().serial,
    ensures forall|i: int, targets: Seq<u32>| 0 <= i < states.len()
        && #[trigger] journal_queue::enabled(states[i], Event::Reserve(targets), layout) ==> states[i].next_serial > retired,
{
    every_finite_queue_interleaving_keeps_reservations_and_frozen_bytes(states, events, layout);
    reveal(journal_queue::inv);
    assert forall|i: int, targets: Seq<u32>| 0 <= i < states.len()
        && #[trigger] journal_queue::enabled(states[i], Event::Reserve(targets), layout) implies states[i].next_serial > retired by {
        assert(journal_queue::inv(states[i], layout));
    }
}

pub proof fn a_terminal_reservation_counter_never_wraps(states: Seq<QueueView>, events: Seq<Event>, layout: &JournalLayout)
    requires execution(states, events, layout), states[0].next_serial == journal_queue::MAX_SERIAL,
    ensures states.last().next_serial == journal_queue::MAX_SERIAL,
        forall|targets: Seq<u32>| !#[trigger] journal_queue::enabled(states.last(), Event::Reserve(targets), layout),
{
    every_finite_queue_interleaving_keeps_reservations_and_frozen_bytes(states, events, layout);
    assert(journal_queue::inv(states.last(), layout));
}

pub proof fn nonempty_older_frozen_and_newer_private_versions_example(layout: &JournalLayout)
    requires layout.wf(),
    ensures exists|v: QueueView| journal_queue::inv(v, layout) && v.frozen.len() == 1 && v.running.is_some()
        && v.frozen[0].images.len() == 1 && v.frozen[0].images[0].image[0] == 0x41
        && v.running.unwrap().edits.len() == 1 && v.running.unwrap().edits[0].stage.image.is_some()
        && v.running.unwrap().edits[0].stage.image.unwrap().image[0] == 0x42,
{
    let initial = QueueView { frozen: Seq::empty(), running: None, used: 0, next_serial: 1 };
    assert(journal_queue::occupied(Seq::empty()) == 0) by { reveal(journal_queue::occupied); }
    assert(journal_queue::inv(initial, layout)) by { reveal(journal_queue::inv); }
    let reserve = Event::Reserve(seq![0u32]);
    let open = Event::Edit(edit_schedule::Event { position: 0, action: Action::Open });
    let old_bytes = Seq::new(4096, |i: int| 0x41u8);
    let new_bytes = Seq::new(4096, |i: int| 0x42u8);
    let stage_old = Event::Edit(edit_schedule::Event { position: 0, action: Action::Stage(old_bytes) });
    let stage_new = Event::Edit(edit_schedule::Event { position: 0, action: Action::Stage(new_bytes) });
    let close = Event::Edit(edit_schedule::Event { position: 0, action: Action::Close });
    assert(journal_queue::enabled(initial, reserve, layout));
    journal_queue::every_queue_event_preserves_credits_and_versions(initial, reserve, layout);
    let reserved = journal_queue::step(initial, reserve, layout);
    journal_queue::every_queue_event_preserves_credits_and_versions(reserved, open, layout);
    let opened = journal_queue::step(reserved, open, layout);
    journal_queue::every_queue_event_preserves_credits_and_versions(opened, stage_old, layout);
    let staged = journal_queue::step(opened, stage_old, layout);
    journal_queue::every_queue_event_preserves_credits_and_versions(staged, close, layout);
    let closed = journal_queue::step(staged, close, layout);
    assert(edit_handles::selected(closed.running.unwrap().edits) == seq![ImageView { block: 0, image: old_bytes }]) by {
        reveal_with_fuel(edit_handles::selected, 2);
        assert(closed.running.unwrap().edits.drop_last() =~= Seq::<EditView>::empty());
    }
    journal_queue::every_queue_event_preserves_credits_and_versions(closed, Event::Seal, layout);
    let frozen = journal_queue::step(closed, Event::Seal, layout);
    journal_queue::every_queue_event_preserves_credits_and_versions(frozen, reserve, layout);
    let newer = journal_queue::step(frozen, reserve, layout);
    journal_queue::every_queue_event_preserves_credits_and_versions(newer, open, layout);
    let editing = journal_queue::step(newer, open, layout);
    journal_queue::every_queue_event_preserves_credits_and_versions(editing, stage_new, layout);
    let result = journal_queue::step(editing, stage_new, layout);
    assert(journal_queue::inv(result, layout));
    assert(result.frozen[0].images[0].image[0] == 0x41);
    assert(result.running.unwrap().edits[0].stage.image.unwrap().image[0] == 0x42);
}

}
