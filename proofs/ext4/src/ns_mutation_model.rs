// SPDX-License-Identifier: MPL-2.0

//! Total optimistic namespace publication transitions over admitted immutable
//! images. Preparation may overlap; replacement of the complete current image
//! is one ordered transition. Actual OSTD locking and durable I/O are separate.

use vstd::prelude::*;
use crate::ea_namespace::{self, NamespaceView};

verus! {

pub const MAX_IMAGE_BYTES: u64 = 268435456;
pub const MAX_EPOCH: u64 = 18446744073709551615;

pub struct View {
    pub epoch: u64, pub limit: u64, pub source: Seq<u8>, pub certificate: NamespaceView,
}
pub struct PreparedView {
    pub epoch: u64, pub before: Seq<u8>, pub after: Seq<u8>,
    pub before_certificate: NamespaceView, pub after_certificate: NamespaceView,
}
pub struct CheckoutView { pub epoch: u64, pub source: Seq<u8>, pub certificate: NamespaceView }

pub open spec fn certified(certificate: NamespaceView, source: Seq<u8>) -> bool {
    ea_namespace::valid(certificate)
        && certificate.allocation.integrity.references.index.header.source == source
        && !crate::super_state::is_dirty(source)
}
#[verifier::opaque]
pub open spec fn valid(v: View) -> bool {
    v.epoch <= v.limit && 0 < v.source.len() <= MAX_IMAGE_BYTES as nat
        && certified(v.certificate, v.source)
}
#[verifier::opaque]
pub open spec fn prepared_valid(p: PreparedView) -> bool {
    0 < p.before.len() == p.after.len() <= MAX_IMAGE_BYTES as nat
        && certified(p.before_certificate, p.before) && certified(p.after_certificate, p.after)
}
pub open spec fn checkout_valid(c: CheckoutView) -> bool {
    0 < c.source.len() <= MAX_IMAGE_BYTES as nat && certified(c.certificate, c.source)
}
pub open spec fn capture(v: View) -> CheckoutView {
    CheckoutView { epoch: v.epoch, source: v.source, certificate: v.certificate }
}
pub open spec fn enabled(v: View, p: PreparedView) -> bool {
    valid(v) && prepared_valid(p) && p.epoch == v.epoch && p.before == v.source
        && v.epoch < v.limit && v.epoch < MAX_EPOCH
}
pub open spec fn publish_step(v: View, p: PreparedView) -> View {
    View { epoch: (v.epoch as nat + 1) as u64, limit: v.limit,
        source: p.after, certificate: p.after_certificate }
}

pub enum Event { Capture, Publish(PreparedView) }
pub open spec fn accepted(v: View, event: Event) -> bool {
    match event { Event::Capture => false, Event::Publish(p) => enabled(v, p) }
}
pub open spec fn step(v: View, event: Event) -> View {
    match event {
        Event::Capture => v,
        Event::Publish(p) => if enabled(v, p) { publish_step(v, p) } else { v },
    }
}

pub proof fn invariant_preserved_by_publication(v: View, p: PreparedView)
    requires valid(v), prepared_valid(p), enabled(v, p),
    ensures valid(publish_step(v, p)),
        publish_step(v, p).epoch as nat == v.epoch as nat + 1,
        publish_step(v, p).epoch <= v.limit,
        publish_step(v, p).limit == v.limit,
        publish_step(v, p).source == p.after,
        publish_step(v, p).certificate == p.after_certificate,
        publish_step(v, p).source.len() == v.source.len(),
{ reveal(valid); reveal(prepared_valid); }

pub proof fn every_event_preserves_the_current_namespace(v: View, event: Event)
    requires valid(v),
    ensures valid(step(v, event)), step(v, event).limit == v.limit,
        step(v, event).source.len() == v.source.len(),
        step(v, event).epoch as nat == v.epoch as nat + if accepted(v, event) { 1nat } else { 0nat },
        !accepted(v, event) ==> step(v, event) == v,
{
    match event {
        Event::Capture => { },
        Event::Publish(p) => {
            if enabled(v, p) { invariant_preserved_by_publication(v, p); }
        },
    }
}

pub proof fn a_conflicting_source_or_epoch_rejects_without_publication(v: View, p: PreparedView)
    requires p.epoch != v.epoch || p.before != v.source,
    ensures !enabled(v, p), step(v, Event::Publish(p)) == v,
{ }

pub proof fn exhausted_publication_counters_never_wrap(v: View, p: PreparedView)
    requires v.epoch >= v.limit || v.epoch == MAX_EPOCH,
    ensures !enabled(v, p), step(v, Event::Publish(p)) == v,
{ }

pub proof fn captured_checkouts_keep_their_exact_immutable_source(v: View)
    requires valid(v),
    ensures checkout_valid(capture(v)), capture(v).epoch == v.epoch,
        capture(v).source == v.source, capture(v).certificate == v.certificate,
{ reveal(valid); }

pub proof fn two_preparations_from_one_revision_cannot_both_publish(v: View, first: PreparedView, second: PreparedView)
    requires enabled(v, first), second.epoch == v.epoch,
    ensures !enabled(publish_step(v, first), second),
        step(publish_step(v, first), Event::Publish(second)) == publish_step(v, first),
{
    invariant_preserved_by_publication(v, first);
}

pub proof fn restoring_old_bytes_cannot_resurrect_a_stale_preparation(current: View, old: PreparedView)
    requires old.epoch < current.epoch, current.source == old.before,
    ensures !enabled(current, old), step(current, Event::Publish(old)) == current,
{ }

pub open spec fn execution(states: Seq<View>, events: Seq<Event>) -> bool {
    &&& states.len() == events.len() + 1
    &&& valid(states[0])
    &&& (forall|i: int| 0 <= i < events.len() ==>
        states[i + 1] == step(states[i], #[trigger] events[i]))
}
pub open spec fn accepted_count(states: Seq<View>, events: Seq<Event>) -> nat
    decreases events.len(),
{
    if events.len() == 0 { 0nat } else {
        accepted_count(states.drop_last(), events.drop_last())
            + if accepted(states[events.len() as int - 1], events.last()) { 1nat } else { 0nat }
    }
}

proof fn execution_prefix(states: Seq<View>, events: Seq<Event>)
    requires execution(states, events), events.len() > 0,
    ensures execution(states.drop_last(), events.drop_last()),
{
    assert forall|i: int| 0 <= i < events.drop_last().len() implies
        (#[trigger] states.drop_last()[i + 1]) == step(states.drop_last()[i], events.drop_last()[i]) by {
        assert(states[i + 1] == step(states[i], events[i]));
    }
}

// History induction treats validated images as opaque certificates. These
// small boundaries expose only sequence geometry and one transition at a time.
proof fn execution_basics(states: Seq<View>, events: Seq<Event>)
    requires execution(states, events),
    ensures states.len() == events.len() + 1, valid(states[0]),
{ }

proof fn execution_last_transition(states: Seq<View>, events: Seq<Event>)
    requires execution(states, events), events.len() > 0,
    ensures states.last() == step(states.drop_last().last(), events.last()),
{
    let i = events.len() as int - 1;
    assert(states[i + 1] == step(states[i], events[i]));
}

proof fn no_events_have_zero_accepted_count(states: Seq<View>, events: Seq<Event>)
    requires events.len() == 0,
    ensures accepted_count(states, events) == 0,
{ reveal(accepted_count); }

proof fn accepted_count_last_transition(states: Seq<View>, events: Seq<Event>)
    requires states.len() == events.len() + 1, events.len() > 0,
    ensures accepted_count(states, events)
        == accepted_count(states.drop_last(), events.drop_last())
            + if accepted(states.drop_last().last(), events.last()) { 1nat } else { 0nat },
{
    hide(accepted);
    reveal(accepted_count);
}

proof fn valid_prefix_and_last_cover_the_whole_history(states: Seq<View>)
    requires states.len() > 0, valid(states.last()),
        forall|i: int| 0 <= i < states.drop_last().len() ==> #[trigger] valid(states.drop_last()[i]),
    ensures forall|i: int| 0 <= i < states.len() ==> #[trigger] valid(states[i]),
{
    assert forall|i: int| 0 <= i < states.len() implies #[trigger] valid(states[i]) by {
        if i < states.drop_last().len() {
            assert(states.drop_last()[i] == states[i]);
            assert(valid(states.drop_last()[i]));
        } else { assert(i == states.len() - 1 && states[i] == states.last()); }
    }
}

pub proof fn every_finite_interleaving_preserves_admission_and_the_publication_count(states: Seq<View>, events: Seq<Event>)
    requires execution(states, events),
    ensures valid(states.last()),
        states.last().limit == states[0].limit,
        states.last().source.len() == states[0].source.len(),
        states.last().epoch as nat == states[0].epoch as nat + accepted_count(states, events),
        (forall|i: int| 0 <= i < states.len() ==> #[trigger] valid(states[i])),
    decreases events.len(),
{
    hide(step); hide(accepted); hide(execution); hide(accepted_count);
    execution_basics(states, events);
    if events.len() == 0 {
        assert(states.len() == 1 && states.last() == states[0]);
        no_events_have_zero_accepted_count(states, events);
        assert forall|i: int| 0 <= i < states.len() implies #[trigger] valid(states[i]) by {
            assert(i == 0);
        }
    } else {
        execution_prefix(states, events);
        let prefix = states.drop_last(); let prior = events.drop_last();
        every_finite_interleaving_preserves_admission_and_the_publication_count(prefix, prior);
        let before = prefix.last(); let event = events.last();
        execution_last_transition(states, events);
        every_event_preserves_the_current_namespace(before, event);
        accepted_count_last_transition(states, events);
        valid_prefix_and_last_cover_the_whole_history(states);
        assert(prefix[0] == states[0]);
    }
}

proof fn ordered_epochs(states: Seq<View>, events: Seq<Event>, first: int, last: int)
    requires execution(states, events), 0 <= first <= last < states.len(),
        forall|i: int| 0 <= i < states.len() ==> #[trigger] valid(states[i]),
    ensures states[first].epoch <= states[last].epoch,
    decreases last - first,
{
    if first < last {
        ordered_epochs(states, events, first, last - 1);
        every_event_preserves_the_current_namespace(states[last - 1], events[last - 1]);
        assert(states[last] == step(states[last - 1], events[last - 1]));
    }
}

pub proof fn accepted_publications_have_strictly_ordered_distinct_revisions(states: Seq<View>, events: Seq<Event>, first: int, last: int)
    requires execution(states, events), 0 <= first < last < events.len(),
        accepted(states[first], events[first]), accepted(states[last], events[last]),
    ensures states[first].epoch < states[last].epoch,
        states[first + 1].epoch < states[last + 1].epoch,
{
    every_finite_interleaving_preserves_admission_and_the_publication_count(states, events);
    every_event_preserves_the_current_namespace(states[first], events[first]);
    every_event_preserves_the_current_namespace(states[last], events[last]);
    ordered_epochs(states, events, first + 1, last);
    assert(states[first + 1] == step(states[first], events[first]));
    assert(states[last + 1] == step(states[last], events[last]));
}

pub proof fn publication_order_is_the_exact_linearization_order(states: Seq<View>, events: Seq<Event>, index: int)
    requires execution(states, events), 0 <= index < events.len(),
    ensures match events[index] {
        Event::Capture => states[index + 1] == states[index],
        Event::Publish(p) => if accepted(states[index], events[index]) {
            states[index + 1].source == p.after && states[index + 1].certificate == p.after_certificate
                && states[index + 1].epoch as nat == states[index].epoch as nat + 1
        } else { states[index + 1] == states[index] },
    },
{
    every_finite_interleaving_preserves_admission_and_the_publication_count(states, events);
    every_event_preserves_the_current_namespace(states[index], events[index]);
    assert(states[index + 1] == step(states[index], events[index]));
}

pub proof fn a_checkout_from_any_history_prefix_remains_a_certified_read(states: Seq<View>, events: Seq<Event>, index: int)
    requires execution(states, events), 0 <= index < states.len(),
    ensures checkout_valid(capture(states[index])),
        capture(states[index]).source == states[index].source,
        capture(states[index]).certificate == states[index].certificate,
{
    every_finite_interleaving_preserves_admission_and_the_publication_count(states, events);
    captured_checkouts_keep_their_exact_immutable_source(states[index]);
}

proof fn enabled_publication_has_valid_inputs(v: View, p: PreparedView)
    requires enabled(v, p),
    ensures valid(v), prepared_valid(p),
{ }

proof fn publish_event_refines_its_enabling_predicate(v: View, p: PreparedView)
    ensures accepted(v, Event::Publish(p)) == enabled(v, p),
        step(v, Event::Publish(p)) == if enabled(v, p) { publish_step(v, p) } else { v },
{
    hide(enabled); hide(publish_step);
}

// Name the finite sequences as parameters before constructing a quantifier;
// an SMT trigger must not contain the literal sequence constructor.
proof fn two_transition_sequences_form_an_execution(states: Seq<View>, events: Seq<Event>)
    requires states.len() == 3, events.len() == 2, valid(states[0]),
        states[1] == step(states[0], events[0]), states[2] == step(states[1], events[1]),
    ensures execution(states, events),
{
    hide(step);
    assert forall|i: int| 0 <= i < events.len() implies
        states[i + 1] == step(states[i], #[trigger] events[i]) by {
        if i == 0 { } else { assert(i == 1); }
    }
}

proof fn two_steps_form_an_execution(first: View, middle: View, last: View, left: Event, right: Event)
    requires valid(first), middle == step(first, left), last == step(middle, right),
    ensures execution(seq![first, middle, last], seq![left, right]),
{
    hide(step); hide(execution);
    two_transition_sequences_form_an_execution(seq![first, middle, last], seq![left, right]);
}

proof fn two_events_with_one_success_have_one_accepted_count(first: View, middle: View, last: View, left: Event, right: Event)
    requires accepted(first, left), !accepted(middle, right),
    ensures accepted_count(seq![first, middle, last], seq![left, right]) == 1,
{
    hide(accepted);
    reveal_with_fuel(accepted_count, 3);
    assert(accepted_count(seq![first, middle, last], seq![left, right])
        == accepted_count(seq![first, middle], seq![left]));
    assert(accepted_count(seq![first, middle], seq![left])
        == accepted_count(seq![first], Seq::<Event>::empty()) + 1);
    assert(accepted_count(seq![first], Seq::<Event>::empty()) == 0);
}

pub proof fn an_admitted_preparation_has_a_successful_publication_then_a_stale_retry(v: View, first: PreparedView, second: PreparedView)
    requires enabled(v, first), prepared_valid(second), second.epoch == v.epoch, second.before == v.source,
    ensures {
        let published = publish_step(v, first);
        execution(seq![v, published, published], seq![Event::Publish(first), Event::Publish(second)])
            && accepted(v, Event::Publish(first)) && !accepted(published, Event::Publish(second))
            && valid(published) && published.source == first.after
            && accepted_count(seq![v, published, published], seq![Event::Publish(first), Event::Publish(second)]) == 1
    },
{
    hide(step); hide(accepted); hide(execution); hide(accepted_count);
    hide(enabled); hide(publish_step);
    enabled_publication_has_valid_inputs(v, first);
    invariant_preserved_by_publication(v, first);
    two_preparations_from_one_revision_cannot_both_publish(v, first, second);
    let published = publish_step(v, first);
    publish_event_refines_its_enabling_predicate(v, first);
    publish_event_refines_its_enabling_predicate(published, second);
    two_steps_form_an_execution(v, published, published, Event::Publish(first), Event::Publish(second));
    two_events_with_one_success_have_one_accepted_count(v, published, published, Event::Publish(first), Event::Publish(second));
}

}
