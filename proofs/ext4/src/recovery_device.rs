// SPDX-License-Identifier: MPL-2.0

//! Recovery refinement under an explicit 4096-byte failure-atomic device
//! contract. Persistence can precede completion or follow abort. A successful
//! flush persists the domain's earlier writes. No Asterinas driver is inferred
//! to satisfy this contract from its addressing sector size.

use vstd::{assert_maps_equal, prelude::*};
use crate::{recovery_io::{self, State}, replay::{self, ReplayPlan}, replay_refinement::{self, Disk}};

verus! {

pub struct Machine { pub io: State, pub stable: Disk, pub cache: Disk }
pub enum Event { Issue, Complete(bool), Persist(u32), Abort }

pub open spec fn target(plan: &ReplayPlan, block: u32) -> bool {
    exists|p: int| 0 <= p < plan.selection().len() && (#[trigger] plan.log()[plan.selection()[p] as int]).block == block
}

pub open spec fn final_home(before: Disk, plan: &ReplayPlan) -> Disk {
    replay_refinement::selected(before, plan.log(), plan.selection())
}

pub open spec fn homes_equal(stable: Disk, before: Disk, plan: &ReplayPlan) -> bool {
    forall|block: u32| #[trigger] target(plan, block) ==> stable[block] == final_home(before, plan)[block]
}

pub open spec fn flush(stable: Disk, cache: Disk) -> Disk {
    Map::new(stable.dom(), |block: u32| if cache.dom().contains(block) { cache[block] } else { stable[block] })
}

pub open spec fn inv(m: Machine, before: Disk, plan: &ReplayPlan, journal: u32, tail: Seq<u8>) -> bool {
    &&& plan.refines() && replay_refinement::all_targets_exist(before, plan.log())
    &&& before.dom().contains(journal) && !target(plan, journal) && tail.len() == 4096
    &&& recovery_io::wf(m.io, plan.selection().len())
    &&& m.stable.dom() == before.dom() && m.cache.dom().subset_of(before.dom())
    &&& (forall|block: u32| #[trigger] m.cache.dom().contains(block) ==>
        (if block == journal { m.cache[block] == tail && m.io.phase >= 2 }
         else { target(plan, block) && m.cache[block] == final_home(before, plan)[block] }))
    &&& (forall|block: u32| before.dom().contains(block) && !target(plan, block) && block != journal
        ==> #[trigger] m.stable[block] == before[block])
    &&& (forall|block: u32| #[trigger] target(plan, block) ==>
        m.stable[block] == before[block] || m.stable[block] == final_home(before, plan)[block])
    &&& (m.stable[journal] == before[journal] || m.stable[journal] == tail)
    &&& (m.io.phase < 2 ==> m.stable[journal] == before[journal] && !m.cache.dom().contains(journal))
    &&& (m.io.phase >= 2 ==> homes_equal(m.stable, before, plan)
        && m.cache.dom().subset_of(set![journal]))
    &&& (m.io.phase >= 3 || (m.io.phase == 2 && m.io.pending)
        ==> m.stable[journal] == tail || m.cache.dom().contains(journal) && m.cache[journal] == tail)
    &&& (m.io.phase == 4 ==> m.stable[journal] == tail && m.cache.dom().is_empty())
    &&& (forall|p: int| 0 <= p < plan.selection().len()
        && (p < m.io.cursor || (m.io.phase == 0 && m.io.pending && p == m.io.cursor)) ==>
        {
            let block = (#[trigger] plan.log()[plan.selection()[p] as int]).block;
            m.stable[block] == final_home(before, plan)[block]
                || m.cache.dom().contains(block) && m.cache[block] == final_home(before, plan)[block]
        })
}

pub open spec fn initial(before: Disk, plan: &ReplayPlan) -> Machine {
    Machine { io: State { phase: if plan.selection().len() == 0 { 1 } else { 0 },
        cursor: 0, request: 0, pending: false, faulted: false }, stable: before, cache: Map::empty() }
}

pub open spec fn enabled(m: Machine, event: Event) -> bool {
    match event {
        Event::Issue => !m.io.pending && !m.io.faulted && m.io.phase < 4,
        Event::Complete(_) => m.io.pending,
        Event::Persist(block) => m.cache.dom().contains(block),
        Event::Abort => true,
    }
}

pub open spec fn next(m: Machine, event: Event, plan: &ReplayPlan, journal: u32, tail: Seq<u8>) -> Machine {
    match event {
        Event::Issue => {
            let cache = if m.io.phase == 0 {
                let write = plan.log()[plan.selection()[m.io.cursor as int] as int];
                m.cache.insert(write.block, write.image)
            } else if m.io.phase == 2 { m.cache.insert(journal, tail) } else { m.cache };
            Machine { io: recovery_io::started(m.io), cache, ..m }
        },
        Event::Complete(success) => {
            let fence = success && (m.io.phase == 1 || m.io.phase == 3);
            Machine { io: recovery_io::completed(m.io, plan.selection().len(), success),
                stable: if fence { flush(m.stable, m.cache) } else { m.stable },
                cache: if fence { Map::empty() } else { m.cache } }
        },
        Event::Persist(block) => Machine { stable: m.stable.insert(block, m.cache[block]), cache: m.cache.remove(block), ..m },
        Event::Abort => Machine { io: State { faulted: true, ..m.io }, ..m },
    }
}

proof fn index_facts(before: Disk, plan: &ReplayPlan)
    requires plan.refines(), replay_refinement::all_targets_exist(before, plan.log()),
    ensures replay_refinement::indices_valid(plan.log(), plan.selection()),
        final_home(before, plan).dom() == before.dom(),
        forall|p: int| 0 <= p < plan.selection().len() ==>
            final_home(before, plan)[(#[trigger] plan.log()[plan.selection()[p] as int]).block]
                == plan.log()[plan.selection()[p] as int].image,
{
    assert forall|p: int| 0 <= p < plan.selection().len() implies (#[trigger] plan.selection()[p]) < plan.log().len() by {
        assert(replay::latest(plan.log(), plan.revocations(), plan.selection()[p] as int));
    }
    replay_refinement::selected_domain(before, plan.log(), plan.selection());
    assert forall|p: int| 0 <= p < plan.selection().len() implies
        final_home(before, plan)[(#[trigger] plan.log()[plan.selection()[p] as int]).block]
            == plan.log()[plan.selection()[p] as int].image by {
        replay_refinement::selected_target_lookup(before, plan.log(), plan.selection(), p);
    }
}

pub proof fn initialization(before: Disk, plan: &ReplayPlan, journal: u32, tail: Seq<u8>)
    requires plan.refines(), replay_refinement::all_targets_exist(before, plan.log()),
        before.dom().contains(journal), !target(plan, journal), tail.len() == 4096,
    ensures inv(initial(before, plan), before, plan, journal, tail),
{
    index_facts(before, plan);
}

pub proof fn every_event_preserves(m: Machine, event: Event, before: Disk, plan: &ReplayPlan, journal: u32, tail: Seq<u8>)
    requires inv(m, before, plan, journal, tail), enabled(m, event),
    ensures inv(next(m, event, plan, journal, tail), before, plan, journal, tail),
{
    index_facts(before, plan);
    let n = next(m, event, plan, journal, tail);
    match event {
        Event::Issue => {
            if m.io.phase == 0 {
                let p = m.io.cursor as int;
                let block = plan.log()[plan.selection()[p] as int].block;
                assert(target(plan, block));
                assert(before.dom().contains(block));
                assert(final_home(before, plan)[block] == plan.log()[plan.selection()[p] as int].image);
            }
        },
        Event::Complete(success) => {
            if success && (m.io.phase == 1 || m.io.phase == 3) {
                assert forall|block: u32| #[trigger] target(plan, block) implies
                    n.stable[block] == final_home(before, plan)[block] by {
                    let p = choose|p: int| 0 <= p < plan.selection().len()
                        && plan.log()[plan.selection()[p] as int].block == block;
                    assert(p < m.io.cursor);
                    assert(m.stable[block] == final_home(before, plan)[block]
                        || m.cache.dom().contains(block) && m.cache[block] == final_home(before, plan)[block]);
                }
                if m.io.phase == 3 {
                    // The retirement Write has completed before the final Flush.
                    assert(m.stable[journal] == tail || m.cache.dom().contains(journal));
                }
            }
        },
        Event::Persist(block) => { },
        Event::Abort => { },
    }
    assert(recovery_io::wf(n.io, plan.selection().len()));
    assert(n.stable.dom() == before.dom() && n.cache.dom().subset_of(before.dom()));
    assert forall|block: u32| #[trigger] n.cache.dom().contains(block) implies
        (if block == journal { n.cache[block] == tail && n.io.phase >= 2 }
         else { target(plan, block) && n.cache[block] == final_home(before, plan)[block] }) by { }
    assert forall|block: u32| before.dom().contains(block) && !target(plan, block) && block != journal
        implies #[trigger] n.stable[block] == before[block] by { }
    assert forall|block: u32| #[trigger] target(plan, block) implies
        n.stable[block] == before[block] || n.stable[block] == final_home(before, plan)[block] by { }
    assert(n.stable[journal] == before[journal] || n.stable[journal] == tail);
    assert(n.io.phase < 2 ==> n.stable[journal] == before[journal] && !n.cache.dom().contains(journal));
    assert(n.io.phase >= 2 ==> homes_equal(n.stable, before, plan) && n.cache.dom().subset_of(set![journal]));
    assert(n.io.phase >= 3 || (n.io.phase == 2 && n.io.pending)
        ==> n.stable[journal] == tail || n.cache.dom().contains(journal) && n.cache[journal] == tail);
    assert(n.io.phase == 4 ==> n.stable[journal] == tail && n.cache.dom().is_empty());
    assert forall|p: int| 0 <= p < plan.selection().len()
        && (p < n.io.cursor || (n.io.phase == 0 && n.io.pending && p == n.io.cursor)) implies
        {
            let block = (#[trigger] plan.log()[plan.selection()[p] as int]).block;
            n.stable[block] == final_home(before, plan)[block]
                || n.cache.dom().contains(block) && n.cache[block] == final_home(before, plan)[block]
        } by { }
    assert(inv(n, before, plan, journal, tail));
}

pub open spec fn execution(states: Seq<Machine>, events: Seq<Event>, plan: &ReplayPlan, journal: u32, tail: Seq<u8>) -> bool {
    &&& states.len() == events.len() + 1
    &&& (forall|i: int| 0 <= i < events.len() ==> #[trigger] enabled(states[i], events[i]))
    &&& (forall|i: int| 0 <= i < events.len() ==>
        states[i + 1] == #[trigger] next(states[i], events[i], plan, journal, tail))
}

proof fn at_cut(states: Seq<Machine>, events: Seq<Event>, before: Disk,
    plan: &ReplayPlan, journal: u32, tail: Seq<u8>, cut: nat)
    requires execution(states, events, plan, journal, tail),
        inv(states[0], before, plan, journal, tail),
        cut < states.len(),
    ensures inv(states[cut as int], before, plan, journal, tail),
    decreases cut,
{
    if cut > 0 {
        at_cut(states, events, before, plan, journal, tail, (cut - 1) as nat);
        assert(states[cut as int] == next(states[cut as int - 1], events[cut as int - 1], plan, journal, tail));
        every_event_preserves(states[cut as int - 1], events[cut as int - 1], before, plan, journal, tail);
    }
}

pub proof fn every_finite_interleaving(states: Seq<Machine>, events: Seq<Event>, before: Disk,
    plan: &ReplayPlan, journal: u32, tail: Seq<u8>)
    requires execution(states, events, plan, journal, tail),
        inv(states[0], before, plan, journal, tail),
    ensures forall|i: int| 0 <= i < states.len() ==> #[trigger] inv(states[i], before, plan, journal, tail),
{
    assert forall|i: int| 0 <= i < states.len() implies #[trigger] inv(states[i], before, plan, journal, tail) by {
        at_cut(states, events, before, plan, journal, tail, i as nat);
    }
}

pub proof fn cleared_tail_is_safe_at_every_crash_cut(m: Machine, before: Disk, plan: &ReplayPlan,
    journal: u32, tail: Seq<u8>)
    requires inv(m, before, plan, journal, tail), before[journal] != tail, m.stable[journal] == tail,
    ensures homes_equal(m.stable, before, plan),
{
}

pub proof fn success_has_stable_homes_and_tail(m: Machine, before: Disk, plan: &ReplayPlan, journal: u32, tail: Seq<u8>)
    requires inv(m, before, plan, journal, tail), !m.io.faulted, m.io.phase == 4, !m.io.pending,
    ensures homes_equal(m.stable, before, plan), m.stable[journal] == tail, m.cache.dom().is_empty(),
{
}

pub proof fn abort_keeps_all_pending_persistence(m: Machine, before: Disk, plan: &ReplayPlan, journal: u32, tail: Seq<u8>)
    requires inv(m, before, plan, journal, tail),
    ensures next(m, Event::Abort, plan, journal, tail).cache == m.cache,
        next(m, Event::Abort, plan, journal, tail).io.pending == m.io.pending,
        !enabled(next(m, Event::Abort, plan, journal, tail), Event::Issue),
{
}

pub proof fn success_image_equals_linux_redo(m: Machine, before: Disk, plan: &ReplayPlan, journal: u32, tail: Seq<u8>)
    requires inv(m, before, plan, journal, tail), !m.io.faulted, m.io.phase == 4, !m.io.pending,
    ensures m.stable == replay_refinement::chronological(before, plan.log(), plan.revocations()).insert(journal, tail),
{
    index_facts(before, plan);
    assert_maps_equal!(m.stable, final_home(before, plan).insert(journal, tail), block => {
        if before.dom().contains(block) && block != journal {
            if target(plan, block) {
                assert(m.stable[block] == final_home(before, plan)[block]);
            } else {
                assert forall|p: int| 0 <= p < plan.selection().len() implies
                    (#[trigger] plan.log()[plan.selection()[p] as int]).block != block by { }
                replay_refinement::selected_frame(before, plan.log(), plan.selection(), block);
            }
        }
    });
    replay_refinement::executable_selection_equals_chronological_redo(before, plan);
}

pub proof fn uncleared_tail_leaves_a_restartable_partial_replay(m: Machine, before: Disk, plan: &ReplayPlan, journal: u32, tail: Seq<u8>)
    requires inv(m, before, plan, journal, tail), m.stable[journal] == before[journal],
    ensures replay_refinement::replay_partial(before, m.stable, plan.log(), plan.selection()),
        replay_refinement::selected(m.stable, plan.log(), plan.selection())
            == replay_refinement::chronological(before, plan.log(), plan.revocations()),
{
    assert forall|block: u32| before.dom().contains(block)
        && (forall|p: int| 0 <= p < plan.selection().len() ==> (#[trigger] plan.log()[plan.selection()[p] as int]).block != block)
        implies #[trigger] m.stable[block] == before[block] by {
        assert(!target(plan, block));
    }
    replay_refinement::interrupted_replay_is_restartable(before, m.stable, plan);
}

pub proof fn all_non_superblock_journal_records_are_preserved(m: Machine, before: Disk, plan: &ReplayPlan, journal: u32, tail: Seq<u8>, logical: u32)
    requires inv(m, before, plan, journal, tail), journal == plan.layout().view().start,
        1 <= logical < plan.layout().view().journal_blocks,
        before.dom().contains((journal + logical) as u32),
    ensures m.stable[(journal + logical) as u32] == before[(journal + logical) as u32],
{
    let block = (journal + logical) as u32;
    assert(!plan.layout().allowed(block));
    assert(!target(plan, block)) by {
        if target(plan, block) {
            let p = choose|p: int| 0 <= p < plan.selection().len() && plan.log()[plan.selection()[p] as int].block == block;
            assert(replay::latest(plan.log(), plan.revocations(), plan.selection()[p] as int));
            assert(plan.layout().allowed(plan.log()[plan.selection()[p] as int].block));
        }
    }
}

}
