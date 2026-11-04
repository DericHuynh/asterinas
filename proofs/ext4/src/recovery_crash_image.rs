// SPDX-License-Identifier: MPL-2.0

//! Complete filesystem-image repairability at admitted recovery crash cuts.
//! This retains the exact admitted plan; fresh-source admission, physical
//! restart quiescence and runtime/kernel refinement remain separate.

use vstd::{assert_maps_equal, prelude::*};
use crate::{bootstrap, disk_image, journal_view, namespace, recovery_admission::{self, AdmissionView},
    recovery_device::{self, Machine}, recovery_image, recovery_io::Recovery, replay,
    replay_refinement::{self, Disk}};

verus! {

pub open spec fn initial_map(admission: AdmissionView) -> Disk {
    disk_image::initial_disk(admission.before.source, admission.before.blocks)
}

pub open spec fn complete_map(admission: AdmissionView, engine: &Recovery) -> Disk {
    replay_refinement::chronological(initial_map(admission), engine.plan().log(), engine.plan().revocations())
        .insert(engine.journal_block(), engine.tail())
}

pub proof fn the_complete_admitted_redo_map_has_the_validated_filesystem_bytes(admission: AdmissionView, engine: &Recovery)
    requires recovery_admission::valid(admission, engine),
    ensures disk_image::flat_bytes(complete_map(admission, engine), admission.before.source, admission.before.blocks)
        == admission.after.index.volume.index.source, namespace::valid(admission.after),
{
    recovery_image::an_admitted_recovery_has_a_valid_initial_device_model(admission, engine);
    let (states, events) = recovery_image::admitted_recovery_images_have_a_finite_successful_execution(admission, engine);
    recovery_device::every_finite_interleaving(states, events, initial_map(admission), engine.plan(), engine.journal_block(), engine.tail());
    assert(recovery_device::inv(states.last(), initial_map(admission), engine.plan(), engine.journal_block(), engine.tail()));
    recovery_device::success_image_equals_linux_redo(states.last(), initial_map(admission), engine.plan(), engine.journal_block(), engine.tail());
}

pub proof fn an_unchanged_tail_cut_is_repairable_to_the_same_complete_validated_image(admission: AdmissionView, engine: &Recovery, machine: Machine)
    requires recovery_admission::valid(admission, engine),
        recovery_device::inv(machine, initial_map(admission), engine.plan(), engine.journal_block(), engine.tail()),
        machine.stable[engine.journal_block()] == initial_map(admission)[engine.journal_block()],
    ensures disk_image::flat_bytes(replay_refinement::selected(machine.stable, engine.plan().log(), engine.plan().selection())
            .insert(engine.journal_block(), engine.tail()), admission.before.source, admission.before.blocks)
        == admission.after.index.volume.index.source, namespace::valid(admission.after),
{
    recovery_device::uncleared_tail_leaves_a_restartable_partial_replay(machine, initial_map(admission), engine.plan(), engine.journal_block(), engine.tail());
    the_complete_admitted_redo_map_has_the_validated_filesystem_bytes(admission, engine);
}

pub proof fn a_changed_retirement_tail_cut_already_has_the_complete_validated_image(admission: AdmissionView, engine: &Recovery, machine: Machine)
    requires recovery_admission::valid(admission, engine),
        recovery_device::inv(machine, initial_map(admission), engine.plan(), engine.journal_block(), engine.tail()),
        machine.stable[engine.journal_block()] != initial_map(admission)[engine.journal_block()],
    ensures disk_image::flat_bytes(machine.stable, admission.before.source, admission.before.blocks)
        == admission.after.index.volume.index.source, namespace::valid(admission.after),
{
    let before = initial_map(admission);
    let plan = engine.plan();
    let journal = engine.journal_block();
    let tail = engine.tail();
    assert(machine.stable[journal] == tail && before[journal] != tail);
    recovery_device::cleared_tail_is_safe_at_every_crash_cut(machine, before, plan, journal, tail);
    assert forall|p: int| 0 <= p < plan.selection().len() implies (#[trigger] plan.selection()[p]) < plan.log().len() by {
        assert(replay::latest(plan.log(), plan.revocations(), plan.selection()[p] as int));
    }
    replay_refinement::selected_domain(before, plan.log(), plan.selection());
    assert_maps_equal!(machine.stable, recovery_device::final_home(before, plan).insert(journal, tail), block => {
        if before.dom().contains(block) && block != journal {
            if recovery_device::target(plan, block) {
                assert(machine.stable[block] == recovery_device::final_home(before, plan)[block]);
            } else {
                assert forall|p: int| 0 <= p < plan.selection().len() implies
                    (#[trigger] plan.log()[plan.selection()[p] as int]).block != block by { }
                replay_refinement::selected_frame(before, plan.log(), plan.selection(), block);
            }
        }
    });
    replay_refinement::executable_selection_equals_chronological_redo(before, plan);
    assert(machine.stable == complete_map(admission, engine));
    the_complete_admitted_redo_map_has_the_validated_filesystem_bytes(admission, engine);
}

pub proof fn every_admitted_recovery_cut_is_complete_or_repairable_with_its_exact_plan(admission: AdmissionView, engine: &Recovery, machine: Machine)
    requires recovery_admission::valid(admission, engine),
        recovery_device::inv(machine, initial_map(admission), engine.plan(), engine.journal_block(), engine.tail()),
    ensures namespace::valid(admission.after),
        if machine.stable[engine.journal_block()] != initial_map(admission)[engine.journal_block()] {
            disk_image::flat_bytes(machine.stable, admission.before.source, admission.before.blocks)
                == admission.after.index.volume.index.source
        } else {
            disk_image::flat_bytes(replay_refinement::selected(machine.stable, engine.plan().log(), engine.plan().selection())
                .insert(engine.journal_block(), engine.tail()), admission.before.source, admission.before.blocks)
                == admission.after.index.volume.index.source
        },
{
    if machine.stable[engine.journal_block()] != initial_map(admission)[engine.journal_block()] {
        a_changed_retirement_tail_cut_already_has_the_complete_validated_image(admission, engine, machine);
    } else {
        an_unchanged_tail_cut_is_repairable_to_the_same_complete_validated_image(admission, engine, machine);
    }
}

pub proof fn unchanged_tail_recovery_cuts_keep_the_exact_canonical_journal_input(admission: AdmissionView, engine: &Recovery, machine: Machine)
    requires recovery_admission::valid(admission, engine),
        recovery_device::inv(machine, initial_map(admission), engine.plan(), engine.journal_block(), engine.tail()),
        machine.stable[engine.journal_block()] == initial_map(admission)[engine.journal_block()],
    ensures journal_view::mapped(machine.stable, admission.before.layout),
        journal_view::snapshot(machine.stable, admission.before.layout) == bootstrap::journal_bytes(admission.before),
{
    reveal(recovery_admission::valid);
    reveal(bootstrap::valid);
    let before = initial_map(admission);
    let layout = admission.before.layout;
    disk_image::a_flat_source_has_the_exact_mapped_journal(admission.before.source, layout);
    assert forall|logical: u32| logical < layout.journal_blocks implies
        machine.stable.dom().contains((layout.start + logical) as u32)
        && (#[trigger] machine.stable[(layout.start + logical) as u32]) == before[(layout.start + logical) as u32]
        && machine.stable[(layout.start + logical) as u32].len() == 4096 by {
        let block = (layout.start + logical) as u32;
        disk_image::initial_block_map_has_the_exact_source_bytes(admission.before.source, admission.before.blocks, block);
        if logical > 0 {
            recovery_device::all_non_superblock_journal_records_are_preserved(machine, before, engine.plan(), engine.journal_block(), engine.tail(), logical);
        }
    }
    assert(journal_view::mapped(machine.stable, layout));
    journal_view::equal_journal_blocks_have_equal_snapshots(machine.stable, before, layout);
}

pub proof fn every_finite_admitted_recovery_execution_has_complete_or_repairable_crash_cuts(admission: AdmissionView, engine: &Recovery,
    states: Seq<Machine>, events: Seq<recovery_device::Event>)
    requires recovery_admission::valid(admission, engine),
        recovery_device::execution(states, events, engine.plan(), engine.journal_block(), engine.tail()),
        states[0] == recovery_device::initial(initial_map(admission), engine.plan()),
    ensures namespace::valid(admission.after),
        forall|cut: int| 0 <= cut < states.len() ==>
            (if (#[trigger] states[cut]).stable[engine.journal_block()] != initial_map(admission)[engine.journal_block()] {
                disk_image::flat_bytes(states[cut].stable, admission.before.source, admission.before.blocks)
                    == admission.after.index.volume.index.source
            } else {
                disk_image::flat_bytes(replay_refinement::selected(states[cut].stable, engine.plan().log(), engine.plan().selection())
                    .insert(engine.journal_block(), engine.tail()), admission.before.source, admission.before.blocks)
                    == admission.after.index.volume.index.source
            }),
        forall|cut: int| 0 <= cut < states.len()
            && (#[trigger] states[cut]).stable[engine.journal_block()] == initial_map(admission)[engine.journal_block()]
            ==> journal_view::snapshot(states[cut].stable, admission.before.layout) == bootstrap::journal_bytes(admission.before),
{
    recovery_image::an_admitted_recovery_has_a_valid_initial_device_model(admission, engine);
    recovery_device::every_finite_interleaving(states, events, initial_map(admission), engine.plan(), engine.journal_block(), engine.tail());
    the_complete_admitted_redo_map_has_the_validated_filesystem_bytes(admission, engine);
    assert forall|cut: int| 0 <= cut < states.len() implies
        (if (#[trigger] states[cut]).stable[engine.journal_block()] != initial_map(admission)[engine.journal_block()] {
            disk_image::flat_bytes(states[cut].stable, admission.before.source, admission.before.blocks)
                == admission.after.index.volume.index.source
        } else {
            disk_image::flat_bytes(replay_refinement::selected(states[cut].stable, engine.plan().log(), engine.plan().selection())
                .insert(engine.journal_block(), engine.tail()), admission.before.source, admission.before.blocks)
                == admission.after.index.volume.index.source
        }) by {
        assert(recovery_device::inv(states[cut], initial_map(admission), engine.plan(), engine.journal_block(), engine.tail()));
        every_admitted_recovery_cut_is_complete_or_repairable_with_its_exact_plan(admission, engine, states[cut]);
    }
    assert forall|cut: int| 0 <= cut < states.len()
        && (#[trigger] states[cut]).stable[engine.journal_block()] == initial_map(admission)[engine.journal_block()]
        implies journal_view::snapshot(states[cut].stable, admission.before.layout) == bootstrap::journal_bytes(admission.before) by {
        assert(recovery_device::inv(states[cut], initial_map(admission), engine.plan(), engine.journal_block(), engine.tail()));
        unchanged_tail_recovery_cuts_keep_the_exact_canonical_journal_input(admission, engine, states[cut]);
    }
}

}
