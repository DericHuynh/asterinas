// SPDX-License-Identifier: MPL-2.0

//! Actual EA recovered-shadow equality under the atomic-block and flush model.
//! This theorem is conditional on the full repaired-shadow admission certificate.
//! Validator completeness and source/device refinement remain separate.

use vstd::prelude::*;
use crate::{ea_bootstrap, disk_image, ea_namespace, patch_set, ea_recovery_admission::{self, AdmissionView},
    recovery_device::{self, Machine}, recovery_io::{self, Recovery}, recovery_patch, replay::{self, ReplayPlan},
    replay_refinement, transaction::ImageView};

verus! {

pub proof fn an_admitted_recovery_has_a_valid_initial_device_model(admission: AdmissionView, engine: &Recovery)
    requires ea_recovery_admission::valid(admission, engine),
    ensures recovery_device::inv(recovery_device::initial(disk_image::initial_disk(admission.before.source, admission.before.blocks), engine.plan()),
        disk_image::initial_disk(admission.before.source, admission.before.blocks), engine.plan(), engine.journal_block(), engine.tail()),
{
    hide(crate::crc::fold);
    reveal(ea_recovery_admission::valid);
    reveal(ea_bootstrap::valid);
    let before = disk_image::initial_disk(admission.before.source, admission.before.blocks);
    let plan = engine.plan();
    assert forall|i: int| 0 <= i < plan.log().len() implies #[trigger] before.dom().contains(plan.log()[i].block) by {
        assert(plan.layout().allowed(plan.log()[i].block));
        disk_image::initial_disk_addresses_are_exactly_the_filesystem_range(admission.before.source, admission.before.blocks, plan.log()[i].block);
    }
    disk_image::initial_disk_addresses_are_exactly_the_filesystem_range(admission.before.source, admission.before.blocks, engine.journal_block());
    assert forall|p: int| 0 <= p < plan.selection().len() implies
        (#[trigger] plan.log()[plan.selection()[p] as int]).block != engine.journal_block() by {
        assert(replay::latest(plan.log(), plan.revocations(), plan.selection()[p] as int));
        assert(plan.layout().allowed(plan.log()[plan.selection()[p] as int].block));
    }
    recovery_device::initialization(before, plan, engine.journal_block(), engine.tail());
}

proof fn selected_indices_are_valid(plan: &ReplayPlan)
    requires plan.refines(),
    ensures replay_refinement::indices_valid(plan.log(), plan.selection()), replay::unique_targets(plan.log(), plan.selection()),
{
    assert forall|p: int| 0 <= p < plan.selection().len() implies (#[trigger] plan.selection()[p]) < plan.log().len() by {
        assert(replay::latest(plan.log(), plan.revocations(), plan.selection()[p] as int));
    }
}

proof fn admission_shapes(admission: AdmissionView, engine: &Recovery)
    requires ea_recovery_admission::valid(admission, engine),
    ensures admission.before.blocks as nat * 4096 <= admission.before.source.len(),
        patch_set::valid(admission.homes), engine.tail().len() == 4096,
        ea_recovery_admission::recovered_source(admission) == ea_recovery_admission::final_source(admission.before.source, admission.homes, engine),
        ea_recovery_admission::recovered_source(admission).len() == admission.before.source.len(), ea_namespace::valid(admission.after),
{
    reveal(ea_recovery_admission::valid);
    reveal(ea_bootstrap::valid);
}

#[verifier::rlimit(30)]
pub proof fn admitted_shadow_has_exactly_the_complete_redo_and_tail_bytes(admission: AdmissionView, engine: &Recovery, block: u32)
    requires ea_recovery_admission::valid(admission, engine), block < admission.before.blocks,
    ensures ea_recovery_admission::final_source(admission.before.source, admission.homes, engine).subrange(block as int * 4096,
            (block as int + 1) * 4096)
        == recovery_device::final_home(disk_image::initial_disk(admission.before.source, admission.before.blocks), engine.plan())
            .insert(engine.journal_block(), engine.tail())[block],
{
    hide(crate::crc::fold);
    hide(patch_set::apply);
    an_admitted_recovery_has_a_valid_initial_device_model(admission, engine);
    admission_shapes(admission, engine);
    reveal(ea_recovery_admission::valid);
    let source = admission.before.source;
    let before = disk_image::initial_disk(source, admission.before.blocks);
    let plan = engine.plan();
    selected_indices_are_valid(plan);
    disk_image::initial_block_map_has_the_exact_source_bytes(source, admission.before.blocks, block);
    let homes = patch_set::apply(source, admission.homes);
    patch_set::applying_patches_preserves_the_source_length(source, admission.homes);
    patch_set::applying_a_patch_replaces_exactly_its_block(source, admission.homes, block);
    let tail = seq![ImageView { block: engine.journal_block(), image: engine.tail() }];
    assert(patch_set::valid(tail)) by { reveal(patch_set::valid); }
    patch_set::applying_a_patch_replaces_exactly_its_block(homes, tail, block);
    patch_set::a_single_patch_selects_exactly_its_target(tail[0], block as int);
    if block == engine.journal_block() {
    } else if recovery_device::target(plan, block) {
        let p = choose|p: int| 0 <= p < plan.selection().len() && (#[trigger] plan.log()[plan.selection()[p] as int]).block == block;
        replay_refinement::selected_target_lookup(before, plan.log(), plan.selection(), p);
        recovery_patch::each_selected_image_is_the_exact_shadow_patch(plan, admission.homes, p);
    } else {
        assert forall|p: int| 0 <= p < plan.selection().len() implies
            (#[trigger] recovery_patch::image(plan, p)).block != block by { }
        recovery_patch::unselected_targets_have_no_shadow_patch(plan, admission.homes, block);
        replay_refinement::selected_frame(before, plan.log(), plan.selection(), block);
    }
}

pub proof fn admitted_recovery_preserves_extra_partition_bytes(admission: AdmissionView, engine: &Recovery, index: int)
    requires ea_recovery_admission::valid(admission, engine), admission.before.blocks as nat * 4096 <= index < admission.before.source.len(),
    ensures ea_recovery_admission::final_source(admission.before.source, admission.homes, engine)[index] == admission.before.source[index],
{
    reveal(ea_recovery_admission::valid);
    reveal(ea_bootstrap::valid);
    reveal(recovery_patch::matches_prefix);
    let plan = engine.plan();
    let logical = index / 4096;
    assert(logical >= admission.before.blocks);
    assert forall|i: int| 0 <= i < admission.homes.len() implies (#[trigger] admission.homes[i]).block < admission.before.blocks by {
        let p = choose|p: int| 0 <= p < plan.selection().len() && admission.homes[i] == recovery_patch::image(plan, p);
        assert(replay::latest(plan.log(), plan.revocations(), plan.selection()[p] as int));
        assert(plan.layout().allowed(plan.log()[plan.selection()[p] as int].block));
    }
    assert(patch_set::selected(admission.homes, logical).is_none()) by {
        if exists|i: int| 0 <= i < admission.homes.len() && (#[trigger] admission.homes[i]).block as int == logical {
            let i = choose|i: int| 0 <= i < admission.homes.len() && (#[trigger] admission.homes[i]).block as int == logical;
            assert(admission.homes[i].block < admission.before.blocks);
        }
    }
    let tail = seq![ImageView { block: engine.journal_block(), image: engine.tail() }];
    patch_set::a_single_patch_selects_exactly_its_target(tail[0], logical);
}

#[verifier::rlimit(30)]
pub proof fn successful_recovery_is_the_complete_validated_filesystem_image(admission: AdmissionView, engine: &Recovery, machine: Machine)
    requires ea_recovery_admission::valid(admission, engine),
        recovery_device::inv(machine, disk_image::initial_disk(admission.before.source, admission.before.blocks),
            engine.plan(), engine.journal_block(), engine.tail()),
        machine.io.phase == 4, !machine.io.pending, !machine.io.faulted,
    ensures disk_image::flat_bytes(machine.stable, admission.before.source, admission.before.blocks)
            == ea_recovery_admission::recovered_source(admission),
        ea_namespace::valid(admission.after),
        forall|block: u32| !#[trigger] recovery_device::enabled(machine, recovery_device::Event::Persist(block)),
{
    an_admitted_recovery_has_a_valid_initial_device_model(admission, engine);
    admission_shapes(admission, engine);
    let source = admission.before.source;
    let blocks = admission.before.blocks;
    let before = disk_image::initial_disk(source, blocks);
    let plan = engine.plan();
    recovery_device::success_image_equals_linux_redo(machine, before, plan, engine.journal_block(), engine.tail());
    recovery_device::success_has_stable_homes_and_tail(machine, before, plan, engine.journal_block(), engine.tail());
    replay_refinement::executable_selection_equals_chronological_redo(before, plan);
    assert(machine.stable == recovery_device::final_home(before, plan).insert(engine.journal_block(), engine.tail()));
    assert(disk_image::flat_bytes(machine.stable, source, blocks) =~= ea_recovery_admission::recovered_source(admission)) by {
        assert forall|i: int| 0 <= i < source.len() implies
            #[trigger] disk_image::flat_bytes(machine.stable, source, blocks)[i] == ea_recovery_admission::recovered_source(admission)[i] by {
            if i < blocks as nat * 4096 {
                let block = (i / 4096) as u32;
                assert(block as int == i / 4096 && block < blocks);
                disk_image::initial_disk_addresses_are_exactly_the_filesystem_range(source, blocks, block);
                admitted_shadow_has_exactly_the_complete_redo_and_tail_bytes(admission, engine, block);
                assert(machine.stable.dom().contains(block));
                assert(machine.stable[block] == ea_recovery_admission::recovered_source(admission).subrange(block as int * 4096, (block as int + 1) * 4096));
                assert(machine.stable[block].len() == 4096);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, 4096);
                assert(machine.stable[block][i % 4096] == ea_recovery_admission::recovered_source(admission)[i]);
            } else {
                admitted_recovery_preserves_extra_partition_bytes(admission, engine, i);
            }
        }
    }
}


pub proof fn admitted_recovery_preserves_the_actual_primary_bytes(admission: AdmissionView, engine: &Recovery)
    requires ea_recovery_admission::valid(admission, engine),
    ensures ea_recovery_admission::recovered_source(admission).subrange(0, 4096)
        == admission.before.source.subrange(0, 4096),
{
    hide(crate::crc::fold);
    hide(patch_set::apply);
    reveal(ea_recovery_admission::valid);
    reveal(ea_bootstrap::valid);
    reveal(recovery_patch::matches_prefix);
    let source = admission.before.source;
    let plan = engine.plan();
    assert forall|i: int| 0 <= i < admission.homes.len() implies (#[trigger] admission.homes[i]).block != 0 by {
        let p = choose|p: int| 0 <= p < plan.selection().len() && admission.homes[i] == recovery_patch::image(plan, p);
        assert(replay::latest(plan.log(), plan.revocations(), plan.selection()[p] as int));
        assert(plan.log()[plan.selection()[p] as int].block != 0);
    }
    assert(patch_set::selected(admission.homes, 0).is_none()) by {
        if exists|i: int| 0 <= i < admission.homes.len() && (#[trigger] admission.homes[i]).block as int == 0 {
            let i = choose|i: int| 0 <= i < admission.homes.len() && (#[trigger] admission.homes[i]).block as int == 0;
            assert(admission.homes[i].block != 0);
        }
    }
    patch_set::applying_a_patch_replaces_exactly_its_block(source, admission.homes, 0);
    patch_set::applying_patches_preserves_the_source_length(source, admission.homes);
    let tail = seq![ImageView { block: engine.journal_block(), image: engine.tail() }];
    assert(patch_set::valid(tail)) by { reveal(patch_set::valid); }
    patch_set::a_single_patch_selects_exactly_its_target(tail[0], 0);
    patch_set::applying_a_patch_replaces_exactly_its_block(patch_set::apply(source, admission.homes), tail, 0);
}

proof fn prepend_event(before: Machine, event: recovery_device::Event, states: Seq<Machine>, events: Seq<recovery_device::Event>,
    plan: &ReplayPlan, journal: u32, tail: Seq<u8>)
    requires recovery_device::execution(states, events, plan, journal, tail), recovery_device::enabled(before, event),
        states[0] == recovery_device::next(before, event, plan, journal, tail),
    ensures recovery_device::execution(seq![before] + states, seq![event] + events, plan, journal, tail),
{
    let ss = seq![before] + states;
    let ee = seq![event] + events;
    assert forall|i: int| 0 <= i < ee.len() implies #[trigger] recovery_device::enabled(ss[i], ee[i]) by {
        if i > 0 { assert(ss[i] == states[i - 1] && ee[i] == events[i - 1]); }
    }
    assert forall|i: int| 0 <= i < ee.len() implies ss[i + 1] == #[trigger] recovery_device::next(ss[i], ee[i], plan, journal, tail) by {
        if i > 0 { assert(ss[i] == states[i - 1] && ee[i] == events[i - 1] && ss[i + 1] == states[i]); }
    }
}

proof fn finite_successful_execution(machine: Machine, before: replay_refinement::Disk, plan: &ReplayPlan, journal: u32, tail: Seq<u8>)
    -> (r: (Seq<Machine>, Seq<recovery_device::Event>))
    requires recovery_device::inv(machine, before, plan, journal, tail), !machine.io.pending, !machine.io.faulted,
    ensures recovery_device::execution(r.0, r.1, plan, journal, tail), r.0[0] == machine,
        recovery_device::inv(r.0.last(), before, plan, journal, tail), r.0.last().io.phase == 4,
        !r.0.last().io.pending, !r.0.last().io.faulted,
    decreases recovery_io::remaining(machine.io, plan.selection().len()),
{
    if machine.io.phase == 4 { (seq![machine], Seq::empty()) }
    else {
        assert(recovery_device::enabled(machine, recovery_device::Event::Issue));
        let issued = recovery_device::next(machine, recovery_device::Event::Issue, plan, journal, tail);
        recovery_device::every_event_preserves(machine, recovery_device::Event::Issue, before, plan, journal, tail);
        assert(recovery_device::enabled(issued, recovery_device::Event::Complete(true)));
        let completed = recovery_device::next(issued, recovery_device::Event::Complete(true), plan, journal, tail);
        recovery_device::every_event_preserves(issued, recovery_device::Event::Complete(true), before, plan, journal, tail);
        recovery_io::a_successful_pair_makes_progress(machine.io, plan.selection().len());
        let (states, events) = finite_successful_execution(completed, before, plan, journal, tail);
        prepend_event(issued, recovery_device::Event::Complete(true), states, events, plan, journal, tail);
        let ss = seq![issued] + states;
        let ee = seq![recovery_device::Event::Complete(true)] + events;
        prepend_event(machine, recovery_device::Event::Issue, ss, ee, plan, journal, tail);
        (seq![machine] + ss, seq![recovery_device::Event::Issue] + ee)
    }
}

pub proof fn admitted_recovery_images_have_a_finite_successful_execution(admission: AdmissionView, engine: &Recovery)
    -> (r: (Seq<Machine>, Seq<recovery_device::Event>))
    requires ea_recovery_admission::valid(admission, engine),
    ensures recovery_device::execution(r.0, r.1, engine.plan(), engine.journal_block(), engine.tail()),
        r.0[0] == recovery_device::initial(disk_image::initial_disk(admission.before.source, admission.before.blocks), engine.plan()),
        r.0.last().io.phase == 4, !r.0.last().io.pending, !r.0.last().io.faulted,
        disk_image::flat_bytes(r.0.last().stable, admission.before.source, admission.before.blocks)
            == ea_recovery_admission::recovered_source(admission),
        ea_namespace::valid(admission.after),
{
    an_admitted_recovery_has_a_valid_initial_device_model(admission, engine);
    let before = disk_image::initial_disk(admission.before.source, admission.before.blocks);
    let initial = recovery_device::initial(before, engine.plan());
    let (states, events) = finite_successful_execution(initial, before, engine.plan(), engine.journal_block(), engine.tail());
    successful_recovery_is_the_complete_validated_filesystem_image(admission, engine, states.last());
    (states, events)
}

}
