// SPDX-License-Identifier: MPL-2.0

//! Fresh-source bootstrap discovery after admitted recovery-model crash cuts.
//! A reset/quiescent capture and actual driver/CortenMM refinement are separate.

use vstd::prelude::*;
use crate::{allocation, bootstrap, bootstrap_frame, bootstrap_identity, directory_index, disk_image,
    inode_table, namespace, recovery_admission::{self, AdmissionView}, recovery_crash_image,
    recovery_device::{self, Machine}, recovery_image, recovery_io::Recovery};

verus! {

pub open spec fn cut_source(admission: AdmissionView, machine: Machine) -> Seq<u8> {
    disk_image::flat_bytes(machine.stable, admission.before.source, admission.before.blocks)
}

proof fn admission_facts(admission: AdmissionView, engine: &Recovery)
    requires recovery_admission::valid(admission, engine),
    ensures bootstrap::valid(admission.before), allocation::valid(admission.after.index.volume),
        bootstrap_identity::preserved(admission.before, admission.after.index.volume.index.source),
        admission.after.index.volume.journal == admission.before.layout,
        admission.after.index.volume.index.source == recovery_admission::final_source(admission.before.source, admission.homes, engine),
        admission.after.index.volume.index.source.len() == admission.before.source.len(),
        admission.before.blocks as nat * 4096 <= admission.before.source.len(),
        admission.before.layout.fs_blocks == admission.before.blocks, engine.journal_block() == admission.before.layout.start,
        admission.before.layout.start > 1, admission.before.ipg >= 16, admission.before.inodes >= 11,
        1024 <= admission.before.layout.journal_blocks <= 32768,
{
    hide(crate::crc::fold);
    reveal(recovery_admission::valid);
    reveal(namespace::valid);
    reveal(directory_index::valid);
    reveal(bootstrap::valid);
}

#[verifier::rlimit(30)]
pub proof fn each_non_journal_cut_block_has_complete_old_or_validated_redo_bytes(admission: AdmissionView, engine: &Recovery,
    machine: Machine, block: u32)
    requires recovery_admission::valid(admission, engine),
        recovery_device::inv(machine, recovery_crash_image::initial_map(admission), engine.plan(), engine.journal_block(), engine.tail()),
        block < admission.before.blocks, block != engine.journal_block(),
    ensures cut_source(admission, machine).len() == admission.before.source.len(),
        cut_source(admission, machine).subrange(block as int * 4096, (block as int + 1) * 4096).len() == 4096,
        cut_source(admission, machine).subrange(block as int * 4096, (block as int + 1) * 4096) == admission.before.source.subrange(block as int * 4096, (block as int + 1) * 4096)
            || cut_source(admission, machine).subrange(block as int * 4096, (block as int + 1) * 4096)
                == admission.after.index.volume.index.source.subrange(block as int * 4096, (block as int + 1) * 4096),
{
    hide(crate::crc::fold);
    hide(recovery_admission::final_source);
    admission_facts(admission, engine);
    let before = recovery_crash_image::initial_map(admission);
    disk_image::initial_block_map_has_the_exact_source_bytes(admission.before.source, admission.before.blocks, block);
    recovery_image::admitted_shadow_has_exactly_the_complete_redo_and_tail_bytes(admission, engine, block);
    assert(machine.stable[block] == before[block]
        || machine.stable[block] == admission.after.index.volume.index.source.subrange(block as int * 4096, (block as int + 1) * 4096));
    assert(machine.stable[block].len() == 4096);
    disk_image::a_flat_projection_reads_every_complete_present_block(machine.stable, admission.before.source, admission.before.blocks, block);
}

proof fn the_bootstrap_inode_table_cannot_alias_the_journal_superblock(admission: AdmissionView, engine: &Recovery)
    requires recovery_admission::valid(admission, engine),
    ensures admission.before.table != engine.journal_block(),
{
    hide(crate::crc::fold);
    admission_facts(admission, engine);
    let after = admission.after.index.volume;
    bootstrap_frame::a_bootstrap_preserving_allocation_image_has_an_admissible_journal_locator(admission.before, after);
    allocation::every_inode_table_position_has_a_metadata_role(after, 8);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(7, after.index.ipg as int, 0, 7);
    assert((8int - 1) / after.index.ipg as int == 0 && (8int - 1) % after.index.ipg as int == 7);
    let table = after.index.groups[0].inode_table;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(table as int * 4096 + 1792, 4096, table as int, 1792);
    assert(inode_table::start(after.index, 8) / 4096 == table);
    allocation::the_internal_journal_has_only_journal_roles(after, engine.journal_block());
}

#[verifier::rlimit(30)]
pub proof fn every_admitted_recovery_cut_has_an_admissible_fresh_bootstrap(admission: AdmissionView, engine: &Recovery, machine: Machine)
    requires recovery_admission::valid(admission, engine),
        recovery_device::inv(machine, recovery_crash_image::initial_map(admission), engine.plan(), engine.journal_block(), engine.tail()),
    ensures bootstrap::admissible(cut_source(admission, machine)),
        bootstrap_frame::same_locator_geometry(admission.before, bootstrap::projection(cut_source(admission, machine))),
{
    hide(crate::crc::fold);
    hide(recovery_admission::final_source);
    admission_facts(admission, engine);
    let old = admission.before;
    let after = admission.after.index.volume;
    let source = cut_source(admission, machine);
    bootstrap_frame::a_bootstrap_preserving_allocation_image_has_an_admissible_journal_locator(old, after);
    each_non_journal_cut_block_has_complete_old_or_validated_redo_bytes(admission, engine, machine, 0);
    each_non_journal_cut_block_has_complete_old_or_validated_redo_bytes(admission, engine, machine, 1);
    the_bootstrap_inode_table_cannot_alias_the_journal_superblock(admission, engine);
    assert(old.table < old.blocks) by { reveal(bootstrap::valid); }
    each_non_journal_cut_block_has_complete_old_or_validated_redo_bytes(admission, engine, machine, old.table);
    assert(source.subrange(old.table as int * 4096 + 1792, old.table as int * 4096 + 2048) == bootstrap::journal_inode(old)) by {
        assert(source.len() == old.source.len() && old.blocks as nat * 4096 <= source.len());
        assert(source.subrange(old.table as int * 4096 + 1792, old.table as int * 4096 + 2048)
            =~= source.subrange(old.table as int * 4096, (old.table as int + 1) * 4096).subrange(1792, 2048));
        assert(after.index.source.subrange(old.table as int * 4096 + 1792, old.table as int * 4096 + 2048) == bootstrap::journal_inode(old));
    }
    bootstrap_frame::complete_bootstrap_block_mixtures_keep_the_same_admitted_locator(old, bootstrap::projection(after.index.source), source);
}

pub proof fn every_finite_admitted_recovery_trace_keeps_fresh_bootstrap_discovery(admission: AdmissionView, engine: &Recovery,
    states: Seq<Machine>, events: Seq<recovery_device::Event>)
    requires recovery_admission::valid(admission, engine),
        recovery_device::execution(states, events, engine.plan(), engine.journal_block(), engine.tail()),
        states[0] == recovery_device::initial(recovery_crash_image::initial_map(admission), engine.plan()),
    ensures forall|i: int| 0 <= i < states.len() ==> bootstrap::admissible(#[trigger] cut_source(admission, states[i]))
        && bootstrap_frame::same_locator_geometry(admission.before, bootstrap::projection(cut_source(admission, states[i]))),
{
    recovery_image::an_admitted_recovery_has_a_valid_initial_device_model(admission, engine);
    recovery_device::every_finite_interleaving(states, events, recovery_crash_image::initial_map(admission), engine.plan(), engine.journal_block(), engine.tail());
    assert forall|i: int| 0 <= i < states.len() implies bootstrap::admissible(#[trigger] cut_source(admission, states[i]))
        && bootstrap_frame::same_locator_geometry(admission.before, bootstrap::projection(cut_source(admission, states[i]))) by {
        every_admitted_recovery_cut_has_an_admissible_fresh_bootstrap(admission, engine, states[i]);
    }
}

pub proof fn unchanged_tail_cuts_have_the_same_fresh_canonical_scan_source(admission: AdmissionView, engine: &Recovery, machine: Machine)
    requires recovery_admission::valid(admission, engine),
        recovery_device::inv(machine, recovery_crash_image::initial_map(admission), engine.plan(), engine.journal_block(), engine.tail()),
        machine.stable[engine.journal_block()] == recovery_crash_image::initial_map(admission)[engine.journal_block()],
    ensures bootstrap::scan_source(bootstrap::projection(cut_source(admission, machine))) == bootstrap::scan_source(admission.before),
{
    hide(crate::crc::fold);
    admission_facts(admission, engine);
    every_admitted_recovery_cut_has_an_admissible_fresh_bootstrap(admission, engine, machine);
    recovery_crash_image::unchanged_tail_recovery_cuts_keep_the_exact_canonical_journal_input(admission, engine, machine);
    disk_image::a_flat_projection_has_the_exact_mapped_journal(machine.stable, admission.before.source, admission.before.layout);
    let next = bootstrap::projection(cut_source(admission, machine));
    assert(bootstrap::journal_bytes(next) == bootstrap::journal_bytes(admission.before));
    assert(bootstrap::valid(next));
    reveal(bootstrap::valid);
}

}
