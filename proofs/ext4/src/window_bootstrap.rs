// SPDX-License-Identifier: MPL-2.0

//! Fresh primary/GDT/inode-8 discovery from every admitted concurrent window
//! persistence cut. Capturing these bytes requires a reset/quiescent device.

use vstd::prelude::*;
use crate::{allocation, bootstrap, bootstrap_frame, bootstrap_identity, directory_index, disk_image,
    inode_table, journal_view, journal_window::{self as window, Operation, WindowView},
    journal_window_device as device, journal_window_media::{self as media, Media},
    namespace, replay_refinement::Disk, window_admission::{self as admission, AdmissionView},
    window_prefix, window_provenance as provenance, window_snapshot};

verus! {

pub open spec fn initial_map(a: AdmissionView) -> Disk { disk_image::initial_disk(a.boot.source, a.boot.blocks) }
pub open spec fn cut_source(a: AdmissionView, v: WindowView, m: Media) -> Seq<u8> {
    disk_image::flat_bytes(media::disk(m, initial_map(a), v), a.boot.source, a.boot.blocks)
}

pub(crate) proof fn admission_facts(a: AdmissionView, v: WindowView)
    requires admission::valid(a, v),
    ensures bootstrap::valid(a.boot), window::valid(v), a.boot.layout == v.layout,
        a.boot.blocks == v.layout.fs_blocks, a.boot.blocks > 2, a.boot.blocks as nat * 4096 <= a.boot.source.len(),
        journal_view::geometry(v.layout),
        a.boot.ipg >= 16, a.boot.inodes >= 11,
        a.boot.source.len() == v.partition_bytes, a.boot.layout.start > 1,
        a.prefixes.len() == v.txs.len() + 1, 0 < a.prefixes.len(), a.boot.table < a.boot.blocks,
        v.initial_journal == bootstrap::journal_bytes(a.boot), v.initial_primary == a.boot.source.subrange(0, 4096),
{
    hide(crate::crc::fold);
    reveal(admission::valid);
    reveal(bootstrap::valid);
    window::a_window_retains_its_geometry_and_bounded_counts(v);
}

pub proof fn each_admitted_prefix_has_a_complete_filesystem_and_the_same_fresh_locator(a: AdmissionView, v: WindowView, k: int)
    requires admission::valid(a, v), 0 <= k < a.prefixes.len(),
    ensures namespace::valid(a.prefixes[k]), allocation::valid(a.prefixes[k].index.volume),
        a.prefixes[k].index.volume.journal == v.layout,
        a.prefixes[k].index.volume.index.source == window_prefix::prefix(a.boot.source, v, k as nat),
        bootstrap_identity::preserved(a.boot, a.prefixes[k].index.volume.index.source),
        bootstrap::admissible(a.prefixes[k].index.volume.index.source),
        bootstrap_frame::same_locator_geometry(a.boot, bootstrap::projection(a.prefixes[k].index.volume.index.source)),
{
    hide(crate::crc::fold);
    reveal(admission::valid);
    assert(admission::certified(a.boot, a.prefixes[k], window_prefix::prefix(a.boot.source, v, k as nat)));
    reveal(namespace::valid);
    reveal(directory_index::valid);
    bootstrap_frame::a_bootstrap_preserving_allocation_image_has_an_admissible_journal_locator(a.boot, a.prefixes[k].index.volume);
}

pub proof fn an_admitted_source_initializes_the_exact_window_device_context(a: AdmissionView, v: WindowView)
    requires admission::valid(a, v),
    ensures provenance::context(initial_map(a), v),
{
    hide(crate::crc::fold);
    admission_facts(a, v);
    disk_image::a_flat_source_has_the_exact_mapped_journal(a.boot.source, a.boot.layout);
    disk_image::initial_block_map_has_the_exact_source_bytes(a.boot.source, a.boot.blocks, 0);
    assert forall|op: Operation| device::legal(op, window::counts(v)) implies #[trigger] initial_map(a).dom().contains(media::address(v, op)) by {
        assert(window::operation_valid(op, v));
        window::every_window_command_is_partition_bounded(v, op);
        disk_image::initial_disk_addresses_are_exactly_the_filesystem_range(a.boot.source, a.boot.blocks, media::address(v, op));
    }
}

pub open spec fn block_prefix(m: Media, v: WindowView, block: u32) -> Option<nat> {
    match provenance::last_at(m.writes, m.ledger.stable, v, block, m.writes.len()) {
        Some(Operation::Dirty) => Some(0nat), Some(Operation::Home(t, _)) => Some(t as nat + 1), _ => None,
    }
}

pub open spec fn variant(a: AdmissionView, prefix: Option<nat>) -> Seq<u8> {
    match prefix { Some(k) => a.prefixes[k as int].index.volume.index.source, None => a.boot.source }
}

pub proof fn each_non_journal_cut_block_is_one_complete_admitted_variant(a: AdmissionView, v: WindowView, m: Media, block: u32)
    requires admission::valid(a, v), media::inv(m, v), block < a.boot.blocks,
        !(v.layout.start <= block < v.layout.start as nat + v.layout.journal_blocks),
    ensures cut_source(a, v, m).len() == a.boot.source.len(),
        match block_prefix(m, v, block) { Some(k) => k < a.prefixes.len(), None => true },
        cut_source(a, v, m).subrange(block as int * 4096, (block as int + 1) * 4096)
            == variant(a, block_prefix(m, v, block)).subrange(block as int * 4096, (block as int + 1) * 4096),
{
    hide(crate::crc::fold);
    admission_facts(a, v);
    let initial = initial_map(a);
    let disk = media::disk(m, initial, v);
    disk_image::initial_block_map_has_the_exact_source_bytes(a.boot.source, a.boot.blocks, block);
    provenance::every_block_is_initial_or_its_last_issued_stable_image(m, initial, v, block);
    match provenance::last_at(m.writes, m.ledger.stable, v, block, m.writes.len()) {
        None => {},
        Some(op) => {
            assert(window::operation_valid(op, v));
            window::every_window_command_is_partition_bounded(v, op);
            match op {
                Operation::Dirty => {
                    assert(block == 0);
                    each_admitted_prefix_has_a_complete_filesystem_and_the_same_fresh_locator(a, v, 0);
                    assert(a.prefixes[0].index.volume.index.source == window_prefix::marked(a.boot.source, v));
                    assert(crate::patch_set::valid(seq![crate::transaction::ImageView { block: 0, image: v.dirty }])) by { reveal(crate::patch_set::valid); reveal(window::valid); }
                    crate::patch_set::applying_a_patch_replaces_exactly_its_block(a.boot.source, seq![crate::transaction::ImageView { block: 0, image: v.dirty }], 0);
                    crate::patch_set::a_single_patch_selects_exactly_its_target(crate::transaction::ImageView { block: 0, image: v.dirty }, 0);
                },
                Operation::Home(t, k) => {
                    window::window_entry(v, t as int); reveal(window::positioned_valid);
                    each_admitted_prefix_has_a_complete_filesystem_and_the_same_fresh_locator(a, v, t as int + 1);
                    window_prefix::a_checkpoint_home_image_is_exactly_its_complete_prefix_block(a.boot.source, v, t as int, k as int);
                },
                Operation::Descriptor(_) | Operation::Payload(_, _) | Operation::Commit(_) => { media::log_location(v, op); },
                Operation::Activate | Operation::Tail(_) => { assert(block == v.layout.start); },
                _ => {},
            }
        },
    }
    assert(disk[block].len() == 4096);
    disk_image::a_flat_projection_reads_every_complete_present_block(disk, a.boot.source, a.boot.blocks, block);
}

#[verifier::rlimit(30)]
proof fn the_journal_inode_table_is_separate_from_primary_descriptors_and_the_entire_journal(a: AdmissionView, v: WindowView)
    requires admission::valid(a, v),
    ensures a.boot.table > 1, !(v.layout.start <= a.boot.table < v.layout.start as nat + v.layout.journal_blocks),
{
    hide(crate::crc::fold);
    admission_facts(a, v);
    each_admitted_prefix_has_a_complete_filesystem_and_the_same_fresh_locator(a, v, 0);
    let volume = a.prefixes[0].index.volume;
    bootstrap_frame::a_bootstrap_preserving_allocation_image_has_an_admissible_journal_locator(a.boot, volume);
    allocation::every_inode_table_position_has_a_metadata_role(volume, 8);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(7, volume.index.ipg as int, 0, 7);
    let table = volume.index.groups[0].inode_table;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(table as int * 4096 + 1792, 4096, table as int, 1792);
    assert(inode_table::start(volume.index, 8) / 4096 == table == a.boot.table);
    allocation::the_primary_superblock_and_descriptor_have_reserved_roles(volume);
    if v.layout.start <= a.boot.table < v.layout.start as nat + v.layout.journal_blocks {
        allocation::the_internal_journal_has_only_journal_roles(volume, a.boot.table);
    }
}

proof fn an_admitted_variant_keeps_a_valid_bootstrap(a: AdmissionView, v: WindowView, k: Option<nat>)
    requires admission::valid(a, v), match k { Some(k) => k < a.prefixes.len(), None => true },
    ensures bootstrap::admissible(variant(a, k)), bootstrap_frame::same_locator_geometry(a.boot, bootstrap::projection(variant(a, k))),
        bootstrap_identity::primary_fixed(a.boot.source.subrange(0, 4096), variant(a, k).subrange(0, 4096)),
        variant(a, k).subrange(a.boot.table as int * 4096 + 1792, a.boot.table as int * 4096 + 2048) == bootstrap::journal_inode(a.boot),
{
    hide(crate::crc::fold);
    admission_facts(a, v);
    match k {
        Some(k) => { each_admitted_prefix_has_a_complete_filesystem_and_the_same_fresh_locator(a, v, k as int); },
        None => {
            bootstrap::every_valid_bootstrap_is_the_unique_source_projection(a.boot);
            assert(a.boot.source.len() >= 8192) by { reveal(bootstrap::valid); }
        },
    }
}

pub proof fn every_admitted_window_cut_has_complete_fresh_bootstrap_discovery(a: AdmissionView, v: WindowView, m: Media)
    requires admission::valid(a, v), media::inv(m, v),
    ensures bootstrap::admissible(cut_source(a, v, m)),
        bootstrap_frame::same_locator_geometry(a.boot, bootstrap::projection(cut_source(a, v, m))),
{
    hide(crate::crc::fold);
    admission_facts(a, v);
    let source = cut_source(a, v, m);
    each_non_journal_cut_block_is_one_complete_admitted_variant(a, v, m, 0);
    each_non_journal_cut_block_is_one_complete_admitted_variant(a, v, m, 1);
    the_journal_inode_table_is_separate_from_primary_descriptors_and_the_entire_journal(a, v);
    each_non_journal_cut_block_is_one_complete_admitted_variant(a, v, m, a.boot.table);
    an_admitted_variant_keeps_a_valid_bootstrap(a, v, block_prefix(m, v, 0));
    an_admitted_variant_keeps_a_valid_bootstrap(a, v, block_prefix(m, v, 1));
    an_admitted_variant_keeps_a_valid_bootstrap(a, v, block_prefix(m, v, a.boot.table));
    let table_source = variant(a, block_prefix(m, v, a.boot.table));
    assert(source.subrange(a.boot.table as int * 4096 + 1792, a.boot.table as int * 4096 + 2048)
        =~= source.subrange(a.boot.table as int * 4096, (a.boot.table as int + 1) * 4096).subrange(1792, 2048));
    assert(table_source.subrange(a.boot.table as int * 4096 + 1792, a.boot.table as int * 4096 + 2048)
        =~= table_source.subrange(a.boot.table as int * 4096, (a.boot.table as int + 1) * 4096).subrange(1792, 2048));
    bootstrap_frame::independently_admitted_bootstrap_blocks_keep_the_same_locator(a.boot,
        bootstrap::projection(variant(a, block_prefix(m, v, 0))), bootstrap::projection(variant(a, block_prefix(m, v, 1))), source);
}

pub proof fn every_finite_admitted_window_interleaving_keeps_fresh_bootstrap_discovery(a: AdmissionView, v: WindowView,
    states: Seq<Media>, events: Seq<device::Event>)
    requires admission::valid(a, v), media::execution(states, events, v), states[0] == media::initial(),
    ensures forall|i: int| 0 <= i < states.len() ==> bootstrap::admissible(#[trigger] cut_source(a, v, states[i]))
        && bootstrap_frame::same_locator_geometry(a.boot, bootstrap::projection(cut_source(a, v, states[i]))),
{
    admission_facts(a, v);
    media::initialization(v);
    media::every_finite_byte_persistence_interleaving_preserves_order(states, events, v);
    assert forall|i: int| 0 <= i < states.len() implies bootstrap::admissible(#[trigger] cut_source(a, v, states[i]))
        && bootstrap_frame::same_locator_geometry(a.boot, bootstrap::projection(cut_source(a, v, states[i]))) by {
        every_admitted_window_cut_has_complete_fresh_bootstrap_discovery(a, v, states[i]);
    }
}

proof fn an_accepted_journal_header_has_the_exact_uuid(journal: Seq<u8>, uuid: Seq<u8>, blocks: u32)
    requires journal.len() >= 1024, crate::journal_superblock::accepted(journal.subrange(0, 1024), uuid, blocks),
    ensures journal.subrange(48, 64) == uuid,
{
    hide(crate::crc::fold);
    assert(crate::journal_superblock::uuid_matches(journal.subrange(0, 1024), uuid));
    assert(uuid.len() == 16);
    let actual = journal.subrange(48, 64);
    assert(actual.len() == uuid.len());
    assert(actual =~= uuid) by {
        assert forall|i: int| 0 <= i < actual.len() implies #[trigger] actual[i] == uuid[i] by {
            assert(journal.subrange(0, 1024)[48 + i] == uuid[i]);
            assert(actual[i] == journal[48 + i]);
        }
    }
}

#[verifier::rlimit(30)]
pub proof fn fresh_bootstrap_scans_the_exact_actual_window_journal(a: AdmissionView, v: WindowView, m: Media, layout: &crate::layout::JournalLayout)
    requires admission::valid(a, v), media::inv(m, v), layout.wf(), layout.view() == v.layout,
    ensures bootstrap::scan_source(bootstrap::projection(cut_source(a, v, m))) == crate::window_recognition::actual_source(m, initial_map(a), v, layout),
        crate::scan_budget::admitted(bootstrap::journal_bytes(bootstrap::projection(cut_source(a, v, m))),
            bootstrap::journal_identity(bootstrap::projection(cut_source(a, v, m))), layout),
{
    hide(crate::crc::fold);
    hide(bootstrap::projection);
    hide(disk_image::flat_bytes);
    hide(crate::journal_superblock::accepted);
    admission_facts(a, v);
    an_admitted_source_initializes_the_exact_window_device_context(a, v);
    every_admitted_window_cut_has_complete_fresh_bootstrap_discovery(a, v, m);
    window_snapshot::every_window_crash_keeps_the_initialized_journal_mapping(m, initial_map(a), v);
    window_snapshot::every_actual_journal_header_retains_its_validated_identity(m, initial_map(a), v);
    disk_image::a_flat_projection_has_the_exact_mapped_journal(media::disk(m, initial_map(a), v), a.boot.source, v.layout);
    let fresh = bootstrap::projection(cut_source(a, v, m));
    let journal = journal_view::snapshot(media::disk(m, initial_map(a), v), v.layout);
    assert(fresh.source == cut_source(a, v, m)) by { reveal(bootstrap::projection); }
    assert(bootstrap::journal_bytes(fresh) == journal);
    an_accepted_journal_header_has_the_exact_uuid(journal, v.uuid, v.layout.journal_blocks);
    bootstrap::a_valid_bootstrap_uses_its_actual_journal_identity_seed(fresh);
    crate::window_recognition::every_window_crash_snapshot_is_admitted_by_scan(m, initial_map(a), v, layout);
}

/// The physical restart source, not retained caller geometry, determines the
/// canonical scan input in the full filesystem recovery admission certificate.
pub proof fn an_admitted_cold_recovery_uses_fresh_discovery_and_validates_its_complete_result(a: AdmissionView, v: WindowView,
    m: Media, layout: &crate::layout::JournalLayout, recovery: &crate::recovery_admission::CheckedRecovery<'_, '_>)
    requires admission::valid(a, v), media::inv(m, v), layout.wf(), layout.view() == v.layout,
        recovery.wf(), recovery.source_view() == cut_source(a, v, m),
    ensures recovery.owner().scan_result().certificate(crate::window_recognition::actual_source(m, initial_map(a), v, layout)),
        recovery.owner().scan_result().maximal(crate::window_recognition::actual_source(m, initial_map(a), v, layout)),
        namespace::valid(recovery.view().after), recovery.view().before == bootstrap::projection(cut_source(a, v, m)),
        recovery.view().after.index.volume.index.source == crate::recovery_admission::final_source(cut_source(a, v, m), recovery.view().homes, recovery.owner()),
        bootstrap_identity::preserved(recovery.view().before, recovery.view().after.index.volume.index.source),
{
    hide(crate::crc::fold);
    fresh_bootstrap_scans_the_exact_actual_window_journal(a, v, m, layout);
    reveal(crate::recovery_admission::valid);
    bootstrap::every_valid_bootstrap_is_the_unique_source_projection(recovery.view().before);
}

pub proof fn every_crash_during_admitted_cold_recovery_keeps_the_original_window_locator(a: AdmissionView, v: WindowView,
    m: Media, recovery: &crate::recovery_admission::CheckedRecovery<'_, '_>, attempt: crate::recovery_device::Machine)
    requires admission::valid(a, v), media::inv(m, v), recovery.wf(), recovery.source_view() == cut_source(a, v, m),
        crate::recovery_device::inv(attempt, crate::recovery_crash_image::initial_map(recovery.view()), recovery.owner().plan(), recovery.owner().journal_block(), recovery.owner().tail()),
    ensures bootstrap::admissible(crate::recovery_bootstrap::cut_source(recovery.view(), attempt)),
        bootstrap_frame::same_locator_geometry(a.boot, bootstrap::projection(crate::recovery_bootstrap::cut_source(recovery.view(), attempt))),
{
    hide(crate::crc::fold);
    every_admitted_window_cut_has_complete_fresh_bootstrap_discovery(a, v, m);
    assert(bootstrap::valid(recovery.view().before) && recovery.view().before.source == cut_source(a, v, m)) by { reveal(crate::recovery_admission::valid); }
    bootstrap::every_valid_bootstrap_is_the_unique_source_projection(recovery.view().before);
    crate::recovery_bootstrap::every_admitted_recovery_cut_has_an_admissible_fresh_bootstrap(recovery.view(), recovery.owner(), attempt);
}

pub proof fn successful_admitted_cold_recovery_has_the_exact_complete_filesystem_image(a: AdmissionView, v: WindowView,
    m: Media, layout: &crate::layout::JournalLayout, recovery: &crate::recovery_admission::CheckedRecovery<'_, '_>, machine: crate::recovery_device::Machine)
    requires admission::valid(a, v), media::inv(m, v), layout.wf(), layout.view() == v.layout,
        recovery.wf(), recovery.source_view() == cut_source(a, v, m),
        crate::recovery_device::inv(machine, disk_image::initial_disk(cut_source(a, v, m), a.boot.blocks),
            recovery.owner().plan(), recovery.owner().journal_block(), recovery.owner().tail()),
        machine.io.phase == 4, !machine.io.pending, !machine.io.faulted,
    ensures disk_image::flat_bytes(machine.stable, cut_source(a, v, m), a.boot.blocks) == recovery.view().after.index.volume.index.source,
        namespace::valid(recovery.view().after),
        recovery.owner().scan_result().maximal(crate::window_recognition::actual_source(m, initial_map(a), v, layout)),
        forall|block: u32| !#[trigger] crate::recovery_device::enabled(machine, crate::recovery_device::Event::Persist(block)),
{
    hide(crate::crc::fold);
    every_admitted_window_cut_has_complete_fresh_bootstrap_discovery(a, v, m);
    an_admitted_cold_recovery_uses_fresh_discovery_and_validates_its_complete_result(a, v, m, layout, recovery);
    crate::recovery_image::successful_recovery_is_the_complete_validated_filesystem_image(recovery.view(), recovery.owner(), machine);
}

}
