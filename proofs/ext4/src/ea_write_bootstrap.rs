// SPDX-License-Identifier: MPL-2.0

//! Fresh raw EA journal discovery at every serialized writer crash cut.
//! The proof uses only complete physical block images and protects the exact
//! inode-8 slice even when another inode in its block is a transaction target.
//! Full repaired-shadow validator completeness remains a separate obligation.

use vstd::prelude::*;
use crate::{bootstrap::BootstrapView, bootstrap_identity, bytes, disk_image,
    ea_allocation, ea_bootstrap, ea_index, ea_namespace::{self, NamespaceView},
    ea_source, ea_write_io, ea_writer_admission::{self, AdmissionView}, group_claims,
    patch_set, transaction::ImageView,
    write_device::{self, Machine}, write_io::{self, Images}, write_media, write_recognition};

verus! {

proof fn locator_facts(v: BootstrapView)
    requires ea_bootstrap::valid(v),
    ensures 8192 <= v.source.len() <= 18446744073709551615, 2 < v.blocks,
        v.blocks as nat * 4096 <= v.source.len(), 0 < v.table < v.blocks,
        v.layout.fs_blocks == v.blocks, v.layout.start > 1,
        1024 <= v.layout.journal_blocks <= 32768,
        v.layout.start as nat + v.layout.journal_blocks <= v.blocks,
        0 < v.ipg <= 32768, v.ipg % 16 == 0, v.inodes >= 11,
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    hide(crate::group::accepted_with_features);
    hide(crate::layout::admitted);
    reveal(ea_bootstrap::valid);
}

proof fn fixed_addresses_keep_each_group_prefix(before: Seq<u8>, after: Seq<u8>, groups: nat, width: nat, number: int)
    requires bootstrap_identity::addresses_fixed(before, after, groups, width), 0 <= number < groups,
    ensures after.subrange(number * width, number * width + 12) == before.subrange(number * width, number * width + 12),
{
}

proof fn preserved_group_zero_addresses_keep_the_journal_inode_coordinate(before: BootstrapView, after: Seq<u8>)
    requires ea_bootstrap::valid(before), bootstrap_identity::preserved(before, after),
    ensures bytes::le32(after, 4104) as nat == before.table,
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    hide(crate::group::accepted_with_features);
    hide(crate::layout::admitted);
    reveal(ea_bootstrap::valid);
    let old_gdt = before.source.subrange(4096, 8192);
    let new_gdt = after.subrange(4096, 8192);
    fixed_addresses_keep_each_group_prefix(old_gdt, new_gdt, (before.blocks as nat + 32767) / 32768,
        crate::superblock::descriptor_bytes(before.source.subrange(1024, 2048)), 0);
    assert(new_gdt.subrange(0, 12) == old_gdt.subrange(0, 12));
    assert forall|i: int| 8 <= i < 12 implies (#[trigger] new_gdt[i]) == old_gdt[i] by {
        assert(new_gdt.subrange(0, 12)[i] == new_gdt[i] && old_gdt.subrange(0, 12)[i] == old_gdt[i]);
    }
    assert(new_gdt.subrange(8, 12) =~= after.subrange(4104, 4108));
    assert(old_gdt.subrange(8, 12) =~= before.source.subrange(4104, 4108));
    assert(bytes::le32(new_gdt, 8) == bytes::le32(old_gdt, 8));
    assert(bytes::le32(after, 4104) == bytes::le32(new_gdt, 8));
    assert(bytes::le32(before.source, 4104) == bytes::le32(old_gdt, 8));
}


proof fn checked_index_locator_inputs(index: ea_index::IndexView)
    requires ea_index::valid(index),
    ensures ea_source::header_valid(index.header), 0 < index.groups.len(),
        ea_source::header_accepted(index.header.source.subrange(1024, 2048), index.header.source.len() as u64),
        8192 <= index.header.source.len() <= 18446744073709551615,
        index.header.blocks as nat == bytes::le32(index.header.source, 1028),
        index.header.inodes as nat == bytes::le32(index.header.source, 1024),
        index.header.ipg as nat == bytes::le32(index.header.source, 1064),
        index.header.seed == crate::superblock::metadata_seed(index.header.source.subrange(1024, 2048)),
        index.header.width as nat == crate::superblock::descriptor_bytes(index.header.source.subrange(1024, 2048)),
        index.header.flex == crate::superblock::flex_bg(index.header.source.subrange(1024, 2048)),
        crate::group::accepted_with_features(index.header.source.subrange(4096,
            4096 + crate::superblock::descriptor_bytes(index.header.source.subrange(1024, 2048)) as int),
            0, index.header.blocks, index.header.ipg, index.header.seed, index.header.flex),
        index.groups[0].descriptor == index.header.source.subrange(4096, 4096 + index.header.width as int),
        index.groups[0].inode_table as nat == bytes::le32(index.header.source, 4104),
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    hide(crate::group::accepted_with_features);
    hide(crate::bitmap::accepted);
    reveal(ea_index::valid);
    reveal(ea_source::header_valid);
    ea_index::every_index_group_retains_its_exact_source_header_and_order(index, 0);
    reveal(ea_index::group_valid);
    let source = index.header.source;
    assert(source.subrange(1024, 2048).subrange(0, 4) =~= source.subrange(1024, 1028));
    assert(source.subrange(1024, 2048).subrange(4, 8) =~= source.subrange(1028, 1032));
    assert(source.subrange(1024, 2048).subrange(40, 44) =~= source.subrange(1064, 1068));
    assert(bytes::le32(index.groups[0].descriptor, 8) == bytes::le32(source, 4104));
}

#[verifier::rlimit(30)]
pub proof fn a_bootstrap_preserving_ea_namespace_has_an_admissible_locator(before: BootstrapView, after: NamespaceView)
    requires ea_bootstrap::valid(before), ea_namespace::valid(after),
        bootstrap_identity::preserved(before, ea_writer_admission::source_of(after)),
    ensures ea_bootstrap::admissible(ea_writer_admission::source_of(after)),
        ea_bootstrap::same_locator_geometry(before, ea_bootstrap::projection(ea_writer_admission::source_of(after))),
        after.allocation.integrity.references.index.header.blocks == before.blocks,
        after.allocation.integrity.references.index.header.inodes == before.inodes,
        after.allocation.integrity.references.index.header.ipg == before.ipg,
        after.allocation.integrity.references.index.header.seed == before.metadata_seed,
        after.allocation.integrity.references.index.groups[0].inode_table == before.table,
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    hide(crate::group::accepted_with_features);
    hide(crate::layout::admitted);
    ea_namespace::allocation_facts(after);
    let index = after.allocation.integrity.references.index;
    let source = index.header.source;
    checked_index_locator_inputs(index);
    ea_bootstrap::primary_source_projection(before, source);
    preserved_group_zero_addresses_keep_the_journal_inode_coordinate(before, source);
    ea_bootstrap::the_same_locator_inputs_give_an_admissible_source(before, source);
}

proof fn ea_transport_target_facts(images: Images)
    requires ea_write_io::valid_images(images),
    ensures write_io::transport_images(images),
        forall|i: int| 0 <= i < images.tx.original.len() ==> (#[trigger] images.tx.original[i]).block >= 2,
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    reveal(ea_write_io::valid_images);
}

proof fn an_actual_source_supplies_the_physical_transport_context(source: Seq<u8>, images: Images)
    requires write_io::transport_images(images),
        images.tx.layout.fs_blocks as nat * 4096 <= source.len(),
        images.initial_primary == source.subrange(0, 4096),
        images.initial_journal == source.subrange(images.tx.layout.start as int * 4096,
            (images.tx.layout.start as int + images.tx.layout.journal_blocks) * 4096),
    ensures write_recognition::transport_context(disk_image::initial_disk(source, images.tx.layout.fs_blocks), images),
{
    hide(crate::crc::fold);
    reveal(write_io::transport_images);
    let disk = disk_image::initial_disk(source, images.tx.layout.fs_blocks);
    disk_image::a_flat_source_has_the_exact_mapped_journal(source, images.tx.layout);
    disk_image::initial_block_map_has_the_exact_source_bytes(source, images.tx.layout.fs_blocks, 0);
    assert forall|k: nat| write_device::is_write(k, images.tx.payloads.len()) implies
        #[trigger] disk.dom().contains(write_media::address(images, k)) by {
        write_media::every_program_write_has_a_complete_bounded_image_transport(images, k);
        disk_image::initial_disk_addresses_are_exactly_the_filesystem_range(source, images.tx.layout.fs_blocks, write_media::address(images, k));
    }
}

pub proof fn an_admitted_source_supplies_the_physical_writer_context(admission: AdmissionView, images: Images)
    requires ea_writer_admission::valid(admission, images),
    ensures write_recognition::transport_context(disk_image::initial_disk(admission.boot.source, images.tx.layout.fs_blocks), images),
        write_recognition::transport_context(disk_image::initial_disk(admission.boot.source, admission.boot.blocks), images),
        images.tx.layout.fs_blocks == admission.boot.blocks,
{
    hide(crate::crc::fold);
    ea_writer_admission::transport_facts(admission, images);
    locator_facts(admission.boot);
    an_actual_source_supplies_the_physical_transport_context(admission.boot.source, images);
}

proof fn the_journal_cannot_alias_the_journal_inode_table(before: BootstrapView, after: NamespaceView)
    requires ea_bootstrap::valid(before), ea_namespace::valid(after),
        bootstrap_identity::preserved(before, ea_writer_admission::source_of(after)),
        after.allocation.journal.layout == before.layout,
    ensures !(before.layout.start <= before.table < before.layout.start as nat + before.layout.journal_blocks),
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    a_bootstrap_preserving_ea_namespace_has_an_admissible_locator(before, after);
    ea_namespace::allocation_facts(after);
    let allocation = after.allocation;
    let index = allocation.integrity.references.index;
    checked_index_locator_inputs(index);
    let record = group_claims::metadata(before.table, (before.ipg / 16) as u32, 3);
    locator_facts(before);
    assert(before.ipg >= 16);
    let claims = group_claims::claims_for_source(index.header.source, index.groups[0].descriptor, 0, index.header.ipg);
    if crate::backup_layout::present(index.header.source.subrange(1024, 2048), 0) {
        assert(claims[3] == record);
    } else { assert(claims[2] == record); }
    assert(claims.contains(record));
    ea_allocation::every_source_reserved_metadata_claim_has_its_exact_final_role(allocation, 0, record, before.table as int);
    if before.layout.start <= before.table < before.layout.start as nat + before.layout.journal_blocks {
        ea_allocation::every_source_journal_block_has_its_final_journal_role(allocation, before.table);
    }
}

pub open spec fn raw_cut_source(old: BootstrapView, images: Images, machine: Machine) -> Seq<u8> {
    disk_image::flat_bytes(
        write_media::disk(machine, disk_image::initial_disk(old.source, old.blocks), images),
        old.source, old.blocks)
}

pub open spec fn cut_source(admission: AdmissionView, images: Images, machine: Machine) -> Seq<u8> {
    raw_cut_source(admission.boot, images, machine)
}

proof fn a_protected_patch_keeps_the_exact_journal_inode(old: BootstrapView, after: Seq<u8>, patches: Seq<ImageView>, index: int)
    requires ea_bootstrap::valid(old), patch_set::valid(patches),
        after == patch_set::apply(old.source, patches), bootstrap_identity::preserved(old, after),
        0 <= index < patches.len(), patches[index].block == old.table,
    ensures patches[index].image.subrange(1792, 2048) == ea_bootstrap::journal_inode(old),
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    hide(patch_set::apply);
    locator_facts(old);
    patch_set::one_target_has_one_image(patches, index);
    patch_set::applying_a_patch_replaces_exactly_its_block(old.source, patches, old.table);
    assert(after.subrange(old.table as int * 4096 + 1792,
        old.table as int * 4096 + 2048) == ea_bootstrap::journal_inode(old));
    assert(after.subrange(old.table as int * 4096,
        (old.table as int + 1) * 4096).subrange(1792, 2048)
        =~= after.subrange(old.table as int * 4096 + 1792,
            old.table as int * 4096 + 2048));
}


proof fn every_home_patch_preserves_the_exact_journal_inode(admission: AdmissionView, images: Images, index: int)
    requires ea_writer_admission::valid(admission, images), 0 <= index < images.tx.original.len(),
        images.tx.original[index].block == admission.boot.table,
    ensures images.tx.original[index].image.subrange(1792, 2048) == ea_bootstrap::journal_inode(admission.boot),
{
    ea_writer_admission::prepared_patch_facts(admission, images);
    a_protected_patch_keeps_the_exact_journal_inode(admission.boot, admission.prepared().after, images.tx.original, index);
}

proof fn transport_primary_marker_facts(images: Images)
    requires write_io::transport_images(images),
    ensures images.dirty.len() == 4096, crate::super_state::is_dirty(images.dirty),
{
    hide(crate::crc::fold);
    reveal(write_io::transport_images);
}

proof fn raw_writer_cuts_keep_the_exact_primary_block(old: BootstrapView, images: Images, machine: Machine, dirty: Seq<u8>)
    requires ea_bootstrap::valid(old), write_io::transport_images(images),
        (forall|i: int| 0 <= i < images.tx.original.len() ==> (#[trigger] images.tx.original[i]).block >= 2),
        write_device::inv(machine, images.tx.payloads.len()),
        write_recognition::transport_context(disk_image::initial_disk(old.source, old.blocks), images),
        images.tx.layout == old.layout, images.initial_primary == old.source.subrange(0, 4096),
        dirty == ea_writer_admission::marked(old.source, images),
    ensures raw_cut_source(old, images, machine).len() == old.source.len(),
        raw_cut_source(old, images, machine).subrange(0, 4096) == old.source.subrange(0, 4096)
            || raw_cut_source(old, images, machine).subrange(0, 4096) == dirty.subrange(0, 4096),
{
    hide(crate::crc::fold);
    hide(patch_set::apply);
    hide(write_media::apply);
    let before = disk_image::initial_disk(old.source, old.blocks);
    let media = write_media::disk(machine, before, images);
    locator_facts(old);
    write_recognition::every_transport_primary_is_initial_or_dirty(machine, before, images);
    disk_image::a_flat_projection_reads_every_complete_present_block(media, old.source, old.blocks, 0);
    transport_primary_marker_facts(images);
    patch_set::a_primary_marker_replaces_exactly_block_zero(old.source, images.dirty);
}

proof fn raw_writer_cuts_keep_the_exact_descriptor_block(old: BootstrapView, images: Images, machine: Machine)
    requires ea_bootstrap::valid(old), write_io::transport_images(images),
        (forall|i: int| 0 <= i < images.tx.original.len() ==> (#[trigger] images.tx.original[i]).block >= 2),
    ensures raw_cut_source(old, images, machine).subrange(4096, 8192) == old.source.subrange(4096, 8192),
{
    hide(crate::crc::fold);
    hide(write_media::apply);
    let before = disk_image::initial_disk(old.source, old.blocks);
    let media = write_media::disk(machine, before, images);
    let limit = write_device::total(images.tx.payloads.len());
    locator_facts(old);
    disk_image::initial_block_map_has_the_exact_source_bytes(old.source, old.blocks, 1);
    write_media::all_transport_writer_commands_avoid_block_one(images);
    write_media::apply_frames_every_unwritten_block(before, images, machine.stable, limit, 1);
    write_media::apply_keeps_every_existing_block(before, images, machine.stable, limit);
    disk_image::a_flat_projection_reads_every_complete_present_block(media, old.source, old.blocks, 1);
}

#[verifier::rlimit(30)]
proof fn raw_writer_cuts_keep_the_exact_primary_and_descriptor_blocks(old: BootstrapView, images: Images, machine: Machine, dirty: Seq<u8>)
    requires ea_bootstrap::valid(old), write_io::transport_images(images),
        (forall|i: int| 0 <= i < images.tx.original.len() ==> (#[trigger] images.tx.original[i]).block >= 2),
        write_device::inv(machine, images.tx.payloads.len()),
        write_recognition::transport_context(disk_image::initial_disk(old.source, old.blocks), images),
        images.tx.layout == old.layout, images.initial_primary == old.source.subrange(0, 4096),
        dirty == ea_writer_admission::marked(old.source, images),
    ensures raw_cut_source(old, images, machine).len() == old.source.len(),
        raw_cut_source(old, images, machine).subrange(0, 4096) == old.source.subrange(0, 4096)
            || raw_cut_source(old, images, machine).subrange(0, 4096) == dirty.subrange(0, 4096),
        raw_cut_source(old, images, machine).subrange(4096, 8192) == old.source.subrange(4096, 8192),
{
    raw_writer_cuts_keep_the_exact_primary_block(old, images, machine, dirty);
    raw_writer_cuts_keep_the_exact_descriptor_block(old, images, machine);
}

#[verifier::rlimit(30)]
proof fn raw_writer_cuts_keep_the_exact_journal_inode_slice(old: BootstrapView, images: Images, machine: Machine)
    requires ea_bootstrap::valid(old), ea_write_io::valid_images(images),
        write_device::inv(machine, images.tx.payloads.len()),
        write_recognition::transport_context(disk_image::initial_disk(old.source, old.blocks), images),
        images.tx.layout == old.layout,
        !(old.layout.start <= old.table < old.layout.start as nat + old.layout.journal_blocks),
        (forall|i: int| 0 <= i < images.tx.original.len() && (#[trigger] images.tx.original[i]).block == old.table ==>
            images.tx.original[i].image.subrange(1792, 2048) == ea_bootstrap::journal_inode(old)),
    ensures raw_cut_source(old, images, machine).subrange(old.table as int * 4096 + 1792,
        old.table as int * 4096 + 2048) == ea_bootstrap::journal_inode(old),
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    hide(write_media::apply);
    reveal(ea_write_io::valid_images);
    reveal(write_io::transport_images);
    let blocks = old.blocks;
    let before = disk_image::initial_disk(old.source, blocks);
    let count = images.tx.payloads.len();
    let limit = write_device::total(count);
    let media = write_media::disk(machine, before, images);
    let source = raw_cut_source(old, images, machine);
    locator_facts(old);
    disk_image::initial_block_map_has_the_exact_source_bytes(old.source, blocks, old.table);
    assert forall|k: nat| k < limit && write_device::is_write(k, count) && machine.stable.contains(k)
        && #[trigger] write_media::address(images, k) == old.table
        implies write_media::image(images, k).len() == 4096
            && write_media::image(images, k).subrange(1792, 2048) == before[old.table].subrange(1792, 2048) by {
        write_media::every_program_write_has_a_complete_bounded_image_transport(images, k);
        if 8 + count <= k < 8 + 2 * count {
            let i = (k - (8 + count)) as int;
            assert(images.tx.original[i].image.subrange(1792, 2048) == ea_bootstrap::journal_inode(old));
        } else {
            assert(old.table != 0);
            assert(!(old.layout.start <= old.table < old.layout.start as nat + old.layout.journal_blocks));
        }
    }
    write_media::apply_preserves_a_fixed_block_slice(before, images, machine.stable, limit, old.table, 1792, 2048);
    disk_image::a_flat_projection_reads_every_complete_present_block(media, old.source, blocks, old.table);
    assert(source.subrange(old.table as int * 4096 + 1792, old.table as int * 4096 + 2048)
        =~= source.subrange(old.table as int * 4096, (old.table as int + 1) * 4096).subrange(1792, 2048));
    assert(before[old.table].subrange(1792, 2048) =~= ea_bootstrap::journal_inode(old));
}

#[verifier::rlimit(30)]
proof fn every_raw_writer_cut_has_an_admissible_fresh_ea_bootstrap(old: BootstrapView, images: Images, machine: Machine, dirty: Seq<u8>)
    requires ea_bootstrap::valid(old), ea_write_io::valid_images(images),
        write_device::inv(machine, images.tx.payloads.len()),
        write_recognition::transport_context(disk_image::initial_disk(old.source, old.blocks), images),
        images.tx.layout == old.layout, images.initial_primary == old.source.subrange(0, 4096),
        dirty == ea_writer_admission::marked(old.source, images), ea_bootstrap::admissible(dirty),
        ea_bootstrap::same_locator_geometry(old, ea_bootstrap::projection(dirty)),
        bootstrap_identity::primary_fixed(old.source.subrange(0, 4096), dirty.subrange(0, 4096)),
        !(old.layout.start <= old.table < old.layout.start as nat + old.layout.journal_blocks),
        (forall|i: int| 0 <= i < images.tx.original.len() && (#[trigger] images.tx.original[i]).block == old.table ==>
            images.tx.original[i].image.subrange(1792, 2048) == ea_bootstrap::journal_inode(old)),
    ensures ea_bootstrap::admissible(raw_cut_source(old, images, machine)),
        ea_bootstrap::same_locator_geometry(old, ea_bootstrap::projection(raw_cut_source(old, images, machine))),
{
    ea_transport_target_facts(images);
    raw_writer_cuts_keep_the_exact_primary_and_descriptor_blocks(old, images, machine, dirty);
    raw_writer_cuts_keep_the_exact_journal_inode_slice(old, images, machine);
    ea_bootstrap::complete_bootstrap_block_mixtures_keep_the_same_admitted_locator(old,
        ea_bootstrap::projection(dirty), raw_cut_source(old, images, machine));
}


pub proof fn every_admitted_writer_cut_has_an_admissible_fresh_ea_bootstrap(admission: AdmissionView, images: Images, machine: Machine)
    requires ea_writer_admission::valid(admission, images), write_device::inv(machine, images.tx.payloads.len()),
    ensures ea_bootstrap::admissible(cut_source(admission, images, machine)),
        ea_bootstrap::same_locator_geometry(admission.boot, ea_bootstrap::projection(cut_source(admission, images, machine))),
{
    an_admitted_source_supplies_the_physical_writer_context(admission, images);
    ea_writer_admission::transport_facts(admission, images);
    ea_writer_admission::dirty_prefix_facts(admission, images);
    let old = admission.boot;
    let dirty = ea_writer_admission::source_of(admission.prefixes[0]);
    a_bootstrap_preserving_ea_namespace_has_an_admissible_locator(old, admission.prefixes[0]);
    the_journal_cannot_alias_the_journal_inode_table(old, admission.prefixes[0]);
    assert forall|i: int| 0 <= i < images.tx.original.len() && (#[trigger] images.tx.original[i]).block == old.table
        implies images.tx.original[i].image.subrange(1792, 2048) == ea_bootstrap::journal_inode(old) by {
        every_home_patch_preserves_the_exact_journal_inode(admission, images, i);
    }
    every_raw_writer_cut_has_an_admissible_fresh_ea_bootstrap(old, images, machine, dirty);
}

pub proof fn every_finite_admitted_writer_trace_keeps_fresh_ea_bootstrap_discovery(admission: AdmissionView, images: Images,
    states: Seq<Machine>, events: Seq<write_device::Event>)
    requires ea_writer_admission::valid(admission, images), write_device::execution(states, events, images.tx.payloads.len()),
        states[0] == write_device::initial(),
    ensures forall|i: int| 0 <= i < states.len() ==> ea_bootstrap::admissible(#[trigger] cut_source(admission, images, states[i]))
        && ea_bootstrap::same_locator_geometry(admission.boot, ea_bootstrap::projection(cut_source(admission, images, states[i]))),
{
    ea_writer_admission::transport_facts(admission, images);
    reveal(ea_write_io::valid_images);
    reveal(write_io::transport_images);
    write_device::initialization(images.tx.payloads.len());
    write_device::every_finite_io_interleaving(states, events, images.tx.payloads.len());
    assert forall|i: int| 0 <= i < states.len() implies ea_bootstrap::admissible(#[trigger] cut_source(admission, images, states[i]))
        && ea_bootstrap::same_locator_geometry(admission.boot, ea_bootstrap::projection(cut_source(admission, images, states[i]))) by {
        every_admitted_writer_cut_has_an_admissible_fresh_ea_bootstrap(admission, images, states[i]);
    }
}

#[verifier::rlimit(30)]
proof fn every_raw_writer_cut_has_the_actual_canonical_ea_scan_source(old: BootstrapView, images: Images,
    machine: Machine, layout: &crate::layout::JournalLayout)
    requires ea_bootstrap::valid(old), write_io::transport_images(images),
        write_device::inv(machine, images.tx.payloads.len()), layout.wf(), layout.view() == images.tx.layout,
        write_recognition::transport_context(disk_image::initial_disk(old.source, old.blocks), images),
        images.tx.layout == old.layout, images.initial_journal == ea_bootstrap::journal_bytes(old),
        images.tx.uuid == ea_bootstrap::journal_identity(old),
        ea_bootstrap::admissible(raw_cut_source(old, images, machine)),
        ea_bootstrap::same_locator_geometry(old, ea_bootstrap::projection(raw_cut_source(old, images, machine))),
    ensures ea_bootstrap::scan_source(ea_bootstrap::projection(raw_cut_source(old, images, machine)))
            == crate::write_recovery::source(machine, disk_image::initial_disk(old.source, old.blocks), images, layout),
        crate::scan_budget::admitted(
            ea_bootstrap::journal_bytes(ea_bootstrap::projection(raw_cut_source(old, images, machine))),
            ea_bootstrap::journal_identity(ea_bootstrap::projection(raw_cut_source(old, images, machine))), layout),
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    hide(write_media::apply);
    reveal(write_io::transport_images);
    let before = disk_image::initial_disk(old.source, old.blocks);
    let media = write_media::disk(machine, before, images);
    let count = images.tx.payloads.len();
    let source = raw_cut_source(old, images, machine);
    let next = ea_bootstrap::projection(source);
    write_media::apply_preserves_initialized_journal_mapping_transport(before, images, machine.stable, write_device::total(count));
    locator_facts(old);
    disk_image::a_flat_projection_has_the_exact_mapped_journal(media, old.source, images.tx.layout);
    assert(ea_bootstrap::journal_bytes(next) == crate::journal_view::snapshot(media, images.tx.layout));
    write_media::journal_superblock_is_one_of_the_ordered_state_images_transport(machine, before, images);
    crate::journal_view::snapshot_block_is_the_physical_image(media, images.tx.layout, 0);
    crate::journal_view::snapshot_block_is_the_physical_image(before, images.tx.layout, 0);
    assert(images.activation.subrange(48, 64) =~= images.initial_journal.subrange(48, 64));
    assert(images.tail.subrange(48, 64) =~= images.activation.subrange(48, 64));
    assert(ea_bootstrap::journal_identity(next) == images.tx.uuid) by {
        assert(ea_bootstrap::journal_bytes(next).subrange(48, 64)
            =~= media[images.journal_block].subrange(48, 64));
        assert(images.initial_journal.subrange(48, 64) == ea_bootstrap::journal_identity(old));
    }
    assert(ea_bootstrap::scan_source(next) == crate::write_recovery::source(machine, before, images, layout)) by {
        ea_bootstrap::a_valid_bootstrap_uses_its_actual_journal_identity_seed(next);
    }
    crate::write_admission::every_writer_crash_snapshot_is_admitted_transport(machine, before, images, layout);
}


pub proof fn every_admitted_writer_cut_has_the_actual_canonical_ea_scan_source(admission: AdmissionView, images: Images,
    machine: Machine, layout: &crate::layout::JournalLayout)
    requires ea_writer_admission::valid(admission, images), write_device::inv(machine, images.tx.payloads.len()),
        layout.wf(), layout.view() == images.tx.layout,
    ensures ea_bootstrap::admissible(cut_source(admission, images, machine)),
        ea_bootstrap::scan_source(ea_bootstrap::projection(cut_source(admission, images, machine)))
            == crate::write_recovery::source(machine, disk_image::initial_disk(admission.boot.source, admission.boot.blocks), images, layout),
        crate::scan_budget::admitted(
            ea_bootstrap::journal_bytes(ea_bootstrap::projection(cut_source(admission, images, machine))),
            ea_bootstrap::journal_identity(ea_bootstrap::projection(cut_source(admission, images, machine))), layout),
{
    every_admitted_writer_cut_has_an_admissible_fresh_ea_bootstrap(admission, images, machine);
    an_admitted_source_supplies_the_physical_writer_context(admission, images);
    ea_writer_admission::transport_facts(admission, images);
    every_raw_writer_cut_has_the_actual_canonical_ea_scan_source(admission.boot, images, machine, layout);
}

proof fn complete_redo_is_the_exact_raw_patch_image(old: BootstrapView, after: Seq<u8>, images: Images, block: u32)
    requires ea_bootstrap::valid(old), patch_set::valid(images.tx.original),
        after == patch_set::apply(old.source, images.tx.original), block < old.blocks,
        write_recognition::transport_context(disk_image::initial_disk(old.source, old.blocks), images),
    ensures crate::replay_refinement::chronological(disk_image::initial_disk(old.source, old.blocks),
        crate::transaction_refinement::log(images.tx), Seq::empty())[block]
        == after.subrange(block as int * 4096, (block as int + 1) * 4096),
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    hide(patch_set::apply);
    let before = disk_image::initial_disk(old.source, old.blocks);
    let log = crate::transaction_refinement::log(images.tx);
    locator_facts(old);
    disk_image::initial_block_map_has_the_exact_source_bytes(old.source, old.blocks, block);
    crate::write_recovery::original_targets_exist_transport(before, images);
    crate::replay_refinement::chronological_lookup(before, log, Seq::empty(), block);
    crate::replay_refinement::last_eligible_characterizes_latest(log, Seq::empty(), block);
    patch_set::applying_a_patch_replaces_exactly_its_block(old.source, images.tx.original, block);
    if let Some(i) = crate::replay_refinement::last_eligible(log, Seq::empty(), block) {
        patch_set::one_target_has_one_image(images.tx.original, i as int);
    } else {
        assert(patch_set::selected(images.tx.original, block as int).is_none()) by {
            if exists|i: int| 0 <= i < images.tx.original.len() && (#[trigger] images.tx.original[i]).block as int == block {
                let i = choose|i: int| 0 <= i < images.tx.original.len() && (#[trigger] images.tx.original[i]).block as int == block;
                assert(log[i].block == block);
                assert(crate::replay::blocked(block, log[i].sequence, Seq::empty()));
            }
        }
    }
}


proof fn complete_redo_is_the_exact_prepared_home_image(admission: AdmissionView, images: Images, block: u32)
    requires ea_writer_admission::valid(admission, images), block < admission.boot.blocks,
    ensures crate::replay_refinement::chronological(disk_image::initial_disk(admission.boot.source, admission.boot.blocks),
        crate::transaction_refinement::log(images.tx), Seq::empty())[block]
        == admission.prepared().after.subrange(block as int * 4096, (block as int + 1) * 4096),
{
    an_admitted_source_supplies_the_physical_writer_context(admission, images);
    ea_writer_admission::prepared_patch_facts(admission, images);
    complete_redo_is_the_exact_raw_patch_image(admission.boot, admission.prepared().after, images, block);
}

proof fn successful_recovery_of_a_raw_writer_cut_has_exact_homes(source: Seq<u8>, blocks: u32, after: Seq<u8>, images: Images,
    machine: Machine, layout: &crate::layout::JournalLayout, result: &crate::scan::Scan,
    recovery: crate::recovery_device::Machine, tail: Seq<u8>, block: u32)
    requires blocks as nat * 4096 <= source.len(), blocks == images.tx.layout.fs_blocks,
        write_recognition::transport_context(disk_image::initial_disk(source, blocks), images),
        write_device::inv(machine, images.tx.payloads.len()), layout.wf(), layout.view() == images.tx.layout,
        crate::write_recovery::returned(result, crate::write_recovery::source(machine, disk_image::initial_disk(source, blocks), images, layout)),
        0 < block < blocks, !(images.tx.layout.start <= block < images.tx.layout.start as nat + images.tx.layout.journal_blocks),
        crate::replay_refinement::chronological(disk_image::initial_disk(source, blocks),
            crate::transaction_refinement::log(images.tx), Seq::empty())[block]
            == after.subrange(block as int * 4096, (block as int + 1) * 4096),
        crate::recovery_device::inv(recovery, write_media::disk(machine, disk_image::initial_disk(source, blocks), images),
            result.plan(), images.journal_block, tail),
        recovery.io.phase == 4, !recovery.io.faulted, !recovery.io.pending,
    ensures recovery.stable[block] == if machine.stable.contains(6 + images.tx.payloads.len()) {
            after.subrange(block as int * 4096, (block as int + 1) * 4096)
        } else { source.subrange(block as int * 4096, (block as int + 1) * 4096) },
        crate::write_protocol::completed_count(machine.io, images.tx.payloads.len()) > 7 + images.tx.payloads.len()
            ==> recovery.stable[block] == after.subrange(block as int * 4096, (block as int + 1) * 4096),
{
    let before = disk_image::initial_disk(source, blocks);
    disk_image::initial_block_map_has_the_exact_source_bytes(source, blocks, block);
    crate::write_recovery::successful_recovery_of_every_writer_cut_has_before_or_after_home_bytes_transport(
        machine, before, images, layout, result, recovery, tail, block);
    if crate::write_protocol::completed_count(machine.io, images.tx.payloads.len()) > 7 + images.tx.payloads.len() {
        write_recognition::acknowledged_commit_has_the_complete_durable_log_transport(machine, before, images);
    }
}

/// Covers a cut selected from any finite modeled trace, including errors,
/// aborts and persistence of commands issued before those events. The scanner
/// witness is for the actual raw cut, and successful recovery remains subject
/// to the declared atomic-block/flush device invariant.
pub proof fn successful_recovery_of_an_ea_writer_cut_has_exact_before_or_after_homes(admission: AdmissionView, images: Images,
    machine: Machine, layout: &crate::layout::JournalLayout, result: &crate::scan::Scan,
    recovery: crate::recovery_device::Machine, tail: Seq<u8>, block: u32)
    requires ea_writer_admission::valid(admission, images), write_device::inv(machine, images.tx.payloads.len()),
        layout.wf(), layout.view() == images.tx.layout,
        crate::write_recovery::returned(result,
            ea_bootstrap::scan_source(ea_bootstrap::projection(cut_source(admission, images, machine)))),
        0 < block < admission.boot.blocks,
        !(images.tx.layout.start <= block < images.tx.layout.start as nat + images.tx.layout.journal_blocks),
        crate::recovery_device::inv(recovery,
            write_media::disk(machine, disk_image::initial_disk(admission.boot.source, admission.boot.blocks), images),
            result.plan(), images.journal_block, tail),
        recovery.io.phase == 4, !recovery.io.faulted, !recovery.io.pending,
    ensures recovery.stable[block] == if machine.stable.contains(6 + images.tx.payloads.len()) {
            admission.prepared().after.subrange(block as int * 4096, (block as int + 1) * 4096)
        } else { admission.boot.source.subrange(block as int * 4096, (block as int + 1) * 4096) },
        crate::write_protocol::completed_count(machine.io, images.tx.payloads.len()) > 7 + images.tx.payloads.len()
            ==> recovery.stable[block] == admission.prepared().after.subrange(block as int * 4096, (block as int + 1) * 4096),
{
    every_admitted_writer_cut_has_the_actual_canonical_ea_scan_source(admission, images, machine, layout);
    an_admitted_source_supplies_the_physical_writer_context(admission, images);
    ea_writer_admission::transport_facts(admission, images);
    locator_facts(admission.boot);
    complete_redo_is_the_exact_prepared_home_image(admission, images, block);
    successful_recovery_of_a_raw_writer_cut_has_exact_homes(admission.boot.source, admission.boot.blocks,
        admission.prepared().after, images, machine, layout, result, recovery, tail, block);
}

pub proof fn every_finite_ea_writer_trace_has_actual_canonical_scanner_admission(admission: AdmissionView, images: Images,
    layout: &crate::layout::JournalLayout, states: Seq<Machine>, events: Seq<write_device::Event>)
    requires ea_writer_admission::valid(admission, images), layout.wf(), layout.view() == images.tx.layout,
        write_device::execution(states, events, images.tx.payloads.len()), states[0] == write_device::initial(),
    ensures forall|i: int| 0 <= i < states.len() ==> ea_bootstrap::admissible(#[trigger] cut_source(admission, images, states[i]))
        && crate::scan_budget::admitted(
            ea_bootstrap::journal_bytes(ea_bootstrap::projection(cut_source(admission, images, states[i]))),
            ea_bootstrap::journal_identity(ea_bootstrap::projection(cut_source(admission, images, states[i]))), layout),
{
    an_admitted_source_supplies_the_physical_writer_context(admission, images);
    let before = disk_image::initial_disk(admission.boot.source, admission.boot.blocks);
    crate::write_admission::every_finite_transport_interleaving_has_actual_scanner_admission(states, events, before, images, layout);
    assert forall|i: int| 0 <= i < states.len() implies ea_bootstrap::admissible(#[trigger] cut_source(admission, images, states[i]))
        && crate::scan_budget::admitted(
            ea_bootstrap::journal_bytes(ea_bootstrap::projection(cut_source(admission, images, states[i]))),
            ea_bootstrap::journal_identity(ea_bootstrap::projection(cut_source(admission, images, states[i]))), layout) by {
        every_admitted_writer_cut_has_the_actual_canonical_ea_scan_source(admission, images, states[i], layout);
    }
}

pub proof fn successful_recovery_of_any_finite_ea_writer_trace_cut_has_exact_homes(admission: AdmissionView, images: Images,
    states: Seq<Machine>, events: Seq<write_device::Event>, cut: int,
    layout: &crate::layout::JournalLayout, result: &crate::scan::Scan,
    recovery: crate::recovery_device::Machine, tail: Seq<u8>, block: u32)
    requires ea_writer_admission::valid(admission, images), layout.wf(), layout.view() == images.tx.layout,
        write_device::execution(states, events, images.tx.payloads.len()), states[0] == write_device::initial(),
        0 <= cut < states.len(),
        crate::write_recovery::returned(result,
            ea_bootstrap::scan_source(ea_bootstrap::projection(cut_source(admission, images, states[cut])))),
        0 < block < admission.boot.blocks,
        !(images.tx.layout.start <= block < images.tx.layout.start as nat + images.tx.layout.journal_blocks),
        crate::recovery_device::inv(recovery,
            write_media::disk(states[cut], disk_image::initial_disk(admission.boot.source, admission.boot.blocks), images),
            result.plan(), images.journal_block, tail),
        recovery.io.phase == 4, !recovery.io.faulted, !recovery.io.pending,
    ensures recovery.stable[block] == if states[cut].stable.contains(6 + images.tx.payloads.len()) {
            admission.prepared().after.subrange(block as int * 4096, (block as int + 1) * 4096)
        } else { admission.boot.source.subrange(block as int * 4096, (block as int + 1) * 4096) },
        crate::write_protocol::completed_count(states[cut].io, images.tx.payloads.len()) > 7 + images.tx.payloads.len()
            ==> recovery.stable[block] == admission.prepared().after.subrange(block as int * 4096, (block as int + 1) * 4096),
{
    an_admitted_source_supplies_the_physical_writer_context(admission, images);
    let before = disk_image::initial_disk(admission.boot.source, admission.boot.blocks);
    crate::write_admission::every_finite_transport_interleaving_has_actual_scanner_admission(states, events, before, images, layout);
    successful_recovery_of_an_ea_writer_cut_has_exact_before_or_after_homes(
        admission, images, states[cut], layout, result, recovery, tail, block);
}

proof fn an_actual_ea_bootstrap_primary_fits_recovery(v: BootstrapView)
    requires ea_bootstrap::valid(v),
    ensures v.source.subrange(0, 4096).len() == 4096,
        ea_source::header_accepted(v.source.subrange(0, 4096).subrange(1024, 2048), v.source.len() as u64),
        bytes::le32(v.source.subrange(0, 4096), 1028) == v.layout.fs_blocks,
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    hide(crate::group::accepted_with_features);
    hide(crate::layout::admitted);
    reveal(ea_bootstrap::valid);
    assert(v.source.subrange(0, 4096).subrange(1024, 2048) =~= v.source.subrange(1024, 2048));
}

proof fn an_active_raw_writer_cut_has_an_actual_dirty_primary(old: BootstrapView, images: Images, machine: Machine,
    layout: &crate::layout::JournalLayout)
    requires ea_bootstrap::valid(old), write_io::transport_images(images),
        (forall|i: int| 0 <= i < images.tx.original.len() ==> (#[trigger] images.tx.original[i]).block >= 2),
        write_device::inv(machine, images.tx.payloads.len()), layout.wf(), layout.view() == images.tx.layout,
        write_recognition::transport_context(disk_image::initial_disk(old.source, old.blocks), images),
        images.tx.layout == old.layout, images.initial_primary == old.source.subrange(0, 4096),
    ensures crate::write_recovery::source(machine, disk_image::initial_disk(old.source, old.blocks), images, layout).start != 0
        ==> crate::super_state::is_dirty(raw_cut_source(old, images, machine).subrange(0, 4096)),
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    hide(write_media::apply);
    reveal(write_io::transport_images);
    locator_facts(old);
    let before = disk_image::initial_disk(old.source, old.blocks);
    let media = write_media::disk(machine, before, images);
    let journal = crate::journal_view::snapshot(media, images.tx.layout);
    let count = images.tx.payloads.len();
    write_media::apply_preserves_initialized_journal_mapping_transport(before, images, machine.stable, write_device::total(count));
    write_media::journal_superblock_is_one_of_the_ordered_state_images_transport(machine, before, images);
    crate::journal_view::snapshot_block_is_the_physical_image(media, images.tx.layout, 0);
    crate::journal_view::snapshot_block_is_the_physical_image(before, images.tx.layout, 0);
    if crate::write_recovery::source(machine, before, images, layout).start != 0 {
        assert(bytes::be32(journal, 28) != 0);
        assert(machine.stable.contains(2));
        write_recognition::every_transport_primary_is_initial_or_dirty(machine, before, images);
        disk_image::a_flat_projection_reads_every_complete_present_block(media, old.source, old.blocks, 0);
    }
}

#[verifier::rlimit(30)]
proof fn every_raw_ea_writer_cut_has_the_recovery_transport_profile(old: BootstrapView, images: Images,
    machine: Machine, layout: &crate::layout::JournalLayout)
    requires ea_bootstrap::valid(old), ea_write_io::valid_images(images),
        write_device::inv(machine, images.tx.payloads.len()), layout.wf(), layout.view() == images.tx.layout,
        write_recognition::transport_context(disk_image::initial_disk(old.source, old.blocks), images),
        images.tx.layout == old.layout, images.initial_primary == old.source.subrange(0, 4096),
        images.initial_journal == ea_bootstrap::journal_bytes(old), images.tx.uuid == ea_bootstrap::journal_identity(old),
        ea_bootstrap::admissible(raw_cut_source(old, images, machine)),
        ea_bootstrap::same_locator_geometry(old, ea_bootstrap::projection(raw_cut_source(old, images, machine))),
    ensures ea_bootstrap::source_can_prepare(ea_bootstrap::projection(raw_cut_source(old, images, machine)), layout),
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    ea_transport_target_facts(images);
    let before = disk_image::initial_disk(old.source, old.blocks);
    let source = raw_cut_source(old, images, machine);
    let next = ea_bootstrap::projection(source);
    every_raw_writer_cut_has_the_actual_canonical_ea_scan_source(old, images, machine, layout);
    an_actual_ea_bootstrap_primary_fits_recovery(next);
    ea_bootstrap::a_valid_bootstrap_uses_its_actual_journal_identity_seed(next);
    assert(crate::scan_budget::source(ea_bootstrap::journal_bytes(next), ea_bootstrap::journal_identity(next), layout)
        == ea_bootstrap::scan_source(next));
    if bytes::be32(ea_bootstrap::journal_bytes(next), 28) != 0 {
        an_active_raw_writer_cut_has_an_actual_dirty_primary(old, images, machine, layout);
        crate::write_recovery::snapshot_state_transport(machine, before, images, layout);
        crate::write_admission::every_committed_ea_writer_stream_excludes_primary_targets(machine, before, images);
    }
    assert(crate::recovery_io::can_prepare_ea(ea_bootstrap::journal_bytes(next), ea_bootstrap::journal_identity(next), layout,
        source.subrange(0, 4096), source.len() as u64)) by {
        reveal(crate::recovery_io::can_prepare_ea);
    }
}

/// The actual raw cut has a sufficient profile for the additive EA recovery
/// engine. Full repaired-namespace inspection may still reject its shadow.
pub proof fn every_admitted_ea_writer_cut_has_the_raw_recovery_transport_profile(admission: AdmissionView, images: Images,
    machine: Machine, layout: &crate::layout::JournalLayout)
    requires ea_writer_admission::valid(admission, images), write_device::inv(machine, images.tx.payloads.len()),
        layout.wf(), layout.view() == images.tx.layout,
    ensures ea_bootstrap::source_can_prepare(ea_bootstrap::projection(cut_source(admission, images, machine)), layout),
{
    every_admitted_writer_cut_has_an_admissible_fresh_ea_bootstrap(admission, images, machine);
    an_admitted_source_supplies_the_physical_writer_context(admission, images);
    ea_writer_admission::transport_facts(admission, images);
    every_raw_ea_writer_cut_has_the_recovery_transport_profile(admission.boot, images, machine, layout);
}

pub proof fn a_fresh_bootstrap_from_an_ea_writer_cut_can_prepare_recovery(admission: AdmissionView, images: Images,
    machine: Machine, boot: &ea_bootstrap::Bootstrap<'_, '_>, layout: &crate::layout::JournalLayout)
    requires ea_writer_admission::valid(admission, images), write_device::inv(machine, images.tx.payloads.len()),
        boot.wf(), boot.view().source == cut_source(admission, images, machine), layout.wf(), layout.view() == images.tx.layout,
    ensures boot.can_prepare_recovery(),
{
    every_admitted_ea_writer_cut_has_the_raw_recovery_transport_profile(admission, images, machine, layout);
    ea_bootstrap::every_valid_bootstrap_is_the_unique_source_projection(boot.view());
    boot.recovery_profile_is_exact(layout);
}

pub proof fn every_finite_ea_writer_trace_has_a_sufficient_raw_recovery_profile(admission: AdmissionView, images: Images,
    layout: &crate::layout::JournalLayout, states: Seq<Machine>, events: Seq<write_device::Event>)
    requires ea_writer_admission::valid(admission, images), layout.wf(), layout.view() == images.tx.layout,
        write_device::execution(states, events, images.tx.payloads.len()), states[0] == write_device::initial(),
    ensures forall|i: int| 0 <= i < states.len() ==> ea_bootstrap::source_can_prepare(
        ea_bootstrap::projection(#[trigger] cut_source(admission, images, states[i])), layout),
{
    an_admitted_source_supplies_the_physical_writer_context(admission, images);
    let before = disk_image::initial_disk(admission.boot.source, admission.boot.blocks);
    crate::write_admission::every_finite_transport_interleaving_has_actual_scanner_admission(states, events, before, images, layout);
    assert forall|i: int| 0 <= i < states.len() implies ea_bootstrap::source_can_prepare(
        ea_bootstrap::projection(#[trigger] cut_source(admission, images, states[i])), layout) by {
        every_admitted_ea_writer_cut_has_the_raw_recovery_transport_profile(admission, images, states[i], layout);
    }
}

}
