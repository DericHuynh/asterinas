// SPDX-License-Identifier: MPL-2.0

//! Whole-image byte projection for the declared serialized atomic-block device
//! model. This does not establish an actual CortenMM/BIO/driver refinement.

use vstd::prelude::*;
use crate::{bootstrap, disk_image, namespace, patch_set,
    transaction::ImageView, write_device::{self, Machine}, write_io::{self, Images}, write_media,
    write_recognition, writer_admission::{self, AdmissionView}};

verus! {

pub proof fn an_admitted_source_supplies_the_physical_writer_context(admission: AdmissionView, images: Images)
    requires writer_admission::valid(admission, images),
    ensures write_recognition::context(disk_image::initial_disk(admission.boot.source, images.tx.layout.fs_blocks), images),
{
    hide(crate::crc::fold);
    reveal(writer_admission::valid);
    reveal(write_io::valid_images);
    reveal(bootstrap::valid);
    let source = admission.boot.source;
    let disk = disk_image::initial_disk(source, images.tx.layout.fs_blocks);
    disk_image::a_flat_source_has_the_exact_mapped_journal(source, images.tx.layout);
    disk_image::initial_block_map_has_the_exact_source_bytes(source, images.tx.layout.fs_blocks, 0);
    assert forall|k: nat| write_device::is_write(k, images.tx.payloads.len()) implies
        #[trigger] disk.dom().contains(write_media::address(images, k)) by {
        write_media::every_program_write_has_a_complete_bounded_image(images, k);
        disk_image::initial_disk_addresses_are_exactly_the_filesystem_range(source, images.tx.layout.fs_blocks, write_media::address(images, k));
    }
}

pub open spec fn expected_block(source: Seq<u8>, images: Images, block: u32) -> Seq<u8> {
    if block == images.journal_block { images.tail }
    else {
        match patch_set::selected(images.tx.original, block as int) {
            Some(image) => image,
            None => match patch_set::selected(write_io::log_images(images), block as int) {
                Some(image) => image,
                None => if block == 0 { images.dirty } else { disk_image::source_block(source, block) },
            },
        }
    }
}

proof fn admission_byte_shapes(admission: AdmissionView, images: Images)
    requires writer_admission::valid(admission, images),
    ensures images.tx.layout.fs_blocks as nat * 4096 <= admission.boot.source.len(),
        images.dirty.len() == 4096, images.tail.len() == 4096,
        patch_set::valid(images.tx.original), patch_set::valid(write_io::log_images(images)),
        writer_admission::final_source(admission.boot.source, images).len() == admission.boot.source.len(),
        admission.after.index.volume.index.source == writer_admission::final_source(admission.boot.source, images),
        namespace::valid(admission.after),
{
    hide(crate::crc::fold);
    hide(crate::transaction::wf);
    reveal(writer_admission::valid);
    reveal(write_io::valid_images);
}

#[verifier::rlimit(30)]
pub proof fn validated_final_image_has_the_expected_block(admission: AdmissionView, images: Images, block: u32)
    requires writer_admission::valid(admission, images), block < images.tx.layout.fs_blocks,
    ensures writer_admission::final_source(admission.boot.source, images).subrange(block as int * 4096,
        (block as int + 1) * 4096) == expected_block(admission.boot.source, images, block),
        writer_admission::final_source(admission.boot.source, images).len() == admission.boot.source.len(),
{
    hide(patch_set::apply);
    admission_byte_shapes(admission, images);
    let source = admission.boot.source;
    let marker = seq![ImageView { block: 0, image: images.dirty }];
    let retirement = seq![ImageView { block: images.journal_block, image: images.tail }];
    assert(patch_set::valid(marker) && patch_set::valid(retirement)) by { reveal(patch_set::valid); }
    let dirty = patch_set::apply(source, marker);
    let logged = patch_set::apply(dirty, write_io::log_images(images));
    let homes = patch_set::apply(logged, images.tx.original);
    patch_set::applying_patches_preserves_the_source_length(source, marker);
    patch_set::applying_patches_preserves_the_source_length(dirty, write_io::log_images(images));
    patch_set::applying_patches_preserves_the_source_length(logged, images.tx.original);
    assert(dirty.len() == source.len() && logged.len() == source.len() && homes.len() == source.len());
    patch_set::applying_a_patch_replaces_exactly_its_block(source, marker, block);
    patch_set::applying_a_patch_replaces_exactly_its_block(dirty, write_io::log_images(images), block);
    patch_set::applying_a_patch_replaces_exactly_its_block(logged, images.tx.original, block);
    patch_set::applying_a_patch_replaces_exactly_its_block(homes, retirement, block);
    patch_set::a_single_patch_selects_exactly_its_target(marker[0], block as int);
    patch_set::a_single_patch_selects_exactly_its_target(retirement[0], block as int);
    assert(patch_set::selected(marker, block as int) == if block == 0 { Some(images.dirty) } else { None });
    assert(patch_set::selected(retirement, block as int) == if block == images.journal_block { Some(images.tail) } else { None });
}

proof fn no_selection_excludes_every_target(images: Seq<ImageView>, block: u32)
    requires patch_set::selected(images, block as int).is_none(),
    ensures forall|i: int| 0 <= i < images.len() ==> (#[trigger] images[i]).block != block,
{
    assert forall|i: int| 0 <= i < images.len() implies (#[trigger] images[i]).block != block by {
        if images[i].block == block {
            assert(exists|i: int| 0 <= i < images.len() && (#[trigger] images[i]).block as int == block);
        }
    }
}

proof fn log_targets_are_exactly_the_encoded_record_range(images: Images, block: u32)
    requires write_io::valid_images(images), patch_set::valid(write_io::log_images(images)),
    ensures patch_set::selected(write_io::log_images(images), block as int).is_some()
        == (images.journal_block as int + 1 <= block < images.journal_block as int + images.tx.payloads.len() + 3),
        images.journal_block as int + 1 <= block < images.journal_block as int + images.tx.payloads.len() + 3
            ==> patch_set::selected(write_io::log_images(images), block as int)
                == Some(write_io::log_images(images)[block as int - images.journal_block as int - 1].image),
{
    hide(crate::crc::fold);
    reveal(write_io::valid_images);
    let logs = write_io::log_images(images);
    if images.journal_block as int + 1 <= block < images.journal_block as int + images.tx.payloads.len() + 3 {
        let index = block as int - images.journal_block as int - 1;
        assert(logs[index].block == block);
        patch_set::one_target_has_one_image(logs, index);
    } else if patch_set::selected(logs, block as int).is_some() {
        let index = choose|i: int| 0 <= i < logs.len() && (#[trigger] logs[i]).block as int == block;
        assert(logs[index].block as int == images.journal_block as int + 1 + index);
    }
}

pub proof fn blocks_outside_the_home_journal_and_primary_targets_retain_their_source_bytes(admission: AdmissionView, images: Images, block: u32)
    requires writer_admission::valid(admission, images), 0 < block < images.tx.layout.fs_blocks,
        !(images.tx.layout.start <= block < images.tx.layout.start as nat + images.tx.layout.journal_blocks),
        patch_set::selected(images.tx.original, block as int).is_none(),
    ensures writer_admission::final_source(admission.boot.source, images).subrange(block as int * 4096, (block as int + 1) * 4096)
        == admission.boot.source.subrange(block as int * 4096, (block as int + 1) * 4096),
{
    hide(crate::crc::fold);
    validated_final_image_has_the_expected_block(admission, images, block);
    admission_byte_shapes(admission, images);
    reveal(writer_admission::valid);
    reveal(write_io::valid_images);
    reveal(crate::transaction::wf);
    log_targets_are_exactly_the_encoded_record_range(images, block);
}

pub proof fn an_untargeted_primary_is_exactly_the_dirty_identity_image(admission: AdmissionView, images: Images)
    requires writer_admission::valid(admission, images), patch_set::selected(images.tx.original, 0).is_none(),
    ensures writer_admission::final_source(admission.boot.source, images).subrange(0, 4096) == images.dirty,
        crate::super_state::preserves(admission.boot.source.subrange(0, 4096), writer_admission::final_source(admission.boot.source, images).subrange(0, 4096)),
{
    hide(crate::crc::fold);
    reveal(writer_admission::valid);
    reveal(write_io::valid_images);
    reveal(crate::transaction::wf);
    validated_final_image_has_the_expected_block(admission, images, 0);
    log_targets_are_exactly_the_encoded_record_range(images, 0);
}

pub proof fn a_selected_home_outside_the_journal_has_the_exact_final_bytes(admission: AdmissionView, images: Images, block: u32, image: Seq<u8>)
    requires writer_admission::valid(admission, images), block < images.tx.layout.fs_blocks,
        !(images.tx.layout.start <= block < images.tx.layout.start as nat + images.tx.layout.journal_blocks),
        patch_set::selected(images.tx.original, block as int) == Some(image),
    ensures writer_admission::final_source(admission.boot.source, images).subrange(block as int * 4096, (block as int + 1) * 4096) == image,
{
    hide(crate::crc::fold);
    validated_final_image_has_the_expected_block(admission, images, block);
    assert(write_io::valid_images(images)) by { reveal(writer_admission::valid); }
    reveal(write_io::valid_images);
}

#[verifier::rlimit(30)]
pub proof fn successful_media_has_exactly_the_expected_block(admission: AdmissionView, images: Images, machine: Machine, block: u32)
    requires writer_admission::valid(admission, images), write_device::inv(machine, images.tx.payloads.len()),
        machine.io.phase is Done, !machine.io.pending, !machine.io.faulted, block < images.tx.layout.fs_blocks,
    ensures write_media::disk(machine, disk_image::initial_disk(admission.boot.source, images.tx.layout.fs_blocks), images)[block]
        == expected_block(admission.boot.source, images, block),
{
    hide(crate::crc::fold);
    hide(write_media::apply);
    an_admitted_source_supplies_the_physical_writer_context(admission, images);
    let source = admission.boot.source;
    let before = disk_image::initial_disk(source, images.tx.layout.fs_blocks);
    let count = images.tx.payloads.len();
    write_recognition::successful_writer_completion_has_exact_durable_home_bytes_and_retired_tail(machine, before, images);
    write_device::successful_completion_is_durable_and_has_no_late_persistence(machine, count);
    reveal(writer_admission::valid);
    reveal(write_io::valid_images);
    disk_image::initial_block_map_has_the_exact_source_bytes(source, images.tx.layout.fs_blocks, block);
    log_targets_are_exactly_the_encoded_record_range(images, block);
    if block == images.journal_block {
    } else if let Some(image) = patch_set::selected(images.tx.original, block as int) {
        let index = choose|i: int| 0 <= i < images.tx.original.len() && (#[trigger] images.tx.original[i]).block as int == block;
        patch_set::one_target_has_one_image(images.tx.original, index);
        assert(image == images.tx.original[index].image);
    } else {
        no_selection_excludes_every_target(images.tx.original, block);
        if images.journal_block as int + 1 <= block < images.journal_block as int + count + 3 {
            let index = (block as int - images.journal_block as int - 1) as nat;
            let k = if index == count + 1 { 6 + count } else { 4 + index };
            assert(4 <= k < 5 + count || k == 6 + count);
            assert(machine.stable.contains(k));
            assert(write_media::address(images, k) == block);
            write_media::journal_record_bytes_follow_the_issued_snapshot(machine, before, images, k);
            assert(write_media::image(images, k) == write_io::log_images(images)[index as int].image);
        } else if block == 0 {
            write_media::without_a_stable_home_target_zero_only_dirty_marking_changes_block_zero(machine, before, images);
            assert(machine.stable.contains(0));
        } else {
            assert forall|k: nat| k < write_device::total(count) && write_device::is_write(k, count) && machine.stable.contains(k)
                implies #[trigger] write_media::address(images, k) != block by {
                if 8 + count <= k < 8 + 2 * count {
                    let index = (k - (8 + count)) as int;
                    assert(images.tx.original[index].block != block);
                }
            }
            write_media::apply_frames_every_unwritten_block(before, images, machine.stable, write_device::total(count), block);
        }
    }
}

proof fn bounded_patches_cannot_select_a_later_partition_block(images: Seq<ImageView>, blocks: u32, block: int)
    requires block >= blocks, forall|i: int| 0 <= i < images.len() ==> (#[trigger] images[i]).block < blocks,
    ensures patch_set::selected(images, block).is_none(),
{
    if exists|i: int| 0 <= i < images.len() && (#[trigger] images[i]).block as int == block {
        let i = choose|i: int| 0 <= i < images.len() && (#[trigger] images[i]).block as int == block;
        assert(images[i].block < blocks);
    }
}

pub proof fn validated_final_image_preserves_extra_partition_bytes(admission: AdmissionView, images: Images, index: int)
    requires writer_admission::valid(admission, images), images.tx.layout.fs_blocks as nat * 4096 <= index < admission.boot.source.len(),
    ensures writer_admission::final_source(admission.boot.source, images)[index] == admission.boot.source[index],
{
    hide(crate::crc::fold);
    reveal(writer_admission::valid);
    reveal(write_io::valid_images);
    let blocks = images.tx.layout.fs_blocks;
    let logical = index / 4096;
    assert(logical >= blocks);
    let logs = write_io::log_images(images);
    assert forall|i: int| 0 <= i < logs.len() implies (#[trigger] logs[i]).block < blocks by {
        assert(logs[i].block as int == images.journal_block as int + 1 + i);
    }
    assert forall|i: int| 0 <= i < images.tx.original.len() implies (#[trigger] images.tx.original[i]).block < blocks by {
        assert(crate::replay::payload_for_layout(images.tx.tags[i], images.tx.payloads[i], images.tx.sequence, images.tx.seed, images.tx.layout));
    }
    let marker = seq![ImageView { block: 0, image: images.dirty }];
    let retirement = seq![ImageView { block: images.journal_block, image: images.tail }];
    bounded_patches_cannot_select_a_later_partition_block(marker, blocks, logical);
    bounded_patches_cannot_select_a_later_partition_block(logs, blocks, logical);
    bounded_patches_cannot_select_a_later_partition_block(images.tx.original, blocks, logical);
    bounded_patches_cannot_select_a_later_partition_block(retirement, blocks, logical);
}

#[verifier::rlimit(30)]
pub proof fn successful_durable_writer_is_the_complete_validated_filesystem_image(admission: AdmissionView, images: Images, machine: Machine)
    requires writer_admission::valid(admission, images), write_device::inv(machine, images.tx.payloads.len()),
        machine.io.phase is Done, !machine.io.pending, !machine.io.faulted,
    ensures disk_image::flat_bytes(write_media::disk(machine, disk_image::initial_disk(admission.boot.source, images.tx.layout.fs_blocks), images),
            admission.boot.source, images.tx.layout.fs_blocks) == admission.after.index.volume.index.source,
        namespace::valid(admission.after),
        forall|k: nat| !#[trigger] write_device::enabled(machine, write_device::Event::Persist(k)),
{
    hide(crate::crc::fold);
    hide(write_media::apply);
    an_admitted_source_supplies_the_physical_writer_context(admission, images);
    let source = admission.boot.source;
    let blocks = images.tx.layout.fs_blocks;
    let before = disk_image::initial_disk(source, blocks);
    let media = write_media::disk(machine, before, images);
    write_device::successful_completion_is_durable_and_has_no_late_persistence(machine, images.tx.payloads.len());
    write_media::apply_keeps_every_existing_block(before, images, machine.stable, write_device::total(images.tx.payloads.len()));
    admission_byte_shapes(admission, images);
    assert(disk_image::flat_bytes(media, source, blocks) =~= admission.after.index.volume.index.source) by {
        assert forall|i: int| 0 <= i < source.len() implies
            #[trigger] disk_image::flat_bytes(media, source, blocks)[i] == admission.after.index.volume.index.source[i] by {
            if i < blocks as nat * 4096 {
                let block = (i / 4096) as u32;
                assert(block as int == i / 4096);
                assert(block < blocks);
                disk_image::initial_disk_addresses_are_exactly_the_filesystem_range(source, blocks, block);
                successful_media_has_exactly_the_expected_block(admission, images, machine, block);
                validated_final_image_has_the_expected_block(admission, images, block);
                assert(media.dom().contains(block));
                assert(media[block] == admission.after.index.volume.index.source.subrange(block as int * 4096, (block as int + 1) * 4096));
                assert(media[block].len() == 4096);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, 4096);
                assert(media[block][i % 4096] == admission.after.index.volume.index.source[i]);
            } else {
                validated_final_image_preserves_extra_partition_bytes(admission, images, i);
            }
        }
    }
}

pub proof fn every_admitted_writer_has_a_finite_validated_completion(admission: AdmissionView, images: Images)
    -> (r: (Seq<Machine>, Seq<write_device::Event>))
    requires writer_admission::valid(admission, images),
    ensures write_device::execution(r.0, r.1, images.tx.payloads.len()), r.0[0] == write_device::initial(),
        r.0.last().io.phase is Done, !r.0.last().io.pending, !r.0.last().io.faulted,
        disk_image::flat_bytes(write_media::disk(r.0.last(), disk_image::initial_disk(admission.boot.source, images.tx.layout.fs_blocks), images),
            admission.boot.source, images.tx.layout.fs_blocks) == admission.after.index.volume.index.source,
        namespace::valid(admission.after),
{
    reveal(writer_admission::valid);
    reveal(write_io::valid_images);
    let count = images.tx.payloads.len();
    write_device::initialization(count);
    let (states, events) = write_device::failure_free_io_has_a_finite_successful_execution(write_device::initial(), count);
    write_device::every_finite_io_interleaving(states, events, count);
    successful_durable_writer_is_the_complete_validated_filesystem_image(admission, images, states.last());
    (states, events)
}

}
