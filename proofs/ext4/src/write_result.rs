// SPDX-License-Identifier: MPL-2.0

//! File-read results through an independently validated result image.
//! This does not establish live-reader publication or kernel/device authority.

use vstd::prelude::*;
use crate::{allocated_inode::{self, NodeView}, allocation::{self, AllocationView}, bytes,
    content_write::{self, WriteView}, disk_image, extent_claims, extent_span::{self, SpanView}, extent_tree, extent_tree_model,
    file_read, group, group_index, group_metadata, inode, inode_projection, inode_size, inode_table, inode_touch, patch_set, write_frame, write_io::Images,
    writer_admission::{self, AdmissionView}, writer_image, write_device::{self, Machine}, write_media};

verus! {

pub open spec fn result_admission(v: WriteView, admission: AdmissionView, images: Images, seconds: int, nanos: nat, after: AllocationView) -> bool {
    write_frame::timed_admission(v, admission, images, seconds, nanos) && allocation::valid(after)
        && after.index.source == writer_admission::final_source(admission.boot.source, images)
}

pub open spec fn result_node(v: WriteView, after: AllocationView) -> NodeView { allocated_inode::source_view(after, v.node.number) }

proof fn result_geometry(v: WriteView, admission: AdmissionView, images: Images, seconds: int, nanos: nat, after: AllocationView)
    requires result_admission(v, admission, images, seconds, nanos, after),
    ensures allocated_inode::valid(v.node), allocation::valid(v.node.volume),
        group_index::valid(v.node.volume.index), group_index::valid(after.index),
        0 < v.node.volume.index.groups.len() <= 32, v.node.volume.index.ipg > 0,
        0 < v.node.number <= v.node.volume.index.inodes,
        v.node.volume.index.blocks as nat * 4096 <= v.node.volume.index.source.len(),
        after.index.blocks as nat * 4096 <= after.index.source.len(),
        v.node.volume.census.roles.len() == v.node.volume.index.blocks, v.node.volume.journal.fs_blocks == v.node.volume.index.blocks,
        v.node.volume.index.blocks == after.index.blocks, v.node.volume.index.inodes == after.index.inodes,
        v.node.volume.index.ipg == after.index.ipg, v.node.volume.index.seed == after.index.seed,
        v.node.volume.index.groups.len() == after.index.groups.len(),
        inode_table::start(v.node.volume.index, v.node.number) == inode_table::start(after.index, v.node.number),
        allocated_inode::live(v.node.volume.index, v.node.number),
        forall|g: int| 0 <= g < v.node.volume.index.groups.len() ==> (#[trigger] v.node.volume.index.groups[g]).descriptor == after.index.groups[g].descriptor
            && v.node.volume.index.groups[g].inode_bitmap == after.index.groups[g].inode_bitmap
            && v.node.volume.index.groups[g].inode_table == after.index.groups[g].inode_table,
{
    hide(file_read::maps);
    hide(crate::crc::fold);
    reveal(content_write::valid);
    reveal(allocated_inode::valid);
    reveal(allocation::valid);
    reveal(allocation::journal_matches);
    reveal(group_index::valid);
    write_frame::a_timed_write_preserves_the_primary_identity_and_complete_gdt(v, admission, images, seconds, nanos);
    inode_projection::a_preserved_primary_and_gdt_keep_index_geometry_and_group_addresses(v.node.volume.index, after.index);
    inode_projection::a_preserved_primary_and_gdt_keep_every_inode_coordinate(v.node.volume.index, after.index, v.node.number);
}

proof fn the_inode_bitmap_is_outside_its_table(meta: group_metadata::GroupView)
    requires group_metadata::valid(meta),
    ensures meta.table_blocks == meta.ipg / 16, meta.inode_bitmap < meta.blocks,
        !(meta.inode_table <= meta.inode_bitmap < meta.inode_table as nat + meta.ipg as nat / 16),
{
    hide(crate::crc::fold);
    reveal(group_metadata::valid);
    reveal(group::accepted_with_features);
}

proof fn equal_inode_bitmap_sources_have_equal_logical_bits(before: group_metadata::GroupView, after: group_metadata::GroupView)
    requires group_metadata::valid(before), group_metadata::valid(after), before.descriptor == after.descriptor, before.ipg == after.ipg,
        group::inode_uninitialized(before.descriptor) || before.source.subrange(before.inode_bitmap as int * 4096,
            (before.inode_bitmap as int + 1) * 4096) == after.source.subrange(after.inode_bitmap as int * 4096, (after.inode_bitmap as int + 1) * 4096),
    ensures before.inodes.raw == after.inodes.raw,
{
    hide(crate::crc::fold);
    reveal(group_metadata::valid);
}

#[verifier::rlimit(30)]
proof fn the_written_inode_stays_allocated_in_the_actual_result(v: WriteView, admission: AdmissionView, images: Images,
    seconds: int, nanos: nat, after: AllocationView)
    requires result_admission(v, admission, images, seconds, nanos, after),
    ensures allocated_inode::live(after.index, v.node.number),
{
    hide(file_read::maps);
    hide(crate::crc::fold);
    hide(inode_touch::sealed_bytes);
    result_geometry(v, admission, images, seconds, nanos, after);
    let volume = v.node.volume;
    allocation::every_inode_table_position_has_a_metadata_role(volume, v.node.number);
    let g = ((v.node.number as int - 1) / volume.index.ipg as int) as u32;
    assert(g as int == (v.node.number as int - 1) / volume.index.ipg as int);
    let before_group = volume.index.groups[g as int];
    let after_group = after.index.groups[g as int];
    group_index::every_checked_group_retains_its_source_and_geometry(volume.index, g as int);
    group_index::every_checked_group_retains_its_source_and_geometry(after.index, g as int);
    if !group::inode_uninitialized(before_group.descriptor) {
        let block = before_group.inode_bitmap;
        allocation::every_group_inode_bitmap_has_a_metadata_role(volume, g);
        allocation::the_primary_superblock_and_descriptor_have_reserved_roles(volume);
        assert(block != 0 && block != v.image.block) by { reveal(content_write::valid); }
        the_inode_bitmap_is_outside_its_table(before_group);
        let metadata = content_write::timed_inode_image(v, seconds, nanos);
        assert(block != metadata.block);
        if volume.journal.start <= block < volume.journal.start as nat + volume.journal.journal_blocks {
            allocation::the_internal_journal_has_only_journal_roles(volume, block);
            assert(false);
        }
        assert(patch_set::selected(images.tx.original, block as int).is_none()) by {
            if patch_set::selected(images.tx.original, block as int).is_some() {
                let i = choose|i: int| 0 <= i < images.tx.original.len() && (#[trigger] images.tx.original[i]).block as int == block;
                assert(i == 0 || i == 1);
            }
        }
        writer_image::blocks_outside_the_home_journal_and_primary_targets_retain_their_source_bytes(admission, images, block);
    }
    equal_inode_bitmap_sources_have_equal_logical_bits(before_group, after_group);
    assert(before_group.inodes.raw == after_group.inodes.raw);
}

proof fn equal_read_fields_have_the_same_inode_projection(before: NodeView, after: AllocationView)
    requires before == allocated_inode::source_view(before.volume, before.number),
        inode_table::raw(after.index, before.number).len() == 256, inode_table::raw(before.volume.index, before.number).len() == 256,
        inode_table::raw(after.index, before.number).subrange(0, 8) == inode_table::raw(before.volume.index, before.number).subrange(0, 8),
        inode_table::raw(after.index, before.number).subrange(20, 124) == inode_table::raw(before.volume.index, before.number).subrange(20, 124),
    ensures allocated_inode::source_view(after, before.number) == (NodeView { volume: after, ..before }),
        bytes::le32(inode_table::raw(after.index, before.number), 100) == bytes::le32(inode_table::raw(before.volume.index, before.number), 100),
        extent_claims::depth(after.index, before.number) == extent_claims::depth(before.volume.index, before.number),
{
    let a = inode_table::raw(before.volume.index, before.number);
    let b = inode_table::raw(after.index, before.number);
    assert forall|i: int| 0 <= i < 8 || 20 <= i < 124 implies (#[trigger] b[i]) == a[i] by {
        if i < 8 {
            assert(b.subrange(0, 8)[i] == b[i] && a.subrange(0, 8)[i] == a[i]);
        } else {
            assert(b.subrange(20, 124)[i - 20] == b[i] && a.subrange(20, 124)[i - 20] == a[i]);
        }
    }
}

proof fn equal_extent_context_fields_keep_the_same_context(v: WriteView, admission: AdmissionView, images: Images, after: AllocationView)
    requires after.index.source == writer_admission::final_source(admission.boot.source, images),
        after.index.blocks == v.node.volume.index.blocks, after.index.seed == v.node.volume.index.seed,
        inode_table::start(after.index, v.node.number) == inode_table::start(v.node.volume.index, v.node.number),
        bytes::le32(inode_table::raw(after.index, v.node.number), 100) == bytes::le32(inode_table::raw(v.node.volume.index, v.node.number), 100),
    ensures extent_claims::context(after.index, v.node.number) == write_frame::final_context(v, admission, images),
{
    hide(crate::crc::fold);
}

proof fn a_touched_inode_keeps_every_field_used_by_reads(raw: Seq<u8>, number: u32, inodes: u32, seed: u32,
    huge: bool, seconds: int, nanos: nat)
    requires inode::metadata_accepted_with_features(raw, number, inodes, seed, huge), crate::inode_time::representable(seconds, nanos),
    ensures inode_touch::sealed_bytes(raw, number, seed, seconds, nanos).subrange(0, 8) == raw.subrange(0, 8),
        inode_touch::sealed_bytes(raw, number, seed, seconds, nanos).subrange(20, 124) == raw.subrange(20, 124),
{
    hide(crate::crc::fold);
    hide(inode_touch::sealed_bytes);
    inode_touch::touching_times_preserves_inode_metadata_identity_and_validity(raw, number, inodes, seed, huge, seconds, nanos);
    let sealed = inode_touch::sealed_bytes(raw, number, seed, seconds, nanos);
    assert(sealed.subrange(0, 8) =~= raw.subrange(0, 8));
    assert(sealed.subrange(20, 124) =~= raw.subrange(20, 124));
}

#[verifier::rlimit(30)]
pub proof fn a_timed_write_keeps_the_actual_validated_inode_and_extent_coordinates(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat, after: AllocationView)
    requires result_admission(v, admission, images, seconds, nanos, after),
    ensures allocated_inode::valid(result_node(v, after)), allocated_inode::live(after.index, v.node.number),
        result_node(v, after) == (NodeView { volume: after, ..v.node }),
        extent_claims::context(after.index, v.node.number) == write_frame::final_context(v, admission, images),
        extent_claims::depth(after.index, v.node.number) == extent_claims::depth(v.node.volume.index, v.node.number),
{
    hide(file_read::maps);
    hide(crate::crc::fold);
    hide(inode_touch::sealed_bytes);
    result_geometry(v, admission, images, seconds, nanos, after);
    the_written_inode_stays_allocated_in_the_actual_result(v, admission, images, seconds, nanos, after);
    allocated_inode::a_live_source_projection_is_a_valid_inode(after, v.node.number);
    allocated_inode::checked_view_is_the_source_projection(v.node);
    write_frame::a_timed_write_has_the_exact_updated_inode_and_unchanged_extent_root(v, admission, images, seconds, nanos);
    let raw = inode_table::raw(v.node.volume.index, v.node.number);
    assert(inode::metadata_accepted_with_features(raw, v.node.number, v.node.volume.index.inodes, v.node.volume.index.seed,
        group_index::has_huge_files(v.node.volume.index))) by { reveal(allocated_inode::valid); }
    a_touched_inode_keeps_every_field_used_by_reads(raw, v.node.number, v.node.volume.index.inodes, v.node.volume.index.seed,
        group_index::has_huge_files(v.node.volume.index), seconds, nanos);
    assert(inode_table::raw(after.index, v.node.number) == inode_touch::sealed_bytes(raw, v.node.number, v.node.volume.index.seed, seconds, nanos));
    assert(raw.len() == 256 && inode_table::raw(after.index, v.node.number).len() == 256) by { reveal(allocated_inode::valid); }
    equal_read_fields_have_the_same_inode_projection(v.node, after);
    equal_extent_context_fields_keep_the_same_context(v, admission, images, after);
}

#[verifier::rlimit(30)]
pub proof fn a_timed_write_preserves_the_actual_inode_mappings(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat, after: AllocationView, logical: u32, physical: u32)
    requires result_admission(v, admission, images, seconds, nanos, after),
    ensures file_read::maps(v.node, logical, physical) == file_read::maps(result_node(v, after), logical, physical),
{
    hide(file_read::maps);
    hide(crate::crc::fold);
    a_timed_write_keeps_the_actual_validated_inode_and_extent_coordinates(v, admission, images, seconds, nanos, after);
    let before = extent_claims::context(v.node.volume.index, v.node.number);
    let next = extent_claims::context(after.index, v.node.number);
    let depth = extent_claims::depth(v.node.volume.index, v.node.number);
    if file_read::maps(v.node, logical, physical) {
        reveal(file_read::maps);
        let span = choose|span: SpanView| #[trigger] extent_tree_model::stored_mapping(before, extent_tree::root_node(before), depth, logical, span)
            && span.initialized && extent_span::mapping(span, logical) == Some(physical as u64);
        write_frame::a_timed_write_preserves_every_complete_extent_mapping(v, admission, images, seconds, nanos, logical, span);
        assert(exists|s: SpanView| #[trigger] extent_tree_model::stored_mapping(next, extent_tree::root_node(next), depth, logical, s)
            && s.initialized && extent_span::mapping(s, logical) == Some(physical as u64));
    }
    if file_read::maps(result_node(v, after), logical, physical) {
        reveal(file_read::maps);
        let span = choose|span: SpanView| #[trigger] extent_tree_model::stored_mapping(next, extent_tree::root_node(next), depth, logical, span)
            && span.initialized && extent_span::mapping(span, logical) == Some(physical as u64);
        write_frame::a_timed_write_preserves_every_complete_extent_mapping(v, admission, images, seconds, nanos, logical, span);
        assert(exists|s: SpanView| #[trigger] extent_tree_model::stored_mapping(before, extent_tree::root_node(before), depth, logical, s)
            && s.initialized && extent_span::mapping(s, logical) == Some(physical as u64));
    }
}

proof fn a_checked_inode_offset_has_no_logical_block_truncation(node: NodeView, offset: u64)
    requires allocated_inode::valid(node), offset < node.size,
    ensures (((offset / 4096) as u32) as nat) == offset as nat / 4096,
{
    hide(crate::crc::fold);
    reveal(allocated_inode::valid);
    inode_size::offsets_never_truncate_to_a_different_logical_block(4096, group_index::has_huge_files(node.volume.index), node.size, offset);
}

#[verifier::rlimit(30)]
proof fn a_replaced_file_byte_has_the_requested_value(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat, after: AllocationView, query: u64)
    requires result_admission(v, admission, images, seconds, nanos, after), query < v.node.size,
        v.offset <= query < v.offset as nat + v.data.len(),
    ensures file_read::byte_at(result_node(v, after), query) == v.data[query as int - v.offset as int],
{
    hide(file_read::maps);
    hide(file_read::byte_at);
    hide(crate::crc::fold);
    hide(inode_touch::sealed_bytes);
    hide(content_write::timed_images);
    hide(writer_admission::final_source);
    result_geometry(v, admission, images, seconds, nanos, after);
    a_timed_write_keeps_the_actual_validated_inode_and_extent_coordinates(v, admission, images, seconds, nanos, after);
    let node = result_node(v, after);
    let logical = (query / 4096) as u32;
    reveal(content_write::valid);
    let index = query as int - v.offset as int;
    content_write::every_replaced_byte_stays_in_the_same_logical_block(v, index);
    a_timed_write_preserves_the_actual_inode_mappings(v, admission, images, seconds, nanos, after, logical, v.image.block);
    assert(file_read::maps(node, logical, v.image.block));
    file_read::an_initialized_file_byte_is_the_exact_source_byte(node, query, v.image.block);
    write_frame::a_timed_write_has_the_exact_content_home(v, admission, images, seconds, nanos);
    assert(after.index.source[v.image.block as int * 4096 + query as int % 4096] == v.image.image[query as int % 4096]);
}

proof fn the_content_target_has_only_its_original_logical_block(v: WriteView, query: u64)
    requires content_write::valid(v), query < v.node.size, file_read::maps(v.node, (query / 4096) as u32, v.image.block),
    ensures query / 4096 == v.offset / 4096, file_read::owned(v.node, (query / 4096) as u32, v.image.block),
{
    hide(file_read::maps);
    hide(crate::crc::fold);
    reveal(content_write::valid);
    file_read::an_initialized_mapping_has_exact_ownership(v.node, (query / 4096) as u32, v.image.block);
    a_checked_inode_offset_has_no_logical_block_truncation(v.node, query);
    a_checked_inode_offset_has_no_logical_block_truncation(v.node, v.offset);
}

proof fn an_outside_byte_in_the_same_logical_block_is_outside_the_block_splice(offset: u64, length: nat, query: u64)
    requires query / 4096 == offset / 4096, !(offset <= query < offset as nat + length),
    ensures query as int % 4096 < offset as int % 4096 || offset as int % 4096 + length <= query as int % 4096,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(query as int, 4096);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(offset as int, 4096);
}

#[verifier::rlimit(30)]
proof fn an_outside_byte_in_the_content_block_is_unchanged(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat, after: AllocationView, query: u64)
    requires result_admission(v, admission, images, seconds, nanos, after), query < v.node.size,
        !(v.offset <= query < v.offset as nat + v.data.len()), file_read::maps(v.node, (query / 4096) as u32, v.image.block),
    ensures file_read::byte_at(result_node(v, after), query) == file_read::byte_at(v.node, query),
{
    hide(file_read::maps);
    hide(file_read::byte_at);
    hide(crate::crc::fold);
    hide(inode_touch::sealed_bytes);
    hide(content_write::timed_images);
    hide(writer_admission::final_source);
    result_geometry(v, admission, images, seconds, nanos, after);
    a_timed_write_keeps_the_actual_validated_inode_and_extent_coordinates(v, admission, images, seconds, nanos, after);
    let node = result_node(v, after);
    a_timed_write_preserves_the_actual_inode_mappings(v, admission, images, seconds, nanos, after, (query / 4096) as u32, v.image.block);
    file_read::an_initialized_file_byte_is_the_exact_source_byte(v.node, query, v.image.block);
    file_read::an_initialized_file_byte_is_the_exact_source_byte(node, query, v.image.block);
    the_content_target_has_only_its_original_logical_block(v, query);
    an_outside_byte_in_the_same_logical_block_is_outside_the_block_splice(v.offset, v.data.len(), query);
    content_write::bytes_outside_the_requested_content_span_are_preserved(v, query as int % 4096);
    write_frame::a_timed_write_has_the_exact_content_home(v, admission, images, seconds, nanos);
    assert(after.index.source[v.image.block as int * 4096 + query as int % 4096] == v.image.image[query as int % 4096]);
}

proof fn an_unselected_initialized_mapping_has_unchanged_block_bytes(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat, logical: u32, physical: u32)
    requires write_frame::timed_admission(v, admission, images, seconds, nanos),
        file_read::maps(v.node, logical, physical), physical != v.image.block,
    ensures physical < v.node.volume.index.blocks,
        writer_admission::final_source(admission.boot.source, images).subrange(physical as int * 4096, (physical as int + 1) * 4096)
            == v.node.volume.index.source.subrange(physical as int * 4096, (physical as int + 1) * 4096),
{
    hide(file_read::maps);
    hide(crate::crc::fold);
    hide(content_write::timed_images);
    hide(writer_admission::final_source);
    assert(allocated_inode::valid(v.node)) by { reveal(content_write::valid); }
    file_read::an_initialized_mapping_has_exact_ownership(v.node, logical, physical);
    write_frame::a_timed_write_preserves_every_unselected_file_or_extent_block(v, admission, images, seconds, nanos, physical);
}

proof fn equal_block_sources_have_equal_selected_bytes(before: Seq<u8>, after: Seq<u8>, block: u32, within: int)
    requires (block as nat + 1) * 4096 <= before.len(), (block as nat + 1) * 4096 <= after.len(), 0 <= within < 4096,
        before.subrange(block as int * 4096, (block as int + 1) * 4096) == after.subrange(block as int * 4096, (block as int + 1) * 4096),
    ensures before[block as int * 4096 + within] == after[block as int * 4096 + within],
{
    assert(before.subrange(block as int * 4096, (block as int + 1) * 4096)[within] == before[block as int * 4096 + within]);
    assert(after.subrange(block as int * 4096, (block as int + 1) * 4096)[within] == after[block as int * 4096 + within]);
}

#[verifier::rlimit(30)]
proof fn an_untargeted_initialized_block_byte_is_unchanged(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat, after: AllocationView, query: u64, physical: u32)
    requires result_admission(v, admission, images, seconds, nanos, after), query < v.node.size,
        physical != v.image.block, file_read::maps(v.node, (query / 4096) as u32, physical),
    ensures file_read::byte_at(result_node(v, after), query) == file_read::byte_at(v.node, query),
{
    hide(file_read::maps);
    hide(file_read::byte_at);
    hide(crate::crc::fold);
    hide(inode_touch::sealed_bytes);
    hide(content_write::timed_images);
    hide(writer_admission::final_source);
    result_geometry(v, admission, images, seconds, nanos, after);
    a_timed_write_keeps_the_actual_validated_inode_and_extent_coordinates(v, admission, images, seconds, nanos, after);
    let node = result_node(v, after);
    a_timed_write_preserves_the_actual_inode_mappings(v, admission, images, seconds, nanos, after, (query / 4096) as u32, physical);
    file_read::an_initialized_file_byte_is_the_exact_source_byte(v.node, query, physical);
    file_read::an_initialized_file_byte_is_the_exact_source_byte(node, query, physical);
    an_unselected_initialized_mapping_has_unchanged_block_bytes(v, admission, images, seconds, nanos, (query / 4096) as u32, physical);
    equal_block_sources_have_equal_selected_bytes(v.node.volume.index.source, after.index.source, physical, query as int % 4096);
    assert(after.index.source[physical as int * 4096 + query as int % 4096]
        == v.node.volume.index.source[physical as int * 4096 + query as int % 4096]);
}

proof fn an_unselected_initialized_file_byte_is_unchanged(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat, after: AllocationView, query: u64, physical: u32)
    requires result_admission(v, admission, images, seconds, nanos, after), query < v.node.size,
        !(v.offset <= query < v.offset as nat + v.data.len()), file_read::maps(v.node, (query / 4096) as u32, physical),
    ensures file_read::byte_at(result_node(v, after), query) == file_read::byte_at(v.node, query),
{
    hide(file_read::maps);
    hide(file_read::byte_at);
    hide(content_write::timed_images);
    hide(writer_admission::final_source);
    if physical == v.image.block {
        an_outside_byte_in_the_content_block_is_unchanged(v, admission, images, seconds, nanos, after, query);
    } else {
        an_untargeted_initialized_block_byte_is_unchanged(v, admission, images, seconds, nanos, after, query, physical);
    }
}

proof fn an_uninitialized_file_byte_stays_zero(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat, after: AllocationView, query: u64)
    requires result_admission(v, admission, images, seconds, nanos, after), query < v.node.size,
        !exists|physical: u32| #[trigger] file_read::maps(v.node, (query / 4096) as u32, physical),
    ensures file_read::byte_at(result_node(v, after), query) == 0, file_read::byte_at(v.node, query) == 0,
{
    hide(file_read::maps);
    hide(file_read::byte_at);
    hide(content_write::timed_images);
    hide(writer_admission::final_source);
    result_geometry(v, admission, images, seconds, nanos, after);
    a_timed_write_keeps_the_actual_validated_inode_and_extent_coordinates(v, admission, images, seconds, nanos, after);
    let node = result_node(v, after);
    let logical = (query / 4096) as u32;
    assert forall|physical: u32| !#[trigger] file_read::maps(node, logical, physical) by {
        a_timed_write_preserves_the_actual_inode_mappings(v, admission, images, seconds, nanos, after, logical, physical);
    }
    file_read::a_missing_initialized_mapping_reads_as_zero(v.node, query);
    file_read::a_missing_initialized_mapping_reads_as_zero(node, query);
}

pub proof fn a_timed_write_has_the_exact_logical_file_byte_result(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat, after: AllocationView, query: u64)
    requires result_admission(v, admission, images, seconds, nanos, after), query < v.node.size,
    ensures allocated_inode::valid(result_node(v, after)),
        file_read::byte_at(result_node(v, after), query) == if v.offset <= query < v.offset as nat + v.data.len() {
            v.data[query as int - v.offset as int]
        } else { file_read::byte_at(v.node, query) },
{
    hide(file_read::maps);
    hide(file_read::byte_at);
    hide(content_write::timed_images);
    hide(writer_admission::final_source);
    a_timed_write_keeps_the_actual_validated_inode_and_extent_coordinates(v, admission, images, seconds, nanos, after);
    let logical = (query / 4096) as u32;
    if v.offset <= query < v.offset as nat + v.data.len() {
        a_replaced_file_byte_has_the_requested_value(v, admission, images, seconds, nanos, after, query);
    } else if exists|physical: u32| #[trigger] file_read::maps(v.node, logical, physical) {
        let physical = choose|physical: u32| #[trigger] file_read::maps(v.node, logical, physical);
        an_unselected_initialized_file_byte_is_unchanged(v, admission, images, seconds, nanos, after, query, physical);
    } else {
        an_uninitialized_file_byte_stays_zero(v, admission, images, seconds, nanos, after, query);
    }
}

pub open spec fn media_source(admission: AdmissionView, images: Images, machine: Machine) -> Seq<u8> {
    disk_image::flat_bytes(write_media::disk(machine, disk_image::initial_disk(admission.boot.source, images.tx.layout.fs_blocks), images),
        admission.boot.source, images.tx.layout.fs_blocks)
}

pub proof fn a_successful_timed_writer_has_exact_durable_logical_file_bytes(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat, machine: Machine, after: AllocationView, query: u64)
    requires write_frame::timed_admission(v, admission, images, seconds, nanos),
        write_device::inv(machine, images.tx.payloads.len()), machine.io.phase is Done, !machine.io.pending, !machine.io.faulted,
        allocation::valid(after), after.index.source == media_source(admission, images, machine), query < v.node.size,
    ensures allocated_inode::valid(result_node(v, after)),
        file_read::byte_at(result_node(v, after), query) == if v.offset <= query < v.offset as nat + v.data.len() {
            v.data[query as int - v.offset as int]
        } else { file_read::byte_at(v.node, query) },
        forall|k: nat| !#[trigger] write_device::enabled(machine, write_device::Event::Persist(k)),
{
    hide(file_read::maps);
    hide(file_read::byte_at);
    hide(content_write::timed_images);
    hide(writer_admission::final_source);
    writer_image::successful_durable_writer_is_the_complete_validated_filesystem_image(admission, images, machine);
    assert(admission.after.index.volume.index.source == writer_admission::final_source(admission.boot.source, images)) by {
        reveal(writer_admission::valid);
    }
    a_timed_write_has_the_exact_logical_file_byte_result(v, admission, images, seconds, nanos, after, query);
}

}
