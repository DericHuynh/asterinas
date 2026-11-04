// SPDX-License-Identifier: MPL-2.0

//! Extent/source framing for the actual admitted timed-content writer image.
//! Root and external tree bytes survive all dirty/log/home/tail overlays.
//! Runtime exclusion, CortenMM origin and fresh-source read admission are separate.

use vstd::prelude::*;
use crate::{allocated_inode, allocation, block_claims, bytes, content_write::{self, WriteView},
    extent, extent_claims, extent_frame, extent_span::SpanView, extent_tree::{self, Context}, extent_tree_model,
    file_read, group_index, inode_group, inode_table, inode_time, inode_touch, patch_set,
    write_io::Images, writer_admission::{self, AdmissionView}, writer_image};

verus! {

pub open spec fn timed_admission(v: WriteView, admission: AdmissionView, images: Images, seconds: int, nanos: nat) -> bool {
    &&& content_write::valid(v) && inode_time::representable(seconds, nanos)
    &&& writer_admission::valid(admission, images)
    &&& admission.boot.source == v.node.volume.index.source && images.tx.layout == v.node.volume.journal
    &&& images.tx.original == content_write::timed_images(v, seconds, nanos)
}

pub open spec fn final_context(v: WriteView, admission: AdmissionView, images: Images) -> Context {
    Context { source: writer_admission::final_source(admission.boot.source, images),
        ..extent_claims::context(v.node.volume.index, v.node.number) }
}

proof fn candidate_source_facts(v: WriteView)
    requires content_write::valid(v),
    ensures allocation::valid(v.node.volume), group_index::valid(v.node.volume.index),
        v.node.volume.census.roles.len() == v.node.volume.index.blocks,
        v.node.volume.journal.fs_blocks == v.node.volume.index.blocks,
        v.image.block < v.node.volume.index.blocks,
        v.node.volume.census.roles[v.image.block as int].kind == 4,
        crate::inode::metadata_accepted_with_features(inode_table::raw(v.node.volume.index, v.node.number), v.node.number,
            v.node.volume.index.inodes, v.node.volume.index.seed, group_index::has_huge_files(v.node.volume.index)),
        extent_claims::accepted(v.node.volume.index, v.node.number),
        block_claims::mapped_claims(v.node.volume.census.roles, extent_claims::claims(v.node.volume.index, v.node.number)),
        0 < v.node.number <= v.node.volume.index.inodes,
{
    hide(file_read::maps);
    hide(crate::crc::fold);
    reveal(content_write::valid);
    reveal(allocated_inode::valid);
    reveal(allocation::valid);
    reveal(allocation::journal_matches);
    reveal(inode_group::ordinary_checked);
}

pub proof fn a_timed_write_preserves_every_unselected_file_or_extent_block(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat, block: u32)
    requires timed_admission(v, admission, images, seconds, nanos),
        block < v.node.volume.census.roles.len(), 4 <= v.node.volume.census.roles[block as int].kind <= 7,
        block != v.image.block,
    ensures writer_admission::final_source(admission.boot.source, images).subrange(block as int * 4096, (block as int + 1) * 4096)
        == v.node.volume.index.source.subrange(block as int * 4096, (block as int + 1) * 4096),
{
    hide(file_read::maps);
    hide(crate::crc::fold);
    candidate_source_facts(v);
    let volume = v.node.volume;
    allocation::the_primary_superblock_and_descriptor_have_reserved_roles(volume);
    allocation::every_inode_table_position_has_a_metadata_role(volume, v.node.number);
    if volume.journal.start <= block < volume.journal.start as nat + volume.journal.journal_blocks {
        allocation::the_internal_journal_has_only_journal_roles(volume, block);
        assert(false);
    }
    let metadata = content_write::timed_inode_image(v, seconds, nanos);
    assert(block != 0 && block != v.image.block && block != metadata.block);
    assert(patch_set::selected(images.tx.original, block as int).is_none()) by {
        if patch_set::selected(images.tx.original, block as int).is_some() {
            let i = choose|i: int| 0 <= i < images.tx.original.len() && (#[trigger] images.tx.original[i]).block as int == block;
            assert(i == 0 || i == 1);
        }
    }
    writer_image::blocks_outside_the_home_journal_and_primary_targets_retain_their_source_bytes(admission, images, block);
}

pub proof fn a_timed_write_preserves_every_external_extent_metadata_block(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat, block: u32)
    requires timed_admission(v, admission, images, seconds, nanos),
        block < v.node.volume.census.roles.len(), v.node.volume.census.roles[block as int].kind == 6,
    ensures writer_admission::final_source(admission.boot.source, images).subrange(block as int * 4096, (block as int + 1) * 4096)
        == v.node.volume.index.source.subrange(block as int * 4096, (block as int + 1) * 4096),
{
    candidate_source_facts(v);
    a_timed_write_preserves_every_unselected_file_or_extent_block(v, admission, images, seconds, nanos, block);
}

proof fn blocks_distinct_from_both_timed_homes_are_unselected(v: WriteView, images: Images, seconds: int, nanos: nat, block: u32)
    requires images.tx.original == content_write::timed_images(v, seconds, nanos),
        block != v.image.block, block != content_write::timed_inode_image(v, seconds, nanos).block,
    ensures patch_set::selected(images.tx.original, block as int).is_none(),
{
    if patch_set::selected(images.tx.original, block as int).is_some() {
        let i = choose|i: int| 0 <= i < images.tx.original.len() && (#[trigger] images.tx.original[i]).block as int == block;
        assert(i == 0 || i == 1);
    }
}

pub proof fn a_timed_write_preserves_the_primary_identity_and_complete_gdt(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat)
    requires timed_admission(v, admission, images, seconds, nanos),
    ensures crate::super_state::preserves(v.node.volume.index.source.subrange(0, 4096),
            writer_admission::final_source(admission.boot.source, images).subrange(0, 4096)),
        writer_admission::final_source(admission.boot.source, images).subrange(4096, 8192) == v.node.volume.index.source.subrange(4096, 8192),
{
    hide(file_read::maps);
    hide(crate::crc::fold);
    hide(inode_touch::sealed_bytes);
    candidate_source_facts(v);
    let volume = v.node.volume;
    allocation::the_primary_superblock_and_descriptor_have_reserved_roles(volume);
    allocation::every_inode_table_position_has_a_metadata_role(volume, v.node.number);
    assert(v.image.block != 0 && v.image.block != 1);
    let metadata = content_write::timed_inode_image(v, seconds, nanos);
    assert(metadata.block != 0 && metadata.block != 1);
    blocks_distinct_from_both_timed_homes_are_unselected(v, images, seconds, nanos, 0);
    blocks_distinct_from_both_timed_homes_are_unselected(v, images, seconds, nanos, 1);
    writer_image::an_untargeted_primary_is_exactly_the_dirty_identity_image(admission, images);
    assert(volume.journal.start > 1) by { reveal(allocation::valid); reveal(allocation::journal_matches); }
    writer_image::blocks_outside_the_home_journal_and_primary_targets_retain_their_source_bytes(admission, images, 1);
}

#[verifier::rlimit(30)]
pub proof fn a_timed_write_has_the_exact_content_home(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat)
    requires timed_admission(v, admission, images, seconds, nanos),
    ensures writer_admission::final_source(admission.boot.source, images).subrange(v.image.block as int * 4096,
        (v.image.block as int + 1) * 4096) == v.image.image,
{
    hide(file_read::maps);
    hide(crate::crc::fold);
    hide(inode_touch::sealed_bytes);
    candidate_source_facts(v);
    let volume = v.node.volume;
    if volume.journal.start <= v.image.block < volume.journal.start as nat + volume.journal.journal_blocks {
        allocation::the_internal_journal_has_only_journal_roles(volume, v.image.block);
        assert(false);
    }
    let metadata = content_write::timed_inode_image(v, seconds, nanos);
    allocation::every_inode_table_position_has_a_metadata_role(volume, v.node.number);
    assert(v.image.block != metadata.block);
    let index = if v.image.block < metadata.block { 0int } else { 1int };
    assert(images.tx.original[index] == v.image);
    assert(patch_set::valid(images.tx.original)) by { reveal(writer_admission::valid); }
    patch_set::one_target_has_one_image(images.tx.original, index);
    writer_image::a_selected_home_outside_the_journal_has_the_exact_final_bytes(admission, images, v.image.block, v.image.image);
}

#[verifier::rlimit(30)]
proof fn the_admitted_timed_inode_home_is_exact(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat)
    requires timed_admission(v, admission, images, seconds, nanos),
    ensures writer_admission::final_source(admission.boot.source, images).subrange(
        content_write::timed_inode_image(v, seconds, nanos).block as int * 4096,
        (content_write::timed_inode_image(v, seconds, nanos).block as int + 1) * 4096) == content_write::timed_inode_image(v, seconds, nanos).image,
        writer_admission::final_source(admission.boot.source, images).len() == v.node.volume.index.source.len(),
{
    hide(file_read::maps);
    hide(crate::crc::fold);
    hide(patch_set::apply);
    hide(inode_touch::sealed_bytes);
    hide(crate::transaction::wf);
    candidate_source_facts(v);
    let volume = v.node.volume;
    allocation::every_inode_table_position_has_a_metadata_role(volume, v.node.number);
    let position = inode_table::start(volume.index, v.node.number);
    let metadata = content_write::timed_inode_image(v, seconds, nanos);
    assert(metadata.block as nat == position / 4096);
    if volume.journal.start <= metadata.block < volume.journal.start as nat + volume.journal.journal_blocks {
        allocation::the_internal_journal_has_only_journal_roles(volume, metadata.block);
        assert(false);
    }
    let index = if v.image.block < metadata.block { 1int } else { 0int };
    assert(images.tx.original[index] == metadata);
    assert(patch_set::valid(images.tx.original)) by { reveal(writer_admission::valid); }
    patch_set::one_target_has_one_image(images.tx.original, index);
    writer_image::validated_final_image_has_the_expected_block(admission, images, metadata.block);
    assert(crate::write_io::valid_images(images)) by { reveal(writer_admission::valid); }
    reveal(crate::write_io::valid_images);
    assert(images.journal_block == volume.journal.start && metadata.block != images.journal_block);
    assert(writer_image::expected_block(admission.boot.source, images, metadata.block) == metadata.image);
}

proof fn the_sealed_inode_has_the_original_extent_root(raw: Seq<u8>, number: u32, inodes: u32, seed: u32,
    huge: bool, seconds: int, nanos: nat)
    requires crate::inode::metadata_accepted_with_features(raw, number, inodes, seed, huge), inode_time::representable(seconds, nanos),
    ensures raw.len() == 256, inode_touch::sealed_bytes(raw, number, seed, seconds, nanos).len() == 256,
        inode_touch::sealed_bytes(raw, number, seed, seconds, nanos).subrange(40, 100) == raw.subrange(40, 100),
{
    hide(crate::crc::fold);
    hide(inode_touch::sealed_bytes);
    inode_touch::touching_times_preserves_inode_metadata_identity_and_validity(raw, number, inodes, seed, huge, seconds, nanos);
    let sealed = inode_touch::sealed_bytes(raw, number, seed, seconds, nanos);
    assert(sealed.subrange(40, 100) =~= raw.subrange(40, 100)) by {
        assert forall|i: int| 0 <= i < 60 implies #[trigger] sealed.subrange(40, 100)[i] == raw.subrange(40, 100)[i] by {
            assert(!inode_touch::changed_byte(40 + i));
        }
    }
}

proof fn a_bounded_inode_splice_contains_the_exact_inode(source: Seq<u8>, position: nat, block: u32, inode: Seq<u8>)
    requires block as nat == position / 4096, position % 4096 <= 3840,
        (block as nat + 1) * 4096 <= source.len(), inode.len() == 256,
    ensures bytes::splice(source.subrange(block as int * 4096, (block as int + 1) * 4096), position as int % 4096, inode).len() == 4096,
        bytes::splice(source.subrange(block as int * 4096, (block as int + 1) * 4096), position as int % 4096, inode)
            .subrange(position as int % 4096, position as int % 4096 + 256) == inode,
{
    assert(bytes::splice(source.subrange(block as int * 4096, (block as int + 1) * 4096), position as int % 4096, inode)
        .subrange(position as int % 4096, position as int % 4096 + 256) =~= inode);
}

proof fn the_timed_inode_splice_has_the_exact_inode_and_root(v: WriteView, seconds: int, nanos: nat)
    requires content_write::valid(v), inode_time::representable(seconds, nanos),
    ensures content_write::timed_inode_image(v, seconds, nanos).image.len() == 4096,
        content_write::timed_inode_image(v, seconds, nanos).image.subrange(
            (inode_table::start(v.node.volume.index, v.node.number) % 4096) as int,
            (inode_table::start(v.node.volume.index, v.node.number) % 4096) as int + 256)
            == inode_touch::sealed_bytes(inode_table::raw(v.node.volume.index, v.node.number), v.node.number, v.node.volume.index.seed, seconds, nanos),
        inode_touch::sealed_bytes(inode_table::raw(v.node.volume.index, v.node.number), v.node.number, v.node.volume.index.seed, seconds, nanos).subrange(40, 100)
            == inode_table::raw(v.node.volume.index, v.node.number).subrange(40, 100),
        inode_table::start(v.node.volume.index, v.node.number) + 256 <= v.node.volume.index.source.len(),
        inode_table::start(v.node.volume.index, v.node.number) % 4096 <= 3840,
        inode_table::start(v.node.volume.index, v.node.number) + 256 <= 17592186044416,
        content_write::timed_inode_image(v, seconds, nanos).block as nat == inode_table::start(v.node.volume.index, v.node.number) / 4096,
        (content_write::timed_inode_image(v, seconds, nanos).block as nat + 1) * 4096 <= v.node.volume.index.source.len(),
        inode_table::raw(v.node.volume.index, v.node.number).len() == 256,
{
    hide(file_read::maps);
    hide(crate::crc::fold);
    hide(inode_touch::sealed_bytes);
    candidate_source_facts(v);
    let volume = v.node.volume;
    allocation::every_inode_table_position_has_a_metadata_role(volume, v.node.number);
    let position = inode_table::start(volume.index, v.node.number);
    let raw = inode_table::raw(volume.index, v.node.number);
    let sealed = inode_touch::sealed_bytes(raw, v.node.number, volume.index.seed, seconds, nanos);
    the_sealed_inode_has_the_original_extent_root(raw, v.node.number, volume.index.inodes,
        volume.index.seed, group_index::has_huge_files(volume.index), seconds, nanos);
    let block = content_write::timed_inode_image(v, seconds, nanos).block;
    assert(block as nat == position / 4096);
    assert((block as nat + 1) * 4096 <= volume.index.source.len());
    a_bounded_inode_splice_contains_the_exact_inode(volume.index.source, position, block, sealed);
}

pub proof fn a_timed_write_has_the_exact_updated_inode_and_unchanged_extent_root(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat)
    requires timed_admission(v, admission, images, seconds, nanos),
    ensures writer_admission::final_source(admission.boot.source, images).subrange(inode_table::start(v.node.volume.index, v.node.number) as int,
            inode_table::start(v.node.volume.index, v.node.number) as int + 256)
        == inode_touch::sealed_bytes(inode_table::raw(v.node.volume.index, v.node.number), v.node.number, v.node.volume.index.seed, seconds, nanos),
        extent_tree::root_node(extent_claims::context(v.node.volume.index, v.node.number)) == extent_tree::root_node(final_context(v, admission, images)),
{
    hide(file_read::maps);
    hide(crate::crc::fold);
    hide(patch_set::apply);
    hide(inode_touch::sealed_bytes);
    hide(content_write::timed_inode_image);
    hide(writer_admission::final_source);
    the_admitted_timed_inode_home_is_exact(v, admission, images, seconds, nanos);
    the_timed_inode_splice_has_the_exact_inode_and_root(v, seconds, nanos);
    let volume = v.node.volume;
    let position = inode_table::start(volume.index, v.node.number);
    let after = writer_admission::final_source(admission.boot.source, images);
    let raw = inode_table::raw(volume.index, v.node.number);
    let sealed = inode_touch::sealed_bytes(raw, v.node.number, volume.index.seed, seconds, nanos);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(position as int, 4096);
    let metadata = content_write::timed_inode_image(v, seconds, nanos);
    let within = (position % 4096) as int;
    assert(metadata.block as int * 4096 + within == position);
    assert(after.subrange(metadata.block as int * 4096, (metadata.block as int + 1) * 4096).subrange(within, within + 256)
        =~= after.subrange(position as int, position as int + 256));
    assert(after.subrange(position as int, position as int + 256) =~= sealed);
    let before = extent_claims::context(volume.index, v.node.number);
    assert(before.root as int == position as int + 40);
    assert(after.subrange(position as int + 40, position as int + 100) =~= sealed.subrange(40, 100));
    assert(raw.subrange(40, 100) =~= before.source.subrange(position as int + 40, position as int + 100));
    assert(after.subrange(before.root as int, before.root as int + 60) =~= before.source.subrange(before.root as int, before.root as int + 60));
}

#[verifier::rlimit(30)]
pub proof fn a_timed_write_preserves_every_complete_extent_mapping(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat, logical: u32, span: SpanView)
    requires timed_admission(v, admission, images, seconds, nanos),
    ensures extent_tree::context_valid(final_context(v, admission, images)),
        extent_tree::subtree_valid(final_context(v, admission, images), extent_tree::root_node(final_context(v, admission, images)),
            None, extent_claims::depth(v.node.volume.index, v.node.number), None, extent::MAX_LOGICAL_END),
        extent_claims::node_claims(final_context(v, admission, images), extent_tree::root_node(final_context(v, admission, images)), None,
            extent_claims::depth(v.node.volume.index, v.node.number), extent_claims::owner(v.node.volume.index, v.node.number))
            == extent_claims::claims(v.node.volume.index, v.node.number),
        extent_tree_model::stored_mapping(extent_claims::context(v.node.volume.index, v.node.number),
            extent_tree::root_node(extent_claims::context(v.node.volume.index, v.node.number)), extent_claims::depth(v.node.volume.index, v.node.number), logical, span)
            == extent_tree_model::stored_mapping(final_context(v, admission, images), extent_tree::root_node(final_context(v, admission, images)),
                extent_claims::depth(v.node.volume.index, v.node.number), logical, span),
{
    hide(file_read::maps);
    hide(crate::crc::fold);
    candidate_source_facts(v);
    a_timed_write_has_the_exact_updated_inode_and_unchanged_extent_root(v, admission, images, seconds, nanos);
    let before = extent_claims::context(v.node.volume.index, v.node.number);
    let after = final_context(v, admission, images);
    let claims = extent_claims::claims(v.node.volume.index, v.node.number);
    assert(extent_frame::metadata_unchanged(before, after, claims)) by {
        assert forall|claim: block_claims::Claim| #[trigger] claims.contains(claim) && claim.kind == 6 implies
            after.source.subrange(claim.start as int * before.size as int, (claim.start as int + 1) * before.size as int)
                == before.source.subrange(claim.start as int * before.size as int, (claim.start as int + 1) * before.size as int) by {
            let i = choose|i: int| 0 <= i < claims.len() && claims[i] == claim;
            reveal(block_claims::mapped_claims);
            assert(block_claims::valid_claim(claims[i], v.node.volume.census.roles.len()));
            assert(block_claims::covers(claims[i], claim.start as int));
            assert(v.node.volume.census.roles[claim.start as int].kind == 6);
            a_timed_write_preserves_every_external_extent_metadata_block(v, admission, images, seconds, nanos, claim.start);
        }
    }
    assert(extent_frame::same_geometry(before, after)) by { reveal(writer_admission::valid); }
    reveal(extent_claims::accepted);
    reveal(group_index::valid);
    extent_frame::preserving_the_root_and_owned_metadata_preserves_the_complete_tree(before, after,
        extent_claims::depth(v.node.volume.index, v.node.number), extent_claims::owner(v.node.volume.index, v.node.number), logical, span);
}

pub proof fn a_timed_write_preserves_every_external_xattr_block(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat, block: u32)
    requires timed_admission(v, admission, images, seconds, nanos),
        block < v.node.volume.census.roles.len(), v.node.volume.census.roles[block as int].kind == 7,
    ensures writer_admission::final_source(admission.boot.source, images).subrange(block as int * 4096, (block as int + 1) * 4096)
        == v.node.volume.index.source.subrange(block as int * 4096, (block as int + 1) * 4096),
{
    candidate_source_facts(v);
    a_timed_write_preserves_every_unselected_file_or_extent_block(v, admission, images, seconds, nanos, block);
}

proof fn sealed_inode_keeps_attribute_storage(raw: Seq<u8>, number: u32, inodes: u32, seed: u32, huge: bool, seconds: int, nanos: nat)
    requires crate::inode::metadata_accepted_with_features(raw, number, inodes, seed, huge), inode_time::representable(seconds, nanos),
    ensures inode_touch::sealed_bytes(raw, number, seed, seconds, nanos).subrange(160, 256) == raw.subrange(160, 256),
        crate::xattr::inode_address(inode_touch::sealed_bytes(raw, number, seed, seconds, nanos)) == crate::xattr::inode_address(raw),
{
    hide(crate::crc::fold); hide(inode_touch::sealed_bytes);
    inode_touch::touching_times_preserves_inode_metadata_identity_and_validity(raw, number, inodes, seed, huge, seconds, nanos);
    let sealed = inode_touch::sealed_bytes(raw, number, seed, seconds, nanos);
    assert(sealed.subrange(160, 256) =~= raw.subrange(160, 256));
    assert(crate::xattr::inode_address(sealed) == crate::xattr::inode_address(raw));
}

pub proof fn a_timed_write_preserves_inline_xattr_bytes_and_the_external_pointer(v: WriteView, admission: AdmissionView,
    images: Images, seconds: int, nanos: nat)
    requires timed_admission(v, admission, images, seconds, nanos),
    ensures writer_admission::final_source(admission.boot.source, images).subrange(inode_table::start(v.node.volume.index, v.node.number) as int + 160,
            inode_table::start(v.node.volume.index, v.node.number) as int + 256)
        == inode_table::raw(v.node.volume.index, v.node.number).subrange(160, 256),
        crate::xattr::inode_address(writer_admission::final_source(admission.boot.source, images).subrange(
            inode_table::start(v.node.volume.index, v.node.number) as int, inode_table::start(v.node.volume.index, v.node.number) as int + 256))
            == crate::xattr::inode_address(inode_table::raw(v.node.volume.index, v.node.number)),
{
    hide(file_read::maps); hide(crate::crc::fold);
    hide(inode_touch::sealed_bytes); hide(writer_admission::final_source);
    hide(patch_set::apply); hide(content_write::timed_inode_image);
    candidate_source_facts(v);
    allocation::every_inode_table_position_has_a_metadata_role(v.node.volume, v.node.number);
    the_admitted_timed_inode_home_is_exact(v, admission, images, seconds, nanos);
    a_timed_write_has_the_exact_updated_inode_and_unchanged_extent_root(v, admission, images, seconds, nanos);
    let volume = v.node.volume;
    let raw = inode_table::raw(volume.index, v.node.number);
    sealed_inode_keeps_attribute_storage(raw, v.node.number, volume.index.inodes,
        volume.index.seed, group_index::has_huge_files(volume.index), seconds, nanos);
    let position = inode_table::start(volume.index, v.node.number) as int;
    let after = writer_admission::final_source(admission.boot.source, images);
    vstd::seq::lemma_seq_subrange_composition(after, position, position + 256, 160, 256);
}

}
