// SPDX-License-Identifier: MPL-2.0

//! Bootstrap preservation under complete-block mixtures with fixed identity.
//! The physical recovery module supplies the mixtures; no device/source-capture
//! or mount authority follows from these immutable-source facts alone.

use vstd::prelude::*;
use crate::{allocation::{self, AllocationView}, bootstrap::{self, BootstrapView}, bootstrap_identity,
    bytes, group, group_index, group_metadata, layout, superblock};

verus! {

pub open spec fn same_locator_geometry(before: BootstrapView, after: BootstrapView) -> bool {
    before.source.len() == after.source.len() && before.layout == after.layout && before.table == after.table
        && before.blocks == after.blocks && before.inodes == after.inodes && before.ipg == after.ipg && before.metadata_seed == after.metadata_seed
}

proof fn the_same_locator_inputs_give_an_admissible_source(before: BootstrapView, source: Seq<u8>)
    requires bootstrap::valid(before), source.len() == before.source.len(),
        superblock::accepted(source.subrange(1024, 2048), source.len() as u64),
        bytes::le32(source, 1024) == before.inodes, bytes::le32(source, 1028) == before.blocks,
        bytes::le32(source, 1064) == before.ipg, bytes::le32(source, 4104) == before.table,
        superblock::metadata_seed(source.subrange(1024, 2048)) == before.metadata_seed,
        group::accepted_with_features(source.subrange(4096, 4096 + superblock::descriptor_bytes(source.subrange(1024, 2048)) as int),
            0, before.blocks, before.ipg, before.metadata_seed, superblock::flex_bg(source.subrange(1024, 2048))),
        source.subrange(before.table as int * 4096 + 1792, before.table as int * 4096 + 2048) == bootstrap::journal_inode(before),
    ensures bootstrap::admissible(source), same_locator_geometry(before, bootstrap::projection(source)),
{
    hide(crate::crc::fold);
    hide(superblock::accepted);
    hide(group::accepted_with_features);
    hide(layout::admitted);
    let tentative = BootstrapView { source, ..before };
    let candidate = BootstrapView { seed: crate::crc::fold(0xffffffff, bootstrap::journal_identity(tentative)), ..tentative };
    assert(bootstrap::valid(candidate)) by { reveal(bootstrap::valid); }
    bootstrap::every_valid_bootstrap_is_the_unique_source_projection(candidate);
}

proof fn primary_source_projection(before: BootstrapView, source: Seq<u8>)
    requires bootstrap::valid(before), source.len() == before.source.len(),
        bootstrap_identity::primary_fixed(before.source.subrange(0, 4096), source.subrange(0, 4096)),
    ensures bytes::le32(source, 1024) == before.inodes, bytes::le32(source, 1028) == before.blocks,
        bytes::le32(source, 1064) == before.ipg,
        superblock::metadata_seed(source.subrange(1024, 2048)) == before.metadata_seed,
        superblock::descriptor_bytes(source.subrange(1024, 2048)) == superblock::descriptor_bytes(before.source.subrange(1024, 2048)),
        superblock::flex_bg(source.subrange(1024, 2048)) == superblock::flex_bg(before.source.subrange(1024, 2048)),
{
    hide(crate::crc::fold);
    reveal(bootstrap::valid);
    bootstrap_identity::fixed_primary_identity_keeps_bootstrap_geometry_and_checksum_domain(before.source.subrange(0, 4096), source.subrange(0, 4096));
    assert(before.source.subrange(0, 4096).subrange(1024, 2048) =~= before.source.subrange(1024, 2048));
    assert(source.subrange(0, 4096).subrange(1024, 2048) =~= source.subrange(1024, 2048));
}

#[verifier::rlimit(30)]
pub proof fn a_bootstrap_preserving_allocation_image_has_an_admissible_journal_locator(before: BootstrapView, after: AllocationView)
    requires bootstrap::valid(before), allocation::valid(after), bootstrap_identity::preserved(before, after.index.source),
    ensures bootstrap::admissible(after.index.source), same_locator_geometry(before, bootstrap::projection(after.index.source)),
        after.index.blocks == before.blocks, after.index.inodes == before.inodes, after.index.ipg == before.ipg,
        after.index.seed == before.metadata_seed, after.index.groups[0].inode_table == before.table,
{
    hide(crate::crc::fold);
    hide(superblock::accepted);
    hide(group::accepted_with_features);
    hide(layout::admitted);
    primary_source_projection(before, after.index.source);
    bootstrap_identity::preserved_group_zero_addresses_keep_the_journal_inode_coordinate(before, after.index.source);
    reveal(allocation::valid);
    reveal(group_index::valid);
    group_index::every_checked_group_retains_its_source_and_geometry(after.index, 0);
    let meta = after.index.groups[0];
    reveal(group_metadata::valid);
    let source = after.index.source;
    let tentative = BootstrapView { source, ..before };
    let candidate = BootstrapView { seed: crate::crc::fold(0xffffffff, bootstrap::journal_identity(tentative)), ..tentative };
    assert(bootstrap::journal_inode(candidate) == bootstrap::journal_inode(before));
    assert(bootstrap::valid(candidate)) by {
        reveal(bootstrap::valid);
        assert(meta.descriptor == source.subrange(4096, 4096 + superblock::descriptor_bytes(source.subrange(1024, 2048)) as int));
    }
    bootstrap::every_valid_bootstrap_is_the_unique_source_projection(candidate);
    assert(meta.inode_table == before.table);
}

#[verifier::rlimit(30)]
proof fn mixed_primary_keeps_the_admitted_locator_inputs(before: BootstrapView, after: BootstrapView, source: Seq<u8>)
    requires bootstrap::valid(before), bootstrap::valid(after), same_locator_geometry(before, after),
        bootstrap_identity::primary_fixed(before.source.subrange(0, 4096), after.source.subrange(0, 4096)),
        source.len() == before.source.len(),
        source.subrange(0, 4096) == before.source.subrange(0, 4096) || source.subrange(0, 4096) == after.source.subrange(0, 4096),
    ensures source.len() >= 8192,
        superblock::accepted(source.subrange(1024, 2048), source.len() as u64),
        bytes::le32(source, 1024) == before.inodes, bytes::le32(source, 1028) == before.blocks, bytes::le32(source, 1064) == before.ipg,
        superblock::metadata_seed(source.subrange(1024, 2048)) == before.metadata_seed,
        superblock::descriptor_bytes(source.subrange(1024, 2048)) == superblock::descriptor_bytes(before.source.subrange(1024, 2048)),
        superblock::flex_bg(source.subrange(1024, 2048)) == superblock::flex_bg(before.source.subrange(1024, 2048)),
{
    hide(crate::crc::fold);
    hide(superblock::accepted);
    hide(group::accepted_with_features);
    hide(layout::admitted);
    assert(bootstrap_identity::primary_fixed(before.source.subrange(0, 4096), source.subrange(0, 4096)));
    primary_source_projection(before, source);
    assert(source.len() >= 8192) by { reveal(bootstrap::valid); }
    assert(superblock::accepted(source.subrange(1024, 2048), source.len() as u64)) by {
        reveal(bootstrap::valid);
        assert(source.subrange(1024, 2048) == source.subrange(0, 4096).subrange(1024, 2048));
        assert(before.source.subrange(1024, 2048) == before.source.subrange(0, 4096).subrange(1024, 2048));
        assert(after.source.subrange(1024, 2048) == after.source.subrange(0, 4096).subrange(1024, 2048));
    }
}

#[verifier::rlimit(30)]
proof fn mixed_descriptors_keep_the_admitted_locator_inputs(before: BootstrapView, after: BootstrapView, source: Seq<u8>)
    requires bootstrap::valid(before), bootstrap::valid(after), same_locator_geometry(before, after),
        bootstrap_identity::primary_fixed(before.source.subrange(0, 4096), after.source.subrange(0, 4096)),
        source.len() == before.source.len(),
        superblock::descriptor_bytes(source.subrange(1024, 2048)) == superblock::descriptor_bytes(before.source.subrange(1024, 2048)),
        superblock::flex_bg(source.subrange(1024, 2048)) == superblock::flex_bg(before.source.subrange(1024, 2048)),
        source.subrange(4096, 8192) == before.source.subrange(4096, 8192) || source.subrange(4096, 8192) == after.source.subrange(4096, 8192),
    ensures bytes::le32(source, 4104) == before.table,
        group::accepted_with_features(source.subrange(4096, 4096 + superblock::descriptor_bytes(source.subrange(1024, 2048)) as int),
            0, before.blocks, before.ipg, before.metadata_seed, superblock::flex_bg(source.subrange(1024, 2048))),
{
    hide(crate::crc::fold);
    hide(superblock::accepted);
    hide(group::accepted_with_features);
    hide(layout::admitted);
    primary_source_projection(before, after.source);
    assert(source.len() >= 8192 && before.source.len() >= 8192 && after.source.len() >= 8192) by { reveal(bootstrap::valid); }
    let width = superblock::descriptor_bytes(before.source.subrange(1024, 2048)) as int;
    assert(width == 32 || width == 64);
    assert(source.subrange(4096, 4096 + width) == source.subrange(4096, 8192).subrange(0, width));
    assert(before.source.subrange(4096, 4096 + width) == before.source.subrange(4096, 8192).subrange(0, width));
    assert(after.source.subrange(4096, 4096 + width) == after.source.subrange(4096, 8192).subrange(0, width));
    assert(bytes::le32(source, 4104) == before.table) by {
        reveal(bootstrap::valid);
        assert(bytes::le32(source.subrange(4096, 8192), 8) == bytes::le32(source, 4104));
        assert(bytes::le32(before.source.subrange(4096, 8192), 8) == bytes::le32(before.source, 4104));
        assert(bytes::le32(after.source.subrange(4096, 8192), 8) == bytes::le32(after.source, 4104));
    }
    assert(group::accepted_with_features(source.subrange(4096, 4096 + width), 0, before.blocks, before.ipg, before.metadata_seed,
        superblock::flex_bg(source.subrange(1024, 2048)))) by { reveal(bootstrap::valid); }
}

pub proof fn complete_bootstrap_block_mixtures_keep_the_same_admitted_locator(before: BootstrapView, after: BootstrapView, source: Seq<u8>)
    requires bootstrap::valid(before), bootstrap::valid(after), same_locator_geometry(before, after),
        bootstrap_identity::primary_fixed(before.source.subrange(0, 4096), after.source.subrange(0, 4096)),
        source.len() == before.source.len(),
        source.subrange(0, 4096) == before.source.subrange(0, 4096) || source.subrange(0, 4096) == after.source.subrange(0, 4096),
        source.subrange(4096, 8192) == before.source.subrange(4096, 8192) || source.subrange(4096, 8192) == after.source.subrange(4096, 8192),
        source.subrange(before.table as int * 4096 + 1792, before.table as int * 4096 + 2048) == bootstrap::journal_inode(before),
    ensures bootstrap::admissible(source), same_locator_geometry(before, bootstrap::projection(source)),
{
    mixed_primary_keeps_the_admitted_locator_inputs(before, after, source);
    mixed_descriptors_keep_the_admitted_locator_inputs(before, after, source);
    the_same_locator_inputs_give_an_admissible_source(before, source);
}

/// Concurrent checkpoints can expose a primary and descriptor from different
/// validated prefixes. Neither block needs to come from one common endpoint.
pub proof fn independently_admitted_bootstrap_blocks_keep_the_same_locator(before: BootstrapView,
    primary: BootstrapView, descriptors: BootstrapView, source: Seq<u8>)
    requires bootstrap::valid(before), bootstrap::valid(primary), bootstrap::valid(descriptors),
        same_locator_geometry(before, primary), same_locator_geometry(before, descriptors),
        bootstrap_identity::primary_fixed(before.source.subrange(0, 4096), primary.source.subrange(0, 4096)),
        bootstrap_identity::primary_fixed(before.source.subrange(0, 4096), descriptors.source.subrange(0, 4096)),
        source.len() == before.source.len(), source.subrange(0, 4096) == primary.source.subrange(0, 4096),
        source.subrange(4096, 8192) == descriptors.source.subrange(4096, 8192),
        source.subrange(before.table as int * 4096 + 1792, before.table as int * 4096 + 2048) == bootstrap::journal_inode(before),
    ensures bootstrap::admissible(source), same_locator_geometry(before, bootstrap::projection(source)),
{
    mixed_primary_keeps_the_admitted_locator_inputs(before, primary, source);
    mixed_descriptors_keep_the_admitted_locator_inputs(before, descriptors, source);
    the_same_locator_inputs_give_an_admissible_source(before, source);
}

}
