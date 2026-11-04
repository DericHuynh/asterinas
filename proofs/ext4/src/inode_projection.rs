// SPDX-License-Identifier: MPL-2.0

//! Relate inode coordinates in independently validated source images.
//! Identity comes from exact source fields, never equality of CRC values.

use vstd::prelude::*;
use crate::{bytes, group_index::{self, IndexView}, group_metadata, inode_table, super_state, superblock};

verus! {

proof fn the_group_descriptor_is_its_exact_source_gdt_slice(index: IndexView, g: int)
    requires group_index::valid(index), 0 <= g < index.groups.len(),
    ensures index.groups[g].descriptor == index.source.subrange(4096, 8192).subrange(
            g * superblock::descriptor_bytes(index.source.subrange(1024, 2048)),
            (g + 1) * superblock::descriptor_bytes(index.source.subrange(1024, 2048))),
        index.groups[g].inode_table as nat == bytes::le32(index.groups[g].descriptor, 8),
        index.groups[g].inode_bitmap as nat == bytes::le32(index.groups[g].descriptor, 4),
        index.groups[g].block_bitmap as nat == bytes::le32(index.groups[g].descriptor, 0),
{
    hide(crate::crc::fold);
    reveal(group_index::valid);
    let meta = index.groups[g];
    group_index::every_checked_group_retains_its_source_and_geometry(index, g);
    assert(meta.source == index.source && meta.number as int == g && group_metadata::valid(meta));
    reveal(group_metadata::valid);
    let width = superblock::descriptor_bytes(index.source.subrange(1024, 2048));
    assert(width == 32 || width == 64);
    assert(0 <= g * width < (g + 1) * width <= 4096);
    assert(meta.descriptor == index.source.subrange(4096 + g * width, 4096 + (g + 1) * width));
    assert(meta.descriptor =~= index.source.subrange(4096, 8192).subrange(g * width, (g + 1) * width));
}

pub proof fn a_preserved_primary_and_gdt_keep_index_geometry_and_group_addresses(before: IndexView, after: IndexView)
    requires group_index::valid(before), group_index::valid(after),
        super_state::preserves(before.source.subrange(0, 4096), after.source.subrange(0, 4096)),
        before.source.subrange(4096, 8192) == after.source.subrange(4096, 8192),
    ensures before.blocks == after.blocks, before.inodes == after.inodes, before.ipg == after.ipg, before.seed == after.seed,
        before.groups.len() == after.groups.len(),
        forall|g: int| 0 <= g < before.groups.len() ==> (#[trigger] before.groups[g]).descriptor == after.groups[g].descriptor
            && before.groups[g].inode_table == after.groups[g].inode_table
            && before.groups[g].inode_bitmap == after.groups[g].inode_bitmap
            && before.groups[g].block_bitmap == after.groups[g].block_bitmap,
{
    hide(crate::crc::fold);
    reveal(group_index::valid);
    reveal(group_index::records_match);
    let old_primary = before.source.subrange(0, 4096);
    let new_primary = after.source.subrange(0, 4096);
    assert(before.source.len() >= 12288 && after.source.len() >= 12288);
    assert forall|i: int| 0 <= i < 4096 && !super_state::edited(i) implies (#[trigger] after.source[i]) == before.source[i] by {
        assert(old_primary[i] == before.source[i] && new_primary[i] == after.source[i]);
        assert(new_primary[i] == old_primary[i]);
    }
    assert(before.source.subrange(1024, 1028) =~= after.source.subrange(1024, 1028));
    assert(before.source.subrange(1028, 1032) =~= after.source.subrange(1028, 1032));
    assert(before.source.subrange(1064, 1068) =~= after.source.subrange(1064, 1068));
    assert(bytes::le32(before.source, 1024) == bytes::le32(after.source, 1024));
    assert(bytes::le32(before.source, 1028) == bytes::le32(after.source, 1028));
    assert(bytes::le32(before.source, 1064) == bytes::le32(after.source, 1064));
    assert(before.blocks == after.blocks && before.inodes == after.inodes && before.ipg == after.ipg);
    assert(before.groups.len() == after.groups.len());
    assert(old_primary.subrange(1024, 2048) =~= before.source.subrange(1024, 2048));
    assert(new_primary.subrange(1024, 2048) =~= after.source.subrange(1024, 2048));
    super_state::recovery_preserves_the_metadata_checksum_domain(old_primary, new_primary, after.source.len() as u64);
    let old_flags = bytes::le32(old_primary, 1120) as u32;
    let new_flags = bytes::le32(new_primary, 1120) as u32;
    assert(old_flags & 0x80u32 == new_flags & 0x80u32) by (bit_vector)
        requires old_flags & 0xfffffffbu32 == new_flags & 0xfffffffbu32;
    assert(superblock::descriptor_bytes(before.source.subrange(1024, 2048)) == superblock::descriptor_bytes(after.source.subrange(1024, 2048)));
    let width = superblock::descriptor_bytes(before.source.subrange(1024, 2048));
    assert forall|g: int| 0 <= g < before.groups.len() implies (#[trigger] before.groups[g]).descriptor == after.groups[g].descriptor
        && before.groups[g].inode_table == after.groups[g].inode_table
        && before.groups[g].inode_bitmap == after.groups[g].inode_bitmap
        && before.groups[g].block_bitmap == after.groups[g].block_bitmap by {
        the_group_descriptor_is_its_exact_source_gdt_slice(before, g);
        the_group_descriptor_is_its_exact_source_gdt_slice(after, g);
    }
}

pub proof fn a_preserved_primary_and_gdt_keep_every_inode_coordinate(before: IndexView, after: IndexView, number: u32)
    requires group_index::valid(before), group_index::valid(after), 0 < number <= before.inodes,
        super_state::preserves(before.source.subrange(0, 4096), after.source.subrange(0, 4096)),
        before.source.subrange(4096, 8192) == after.source.subrange(4096, 8192),
    ensures inode_table::start(before, number) == inode_table::start(after, number),
{
    a_preserved_primary_and_gdt_keep_index_geometry_and_group_addresses(before, after);
    reveal(group_index::valid);
    vstd::arithmetic::mul::lemma_mul_is_commutative(before.ipg as int, before.groups.len() as int);
    vstd::arithmetic::div_mod::lemma_multiply_divide_lt(number as int - 1, before.ipg as int, before.groups.len() as int);
}

}
