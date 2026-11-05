// SPDX-License-Identifier: MPL-2.0

//! Recovery's static bootstrap identity policy. Geometry/UUID/boot bytes,
//! every group bitmap/table address and the complete journal inode are fixed.
//! Other inodes sharing inode 8's physical block may still be updated.

use vstd::prelude::*;
use crate::{bootstrap::{self, Bootstrap, BootstrapView}, bytes, snapshot::Snapshot, super_state, superblock};

verus! {

pub open spec fn primary_fixed(before: Seq<u8>, after: Seq<u8>) -> bool {
    &&& before.len() == 4096 && after.len() == 4096
    &&& super_state::same_feature_flags(before, after) && super_state::same_compatible_flags(before, after)
    &&& forall|i: int| 0 <= i < 4096 && !super_state::replay_mutable(i) ==> #[trigger] after[i] == before[i]
}

pub open spec fn addresses_fixed(before: Seq<u8>, after: Seq<u8>, groups: nat, width: nat) -> bool {
    &&& before.len() == 4096 && after.len() == 4096 && 0 < groups <= 32 && (width == 32 || width == 64)
    &&& forall|g: int| 0 <= g < groups ==>
        #[trigger] after.subrange(g * width, g * width + 12) == before.subrange(g * width, g * width + 12)
        && (width == 64 ==> after.subrange(g * width + 32, g * width + 44) == before.subrange(g * width + 32, g * width + 44))
}

pub open spec fn preserved(before: BootstrapView, after: Seq<u8>) -> bool {
    &&& after.len() == before.source.len()
    &&& primary_fixed(before.source.subrange(0, 4096), after.subrange(0, 4096))
    &&& addresses_fixed(before.source.subrange(4096, 8192), after.subrange(4096, 8192), (before.blocks as nat + 32767) / 32768, superblock::descriptor_bytes(before.source.subrange(1024, 2048)))
    &&& after.subrange(before.table as int * 4096 + 1792, before.table as int * 4096 + 2048)
        == bootstrap::journal_inode(before)
}

proof fn fixed_addresses_keep_each_group_prefix(before: Seq<u8>, after: Seq<u8>, groups: nat, width: nat, number: int)
    requires addresses_fixed(before, after, groups, width), 0 <= number < groups,
    ensures after.subrange(number * width, number * width + 12) == before.subrange(number * width, number * width + 12),
{
}

pub proof fn fixed_primary_identity_keeps_bootstrap_geometry_and_checksum_domain(before: Seq<u8>, after: Seq<u8>)
    requires primary_fixed(before, after),
    ensures bytes::le32(before, 1024) == bytes::le32(after, 1024), bytes::le32(before, 1028) == bytes::le32(after, 1028),
        bytes::le32(before, 1064) == bytes::le32(after, 1064),
        superblock::metadata_seed(before.subrange(1024, 2048)) == superblock::metadata_seed(after.subrange(1024, 2048)),
        superblock::descriptor_bytes(before.subrange(1024, 2048)) == superblock::descriptor_bytes(after.subrange(1024, 2048)),
        superblock::flex_bg(before.subrange(1024, 2048)) == superblock::flex_bg(after.subrange(1024, 2048)),
{
    hide(crate::crc::fold);
    let old_flags = bytes::le32(before, 1120) as u32;
    let new_flags = bytes::le32(after, 1120) as u32;
    assert(old_flags & 0x2000u32 == new_flags & 0x2000u32) by (bit_vector)
        requires old_flags & 0xfffffffbu32 == new_flags & 0xfffffffbu32;
    assert(old_flags & 0x80u32 == new_flags & 0x80u32) by (bit_vector)
        requires old_flags & 0xfffffffbu32 == new_flags & 0xfffffffbu32;
    assert(old_flags & 0x200u32 == new_flags & 0x200u32) by (bit_vector)
        requires old_flags & 0xfffffffbu32 == new_flags & 0xfffffffbu32;
    assert(before.subrange(1128, 1144) =~= after.subrange(1128, 1144));
    assert(bytes::le32(before, 1648) == bytes::le32(after, 1648));
    assert(before.subrange(1024, 2048).subrange(104, 120) =~= before.subrange(1128, 1144));
    assert(after.subrange(1024, 2048).subrange(104, 120) =~= after.subrange(1128, 1144));
    reveal(superblock::metadata_seed);
}

#[verifier::rlimit(30)]
pub proof fn preserved_group_zero_addresses_keep_the_journal_inode_coordinate(before: BootstrapView, after: Seq<u8>)
    requires bootstrap::valid(before), preserved(before, after),
    ensures bytes::le32(after, 4104) as nat == before.table,
{
    hide(crate::crc::fold);
    hide(superblock::accepted);
    hide(crate::group::accepted_with_features);
    hide(crate::layout::admitted);
    reveal(bootstrap::valid);
    let old_gdt = before.source.subrange(4096, 8192);
    let new_gdt = after.subrange(4096, 8192);
    fixed_addresses_keep_each_group_prefix(old_gdt, new_gdt, (before.blocks as nat + 32767) / 32768,
        superblock::descriptor_bytes(before.source.subrange(1024, 2048)), 0);
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

fn check_primary(before: &[u8], after: &[u8]) -> (r: bool)
    ensures r == primary_fixed(before@, after@),
{
    if before.len() != 4096 || after.len() != 4096 { return false; }
    if bytes::read_le32(before, 1116).unwrap() & !8u32 != bytes::read_le32(after, 1116).unwrap() & !8u32 { return false; }
    if (bytes::read_le32(before, 1120).unwrap() & 0xfffffffbu32)
        != (bytes::read_le32(after, 1120).unwrap() & 0xfffffffbu32) { return false; }
    let mut index = 0usize;
    while index < 4096
        invariant index <= 4096, before.len() == 4096, after.len() == 4096,
            forall|i: int| 0 <= i < index && !super_state::replay_mutable(i) ==> #[trigger] after@[i] == before@[i],
        decreases 4096 - index,
    {
        let mutable = (1032 <= index && index < 1044) || (1068 <= index && index < 1100)
            || (1116 <= index && index < 1120) || (1120 <= index && index < 1124) || (1144 <= index && index < 1224)
            || (1288 <= index && index < 1292) || (2044 <= index && index < 2048);
        if !mutable && after[index] != before[index] { return false; }
        index += 1;
    }
    true
}

fn check_addresses(before: &[u8], after: &[u8], groups: u32, width: usize) -> (r: bool)
    ensures r == addresses_fixed(before@, after@, groups as nat, width as nat),
{
    if before.len() != 4096 || after.len() != 4096 || groups == 0 || groups > 32 || (width != 32 && width != 64) { return false; }
    let mut group = 0u32;
    while group < groups
        invariant group <= groups <= 32, groups > 0, before.len() == 4096, after.len() == 4096, width == 32 || width == 64,
            forall|g: int| 0 <= g < group ==>
                #[trigger] after@.subrange(g * width, g * width + 12) == before@.subrange(g * width, g * width + 12)
                && (width == 64 ==> after@.subrange(g * width + 32, g * width + 44) == before@.subrange(g * width + 32, g * width + 44)),
        decreases groups - group,
    {
        let old = &before[group as usize * width..group as usize * width + 12];
        let new = &after[group as usize * width..group as usize * width + 12];
        if !bytes::equal(old, new) {
            assert(!addresses_fixed(before@, after@, groups as nat, width as nat));
            return false;
        }
        if width == 64 && !bytes::equal(&before[group as usize * width + 32..group as usize * width + 44],
            &after[group as usize * width + 32..group as usize * width + 44]) { return false; }
        group += 1;
    }
    true
}

pub fn check(before: &Bootstrap<'_, '_>, after: &Snapshot<'_>) -> (r: bool)
    ensures before.wf(), r == preserved(before.view(), after.view()),
{
    let source = before.source();
    if source.partition_bytes() != after.partition_bytes() { return false; }
    assert(after.view().len() >= 8192) by { reveal(bootstrap::valid); }
    if !check_primary(before.primary(), after.block(0).unwrap().as_slice()) { return false; }
    if !check_addresses(source.block(1).unwrap().as_slice(), after.block(1).unwrap().as_slice(), before.group_count(), before.descriptor_size()) { return false; }
    let table = before.journal_inode_block();
    assert((table as nat + 1) * 4096 <= after.view().len()) by { reveal(bootstrap::valid); }
    let new_inode = after.block(table).unwrap().range(1792, 256).unwrap();
    bytes::equal(before.raw_journal_inode(), new_inode)
}

}
