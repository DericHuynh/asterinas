// SPDX-License-Identifier: MPL-2.0

//! EA_INODE primary recovery-state images retain the original feature profile.
//! Every accepted image validates its own raw ext4 header and checksum.

use vstd::prelude::*;
use crate::{bytes, crc, ea_source, feature_policy, frozen::FrozenBlock, super_state};

verus! {

proof fn flags_change_only_recovery(flags: u32, dirty: bool)
    ensures super_state::recovery_flags(flags, dirty) & !4u32 == flags & !4u32,
        super_state::recovery_flags(flags, dirty) & 0x80u32 == flags & 0x80u32,
        (super_state::recovery_flags(flags, dirty) & 4u32 != 0) == dirty,
        super_state::recovery_flags(flags, dirty) & ea_source::EA_INODE == flags & ea_source::EA_INODE,
        feature_policy::incompat_allowed(flags & !ea_source::EA_INODE)
            == feature_policy::incompat_allowed(super_state::recovery_flags(flags, dirty) & !ea_source::EA_INODE),
{
    assert(!4u32 == 0xfffffffbu32) by (bit_vector);
    if dirty {
        assert((flags | 4u32) & !4u32 == flags & !4u32) by (bit_vector);
        assert((flags | 4u32) & 4u32 != 0) by (bit_vector);
        assert((flags | 4u32) & 0x80u32 == flags & 0x80u32) by (bit_vector);
        assert((flags | 4u32) & 0x400u32 == flags & 0x400u32) by (bit_vector);
    } else {
        assert((flags & !4u32) & !4u32 == flags & !4u32) by (bit_vector);
        assert((flags & !4u32) & 4u32 == 0) by (bit_vector);
        assert((flags & !4u32) & 0x80u32 == flags & 0x80u32) by (bit_vector);
        assert((flags & !4u32) & 0x400u32 == flags & 0x400u32) by (bit_vector);
    }
    assert((flags & !ea_source::EA_INODE) & !4u32
        == (super_state::recovery_flags(flags, dirty) & !ea_source::EA_INODE) & !4u32) by (bit_vector)
        requires super_state::recovery_flags(flags, dirty) & !4u32 == flags & !4u32;
    feature_policy::changing_only_recover_preserves_incompatible_feature_admission(
        flags & !ea_source::EA_INODE,
        super_state::recovery_flags(flags, dirty) & !ea_source::EA_INODE);
}

pub fn recovery_image(s: &[u8], partition_bytes: u64, dirty: bool) -> (r: Option<FrozenBlock>)
    ensures match r {
        Some(b) => ea_source::header_accepted(s@.subrange(1024, 2048), partition_bytes)
            && super_state::preserves(s@, b.view())
            && ea_source::header_accepted(b.view().subrange(1024, 2048), partition_bytes)
            && b.view() == super_state::recovery_bytes(s@, dirty)
            && bytes::le32(b.view(), 1120) == super_state::recovery_flags(bytes::le32(s@, 1120) as u32, dirty) as nat
            && super_state::is_dirty(b.view()) == dirty,
        None => s.len() != 4096 || !ea_source::header_accepted(s@.subrange(1024, 2048), partition_bytes),
    },
{
    if s.len() != 4096 { return None; }
    if !ea_source::validate_header(&s[1024..2048], partition_bytes) { return None; }
    let mut image = bytes::zero_block();
    bytes::write_bytes(image.as_mut_slice(), 0, s);
    let old_flags = bytes::read_le32(s, 1120).unwrap();
    let new_flags = if dirty { old_flags | 4u32 } else { old_flags & !4u32 };
    proof { flags_change_only_recovery(old_flags, dirty); }
    bytes::write_le32(image.as_mut_slice(), 1120, new_flags);
    let checksum = crc::crc32c(0xffffffff, &image[1024..2044]);
    let ghost before_checksum = image@;
    bytes::write_le32(image.as_mut_slice(), 2044, checksum);
    proof {
        assert(!4u32 == 0xfffffffbu32) by (bit_vector);
        assert(super_state::preserves(s@, image@)) by {
            assert forall|i: int| 0 <= i < 4096 && !super_state::edited(i)
                implies #[trigger] image@[i] == s@[i] by { }
        }
        assert(image@.subrange(1024, 2044) =~= before_checksum.subrange(1024, 2044));
        assert(image@.subrange(1024, 2048).subrange(0, 1020) =~= before_checksum.subrange(1024, 2044));
        assert(bytes::le32(image@.subrange(1024, 2048), 1020) == checksum as nat);
        assert(bytes::le32(image@.subrange(1024, 2048), 96) == new_flags as nat);
        assert(image@.subrange(1024, 2048)[373] == s@.subrange(1024, 2048)[373]);
        assert forall|o: int| 0 <= o && o + 4 <= 1020 && (o + 4 <= 96 || 100 <= o)
            implies #[trigger] bytes::le32(image@.subrange(1024, 2048), o)
                == bytes::le32(s@.subrange(1024, 2048), o) by { }
        assert forall|o: int| 0 <= o && o + 2 <= 1020 && (o + 2 <= 96 || 100 <= o)
            implies #[trigger] bytes::le16(image@.subrange(1024, 2048), o)
                == bytes::le16(s@.subrange(1024, 2048), o) by { }
        assert(ea_source::header_accepted(image@.subrange(1024, 2048), partition_bytes));
        assert(image@ =~= super_state::recovery_bytes(s@, dirty)) by { reveal(super_state::recovery_bytes); }
    }
    if !ea_source::validate_header(&image[1024..2048], partition_bytes) { return None; }
    FrozenBlock::from_vec(image)
}

pub proof fn ea_recovery_state_images_retain_the_feature_and_checksum_domains(before: Seq<u8>, after: Seq<u8>, partition_bytes: u64)
    requires ea_source::header_accepted(before.subrange(1024, 2048), partition_bytes),
        ea_source::header_accepted(after.subrange(1024, 2048), partition_bytes),
        super_state::preserves(before, after),
    ensures bytes::le32(before, 1120) as u32 & ea_source::EA_INODE != 0,
        bytes::le32(after, 1120) as u32 & ea_source::EA_INODE != 0,
        crate::superblock::metadata_seed(before.subrange(1024, 2048))
            == crate::superblock::metadata_seed(after.subrange(1024, 2048)),
        before.subrange(1128, 1144) == after.subrange(1128, 1144),
        before.subrange(0, 1024) == after.subrange(0, 1024),
        before.subrange(2048, 4096) == after.subrange(2048, 4096),
{
    super_state::recovery_preserves_the_metadata_checksum_domain(before, after, partition_bytes);
    super_state::recovery_flag_image_preserves_uuid_and_boot_bytes(before, after);
}

}
