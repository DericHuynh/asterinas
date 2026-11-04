// SPDX-License-Identifier: MPL-2.0

//! Exact ext4 needs-recovery images. An ordinary transaction must retain the
//! bit; only the quiescent unmount protocol may persist a cleared image.

use vstd::prelude::*;
use crate::{bytes, crc, frozen::FrozenBlock, superblock};

verus! {

pub open spec fn recovery_flags(flags: u32, dirty: bool) -> u32 {
    if dirty { flags | 4u32 } else { flags & 0xfffffffbu32 }
}

pub open spec fn same_feature_flags(before: Seq<u8>, after: Seq<u8>) -> bool {
    (bytes::le32(before, 1120) as u32 & 0xfffffffbu32)
        == (bytes::le32(after, 1120) as u32 & 0xfffffffbu32)
}

pub open spec fn is_dirty(primary: Seq<u8>) -> bool { bytes::le32(primary, 1120) as u32 & 4 != 0 }

proof fn flags_change_only_recovery(flags: u32, dirty: bool)
    ensures recovery_flags(flags, dirty) & 0xfffffffbu32 == flags & 0xfffffffbu32,
        recovery_flags(flags, dirty) & 0x80u32 == flags & 0x80u32,
        (recovery_flags(flags, dirty) & 4 != 0) == dirty,
        crate::feature_policy::incompat_allowed(flags) ==> crate::feature_policy::incompat_allowed(recovery_flags(flags, dirty)),
{
    if dirty {
        assert((flags | 4u32) & 0xfffffffbu32 == flags & 0xfffffffbu32) by (bit_vector);
        assert((flags | 4u32) & 0x80u32 == flags & 0x80u32) by (bit_vector);
        assert((flags | 4u32) & 4u32 != 0) by (bit_vector);
    } else {
        assert((flags & 0xfffffffbu32) & 0xfffffffbu32 == flags & 0xfffffffbu32) by (bit_vector);
        assert((flags & 0xfffffffbu32) & 0x80u32 == flags & 0x80u32) by (bit_vector);
        assert((flags & 0xfffffffbu32) & 4u32 == 0) by (bit_vector);
    }
    assert(!4u32 == 0xfffffffbu32) by (bit_vector);
    crate::feature_policy::changing_only_recover_preserves_incompatible_feature_admission(flags, recovery_flags(flags, dirty));
}

pub open spec fn edited(index: int) -> bool {
    1120 <= index < 1124 || 2044 <= index < 2048
}

pub open spec fn preserves(before: Seq<u8>, after: Seq<u8>) -> bool {
    &&& before.len() == 4096 && after.len() == 4096
    &&& same_feature_flags(before, after)
    &&& (forall|i: int| 0 <= i < 4096 && !edited(i) ==> #[trigger] after[i] == before[i])
}

#[verifier::opaque]
pub open spec fn recovery_bytes(before: Seq<u8>, dirty: bool) -> Seq<u8> {
    let fields = bytes::splice(before, 1120, bytes::encoded_le(recovery_flags(bytes::le32(before, 1120) as u32, dirty)));
    let checksum = crc::fold(0xffffffff, fields.subrange(1024, 2044));
    bytes::splice(fields, 2044, bytes::encoded_le(checksum))
}

pub fn recovery_image(s: &[u8], partition_bytes: u64, dirty: bool) -> (r: Option<FrozenBlock>)
    ensures match r {
        Some(b) => superblock::accepted(s@.subrange(1024, 2048), partition_bytes)
            && preserves(s@, b.view()) && superblock::accepted(b.view().subrange(1024, 2048), partition_bytes)
            && b.view() == recovery_bytes(s@, dirty)
            && bytes::le32(b.view(), 1120) == recovery_flags(bytes::le32(s@, 1120) as u32, dirty) as nat
            && is_dirty(b.view()) == dirty,
        None => s.len() != 4096 || !superblock::accepted(s@.subrange(1024, 2048), partition_bytes),
    },
{
    if s.len() != 4096 { return None; }
    if superblock::parse(&s[1024..2048], partition_bytes).is_none() { return None; }
    assert(superblock::accepted(s@.subrange(1024, 2048), partition_bytes));
    let mut image = bytes::zero_block();
    bytes::write_bytes(image.as_mut_slice(), 0, s);
    let old_flags = bytes::read_le32(s, 1120).unwrap();
    let new_flags = if dirty { old_flags | 4u32 } else { old_flags & 0xfffffffbu32 };
    proof { flags_change_only_recovery(old_flags, dirty); }
    bytes::write_le32(image.as_mut_slice(), 1120, new_flags);
    let checksum = crc::crc32c(0xffffffff, &image[1024..2044]);
    let ghost before_checksum = image@;
    bytes::write_le32(image.as_mut_slice(), 2044, checksum);
    proof {
        assert(preserves(s@, image@)) by {
            assert forall|i: int| 0 <= i < 4096 && !edited(i) implies #[trigger] image@[i] == s@[i] by { }
        }
        assert(image@.subrange(1024, 2044) =~= before_checksum.subrange(1024, 2044));
        assert(image@.subrange(1024, 2048).subrange(0, 1020) =~= before_checksum.subrange(1024, 2044));
        assert(bytes::le32(image@.subrange(1024, 2048), 1020) == checksum as nat);
        assert(bytes::le32(image@.subrange(1024, 2048), 96) == new_flags as nat);
        assert(image@.subrange(1024, 2048)[373] == s@.subrange(1024, 2048)[373]);
        assert forall|o: int| 0 <= o && o + 4 <= 1024 && o != 96 && o + 4 <= 1020
            && (o + 4 <= 96 || 100 <= o)
            implies #[trigger] bytes::le32(image@.subrange(1024, 2048), o)
                == bytes::le32(s@.subrange(1024, 2048), o) by { }
        assert forall|o: int| 0 <= o && o + 2 <= 1020 && (o + 2 <= 96 || 100 <= o)
            implies #[trigger] bytes::le16(image@.subrange(1024, 2048), o)
                == bytes::le16(s@.subrange(1024, 2048), o) by { }
        assert(superblock::accepted(image@.subrange(1024, 2048), partition_bytes));
        assert(image@ =~= recovery_bytes(s@, dirty)) by { reveal(recovery_bytes); }
    }
    FrozenBlock::from_vec(image)
}

pub proof fn recovery_flag_image_preserves_uuid_and_boot_bytes(before: Seq<u8>, after: Seq<u8>)
    requires preserves(before, after),
    ensures before.subrange(0, 1024) == after.subrange(0, 1024),
        before.subrange(1128, 1144) == after.subrange(1128, 1144),
        before.subrange(2048, 4096) == after.subrange(2048, 4096),
{
    assert(before.subrange(0, 1024) =~= after.subrange(0, 1024));
    assert(before.subrange(1128, 1144) =~= after.subrange(1128, 1144));
    assert(before.subrange(2048, 4096) =~= after.subrange(2048, 4096));
}

/// Mutable counters, timestamps, mount bookkeeping, label/mount path, and
/// checksum. UUID, block/inode geometry, journal identity, and boot bytes are
/// immutable under recovery. The recovery bit itself must remain set.
pub open spec fn replay_mutable(i: int) -> bool {
    1032 <= i < 1044 || 1068 <= i < 1100 || 1120 <= i < 1124
        || 1144 <= i < 1224 || 1288 <= i < 1292 || 2044 <= i < 2048
}

pub open spec fn replay_ok(before: Seq<u8>, after: Seq<u8>, partition_bytes: u64) -> bool {
    &&& before.len() == 4096 && after.len() == 4096
    &&& same_feature_flags(before, after)
    &&& superblock::accepted(before.subrange(1024, 2048), partition_bytes)
    &&& superblock::accepted(after.subrange(1024, 2048), partition_bytes)
    &&& is_dirty(after)
    &&& (forall|i: int| 0 <= i < 4096 && !replay_mutable(i) ==> #[trigger] after[i] == before[i])
}

pub fn valid_replay(before: &[u8], after: &[u8], partition_bytes: u64) -> (r: bool)
    ensures r == replay_ok(before@, after@, partition_bytes),
{
    if before.len() != 4096 || after.len() != 4096 { return false; }
    if superblock::parse(&before[1024..2048], partition_bytes).is_none()
        || superblock::parse(&after[1024..2048], partition_bytes).is_none()
        || bytes::read_le32(after, 1120).unwrap() & 4 == 0
        || (bytes::read_le32(before, 1120).unwrap() & 0xfffffffbu32)
            != (bytes::read_le32(after, 1120).unwrap() & 0xfffffffbu32) { return false; }
    let mut i = 0usize;
    while i < 4096
        invariant i <= 4096, before.len() == 4096, after.len() == 4096,
            forall|j: int| 0 <= j < i && !replay_mutable(j) ==> #[trigger] after@[j] == before@[j],
        decreases 4096 - i,
    {
        let mutable = (1032 <= i && i < 1044) || (1068 <= i && i < 1100)
            || (1120 <= i && i < 1124) || (1144 <= i && i < 1224)
            || (1288 <= i && i < 1292) || (2044 <= i && i < 2048);
        if !mutable && after[i] != before[i] { return false; }
        proof {
            assert forall|j: int| 0 <= j < i + 1 && !replay_mutable(j) implies #[trigger] after@[j] == before@[j] by {
                if j < i { assert(after@[j] == before@[j]); }
            }
        }
        i += 1;
    }
    true
}

pub proof fn replay_preserves_geometry_and_keeps_recovery(before: Seq<u8>, after: Seq<u8>, partition_bytes: u64)
    requires replay_ok(before, after, partition_bytes),
    ensures bytes::le32(before, 1024) == bytes::le32(after, 1024),
        bytes::le32(before, 1028) == bytes::le32(after, 1028),
        bytes::le32(before, 1064) == bytes::le32(after, 1064),
        bytes::le32(before, 1248) == bytes::le32(after, 1248),
        is_dirty(after),
        before.subrange(1128, 1144) == after.subrange(1128, 1144),
{
    assert(before.subrange(1128, 1144) =~= after.subrange(1128, 1144));
}

pub proof fn replay_policy_is_stable_under_another_valid_replay(root: Seq<u8>, current: Seq<u8>, next: Seq<u8>, partition_bytes: u64)
    requires replay_ok(root, current, partition_bytes), replay_ok(root, next, partition_bytes),
    ensures replay_ok(current, next, partition_bytes),
{
    assert forall|i: int| 0 <= i < 4096 && !replay_mutable(i) implies #[trigger] next[i] == current[i] by {
        assert(next[i] == root[i] && current[i] == root[i]);
    }
}

/// Both recovery state-image construction and ordinary replay retain the
/// feature-selected ext4 metadata checksum domain, independently of JBD2.
pub proof fn recovery_preserves_the_metadata_checksum_domain(before: Seq<u8>, after: Seq<u8>, partition_bytes: u64)
    requires preserves(before, after) || replay_ok(before, after, partition_bytes),
    ensures same_feature_flags(before, after),
        superblock::metadata_seed(before.subrange(1024, 2048))
            == superblock::metadata_seed(after.subrange(1024, 2048)),
{
    let old_flags = bytes::le32(before, 1120) as u32;
    let new_flags = bytes::le32(after, 1120) as u32;
    assert(old_flags & 0xfffffffbu32 == new_flags & 0xfffffffbu32);
    assert(old_flags & 0x2000u32 == new_flags & 0x2000u32) by (bit_vector)
        requires old_flags & 0xfffffffbu32 == new_flags & 0xfffffffbu32;
    assert(before.subrange(1128, 1144) =~= after.subrange(1128, 1144));
    assert(bytes::le32(before, 1648) == bytes::le32(after, 1648));
    assert(before.subrange(1024, 2048).subrange(104, 120) =~= before.subrange(1128, 1144));
    assert(after.subrange(1024, 2048).subrange(104, 120) =~= after.subrange(1128, 1144));
    reveal(superblock::metadata_seed);
}

}
