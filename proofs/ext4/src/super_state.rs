// SPDX-License-Identifier: MPL-2.0

//! Exact ext4 needs-recovery images. An ordinary transaction must retain the
//! bit; only the quiescent unmount protocol may persist a cleared image.

use vstd::prelude::*;
use crate::{bytes, crc, frozen::FrozenBlock, superblock};

verus! {

pub open spec fn edited(index: int) -> bool {
    1120 <= index < 1124 || 2044 <= index < 2048
}

pub open spec fn preserves(before: Seq<u8>, after: Seq<u8>) -> bool {
    &&& before.len() == 4096 && after.len() == 4096
    &&& (forall|i: int| 0 <= i < 4096 && !edited(i) ==> #[trigger] after[i] == before[i])
}

pub open spec fn recovery_bytes(before: Seq<u8>, dirty: bool) -> Seq<u8> {
    let fields = bytes::splice(before, 1120, bytes::encoded_le(if dirty { 0x46u32 } else { 0x42u32 }));
    let checksum = crc::fold(0xffffffff, fields.subrange(1024, 2044));
    bytes::splice(fields, 2044, bytes::encoded_le(checksum))
}

pub fn recovery_image(s: &[u8], partition_bytes: u64, dirty: bool) -> (r: Option<FrozenBlock>)
    ensures match r {
        Some(b) => superblock::accepted(s@.subrange(1024, 2048), partition_bytes)
            && preserves(s@, b.view()) && superblock::accepted(b.view().subrange(1024, 2048), partition_bytes)
            && b.view() == recovery_bytes(s@, dirty)
            && bytes::le32(b.view(), 1120) == if dirty { 0x46nat } else { 0x42nat },
        None => s.len() != 4096 || !superblock::accepted(s@.subrange(1024, 2048), partition_bytes),
    },
{
    if s.len() != 4096 { return None; }
    if superblock::parse(&s[1024..2048], partition_bytes).is_none() { return None; }
    assert(superblock::accepted(s@.subrange(1024, 2048), partition_bytes));
    let mut image = bytes::zero_block();
    bytes::write_bytes(image.as_mut_slice(), 0, s);
    bytes::write_le32(image.as_mut_slice(), 1120, if dirty { 0x46 } else { 0x42 });
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
        assert(bytes::le32(image@.subrange(1024, 2048), 96) == if dirty { 0x46nat } else { 0x42nat });
        assert(image@.subrange(1024, 2048)[373] == s@.subrange(1024, 2048)[373]);
        assert forall|o: int| 0 <= o && o + 4 <= 1024 && o != 96 && o + 4 <= 1020
            && (o + 4 <= 96 || 100 <= o)
            implies #[trigger] bytes::le32(image@.subrange(1024, 2048), o)
                == bytes::le32(s@.subrange(1024, 2048), o) by { }
        assert forall|o: int| 0 <= o && o + 2 <= 1020 && (o + 2 <= 96 || 100 <= o)
            implies #[trigger] bytes::le16(image@.subrange(1024, 2048), o)
                == bytes::le16(s@.subrange(1024, 2048), o) by { }
        assert(superblock::accepted(image@.subrange(1024, 2048), partition_bytes));
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
    &&& superblock::accepted(before.subrange(1024, 2048), partition_bytes)
    &&& superblock::accepted(after.subrange(1024, 2048), partition_bytes)
    &&& bytes::le32(after, 1120) == 0x46
    &&& (forall|i: int| 0 <= i < 4096 && !replay_mutable(i) ==> #[trigger] after[i] == before[i])
}

pub fn valid_replay(before: &[u8], after: &[u8], partition_bytes: u64) -> (r: bool)
    ensures r == replay_ok(before@, after@, partition_bytes),
{
    if before.len() != 4096 || after.len() != 4096 { return false; }
    if superblock::parse(&before[1024..2048], partition_bytes).is_none()
        || superblock::parse(&after[1024..2048], partition_bytes).is_none()
        || bytes::read_le32(after, 1120).unwrap() != 0x46 { return false; }
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
        bytes::le32(after, 1120) == 0x46,
        before.subrange(1128, 1144) == after.subrange(1128, 1144),
{
    assert(before.subrange(1128, 1144) =~= after.subrange(1128, 1144));
}

}
