// SPDX-License-Identifier: MPL-2.0

//! Exact supported feature masks and source-selected read-only/stable-identity
//! policy. A recognized bit is not permission to bypass format or image checks.

use vstd::prelude::*;
use crate::bytes;

verus! {

pub const HAS_JOURNAL: u32 = 0x4;
pub const SPARSE_SUPER2: u32 = 0x200;
pub const STABLE_INODES: u32 = 0x800;
pub const BTREE_DIR: u32 = 0x4;
pub const DIR_NLINK: u32 = 0x20;
pub const READONLY: u32 = 0x1000;

pub open spec fn compat_allowed(flags: u32) -> bool { flags & !0xa04u32 == 0 && flags & HAS_JOURNAL != 0 }
pub open spec fn ro_allowed(flags: u32) -> bool { flags & !0x146fu32 == 0 && flags & 0x442u32 == 0x442u32 }
pub open spec fn incompat_allowed(flags: u32) -> bool { flags & 0xffffdd7bu32 == 0x42u32 }
pub open spec fn readonly(s: Seq<u8>) -> bool { bytes::le32(s, 100) as u32 & READONLY != 0 }
pub open spec fn stable_inodes(s: Seq<u8>) -> bool { bytes::le32(s, 92) as u32 & STABLE_INODES != 0 }
pub open spec fn dir_nlink(s: Seq<u8>) -> bool { bytes::le32(s, 100) as u32 & DIR_NLINK != 0 }

pub fn compatible_flags(flags: u32) -> (r: bool) ensures r == compat_allowed(flags) {
    flags & !0xa04u32 == 0 && flags & HAS_JOURNAL != 0
}
pub fn readonly_compatible_flags(flags: u32) -> (r: bool) ensures r == ro_allowed(flags) {
    flags & !0x146fu32 == 0 && flags & 0x442u32 == 0x442u32
}
pub fn incompatible_flags(flags: u32) -> (r: bool) ensures r == incompat_allowed(flags) {
    flags & 0xffffdd7bu32 == 0x42u32
}
pub fn is_readonly(s: &[u8]) -> (r: Option<bool>)
    ensures match r { Some(value) => s.len() == 1024 && value == readonly(s@), None => s.len() != 1024 },
{
    if s.len() != 1024 { None } else { Some(bytes::read_le32(s, 100).unwrap() & READONLY != 0) }
}
pub fn has_dir_nlink(s: &[u8]) -> (r: Option<bool>)
    ensures match r { Some(value) => s.len() == 1024 && value == dir_nlink(s@), None => s.len() != 1024 },
{
    if s.len() != 1024 { None } else { Some(bytes::read_le32(s, 100).unwrap() & DIR_NLINK != 0) }
}
pub fn has_stable_inodes(s: &[u8]) -> (r: Option<bool>)
    ensures match r { Some(value) => s.len() == 1024 && value == stable_inodes(s@), None => s.len() != 1024 },
{
    if s.len() != 1024 { None } else { Some(bytes::read_le32(s, 92).unwrap() & STABLE_INODES != 0) }
}

pub proof fn every_admitted_mask_keeps_required_features_and_rejects_unimplemented_bits(compat: u32, ro: u32)
    requires compat_allowed(compat), ro_allowed(ro),
    ensures compat & 4u32 != 0, ro & 0x442u32 == 0x442u32,
        compat & 0xfffff5fbu32 == 0, ro & 0xffffeb90u32 == 0,
{ assert(compat & 0xfffff5fbu32 == 0 && ro & 0xffffeb90u32 == 0) by (bit_vector)
    requires compat & !0xa04u32 == 0, ro & !0x146fu32 == 0; }

pub proof fn linux_unsupported_compression_and_dirdata_markers_are_always_rejected(flags: u32)
    requires flags & 0x1001u32 != 0,
    ensures !incompat_allowed(flags),
{ assert(flags & 0x1001u32 != 0 ==> flags & 0xffffdd7bu32 != 0x42u32) by (bit_vector); }

pub proof fn bootstrap_identity_preserves_source_feature_policy(before: Seq<u8>, after: Seq<u8>)
    requires crate::bootstrap_identity::primary_fixed(before, after),
    ensures readonly(before.subrange(1024, 2048)) == readonly(after.subrange(1024, 2048)),
        stable_inodes(before.subrange(1024, 2048)) == stable_inodes(after.subrange(1024, 2048)),
        dir_nlink(before.subrange(1024, 2048)) == dir_nlink(after.subrange(1024, 2048)),
        before.subrange(1128, 1144) == after.subrange(1128, 1144),
        bytes::le32(before, 1028) == bytes::le32(after, 1028),
{
    assert(bytes::le32(before, 1116) == bytes::le32(after, 1116));
    assert(bytes::le32(before, 1124) == bytes::le32(after, 1124));
    crate::bootstrap_identity::fixed_primary_identity_keeps_bootstrap_geometry_and_checksum_domain(before, after);
    assert(before.subrange(1128, 1144) =~= after.subrange(1128, 1144));
}

pub proof fn recovery_mark_preserves_readonly_stable_and_link_count_features(before: Seq<u8>, after: Seq<u8>)
    requires crate::super_state::preserves(before, after),
    ensures readonly(before.subrange(1024, 2048)) == readonly(after.subrange(1024, 2048)),
        stable_inodes(before.subrange(1024, 2048)) == stable_inodes(after.subrange(1024, 2048)),
        dir_nlink(before.subrange(1024, 2048)) == dir_nlink(after.subrange(1024, 2048)),
{
    assert(bytes::le32(before, 1116) == bytes::le32(after, 1116));
    assert(bytes::le32(before, 1124) == bytes::le32(after, 1124));
}

pub proof fn no_serial_writer_starts_on_a_readonly_filesystem(images: crate::write_io::Images)
    requires crate::write_io::valid_images(images),
    ensures !readonly(images.initial_primary.subrange(1024, 2048)),
{ reveal(crate::write_io::valid_images); }

pub proof fn no_concurrent_window_starts_on_a_readonly_filesystem(window: crate::journal_window::WindowView)
    requires crate::journal_window::valid(window),
    ensures !readonly(window.initial_primary.subrange(1024, 2048)),
{ reveal(crate::journal_window::valid); }

}
