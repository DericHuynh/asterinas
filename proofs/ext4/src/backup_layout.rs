// SPDX-License-Identifier: MPL-2.0

//! Linux ext4_bg_has_super selection: SPARSE_SUPER2's explicit groups take
//! precedence, otherwise classic sparse powers or backups in every group.
//! Group numbers are filesystem coordinates, not CortenMM frame identifiers.

use vstd::prelude::*;
use crate::{bytes, group_claims, snapshot::Snapshot, feature_policy};

verus! {

pub open spec fn present(s: Seq<u8>, number: u32) -> bool {
    if number == 0 { true }
    else if bytes::le32(s, 92) as u32 & feature_policy::SPARSE_SUPER2 != 0 {
        number as nat == bytes::le32(s, 588) || number as nat == bytes::le32(s, 592)
    } else if bytes::le32(s, 100) as u32 & 1 == 0 { true }
    else { group_claims::sparse_super(number) }
}

pub fn has_backup(s: &[u8], number: u32) -> (r: Option<bool>)
    ensures match r { Some(value) => s.len() == 1024 && number < 32 && value == present(s@, number),
        None => s.len() != 1024 || number >= 32 },
{
    if s.len() != 1024 || number >= 32 { return None; }
    if number == 0 { return Some(true); }
    if bytes::read_le32(s, 92).unwrap() & feature_policy::SPARSE_SUPER2 != 0 {
        return Some(number == bytes::read_le32(s, 588).unwrap() || number == bytes::read_le32(s, 592).unwrap());
    }
    if bytes::read_le32(s, 100).unwrap() & 1 == 0 { return Some(true); }
    group_claims::backup_group(number)
}

pub fn source_group(source: &Snapshot<'_>, number: u32) -> (r: Option<bool>)
    ensures match r { Some(value) => source.view().len() >= 4096 && number < 32
        && value == present(source.view().subrange(1024, 2048), number),
        None => source.view().len() < 4096 || number >= 32 },
{
    let primary = match source.block(0) { Some(block) => block, None => { return None; } };
    has_backup(primary.range(1024, 1024).unwrap(), number)
}

pub proof fn explicit_backup_groups_override_the_classic_sparse_rule(s: Seq<u8>, number: u32)
    requires s.len() == 1024, number > 0, bytes::le32(s, 92) as u32 & feature_policy::SPARSE_SUPER2 != 0,
    ensures present(s, number) == (number as nat == bytes::le32(s, 588) || number as nat == bytes::le32(s, 592)),
{ }

pub proof fn non_sparse_layout_reserves_primary_and_backup_metadata_in_every_group(s: Seq<u8>, number: u32)
    requires s.len() == 1024, bytes::le32(s, 92) as u32 & feature_policy::SPARSE_SUPER2 == 0,
        bytes::le32(s, 100) as u32 & 1 == 0,
    ensures present(s, number),
{ }

pub proof fn bootstrap_identity_preserves_every_backup_coordinate(before: Seq<u8>, after: Seq<u8>, number: u32)
    requires crate::bootstrap_identity::primary_fixed(before, after),
    ensures present(before.subrange(1024, 2048), number) == present(after.subrange(1024, 2048), number),
{
    let old_compat = bytes::le32(before, 1116) as u32; let new_compat = bytes::le32(after, 1116) as u32;
    assert(old_compat & 0x200u32 == new_compat & 0x200u32) by (bit_vector)
        requires old_compat & !8u32 == new_compat & !8u32;
    assert(bytes::le32(before, 1124) == bytes::le32(after, 1124));
    assert(bytes::le32(before, 1612) == bytes::le32(after, 1612));
    assert(bytes::le32(before, 1616) == bytes::le32(after, 1616));
}

}
