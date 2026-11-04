// SPDX-License-Identifier: MPL-2.0

//! Recovery's static bootstrap identity policy. Geometry/UUID/boot bytes,
//! every group bitmap/table address and the complete journal inode are fixed.
//! Other inodes sharing inode 8's physical block may still be updated.

use vstd::prelude::*;
use crate::{bootstrap::{self, Bootstrap, BootstrapView}, bytes, snapshot::Snapshot, super_state};

verus! {

pub open spec fn primary_fixed(before: Seq<u8>, after: Seq<u8>) -> bool {
    &&& before.len() == 4096 && after.len() == 4096
    &&& super_state::same_feature_flags(before, after)
    &&& forall|i: int| 0 <= i < 4096 && !super_state::replay_mutable(i) ==> #[trigger] after[i] == before[i]
}

pub open spec fn addresses_fixed(before: Seq<u8>, after: Seq<u8>, groups: nat) -> bool {
    &&& before.len() == 4096 && after.len() == 4096 && 0 < groups <= 32
    &&& forall|g: int| 0 <= g < groups ==>
        #[trigger] after.subrange(g * 32, g * 32 + 12) == before.subrange(g * 32, g * 32 + 12)
}

pub open spec fn preserved(before: BootstrapView, after: Seq<u8>) -> bool {
    &&& after.len() == before.source.len()
    &&& primary_fixed(before.source.subrange(0, 4096), after.subrange(0, 4096))
    &&& addresses_fixed(before.source.subrange(4096, 8192), after.subrange(4096, 8192), (before.blocks as nat + 32767) / 32768)
    &&& after.subrange(before.table as int * 4096 + 1792, before.table as int * 4096 + 2048)
        == bootstrap::journal_inode(before)
}

fn check_primary(before: &[u8], after: &[u8]) -> (r: bool)
    ensures r == primary_fixed(before@, after@),
{
    if before.len() != 4096 || after.len() != 4096 { return false; }
    if (bytes::read_le32(before, 1120).unwrap() & 0xfffffffbu32)
        != (bytes::read_le32(after, 1120).unwrap() & 0xfffffffbu32) { return false; }
    let mut index = 0usize;
    while index < 4096
        invariant index <= 4096, before.len() == 4096, after.len() == 4096,
            forall|i: int| 0 <= i < index && !super_state::replay_mutable(i) ==> #[trigger] after@[i] == before@[i],
        decreases 4096 - index,
    {
        let mutable = (1032 <= index && index < 1044) || (1068 <= index && index < 1100)
            || (1120 <= index && index < 1124) || (1144 <= index && index < 1224)
            || (1288 <= index && index < 1292) || (2044 <= index && index < 2048);
        if !mutable && after[index] != before[index] { return false; }
        index += 1;
    }
    true
}

fn check_addresses(before: &[u8], after: &[u8], groups: u32) -> (r: bool)
    ensures r == addresses_fixed(before@, after@, groups as nat),
{
    if before.len() != 4096 || after.len() != 4096 || groups == 0 || groups > 32 { return false; }
    let mut group = 0u32;
    while group < groups
        invariant group <= groups <= 32, groups > 0, before.len() == 4096, after.len() == 4096,
            forall|g: int| 0 <= g < group ==>
                #[trigger] after@.subrange(g * 32, g * 32 + 12) == before@.subrange(g * 32, g * 32 + 12),
        decreases groups - group,
    {
        let old = &before[group as usize * 32..group as usize * 32 + 12];
        let new = &after[group as usize * 32..group as usize * 32 + 12];
        if !bytes::equal(old, new) {
            assert(!addresses_fixed(before@, after@, groups as nat));
            return false;
        }
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
    if !check_addresses(source.block(1).unwrap().as_slice(), after.block(1).unwrap().as_slice(), before.group_count()) { return false; }
    let table = before.journal_inode_block();
    assert((table as nat + 1) * 4096 <= after.view().len()) by { reveal(bootstrap::valid); }
    let new_inode = after.block(table).unwrap().range(1792, 256).unwrap();
    bytes::equal(before.raw_journal_inode(), new_inode)
}

}
