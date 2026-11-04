// SPDX-License-Identifier: MPL-2.0

//! Complete inode-bitmap traversal for one initialized group. Every live file
//! contributes its source-bound extent claims; reserved unused inodes cannot
//! carry storage. Journal inode 8 is validated separately by the volume builder.

use vstd::prelude::*;
use crate::{bitmap, block_claims::{self, Census, Claim, Slot}, bytes, crc, group,
    group_index::{self, GroupIndex, IndexView}, group_metadata, inode, inode_claims, inode_blocks, inode_table, extent_claims};

verus! {

pub open spec fn number(v: IndexView, group: u32, slot: nat) -> u32 {
    (group as nat * v.ipg as nat + slot + 1) as u32
}

pub open spec fn allocated(v: IndexView, group: u32, slot: nat) -> bool {
    bitmap::set(v.groups[group as int].inodes.raw, slot as int)
}

pub open spec fn ordinary(number: u32) -> bool { number == 2 || number >= 11 }

#[verifier::opaque]
pub open spec fn empty_reserved(raw: Seq<u8>) -> bool {
    &&& raw.len() == 256
    &&& bytes::le16(raw, 0) == 0 && bytes::le32(raw, 4) == 0 && bytes::le32(raw, 20) == 0
    &&& bytes::le16(raw, 26) == 0 && bytes::le32(raw, 28) == 0 && bytes::le32(raw, 32) == 0
    &&& bytes::le32(raw, 104) == 0 && bytes::le32(raw, 108) == 0
    &&& bytes::le16(raw, 116) == 0 && bytes::le16(raw, 118) == 0
    &&& forall|i: int| 40 <= i < 100 ==> #[trigger] raw[i] == 0
}

pub fn reserved_is_empty(raw: &[u8]) -> (r: bool) ensures r == empty_reserved(raw@) {
    if raw.len() != 256 { proof { reveal(empty_reserved); } return false; }
    if bytes::read_le16(raw, 0).unwrap() != 0 || bytes::read_le32(raw, 4).unwrap() != 0
        || bytes::read_le32(raw, 20).unwrap() != 0 || bytes::read_le16(raw, 26).unwrap() != 0
        || bytes::read_le32(raw, 28).unwrap() != 0 || bytes::read_le32(raw, 32).unwrap() != 0
        || bytes::read_le32(raw, 104).unwrap() != 0 || bytes::read_le32(raw, 108).unwrap() != 0
        || bytes::read_le16(raw, 116).unwrap() != 0 || bytes::read_le16(raw, 118).unwrap() != 0
    { proof { reveal(empty_reserved); } return false; }
    let mut i = 40usize;
    while i < 100
        invariant 40 <= i <= 100, raw.len() == 256,
            forall|j: int| 40 <= j < i ==> #[trigger] raw@[j] == 0,
        decreases 100 - i,
    {
        if raw[i] != 0 { proof { reveal(empty_reserved); } return false; }
        i += 1;
    }
    proof { reveal(empty_reserved); }
    true
}

#[verifier::opaque]
pub open spec fn ordinary_checked(v: IndexView, roles: Seq<Slot>, n: u32) -> bool {
    let raw = inode_table::raw(v, n);
    &&& extent_claims::accepted(v, n)
    &&& n == 2 ==> (bytes::le16(raw, 0) as u16 & 0xf000) == 0x4000
    &&& !group_index::has_huge_files(v) ==> bytes::le16(raw, 116) == 0
    &&& inode_blocks::sectors(raw, 4096, group_index::has_huge_files(v)) == 8 * inode_claims::allocated(extent_claims::claims(v, n))
    &&& block_claims::mapped_claims(roles, extent_claims::claims(v, n))
}

#[verifier::opaque]
pub open spec fn node_checked(v: IndexView, roles: Seq<Slot>, group: u32, slot: nat) -> bool {
    let n = number(v, group, slot);
    &&& n <= 10 ==> allocated(v, group, slot)
    &&& allocated(v, group, slot) ==> {
        &&& slot + bytes::le16(v.groups[group as int].descriptor, 28) <= v.ipg
        &&& if ordinary(n) { ordinary_checked(v, roles, n) }
            else { n == 8 || empty_reserved(inode_table::raw(v, n)) }
    }
}

#[verifier::opaque]
pub open spec fn checked_prefix(v: IndexView, roles: Seq<Slot>, group: u32, count: nat) -> bool {
    forall|slot: nat| slot < count ==> #[trigger] node_checked(v, roles, group, slot)
}

pub open spec fn contribution(v: IndexView, group: u32, slot: nat) -> Seq<Claim> {
    let n = number(v, group, slot);
    if allocated(v, group, slot) && ordinary(n) { extent_claims::claims(v, n) }
    else { Seq::empty() }
}

#[verifier::opaque]
pub open spec fn claims(v: IndexView, group: u32, count: nat) -> Seq<Claim>
    decreases count,
{
    if count == 0 { Seq::empty() }
    else { claims(v, group, (count - 1) as nat) + contribution(v, group, (count - 1) as nat) }
}

pub open spec fn is_directory(v: IndexView, group: u32, slot: nat) -> bool {
    let n = number(v, group, slot);
    allocated(v, group, slot) && ordinary(n) && (bytes::le16(inode_table::raw(v, n), 0) as u16 & 0xf000) == 0x4000
}

#[verifier::opaque]
pub open spec fn directory_count(v: IndexView, group: u32, count: nat) -> nat
    decreases count,
{
    if count == 0 { 0nat }
    else { directory_count(v, group, (count - 1) as nat) + if is_directory(v, group, (count - 1) as nat) { 1nat } else { 0nat } }
}

pub proof fn number_has_the_expected_group_and_slot(v: IndexView, g: u32, slot: nat)
    requires group_index::valid(v), g < v.groups.len(), slot < v.ipg,
    ensures g as nat * v.ipg as nat + slot + 1 <= v.inodes as nat,
        0 < number(v, g, slot) <= v.inodes,
        (number(v, g, slot) as int - 1) / v.ipg as int == g as int,
        (number(v, g, slot) as int - 1) % v.ipg as int == slot as int,
{
    reveal(group_index::valid);
    assert(g as nat * v.ipg as nat + slot + 1 <= v.inodes as nat) by (nonlinear_arith)
        requires g < v.groups.len(), slot < v.ipg, v.inodes as nat == v.groups.len() * v.ipg as nat;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        number(v, g, slot) as int - 1, v.ipg as int, g as int, slot as int);
}

pub proof fn occupied_preservation_keeps_checked_nodes(v: IndexView, before: Seq<Slot>, after: Seq<Slot>, g: u32, count: nat)
    requires checked_prefix(v, before, g, count), block_claims::preserves_occupied(before, after),
    ensures checked_prefix(v, after, g, count),
{
    reveal(checked_prefix);
    assert forall|slot: nat| slot < count implies #[trigger] node_checked(v, after, g, slot) by {
        assert(node_checked(v, before, g, slot));
        reveal(node_checked);
        reveal(ordinary_checked);
        let n = number(v, g, slot);
        if allocated(v, g, slot) && ordinary(n) {
            block_claims::occupied_preservation_keeps_mapped_claims(before, after, extent_claims::claims(v, n));
        }
    }
}

proof fn append_checked_node(v: IndexView, before: Seq<Slot>, after: Seq<Slot>, g: u32, count: nat)
    requires checked_prefix(v, before, g, count), block_claims::preserves_occupied(before, after), node_checked(v, after, g, count),
    ensures checked_prefix(v, after, g, count + 1),
{
    occupied_preservation_keeps_checked_nodes(v, before, after, g, count);
    reveal(checked_prefix);
    assert forall|slot: nat| slot < count + 1 implies #[trigger] node_checked(v, after, g, slot) by { }
}

pub fn collect(index: &GroupIndex<'_>, mut census: Census, g: u32) -> (r: Option<Census>)
    ensures index.wf(), match r {
        Some(next) => g < index.view().groups.len() && next.wf() && next.view().roles.len() == index.view().blocks
            && block_claims::preserves_occupied(census.view().roles, next.view().roles)
            && next.view().claims == census.view().claims + claims(index.view(), g, index.view().ipg as nat)
            && checked_prefix(index.view(), next.view().roles, g, index.view().ipg as nat)
            && directory_count(index.view(), g, index.view().ipg as nat) == bytes::le16(index.view().groups[g as int].descriptor, 16),
        None => true,
    },
{
    hide(crc::fold);
    hide(group_metadata::valid);
    let ghost original = census.view();
    let (blocks, inodes, ipg, seed) = index.parameters();
    let meta = match index.get(g) { Some(meta) => meta, None => { return None; } };
    let _ = meta.parameters();
    if census.block_count() != blocks { return None; }
    let descriptor = meta.descriptor();
    assert(descriptor.len() == 32 || descriptor.len() == 64) by { reveal(group_metadata::valid); reveal(group::accepted_with_features); }
    let unused = bytes::read_le16(descriptor, 28).unwrap() as u32;
    let used_dirs = bytes::read_le16(descriptor, 16).unwrap() as u32;
    assert(unused <= ipg && ipg <= 32768) by {
        reveal(group_index::valid); reveal(group_index::records_match); reveal(group_metadata::valid); reveal(group::accepted_with_features);
    }
    let (_, bitmap) = meta.bitmaps();
    assert(bitmap.view().valid == ipg) by {
        reveal(group_index::valid); reveal(group_index::records_match); reveal(group_metadata::valid);
    }
    let mut slot = 0u32;
    let mut directories = 0u32;
    assert(claims(index.view(), g, 0) == Seq::<Claim>::empty()) by { reveal(claims); }
    assert(directory_count(index.view(), g, 0) == 0) by { reveal(directory_count); }
    assert(checked_prefix(index.view(), census.view().roles, g, 0)) by { reveal(checked_prefix); }
    assert(block_claims::preserves_occupied(original.roles, census.view().roles)) by { reveal(block_claims::preserves_occupied); }
    while slot < ipg
        invariant index.wf(), g < index.view().groups.len(), (blocks, inodes, ipg, seed) ==
                (index.view().blocks, index.view().inodes, index.view().ipg, index.view().seed),
            slot <= ipg <= 32768, unused <= ipg, descriptor@ == index.view().groups[g as int].descriptor,
            unused as nat == bytes::le16(descriptor@, 28), used_dirs as nat == bytes::le16(descriptor@, 16),
            bitmap.view() == index.view().groups[g as int].inodes, bitmap.view().valid == ipg,
            census.wf(), census.view().roles.len() == blocks,
            census.view().claims == original.claims + claims(index.view(), g, slot as nat),
            block_claims::preserves_occupied(original.roles, census.view().roles),
            checked_prefix(index.view(), census.view().roles, g, slot as nat),
            directories <= slot, directories as nat == directory_count(index.view(), g, slot as nat),
        decreases ipg - slot,
    {
        proof { number_has_the_expected_group_and_slot(index.view(), g, slot as nat); }
        let n = (g as u64 * ipg as u64 + slot as u64 + 1) as u32;
        let is_allocated = bitmap.is_set(slot).unwrap();
        if n <= 10 && !is_allocated { return None; }
        let ghost before = census.view();
        let mut directory = false;
        if is_allocated {
            if slot >= ipg - unused { return None; }
            let raw = inode_table::read(index, n).unwrap();
            if n == 2 || n >= 11 {
                let mode = bytes::read_le16(raw, 0).unwrap();
                if n == 2 && mode & 0xf000 != 0x4000 { return None; }
                directory = mode & 0xf000 == 0x4000;
                let bound = match extent_claims::bind(index, n, blocks as u64 + 1) {
                    Some(bound) => bound, None => { return None; }
                };
                census = match extent_claims::collect(census, &bound) {
                    Some(next) => next, None => { return None; }
                };
                assert(ordinary_checked(index.view(), census.view().roles, n)) by { reveal(ordinary_checked); }
            } else if n != 8 && !reserved_is_empty(raw) { return None; }
        }
        proof {
            if !is_allocated || !ordinary(n) { reveal(block_claims::preserves_occupied); }
            assert(node_checked(index.view(), census.view().roles, g, slot as nat)) by { reveal(node_checked); }
            append_checked_node(index.view(), before.roles, census.view().roles, g, slot as nat);
            block_claims::occupied_slot_preservation_is_transitive(original.roles, before.roles, census.view().roles);
            assert(claims(index.view(), g, slot as nat + 1) == claims(index.view(), g, slot as nat) + contribution(index.view(), g, slot as nat)) by { reveal(claims); }
            assert(directory_count(index.view(), g, slot as nat + 1) == directory_count(index.view(), g, slot as nat)
                + if directory { 1nat } else { 0nat }) by { reveal(directory_count); }
        }
        if directory { directories += 1; }
        slot += 1;
    }
    if directories != used_dirs { return None; }
    Some(census)
}

}
