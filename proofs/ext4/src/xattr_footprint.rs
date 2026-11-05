// SPDX-License-Identifier: MPL-2.0

//! Check xattr transaction byte authority against the exact allocation census.
//! Shared entries/values, neighboring inodes and unrelated metadata are framed.
//! Lazy bitmaps are compared with their admitted logical image, not stale media.

use vstd::prelude::*;
use crate::{allocated_inode::{self, AllocatedInode, NodeView}, bytes, inode_table,
    patch_set::PatchSet, superblock, xattr_source};

verus! {

#[derive(Clone, Copy)]
pub struct Region { pub inode_block: u32, pub offset: usize, pub old: u32, pub new: u32, pub refs: u32,
    pub account: u32, pub bitmap: u32, pub group: u32, pub width: usize }
pub open spec fn accounting(old: u32, new: u32, refs: u32) -> u32 {
    if new > 0 && new != old { new } else if new == 0 && old > 0 && refs == 1 { old } else { 0 }
}
pub open spec fn old_refs(node: NodeView) -> nat {
    let old = xattr_source::pointer(node.volume.index, node.number);
    if old == 0 { 0 } else { bytes::le32(xattr_source::block_bytes(node.volume.index, old), 4) }
}
#[verifier::opaque]
pub open spec fn valid(r: Region, node: NodeView) -> bool {
    let index = node.volume.index;
    &&& allocated_inode::valid(node) && (r.account == 0 || r.inode_block != r.bitmap) && r.offset <= 3840 && r.group < 32 && (r.width == 32 || r.width == 64)
    &&& r.inode_block as nat == inode_table::start(index, node.number) / 4096 && r.offset as nat == inode_table::start(index, node.number) % 4096
    &&& r.old as nat == xattr_source::pointer(index, node.number) && r.refs as nat == old_refs(node)
    &&& r.new < index.blocks && r.old < index.blocks && r.width as nat == superblock::descriptor_bytes(index.source.subrange(1024, 2048))
    &&& (r.new > 0 && r.new != r.old ==> r.new < node.volume.census.roles.len() && node.volume.census.roles[r.new as int].kind == 0)
    &&& (r.new > 0 && r.new == r.old ==> r.refs == 1)
    &&& r.account == accounting(r.old, r.new, r.refs)
    &&& (r.account == 0 ==> r.bitmap == 0 && r.group == 0)
    &&& (r.account > 0 ==> r.group == r.account / 32768 && r.group < index.groups.len() && r.bitmap == index.groups[r.group as int].block_bitmap)
}
pub open spec fn allowed(r: Region, block: u32, i: int) -> bool {
    let relative = i - r.group as int * r.width as int;
    if block == r.inode_block { r.offset <= i < r.offset + 256 }
    else if r.new > 0 && block == r.new { true }
    else if r.old > 0 && block == r.old && r.old != r.new && r.refs > 1 { 4 <= i < 8 || 16 <= i < 20 }
    else if r.account > 0 && block == r.bitmap { i == r.account as int % 32768 / 8 }
    else if r.account > 0 && block == 1 { 12 <= relative < 14 || 18 <= relative < 20 || 24 <= relative < 26 || 30 <= relative < 32
        || r.width == 64 && 56 <= relative < 58 }
    else if block == 0 { r.account > 0 && 1036 <= i < 1040 || 1116 <= i < 1124 || 2044 <= i < 2048 }
    else { false }
}
pub open spec fn reference(r: Region, node: NodeView, block: u32) -> Seq<u8> {
    if r.account > 0 && block == r.bitmap { node.volume.index.groups[r.group as int].allocation.raw }
    else { xattr_source::block_bytes(node.volume.index, block as nat) }
}
pub open spec fn confined(r: Region, node: NodeView, images: Seq<crate::transaction::ImageView>) -> bool {
    valid(r, node) && forall|k: int| 0 <= k < images.len() ==> (#[trigger] images[k]).block < node.volume.index.blocks
        && (forall|i: int| 0 <= i < 4096 && !allowed(r, images[k].block, i) ==> #[trigger] images[k].image[i] == reference(r, node, images[k].block)[i])
}
fn bytes_confined(before: &[u8], after: &[u8], r: Region, block: u32) -> (ok: bool)
    requires r.offset <= 3840, r.group < 32, r.width == 32 || r.width == 64,
    ensures ok ==> before.len() == 4096 && after.len() == 4096 && (forall|i: int| 0 <= i < 4096 && !allowed(r, block, i) ==> #[trigger] after@[i] == before@[i]),
{
    if before.len() != 4096 || after.len() != 4096 { return false; }
    let start = r.group as usize * r.width; let mut i = 0usize;
    while i < 4096
        invariant i <= 4096, before.len() == 4096, after.len() == 4096, r.offset <= 3840, r.group < 32, r.width == 32 || r.width == 64,
            start == r.group as nat * r.width as nat,
            forall|j: int| 0 <= j < i && !allowed(r, block, j) ==> #[trigger] after@[j] == before@[j],
        decreases 4096 - i,
    {
        let changed = if block == r.inode_block { r.offset <= i && i < r.offset + 256 }
        else if r.new > 0 && block == r.new { true }
        else if r.old > 0 && block == r.old && r.old != r.new && r.refs > 1 { 4 <= i && i < 8 || 16 <= i && i < 20 }
        else if r.account > 0 && block == r.bitmap { i == (r.account % 32768 / 8) as usize }
        else if r.account > 0 && block == 1 {
            if i < start { false } else { let relative = i - start;
                12 <= relative && relative < 14 || 18 <= relative && relative < 20 || 24 <= relative && relative < 26
                    || 30 <= relative && relative < 32 || r.width == 64 && 56 <= relative && relative < 58 }
        } else if block == 0 { r.account > 0 && 1036 <= i && i < 1040 || 1116 <= i && i < 1124 || 2044 <= i && i < 2048 }
        else { false };
        if !changed && before[i] != after[i] { return false; } i += 1;
    }
    true
}
pub fn check(node: &AllocatedInode<'_, '_>, new: u32, patches: &PatchSet) -> (result: Option<Region>)
    ensures node.wf(), patches.wf(), match result { Some(r) => r.new == new && confined(r, node.view(), patches.view()), None => true },
{
    let n = patches.len();
    let volume = node.volume(); let index = volume.index(); let (blocks, _, _, _) = index.parameters(); let number = node.number();
    let old = crate::xattr::inode_pointer(node.raw()).unwrap(); if old >= blocks as u64 || new >= blocks { return None; } let old = old as u32;
    let refs = if old == 0 { 0u32 } else { let source = match index.source().block(old) { Some(source) => source, None => { return None; } }; bytes::read_le32(source.as_slice(), 4).unwrap() };
    if new > 0 && new != old { let role = match volume.census().role_of(new) { Some(role) => role, None => { return None; } }; if role.kind != 0 { return None; } }
    if new > 0 && new == old && refs != 1 { return None; }
    let position = match inode_table::position(index, number) { Some(position) => position, None => { return None; } }; if position / 4096 > u32::MAX as u64 || position % 4096 > 3840 { return None; }
    let account = if new > 0 && new != old { new } else if new == 0 && old > 0 && refs == 1 { old } else { 0u32 };
    let primary = match index.source().block(0) { Some(source) => source, None => { return None; } };
    let width = match superblock::descriptor_length(primary.range(1024, 1024).unwrap()) { Some(width) => width, None => { return None; } };
    let group = if account == 0 { 0u32 } else { account / 32768 }; if group >= 32 { return None; }
    let meta = match index.get(group) { Some(meta) => meta, None => { return None; } };
    let bitmap = if account == 0 { 0u32 } else { meta.info().block_bitmap };
    let logical = meta.bitmaps().0.raw_image(); if logical.len() != 4096 { return None; }
    let r = Region { inode_block: (position / 4096) as u32, offset: (position % 4096) as usize, old, new, refs, account, bitmap, group, width };
    if account > 0 && r.inode_block == bitmap { return None; }
    assert(allocated_inode::valid(node.view()));
    assert(r.inode_block as nat == inode_table::start(index.view(), number) / 4096 && r.offset as nat == inode_table::start(index.view(), number) % 4096);
    assert(r.old as nat == xattr_source::pointer(index.view(), number));
    assert(r.refs as nat == old_refs(node.view()));
    assert(r.width as nat == superblock::descriptor_bytes(index.view().source.subrange(1024, 2048)));
    assert(r.new > 0 && r.new != r.old ==> r.new < node.view().volume.census.roles.len() && node.view().volume.census.roles[r.new as int].kind == 0);
    assert(r.account > 0 ==> r.group < index.view().groups.len() && r.bitmap == index.view().groups[r.group as int].block_bitmap);
    assert(valid(r, node.view())) by { reveal(valid); }
    let mut k = 0usize;
    while k < n
        invariant node.wf(), patches.wf(), n == patches.view().len(), n <= 4096, k <= n, valid(r, node.view()),
            r.account == account, r.bitmap == bitmap, r.group == group, r.width == width, r.new == new, r.old == old, r.refs == refs,
            logical.len() == 4096, logical@ == node.view().volume.index.groups[group as int].allocation.raw,
            index.view() == node.view().volume.index,
            forall|j: int| 0 <= j < k ==> (#[trigger] patches.view()[j]).block < blocks
                && (forall|i: int| 0 <= i < 4096 && !allowed(r, patches.view()[j].block, i) ==> #[trigger] patches.view()[j].image[i] == reference(r, node.view(), patches.view()[j].block)[i]),
            blocks == node.view().volume.index.blocks,
        decreases n - k,
    {
        proof { reveal(valid); }
        let image = patches.at(k).unwrap(); let block = image.block(); if block >= blocks { return None; }
        let original = match index.source().block(block) { Some(source) => source, None => { return None; } };
        let before = if account > 0 && block == bitmap { logical } else { original.as_slice() };
        if !bytes_confined(before, image.as_slice(), r, block) { return None; }
        if account > 0 && block == bitmap {
            let bit = account % 32768; let byte = (bit / 8) as usize; let mask = 1u8 << (bit % 8); let taking = account == new && new > 0;
            let expected = if taking { logical[byte] | mask } else { logical[byte] & !mask };
            if image.as_slice()[byte] != expected { return None; }
        }
        if account > 0 && block == 1 {
            let position = group as usize * width;
            if bytes::read_le16(image.as_slice(), position + 18) != Some(bytes::read_le16(original.as_slice(), position + 18).unwrap() & !2u16) { return None; }
        }
        if block == 0 {
            if bytes::read_le32(image.as_slice(), 1116).unwrap() != bytes::read_le32(original.as_slice(), 1116).unwrap() | 8u32
                || bytes::read_le32(image.as_slice(), 1120).unwrap() != bytes::read_le32(original.as_slice(), 1120).unwrap() | 4u32 { return None; }
        }
        if old > 0 && block == old && new != old && refs > 1 && bytes::read_le32(image.as_slice(), 4).unwrap() != refs - 1 { return None; }
        k += 1;
    }
    Some(r)
}

pub proof fn a_shared_blocks_entry_and_value_bytes_are_outside_write_authority(r: Region, node: NodeView, images: Seq<crate::transaction::ImageView>, k: int, i: int)
    requires confined(r, node, images), 0 <= k < images.len(), images[k].block == r.old, r.old > 1, r.old != r.new, r.refs > 1,
        r.old != r.inode_block, r.account == 0 || r.old != r.bitmap, 32 <= i < 4096,
    ensures images[k].image[i] == xattr_source::block_bytes(node.volume.index, r.old as nat)[i],
{ reveal(valid); }
pub proof fn another_inodes_bytes_in_the_same_block_are_outside_write_authority(r: Region, node: NodeView, images: Seq<crate::transaction::ImageView>, k: int, i: int)
    requires confined(r, node, images), 0 <= k < images.len(), images[k].block == r.inode_block, 0 <= i < 4096, !(r.offset <= i < r.offset + 256),
    ensures images[k].image[i] == xattr_source::block_bytes(node.volume.index, r.inode_block as nat)[i],
{ reveal(valid); }

}
