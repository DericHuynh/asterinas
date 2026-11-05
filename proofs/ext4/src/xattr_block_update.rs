// SPDX-License-Identifier: MPL-2.0

//! Bounded block selection and candidate allocation-accounting images for
//! xattr copy-on-write. Complete filesystem admission checks the combined
//! inode/block/bitmap/descriptor/superblock transaction before dispatch.

use vstd::prelude::*;
use crate::{allocation::Allocation, bytes, crc, patch_set::PatchSet, snapshot::Snapshot, xattr};

verus! {

pub fn free_block(volume: &Allocation<'_>) -> (r: Option<u32>)
    ensures volume.wf(), match r { Some(block) => block > 1 && block < volume.view().census.roles.len()
        && volume.view().census.roles[block as int].kind == 0, None => true },
{
    let census = volume.census(); let n = census.block_count(); let mut i = 2u32;
    while i < n invariant volume.wf(), census.view() == volume.view().census, 2 <= i <= n <= 1048576,
        n == census.view().roles.len(), decreases n - i,
    { if census.role_of(i).unwrap().kind == 0 { return Some(i); } i += 1; }
    None
}
fn copy(raw: &[u8]) -> (r: Option<Vec<u8>>)
    ensures match r { Some(next) => raw.len() <= 4096 && next@ == raw@, None => raw.len() > 4096 },
{
    if raw.len() > 4096 { return None; }
    let mut next = Vec::new(); let mut i = 0usize;
    while i < raw.len() invariant i <= raw.len() <= 4096, next@ == raw@.take(i as int), decreases raw.len() - i,
    { next.push(raw[i]); assert(next@ =~= raw@.take(i as int + 1)); i += 1; }
    Some(next)
}
pub open spec fn refcount_frame(before: Seq<u8>, after: Seq<u8>) -> bool {
    before.len() == 4096 && after.len() == 4096 && forall|i: int| 0 <= i < 4096 && !(4 <= i < 8) && !(16 <= i < 20) ==> #[trigger] after[i] == before[i]
}
pub fn detach_shared(raw: &[u8], physical: u32, seed: u32, inodes: u32) -> (r: Option<Vec<u8>>)
    ensures match r { Some(after) => refcount_frame(raw@, after@) && xattr::header(after@, physical as u64, seed, true)
        && bytes::le32(after@, 4) + 1 == bytes::le32(raw@, 4), None => true },
{
    hide(crate::crc::fold);
    if raw.len() != 4096 { return None; }
    let block = match xattr::parse_block(raw, physical as u64, seed, true, false, inodes) { Some(block) => block, None => { return None; } };
    let refs = block.refcount(); if refs < 2 { return None; }
    let mut after = copy(raw).unwrap(); bytes::write_le32(after.as_mut_slice(), 4, refs - 1);
    let checksum = xattr::checksum(&after, physical as u64, seed).unwrap(); bytes::write_le32(after.as_mut_slice(), 16, checksum);
    if xattr::parse_block(&after, physical as u64, seed, true, false, inodes).is_none() { return None; }
    if bytes::read_le32(&after, 4).unwrap() != refs - 1 { return None; }
    let mut i = 0usize;
    while i < 4096
        invariant raw.len() == 4096, after.len() == 4096, i <= 4096,
            forall|j: int| 0 <= j < i && !(4 <= j < 8) && !(16 <= j < 20) ==> #[trigger] after@[j] == raw@[j],
        decreases 4096 - i,
    { if !(4 <= i && i < 8) && !(16 <= i && i < 20) && after[i] != raw[i] { return None; } i += 1; }
    assert(refcount_frame(raw@, after@));
    Some(after)
}

// Exactly one allocation bit changes per lifecycle operation: an exclusive
// old block is reused, so allocating and freeing never occur together.
pub fn accounting(volume: &Allocation<'_>, physical: u32, taking: bool) -> (r: Option<PatchSet>)
    ensures volume.wf(), match r { Some(patches) => patches.wf(), None => true },
{
    hide(crate::crc::fold);
    let index = volume.index(); let (blocks, _, _, seed) = index.parameters();
    if physical <= 1 || physical >= blocks || physical >= 1048576 { return None; }
    let role = match volume.census().role_of(physical) { Some(role) => role, None => { return None; } };
    if taking && role.kind != 0 || !taking && role.kind != 7 { return None; }
    let number = physical / 32768; let bit = physical % 32768;
    let meta = match index.get(number) { Some(meta) => meta, None => { return None; } };
    let descriptor = meta.descriptor(); if descriptor.len() != 32 && descriptor.len() != 64 { return None; }
    let (bitmap, _) = meta.bitmaps(); let logical = bitmap.raw_image(); if logical.len() != 4096 { return None; }
    if bitmap.is_set(bit) != Some(!taking) { return None; }
    let mut bitmap_bytes = copy(logical).unwrap(); let byte = (bit / 8) as usize;
    let mask = 1u8 << (bit % 8); let old = bitmap_bytes[byte]; bitmap_bytes.set(byte, if taking { old | mask } else { old & !mask });
    let mut desc = copy(descriptor).unwrap(); let free = bytes::read_le16(&desc, 12).unwrap();
    if taking && free == 0 || !taking && free == u16::MAX { return None; }
    let updated = bytes::encode_le16(if taking { free - 1 } else { free + 1 }); bytes::write_bytes(desc.as_mut_slice(), 12, &updated);
    let flags = bytes::read_le16(&desc, 18).unwrap() & !2u16; let flags = bytes::encode_le16(flags); bytes::write_bytes(desc.as_mut_slice(), 18, &flags);
    let crc = crc::crc32c(seed, &bitmap_bytes); let low = bytes::encode_le16((crc % 65536) as u16); bytes::write_bytes(desc.as_mut_slice(), 24, &low);
    if desc.len() == 64 { let high = bytes::encode_le16((crc / 65536) as u16); bytes::write_bytes(desc.as_mut_slice(), 56, &high); }
    bytes::write_bytes(desc.as_mut_slice(), 30, &[0u8, 0u8]); let group = bytes::encode_le32(number);
    let partial = crc::crc32c(seed, &group); let crc = crc::crc32c(partial, &desc); let crc = bytes::encode_le16((crc % 65536) as u16);
    bytes::write_bytes(desc.as_mut_slice(), 30, &crc);
    let gdt_source = match index.source().block(1) { Some(source) => source, None => { return None; } };
    let mut gdt = copy(gdt_source.as_slice()).unwrap();
    if number >= 32 || desc.len() > 64 { return None; }
    assert(number as nat * desc.len() <= 2048) by (nonlinear_arith) requires number < 32, desc.len() <= 64;
    let position = number as usize * desc.len(); if !bytes::write_bytes(gdt.as_mut_slice(), position, &desc) { return None; }
    let primary_source = match index.source().block(0) { Some(source) => source, None => { return None; } };
    let mut primary = copy(primary_source.as_slice()).unwrap(); let free = bytes::read_le32(&primary, 1036).unwrap();
    if taking && free == 0 || !taking && free == u32::MAX { return None; }
    bytes::write_le32(primary.as_mut_slice(), 1036, if taking { free - 1 } else { free + 1 });
    let dirty = bytes::read_le32(&primary, 1120).unwrap() | 4u32; bytes::write_le32(primary.as_mut_slice(), 1120, dirty);
    let crc = crc::crc32c(0xffffffff, &primary[1024..2044]); bytes::write_le32(primary.as_mut_slice(), 2044, crc);
    let mut patches = PatchSet::new();
    patches = match patches.insert(0, &primary) { Ok(patches) => patches, Err(_) => { return None; } };
    patches = match patches.insert(1, &gdt) { Ok(patches) => patches, Err(_) => { return None; } };
    patches = match patches.insert(meta.info().block_bitmap, &bitmap_bytes) { Ok(patches) => patches, Err(_) => { return None; } };
    Some(patches)
}

pub proof fn shared_detachment_preserves_every_entry_and_value_byte(before: Seq<u8>, after: Seq<u8>, i: int)
    requires refcount_frame(before, after), 32 <= i < 4096, ensures after[i] == before[i],
{ }

}
