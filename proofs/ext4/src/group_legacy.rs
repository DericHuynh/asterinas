// SPDX-License-Identifier: MPL-2.0

//! Legacy ext4 GDT_CSUM descriptor CRC16. It is distinct from METADATA_CSUM:
//! the legacy feature does not authenticate bitmap contents with bitmap CRCs.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::bytes;

verus! {

pub open spec fn bit(c: u16) -> u16 {
    if c & 1 != 0 { (c >> 1) ^ 0xa001u16 } else { c >> 1 }
}
pub open spec fn steps(c: u16, n: nat) -> u16
    decreases n,
{
    if n == 0 { c } else { bit(steps(c, (n - 1) as nat)) }
}
pub open spec fn byte(c: u16, b: u8) -> u16 { steps(c ^ b as u16, 8) }
pub open spec fn fold(c: u16, s: Seq<u8>) -> u16
    decreases s.len(),
{
    if s.len() == 0 { c } else { byte(fold(c, s.drop_last()), s.last()) }
}
pub open spec fn geometry(uuid: Seq<u8>, descriptor: Seq<u8>) -> bool {
    uuid.len() == 16 && 32 <= descriptor.len() <= 65536
}
pub open spec fn descriptor_sum(uuid: Seq<u8>, group: u32, descriptor: Seq<u8>) -> u16 {
    fold(fold(fold(fold(0xffffu16, uuid), bytes::encoded_le(group)),
        descriptor.subrange(0, 30)), descriptor.subrange(32, descriptor.len() as int))
}
pub open spec fn valid(uuid: Seq<u8>, group: u32, descriptor: Seq<u8>) -> bool {
    geometry(uuid, descriptor) && bytes::le16(descriptor, 30) == descriptor_sum(uuid, group, descriptor)
}

pub fn crc16(seed: u16, raw: &[u8]) -> (r: u16)
    ensures r == fold(seed, raw@),
{
    let mut value = seed;
    let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len(), value == fold(seed, raw@.subrange(0, i as int)),
        decreases raw.len() - i,
    {
        let old_value = value;
        value = value ^ raw[i] as u16;
        let mut bit = 0u8;
        while bit < 8
            invariant bit <= 8, value == steps(old_value ^ raw@[i as int] as u16, bit as nat),
            decreases 8 - bit,
        {
            value = if value & 1 != 0 { (value >> 1) ^ 0xa001u16 } else { value >> 1 };
            bit += 1;
        }
        proof {
            assert(raw@.subrange(0, i as int + 1).drop_last() =~= raw@.subrange(0, i as int));
            assert(raw@.subrange(0, i as int + 1).last() == raw@[i as int]);
        }
        i += 1;
    }
    proof { assert(raw@.subrange(0, raw.len() as int) =~= raw@); }
    value
}

/// Linux folds UUID, little-endian group number and descriptor bytes, skipping
/// (rather than zeroing) the two-byte bg_checksum field at offset 30.
pub fn descriptor_checksum(uuid: &[u8], group: u32, descriptor: &[u8]) -> (r: Option<u16>)
    ensures match r {
        Some(c) => geometry(uuid@, descriptor@) && c == descriptor_sum(uuid@, group, descriptor@),
        None => !geometry(uuid@, descriptor@),
    },
{
    if uuid.len() != 16 || descriptor.len() < 32 || descriptor.len() > 65536 { return None; }
    let group_bytes = bytes::encode_le32(group);
    let a = crc16(0xffffu16, uuid);
    let b = crc16(a, &group_bytes);
    let c = crc16(b, &descriptor[..30]);
    Some(crc16(c, &descriptor[32..]))
}

pub fn descriptor_valid(uuid: &[u8], group: u32, descriptor: &[u8]) -> (r: bool)
    ensures r == valid(uuid@, group, descriptor@),
{
    match descriptor_checksum(uuid, group, descriptor) {
        Some(sum) => bytes::read_le16(descriptor, 30) == Some(sum),
        None => false,
    }
}

pub fn seal_descriptor(uuid: &[u8], group: u32, descriptor: &[u8]) -> (r: Option<Vec<u8>>)
    ensures match r {
        Some(sealed) => geometry(uuid@, descriptor@) && sealed.len() == descriptor.len()
            && valid(uuid@, group, sealed@)
            && forall|i: int| 0 <= i < descriptor.len() && (i < 30 || i >= 32)
                ==> #[trigger] sealed@[i] == descriptor@[i],
        None => !geometry(uuid@, descriptor@),
    },
{
    let sum = match descriptor_checksum(uuid, group, descriptor) {
        Some(sum) => sum, None => { return None; }
    };
    let mut result = Vec::<u8>::new();
    let mut i = 0usize;
    while i < descriptor.len()
        invariant i <= descriptor.len(), result@ == descriptor@.subrange(0, i as int),
        decreases descriptor.len() - i,
    { result.push(descriptor[i]); i += 1; }
    proof { assert(result@ =~= descriptor@); }
    let encoded = bytes::encode_le16(sum);
    result.set(30, encoded[0]); result.set(31, encoded[1]);
    proof {
        assert(result@.subrange(0, 30) =~= descriptor@.subrange(0, 30));
        assert(result@.subrange(32, result.len() as int) =~= descriptor@.subrange(32, descriptor.len() as int));
    }
    Some(result)
}

pub struct LazyState {
    pub block_uninitialized: bool, pub inode_uninitialized: bool, pub inode_table_zeroed: bool,
}

/// A checksum-valid descriptor supplies lazy-state flags; actual canonical
/// bitmap synthesis, initialized-table provenance and global ownership are
/// checked separately before any inode or block can be used.
pub fn lazy_state(uuid: &[u8], group: u32, descriptor: &[u8]) -> (r: Option<LazyState>)
    ensures match r {
        Some(state) => valid(uuid@, group, descriptor@)
            && bytes::le16(descriptor@, 18) as u16 & !7u16 == 0
            && state.block_uninitialized == (bytes::le16(descriptor@, 18) as u16 & 2 != 0)
            && state.inode_uninitialized == (bytes::le16(descriptor@, 18) as u16 & 1 != 0)
            && state.inode_table_zeroed == (bytes::le16(descriptor@, 18) as u16 & 4 != 0),
        None => !valid(uuid@, group, descriptor@)
            || bytes::le16(descriptor@, 18) as u16 & !7u16 != 0,
    },
{
    if !descriptor_valid(uuid, group, descriptor) { return None; }
    let flags = bytes::read_le16(descriptor, 18).unwrap();
    if flags & !7u16 != 0 { return None; }
    Some(LazyState { block_uninitialized: flags & 2 != 0, inode_uninitialized: flags & 1 != 0,
        inode_table_zeroed: flags & 4 != 0 })
}

}
