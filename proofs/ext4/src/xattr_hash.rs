// SPDX-License-Identifier: MPL-2.0

//! Linux unsigned xattr entry hashes and the zero-stopping block hash.
//! Hashes are cache hints; full namespace/name/value bytes establish identity.

use vstd::prelude::*;
use crate::bytes;

verus! {

pub open spec fn rotate5(x: u32) -> u32 { (x << 5) ^ (x >> 27) }
pub open spec fn rotate16(x: u32) -> u32 { (x << 16) ^ (x >> 16) }
pub open spec fn names(name: Seq<u8>) -> u32 decreases name.len() {
    if name.len() == 0 { 0 } else { rotate5(names(name.drop_last())) ^ name.last() as u32 }
}
pub open spec fn word(value: Seq<u8>, i: nat) -> u32 {
    let padded = value + Seq::new(((4 - value.len() % 4) % 4) as nat, |j: int| 0u8);
    bytes::le32(padded, i as int * 4) as u32
}
#[verifier::opaque]
pub open spec fn values(value: Seq<u8>, seed: u32, length: nat) -> u32 decreases length {
    if length == 0 { seed } else { rotate16(values(value, seed, (length - 1) as nat)) ^ word(value, (length - 1) as nat) }
}
pub open spec fn entry(name: Seq<u8>, value: Seq<u8>) -> u32 { values(value, names(name), (value.len() + 3) / 4) }
#[verifier::opaque]
pub open spec fn prefix(hashes: Seq<u32>, length: nat) -> u32 decreases length {
    if length == 0 { 0 } else {
        let previous = prefix(hashes, (length - 1) as nat);
        if hashes[length as int - 1] == 0 || exists|i: int| 0 <= i < length - 1 && #[trigger] hashes[i] == 0 { 0 }
        else { rotate16(previous) ^ hashes[length as int - 1] }
    }
}
pub fn entry_hash(name: &[u8], value: &[u8]) -> (r: Option<u32>)
    ensures match r { Some(hash) => name.len() <= 255 && value.len() <= 65536 && hash == entry(name@, value@),
        None => name.len() > 255 || value.len() > 65536 },
{
    if name.len() > 255 || value.len() > 65536 { return None; }
    let mut hash = 0u32;
    let mut i = 0usize;
    while i < name.len()
        invariant i <= name.len() <= 255, hash == names(name@.take(i as int)),
        decreases name.len() - i,
    {
        hash = (hash << 5) ^ (hash >> 27) ^ name[i] as u32;
        assert(name@.take(i as int + 1).drop_last() =~= name@.take(i as int));
        i += 1;
    }
    assert(name@.take(i as int) =~= name@);
    let count = (value.len() + 3) / 4;
    let mut i = 0usize;
    assert(values(value@, hash, 0) == hash) by { reveal(values); }
    while i < count
        invariant value.len() <= 65536, count == (value.len() + 3) / 4, i <= count <= 16384,
            hash == values(value@, names(name@), i as nat),
        decreases count - i,
    {
        let start = i * 4;
        let mut raw = [0u8; 4];
        let mut j = 0usize;
        while j < 4
            invariant value.len() <= 65536, start == i * 4, i < count <= 16384, j <= 4,
                forall|k: int| 0 <= k < j ==> (#[trigger] raw@[k]) == if start + k < value.len() { value@[start + k] } else { 0u8 },
            decreases 4 - j,
        { raw[j] = if start + j < value.len() { value[start + j] } else { 0u8 }; j += 1; }
        let ghost padded = value@ + Seq::new(((4 - value@.len() % 4) % 4) as nat, |j: int| 0u8);
        assert(raw@ =~= padded.subrange(start as int, start as int + 4));
        let v = bytes::read_le32(&raw, 0).unwrap();
        hash = (hash << 16) ^ (hash >> 16) ^ v;
        assert(hash == values(value@, names(name@), i as nat + 1)) by { reveal(values); }
        i += 1;
    }
    Some(hash)
}
pub fn block_hash(hashes: &[u32]) -> (r: Option<u32>)
    ensures match r { Some(hash) => hashes.len() <= 4096 && hash == prefix(hashes@, hashes.len() as nat), None => hashes.len() > 4096 },
{
    if hashes.len() > 4096 { return None; }
    let mut hash = 0u32;
    let mut zero = false;
    let mut i = 0usize;
    assert(prefix(hashes@, 0) == 0) by { reveal(prefix); }
    while i < hashes.len()
        invariant i <= hashes.len() <= 4096, hash == prefix(hashes@, i as nat),
            zero == (exists|j: int| 0 <= j < i && #[trigger] hashes@[j] == 0), zero ==> hash == 0,
        decreases hashes.len() - i,
    {
        if hashes[i] == 0 { zero = true; }
        hash = if zero { 0u32 } else { (hash << 16) ^ (hash >> 16) ^ hashes[i] };
        assert(hash == prefix(hashes@, i as nat + 1)) by { reveal(prefix); }
        i += 1;
    }
    Some(hash)
}
pub proof fn any_zero_entry_hash_disables_block_sharing(hashes: Seq<u32>, i: int)
    requires 0 <= i < hashes.len(), hashes[i] == 0,
    ensures prefix(hashes, hashes.len()) == 0,
{ reveal(prefix); }

}
