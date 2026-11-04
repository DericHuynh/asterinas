// SPDX-License-Identifier: MPL-2.0

//! Linux xattr entry decoding, exact namespace/name keys and bounded values.
//! Value-inode descriptors are data, never permission to dereference an inode.

use vstd::prelude::*;
use crate::bytes;

verus! {

pub const MAX_VALUE: u32 = 16777216;

#[derive(Clone, Copy)]
pub struct Entry {
    pub position: usize, pub next: usize, pub namespace: u8, pub name_length: usize,
    pub value_offset: usize, pub value_size: u32, pub value_inode: u32, pub hash: u32,
}

pub open spec fn padded(value: nat) -> nat { (value + 3) / 4 * 4 }
pub open spec fn name(raw: Seq<u8>, e: Entry) -> Seq<u8> { raw.subrange(e.position as int + 16, e.position as int + 16 + e.name_length as int) }
pub open spec fn same_key(raw: Seq<u8>, a: Entry, b: Entry) -> bool { a.namespace == b.namespace && name(raw, a) == name(raw, b) }

#[verifier::opaque]
pub open spec fn record(raw: Seq<u8>, base: usize, ea: bool, inodes: u32, e: Entry) -> bool {
    &&& raw.len() <= 65536 && e.position as nat + 16 <= raw.len() && base <= raw.len()
    &&& bytes::le32(raw, e.position as int) != 0
    &&& e.next as nat == e.position as nat + 16 + padded(e.name_length as nat) && e.next as nat + 4 <= raw.len()
    &&& e.name_length == raw[e.position as int] && e.namespace == raw[e.position as int + 1]
    &&& e.value_size as nat == bytes::le32(raw, e.position as int + 8)
    &&& e.value_inode as nat == bytes::le32(raw, e.position as int + 4) && e.hash as nat == bytes::le32(raw, e.position as int + 12)
    &&& e.value_size <= MAX_VALUE
    &&& e.value_offset as nat == if e.value_size == 0 || e.value_inode != 0 { 0nat } else { base as nat + bytes::le16(raw, e.position as int + 2) }
    &&& (forall|i: int| 0 <= i < e.name_length ==> #[trigger] raw[e.position as int + 16 + i] != 0)
    &&& (if e.value_inode == 0 {
        e.value_size == 0 || e.value_offset as nat + padded(e.value_size as nat) <= raw.len()
    } else { ea && 0 < e.value_size && e.value_inode != 2 && (e.value_inode >= 11 || e.value_inode == 3 || e.value_inode == 4) && e.value_inode <= inodes })
}

pub fn decode(raw: &[u8], position: usize, base: usize, ea: bool, inodes: u32) -> (r: Option<Entry>)
    ensures match r { Some(e) => record(raw@, base, ea, inodes, e) && e.position == position, None => true },
{
    if raw.len() > 65536 || position > raw.len() || raw.len() - position < 16 || base > raw.len() { return None; }
    if bytes::read_le32(raw, position).unwrap() == 0 { return None; }
    let length = raw[position] as usize;
    let step = 16 + (length + 3) / 4 * 4;
    if step > raw.len() - position || raw.len() - position - step < 4 { return None; }
    let size = bytes::read_le32(raw, position + 8).unwrap();
    let inode = bytes::read_le32(raw, position + 4).unwrap();
    if size > MAX_VALUE { return None; }
    let offset = if size == 0 || inode != 0 { 0usize } else { base + bytes::read_le16(raw, position + 2).unwrap() as usize };
    if inode != 0 {
        if !ea || size == 0 || inode == 2 || (inode < 11 && inode != 3 && inode != 4) || inode > inodes { return None; }
    } else if size != 0 && (offset > raw.len() || (size as u64 + 3) / 4 * 4 > (raw.len() - offset) as u64) { return None; }
    let mut i = 0usize;
    while i < length
        invariant raw.len() <= 65536, position + step + 4 <= raw.len(), step == 16 + (length + 3) / 4 * 4,
            length <= 255, i <= length, forall|j: int| 0 <= j < i ==> #[trigger] raw@[position as int + 16 + j] != 0,
        decreases length - i,
    {
        if raw[position + 16 + i] == 0 { return None; }
        i += 1;
    }
    let e = Entry { position, next: position + step, namespace: raw[position + 1], name_length: length,
        value_offset: offset, value_size: size, value_inode: inode, hash: bytes::read_le32(raw, position + 12).unwrap() };
    assert(record(raw@, base, ea, inodes, e)) by { reveal(record); }
    Some(e)
}

pub open spec fn lex_less(a: Seq<u8>, b: Seq<u8>) -> bool {
    a.len() == b.len() && exists|i: int| 0 <= i < a.len() && a[i] < b[i]
        && (forall|j: int| 0 <= j < i ==> #[trigger] a[j] == b[j])
}

pub open spec fn key_less(raw: Seq<u8>, a: Entry, b: Entry) -> bool {
    a.namespace < b.namespace || a.namespace == b.namespace && (a.name_length < b.name_length
        || a.name_length == b.name_length && lex_less(name(raw, a), name(raw, b)))
}

pub(crate) fn before(raw: &[u8], a: Entry, b: Entry) -> (r: bool)
    requires a.position as nat + 16 + a.name_length <= raw.len(), b.position as nat + 16 + b.name_length <= raw.len(),
    ensures r == key_less(raw@, a, b),
{
    if a.namespace != b.namespace { return a.namespace < b.namespace; }
    if a.name_length != b.name_length { return a.name_length < b.name_length; }
    let an = &raw[a.position + 16..a.position + 16 + a.name_length];
    let bn = &raw[b.position + 16..b.position + 16 + b.name_length];
    assert(an@ == name(raw@, a) && bn@ == name(raw@, b));
    let mut i = 0usize;
    while i < a.name_length
        invariant i <= a.name_length == b.name_length,
            a.namespace == b.namespace, an@ == name(raw@, a), bn@ == name(raw@, b),
            an.len() == a.name_length, bn.len() == b.name_length,
            a.position as nat + 16 + a.name_length <= raw.len(), b.position as nat + 16 + b.name_length <= raw.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] an@[j] == bn@[j],
        decreases a.name_length - i,
    {
        let x = an[i];
        let y = bn[i];
        if x != y {
            if x < y {
                assert(lex_less(name(raw@, a), name(raw@, b))) by { assert(exists|k: int| 0 <= k < a.name_length && name(raw@, a)[k] < name(raw@, b)[k] && (forall|j: int| 0 <= j < k ==> #[trigger] name(raw@, a)[j] == name(raw@, b)[j])); }
            } else {
                assert(!lex_less(name(raw@, a), name(raw@, b))) by {
                    if lex_less(name(raw@, a), name(raw@, b)) {
                        let k = choose|k: int| 0 <= k < a.name_length && name(raw@, a)[k] < name(raw@, b)[k] && (forall|j: int| 0 <= j < k ==> #[trigger] name(raw@, a)[j] == name(raw@, b)[j]);
                        if k < i { assert(name(raw@, a)[k] == name(raw@, b)[k]); }
                        if i < k { assert(name(raw@, a)[i as int] == name(raw@, b)[i as int]); }
                    }
                }
            }
            return x < y;
        }
        i += 1;
    }
    assert(name(raw@, a) =~= name(raw@, b));
    false
}

pub proof fn decoded_values_cannot_escape_their_container(raw: Seq<u8>, base: usize, ea: bool, inodes: u32, e: Entry)
    requires record(raw, base, ea, inodes, e), e.value_inode == 0,
    ensures e.position + 16 + e.name_length <= raw.len(), e.value_offset as nat + e.value_size <= raw.len(),
        e.value_size > 0 ==> e.value_offset as nat + padded(e.value_size as nat) <= raw.len(),
{
    reveal(record);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(e.name_length as int + 3, 4);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(e.value_size as int + 3, 4);
}

pub proof fn decoded_entry_has_a_bounded_name(raw: Seq<u8>, base: usize, ea: bool, inodes: u32, e: Entry)
    requires record(raw, base, ea, inodes, e),
    ensures raw.len() <= 65536, e.position <= 65520, e.name_length <= 255,
        e.position as nat + 16 + e.name_length <= raw.len(), e.next > e.position, e.next as nat + 4 <= raw.len(),
{
    reveal(record);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(e.name_length as int + 3, 4);
}

}
