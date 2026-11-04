// SPDX-License-Identifier: MPL-2.0

//! Linear-directory records for 4 KiB metadata-csum directories. Names are
//! byte strings; UTF-8 is not assumed. This is not namespace authorization.

use vstd::prelude::*;
use crate::bytes::{le16, le32, read_le16, read_le32};
use crate::crc;

verus! {

pub struct Entry {
    pub inode: u32,
    pub next: usize,
    pub name_offset: usize,
    pub name_length: u8,
    pub file_type: u8,
}

pub open spec fn name_ok(s: Seq<u8>, start: int, count: nat) -> bool {
    forall|i: int| 0 <= i < count ==> s[start + i] != 0 && #[trigger] s[start + i] != 47
}

pub open spec fn accepted(s: Seq<u8>, o: int, inodes: u32) -> bool {
    &&& s.len() == 4096
    &&& 0 <= o && o + 8 <= 4084
    &&& o % 4 == 0
    &&& 8 <= le16(s, o + 4)
    &&& le16(s, o + 4) % 4 == 0
    &&& o + le16(s, o + 4) <= 4084
    &&& 8 + s[o + 6] as nat <= le16(s, o + 4)
    &&& le32(s, o) <= inodes
    &&& (le32(s, o) == 0 || (s[o + 6] > 0 && (s[o + 7] == 1 || s[o + 7] == 2)
        && name_ok(s, o + 8, s[o + 6] as nat)))
}

pub fn parse(s: &[u8], o: usize, inodes: u32) -> (r: Option<Entry>)
    ensures match r {
        Some(e) => accepted(s@, o as int, inodes)
            && e.inode as nat == le32(s@, o as int)
            && e.next as int == o as int + le16(s@, o as int + 4)
            && o < e.next <= 4084 && e.name_offset == o + 8
            && e.name_length == s@[o as int + 6] && e.file_type == s@[o as int + 7],
        None => !accepted(s@, o as int, inodes),
    },
{
    if s.len() != 4096 || o > 4076 || o % 4 != 0 { return None; }
    let inode = read_le32(s, o).unwrap();
    let record = read_le16(s, o + 4).unwrap();
    let name_length = s[o + 6];
    let file_type = s[o + 7];
    if record < 8 || record % 4 != 0 || record as usize > 4084 - o
        || 8 + name_length as usize > record as usize || inode > inodes
    { return None; }
    if inode != 0 {
        if name_length == 0 || (file_type != 1 && file_type != 2) { return None; }
        let mut i = 0usize;
        while i < name_length as usize
            invariant i <= name_length, o <= 4076,
                s.len() == 4096, name_length == s@[o as int + 6],
                inode > 0, inode as nat == le32(s@, o as int),
                o + 8 + name_length as int <= 4084,
                name_ok(s@, o as int + 8, i as nat),
            decreases name_length as usize - i,
        {
            if s[o + 8 + i] == 0 || s[o + 8 + i] == 47 {
                proof {
                    if name_ok(s@, o as int + 8, name_length as nat) {
                        assert(s@[o as int + 8 + i as int] != 0
                            && s@[o as int + 8 + i as int] != 47);
                    }
                }
                return None;
            }
            proof {
                assert forall|j: int| 0 <= j < i + 1 implies
                    s@[o as int + 8 + j] != 0 && #[trigger] s@[o as int + 8 + j] != 47 by {
                    if j < i { assert(s@[o as int + 8 + j] != 0 && s@[o as int + 8 + j] != 47); }
                }
            }
            i += 1;
        }
    }
    Some(Entry { inode, next: o + record as usize, name_offset: o + 8, name_length, file_type })
}

/// inode_seed is the raw CRC accumulator after filesystem UUID (or csum_seed),
/// LE inode number, and LE inode generation. Binding it to an inode is a caller
/// obligation, not an authenticity claim about media.
pub fn valid_tail(s: &[u8], inode_seed: u32) -> (r: bool)
    ensures r == (s.len() == 4096 && le32(s@, 4084) == 0 && le16(s@, 4088) == 12
        && s@[4090] == 0 && s@[4091] == 0xde
        && le32(s@, 4092) == crc::fold(inode_seed, s@.subrange(0, 4084)) as nat),
{
    if s.len() != 4096 { return false; }
    if read_le32(s, 4084).unwrap() != 0 || read_le16(s, 4088).unwrap() != 12
        || s[4090] != 0 || s[4091] != 0xde { return false; }
    read_le32(s, 4092).unwrap() == crc::crc32c(inode_seed, &s[0..4084])
}

}
