// SPDX-License-Identifier: MPL-2.0

//! Checked leaf extents. Tree traversal and global physical ownership are
//! separate obligations; this module never grants an allocation capability.

use vstd::prelude::*;
use crate::bytes::{le16, le32, read_le16, read_le32, encode_le16, encode_le32};

verus! {

// Linux ext4_valid_extent rejects a u32 exclusive end that wraps to zero.
// Logical block MAX is reserved; the largest accepted exclusive end is MAX.
pub const MAX_LOGICAL_END: u64 = 4294967295;

pub struct Extent {
    pub logical: u32,
    pub length: u32,
    pub physical: u32,
    pub initialized: bool,
}

pub enum Mapping { Data(u32), Zero }

pub open spec fn length(raw: nat) -> nat {
    if raw <= 32768 { raw } else { (raw - 32768) as nat }
}

pub open spec fn accepted(s: Seq<u8>, o: int, blocks: u32) -> bool {
    &&& 0 <= o && o + 12 <= s.len()
    &&& le16(s, o + 6) == 0
    &&& le16(s, o + 4) > 0
    &&& le32(s, o) + length(le16(s, o + 4)) <= MAX_LOGICAL_END
    &&& le32(s, o + 8) > 0
    &&& le32(s, o + 8) + length(le16(s, o + 4)) <= blocks
}

impl Extent {
    pub open spec fn wf(&self, blocks: u32) -> bool {
        &&& 0 < self.length <= if self.initialized { 32768u32 } else { 32767u32 }
        &&& self.logical as int + self.length <= MAX_LOGICAL_END
        &&& 0 < self.physical
        &&& self.physical as int + self.length <= blocks
    }

    pub open spec fn represents(&self, s: Seq<u8>, o: int) -> bool {
        &&& self.logical as nat == le32(s, o)
        &&& self.physical as nat == le32(s, o + 8)
        &&& self.length as nat == length(le16(s, o + 4))
        &&& self.initialized == (le16(s, o + 4) <= 32768)
    }

    pub fn valid(&self, blocks: u32) -> (r: bool)
        ensures r == self.wf(blocks),
    {
        self.length > 0 && self.length <= (if self.initialized { 32768 } else { 32767 })
            && self.logical as u64 + self.length as u64 <= MAX_LOGICAL_END
            && self.physical > 0 && self.physical as u64 + self.length as u64 <= blocks as u64
    }

    pub fn resolve(&self, logical: u32, blocks: u32) -> (r: Option<Mapping>)
        ensures match r {
            Some(Mapping::Data(b)) => self.wf(blocks) && self.initialized
                && self.logical <= logical < self.logical as int + self.length
                && b as int == self.physical as int + logical - self.logical && b < blocks,
            Some(Mapping::Zero) => self.wf(blocks) && !self.initialized
                && self.logical <= logical < self.logical as int + self.length,
            None => !self.wf(blocks) || logical < self.logical
                || logical >= self.logical as int + self.length,
        },
    {
        if !self.valid(blocks) || logical < self.logical
            || logical as u64 >= self.logical as u64 + self.length as u64 { return None; }
        if !self.initialized { Some(Mapping::Zero) }
        else { Some(Mapping::Data(self.physical + (logical - self.logical))) }
    }

    pub fn encode(&self, blocks: u32) -> (r: Option<[u8; 12]>)
        ensures match r {
            Some(s) => self.wf(blocks) && accepted(s@, 0, blocks) && self.represents(s@, 0),
            None => !self.wf(blocks),
        },
    {
        if !self.valid(blocks) { return None; }
        let l = encode_le32(self.logical);
        let p = encode_le32(self.physical);
        let raw = if self.initialized { self.length as u16 }
            else { (self.length + 32768) as u16 };
        let n = encode_le16(raw);
        Some([l[0], l[1], l[2], l[3], n[0], n[1], 0, 0, p[0], p[1], p[2], p[3]])
    }
}

pub fn parse(s: &[u8], o: usize, blocks: u32) -> (r: Option<Extent>)
    ensures match r {
        Some(e) => accepted(s@, o as int, blocks) && e.wf(blocks) && e.represents(s@, o as int),
        None => !accepted(s@, o as int, blocks),
    },
{
    if o > s.len() || s.len() - o < 12 { return None; }
    let logical = read_le32(s, o).unwrap();
    let raw = read_le16(s, o + 4).unwrap();
    let high = read_le16(s, o + 6).unwrap();
    let physical = read_le32(s, o + 8).unwrap();
    let count = if raw <= 32768 { raw as u32 } else { raw as u32 - 32768 };
    let e = Extent { logical, physical, length: count, initialized: raw <= 32768 };
    if high != 0 || !e.valid(blocks) { None } else { Some(e) }
}

pub open spec fn leaf_header(s: Seq<u8>) -> bool {
    &&& s.len() == 60
    &&& le16(s, 0) == 0xf30a
    &&& le16(s, 2) <= 4
    &&& le16(s, 4) == 4
    &&& le16(s, 6) == 0
}

pub open spec fn entry_offset(i: int) -> int { 12 + 12 * i }

pub open spec fn leaf_entries(s: Seq<u8>, count: nat, blocks: u32) -> bool {
    &&& (forall|i: int| 0 <= i < count ==> #[trigger] accepted(s, entry_offset(i), blocks))
    &&& (forall|i: int| 0 <= i < count - 1 ==>
        le32(s, entry_offset(i)) + length(le16(s, entry_offset(i) + 4))
        <= #[trigger] le32(s, entry_offset(i + 1)))
}

/// Initial inline-root subset: at most four leaf extents, with no recursion or
/// allocation. A nonzero tree depth is explicitly rejected.
pub fn validate_inline_root(s: &[u8], blocks: u32) -> (r: Option<u16>)
    ensures match r {
        Some(n) => leaf_header(s@) && n as nat == le16(s@, 2)
            && leaf_entries(s@, n as nat, blocks),
        None => !leaf_header(s@) || !leaf_entries(s@, le16(s@, 2), blocks),
    },
{
    if s.len() != 60 { return None; }
    let n = read_le16(s, 2).unwrap();
    if read_le16(s, 0).unwrap() != 0xf30a || n > 4
        || read_le16(s, 4).unwrap() != 4 || read_le16(s, 6).unwrap() != 0 { return None; }
    let mut i = 0usize;
    let mut end = 0u64;
    while i < n as usize
        invariant i <= n <= 4, leaf_header(s@), n as nat == le16(s@, 2),
            leaf_entries(s@, i as nat, blocks),
            i == 0 ==> end == 0,
            i > 0 ==> end as int == le32(s@, entry_offset(i as int - 1))
                + length(le16(s@, entry_offset(i as int - 1) + 4)),
        decreases n as usize - i,
    {
        let o = 12 + 12 * i;
        let e = match parse(s, o, blocks) {
            Some(e) => e,
            None => {
                proof {
                    if leaf_entries(s@, n as nat, blocks) {
                        assert(accepted(s@, entry_offset(i as int), blocks));
                    }
                }
                return None;
            }
        };
        if (e.logical as u64) < end {
            proof {
                if i == 0 { assert(end == 0); }
                if leaf_entries(s@, n as nat, blocks) {
                    assert(le32(s@, entry_offset(i as int - 1))
                        + length(le16(s@, entry_offset(i as int - 1) + 4))
                        <= le32(s@, entry_offset((i as int - 1) + 1)));
                }
            }
            return None;
        }
        proof {
            assert forall|j: int| 0 <= j < i + 1 implies
                #[trigger] accepted(s@, entry_offset(j), blocks) by {
                if j < i { assert(accepted(s@, entry_offset(j), blocks)); }
            }
            assert forall|j: int| 0 <= j < i implies
                le32(s@, entry_offset(j)) + length(le16(s@, entry_offset(j) + 4))
                    <= #[trigger] le32(s@, entry_offset(j + 1)) by {
                if j < i as int - 1 {
                    assert(le32(s@, entry_offset(j)) + length(le16(s@, entry_offset(j) + 4))
                        <= le32(s@, entry_offset(j + 1)));
                }
            }
        }
        end = e.logical as u64 + e.length as u64;
        i += 1;
    }
    Some(n)
}

pub proof fn disjoint_logical_ranges(s: Seq<u8>, n: nat, blocks: u32, i: int, j: int)
    requires leaf_entries(s, n, blocks), 0 <= i < j < n,
    ensures le32(s, entry_offset(i)) + length(le16(s, entry_offset(i) + 4))
        <= le32(s, entry_offset(j)),
    decreases j - i,
{
    assert(accepted(s, entry_offset(i), blocks));
    assert(le32(s, entry_offset(i)) + length(le16(s, entry_offset(i) + 4))
        <= le32(s, entry_offset(i + 1)));
    if j > i + 1 { disjoint_logical_ranges(s, n, blocks, i + 1, j); }
}

}
