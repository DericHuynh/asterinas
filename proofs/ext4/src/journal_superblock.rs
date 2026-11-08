// SPDX-License-Identifier: MPL-2.0

//! JBD2 superblock admission, independent of recovery and replay authority.
//! An empty mke2fs journal has no checksum feature. Enabling v3 on disk is a
//! separate crash-safe format transition, not a side effect of this parser.

use vstd::prelude::*;
use crate::bytes::*;
use crate::crc;

verus! {

pub struct JournalInfo {
    pub blocks: u32,
    pub sequence: u32,
    pub start: u32,
    pub csum_v3: bool,
    pub revoke: bool,
    pub uuid_seed: u32,
}

pub open spec fn uuid_matches(s: Seq<u8>, uuid: Seq<u8>) -> bool {
    &&& s.len() >= 64 && uuid.len() == 16
    &&& (forall|i: int| 0 <= i < 16 ==> #[trigger] s[48 + i] == uuid[i])
}

pub fn matching_uuid(s: &[u8], uuid: &[u8]) -> (r: bool)
    ensures r == uuid_matches(s@, uuid@),
{
    if s.len() < 64 || uuid.len() != 16 { return false; }
    let mut i = 0usize;
    while i < 16
        invariant i <= 16, s.len() >= 64, uuid.len() == 16,
            forall|j: int| 0 <= j < i ==> #[trigger] s@[48 + j] == uuid@[j],
        decreases 16 - i,
    {
        if s[48 + i] != uuid[i] {
            proof {
                if uuid_matches(s@, uuid@) { assert(s@[48 + i as int] == uuid@[i as int]); }
            }
            return false;
        }
        proof {
            assert forall|j: int| 0 <= j < i + 1 implies #[trigger] s@[48 + j] == uuid@[j] by {
                if j < i { assert(s@[48 + j] == uuid@[j]); }
            }
        }
        i += 1;
    }
    true
}

pub open spec fn accepted(s: Seq<u8>, uuid: Seq<u8>, journal_blocks: u32) -> bool {
    &&& s.len() == 1024
    &&& uuid_matches(s, uuid)
    &&& be32(s, 0) == 0xc03b3998
    &&& be32(s, 4) == 4
    &&& be32(s, 12) == 4096
    &&& be32(s, 16) == journal_blocks && journal_blocks >= 1024
    &&& be32(s, 20) == 1
    // MAX is a readable clean terminal sequence, not a writable generation.
    &&& 0 < be32(s, 24)
    &&& (be32(s, 28) == 0 || 1 <= be32(s, 28) < journal_blocks)
    &&& be32(s, 32) == 0
    &&& be32(s, 36) == 0
    &&& be32(s, 44) == 0
    &&& be32(s, 64) == 1
    &&& be32(s, 68) == 0
    &&& be32(s, 84) == 0
    &&& (be32(s, 40) == 0 || be32(s, 40) == 16 || be32(s, 40) == 17)
    &&& (if be32(s, 40) == 0 { s[80] == 0 }
        else { s[80] == 4 && be32(s, 252) == crc::fold(0xffffffff, crc::zero4(s, 252)) as nat })
}

pub fn parse(s: &[u8], uuid: &[u8], journal_blocks: u32) -> (r: Option<JournalInfo>)
    ensures match r {
        Some(j) => accepted(s@, uuid@, journal_blocks) && j.blocks == journal_blocks
            && j.sequence as nat == be32(s@, 24) && j.start as nat == be32(s@, 28)
            && j.csum_v3 == (be32(s@, 40) != 0) && j.revoke == (be32(s@, 40) == 17)
            && j.uuid_seed == crc::fold(0xffffffff, uuid@),
        None => !accepted(s@, uuid@, journal_blocks),
    },
{
    if s.len() != 1024 || !matching_uuid(s, uuid) { return None; }
    let blocks = read_be32(s, 16).unwrap();
    let sequence = read_be32(s, 24).unwrap();
    let start = read_be32(s, 28).unwrap();
    let features = read_be32(s, 40).unwrap();
    if read_be32(s, 0).unwrap() != 0xc03b3998 || read_be32(s, 4).unwrap() != 4
        || read_be32(s, 12).unwrap() != 4096 || blocks != journal_blocks || blocks < 1024
        || read_be32(s, 20).unwrap() != 1 || sequence == 0
        || (start != 0 && (start < 1 || start >= blocks))
        || read_be32(s, 32).unwrap() != 0 || read_be32(s, 36).unwrap() != 0
        || read_be32(s, 44).unwrap() != 0 || read_be32(s, 64).unwrap() != 1
        || read_be32(s, 68).unwrap() != 0 || read_be32(s, 84).unwrap() != 0
        || (features != 0 && features != 16 && features != 17)
    { return None; }
    if features == 0 {
        if s[80] != 0 { return None; }
    } else {
        if s[80] != 4 || read_be32(s, 252).unwrap() != crc::crc32c_zero4(0xffffffff, s, 252).unwrap()
        { return None; }
    }
    let uuid_seed = crc::crc32c(0xffffffff, uuid);
    Some(JournalInfo { blocks, sequence, start, csum_v3: features != 0,
        revoke: features == 17, uuid_seed })
}

}
