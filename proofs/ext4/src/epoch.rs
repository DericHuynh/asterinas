// SPDX-License-Identifier: MPL-2.0

//! Conservative, nonwrapping epoch selection from a quiescent journal snapshot.
//! Header-shaped payload bytes can only prevent a writable admission. Checksums
//! are deliberately irrelevant to freshness; they are not authentication.

use vstd::prelude::*;
use crate::bytes;

verus! {

pub open spec fn header_id(journal: Seq<u8>, slot: int, id: u32) -> bool {
    let offset = slot * 4096;
    &&& 1 <= slot && (slot + 1) * 4096 <= journal.len()
    &&& bytes::be32(journal, offset) == 0xc03b3998
    &&& (bytes::be32(journal, offset + 4) == 1
        || bytes::be32(journal, offset + 4) == 2
        || bytes::be32(journal, offset + 4) == 5)
    &&& bytes::be32(journal, offset + 8) == id as nat
}

pub open spec fn newer(journal: Seq<u8>, minimum: u32, sequence: u32) -> bool {
    &&& minimum < sequence < 4294967295
    &&& (forall|slot: int, id: u32| #[trigger] header_id(journal, slot, id) ==> id < sequence)
}

pub open spec fn admissible(journal: Seq<u8>, minimum: u32) -> bool {
    &&& 1024 * 4096 <= journal.len() <= 32768 * 4096 && journal.len() % 4096 == 0
    &&& minimum < 4294967294
    &&& !(exists|slot: int, id: u32| #[trigger] header_id(journal, slot, id) && id >= 4294967294)
}

pub fn fresh_sequence(journal: &[u8], minimum: u32) -> (r: Option<u32>)
    ensures match r {
        Some(sequence) => admissible(journal@, minimum) && newer(journal@, minimum, sequence),
        None => !admissible(journal@, minimum),
    },
{
    if journal.len() < 1024 * 4096 || journal.len() > 32768 * 4096
        || journal.len() % 4096 != 0 || minimum >= 4294967294 { return None; }
    let blocks = journal.len() / 4096;
    let mut largest = minimum;
    let mut slot = 1usize;
    while slot < blocks
        invariant 1 <= slot <= blocks, blocks == journal.len() / 4096,
            journal.len() % 4096 == 0, 1024 <= blocks <= 32768,
            minimum <= largest < 4294967294,
            forall|j: int, id: u32| 1 <= j < slot && #[trigger] header_id(journal@, j, id) ==> id <= largest,
        decreases blocks - slot,
    {
        let offset = slot * 4096;
        let magic = bytes::read_be32(journal, offset).unwrap();
        let kind = bytes::read_be32(journal, offset + 4).unwrap();
        if magic == 0xc03b3998 && (kind == 1 || kind == 2 || kind == 5) {
            let id = bytes::read_be32(journal, offset + 8).unwrap();
            if id >= 4294967294 {
                proof {
                    assert(header_id(journal@, slot as int, id));
                    assert(exists|j: int, value: u32| #[trigger] header_id(journal@, j, value) && value >= 4294967294);
                }
                return None;
            }
            if id > largest { largest = id; }
        }
        proof {
            assert forall|j: int, id: u32| 1 <= j < slot + 1 && #[trigger] header_id(journal@, j, id)
                implies id <= largest by {
                if j == slot { assert(id as nat == bytes::be32(journal@, slot as int * 4096 + 8)); }
            }
        }
        slot += 1;
    }
    proof {
        assert forall|j: int, id: u32| #[trigger] header_id(journal@, j, id) implies id < largest + 1 by {
            assert(1 <= j < blocks);
        }
    }
    Some(largest + 1)
}

pub proof fn fresh_epoch_has_no_old_commit(journal: Seq<u8>, minimum: u32, sequence: u32, slot: int)
    requires newer(journal, minimum, sequence),
    ensures !header_id(journal, slot, sequence),
{
}

}
