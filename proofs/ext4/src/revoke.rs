// SPDX-License-Identifier: MPL-2.0

//! JBD2 v3 revoke records with 32-bit targets. Linux recovery suppresses a write
//! when a revoke for that block is in the same or a later committed transaction.
//! Reference: pinned fs/jbd2/revoke.c and fs/jbd2/recovery.c in sources.json.

use vstd::prelude::*;
use crate::{bytes, crc, frozen::FrozenBlock, jbd2};

verus! {

pub struct Revokes { blocks: Vec<u32> }

pub open spec fn header(s: Seq<u8>, sequence: u32, seed: u32) -> bool {
    &&& s.len() == 4096
    &&& jbd2::header_ok(s, sequence) && bytes::be32(s, 4) == 5
    &&& 16 <= bytes::be32(s, 12) <= 4092 && bytes::be32(s, 12) % 4 == 0
    &&& bytes::be32(s, 4092) == crc::fold(seed, crc::zero4(s, 4092)) as nat
}

pub open spec fn count(s: Seq<u8>) -> nat { ((bytes::be32(s, 12) - 16) / 4) as nat }

pub open spec fn targets_bounded(s: Seq<u8>, n: nat, fs_blocks: u32) -> bool {
    forall|i: int| 0 <= i < n ==> #[trigger] bytes::be32(s, 16 + 4 * i) < fs_blocks
}

impl Revokes {
    pub closed spec fn view(&self) -> Seq<u32> { self.blocks@ }
    pub fn blocks(&self) -> (r: &[u32]) ensures r@ == self.view() { self.blocks.as_slice() }
}

pub fn parse(s: &[u8], sequence: u32, fs_blocks: u32, seed: u32) -> (r: Option<Revokes>)
    ensures match r {
        Some(v) => header(s@, sequence, seed) && targets_bounded(s@, count(s@), fs_blocks)
            && v.view().len() == count(s@)
            && (forall|i: int| 0 <= i < v.view().len()
                ==> (#[trigger] v.view()[i]) as nat == bytes::be32(s@, 16 + 4 * i)),
        None => !header(s@, sequence, seed) || !targets_bounded(s@, count(s@), fs_blocks),
    },
{
    if s.len() != 4096 { return None; }
    let h = match jbd2::parse_header(s, sequence) { Some(h) => h, None => { return None; } };
    let used = bytes::read_be32(s, 12).unwrap();
    if h.kind != 5 || used < 16 || used > 4092 || used % 4 != 0 { return None; }
    if bytes::read_be32(s, 4092).unwrap() != crc::crc32c_zero4(seed, s, 4092).unwrap() { return None; }
    let n = ((used - 16) / 4) as usize;
    let mut blocks = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant i <= n <= 1019, s.len() == 4096, header(s@, sequence, seed),
            n as nat == count(s@), blocks.len() == i,
            targets_bounded(s@, i as nat, fs_blocks),
            forall|j: int| 0 <= j < i ==> (#[trigger] blocks@[j]) as nat == bytes::be32(s@, 16 + 4 * j),
        decreases n - i,
    {
        let b = bytes::read_be32(s, 16 + 4 * i).unwrap();
        if b >= fs_blocks {
            proof {
                if targets_bounded(s@, count(s@), fs_blocks) {
                    assert(bytes::be32(s@, 16 + 4 * i as int) < fs_blocks);
                }
            }
            return None;
        }
        blocks.push(b);
        proof {
            assert forall|j: int| 0 <= j < i + 1 implies
                #[trigger] bytes::be32(s@, 16 + 4 * j) < fs_blocks by {
                if j < i { assert(bytes::be32(s@, 16 + 4 * j) < fs_blocks); }
            }
            assert forall|j: int| 0 <= j < i + 1 implies
                (#[trigger] blocks@[j]) as nat == bytes::be32(s@, 16 + 4 * j) by {
                if j < i { assert(blocks@[j] as nat == bytes::be32(s@, 16 + 4 * j)); }
            }
            assert(targets_bounded(s@, (i + 1) as nat, fs_blocks));
        }
        i += 1;
    }
    Some(Revokes { blocks })
}

pub open spec fn admissible(blocks: Seq<u32>, sequence: u32, fs_blocks: u32) -> bool {
    &&& blocks.len() <= 1019 && sequence > 0
    &&& (forall|i: int| 0 <= i < blocks.len() ==> #[trigger] blocks[i] < fs_blocks)
}

pub fn valid_input(blocks: &[u32], sequence: u32, fs_blocks: u32) -> (r: bool)
    ensures r == admissible(blocks@, sequence, fs_blocks),
{
    if blocks.len() > 1019 || sequence == 0 { return false; }
    let mut i = 0usize;
    while i < blocks.len()
        invariant i <= blocks.len() <= 1019, sequence > 0,
            forall|j: int| 0 <= j < i ==> #[trigger] blocks@[j] < fs_blocks,
        decreases blocks.len() - i,
    {
        if blocks[i] >= fs_blocks { return false; }
        proof {
            assert forall|j: int| 0 <= j < i + 1 implies #[trigger] blocks@[j] < fs_blocks by {
                if j < i { assert(blocks@[j] < fs_blocks); }
            }
        }
        i += 1;
    }
    true
}

pub fn encode(blocks: &[u32], sequence: u32, fs_blocks: u32, seed: u32) -> (r: Option<FrozenBlock>)
    ensures match r {
        Some(b) => admissible(blocks@, sequence, fs_blocks) && header(b.view(), sequence, seed)
            && count(b.view()) == blocks.len()
            && targets_bounded(b.view(), count(b.view()), fs_blocks)
            && (forall|i: int| 0 <= i < blocks.len()
                ==> #[trigger] bytes::be32(b.view(), 16 + 4 * i) == blocks@[i]),
        None => !admissible(blocks@, sequence, fs_blocks),
    },
{
    if !valid_input(blocks, sequence, fs_blocks) { return None; }
    let mut block = bytes::zero_block();
    let h = jbd2::encode_header(5, sequence).unwrap();
    bytes::write_bytes(block.as_mut_slice(), 0, &h);
    proof {
        assert(bytes::be32(block@, 0) == bytes::be32(h@, 0));
        assert(bytes::be32(block@, 4) == bytes::be32(h@, 4));
        assert(bytes::be32(block@, 8) == bytes::be32(h@, 8));
        assert(jbd2::header_ok(block@, sequence));
    }
    let ghost before_count = block@;
    bytes::write_be32(block.as_mut_slice(), 12, (16 + 4 * blocks.len()) as u32);
    proof {
        bytes::splice_word_frame(before_count, 12, bytes::encoded_be((16 + 4 * blocks.len()) as u32), 0);
        bytes::splice_word_frame(before_count, 12, bytes::encoded_be((16 + 4 * blocks.len()) as u32), 4);
        bytes::splice_word_frame(before_count, 12, bytes::encoded_be((16 + 4 * blocks.len()) as u32), 8);
        assert(jbd2::header_ok(block@, sequence));
    }
    let mut i = 0usize;
    while i < blocks.len()
        invariant i <= blocks.len() <= 1019, admissible(blocks@, sequence, fs_blocks),
            block.len() == 4096, jbd2::header_ok(block@, sequence), bytes::be32(block@, 4) == 5,
            bytes::be32(block@, 12) == 16 + 4 * blocks.len(),
            block@.subrange(4092, 4096) == seq![0u8, 0u8, 0u8, 0u8],
            forall|j: int| 0 <= j < i ==> #[trigger] bytes::be32(block@, 16 + 4 * j) == blocks@[j],
        decreases blocks.len() - i,
    {
        let ghost before = block@;
        let b = blocks[i];
        bytes::write_be32(block.as_mut_slice(), 16 + 4 * i, b);
        proof {
            bytes::splice_word_frame(before, 16 + 4 * i as int, bytes::encoded_be(b), 0);
            bytes::splice_word_frame(before, 16 + 4 * i as int, bytes::encoded_be(b), 4);
            bytes::splice_word_frame(before, 16 + 4 * i as int, bytes::encoded_be(b), 8);
            bytes::splice_word_frame(before, 16 + 4 * i as int, bytes::encoded_be(b), 12);
            assert(jbd2::header_ok(block@, sequence));
            assert(block@.subrange(4092, 4096) =~= before.subrange(4092, 4096));
            assert forall|j: int| 0 <= j < i + 1 implies
                #[trigger] bytes::be32(block@, 16 + 4 * j) == blocks@[j] by {
                if j < i { bytes::splice_word_frame(before, 16 + 4 * i as int, bytes::encoded_be(b), 16 + 4 * j); }
            }
        }
        i += 1;
    }
    let ghost before = block@;
    let checksum = crc::crc32c(seed, block.as_slice());
    bytes::write_be32(block.as_mut_slice(), 4092, checksum);
    proof {
        crc::zero4_restores_written_checksum(before, 4092, checksum);
        bytes::splice_word_frame(before, 4092, bytes::encoded_be(checksum), 0);
        bytes::splice_word_frame(before, 4092, bytes::encoded_be(checksum), 4);
        bytes::splice_word_frame(before, 4092, bytes::encoded_be(checksum), 8);
        bytes::splice_word_frame(before, 4092, bytes::encoded_be(checksum), 12);
        assert(jbd2::header_ok(block@, sequence));
        assert forall|j: int| 0 <= j < blocks.len() implies
            #[trigger] bytes::be32(block@, 16 + 4 * j) == blocks@[j] by {
            bytes::splice_word_frame(before, 4092, bytes::encoded_be(checksum), 16 + 4 * j);
        }
        assert forall|j: int| 0 <= j < blocks.len() implies
            #[trigger] bytes::be32(block@, 16 + 4 * j) < fs_blocks by {
            assert(blocks@[j] < fs_blocks);
        }
    }
    FrozenBlock::from_vec(block)
}

}
