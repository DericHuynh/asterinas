// SPDX-License-Identifier: MPL-2.0

//! Linux JBD2 v3 primitives. CRC equality is only an integrity check; none of
//! these functions authorizes replay or proves a record's freshness.

use vstd::prelude::*;
use crate::bytes::*;
use crate::crc;
use crate::frozen::FrozenBlock;

verus! {

pub const MAGIC: u32 = 0xc03b3998;

pub struct Header { pub kind: u32, pub sequence: u32 }
pub struct Tag { pub block: u32, pub flags: u32, pub checksum: u32 }

pub open spec fn tag_bytes(t: Tag) -> Seq<u8> {
    crate::bytes::encoded_be(t.block) + crate::bytes::encoded_be(t.flags)
        + seq![0u8, 0u8, 0u8, 0u8] + crate::bytes::encoded_be(t.checksum)
}

pub open spec fn header_ok(s: Seq<u8>, sequence: u32) -> bool {
    &&& s.len() >= 12
    &&& be32(s, 0) == 0xc03b3998
    &&& (be32(s, 4) == 1 || be32(s, 4) == 2 || be32(s, 4) == 5)
    &&& 0 < sequence
    &&& be32(s, 8) == sequence
}

pub fn parse_header(s: &[u8], sequence: u32) -> (r: Option<Header>)
    ensures match r {
        Some(h) => header_ok(s@, sequence) && h.kind as nat == be32(s@, 4)
            && h.sequence == sequence,
        None => !header_ok(s@, sequence),
    },
{
    if s.len() < 12 || sequence == 0 { return None; }
    let magic = read_be32(s, 0).unwrap();
    let kind = read_be32(s, 4).unwrap();
    let seq = read_be32(s, 8).unwrap();
    if magic != MAGIC || (kind != 1 && kind != 2 && kind != 5) || seq != sequence { None }
    else { Some(Header { kind, sequence }) }
}

pub fn encode_header(kind: u32, sequence: u32) -> (r: Option<[u8; 12]>)
    ensures match r {
        Some(s) => header_ok(s@, sequence) && be32(s@, 4) == kind,
        None => sequence == 0 || (kind != 1 && kind != 2 && kind != 5),
    },
{
    if sequence == 0 || (kind != 1 && kind != 2 && kind != 5) { return None; }
    let m = encode_be32(MAGIC);
    let k = encode_be32(kind);
    let t = encode_be32(sequence);
    Some([m[0], m[1], m[2], m[3], k[0], k[1], k[2], k[3], t[0], t[1], t[2], t[3]])
}

pub open spec fn flags_ok(f: nat) -> bool {
    f == 0 || f == 1 || f == 2 || f == 3 || f == 8 || f == 9 || f == 10 || f == 11
}

pub open spec fn tag_ok(s: Seq<u8>, offset: int, blocks: u32) -> bool {
    &&& 0 <= offset && offset + 16 <= s.len()
    // Block zero contains the ext4 superblock in the 4 KiB profile. Whether a
    // decoded target may be written is decided by the validated replay plan.
    &&& be32(s, offset) < blocks
    &&& flags_ok(be32(s, offset + 4))
    &&& be32(s, offset + 8) == 0
}

pub fn parse_tag(s: &[u8], offset: usize, blocks: u32) -> (r: Option<Tag>)
    ensures match r {
        Some(t) => tag_ok(s@, offset as int, blocks)
            && t.block as nat == be32(s@, offset as int)
            && t.flags as nat == be32(s@, offset as int + 4)
            && t.checksum as nat == be32(s@, offset as int + 12),
        None => !tag_ok(s@, offset as int, blocks),
    },
{
    if offset > s.len() || s.len() - offset < 16 { return None; }
    let block = read_be32(s, offset).unwrap();
    let flags = read_be32(s, offset + 4).unwrap();
    let high = read_be32(s, offset + 8).unwrap();
    let checksum = read_be32(s, offset + 12).unwrap();
    if block >= blocks || high != 0
        || (flags != 0 && flags != 1 && flags != 2 && flags != 3
            && flags != 8 && flags != 9 && flags != 10 && flags != 11) { None }
    else { Some(Tag { block, flags, checksum }) }
}

pub fn encode_tag(t: &Tag, blocks: u32) -> (r: Option<[u8; 16]>)
    ensures match r {
        Some(s) => tag_ok(s@, 0, blocks) && be32(s@, 0) == t.block
            && be32(s@, 4) == t.flags && be32(s@, 12) == t.checksum && s@ == tag_bytes(*t),
        None => t.block >= blocks || !flags_ok(t.flags as nat),
    },
{
    if t.block >= blocks
        || (t.flags != 0 && t.flags != 1 && t.flags != 2 && t.flags != 3
            && t.flags != 8 && t.flags != 9 && t.flags != 10 && t.flags != 11) { return None; }
    let b = encode_be32(t.block);
    let f = encode_be32(t.flags);
    let c = encode_be32(t.checksum);
    Some([b[0], b[1], b[2], b[3], f[0], f[1], f[2], f[3], 0, 0, 0, 0, c[0], c[1], c[2], c[3]])
}

pub fn payload_checksum(uuid_seed: u32, sequence: u32, escaped: &[u8]) -> (r: Option<u32>)
    ensures match r {
        Some(c) => escaped.len() == 4096 && sequence > 0
            && c == crc::fold(crc::fold(uuid_seed,
                seq![(sequence / 16777216) as u8, ((sequence / 65536) % 256) as u8,
                    ((sequence / 256) % 256) as u8, (sequence % 256) as u8]), escaped@),
        None => escaped.len() != 4096 || sequence == 0,
    },
{
    if escaped.len() != 4096 || sequence == 0 { return None; }
    let seq = encode_be32(sequence);
    proof {
        assert(seq@ =~= seq![(sequence / 16777216) as u8,
            ((sequence / 65536) % 256) as u8, ((sequence / 256) % 256) as u8,
            (sequence % 256) as u8]);
    }
    let seed = crc::crc32c(uuid_seed, &seq);
    Some(crc::crc32c(seed, escaped))
}

pub open spec fn commit_ok(s: Seq<u8>, sequence: u32, uuid_seed: u32) -> bool {
    s.len() == 4096 && header_ok(s, sequence) && be32(s, 4) == 2
        && be32(s, 16) == crc::fold(uuid_seed, crc::zero4(s, 16)) as nat
}

pub fn valid_commit(s: &[u8], sequence: u32, uuid_seed: u32) -> (r: bool)
    ensures r == commit_ok(s@, sequence, uuid_seed),
{
    if s.len() != 4096 { return false; }
    let h = match parse_header(s, sequence) { Some(h) => h, None => { return false; } };
    if h.kind != 2 { return false; }
    read_be32(s, 16).unwrap() == crc::crc32c_zero4(uuid_seed, s, 16).unwrap()
}

pub fn encode_commit(sequence: u32, uuid_seed: u32) -> (r: Option<FrozenBlock>)
    ensures match r {
        Some(block) => sequence > 0 && commit_ok(block.view(), sequence, uuid_seed),
        None => sequence == 0,
    },
{
    if sequence == 0 { return None; }
    let mut block = crate::bytes::zero_block();
    let header = encode_header(2, sequence).unwrap();
    crate::bytes::write_bytes(block.as_mut_slice(), 0, &header);
    proof {
        assert(be32(block@, 0) == be32(header@, 0));
        assert(be32(block@, 4) == be32(header@, 4));
        assert(be32(block@, 8) == be32(header@, 8));
        assert(header_ok(block@, sequence));
        assert(block@.subrange(16, 20) =~= seq![0u8, 0u8, 0u8, 0u8]);
    }
    let ghost before = block@;
    let checksum = crc::crc32c(uuid_seed, block.as_slice());
    crate::bytes::write_be32(block.as_mut_slice(), 16, checksum);
    proof {
        crc::zero4_restores_written_checksum(before, 16, checksum);
        crate::bytes::splice_word_frame(before, 16, crate::bytes::encoded_be(checksum), 0);
        crate::bytes::splice_word_frame(before, 16, crate::bytes::encoded_be(checksum), 4);
        crate::bytes::splice_word_frame(before, 16, crate::bytes::encoded_be(checksum), 8);
        assert(header_ok(block@, sequence));
    }
    FrozenBlock::from_vec(block)
}

/// Checked counter arithmetic, including the terminal next-tail value MAX.
/// This is not permission to begin a transaction with that value: the system
/// model reserves room for retirement and stops before that transaction.
/// Reuse across remount still needs a byte-level generation/window proof.
pub fn next_sequence(sequence: u32) -> (r: Option<u32>)
    ensures match r {
        Some(next) => 0 < sequence < 4294967295 && next as int == sequence as int + 1,
        None => sequence == 0 || sequence == 4294967295,
    },
{
    if sequence == 0 || sequence == 4294967295 { None } else { Some(sequence + 1) }
}

}
