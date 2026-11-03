// SPDX-License-Identifier: MPL-2.0

//! Linux JBD2 v3 primitives. CRC equality is only an integrity check; none of
//! these functions authorizes replay or proves a record's freshness.

use vstd::prelude::*;
use crate::bytes::{be32, read_be32, encode_be32};
use crate::crc;

verus! {

pub const MAGIC: u32 = 0xc03b3998;

pub struct Header { pub kind: u32, pub sequence: u32 }
pub struct Tag { pub block: u32, pub flags: u32, pub checksum: u32 }

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
    &&& 0 < be32(s, offset) < blocks
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
    if block == 0 || block >= blocks || high != 0
        || (flags != 0 && flags != 1 && flags != 2 && flags != 3
            && flags != 8 && flags != 9 && flags != 10 && flags != 11) { None }
    else { Some(Tag { block, flags, checksum }) }
}

pub fn encode_tag(t: &Tag, blocks: u32) -> (r: Option<[u8; 16]>)
    ensures match r {
        Some(s) => tag_ok(s@, 0, blocks) && be32(s@, 0) == t.block
            && be32(s@, 4) == t.flags && be32(s@, 12) == t.checksum,
        None => t.block == 0 || t.block >= blocks || !flags_ok(t.flags as nat),
    },
{
    if t.block == 0 || t.block >= blocks
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

pub fn valid_commit(s: &[u8], sequence: u32, uuid_seed: u32) -> (r: bool)
    ensures r == (s.len() == 4096 && header_ok(s@, sequence) && be32(s@, 4) == 2
        && be32(s@, 16) == crc::fold(uuid_seed, crc::zero4(s@, 16)) as nat),
{
    if s.len() != 4096 { return false; }
    let h = match parse_header(s, sequence) { Some(h) => h, None => { return false; } };
    if h.kind != 2 { return false; }
    read_be32(s, 16).unwrap() == crc::crc32c_zero4(uuid_seed, s, 16).unwrap()
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
