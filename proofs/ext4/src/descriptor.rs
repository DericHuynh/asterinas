// SPDX-License-Identifier: MPL-2.0

//! Bounded JBD2 v3 descriptor decoding. The first tag carries the filesystem
//! UUID and subsequent tags use SAME_UUID, as in Linux's single-user writer.
//! Reference: pinned fs/jbd2/commit.c and fs/jbd2/recovery.c in sources.json.

use vstd::prelude::*;
use crate::{bytes, crc, frozen::FrozenBlock, jbd2};

verus! {

pub struct Descriptor { tags: Vec<jbd2::Tag> }

pub open spec fn offset(index: int) -> int { if index == 0 { 12 } else { 28 + 16 * index } }

pub open spec fn entry_ok(s: Seq<u8>, index: int, blocks: u32) -> bool {
    &&& 0 <= index < 250
    &&& jbd2::tag_ok(s, offset(index), blocks)
    &&& (if index == 0 {
        let f = bytes::be32(s, offset(index) + 4);
        f == 0 || f == 1 || f == 8 || f == 9
    } else {
        let f = bytes::be32(s, offset(index) + 4);
        f == 2 || f == 3 || f == 10 || f == 11
    })
}

pub open spec fn last(s: Seq<u8>, index: int) -> bool { bytes::be32(s, offset(index) + 4) >= 8 }

pub open spec fn prefix(s: Seq<u8>, count: nat, blocks: u32) -> bool {
    forall|i: int| 0 <= i < count ==> #[trigger] entry_ok(s, i, blocks) && !last(s, i)
}

pub open spec fn header_uuid(s: Seq<u8>, uuid: Seq<u8>, sequence: u32) -> bool {
    &&& s.len() == 4096 && uuid.len() == 16
    &&& jbd2::header_ok(s, sequence) && bytes::be32(s, 4) == 1
    &&& s.subrange(28, 44) == uuid
}

pub open spec fn base(s: Seq<u8>, uuid: Seq<u8>, sequence: u32, seed: u32) -> bool {
    &&& header_uuid(s, uuid, sequence)
    &&& bytes::be32(s, 4092) == crc::fold(seed, crc::zero4(s, 4092)) as nat
}

pub open spec fn input_tag(t: jbd2::Tag, index: int, count: nat, blocks: u32) -> bool {
    &&& t.block < blocks
    &&& (if index == 0 { t.flags == 0 || t.flags == 1 || t.flags == 8 || t.flags == 9 }
         else { t.flags == 2 || t.flags == 3 || t.flags == 10 || t.flags == 11 })
    &&& (t.flags >= 8) == (index + 1 == count)
}

pub open spec fn admissible(tags: Seq<jbd2::Tag>, uuid: Seq<u8>, sequence: u32, blocks: u32) -> bool {
    &&& 0 < tags.len() <= 250 && uuid.len() == 16 && sequence > 0
    &&& (forall|i: int| 0 <= i < tags.len() ==> #[trigger] input_tag(tags[i], i, tags.len(), blocks))
}

pub open spec fn candidate(s: Seq<u8>, count: nat, blocks: u32) -> bool {
    &&& 0 < count <= 250
    &&& prefix(s, (count - 1) as nat, blocks)
    &&& entry_ok(s, count as int - 1, blocks)
    &&& last(s, count as int - 1)
}

pub open spec fn represents(s: Seq<u8>, tags: Seq<jbd2::Tag>) -> bool {
    forall|i: int| 0 <= i < tags.len() ==>
        (#[trigger] tags[i]).block as nat == bytes::be32(s, offset(i))
        && tags[i].flags as nat == bytes::be32(s, offset(i) + 4)
        && tags[i].checksum as nat == bytes::be32(s, offset(i) + 12)
}

impl Descriptor {
    pub closed spec fn view(&self) -> Seq<jbd2::Tag> { self.tags@ }
    pub fn tags(&self) -> (r: &[jbd2::Tag]) ensures r@ == self.view() { self.tags.as_slice() }
}

pub proof fn prefix_is_shorter_than_any_candidate(s: Seq<u8>, done: nat, count: nat, blocks: u32)
    requires prefix(s, done, blocks), candidate(s, count, blocks),
    ensures done < count,
{
    if count <= done {
        assert(entry_ok(s, count as int - 1, blocks) && !last(s, count as int - 1));
    }
}

pub proof fn bad_next_entry_excludes_all_candidates(s: Seq<u8>, done: nat, blocks: u32)
    requires prefix(s, done, blocks), !entry_ok(s, done as int, blocks),
    ensures !exists|n: nat| candidate(s, n, blocks),
{
    if exists|n: nat| candidate(s, n, blocks) {
        let n = choose|n: nat| candidate(s, n, blocks);
        prefix_is_shorter_than_any_candidate(s, done, n, blocks);
        if done + 1 < n { assert(entry_ok(s, done as int, blocks)); }
        else { assert(done == n - 1); }
    }
}

pub fn parse(s: &[u8], uuid: &[u8], sequence: u32, blocks: u32, seed: u32) -> (r: Option<Descriptor>)
    ensures match r {
        Some(d) => base(s@, uuid@, sequence, seed) && candidate(s@, d.view().len(), blocks)
            && represents(s@, d.view()),
        None => !base(s@, uuid@, sequence, seed) || !(exists|n: nat| candidate(s@, n, blocks)),
    },
{
    if s.len() != 4096 || uuid.len() != 16 { return None; }
    let h = match jbd2::parse_header(s, sequence) { Some(h) => h, None => { return None; } };
    if h.kind != 1 { return None; }
    if !bytes::equal(&s[28..44], uuid) { return None; }
    if bytes::read_be32(s, 4092).unwrap() != crc::crc32c_zero4(seed, s, 4092).unwrap() { return None; }
    let mut tags = Vec::new();
    let mut i = 0usize;
    while i < 250
        invariant i <= 250, tags.len() == i,
            base(s@, uuid@, sequence, seed), s.len() == 4096,
            prefix(s@, i as nat, blocks), represents(s@, tags@),
        decreases 250 - i,
    {
        let position = if i == 0 { 12 } else { 28 + 16 * i };
        let tag = match jbd2::parse_tag(s, position, blocks) {
            Some(tag) => tag,
            None => {
                proof { bad_next_entry_excludes_all_candidates(s@, i as nat, blocks); }
                return None;
            }
        };
        let f = tag.flags;
        if (i == 0 && f != 0 && f != 1 && f != 8 && f != 9)
            || (i != 0 && f != 2 && f != 3 && f != 10 && f != 11) {
            proof { bad_next_entry_excludes_all_candidates(s@, i as nat, blocks); }
            return None;
        }
        tags.push(tag);
        proof {
            assert forall|j: int| 0 <= j < tags.len() implies
                (#[trigger] tags@[j]).block as nat == bytes::be32(s@, offset(j))
                && tags@[j].flags as nat == bytes::be32(s@, offset(j) + 4)
                && tags@[j].checksum as nat == bytes::be32(s@, offset(j) + 12) by {
                if j < i { assert(represents(s@, tags@.subrange(0, i as int))); }
            }
        }
        if f >= 8 { return Some(Descriptor { tags }); }
        proof {
            assert forall|j: int| 0 <= j < i + 1 implies
                #[trigger] entry_ok(s@, j, blocks) && !last(s@, j) by {
                if j < i { assert(entry_ok(s@, j, blocks) && !last(s@, j)); }
            }
            assert(prefix(s@, (i + 1) as nat, blocks));
        }
        i += 1;
    }
    proof {
        if exists|n: nat| candidate(s@, n, blocks) {
            let n = choose|n: nat| candidate(s@, n, blocks);
            prefix_is_shorter_than_any_candidate(s@, i as nat, n, blocks);
        }
    }
    None
}

pub proof fn descriptor_length_is_unique(s: Seq<u8>, a: nat, b: nat, blocks: u32)
    requires candidate(s, a, blocks), candidate(s, b, blocks),
    ensures a == b,
{
    if a < b { prefix_is_shorter_than_any_candidate(s, (b - 1) as nat, a, blocks); }
    if b < a { prefix_is_shorter_than_any_candidate(s, (a - 1) as nat, b, blocks); }
}

pub fn valid_input(tags: &[jbd2::Tag], uuid: &[u8], sequence: u32, blocks: u32) -> (r: bool)
    ensures r == admissible(tags@, uuid@, sequence, blocks),
{
    if tags.len() == 0 || tags.len() > 250 || uuid.len() != 16 || sequence == 0 { return false; }
    let mut i = 0usize;
    while i < tags.len()
        invariant i <= tags.len(), 0 < tags.len() <= 250, uuid.len() == 16, sequence > 0,
            forall|j: int| 0 <= j < i ==> #[trigger] input_tag(tags@[j], j, tags.len() as nat, blocks),
        decreases tags.len() - i,
    {
        let t = &tags[i];
        let f = t.flags;
        if t.block >= blocks || (i == 0 && f != 0 && f != 1 && f != 8 && f != 9)
            || (i != 0 && f != 2 && f != 3 && f != 10 && f != 11)
            || (f >= 8) != (i + 1 == tags.len()) {
            proof {
                if admissible(tags@, uuid@, sequence, blocks) {
                    assert(input_tag(tags@[i as int], i as int, tags.len() as nat, blocks));
                }
            }
            return false;
        }
        proof {
            assert forall|j: int| 0 <= j < i + 1 implies
                #[trigger] input_tag(tags@[j], j, tags.len() as nat, blocks) by {
                if j < i { assert(input_tag(tags@[j], j, tags.len() as nat, blocks)); }
            }
        }
        i += 1;
    }
    true
}

proof fn framing(s: Seq<u8>, uuid: Seq<u8>, sequence: u32, position: int, data: Seq<u8>)
    requires header_uuid(s, uuid, sequence), 12 <= position, position + data.len() <= 4096,
        position + data.len() <= 28 || position >= 44,
    ensures header_uuid(bytes::splice(s, position, data), uuid, sequence),
        position + data.len() <= 4092 ==>
            bytes::splice(s, position, data).subrange(4092, 4096) == s.subrange(4092, 4096),
{
    bytes::splice_word_frame(s, position, data, 0);
    bytes::splice_word_frame(s, position, data, 4);
    bytes::splice_word_frame(s, position, data, 8);
    assert(bytes::splice(s, position, data).subrange(28, 44) =~= uuid);
    if position + data.len() <= 4092 {
        assert(bytes::splice(s, position, data).subrange(4092, 4096) =~= s.subrange(4092, 4096));
    }
}

proof fn record_frame(s: Seq<u8>, position: int, data: Seq<u8>, index: int)
    requires s.len() == 4096, 0 <= position, position + data.len() <= 4096,
        0 <= index < 250, offset(index) + 16 <= position || offset(index) >= position + data.len(),
    ensures bytes::be32(bytes::splice(s, position, data), offset(index)) == bytes::be32(s, offset(index)),
        bytes::be32(bytes::splice(s, position, data), offset(index) + 4) == bytes::be32(s, offset(index) + 4),
        bytes::be32(bytes::splice(s, position, data), offset(index) + 8) == bytes::be32(s, offset(index) + 8),
        bytes::be32(bytes::splice(s, position, data), offset(index) + 12) == bytes::be32(s, offset(index) + 12),
{
    bytes::splice_word_frame(s, position, data, offset(index));
    bytes::splice_word_frame(s, position, data, offset(index) + 4);
    bytes::splice_word_frame(s, position, data, offset(index) + 8);
    bytes::splice_word_frame(s, position, data, offset(index) + 12);
}

fn initial_block(uuid: &[u8], sequence: u32) -> (r: Vec<u8>)
    requires uuid.len() == 16, sequence > 0,
    ensures header_uuid(r@, uuid@, sequence),
        r@.subrange(4092, 4096) == seq![0u8, 0u8, 0u8, 0u8],
{
    let mut block = bytes::zero_block();
    let h = jbd2::encode_header(1, sequence).unwrap();
    bytes::write_bytes(block.as_mut_slice(), 0, &h);
    proof {
        assert(bytes::be32(block@, 0) == bytes::be32(h@, 0));
        assert(bytes::be32(block@, 4) == bytes::be32(h@, 4));
        assert(bytes::be32(block@, 8) == bytes::be32(h@, 8));
        assert(jbd2::header_ok(block@, sequence));
        assert(bytes::be32(block@, 4) == 1);
    }
    let ghost before = block@;
    bytes::write_bytes(block.as_mut_slice(), 28, uuid);
    proof {
        bytes::splice_word_frame(before, 28, uuid@, 0);
        bytes::splice_word_frame(before, 28, uuid@, 4);
        bytes::splice_word_frame(before, 28, uuid@, 8);
        assert(block@.subrange(28, 44) =~= uuid@);
        assert(jbd2::header_ok(block@, sequence));
    }
    block
}

pub fn encode(tags: &[jbd2::Tag], uuid: &[u8], sequence: u32, blocks: u32, seed: u32) -> (r: Option<FrozenBlock>)
    ensures match r {
        Some(b) => admissible(tags@, uuid@, sequence, blocks) && base(b.view(), uuid@, sequence, seed)
            && candidate(b.view(), tags.len() as nat, blocks) && represents(b.view(), tags@),
        None => !admissible(tags@, uuid@, sequence, blocks),
    },
{
    if !valid_input(tags, uuid, sequence, blocks) { return None; }
    let mut block = initial_block(uuid, sequence);
    let mut i = 0usize;
    while i < tags.len()
        invariant i <= tags.len() <= 250, admissible(tags@, uuid@, sequence, blocks),
            header_uuid(block@, uuid@, sequence),
            block@.subrange(4092, 4096) == seq![0u8, 0u8, 0u8, 0u8],
            forall|j: int| 0 <= j < i ==>
                (#[trigger] tags@[j]).block as nat == bytes::be32(block@, offset(j))
                && tags@[j].flags as nat == bytes::be32(block@, offset(j) + 4)
                && bytes::be32(block@, offset(j) + 8) == 0
                && tags@[j].checksum as nat == bytes::be32(block@, offset(j) + 12),
        decreases tags.len() - i,
    {
        let t = &tags[i];
        proof { assert(input_tag(tags@[i as int], i as int, tags.len() as nat, blocks)); }
        let encoded = jbd2::encode_tag(t, blocks).unwrap();
        let position = if i == 0 { 12 } else { 28 + 16 * i };
        let ghost before = block@;
        bytes::write_bytes(block.as_mut_slice(), position, &encoded);
        proof {
            framing(before, uuid@, sequence, position as int, encoded@);
            assert forall|j: int| 0 <= j < i + 1 implies
                (#[trigger] tags@[j]).block as nat == bytes::be32(block@, offset(j))
                && tags@[j].flags as nat == bytes::be32(block@, offset(j) + 4)
                && bytes::be32(block@, offset(j) + 8) == 0
                && tags@[j].checksum as nat == bytes::be32(block@, offset(j) + 12) by {
                if j < i {
                    record_frame(before, position as int, encoded@, j);
                    assert(tags@[j].block as nat == bytes::be32(before, offset(j)));
                }
            }
        }
        i += 1;
    }
    let ghost before = block@;
    let c = crc::crc32c(seed, block.as_slice());
    bytes::write_be32(block.as_mut_slice(), 4092, c);
    proof {
        framing(before, uuid@, sequence, 4092, bytes::encoded_be(c));
        assert(crc::zero4(block@, 4092) =~= before);
        assert forall|j: int| 0 <= j < tags.len() implies
            (#[trigger] tags@[j]).block as nat == bytes::be32(block@, offset(j))
            && tags@[j].flags as nat == bytes::be32(block@, offset(j) + 4)
            && bytes::be32(block@, offset(j) + 8) == 0
            && tags@[j].checksum as nat == bytes::be32(block@, offset(j) + 12) by {
            record_frame(before, 4092, bytes::encoded_be(c), j);
        }
        assert(represents(block@, tags@));
        assert forall|j: int| 0 <= j < tags.len() - 1 implies
            #[trigger] entry_ok(block@, j, blocks) && !last(block@, j) by {
            assert(input_tag(tags@[j], j, tags.len() as nat, blocks));
        }
        assert(input_tag(tags@[tags.len() as int - 1], tags.len() as int - 1, tags.len() as nat, blocks));
    }
    FrozenBlock::from_vec(block)
}

pub proof fn descriptor_representation_is_unique(s: Seq<u8>, a: Seq<jbd2::Tag>, b: Seq<jbd2::Tag>, blocks: u32)
    requires candidate(s, a.len(), blocks), candidate(s, b.len(), blocks), represents(s, a), represents(s, b),
    ensures a == b,
{
    descriptor_length_is_unique(s, a.len(), b.len(), blocks);
    assert(a =~= b);
}

}
