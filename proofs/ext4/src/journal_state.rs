// SPDX-License-Identifier: MPL-2.0

//! JBD2 superblock state images. Constructing these bytes does not authorize
//! issuing them: the recovery/commit protocol must order their persistence.

use vstd::prelude::*;
use crate::{bytes, crc, frozen::FrozenBlock, journal_superblock};

verus! {

pub open spec fn edited(index: int) -> bool {
    24 <= index < 32 || 40 <= index < 44 || index == 80 || 252 <= index < 256
}

pub open spec fn preserves(before: Seq<u8>, after: Seq<u8>) -> bool {
    &&& before.len() == 4096 && after.len() == 4096
    &&& (forall|i: int| 0 <= i < 4096 && !edited(i) ==> #[trigger] after[i] == before[i])
}

proof fn unchanged_word(before: Seq<u8>, after: Seq<u8>, offset: int)
    requires preserves(before, after), 0 <= offset, offset + 4 <= 4096,
        !edited(offset), !edited(offset + 1), !edited(offset + 2), !edited(offset + 3),
    ensures bytes::be32(before, offset) == bytes::be32(after, offset),
{
}

pub open spec fn input_ok(s: Seq<u8>, uuid: Seq<u8>, blocks: u32, sequence: u32, start: u32) -> bool {
    &&& s.len() == 4096
    &&& journal_superblock::accepted(s.subrange(0, 1024), uuid, blocks)
    &&& (bytes::be32(s, 28) == 0 || bytes::be32(s, 40) != 0)
    &&& sequence > 0 && (start == 0 || 1 <= start < blocks)
}

pub fn encode(s: &[u8], uuid: &[u8], blocks: u32, sequence: u32, start: u32) -> (r: Option<FrozenBlock>)
    ensures match r {
        Some(b) => input_ok(s@, uuid@, blocks, sequence, start) && preserves(s@, b.view())
            && journal_superblock::accepted(b.view().subrange(0, 1024), uuid@, blocks)
            && bytes::be32(b.view(), 24) == sequence as nat && bytes::be32(b.view(), 28) == start as nat
            && bytes::be32(b.view(), 40) == 17 && b.view()[80] == 4,
        None => !input_ok(s@, uuid@, blocks, sequence, start),
    },
{
    if s.len() != 4096 || sequence == 0 || (start != 0 && (start < 1 || start >= blocks)) { return None; }
    let info = match journal_superblock::parse(&s[..1024], uuid, blocks) {
        Some(info) => info, None => { return None; }
    };
    if info.start != 0 && !info.csum_v3 { return None; }
    let mut image = bytes::zero_block();
    bytes::write_bytes(image.as_mut_slice(), 0, s);
    bytes::write_be32(image.as_mut_slice(), 24, sequence);
    bytes::write_be32(image.as_mut_slice(), 28, start);
    bytes::write_be32(image.as_mut_slice(), 40, 17);
    let checksum_type = [4u8];
    bytes::write_bytes(image.as_mut_slice(), 80, &checksum_type);
    let checksum = crc::crc32c_zero4(0xffffffff, &image[..1024], 252).unwrap();
    let ghost before_checksum = image@;
    bytes::write_be32(image.as_mut_slice(), 252, checksum);
    proof {
        assert(preserves(s@, image@)) by {
            assert forall|i: int| 0 <= i < 4096 && !edited(i) implies #[trigger] image@[i] == s@[i] by { }
        }
        assert(crc::zero4(image@.subrange(0, 1024), 252)
            =~= crc::zero4(before_checksum.subrange(0, 1024), 252));
        unchanged_word(s@, image@, 0);
        unchanged_word(s@, image@, 4);
        unchanged_word(s@, image@, 12);
        unchanged_word(s@, image@, 16);
        unchanged_word(s@, image@, 20);
        unchanged_word(s@, image@, 32);
        unchanged_word(s@, image@, 36);
        unchanged_word(s@, image@, 44);
        unchanged_word(s@, image@, 64);
        unchanged_word(s@, image@, 68);
        unchanged_word(s@, image@, 84);
        assert forall|i: int| 0 <= i < 16 implies #[trigger] image@[48 + i] == uuid@[i] by {
            assert(s@.subrange(0, 1024)[48 + i] == uuid@[i]);
            assert(s@[48 + i] == uuid@[i]);
        }
        assert(bytes::be32(image@, 24) == sequence as nat);
        assert(bytes::be32(image@, 28) == start as nat);
        assert(bytes::be32(image@, 40) == 17);
        assert(journal_superblock::accepted(image@.subrange(0, 1024), uuid@, blocks));
    }
    FrozenBlock::from_vec(image)
}

pub proof fn recovery_tail_does_not_change_journal_geometry(before: Seq<u8>, after: Seq<u8>)
    requires preserves(before, after),
    ensures bytes::be32(before, 12) == bytes::be32(after, 12),
        bytes::be32(before, 16) == bytes::be32(after, 16),
        bytes::be32(before, 20) == bytes::be32(after, 20),
        before.subrange(48, 64) == after.subrange(48, 64),
{
    unchanged_word(before, after, 12);
    unchanged_word(before, after, 16);
    unchanged_word(before, after, 20);
    assert(before.subrange(48, 64) =~= after.subrange(48, 64));
}

}
