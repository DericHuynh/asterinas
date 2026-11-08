// SPDX-License-Identifier: MPL-2.0

//! Variable JBD2 tags, descriptor/revoke blocks and payload checksum domains.
//! Parsed addresses describe bytes only; role, epoch and replay policy are
//! supplied by a separately admitted filesystem transaction.

use vstd::prelude::*;
use crate::{bytes, crc, jbd2_features::{self as features, Checksum, Features}};

verus! {

pub const ESCAPE: u32 = 1;
pub const SAME_UUID: u32 = 2;
pub const DELETED: u32 = 4;
pub const LAST_TAG: u32 = 8;
pub const MAX_TAGS: usize = 8192;
pub const MAX_REVOKES: usize = 16384;

#[derive(Clone, Copy)]
pub struct Tag { pub block: u64, pub flags: u32, pub checksum: u32 }
pub struct ParsedTag { pub tag: Tag, pub next: usize }

pub open spec fn be16_word(raw: Seq<u8>, offset: int) -> nat {
    256 * raw[offset] as nat + raw[offset + 1] as nat
}
pub open spec fn be16_image(value: u16) -> Seq<u8> {
    seq![(value / 256) as u8, (value % 256) as u8]
}
pub open spec fn tag_flags(raw: Seq<u8>, offset: int, f: features::FeatureView) -> u32 {
    if f.checksum is V3 { bytes::be32(raw, offset + 4) as u32 }
    else { be16_word(raw, offset + 6) as u32 }
}
pub open spec fn tag_checksum(raw: Seq<u8>, offset: int, f: features::FeatureView) -> u32 {
    if f.checksum is V3 { bytes::be32(raw, offset + 12) as u32 }
    else if f.checksum is V2 { be16_word(raw, offset + 4) as u32 } else { 0u32 }
}
pub open spec fn tag_high(raw: Seq<u8>, offset: int, f: features::FeatureView) -> u32 {
    if f.checksum is V3 || features::wide(f) { bytes::be32(raw, offset + 8) as u32 } else { 0u32 }
}
pub open spec fn tag_address(raw: Seq<u8>, offset: int, f: features::FeatureView) -> u64 {
    ((tag_high(raw, offset, f) as u64) << 32) | (bytes::be32(raw, offset) as u32) as u64
}
pub open spec fn tag_admitted(raw: Seq<u8>, offset: int, f: features::FeatureView, blocks: u64) -> bool {
    &&& 0 <= offset && offset + features::tag_width(f) <= raw.len()
    &&& tag_flags(raw, offset, f) & !15u32 == 0
    &&& (features::wide(f) || tag_high(raw, offset, f) == 0)
    &&& tag_address(raw, offset, f) < blocks
}
pub open spec fn tag_matches(tag: Tag, raw: Seq<u8>, offset: int, f: features::FeatureView) -> bool {
    tag.block == tag_address(raw, offset, f)
        && tag.flags == tag_flags(raw, offset, f) && tag.checksum == tag_checksum(raw, offset, f)
}
pub open spec fn tag_encodable(tag: Tag, f: features::FeatureView, blocks: u64) -> bool {
    &&& tag.block < blocks && tag.flags & !15u32 == 0
    &&& (features::wide(f) || tag.block <= 0xffff_ffffu64)
    &&& (f.checksum is V2 ==> tag.checksum <= 65535)
}
pub open spec fn same_tag(a: Tag, b: Tag) -> bool {
    a.block == b.block && a.flags == b.flags && a.checksum == b.checksum
}
pub open spec fn encoded_tag_matches(raw: Seq<u8>, tag: Tag, f: features::FeatureView) -> bool {
    &&& raw.len() == features::tag_width(f)
    &&& tag_address(raw, 0, f) == tag.block && tag_flags(raw, 0, f) == tag.flags
    &&& tag_checksum(raw, 0, f) == if f.checksum is V2 || f.checksum is V3 { tag.checksum } else { 0u32 }
    // Linux's extra V2 trailing bytes are canonical zero padding.
    &&& (f.checksum is V2 ==> raw[raw.len() as int - 2] == 0 && raw[raw.len() as int - 1] == 0)
}

fn be16(raw: &[u8], offset: usize) -> (r: Option<u16>)
    ensures match r {
        Some(v) => offset as int + 2 <= raw.len() && v as nat == be16_word(raw@, offset as int),
        None => offset as int + 2 > raw.len(),
    },
{
    if offset > raw.len() || raw.len() - offset < 2 { return None; }
    Some(256 * (raw[offset] as u16) + raw[offset + 1] as u16)
}
proof fn local_writer_frames_reads(before: Seq<u8>, offset: int, data: Seq<u8>)
    requires 0 <= offset, offset + data.len() <= before.len(),
    ensures
        forall|i: int| 0 <= i < before.len() && !(offset <= i < offset + data.len()) ==>
            #[trigger] bytes::splice(before, offset, data)[i] == before[i],
        forall|word: int| 0 <= word && word + 2 <= before.len()
            && (word + 2 <= offset || word >= offset + data.len()) ==>
                #[trigger] be16_word(bytes::splice(before, offset, data), word) == be16_word(before, word),
        forall|word: int| 0 <= word && word + 4 <= before.len()
            && (word + 4 <= offset || word >= offset + data.len()) ==>
                #[trigger] bytes::be32(bytes::splice(before, offset, data), word) == bytes::be32(before, word),
{
    assert forall|i: int| 0 <= i < before.len() && !(offset <= i < offset + data.len())
        implies #[trigger] bytes::splice(before, offset, data)[i] == before[i] by {
        bytes::splice_frame(before, offset, data, i);
    }
}

fn put32(raw: &mut [u8], offset: usize, value: u32) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r == (offset as int + 4 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, offset as int, bytes::encoded_be(value)) } else { old(raw)@ },
        r ==> bytes::be32(final(raw)@, offset as int) == value as nat,
        forall|i: int| 0 <= i < old(raw).len() && !(offset <= i < offset as int + 4)
            ==> #[trigger] final(raw)@[i] == old(raw)@[i],
        forall|word: int| 0 <= word && word + 2 <= old(raw).len()
            && (word + 2 <= offset || word >= offset as int + 4) ==>
                #[trigger] be16_word(final(raw)@, word) == be16_word(old(raw)@, word),
        forall|word: int| 0 <= word && word + 4 <= old(raw).len()
            && (word + 4 <= offset || word >= offset as int + 4) ==>
                #[trigger] bytes::be32(final(raw)@, word) == bytes::be32(old(raw)@, word),
{
    let ghost before = raw@;
    let success = bytes::write_be32(raw, offset, value);
    proof { if success { local_writer_frames_reads(before, offset as int, bytes::encoded_be(value)); } }
    success
}

fn put16(raw: &mut [u8], offset: usize, value: u16) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r == (offset as int + 2 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, offset as int, be16_image(value)) } else { old(raw)@ },
        r ==> be16_word(final(raw)@, offset as int) == value as nat,
        forall|i: int| 0 <= i < old(raw).len() && !(offset <= i < offset as int + 2)
            ==> #[trigger] final(raw)@[i] == old(raw)@[i],
        forall|word: int| 0 <= word && word + 2 <= old(raw).len()
            && (word + 2 <= offset || word >= offset as int + 2) ==>
                #[trigger] be16_word(final(raw)@, word) == be16_word(old(raw)@, word),
        forall|word: int| 0 <= word && word + 4 <= old(raw).len()
            && (word + 4 <= offset || word >= offset as int + 2) ==>
                #[trigger] bytes::be32(final(raw)@, word) == bytes::be32(old(raw)@, word),
{
    let encoded = [(value / 256) as u8, (value % 256) as u8];
    proof { vstd::arithmetic::div_mod::lemma_fundamental_div_mod(value as int, 256); }
    let ghost before = raw@;
    let success = bytes::write_bytes(raw, offset, &encoded);
    proof { if success { local_writer_frames_reads(before, offset as int, encoded@); } }
    success
}

fn zeroes(length: usize) -> (r: Option<Vec<u8>>)
    ensures match r {
        Some(raw) => length <= 65536 && raw@ == Seq::<u8>::new(length as nat, |i: int| 0u8),
        None => length > 65536,
    },
{
    if length > 65536 { return None; }
    let mut raw = Vec::<u8>::new(); let mut i = 0usize;
    while i < length
        invariant i <= length <= 65536, raw.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] raw@[j] == 0,
        decreases length - i,
    { raw.push(0); i += 1; }
    assert(raw@ =~= Seq::<u8>::new(length as nat, |j: int| 0u8));
    Some(raw)
}

proof fn address_halves_rejoin(block: u64)
    ensures (((block >> 32) as u32 as u64) << 32) | (block as u32 as u64) == block,
        block <= 0xffff_ffffu64 ==> (block >> 32) == 0,
        (block >> 32) <= 0xffff_ffffu64,
{
    assert((((block >> 32) as u32 as u64) << 32) | (block as u32 as u64) == block) by (bit_vector);
    assert(block <= 0xffff_ffffu64 ==> (block >> 32) == 0) by (bit_vector);
    assert((block >> 32) <= 0xffff_ffffu64) by (bit_vector);
}
proof fn flags_fit_the_legacy_field(flags: u32)
    requires flags & !15u32 == 0,
    ensures flags <= 15, flags as u16 as u32 == flags,
{
    assert(flags <= 15 && flags as u16 as u32 == flags) by (bit_vector)
        requires flags & !15u32 == 0;
}
proof fn equal_prefix_preserves_byte(before: Seq<u8>, after: Seq<u8>, prefix: int, index: int)
    requires 0 <= index < prefix <= before.len(), prefix <= after.len(),
        before.take(prefix) == after.take(prefix),
    ensures before[index] == after[index],
{
    assert(before.take(prefix)[index] == before[index]);
    assert(after.take(prefix)[index] == after[index]);
    assert(before.take(prefix)[index] == after.take(prefix)[index]);
}
proof fn equal_prefix_preserves_subrange(before: Seq<u8>, after: Seq<u8>, prefix: int, first: int, end: int)
    requires 0 <= first <= end <= prefix <= before.len(), prefix <= after.len(),
        before.take(prefix) == after.take(prefix),
    ensures before.subrange(first, end) == after.subrange(first, end),
{
    assert forall|i: int| 0 <= i < end - first implies
        #[trigger] before.subrange(first, end)[i] == after.subrange(first, end)[i] by {
        equal_prefix_preserves_byte(before, after, prefix, first + i);
    }
    assert(before.subrange(first, end) =~= after.subrange(first, end));
}
proof fn equal_prefix_preserves_be32(before: Seq<u8>, after: Seq<u8>, prefix: int, word: int)
    requires 0 <= word, word + 4 <= prefix <= before.len(), prefix <= after.len(),
        before.take(prefix) == after.take(prefix),
    ensures bytes::be32(before, word) == bytes::be32(after, word),
{
    equal_prefix_preserves_byte(before, after, prefix, word);
    equal_prefix_preserves_byte(before, after, prefix, word + 1);
    equal_prefix_preserves_byte(before, after, prefix, word + 2);
    equal_prefix_preserves_byte(before, after, prefix, word + 3);
}

proof fn captured_prefix_is_unchanged(before: Seq<u8>, after: Seq<u8>, offset: int, data: Seq<u8>, prefix: int)
    requires 0 <= prefix <= offset, offset + data.len() <= before.len(),
        after == bytes::splice(before, offset, data),
    ensures after.take(prefix) == before.take(prefix),
{
    assert(after.take(prefix) =~= before.take(prefix));
}
fn copy_span(raw: &mut [u8], offset: usize, data: &[u8]) -> (r: bool)
    ensures final(raw).len() == old(raw).len(), r == (offset as int + data.len() <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, offset as int, data@) } else { old(raw)@ },
        r ==> final(raw)@.subrange(offset as int, offset as int + data.len()) == data@,
        forall|i: int| 0 <= i < old(raw).len() && !(offset <= i < offset as int + data.len())
            ==> #[trigger] final(raw)@[i] == old(raw)@[i],
{
    let ghost before = raw@;
    let success = bytes::write_bytes(raw, offset, data);
    proof {
        if success {
            local_writer_frames_reads(before, offset as int, data@);
            assert(raw@.subrange(offset as int, offset as int + data.len()) =~= data@);
        }
    }
    success
}

/// V2 has a two-byte unused trailer after its conditional high address word;
/// its sizes are 10/14, not the older 8/12 or V3's fixed 16 bytes.
pub fn parse_tag(raw: &[u8], offset: usize, f: Features, filesystem_blocks: u64)
    -> (r: Option<ParsedTag>)
    ensures f.wf(), match r {
        Some(parsed) => tag_admitted(raw@, offset as int, f.view(), filesystem_blocks)
            && tag_matches(parsed.tag, raw@, offset as int, f.view())
            && parsed.next as int == offset as int + features::tag_width(f.view())
            && offset < parsed.next <= raw.len(),
        None => !tag_admitted(raw@, offset as int, f.view(), filesystem_blocks),
    },
{
    let _ = f.version();
    let width = f.tag_bytes();
    if offset > raw.len() || raw.len() - offset < width { return None; }
    let low = bytes::read_be32(raw, offset).unwrap();
    let (flags, checksum, high) = match f.checksum() {
        Checksum::V3 => (
            bytes::read_be32(raw, offset + 4).unwrap(),
            bytes::read_be32(raw, offset + 12).unwrap(),
            bytes::read_be32(raw, offset + 8).unwrap(),
        ),
        Checksum::V2 => (
            be16(raw, offset + 6).unwrap() as u32,
            be16(raw, offset + 4).unwrap() as u32,
            if f.wide_tags() { bytes::read_be32(raw, offset + 8).unwrap() } else { 0 },
        ),
        _ => (
            be16(raw, offset + 6).unwrap() as u32, 0u32,
            if f.wide_tags() { bytes::read_be32(raw, offset + 8).unwrap() } else { 0 },
        ),
    };
    if flags & !15u32 != 0 || (!f.wide_tags() && high != 0) { return None; }
    let block = ((high as u64) << 32) | low as u64;
    if block >= filesystem_blocks { return None; }
    Some(ParsedTag { tag: Tag { block, flags, checksum }, next: offset + width })
}

pub fn encode_tag(tag: Tag, f: Features, filesystem_blocks: u64) -> (r: Option<Vec<u8>>)
    ensures f.wf(), match r {
        Some(raw) => tag_encodable(tag, f.view(), filesystem_blocks)
            && tag_admitted(raw@, 0, f.view(), filesystem_blocks)
            && encoded_tag_matches(raw@, tag, f.view()),
        None => !tag_encodable(tag, f.view(), filesystem_blocks),
    },
{
    hide(features::feature_valid);
    hide(crc::fold);
    let _ = f.version();
    if tag.block >= filesystem_blocks || tag.flags & !15u32 != 0
        || (!f.wide_tags() && tag.block > 0xffff_ffffu64) { return None; }
    if matches!(f.checksum(), Checksum::V2) && tag.checksum > 65535 { return None; }
    proof { address_halves_rejoin(tag.block); flags_fit_the_legacy_field(tag.flags); }
    let width = f.tag_bytes();
    let mut raw = zeroes(width).unwrap();
    put32(&mut raw, 0, tag.block as u32);
    match f.checksum() {
        Checksum::V3 => {
            put32(&mut raw, 4, tag.flags);
            put32(&mut raw, 8, (tag.block >> 32) as u32);
            put32(&mut raw, 12, tag.checksum);
            proof {
                assert(raw.len() == 16);
                assert(bytes::be32(raw@, 0) == tag.block as u32 as nat);
                assert(bytes::be32(raw@, 4) == tag.flags);
                assert(bytes::be32(raw@, 8) == (tag.block >> 32) as u32 as nat);
                assert(bytes::be32(raw@, 12) == tag.checksum);
                assert(tag_address(raw@, 0, f.view()) == tag.block);
                assert(encoded_tag_matches(raw@, tag, f.view()));
            }
        },
        Checksum::V2 => {
            put16(&mut raw, 4, tag.checksum as u16);
            put16(&mut raw, 6, tag.flags as u16);
            if f.wide_tags() { put32(&mut raw, 8, (tag.block >> 32) as u32); }
            proof {
                assert(bytes::be32(raw@, 0) == tag.block as u32 as nat);
                assert(be16_word(raw@, 4) == tag.checksum);
                assert(be16_word(raw@, 6) == tag.flags);
                if features::wide(f.view()) {
                    assert(raw.len() == 14);
                    assert(bytes::be32(raw@, 8) == (tag.block >> 32) as u32 as nat);
                    assert(raw@[12] == 0 && raw@[13] == 0);
                } else {
                    assert(raw.len() == 10);
                    assert(raw@[8] == 0 && raw@[9] == 0);
                }
                assert(tag_address(raw@, 0, f.view()) == tag.block);
                assert(encoded_tag_matches(raw@, tag, f.view()));
            }
        },
        _ => {
            put16(&mut raw, 6, tag.flags as u16);
            if f.wide_tags() { put32(&mut raw, 8, (tag.block >> 32) as u32); }
            proof {
                assert(bytes::be32(raw@, 0) == tag.block as u32 as nat);
                assert(be16_word(raw@, 6) == tag.flags);
                if features::wide(f.view()) {
                    assert(bytes::be32(raw@, 8) == (tag.block >> 32) as u32 as nat);
                }
                assert(tag_address(raw@, 0, f.view()) == tag.block);
                assert(encoded_tag_matches(raw@, tag, f.view()));
            }
        },
    }
    proof {
        assert(tag_encodable(tag, f.view(), filesystem_blocks));
        assert(tag_admitted(raw@, 0, f.view(), filesystem_blocks));
    }
    Some(raw)
}

pub struct Descriptor { sequence: u32, tags: Vec<Tag>, filesystem_blocks: Ghost<u64> }
impl Descriptor {
    pub closed spec fn descriptor_tags(&self) -> Seq<Tag> { self.tags@ }
    pub closed spec fn descriptor_limit(&self) -> u64 { self.filesystem_blocks@ }
    pub closed spec fn descriptor_tid(&self) -> u32 { self.sequence }
    pub open spec fn descriptor_wf(&self) -> bool {
        &&& 0 < self.descriptor_tags().len() <= MAX_TAGS
        &&& forall|i: int| 0 <= i < self.descriptor_tags().len() ==>
            #[trigger] self.descriptor_tags()[i].block < self.descriptor_limit()
                && self.descriptor_tags()[i].flags & !15u32 == 0
                && ((self.descriptor_tags()[i].flags & LAST_TAG != 0)
                    == (i + 1 == self.descriptor_tags().len()))
    }
    #[verifier::type_invariant]
    spec fn descriptor_invariant(self) -> bool { self.descriptor_wf() }
    pub fn descriptor_sequence(&self) -> (r: u32)
        ensures self.descriptor_wf(), r == self.descriptor_tid(),
    { proof { use_type_invariant(self); } self.sequence }
    pub fn descriptor_len(&self) -> (r: usize)
        ensures self.descriptor_wf(), r == self.descriptor_tags().len(), 0 < r <= MAX_TAGS,
    { proof { use_type_invariant(self); } self.tags.len() }
    pub fn descriptor_tag(&self, index: usize) -> (r: Option<Tag>)
        ensures self.descriptor_wf(), match r {
            Some(t) => index < self.descriptor_tags().len() && same_tag(t, self.descriptor_tags()[index as int])
                && t.block < self.descriptor_limit() && t.flags & !15u32 == 0,
            None => index >= self.descriptor_tags().len(),
        },
    {
        proof { use_type_invariant(self); }
        if index >= self.tags.len() { None } else { Some(self.tags[index]) }
    }
}
#[verifier::opaque]
pub open spec fn descriptor_header(raw: Seq<u8>, f: features::FeatureView, sequence: u32, seed: u32) -> bool {
    &&& crate::block_size::accepted(raw.len() as nat)
    &&& bytes::be32(raw, 0) == features::MAGIC
    &&& bytes::be32(raw, 4) == 1 && bytes::be32(raw, 8) == sequence
    &&& features::metadata_valid(f, seed, raw)
}
proof fn descriptor_header_checked(raw: Seq<u8>, f: features::FeatureView, sequence: u32, seed: u32)
    requires crate::block_size::accepted(raw.len() as nat),
        bytes::be32(raw, 0) == features::MAGIC, bytes::be32(raw, 4) == 1,
        bytes::be32(raw, 8) == sequence, features::metadata_valid(f, seed, raw),
    ensures descriptor_header(raw, f, sequence, seed),
{ reveal(descriptor_header); }

#[verifier::opaque]
pub open spec fn descriptor_entry(raw: Seq<u8>, f: features::FeatureView, uuid: Seq<u8>,
    blocks: u64, offset: nat, tag: Tag) -> bool
{
    let limit = raw.len() - features::tail_width(f);
    let next = offset + features::tag_width(f);
    &&& tag_admitted(raw.take(limit as int), offset as int, f, blocks)
    &&& tag_matches(tag, raw.take(limit as int), offset as int, f)
    &&& (tag.flags & SAME_UUID == 0 ==> next + 16 <= limit && raw.subrange(next as int, next as int + 16) == uuid)
}
pub open spec fn entry_end(offset: nat, f: features::FeatureView, tag: Tag) -> nat {
    offset + features::tag_width(f) + if tag.flags & SAME_UUID == 0 { 16nat } else { 0nat }
}
#[verifier::opaque]
pub open spec fn descriptor_witness(raw: Seq<u8>, f: features::FeatureView, uuid: Seq<u8>,
    blocks: u64, tags: Seq<Tag>, positions: Seq<nat>) -> bool
{
    &&& tags.len() == positions.len()
    &&& (tags.len() > 0 ==> positions[0] == 12)
    &&& forall|i: int| 0 <= i < tags.len() ==>
        #[trigger] descriptor_entry(raw, f, uuid, blocks, positions[i], tags[i])
            && (i > 0 ==> positions[i] == entry_end(positions[i - 1], f, tags[i - 1]))
}

proof fn descriptor_entry_checked(raw: Seq<u8>, f: features::FeatureView, uuid: Seq<u8>,
    blocks: u64, offset: nat, tag: Tag)
    requires tag_admitted(raw.take((raw.len() - features::tail_width(f)) as int), offset as int, f, blocks),
        tag_matches(tag, raw.take((raw.len() - features::tail_width(f)) as int), offset as int, f),
        tag.flags & SAME_UUID == 0 ==> offset + features::tag_width(f) + 16 <= raw.len() - features::tail_width(f)
            && raw.subrange(offset as int + features::tag_width(f), offset as int + features::tag_width(f) + 16) == uuid,
    ensures descriptor_entry(raw, f, uuid, blocks, offset, tag),
{ reveal(descriptor_entry); }

proof fn descriptor_witness_empty(raw: Seq<u8>, f: features::FeatureView, uuid: Seq<u8>, blocks: u64)
    ensures descriptor_witness(raw, f, uuid, blocks, Seq::<Tag>::empty(), Seq::<nat>::empty()),
{ reveal(descriptor_witness); }

proof fn descriptor_witness_push(raw: Seq<u8>, f: features::FeatureView, uuid: Seq<u8>,
    blocks: u64, tags: Seq<Tag>, positions: Seq<nat>, tag: Tag, offset: nat)
    requires descriptor_witness(raw, f, uuid, blocks, tags, positions),
        descriptor_entry(raw, f, uuid, blocks, offset, tag),
        tags.len() == 0 ==> offset == 12,
        tags.len() > 0 ==> offset == entry_end(positions[tags.len() as int - 1], f, tags[tags.len() as int - 1]),
    ensures descriptor_witness(raw, f, uuid, blocks, tags.push(tag), positions.push(offset)),
{
    reveal(descriptor_witness);
    assert forall|i: int| 0 <= i < tags.len() + 1 implies
        #[trigger] descriptor_entry(raw, f, uuid, blocks, positions.push(offset)[i], tags.push(tag)[i])
        && (i > 0 ==> positions.push(offset)[i] == entry_end(positions.push(offset)[i - 1], f, tags.push(tag)[i - 1])) by {
        if i < tags.len() {
            assert(descriptor_entry(raw, f, uuid, blocks, positions[i], tags[i]));
        } else { assert(i == tags.len()); }
    }
}

proof fn descriptor_witness_index(raw: Seq<u8>, f: features::FeatureView, uuid: Seq<u8>,
    blocks: u64, tags: Seq<Tag>, positions: Seq<nat>, index: int)
    requires descriptor_witness(raw, f, uuid, blocks, tags, positions), 0 <= index < tags.len(),
    ensures tags.len() == positions.len(),
        descriptor_entry(raw, f, uuid, blocks, positions[index], tags[index]),
        index > 0 ==> positions[index] == entry_end(positions[index - 1], f, tags[index - 1]),
{
    reveal(descriptor_witness);
    assert(descriptor_entry(raw, f, uuid, blocks, positions[index], tags[index]));
}

proof fn tag_readers_translate(source: Seq<u8>, target: Seq<u8>, offset: int, limit: int,
    f: features::FeatureView)
    requires features::feature_valid(f), source.len() == features::tag_width(f),
        0 <= offset, offset + source.len() <= limit <= target.len(),
        source == target.subrange(offset, offset + source.len()),
    ensures tag_flags(source, 0, f) == tag_flags(target.take(limit), offset, f),
        tag_checksum(source, 0, f) == tag_checksum(target.take(limit), offset, f),
        tag_high(source, 0, f) == tag_high(target.take(limit), offset, f),
        tag_address(source, 0, f) == tag_address(target.take(limit), offset, f),
{
    assert forall|i: int| 0 <= i < source.len() implies
        #[trigger] target.take(limit)[offset + i] == source[i] by {}
    if f.checksum is V3 {
        assert(features::tag_width(f) == 16);
    } else if f.checksum is V2 {
        if features::wide(f) { assert(features::tag_width(f) == 14); }
        else { assert(features::tag_width(f) == 10); }
    } else if features::wide(f) { assert(features::tag_width(f) == 12); }
    else { assert(features::tag_width(f) == 8); }
}
proof fn descriptor_entry_prefix_frame(before: Seq<u8>, after: Seq<u8>, prefix: nat,
    f: features::FeatureView, uuid: Seq<u8>, blocks: u64, offset: nat, tag: Tag)
    requires features::feature_valid(f), before.len() == after.len(), prefix <= before.len(),
        before.take(prefix as int) == after.take(prefix as int),
        descriptor_entry(before, f, uuid, blocks, offset, tag), entry_end(offset, f, tag) <= prefix,
    ensures descriptor_entry(after, f, uuid, blocks, offset, tag),
{
    reveal(descriptor_entry);
    let width = features::tag_width(f);
    let limit = before.len() - features::tail_width(f);
    let wire = before.subrange(offset as int, offset as int + width);
    assert(offset + width <= entry_end(offset, f, tag) <= prefix);
    equal_prefix_preserves_subrange(before, after, prefix as int, offset as int, offset as int + width);
    assert(wire =~= after.subrange(offset as int, offset as int + width));
    tag_readers_translate(wire, before, offset as int, limit as int, f);
    tag_readers_translate(wire, after, offset as int, limit as int, f);
    if tag.flags & SAME_UUID == 0 {
        assert(entry_end(offset, f, tag) == offset + width + 16);
        equal_prefix_preserves_subrange(before, after, prefix as int,
            offset as int + width, offset as int + width + 16);
        assert(before.subrange(offset as int + width, offset as int + width + 16)
            =~= after.subrange(offset as int + width, offset as int + width + 16));
    }
}

proof fn descriptor_entry_from_wire(encoded: Seq<u8>, raw: Seq<u8>, f: features::FeatureView,
    uuid: Seq<u8>, blocks: u64, offset: nat, tag: Tag)
    requires features::feature_valid(f), encoded.len() == features::tag_width(f),
        offset + encoded.len() <= raw.len() - features::tail_width(f),
        encoded == raw.subrange(offset as int, offset as int + encoded.len()),
        tag_admitted(encoded, 0, f, blocks), tag_matches(tag, encoded, 0, f),
        tag.flags & SAME_UUID == 0 ==> offset + encoded.len() + 16 <= raw.len() - features::tail_width(f)
            && raw.subrange(offset as int + encoded.len(), offset as int + encoded.len() + 16) == uuid,
    ensures descriptor_entry(raw, f, uuid, blocks, offset, tag),
{
    tag_readers_translate(encoded, raw, offset as int, (raw.len() - features::tail_width(f)) as int, f);
    descriptor_entry_checked(raw, f, uuid, blocks, offset, tag);
}

proof fn descriptor_witness_prefix_frame(before: Seq<u8>, after: Seq<u8>, prefix: nat,
    f: features::FeatureView, uuid: Seq<u8>, blocks: u64, tags: Seq<Tag>, positions: Seq<nat>)
    requires features::feature_valid(f), before.len() == after.len(), prefix <= before.len(),
        before.take(prefix as int) == after.take(prefix as int),
        descriptor_witness(before, f, uuid, blocks, tags, positions),
        forall|i: int| 0 <= i < tags.len() ==> #[trigger] entry_end(positions[i], f, tags[i]) <= prefix,
    ensures descriptor_witness(after, f, uuid, blocks, tags, positions),
{
    reveal(descriptor_witness);
    assert forall|i: int| 0 <= i < tags.len() implies
        #[trigger] descriptor_entry(after, f, uuid, blocks, positions[i], tags[i])
        && (i > 0 ==> positions[i] == entry_end(positions[i - 1], f, tags[i - 1])) by {
        descriptor_witness_index(before, f, uuid, blocks, tags, positions, i);
        descriptor_entry_prefix_frame(before, after, prefix, f, uuid, blocks, positions[i], tags[i]);
    }
}

pub fn parse_descriptor(raw: &[u8], f: Features, expected_sequence: u32,
    uuid_seed: u32, target_uuid: &[u8], filesystem_blocks: u64) -> (r: Option<Descriptor>)
    ensures f.wf(), match r {
        Some(d) => d.descriptor_wf() && d.descriptor_tid() == expected_sequence
            && d.descriptor_limit() == filesystem_blocks && target_uuid.len() == 16
            && descriptor_header(raw@, f.view(), expected_sequence, uuid_seed)
            && exists|positions: Seq<nat>| descriptor_witness(raw@, f.view(), target_uuid@,
                filesystem_blocks, d.descriptor_tags(), positions),
        None => true,
    },
{
    hide(crc::fold);
    let _ = f.version();
    if !crate::block_size::valid(raw.len()) || target_uuid.len() != 16 { return None; }
    if bytes::read_be32(raw, 0).unwrap() != features::MAGIC
        || bytes::read_be32(raw, 4).unwrap() != 1
        || bytes::read_be32(raw, 8).unwrap() != expected_sequence
        || !features::metadata_checksum_valid(f, uuid_seed, raw) { return None; }
    proof { descriptor_header_checked(raw@, f.view(), expected_sequence, uuid_seed); }
    let limit = raw.len() - f.descriptor_tail_bytes();
    let mut offset = 12usize;
    let mut tags = Vec::<Tag>::new();
    let ghost mut positions = Seq::<nat>::empty();
    proof { descriptor_witness_empty(raw@, f.view(), target_uuid@, filesystem_blocks); }
    while offset < limit
        invariant 12 <= offset <= limit <= raw.len(), tags.len() <= MAX_TAGS, positions.len() == tags.len(),
            limit == raw.len() - features::tail_width(f.view()), f.wf(), target_uuid.len() == 16,
            descriptor_header(raw@, f.view(), expected_sequence, uuid_seed),
            descriptor_witness(raw@, f.view(), target_uuid@, filesystem_blocks, tags@, positions),
            (tags.len() == 0 ==> offset == 12),
            (tags.len() > 0 ==> offset == entry_end(positions[tags.len() as int - 1], f.view(), tags@[tags.len() as int - 1])),
            forall|i: int| 0 <= i < tags.len() ==> #[trigger] tags@[i].block < filesystem_blocks
                && tags@[i].flags & !15u32 == 0 && tags@[i].flags & LAST_TAG == 0,
        decreases limit - offset,
    {
        if tags.len() >= MAX_TAGS { return None; }
        let parsed = match parse_tag(&raw[..limit], offset, f, filesystem_blocks) {
            Some(parsed) => parsed, None => { return None; }
        };
        let ghost start = offset as nat;
        offset = parsed.next;
        if parsed.tag.flags & SAME_UUID == 0 {
            if offset > limit || limit - offset < 16 { return None; }
            if !bytes::equal(&raw[offset..offset + 16], target_uuid) { return None; }
            offset += 16;
        }
        assert(offset == entry_end(start, f.view(), parsed.tag));
        // SAME_UUID can inherit the already selected journal/filesystem UUID.
        // No missing or foreign UUID is guessed from a payload block.
        let last = parsed.tag.flags & LAST_TAG != 0;
        let ghost old_tags = tags@;
        let ghost old_positions = positions;
        tags.push(parsed.tag);
        proof {
            descriptor_entry_checked(raw@, f.view(), target_uuid@, filesystem_blocks, start, parsed.tag);
            descriptor_witness_push(raw@, f.view(), target_uuid@, filesystem_blocks,
                old_tags, old_positions, parsed.tag, start);
            positions = old_positions.push(start);
            assert(tags@ == old_tags.push(parsed.tag));
            assert(positions.len() == tags.len());
            assert(positions[tags.len() as int - 1] == start);
            assert(tags@[tags.len() as int - 1] == parsed.tag);
            assert(offset == entry_end(positions[tags.len() as int - 1], f.view(), tags@[tags.len() as int - 1]));
            assert(descriptor_witness(raw@, f.view(), target_uuid@, filesystem_blocks, tags@, positions));
        }
        if last {
            let result = Descriptor { sequence: expected_sequence, tags, filesystem_blocks: Ghost(filesystem_blocks) };
            proof {
                assert(result.descriptor_wf());
                assert(exists|p: Seq<nat>| descriptor_witness(raw@, f.view(), target_uuid@,
                    filesystem_blocks, result.descriptor_tags(), p)) by {
                    assert(descriptor_witness(raw@, f.view(), target_uuid@, filesystem_blocks, result.descriptor_tags(), positions));
                }
            }
            return Some(result);
        }
    }
    None
}

proof fn canonical_flag_cases(original: u32, same_uuid: bool, last: bool)
    ensures
        ((original & 5u32) | (if same_uuid { 2u32 } else { 0u32 }) | (if last { 8u32 } else { 0u32 }))
            == if last {
                (if same_uuid { (original & 5u32) | 2u32 } else { original & 5u32 }) | 8u32
            } else { if same_uuid { (original & 5u32) | 2u32 } else { original & 5u32 } },
        (((original & 5u32) | (if same_uuid { 2u32 } else { 0u32 }) | (if last { 8u32 } else { 0u32 })) & 2u32)
            == if same_uuid { 2u32 } else { 0u32 },
{
    assert(((original & 5u32) | (if same_uuid { 2u32 } else { 0u32 }) | (if last { 8u32 } else { 0u32 }))
        == if last {
            (if same_uuid { (original & 5u32) | 2u32 } else { original & 5u32 }) | 8u32
        } else { if same_uuid { (original & 5u32) | 2u32 } else { original & 5u32 } }) by (bit_vector);
    assert((((original & 5u32) | (if same_uuid { 2u32 } else { 0u32 }) | (if last { 8u32 } else { 0u32 })) & 2u32)
        == if same_uuid { 2u32 } else { 0u32 }) by (bit_vector);
}

pub open spec fn canonical_tag(tag: Tag, index: int, count: nat, f: features::FeatureView) -> Tag {
    Tag { block: tag.block,
        flags: (tag.flags & (ESCAPE | DELETED)) | (if index == 0 { 0u32 } else { SAME_UUID })
            | (if index + 1 == count { LAST_TAG } else { 0u32 }),
        checksum: if features::metadata(f) { tag.checksum } else { 0u32 } }
}
pub open spec fn canonical_tags(tags: Seq<Tag>, f: features::FeatureView) -> Seq<Tag> {
    Seq::new(tags.len(), |i: int| canonical_tag(tags[i], i, tags.len(), f))
}

fn finish_descriptor(raw: Vec<u8>, f: Features, sequence: u32, uuid_seed: u32,
    target_uuid: &[u8], filesystem_blocks: u64, tags: &[Tag], block_bytes: usize,
    witness: Ghost<Seq<nat>>) -> (r: Option<Vec<u8>>)
    requires f.wf(), raw.len() == block_bytes, target_uuid.len() == 16, 0 < tags.len() <= MAX_TAGS,
        descriptor_header(raw@, f.view(), sequence, uuid_seed),
        descriptor_witness(raw@, f.view(), target_uuid@, filesystem_blocks,
            canonical_tags(tags@, f.view()), witness@),
    ensures f.wf(), match r {
        Some(image) => image@ == raw@ && image.len() == block_bytes && target_uuid.len() == 16
            && 0 < tags.len() <= MAX_TAGS && descriptor_header(image@, f.view(), sequence, uuid_seed)
            && exists|positions: Seq<nat>| descriptor_witness(image@, f.view(), target_uuid@,
                filesystem_blocks, canonical_tags(tags@, f.view()), positions),
        None => false,
    },
{
    proof {
        assert(exists|positions: Seq<nat>| descriptor_witness(raw@, f.view(), target_uuid@,
            filesystem_blocks, canonical_tags(tags@, f.view()), positions)) by {
            assert(descriptor_witness(raw@, f.view(), target_uuid@,
                filesystem_blocks, canonical_tags(tags@, f.view()), witness@));
        }
    }
    Some(raw)
}

/// Emit canonical UUID/LAST_TAG flags: one explicit UUID per descriptor, then
/// SAME_UUID; block/checksum/ESCAPE/DELETED semantics are retained.
pub fn encode_descriptor(tags: &[Tag], f: Features, sequence: u32, uuid_seed: u32,
    target_uuid: &[u8], filesystem_blocks: u64, block_bytes: usize) -> (r: Option<Vec<u8>>)
    ensures f.wf(), match r {
        Some(raw) => raw.len() == block_bytes && target_uuid.len() == 16
            && 0 < tags.len() <= MAX_TAGS && descriptor_header(raw@, f.view(), sequence, uuid_seed)
            && exists|positions: Seq<nat>| descriptor_witness(raw@, f.view(), target_uuid@,
                filesystem_blocks, canonical_tags(tags@, f.view()), positions),
        None => true,
    },
{
    hide(features::feature_valid);
    hide(crc::fold);
    let _ = f.version();
    if !crate::block_size::valid(block_bytes) || target_uuid.len() != 16
        || tags.len() == 0 || tags.len() > MAX_TAGS { return None; }
    let mut raw = zeroes(block_bytes).unwrap();
    put32(&mut raw, 0, features::MAGIC); put32(&mut raw, 4, 1); put32(&mut raw, 8, sequence);
    let limit = block_bytes - f.descriptor_tail_bytes();
    let mut offset = 12usize; let mut i = 0usize;
    let ghost mut positions = Seq::<nat>::empty();
    proof {
        descriptor_witness_empty(raw@, f.view(), target_uuid@, filesystem_blocks);
        assert(canonical_tags(tags@, f.view()).take(0) =~= Seq::<Tag>::empty());
    }
    while i < tags.len()
        invariant f.wf(), i <= tags.len() <= MAX_TAGS, tags.len() > 0, 12 <= offset <= limit <= raw.len(), raw.len() == block_bytes,
            crate::block_size::accepted(block_bytes as nat), target_uuid.len() == 16,
            bytes::be32(raw@, 0) == features::MAGIC, bytes::be32(raw@, 4) == 1, bytes::be32(raw@, 8) == sequence,
            positions.len() == i, limit == raw.len() - features::tail_width(f.view()),
            i == 0 ==> offset == 12,
            forall|j: int| 0 <= j < i ==> #[trigger] entry_end(positions[j], f.view(),
                canonical_tags(tags@, f.view())[j]) <= offset,
            descriptor_witness(raw@, f.view(), target_uuid@, filesystem_blocks,
                canonical_tags(tags@, f.view()).take(i as int), positions),
            i > 0 ==> offset == entry_end(positions[i as int - 1], f.view(),
                canonical_tags(tags@, f.view())[i as int - 1]),
        decreases tags.len() - i,
    {
        let ghost beginning = offset as nat;
        let ghost previous_wire = raw@;
        let ghost previous_positions = positions;
        let ghost previous_index = i;
        let ghost previous_tags = canonical_tags(tags@, f.view()).take(i as int);
        proof {
            assert(previous_tags.len() == i);
            assert(descriptor_witness(previous_wire, f.view(), target_uuid@, filesystem_blocks,
                previous_tags, previous_positions));
        }
        let mut tag = tags[i];
        let ghost input_flags = tag.flags;
        let ghost include_uuid = i != 0;
        let ghost include_last = i + 1 == tags.len();
        if tag.flags & !15u32 != 0 { return None; }
        tag.flags = tag.flags & (ESCAPE | DELETED);
        if i != 0 { tag.flags |= SAME_UUID; }
        if i + 1 == tags.len() { tag.flags |= LAST_TAG; }
        proof {
            assert((ESCAPE | DELETED) == 5u32) by (bit_vector);
            assert(SAME_UUID == 2u32 && LAST_TAG == 8u32);
            assert(input_flags == tags@[i as int].flags);
            canonical_flag_cases(input_flags, include_uuid, include_last);
            let actual = tag.flags;
            let normalized = (input_flags & 5u32)
                | (if include_uuid { 2u32 } else { 0u32 })
                | (if include_last { 8u32 } else { 0u32 });
            assert(actual == if include_last {
                (if include_uuid { (input_flags & 5u32) | 2u32 } else { input_flags & 5u32 }) | 8u32
            } else { if include_uuid { (input_flags & 5u32) | 2u32 } else { input_flags & 5u32 } });
            assert(actual == normalized);
            let canonical = canonical_tag(tags@[i as int], i as int, tags.len() as nat, f.view());
            assert(canonical.flags == normalized);
            assert(canonical_tags(tags@, f.view())[i as int] == canonical);
            assert(tag.block == canonical.block && tag.flags == canonical.flags);
            assert((canonical.flags & SAME_UUID) == if i == 0 { 0u32 } else { SAME_UUID });
        }
        let encoded = match encode_tag(tag, f, filesystem_blocks) { Some(raw) => raw, None => { return None; } };
        let uuid_bytes = if i == 0 { 16usize } else { 0usize };
        if offset > limit || encoded.len() > limit - offset { return None; }
        if uuid_bytes > limit - offset - encoded.len() { return None; }
        let copied = copy_span(&mut raw, offset, &encoded);
        assert(copied);
        offset += encoded.len();
        if i == 0 {
            let copied_uuid = copy_span(&mut raw, offset, target_uuid);
            assert(copied_uuid);
            offset += 16;
        }
        proof {
            let wire_tag = canonical_tags(tags@, f.view())[i as int];
            assert(tag.block == wire_tag.block && tag.flags == wire_tag.flags);
            assert(encoded.len() == features::tag_width(f.view()));
            assert(raw@.take(beginning as int) =~= previous_wire.take(beginning as int));
            assert(encoded@ =~= raw@.subrange(beginning as int, beginning as int + encoded.len()));
            assert(tag_matches(wire_tag, encoded@, 0, f.view()));
            if i == 0 {
                assert(wire_tag.flags & SAME_UUID == 0);
                assert(raw@.subrange(beginning as int + encoded.len(), beginning as int + encoded.len() + 16) == target_uuid@);
            } else { assert(wire_tag.flags & SAME_UUID != 0); }
            descriptor_entry_from_wire(encoded@, raw@, f.view(), target_uuid@, filesystem_blocks, beginning, wire_tag);
            assert(entry_end(beginning, f.view(), wire_tag) == offset);
            assert forall|j: int| 0 <= j < previous_tags.len() implies
                #[trigger] entry_end(previous_positions[j], f.view(), previous_tags[j]) <= beginning by {
                assert(previous_tags[j] == canonical_tags(tags@, f.view())[j]);
            }
            descriptor_witness_prefix_frame(previous_wire, raw@, beginning, f.view(), target_uuid@,
                filesystem_blocks, previous_tags, previous_positions);
            descriptor_witness_push(raw@, f.view(), target_uuid@, filesystem_blocks,
                previous_tags, previous_positions, wire_tag, beginning);
            positions = positions.push(beginning);
            let processed = canonical_tags(tags@, f.view()).take(i as int + 1);
            assert(processed =~= previous_tags.push(wire_tag));
            assert(descriptor_witness(raw@, f.view(), target_uuid@, filesystem_blocks, processed, positions));
        }
        i += 1;
    }
    let ghost before_checksum = raw@;
    assert(bytes::be32(before_checksum, 0) == features::MAGIC
        && bytes::be32(before_checksum, 4) == 1 && bytes::be32(before_checksum, 8) == sequence);
    assert(canonical_tags(tags@, f.view()).take(i as int) =~= canonical_tags(tags@, f.view()));
    if !features::stamp_metadata_checksum(f, uuid_seed, &mut raw) { return None; }
    proof {
        assert(raw@.take(limit as int) =~= before_checksum.take(limit as int));
        equal_prefix_preserves_be32(before_checksum, raw@, limit as int, 0);
        equal_prefix_preserves_be32(before_checksum, raw@, limit as int, 4);
        equal_prefix_preserves_be32(before_checksum, raw@, limit as int, 8);
        assert(bytes::be32(raw@, 0) == features::MAGIC
            && bytes::be32(raw@, 4) == 1 && bytes::be32(raw@, 8) == sequence);
        assert(features::metadata_valid(f.view(), uuid_seed, raw@));
        descriptor_header_checked(raw@, f.view(), sequence, uuid_seed);
        assert(raw.len() == block_bytes && target_uuid.len() == 16 && 0 < tags.len() <= MAX_TAGS);
        descriptor_witness_prefix_frame(before_checksum, raw@, limit as nat, f.view(), target_uuid@,
            filesystem_blocks, canonical_tags(tags@, f.view()), positions);
        assert(descriptor_witness(raw@, f.view(), target_uuid@, filesystem_blocks,
            canonical_tags(tags@, f.view()), positions));
    }
    finish_descriptor(raw, f, sequence, uuid_seed, target_uuid, filesystem_blocks,
        tags, block_bytes, Ghost(positions))
}

pub open spec fn payload_sum(f: features::FeatureView, seed: u32, sequence: u32, stored: Seq<u8>) -> u32 {
    let sum = crc::fold(crc::fold(seed, bytes::encoded_be(sequence)), stored);
    if f.checksum is V2 { sum & 65535u32 } else if f.checksum is V3 { sum } else { 0u32 }
}
pub open spec fn payload_valid(f: features::FeatureView, seed: u32, sequence: u32,
    tag: Tag, stored: Seq<u8>) -> bool {
    crate::block_size::accepted(stored.len() as nat)
        && (!features::metadata(f) || tag.checksum == payload_sum(f, seed, sequence, stored))
}
pub open spec fn escaped_image(raw: Seq<u8>) -> Seq<u8> {
    if bytes::be32(raw, 0) == features::MAGIC { bytes::splice(raw, 0, seq![0u8, 0u8, 0u8, 0u8]) } else { raw }
}
pub open spec fn restored_image(raw: Seq<u8>, escaped: bool) -> Seq<u8> {
    if escaped { bytes::splice(raw, 0, bytes::encoded_be(features::MAGIC)) } else { raw }
}
pub proof fn payload_magic_escape_round_trips(raw: Seq<u8>)
    requires crate::block_size::accepted(raw.len() as nat),
    ensures restored_image(escaped_image(raw), bytes::be32(raw, 0) == features::MAGIC) == raw,
{
    assert(restored_image(escaped_image(raw), bytes::be32(raw, 0) == features::MAGIC) =~= raw);
}

/// Check stored (possibly escaped) bytes before magic restoration.
pub fn payload_checksum_valid(f: Features, uuid_seed: u32, sequence: u32,
    tag: Tag, stored: &[u8]) -> (r: bool)
    ensures f.wf(), r == payload_valid(f.view(), uuid_seed, sequence, tag, stored@),
{
    let _ = f.version();
    if !crate::block_size::valid(stored.len()) { return false; }
    match f.checksum() {
        Checksum::V2 | Checksum::V3 => {
            let encoded = bytes::encode_be32(sequence);
            let checksum = crc::crc32c(crc::crc32c(uuid_seed, &encoded), stored);
            match f.checksum() {
                Checksum::V2 => tag.checksum == (checksum & 65535),
                _ => tag.checksum == checksum,
            }
        },
        _ => true,
    }
}

pub fn payload_checksum(f: Features, uuid_seed: u32, sequence: u32, stored: &[u8])
    -> (r: Option<u32>)
    ensures f.wf(), match r {
        Some(sum) => crate::block_size::accepted(stored.len() as nat) && sum == payload_sum(f.view(), uuid_seed, sequence, stored@),
        None => !crate::block_size::accepted(stored.len() as nat),
    },
{
    let _ = f.version();
    if !crate::block_size::valid(stored.len()) { return None; }
    match f.checksum() {
        Checksum::V2 | Checksum::V3 => {
            let encoded = bytes::encode_be32(sequence);
            let checksum = crc::crc32c(crc::crc32c(uuid_seed, &encoded), stored);
            if matches!(f.checksum(), Checksum::V2) { Some(checksum & 65535) } else { Some(checksum) }
        },
        _ => Some(0),
    }
}

pub fn escape_payload(raw: &[u8]) -> (r: Option<(Vec<u8>, bool)>)
    ensures match r {
        Some(pair) => crate::block_size::accepted(raw.len() as nat) && pair.0@ == escaped_image(raw@)
            && pair.1 == (bytes::be32(raw@, 0) == features::MAGIC),
        None => !crate::block_size::accepted(raw.len() as nat),
    },
{
    if !crate::block_size::valid(raw.len()) { return None; }
    let escaped = bytes::read_be32(raw, 0).unwrap() == features::MAGIC;
    let mut image = zeroes(raw.len()).unwrap(); let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len(), image.len() == raw.len(),
            escaped == (bytes::be32(raw@, 0) == features::MAGIC),
            forall|j: int| 0 <= j < i ==> #[trigger] image@[j] == if escaped && j < 4 { 0u8 } else { raw@[j] },
        decreases raw.len() - i,
    { image[i] = if escaped && i < 4 { 0 } else { raw[i] }; i += 1; }
    assert(image@ =~= escaped_image(raw@));
    Some((image, escaped))
}

pub fn restore_payload(stored: &[u8], escaped: bool) -> (r: Option<Vec<u8>>)
    ensures match r {
        Some(raw) => crate::block_size::accepted(stored.len() as nat) && raw@ == restored_image(stored@, escaped),
        None => !crate::block_size::accepted(stored.len() as nat),
    },
{
    if !crate::block_size::valid(stored.len()) { return None; }
    let mut image = zeroes(stored.len()).unwrap(); let mut i = 0usize;
    while i < stored.len()
        invariant i <= stored.len(), image.len() == stored.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] image@[j] == stored@[j],
        decreases stored.len() - i,
    { image[i] = stored[i]; i += 1; }
    assert(image@ =~= stored@);
    if escaped { put32(&mut image, 0, features::MAGIC); }
    Some(image)
}

pub open spec fn revoke_stride(f: features::FeatureView) -> nat { if features::wide(f) { 8nat } else { 4nat } }
pub open spec fn revoke_address(raw: Seq<u8>, f: features::FeatureView, index: int) -> u64 {
    let offset = 16 + index * revoke_stride(f) as int;
    if features::wide(f) {
        ((bytes::be32(raw, offset) as u64) << 32) | bytes::be32(raw, offset + 4) as u64
    } else { bytes::be32(raw, offset) as u64 }
}
pub open spec fn revoke_header(raw: Seq<u8>, f: features::FeatureView, sequence: u32, seed: u32) -> bool {
    &&& f.incompat & features::INCOMPAT_REVOKE != 0 && crate::block_size::accepted(raw.len() as nat)
    &&& bytes::be32(raw, 0) == features::MAGIC && bytes::be32(raw, 4) == 5 && bytes::be32(raw, 8) == sequence
    &&& features::metadata_valid(f, seed, raw)
    &&& 16 <= bytes::be32(raw, 12) <= raw.len() - features::tail_width(f)
    &&& (bytes::be32(raw, 12) - 16) % (revoke_stride(f) as int) == 0
}
pub open spec fn revoke_admitted(raw: Seq<u8>, f: features::FeatureView,
    sequence: u32, seed: u32, blocks: u64) -> bool {
    &&& revoke_header(raw, f, sequence, seed)
    &&& (bytes::be32(raw, 12) - 16) / (revoke_stride(f) as int) <= MAX_REVOKES
    &&& forall|i: int| 0 <= i < (bytes::be32(raw, 12) - 16) / (revoke_stride(f) as int) ==>
        #[trigger] revoke_address(raw, f, i) < blocks
}
pub open spec fn revoke_projection(raw: Seq<u8>, f: features::FeatureView) -> Seq<u64> {
    Seq::new(((bytes::be32(raw, 12) - 16) / (revoke_stride(f) as int)) as nat, |i: int| revoke_address(raw, f, i))
}
proof fn revoke_address_prefix_frame(before: Seq<u8>, after: Seq<u8>, prefix: int,
    f: features::FeatureView, index: int)
    requires features::feature_valid(f), 0 <= index,
        16 + (index + 1) * (revoke_stride(f) as int) <= prefix <= before.len(), prefix <= after.len(),
        before.take(prefix) == after.take(prefix),
    ensures revoke_address(before, f, index) == revoke_address(after, f, index),
{
    let offset = 16 + index * revoke_stride(f) as int;
    if features::wide(f) {
        assert(revoke_stride(f) == 8);
        assert(offset + 8 <= prefix);
    } else {
        assert(revoke_stride(f) == 4);
        assert(offset + 4 <= prefix);
    }
    equal_prefix_preserves_be32(before, after, prefix, offset);
    assert(bytes::be32(before, offset) == bytes::be32(after, offset));
    if features::wide(f) {
        equal_prefix_preserves_be32(before, after, prefix, offset + 4);
        assert(bytes::be32(before, offset + 4) == bytes::be32(after, offset + 4));
    }
}

pub struct RevokeView {
    pub sequence: u32, pub blocks: Seq<u64>, pub source: Seq<u8>, pub features: features::FeatureView,
    pub seed: u32, pub filesystem_blocks: u64,
}
pub open spec fn revoke_well_formed(v: RevokeView) -> bool {
    features::feature_valid(v.features) && revoke_admitted(v.source, v.features, v.sequence, v.seed, v.filesystem_blocks)
        && v.blocks == revoke_projection(v.source, v.features)
}
pub struct Revokes {
    sequence: u32, blocks: Vec<u64>,
    source: Ghost<Seq<u8>>, features: Ghost<features::FeatureView>, seed: Ghost<u32>, limit: Ghost<u64>,
}
impl Revokes {
    pub closed spec fn revoke_view(&self) -> RevokeView {
        RevokeView { sequence: self.sequence, blocks: self.blocks@, source: self.source@,
            features: self.features@, seed: self.seed@, filesystem_blocks: self.limit@ }
    }
    pub open spec fn revokes_wf(&self) -> bool { revoke_well_formed(self.revoke_view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.revokes_wf() }
    pub fn revoke_sequence(&self) -> (r: u32) ensures self.revokes_wf(), r == self.revoke_view().sequence,
    { proof { use_type_invariant(self); } self.sequence }
    pub fn revoke_len(&self) -> (r: usize)
        ensures self.revokes_wf(), r == self.revoke_view().blocks.len(), r <= MAX_REVOKES,
    { proof { use_type_invariant(self); } self.blocks.len() }
    pub fn revoke_block(&self, index: usize) -> (r: Option<u64>)
        ensures self.revokes_wf(), match r {
            Some(block) => index < self.revoke_view().blocks.len() && block == self.revoke_view().blocks[index as int]
                && block < self.revoke_view().filesystem_blocks,
            None => index >= self.revoke_view().blocks.len(),
        },
    {
        proof { use_type_invariant(self); }
        if index >= self.blocks.len() { None } else { Some(self.blocks[index]) }
    }
}

pub fn parse_revoke(raw: &[u8], f: Features, sequence: u32, uuid_seed: u32,
    filesystem_blocks: u64) -> (r: Option<Revokes>)
    ensures f.wf(), match r {
        Some(revokes) => revokes.revokes_wf() && revokes.revoke_view() == (RevokeView {
            sequence, blocks: revoke_projection(raw@, f.view()), source: raw@, features: f.view(),
            seed: uuid_seed, filesystem_blocks }),
        None => !revoke_admitted(raw@, f.view(), sequence, uuid_seed, filesystem_blocks),
    },
{
    hide(features::feature_valid);
    hide(crc::fold);
    let _ = f.version();
    if !f.revoke() || !crate::block_size::valid(raw.len()) { return None; }
    if bytes::read_be32(raw, 0).unwrap() != features::MAGIC
        || bytes::read_be32(raw, 4).unwrap() != 5
        || bytes::read_be32(raw, 8).unwrap() != sequence
        || !features::metadata_checksum_valid(f, uuid_seed, raw) { return None; }
    let count = bytes::read_be32(raw, 12).unwrap() as usize;
    let limit = raw.len() - f.descriptor_tail_bytes();
    let stride = if f.wide_tags() { 8usize } else { 4usize };
    if count < 16 || count > limit || (count - 16) % stride != 0 { return None; }
    let entries = (count - 16) / stride;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(count as int - 16, stride as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative((count as int - 16) / (stride as int), stride as int);
        assert(entries as int == (count as int - 16) / (stride as int));
        assert((count as int - 16) % (stride as int) == 0);
        assert(count == 16 + entries * stride) by (nonlinear_arith)
            requires count as int - 16 == (count as int - 16) / (stride as int) * (stride as int)
                    + (count as int - 16) % (stride as int),
                (count as int - 16) % (stride as int) == 0,
                entries as int == (count as int - 16) / (stride as int);
        assert(entries <= MAX_REVOKES);
        assert(revoke_header(raw@, f.view(), sequence, uuid_seed));
        assert(revoke_projection(raw@, f.view()).len() == entries);
    }
    let mut blocks = Vec::<u64>::new(); let mut i = 0usize;
    while i < entries
        invariant f.wf(), i == blocks.len() <= entries <= MAX_REVOKES,
            count == 16 + entries * stride, 16 <= count <= limit <= raw.len(),
            bytes::be32(raw@, 12) == count,
            entries as int == (bytes::be32(raw@, 12) - 16) / (revoke_stride(f.view()) as int),
            stride == 4 || stride == 8, stride == revoke_stride(f.view()),
            revoke_header(raw@, f.view(), sequence, uuid_seed),
            revoke_projection(raw@, f.view()).len() == entries,
            blocks@ == revoke_projection(raw@, f.view()).take(i as int),
            forall|j: int| 0 <= j < i ==> #[trigger] blocks@[j] < filesystem_blocks,
        decreases entries - i,
    {
        let offset = 16 + i * stride;
        let first = bytes::read_be32(raw, offset).unwrap() as u64;
        let block = if f.wide_tags() {
            (first << 32) | bytes::read_be32(raw, offset + 4).unwrap() as u64
        } else { first };
        assert(block == revoke_address(raw@, f.view(), i as int));
        if block >= filesystem_blocks {
            proof { assert(!revoke_admitted(raw@, f.view(), sequence, uuid_seed, filesystem_blocks)); }
            return None;
        }
        blocks.push(block);
        proof {
            assert(revoke_projection(raw@, f.view()).take(i as int + 1)
                =~= revoke_projection(raw@, f.view()).take(i as int).push(block));
        }
        i += 1;
    }
    proof {
        assert(blocks@ =~= revoke_projection(raw@, f.view()));
        assert forall|j: int| 0 <= j < (bytes::be32(raw@, 12) - 16) / (revoke_stride(f.view()) as int)
            implies #[trigger] revoke_address(raw@, f.view(), j) < filesystem_blocks by {
            assert(j < entries);
            assert(revoke_projection(raw@, f.view())[j] == revoke_address(raw@, f.view(), j));
            assert(blocks@[j] == revoke_projection(raw@, f.view())[j]);
            assert(blocks@[j] < filesystem_blocks);
        }
        assert(revoke_admitted(raw@, f.view(), sequence, uuid_seed, filesystem_blocks));
    }
    Some(Revokes { sequence, blocks, source: Ghost(raw@), features: Ghost(f.view()),
        seed: Ghost(uuid_seed), limit: Ghost(filesystem_blocks) })
}

pub fn encode_revoke(blocks: &[u64], f: Features, sequence: u32, uuid_seed: u32,
    filesystem_blocks: u64, block_bytes: usize) -> (r: Option<Vec<u8>>)
    ensures f.wf(), match r {
        Some(raw) => raw.len() == block_bytes && revoke_admitted(raw@, f.view(), sequence, uuid_seed, filesystem_blocks)
            && revoke_projection(raw@, f.view()) == blocks@,
        None => true,
    },
{
    hide(features::feature_valid);
    hide(crc::fold);
    let _ = f.version();
    if !f.revoke() || !crate::block_size::valid(block_bytes) || blocks.len() > MAX_REVOKES { return None; }
    let stride = if f.wide_tags() { 8usize } else { 4usize };
    let limit = block_bytes - f.descriptor_tail_bytes();
    if blocks.len() > (limit - 16) / stride { return None; }
    let count = 16 + blocks.len() * stride;
    let mut raw = zeroes(block_bytes).unwrap();
    put32(&mut raw, 0, features::MAGIC); put32(&mut raw, 4, 5); put32(&mut raw, 8, sequence);
    put32(&mut raw, 12, count as u32);
    let mut i = 0usize;
    while i < blocks.len()
        invariant f.wf(), i <= blocks.len() <= MAX_REVOKES, raw.len() == block_bytes,
            16 + blocks.len() * stride <= limit <= block_bytes, stride == 4 || stride == 8,
            stride == revoke_stride(f.view()), limit == raw.len() - features::tail_width(f.view()),
            count == 16 + blocks.len() * stride,
            crate::block_size::accepted(block_bytes as nat), f.view().incompat & features::INCOMPAT_REVOKE != 0,
            bytes::be32(raw@, 0) == features::MAGIC && bytes::be32(raw@, 4) == 5
                && bytes::be32(raw@, 8) == sequence && bytes::be32(raw@, 12) == count,
            forall|j: int| 0 <= j < i ==> #[trigger] revoke_address(raw@, f.view(), j) == blocks@[j],
            forall|j: int| 0 <= j < i ==> #[trigger] blocks@[j] < filesystem_blocks
                && (features::wide(f.view()) || blocks@[j] <= 0xffff_ffffu64),
        decreases blocks.len() - i,
    {
        let block = blocks[i];
        let ghost previous_wire = raw@;
        if block >= filesystem_blocks || (!f.wide_tags() && block > 0xffff_ffffu64) { return None; }
        if f.wide_tags() {
            put32(&mut raw, 16 + i * stride, (block >> 32) as u32);
            put32(&mut raw, 20 + i * stride, block as u32);
        } else { put32(&mut raw, 16 + i * stride, block as u32); }
        proof {
            address_halves_rejoin(block);
            assert(revoke_address(raw@, f.view(), i as int) == block);
            assert(raw@.take(16 + i as int * stride as int) =~= previous_wire.take(16 + i as int * stride as int));
            assert forall|j: int| 0 <= j < i implies
                #[trigger] revoke_address(raw@, f.view(), j) == blocks@[j] by {
                revoke_address_prefix_frame(previous_wire, raw@, 16 + i as int * stride as int, f.view(), j);
            }
        }
        i += 1;
    }
    let ghost before_checksum = raw@;
    if !features::stamp_metadata_checksum(f, uuid_seed, &mut raw) { return None; }
    proof {
        assert(raw@.take(count as int) =~= before_checksum.take(count as int));
        assert forall|j: int| 0 <= j < blocks.len() implies
            #[trigger] revoke_address(raw@, f.view(), j) == blocks@[j] by {
            revoke_address_prefix_frame(before_checksum, raw@, count as int, f.view(), j);
        }
        assert(revoke_header(raw@, f.view(), sequence, uuid_seed));
        assert(revoke_projection(raw@, f.view()).len() == blocks.len());
        assert(revoke_projection(raw@, f.view()) =~= blocks@);
        assert(revoke_admitted(raw@, f.view(), sequence, uuid_seed, filesystem_blocks));
    }
    Some(raw)
}

}
