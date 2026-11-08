// SPDX-License-Identifier: MPL-2.0

//! Standalone JBD2 feature/version and checksum codecs.
//! This expansion does not grant replay, mount or device-fence authority.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{block_size, bytes, crc};

verus! {

pub const MAGIC: u32 = 0xc03b3998;
pub const COMPAT_CHECKSUM: u32 = 1;
pub const INCOMPAT_REVOKE: u32 = 1;
pub const INCOMPAT_64BIT: u32 = 2;
pub const INCOMPAT_ASYNC_COMMIT: u32 = 4;
pub const INCOMPAT_CSUM_V2: u32 = 8;
pub const INCOMPAT_CSUM_V3: u32 = 16;
pub const INCOMPAT_FAST_COMMIT: u32 = 32;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Checksum { None, V1, V2, V3 }

pub struct FeatureView { pub version: u32, pub compat: u32, pub incompat: u32, pub checksum: Checksum }
pub open spec fn selected_checksum(compat: u32, incompat: u32) -> Checksum {
    if incompat & INCOMPAT_CSUM_V3 != 0 { Checksum::V3 }
    else if incompat & INCOMPAT_CSUM_V2 != 0 { Checksum::V2 }
    else if compat & COMPAT_CHECKSUM != 0 { Checksum::V1 } else { Checksum::None }
}
pub open spec fn allowed(version: u32, compat: u32, incompat: u32, ro: u32, checksum_type: u8) -> bool {
    let v1 = compat & COMPAT_CHECKSUM != 0;
    let v2 = incompat & INCOMPAT_CSUM_V2 != 0;
    let v3 = incompat & INCOMPAT_CSUM_V3 != 0;
    &&& (version == 1 || version == 2) && ro == 0
    &&& compat & !1u32 == 0 && incompat & !63u32 == 0
    &&& (version == 1 ==> compat == 0 && incompat == 0)
    &&& !(v1 && (v2 || v3)) && !(v2 && v3)
    &&& ((v2 || v3) ==> checksum_type == 4)
}
pub open spec fn feature_valid(v: FeatureView) -> bool {
    allowed(v.version, v.compat, v.incompat, 0,
        if v.checksum is V2 || v.checksum is V3 { 4u8 } else { 0u8 })
        && v.checksum == selected_checksum(v.compat, v.incompat)
}
pub open spec fn wide(v: FeatureView) -> bool { v.incompat & INCOMPAT_64BIT != 0 }
pub open spec fn metadata(v: FeatureView) -> bool { v.checksum is V2 || v.checksum is V3 }
pub open spec fn tag_width(v: FeatureView) -> nat {
    if v.checksum is V3 { 16nat } else if v.checksum is V2 {
        if wide(v) { 14nat } else { 10nat }
    } else { if wide(v) { 12nat } else { 8nat } }
}
pub open spec fn tail_width(v: FeatureView) -> nat { if metadata(v) { 4nat } else { 0nat } }

#[derive(Clone, Copy)]
pub struct Features { version: u32, compat: u32, incompat: u32, checksum: Checksum }

impl Features {
    pub closed spec fn view(&self) -> FeatureView {
        FeatureView { version: self.version, compat: self.compat, incompat: self.incompat, checksum: self.checksum }
    }
    pub open spec fn wf(&self) -> bool { feature_valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn version(&self) -> (r: u32) ensures self.wf(), r == self.view().version {
        proof { use_type_invariant(self); } self.version
    }
    pub fn compatible_bits(&self) -> (r: u32) ensures self.wf(), r == self.view().compat {
        proof { use_type_invariant(self); } self.compat
    }
    pub fn incompatible_bits(&self) -> (r: u32) ensures self.wf(), r == self.view().incompat {
        proof { use_type_invariant(self); } self.incompat
    }
    pub fn checksum(&self) -> (r: Checksum) ensures self.wf(), r == self.view().checksum {
        proof { use_type_invariant(self); } self.checksum
    }
    pub fn wide_tags(&self) -> (r: bool) ensures self.wf(), r == wide(self.view()) {
        proof { use_type_invariant(self); } self.incompat & INCOMPAT_64BIT != 0
    }
    pub fn revoke(&self) -> (r: bool) ensures self.wf(), r == (self.view().incompat & INCOMPAT_REVOKE != 0) {
        proof { use_type_invariant(self); } self.incompat & INCOMPAT_REVOKE != 0
    }
    pub fn async_commit(&self) -> (r: bool) ensures self.wf(), r == (self.view().incompat & INCOMPAT_ASYNC_COMMIT != 0) {
        proof { use_type_invariant(self); } self.incompat & INCOMPAT_ASYNC_COMMIT != 0
    }
    pub fn fast_commit(&self) -> (r: bool) ensures self.wf(), r == (self.view().incompat & INCOMPAT_FAST_COMMIT != 0) {
        proof { use_type_invariant(self); } self.incompat & INCOMPAT_FAST_COMMIT != 0
    }
    pub fn metadata_checksum(&self) -> (r: bool) ensures self.wf(), r == metadata(self.view()) {
        proof { use_type_invariant(self); }
        match self.checksum { Checksum::V2 | Checksum::V3 => true, _ => false }
    }
    pub fn tag_bytes(&self) -> (r: usize)
        ensures self.wf(), r == tag_width(self.view()), 8 <= r <= 16,
    {
        proof { use_type_invariant(self); }
        match self.checksum {
            Checksum::V3 => 16,
            Checksum::V2 => if self.incompat & INCOMPAT_64BIT != 0 { 14 } else { 10 },
            _ => if self.incompat & INCOMPAT_64BIT != 0 { 12 } else { 8 },
        }
    }
    pub fn descriptor_tail_bytes(&self) -> (r: usize)
        ensures self.wf(), r == tail_width(self.view()), r == 0 || r == 4,
    {
        proof { use_type_invariant(self); }
        match self.checksum { Checksum::V2 | Checksum::V3 => 4, _ => 0 }
    }
}

/// Parse understood JBD2 features. Unknown bits are rejected by this standalone
/// profile; the surrounding filesystem feature policy is unchanged.
pub fn negotiate(version: u32, compat: u32, incompat: u32, ro: u32, checksum_type: u8)
    -> (r: Option<Features>)
    ensures match r {
        Some(f) => f.wf() && f.view() == (FeatureView { version, compat, incompat,
            checksum: selected_checksum(compat, incompat) }) && allowed(version, compat, incompat, ro, checksum_type),
        None => !allowed(version, compat, incompat, ro, checksum_type),
    },
{
    if version != 1 && version != 2 { return None; }
    if ro != 0 || compat & !1u32 != 0 || incompat & !63u32 != 0 { return None; }
    if version == 1 && (compat != 0 || incompat != 0) { return None; }
    let v1 = compat & COMPAT_CHECKSUM != 0;
    let v2 = incompat & INCOMPAT_CSUM_V2 != 0;
    let v3 = incompat & INCOMPAT_CSUM_V3 != 0;
    if (v1 && (v2 || v3)) || (v2 && v3) { return None; }
    if (v2 || v3) && checksum_type != 4 { return None; }
    let checksum = if v3 { Checksum::V3 } else if v2 { Checksum::V2 }
        else if v1 { Checksum::V1 } else { Checksum::None };
    Some(Features { version, compat, incompat, checksum })
}

pub struct SuperView {
    pub block_bytes: u32, pub blocks: u32, pub first: u32, pub sequence: u32, pub start: u32,
    pub error: u32, pub uuid: Seq<u8>, pub users: u32, pub fast_commit_blocks: u32, pub features: FeatureView,
}
pub open spec fn source_features(raw: Seq<u8>) -> FeatureView {
    let version = if bytes::be32(raw, 4) == 3 { 1u32 } else { 2u32 };
    let compat = if version == 2 { bytes::be32(raw, 36) as u32 } else { 0u32 };
    let incompat = if version == 2 { bytes::be32(raw, 40) as u32 } else { 0u32 };
    FeatureView { version, compat, incompat, checksum: selected_checksum(compat, incompat) }
}
pub open spec fn source_fc(raw: Seq<u8>) -> u32 {
    if source_features(raw).incompat & INCOMPAT_FAST_COMMIT != 0 {
        if bytes::be32(raw, 84) == 0 { 256u32 } else { bytes::be32(raw, 84) as u32 }
    } else { 0u32 }
}
pub open spec fn super_admitted(raw: Seq<u8>) -> bool {
    let f = source_features(raw);
    &&& raw.len() >= 1024 && bytes::be32(raw, 0) == MAGIC
    &&& (bytes::be32(raw, 4) == 3 || bytes::be32(raw, 4) == 4)
    &&& allowed(f.version, f.compat, f.incompat,
        if f.version == 2 { bytes::be32(raw, 44) as u32 } else { 0u32 },
        if f.version == 2 { raw[80] } else { 0u8 })
    &&& block_size::accepted(bytes::be32(raw, 12))
    &&& bytes::be32(raw, 16) >= 1024
    &&& 0 < bytes::be32(raw, 20) < bytes::be32(raw, 16)
    &&& (bytes::be32(raw, 28) == 0 || bytes::be32(raw, 20) <= bytes::be32(raw, 28) < bytes::be32(raw, 16))
    &&& (!metadata(f) || bytes::be32(raw, 252)
        == crc::fold(0xffff_ffff, crc::zero4(raw.take(1024), 252)) as nat)
    &&& source_fc(raw) as nat <= bytes::be32(raw, 16) - 1024
}
pub open spec fn super_projection(raw: Seq<u8>) -> SuperView {
    SuperView { block_bytes: bytes::be32(raw, 12) as u32, blocks: bytes::be32(raw, 16) as u32,
        first: bytes::be32(raw, 20) as u32, sequence: bytes::be32(raw, 24) as u32,
        start: bytes::be32(raw, 28) as u32, error: bytes::be32(raw, 32) as u32,
        uuid: raw.subrange(48, 64), users: if source_features(raw).version == 2 { bytes::be32(raw, 64) as u32 } else { 1u32 },
        fast_commit_blocks: source_fc(raw), features: source_features(raw) }
}
pub struct Superblock {
    pub block_bytes: u32, pub blocks: u32, pub first: u32, pub sequence: u32, pub start: u32,
    pub error: u32, pub uuid: [u8; 16], pub users: u32, pub fast_commit_blocks: u32, features: Features,
}
impl Superblock {
    pub closed spec fn view(&self) -> SuperView {
        SuperView { block_bytes: self.block_bytes, blocks: self.blocks, first: self.first, sequence: self.sequence,
            start: self.start, error: self.error, uuid: self.uuid@, users: self.users,
            fast_commit_blocks: self.fast_commit_blocks, features: self.features.view() }
    }
    pub fn features(&self) -> (r: Features)
        ensures r.wf(), r.view() == self.view().features,
    { proof { use_type_invariant(&self.features); } self.features }
}

/// Decode the fixed 1024-byte JBD2 superblock, not a filesystem superblock.
/// V1 padding is not interpreted as V2 feature words.
pub fn parse_superblock(raw: &[u8]) -> (r: Option<Superblock>)
    ensures match r {
        Some(s) => super_admitted(raw@) && s.view() == super_projection(raw@) && s.view().features.version >= 1
            && 1024 <= s.view().blocks && 0 < s.view().first < s.view().blocks
            && s.view().fast_commit_blocks <= s.view().blocks - 1024
            && block_size::accepted(s.view().block_bytes as nat),
        None => !super_admitted(raw@),
    },
{
    hide(crc::fold);
    if raw.len() < 1024 { return None; }
    if bytes::read_be32(raw, 0).unwrap() != MAGIC { return None; }
    let kind = bytes::read_be32(raw, 4).unwrap();
    let version = if kind == 3 { 1u32 } else if kind == 4 { 2u32 } else { return None; };
    let compat = if version == 2 { bytes::read_be32(raw, 36).unwrap() } else { 0 };
    let incompat = if version == 2 { bytes::read_be32(raw, 40).unwrap() } else { 0 };
    let ro = if version == 2 { bytes::read_be32(raw, 44).unwrap() } else { 0 };
    let checksum_type = if version == 2 { raw[80] } else { 0 };
    let features = match negotiate(version, compat, incompat, ro, checksum_type) {
        Some(features) => features, None => { return None; }
    };
    let block_bytes = bytes::read_be32(raw, 12).unwrap();
    let blocks = bytes::read_be32(raw, 16).unwrap();
    let first = bytes::read_be32(raw, 20).unwrap();
    let sequence = bytes::read_be32(raw, 24).unwrap();
    let start = bytes::read_be32(raw, 28).unwrap();
    if !block_size::valid(block_bytes as usize) || blocks < 1024
        || first == 0 || first >= blocks || (start != 0 && (start < first || start >= blocks)) { return None; }
    if features.metadata_checksum() {
        let actual = crc::crc32c_zero4(0xffff_ffff, &raw[..1024], 252).unwrap();
        if bytes::read_be32(raw, 252).unwrap() != actual { return None; }
    }
    let fast_commit_blocks = if features.fast_commit() {
        let value = bytes::read_be32(raw, 84).unwrap();
        if value == 0 { 256u32 } else { value }
    } else { 0u32 };
    if fast_commit_blocks > blocks - 1024 { return None; }
    assert(super_admitted(raw@));
    let mut uuid = [0u8; 16]; let mut i = 0usize;
    while i < 16
        invariant i <= 16, raw.len() >= 1024, super_admitted(raw@),
            features.wf(), features.view() == source_features(raw@),
            block_bytes as nat == bytes::be32(raw@, 12), blocks as nat == bytes::be32(raw@, 16),
            first as nat == bytes::be32(raw@, 20), sequence as nat == bytes::be32(raw@, 24),
            start as nat == bytes::be32(raw@, 28), fast_commit_blocks == source_fc(raw@),
            forall|j: int| 0 <= j < i ==> #[trigger] uuid@[j] == raw@[48 + j],
        decreases 16 - i,
    { uuid[i] = raw[48 + i]; i += 1; }
    assert(uuid@ =~= raw@.subrange(48, 64));
    Some(Superblock { block_bytes, blocks, first, sequence, start,
        error: bytes::read_be32(raw, 32).unwrap(), uuid,
        users: if version == 2 { bytes::read_be32(raw, 64).unwrap() } else { 1 },
        fast_commit_blocks, features })
}

pub open spec fn crc_be_bit(c: u32) -> u32 {
    if c & 0x8000_0000u32 != 0 { (c << 1) ^ 0x04c1_1db7u32 } else { c << 1 }
}
pub open spec fn crc_be_steps(c: u32, n: nat) -> u32
    decreases n,
{ if n == 0 { c } else { crc_be_bit(crc_be_steps(c, (n - 1) as nat)) } }
pub open spec fn crc_be_byte(c: u32, b: u8) -> u32 { crc_be_steps(c ^ ((b as u32) << 24), 8) }
pub open spec fn crc_be_fold(c: u32, raw: Seq<u8>) -> u32
    decreases raw.len(),
{ if raw.len() == 0 { c } else { crc_be_byte(crc_be_fold(c, raw.drop_last()), raw.last()) } }

/// Linux crc32_be uses the normal Ethernet polynomial and no final complement.
pub fn crc32_be(seed: u32, raw: &[u8]) -> (r: u32)
    ensures r == crc_be_fold(seed, raw@),
{
    let mut result = seed; let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len(), result == crc_be_fold(seed, raw@.subrange(0, i as int)),
        decreases raw.len() - i,
    {
        let ghost previous = result;
        result = result ^ ((raw[i] as u32) << 24);
        let mut bit = 0u8;
        while bit < 8
            invariant bit <= 8, i < raw.len(),
                result == crc_be_steps(previous ^ ((raw@[i as int] as u32) << 24), bit as nat),
            decreases 8 - bit,
        {
            result = if result & 0x8000_0000u32 != 0 {
                (result << 1) ^ 0x04c1_1db7u32
            } else { result << 1 };
            bit += 1;
        }
        proof {
            assert(raw@.subrange(0, i as int + 1).drop_last() =~= raw@.subrange(0, i as int));
            assert(raw@.subrange(0, i as int + 1).last() == raw@[i as int]);
        }
        i += 1;
    }
    assert(raw@.subrange(0, raw.len() as int) =~= raw@);
    result
}
pub fn extend_v1(checksum: u32, raw: &[u8]) -> (r: u32)
    ensures r == crc_be_fold(checksum, raw@),
{ crc32_be(checksum, raw) }

pub open spec fn metadata_valid(f: FeatureView, seed: u32, raw: Seq<u8>) -> bool {
    block_size::accepted(raw.len()) && (!metadata(f) ||
        bytes::be32(raw, raw.len() as int - 4) == crc::fold(seed, crc::zero4(raw, raw.len() as int - 4)) as nat)
}
pub open spec fn metadata_image(f: FeatureView, seed: u32, raw: Seq<u8>) -> Seq<u8> {
    if metadata(f) { bytes::splice(raw, raw.len() as int - 4,
        bytes::encoded_be(crc::fold(seed, crc::zero4(raw, raw.len() as int - 4)))) } else { raw }
}
proof fn zeroed_checksum_domain_is_independent_of_the_stored_word(raw: Seq<u8>, offset: int, value: u32)
    requires 0 <= offset, offset + 4 <= raw.len(),
    ensures crc::zero4(bytes::splice(raw, offset, bytes::encoded_be(value)), offset) == crc::zero4(raw, offset),
{
    assert(crc::zero4(bytes::splice(raw, offset, bytes::encoded_be(value)), offset) =~= crc::zero4(raw, offset));
}
fn put_word(raw: &mut [u8], offset: usize, value: u32) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r == (offset as int + 4 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, offset as int, bytes::encoded_be(value)) } else { old(raw)@ },
        r ==> bytes::be32(final(raw)@, offset as int) == value,
        forall|i: int| 0 <= i < old(raw).len() && !(offset <= i < offset as int + 4)
            ==> #[trigger] final(raw)@[i] == old(raw)@[i],
        forall|word: int| 0 <= word && word + 4 <= old(raw).len()
            && (word + 4 <= offset || word >= offset as int + 4) ==>
                #[trigger] bytes::be32(final(raw)@, word) == bytes::be32(old(raw)@, word),
{
    let ghost before = raw@;
    let success = bytes::write_be32(raw, offset, value);
    proof {
        if success {
            assert forall|i: int| 0 <= i < before.len() && !(offset <= i < offset as int + 4)
                implies #[trigger] raw@[i] == before[i] by {
                bytes::splice_frame(before, offset as int, bytes::encoded_be(value), i);
            }
            assert forall|word: int| 0 <= word && word + 4 <= before.len()
                && (word + 4 <= offset || word >= offset as int + 4)
                implies #[trigger] bytes::be32(raw@, word) == bytes::be32(before, word) by {
                bytes::splice_word_frame(before, offset as int, bytes::encoded_be(value), word);
            }
        }
    }
    success
}

pub fn metadata_checksum_valid(features: Features, seed: u32, raw: &[u8]) -> (r: bool)
    ensures features.wf(), r == metadata_valid(features.view(), seed, raw@),
{
    if !block_size::valid(raw.len()) { proof { use_type_invariant(&features); } return false; }
    if !features.metadata_checksum() { return true; }
    let offset = raw.len() - 4;
    let expected = crc::crc32c_zero4(seed, raw, offset).unwrap();
    bytes::read_be32(raw, offset).unwrap() == expected
}
pub fn stamp_metadata_checksum(features: Features, seed: u32, raw: &mut [u8]) -> (r: bool)
    ensures features.wf(), final(raw).len() == old(raw).len(),
        r == block_size::accepted(old(raw)@.len()),
        final(raw)@ == if r { metadata_image(features.view(), seed, old(raw)@) } else { old(raw)@ },
        r ==> metadata_valid(features.view(), seed, final(raw)@),
{
    proof { use_type_invariant(&features); }
    if !block_size::valid(raw.len()) { return false; }
    if !features.metadata_checksum() { return true; }
    let offset = raw.len() - 4;
    let ghost before = raw@;
    let checksum = crc::crc32c_zero4(seed, raw, offset).unwrap();
    let success = put_word(raw, offset, checksum);
    assert(success);
    proof {
        zeroed_checksum_domain_is_independent_of_the_stored_word(before, offset as int, checksum);
        assert(metadata_valid(features.view(), seed, raw@));
    }
    true
}

pub open spec fn commit_valid(f: FeatureView, seed: u32, sequence: u32, transaction_crc: u32, raw: Seq<u8>) -> bool {
    &&& block_size::accepted(raw.len())
    &&& bytes::be32(raw, 0) == MAGIC && bytes::be32(raw, 4) == 2 && bytes::be32(raw, 8) == sequence
    &&& match f.checksum {
        Checksum::None => true,
        Checksum::V1 => (raw[12] == 1 && raw[13] == 4 && bytes::be32(raw, 16) == transaction_crc)
            || (raw[12] == 0 && raw[13] == 0 && bytes::be32(raw, 16) == 0),
        _ => bytes::be32(raw, 16) == crc::fold(seed, crc::zero4(raw, 16)) as nat,
    }
}
pub fn commit_checksum_valid(features: Features, seed: u32, sequence: u32,
    transaction_v1_checksum: u32, raw: &[u8]) -> (r: bool)
    ensures features.wf(), r == commit_valid(features.view(), seed, sequence, transaction_v1_checksum, raw@),
{
    proof { use_type_invariant(&features); }
    if !block_size::valid(raw.len()) { return false; }
    if bytes::read_be32(raw, 0).unwrap() != MAGIC || bytes::read_be32(raw, 4).unwrap() != 2
        || bytes::read_be32(raw, 8).unwrap() != sequence { return false; }
    match features.checksum() {
        Checksum::None => true,
        Checksum::V1 => {
            let found = bytes::read_be32(raw, 16).unwrap();
            (raw[12] == 1 && raw[13] == 4 && found == transaction_v1_checksum)
                || (raw[12] == 0 && raw[13] == 0 && found == 0)
        },
        _ => bytes::read_be32(raw, 16).unwrap() == crc::crc32c_zero4(seed, raw, 16).unwrap(),
    }
}

pub fn encode_commit(features: Features, seed: u32, sequence: u32,
    transaction_v1_checksum: u32, block_bytes: usize, seconds: u64, nanoseconds: u32)
    -> (r: Option<Vec<u8>>)
    ensures features.wf(), match r {
        Some(raw) => raw.len() == block_bytes && block_size::accepted(block_bytes as nat)
            && commit_valid(features.view(), seed, sequence, transaction_v1_checksum, raw@),
        None => !block_size::accepted(block_bytes as nat) || nanoseconds >= 1_000_000_000,
    },
{
    proof { use_type_invariant(&features); }
    if !block_size::valid(block_bytes) || nanoseconds >= 1_000_000_000 { return None; }
    let mut raw = Vec::<u8>::new(); let mut i = 0usize;
    while i < block_bytes
        invariant i == raw.len(), i <= block_bytes <= 65536,
            forall|j: int| 0 <= j < i ==> #[trigger] raw@[j] == 0,
        decreases block_bytes - i,
    { raw.push(0); i += 1; }
    let _ = put_word(&mut raw, 0, MAGIC);
    let _ = put_word(&mut raw, 4, 2);
    let _ = put_word(&mut raw, 8, sequence);
    let _ = put_word(&mut raw, 48, (seconds >> 32) as u32);
    let _ = put_word(&mut raw, 52, seconds as u32);
    let _ = put_word(&mut raw, 56, nanoseconds);
    assert(bytes::be32(raw@, 0) == MAGIC && bytes::be32(raw@, 4) == 2 && bytes::be32(raw@, 8) == sequence);
    let checksum = match features.checksum() {
        Checksum::V1 => { raw[12] = 1; raw[13] = 4; transaction_v1_checksum },
        Checksum::V2 | Checksum::V3 => crc::crc32c_zero4(seed, &raw, 16).unwrap(),
        Checksum::None => 0,
    };
    let ghost before = raw@;
    proof {
        assert(bytes::be32(before, 0) == MAGIC && bytes::be32(before, 4) == 2 && bytes::be32(before, 8) == sequence);
        if metadata(features.view()) {
            assert(checksum == crc::fold(seed, crc::zero4(before, 16)));
        }
    }
    let _ = put_word(&mut raw, 16, checksum);
    proof {
        assert(bytes::be32(raw@, 0) == MAGIC && bytes::be32(raw@, 4) == 2 && bytes::be32(raw@, 8) == sequence);
        if metadata(features.view()) {
            assert(before.subrange(16, 20) =~= seq![0u8, 0u8, 0u8, 0u8]);
            crc::zero4_restores_written_checksum(before, 16, checksum);
            zeroed_checksum_domain_is_independent_of_the_stored_word(before, 16, checksum);
            assert(bytes::be32(raw@, 16) == crc::fold(seed, crc::zero4(raw@, 16)) as nat);
        } else if features.view().checksum is V1 {
            assert(raw@[12] == 1 && raw@[13] == 4 && bytes::be32(raw@, 16) == transaction_v1_checksum);
        }
        assert(commit_valid(features.view(), seed, sequence, transaction_v1_checksum, raw@));
    }
    Some(raw)
}

/// Offline format after-image. This preserves bytes outside the feature,
/// checksum-type, fast-commit-size and checksum fields. No write authority.
pub fn rewrite_clean_features(source: &[u8], requested: Features, fast_commit_blocks: u32)
    -> (r: Option<Vec<u8>>)
    ensures requested.wf(), match r {
        Some(raw) => source.len() >= 1024 && raw.len() == 1024 && super_admitted(raw@)
            && source_features(raw@) == requested.view()
            && bytes::be32(raw@, 28) == 0 && bytes::be32(raw@, 32) == 0
            && (forall|i: int| 0 <= i < 1024 && !(36 <= i < 48) && i != 80
                && !(84 <= i < 88) && !(252 <= i < 256) ==> #[trigger] raw@[i] == source@[i]),
        None => true,
    },
{
    proof { use_type_invariant(&requested); }
    let old = match parse_superblock(source) { Some(old) => old, None => { return None; } };
    if old.features().version() != 2 || requested.version() != 2 || old.start != 0 || old.error != 0 { return None; }
    let fc = if requested.fast_commit() { if fast_commit_blocks == 0 { 256u32 } else { fast_commit_blocks } } else { 0u32 };
    if fc > old.blocks - 1024 { return None; }
    let mut raw = Vec::<u8>::new(); let mut i = 0usize;
    while i < 1024
        invariant i <= 1024, raw.len() == i, source.len() >= 1024,
            forall|j: int| 0 <= j < i ==> #[trigger] raw@[j] == source@[j],
        decreases 1024 - i,
    { raw.push(source[i]); i += 1; }
    assert(raw@ =~= source@.take(1024));
    proof {
        assert(bytes::be32(raw@, 4) == 4);
        assert(bytes::be32(raw@, 16) == old.blocks);
        assert(bytes::be32(raw@, 28) == 0 && bytes::be32(raw@, 32) == 0);
    }
    let _ = put_word(&mut raw, 36, requested.compatible_bits());
    let _ = put_word(&mut raw, 40, requested.incompatible_bits());
    let _ = put_word(&mut raw, 44, 0);
    let _ = put_word(&mut raw, 84, if requested.fast_commit() { fast_commit_blocks } else { 0 });
    let _ = put_word(&mut raw, 252, 0);
    raw[80] = if requested.metadata_checksum() { 4 } else { 0 };
    proof {
        assert(source_features(raw@) == requested.view());
        assert(source_fc(raw@) == fc);
        assert(bytes::be32(raw@, 28) == 0 && bytes::be32(raw@, 32) == 0);
    }
    if requested.metadata_checksum() {
        let checksum = crc::crc32c_zero4(0xffff_ffff, &raw, 252).unwrap();
        let ghost before = raw@;
        let _ = put_word(&mut raw, 252, checksum);
        proof {
            assert(before.subrange(252, 256) =~= seq![0u8, 0u8, 0u8, 0u8]);
            crc::zero4_restores_written_checksum(before, 252, checksum);
            zeroed_checksum_domain_is_independent_of_the_stored_word(before, 252, checksum);
            assert(bytes::be32(raw@, 252) == crc::fold(0xffff_ffff, crc::zero4(raw@, 252)) as nat);
        }
    }
    proof {
        // Establish framing before using the source's admitted geometry.
        assert forall|j: int| 0 <= j < 1024 && !(36 <= j < 48) && j != 80
            && !(84 <= j < 88) && !(252 <= j < 256) implies #[trigger] raw@[j] == source@[j] by {}
        assert(raw.len() == 1024);
        assert(raw@.take(1024) =~= raw@);
        assert(bytes::be32(raw@, 0) == bytes::be32(source@, 0));
        assert(bytes::be32(raw@, 4) == bytes::be32(source@, 4));
        assert(bytes::be32(raw@, 12) == bytes::be32(source@, 12));
        assert(bytes::be32(raw@, 16) == bytes::be32(source@, 16));
        assert(bytes::be32(raw@, 20) == bytes::be32(source@, 20));
        assert(bytes::be32(raw@, 28) == bytes::be32(source@, 28));
        assert(super_admitted(source@));
        assert(bytes::be32(raw@, 0) == MAGIC && bytes::be32(raw@, 4) == 4);
        assert(block_size::accepted(bytes::be32(raw@, 12)));
        assert(bytes::be32(raw@, 16) >= 1024);
        assert(0 < bytes::be32(raw@, 20) < bytes::be32(raw@, 16));
        assert(bytes::be32(raw@, 28) == 0);

        assert(source_features(raw@) == requested.view());
        assert(bytes::be32(raw@, 44) == 0);
        assert(raw@[80] == if metadata(requested.view()) { 4u8 } else { 0u8 });
        assert(allowed(source_features(raw@).version, source_features(raw@).compat,
            source_features(raw@).incompat, bytes::be32(raw@, 44) as u32, raw@[80]));
        assert(source_fc(raw@) == fc);
        assert(source_fc(raw@) as nat <= bytes::be32(raw@, 16) - 1024);
        if metadata(source_features(raw@)) {
            assert(bytes::be32(raw@, 252)
                == crc::fold(0xffff_ffff, crc::zero4(raw@.take(1024), 252)) as nat);
        }
        assert(super_admitted(raw@));
    }
    Some(raw)
}

}
