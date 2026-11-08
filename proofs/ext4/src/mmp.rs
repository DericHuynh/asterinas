// SPDX-License-Identifier: MPL-2.0

//! Linux MMP bytes and an owned observation/write/flush protocol. It needs
//! cooperative peers, noncolliding claim sequences, fresh device reads,
//! bounded write visibility and a monotonic clock. Disk wall time is only
//! diagnostic. Protocol state does not grant a mount or device lease.
//!
//! Available owners and outstanding commands have separate private runtime
//! representations. Ghost histories bind every command, report, and abort to
//! its exact software predecessor. An aborted pending command remains pending
//! until its completion report; forgetting it cannot recover an owner.

use vstd::prelude::*;
use crate::{block_size, bytes, crc};

verus! {

pub const MAGIC: u32 = 0x004d4d50;
pub const SEQ_CLEAN: u32 = 0xff4d4d50;
pub const SEQ_FSCK: u32 = 0xe24d4d50;
pub const SEQ_MAX: u32 = 0xe24d4d4f;
pub const STRUCT_BYTES: usize = 1024;
pub const CHECKSUM_OFFSET: usize = 1020;
pub const MIN_CHECK_SECONDS: u16 = 5;
pub const MAX_CHECK_SECONDS: u16 = 300;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Error { Geometry, Address, Magic, Checksum, Name, Busy, Sequence, Clock, Wait, Phase, Exhausted, Io }
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Sequence { Clean, Fsck, Active(u32), Unknown(u32) }
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Stage {
    WaitOld, NeedWrite, NeedFlush, WaitClaim, Ready,
    Quiesce, NeedStopRead, NeedCleanWrite, NeedCleanFlush, Stopped, Faulted,
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Completion { Succeeded, Failed }
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ReadKind { OldObservation, ClaimObservation, HeartbeatObservation, StopObservation }

pub open spec fn sequence_class(sequence: u32) -> Sequence {
    if sequence == SEQ_CLEAN { Sequence::Clean }
    else if sequence == SEQ_FSCK { Sequence::Fsck }
    else if sequence <= SEQ_MAX { Sequence::Active(sequence) } else { Sequence::Unknown(sequence) }
}
pub open spec fn disk_time(raw: Seq<u8>) -> u64 {
    (bytes::le32(raw, 8) as u64) | ((bytes::le32(raw, 12) as u64) << 32)
}
pub open spec fn checksum(raw: Seq<u8>, seed: u32) -> u32 { crc::fold(seed, raw.take(1020)) }
pub open spec fn rewritten(before: Seq<u8>, after: Seq<u8>, sequence: u32, wall_time: u64,
    node: Seq<u8>, device: Seq<u8>, interval: u16, seed: u32, metadata: bool) -> bool
{
    &&& before.len() == after.len() && block_size::accepted(after.len()) && after.len() >= 1024
    &&& node.len() <= 64 && device.len() <= 32
    &&& bytes::le32(after, 0) == MAGIC && bytes::le32(after, 4) == sequence
    &&& disk_time(after) == wall_time && bytes::le16(after, 112) == interval
    &&& forall|i: int| 0 <= i < 64 ==> #[trigger] after[16 + i] == if i < node.len() { node[i] } else { 0 }
    &&& forall|i: int| 0 <= i < 32 ==> #[trigger] after[80 + i] == if i < device.len() { device[i] } else { 0 }
    &&& after.subrange(114, 1020) == before.subrange(114, 1020)
    &&& after.subrange(1024, after.len() as int) == before.subrange(1024, before.len() as int)
    &&& if metadata { bytes::le32(after, 1020) == checksum(after, seed) }
        else { after.subrange(1020, 1024) == before.subrange(1020, 1024) }
}
pub fn classify(sequence: u32) -> (r: Sequence)
    ensures r == sequence_class(sequence),
{
    if sequence == SEQ_CLEAN { Sequence::Clean }
    else if sequence == SEQ_FSCK { Sequence::Fsck }
    else if sequence <= SEQ_MAX { Sequence::Active(sequence) }
    else { Sequence::Unknown(sequence) }
}
fn copy(raw: &[u8]) -> (r: Vec<u8>) ensures r@ == raw@ {
    let mut out = Vec::new(); let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len(), out.len() == i, out@ == raw@.take(i as int),
        decreases raw.len() - i,
    { out.push(raw[i]); i += 1; }
    out
}
pub open spec fn encoded16(value: u16) -> Seq<u8> { seq![(value % 256) as u8, (value / 256) as u8] }
pub open spec fn encoded64(value: u64) -> Seq<u8> {
    bytes::encoded_le((value & 0xffffffffu64) as u32) + bytes::encoded_le((value >> 32) as u32)
}
fn write32(raw: &mut Vec<u8>, at: usize, value: u32) -> (r: bool)
    ensures final(raw).len() == old(raw).len(), r == (at as int + 4 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, at as int, bytes::encoded_le(value)) } else { old(raw)@ },
        r ==> bytes::le32(final(raw)@, at as int) == value,
{
    bytes::write_le32(raw.as_mut_slice(), at, value)
}
fn write16(raw: &mut Vec<u8>, at: usize, value: u16) -> (r: bool)
    ensures final(raw).len() == old(raw).len(), r == (at as int + 2 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, at as int, encoded16(value)) } else { old(raw)@ },
        r ==> bytes::le16(final(raw)@, at as int) == value,
{
    let word = bytes::encode_le16(value);
    proof {
        assert(word@[0] as int == value as int % 256
            && word@[1] as int == value as int / 256) by (nonlinear_arith)
            requires word@[0] as int + 256 * word@[1] as int == value as int,
                0 <= word@[0] <= 255, 0 <= word@[1] <= 255;
        assert(word@ =~= encoded16(value));
    }
    bytes::write_bytes(raw.as_mut_slice(), at, &word)
}
fn read64(raw: &[u8], at: usize) -> (r: Option<u64>)
    ensures match r { Some(value) => at + 8 <= raw.len()
        && value == (bytes::le32(raw@, at as int) as u64) | ((bytes::le32(raw@, at as int + 4) as u64) << 32),
        None => at > raw.len() || raw.len() - at < 8 },
{
    if at > raw.len() || raw.len() - at < 8 { return None; }
    let low = bytes::read_le32(raw, at).unwrap() as u64;
    let high = bytes::read_le32(raw, at + 4).unwrap() as u64;
    Some(low | (high << 32))
}
fn write64(raw: &mut Vec<u8>, at: usize, value: u64) -> (r: bool)
    ensures final(raw).len() == old(raw).len(), r == (at as int + 8 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, at as int, encoded64(value)) } else { old(raw)@ },
        r ==> (bytes::le32(final(raw)@, at as int) as u64) | ((bytes::le32(final(raw)@, at as int + 4) as u64) << 32) == value,
{
    if at > raw.len() || raw.len() - at < 8 { return false; }
    let ghost before = raw@;
    proof {
        assert((value & 0xffffffffu64) <= u32::MAX as u64) by (bit_vector);
        assert((value >> 32) <= u32::MAX as u64) by (bit_vector);
    }
    let low = (value & 0xffffffffu64) as u32;
    let high = (value >> 32) as u32;
    write32(raw, at, low);
    write32(raw, at + 4, high);
    proof {
        assert(raw@ =~= bytes::splice(before, at as int, encoded64(value)));
        assert((low as u64) | ((high as u64) << 32) == value) by (bit_vector)
            requires low == (value & 0xffffffffu64) as u32, high == (value >> 32) as u32;
    }
    true
}
fn due(now: u64, seconds: u64) -> (r: Option<u64>)
    ensures match r { Some(end) => end as nat == now as nat + seconds as nat, None => now as nat + seconds as nat > u64::MAX },
{
    if seconds > u64::MAX - now { None } else { Some(now + seconds) }
}
fn wait_seconds(interval: u16) -> (r: u64)
    ensures r == if interval as nat * 2 + 1 < interval as nat + 60 { interval as nat * 2 + 1 } else { interval as nat + 60 }, 0 < r <= 65595,
{
    let a = interval as u64 * 2 + 1;
    let b = interval as u64 + 60;
    if a < b { a } else { b }
}
fn next_sequence(sequence: u32) -> (r: u32)
    ensures r == if sequence >= SEQ_MAX { 1u32 } else { (sequence + 1) as u32 }, 0 < r <= SEQ_MAX,
{
    if sequence >= SEQ_MAX { 1 } else { sequence + 1 }
}

pub struct RecordView { pub raw: Seq<u8>, pub sequence: u32, pub wall_time: u64, pub interval: u16 }
pub open spec fn record_valid(v: RecordView) -> bool {
    block_size::accepted(v.raw.len()) && v.raw.len() >= 1024
        && bytes::le32(v.raw, 0) == MAGIC && v.sequence == bytes::le32(v.raw, 4) as u32
        && v.wall_time == disk_time(v.raw) && v.interval == bytes::le16(v.raw, 112) as u16
}
pub struct Record { raw: Vec<u8>, sequence: u32, wall_time: u64, interval: u16 }
impl Record {
    pub closed spec fn view(&self) -> RecordView {
        RecordView { raw: self.raw@, sequence: self.sequence, wall_time: self.wall_time, interval: self.interval }
    }
    pub open spec fn wf(&self) -> bool { record_valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn record_bytes(&self) -> (r: &[u8]) ensures r@ == self.view().raw { &self.raw }
    pub fn record_sequence(&self) -> (r: u32) ensures r == self.view().sequence { self.sequence }
    pub fn record_wall_time(&self) -> (r: u64) ensures r == self.view().wall_time { self.wall_time }
    pub fn record_check_interval(&self) -> (r: u16) ensures r == self.view().interval { self.interval }
    pub fn record_node_name(&self) -> (r: &[u8])
        ensures self.wf(), r@ == self.view().raw.subrange(16, 80),
    { proof { use_type_invariant(self); }
        if self.raw.len() < 80 { &[] } else { &self.raw[16..80] }
    }
    pub fn record_device_name(&self) -> (r: &[u8])
        ensures self.wf(), r@ == self.view().raw.subrange(80, 112),
    { proof { use_type_invariant(self); }
        if self.raw.len() < 112 { &[] } else { &self.raw[80..112] }
    }
}

/// The checksum is the filesystem metadata seed over exactly bytes 0..1020.
pub fn parse(raw: &[u8], seed: u32, metadata: bool) -> (r: Result<Record, Error>)
    ensures (match r { Ok(_) => true, Err(_) => false }) == record_error(raw@, seed, metadata).is_none(),
        match r { Err(error) => record_error(raw@, seed, metadata) == Some(error), Ok(_) => true },
        match r {
        Ok(record) => record.wf() && record.view().raw == raw@
            && (metadata ==> bytes::le32(raw@, 1020) == checksum(raw@, seed)),
        Err(_) => true,
    },
{
    if !block_size::valid(raw.len()) || raw.len() < STRUCT_BYTES { return Err(Error::Geometry); }
    if bytes::read_le32(raw, 0) != Some(MAGIC) { return Err(Error::Magic); }
    if metadata && bytes::read_le32(raw, CHECKSUM_OFFSET) != Some(crc::crc32c(seed, &raw[..CHECKSUM_OFFSET])) {
        return Err(Error::Checksum);
    }
    let sequence = bytes::read_le32(raw, 4).unwrap();
    let wall_time = match read64(raw, 8) { Some(value) => value, None => { return Err(Error::Geometry); } };
    let interval = bytes::read_le16(raw, 112).unwrap();
    Ok(Record { raw: copy(raw), sequence, wall_time, interval })
}

proof fn equal_prefix_byte(before: Seq<u8>, after: Seq<u8>, prefix: int, index: int)
    requires before.len() == after.len(), 0 <= index < prefix <= before.len(),
        before.take(prefix) == after.take(prefix),
    ensures before[index] == after[index],
{
    vstd::seq::lemma_seq_subrange_index(before, 0, prefix, index);
    vstd::seq::lemma_seq_subrange_index(after, 0, prefix, index);
}
proof fn equal_prefix_word(before: Seq<u8>, after: Seq<u8>, prefix: int, at: int)
    requires before.len() == after.len(), 0 <= at, at + 4 <= prefix <= before.len(),
        before.take(prefix) == after.take(prefix),
    ensures bytes::le32(before, at) == bytes::le32(after, at),
{
    equal_prefix_byte(before, after, prefix, at);
    equal_prefix_byte(before, after, prefix, at + 1);
    equal_prefix_byte(before, after, prefix, at + 2);
    equal_prefix_byte(before, after, prefix, at + 3);
}
proof fn equal_prefix_range(before: Seq<u8>, after: Seq<u8>, prefix: int, first: int, end: int)
    requires before.len() == after.len(), 0 <= first <= end <= prefix <= before.len(),
        before.take(prefix) == after.take(prefix),
    ensures before.subrange(first, end) == after.subrange(first, end),
{
    vstd::seq::lemma_seq_subrange_len(before, first, end);
    vstd::seq::lemma_seq_subrange_len(after, first, end);
    assert forall|i: int| 0 <= i < end - first implies
        #[trigger] before.subrange(first, end)[i] == #[trigger] after.subrange(first, end)[i] by {
        equal_prefix_byte(before, after, prefix, first + i);
        vstd::seq::lemma_seq_subrange_index(before, first, end, i);
        vstd::seq::lemma_seq_subrange_index(after, first, end, i);
    }
    assert(before.subrange(first, end) =~= after.subrange(first, end));
}

proof fn prefix_preserves_padded_name(before: Seq<u8>, after: Seq<u8>, name: Seq<u8>,
    offset: nat, width: nat, prefix: nat)
    requires before.len() == after.len(), offset + width <= prefix <= before.len(),
        before.take(prefix as int) == after.take(prefix as int),
        forall|j: int| 0 <= j < width ==> #[trigger] before[offset as int + j]
            == if j < name.len() { name[j] } else { 0u8 },
    ensures forall|j: int| 0 <= j < width ==> #[trigger] after[offset as int + j]
        == if j < name.len() { name[j] } else { 0u8 },
{
    assert forall|j: int| 0 <= j < width implies #[trigger] after[offset as int + j]
        == if j < name.len() { name[j] } else { 0u8 } by {
        equal_prefix_byte(before, after, prefix as int, offset as int + j);
    }
}

proof fn checksum_sealing_preserves_prepared_record(source: Seq<u8>, body: Seq<u8>, after: Seq<u8>,
    sequence: u32, wall_time: u64, node: Seq<u8>, device: Seq<u8>, interval: u16, seed: u32, metadata: bool)
    requires rewritten(source, body, sequence, wall_time, node, device, interval, seed, false),
        after.len() == body.len(), after.take(1020) == body.take(1020),
        after.subrange(1024, after.len() as int) == body.subrange(1024, body.len() as int),
        metadata ==> bytes::le32(after, 1020) == checksum(after, seed),
        !metadata ==> after == body,
    ensures rewritten(source, after, sequence, wall_time, node, device, interval, seed, metadata),
{
    hide(crc::fold);
    equal_prefix_word(body, after, 1020, 0);
    equal_prefix_word(body, after, 1020, 4);
    equal_prefix_word(body, after, 1020, 8);
    equal_prefix_word(body, after, 1020, 12);
    equal_prefix_byte(body, after, 1020, 112);
    equal_prefix_byte(body, after, 1020, 113);
    equal_prefix_range(body, after, 1020, 114, 1020);
    prefix_preserves_padded_name(body, after, node, 16, 64, 1020);
    prefix_preserves_padded_name(body, after, device, 80, 32, 1020);
    assert(disk_time(after) == disk_time(body));
    assert(bytes::le16(after, 112) == bytes::le16(body, 112));
}

pub fn rewrite(raw: &[u8], sequence: u32, wall_time: u64, node: &[u8], device: &[u8],
    interval: u16, seed: u32, metadata: bool) -> (r: Result<Vec<u8>, Error>)
    ensures (match r { Ok(_) => true, Err(_) => false }) == rewrite_error_bytes(raw@, node@, device@).is_none(),
        match r { Err(error) => rewrite_error_bytes(raw@, node@, device@) == Some(error), Ok(_) => true },
        match r {
        Ok(out) => rewritten(raw@, out@, sequence, wall_time, node@, device@, interval, seed, metadata),
        Err(_) => true,
    },
{
    hide(crc::fold);
    if !block_size::valid(raw.len()) || raw.len() < STRUCT_BYTES { return Err(Error::Geometry); }
    if node.len() > 64 || device.len() > 32 { return Err(Error::Name); }
    let mut out = copy(raw);
    if !write32(&mut out, 0, MAGIC) || !write32(&mut out, 4, sequence)
        || !write64(&mut out, 8, wall_time) || !write16(&mut out, 112, interval) {
        return Err(Error::Geometry);
    }
    let ghost header = out@;
    proof {
        assert(bytes::le32(header, 0) == MAGIC);
        assert(bytes::le32(header, 4) == sequence);
        assert(disk_time(header) == wall_time);
        assert(bytes::le16(header, 112) == interval);
        assert(header.subrange(114, 1020) == raw@.subrange(114, 1020));
        assert(header.subrange(1020, header.len() as int) == raw@.subrange(1020, raw.len() as int));
    }
    let mut i = 0usize;
    while i < 64
        invariant i <= 64, out.len() == raw.len(), raw.len() >= STRUCT_BYTES, header.len() == raw.len(),
            bytes::le32(header, 0) == MAGIC, bytes::le32(header, 4) == sequence,
            disk_time(header) == wall_time, bytes::le16(header, 112) == interval,
            header.subrange(114, 1020) == raw@.subrange(114, 1020),
            header.subrange(1020, header.len() as int) == raw@.subrange(1020, raw.len() as int),
            out@.take(16) == header.take(16),
            out@.subrange(80, out.len() as int) == header.subrange(80, header.len() as int),
            forall|j: int| 0 <= j < i ==> #[trigger] out@[16 + j] == if j < node.len() { node@[j] } else { 0 },
        decreases 64 - i,
    { out.set(16 + i, if i < node.len() { node[i] } else { 0 }); i += 1; }
    let ghost named = out@;
    i = 0;
    while i < 32
        invariant i <= 32, out.len() == raw.len(), raw.len() >= STRUCT_BYTES, named.len() == raw.len(),
            header.len() == raw.len(),
            bytes::le32(header, 0) == MAGIC, bytes::le32(header, 4) == sequence,
            disk_time(header) == wall_time, bytes::le16(header, 112) == interval,
            header.subrange(114, 1020) == raw@.subrange(114, 1020),
            header.subrange(1020, header.len() as int) == raw@.subrange(1020, raw.len() as int),
            named.take(16) == header.take(16),
            named.subrange(80, named.len() as int) == header.subrange(80, header.len() as int),
            forall|j: int| 0 <= j < 64 ==> #[trigger] named[16 + j] == if j < node.len() { node@[j] } else { 0 },
            out@.take(80) == named.take(80),
            out@.subrange(112, out.len() as int) == named.subrange(112, named.len() as int),
            forall|j: int| 0 <= j < i ==> #[trigger] out@[80 + j] == if j < device.len() { device@[j] } else { 0 },
        decreases 32 - i,
    { out.set(80 + i, if i < device.len() { device[i] } else { 0 }); i += 1; }
    proof {
        assert(out@.take(16) =~= header.take(16));
        assert forall|j: int| 112 <= j < out.len() implies #[trigger] out@[j] == #[trigger] header[j] by {
            assert(out@.subrange(112, out.len() as int)[j - 112]
                == named.subrange(112, named.len() as int)[j - 112]);
            assert(named.subrange(80, named.len() as int)[j - 80]
                == header.subrange(80, header.len() as int)[j - 80]);
        }
        assert(out@.subrange(112, out.len() as int) =~= header.subrange(112, header.len() as int));
        assert forall|j: int| 0 <= j < 16 implies #[trigger] out@[j] == #[trigger] header[j] by {
            assert(out@.take(16)[j] == header.take(16)[j]);
        }
        assert(bytes::le32(out@, 0) == bytes::le32(header, 0));
        assert(bytes::le32(out@, 0) == MAGIC);
        assert(out@[4] == header[4] && out@[5] == header[5]
            && out@[6] == header[6] && out@[7] == header[7]);
        assert(bytes::le32(out@, 4) == bytes::le32(header, 4));
        assert(bytes::le32(out@, 4) == sequence);
        assert(out@[8] == header[8] && out@[9] == header[9]
            && out@[10] == header[10] && out@[11] == header[11]);
        assert(out@[12] == header[12] && out@[13] == header[13]
            && out@[14] == header[14] && out@[15] == header[15]);
        assert(bytes::le32(out@, 8) == bytes::le32(header, 8));
        assert(bytes::le32(out@, 12) == bytes::le32(header, 12));
        assert(disk_time(out@) == disk_time(header));
        assert(disk_time(out@) == wall_time);
        assert(out@[112] == header[112] && out@[113] == header[113]);
        assert(bytes::le16(out@, 112) == bytes::le16(header, 112));
        assert(bytes::le16(out@, 112) == interval);
        prefix_preserves_padded_name(named, out@, node@, 16, 64, 80);
        assert(out@.subrange(114, 1020) == raw@.subrange(114, 1020));
        assert(out@.subrange(1020, out.len() as int) == raw@.subrange(1020, raw.len() as int));
    }
    let ghost body = out@;
    proof {
        vstd::seq::lemma_seq_subrange_composition(raw@, 1020, raw.len() as int, 0, 4);
        vstd::seq::lemma_seq_subrange_composition(body, 1020, body.len() as int, 0, 4);
        vstd::seq::lemma_seq_subrange_composition(raw@, 1020, raw.len() as int, 4, raw.len() as int - 1020);
        vstd::seq::lemma_seq_subrange_composition(body, 1020, body.len() as int, 4, body.len() as int - 1020);
        assert(body.subrange(1020, 1024) == raw@.subrange(1020, 1024));
        assert(body.subrange(1024, body.len() as int) == raw@.subrange(1024, raw.len() as int));
        assert forall|j: int| 0 <= j < 32 implies #[trigger] body[80 + j]
            == if j < device.len() { device@[j] } else { 0u8 } by {
            assert(body[80 + j] == out@[80 + j]);
        }
        assert(rewritten(raw@, body, sequence, wall_time, node@, device@, interval, seed, false));
    }
    if metadata {
        let checksum = crc::crc32c(seed, &out[..CHECKSUM_OFFSET]);
        proof { assert(out@.subrange(0, 1020) =~= body.take(1020)); }
        if !write32(&mut out, CHECKSUM_OFFSET, checksum) { return Err(Error::Geometry); }
        proof {
            assert(out@.take(1020) =~= body.take(1020));
            assert(out@.subrange(1024, out.len() as int) =~= body.subrange(1024, body.len() as int));
            assert(bytes::le32(out@, 1020) == crate::mmp::checksum(out@, seed));
        }
    }
    proof {
        assert(out@.take(1020) =~= body.take(1020));
        assert(out@.subrange(1024, out.len() as int) =~= body.subrange(1024, body.len() as int));
        checksum_sealing_preserves_prepared_record(raw@, body, out@, sequence, wall_time,
            node@, device@, interval, seed, metadata);
    }
    Ok(out)
}

pub fn encode(block_bytes: usize, sequence: u32, wall_time: u64,
    node: &[u8], device: &[u8], interval: u16, seed: u32, metadata: bool)
    -> Result<Vec<u8>, Error>
{
    if !block_size::valid(block_bytes) || block_bytes < STRUCT_BYTES { return Err(Error::Geometry); }
    let mut raw = Vec::new(); let mut i = 0usize;
    while i < block_bytes
        invariant i <= block_bytes, raw.len() == i,
        decreases block_bytes - i,
    { raw.push(0); i += 1; }
    rewrite(&raw, sequence, wall_time, node, device, interval, seed, metadata)
}

#[verifier::ext_equal]
pub struct ProtectorView {
    pub raw: Seq<u8>, pub block: u64, pub seed: u32, pub metadata: bool,
    pub node: Seq<u8>, pub device: Seq<u8>, pub sequence: u32, pub chosen: u32,
    pub update_seconds: u16, pub check_seconds: u16, pub wait: u64,
    pub deadline: u64, pub next_update: u64, pub last_clock: u64,
    pub claiming: bool, pub stage: Stage, pub next_request: u64,
}
pub open spec fn fixed_parameters(a: ProtectorView, b: ProtectorView) -> bool {
    a.block == b.block && a.seed == b.seed && a.metadata == b.metadata
        && a.node == b.node && a.device == b.device && a.chosen == b.chosen
        && a.update_seconds == b.update_seconds && a.wait == b.wait
}
pub open spec fn ready_result(v: ProtectorView, now: u64) -> ProtectorView {
    if now as nat + v.check_seconds as nat > u64::MAX || now as nat + v.update_seconds as nat > u64::MAX {
        ProtectorView { stage: Stage::Faulted, ..v }
    } else {
        ProtectorView { deadline: (now + v.check_seconds) as u64,
            next_update: (now + v.update_seconds) as u64, last_clock: now, stage: Stage::Ready, ..v }
    }
}
pub open spec fn write_result(v: ProtectorView, image: Seq<u8>, sequence: u32, clean: bool,
    completion: Completion, started: u64, now: u64) -> ProtectorView
{
    let attempted = ProtectorView { raw: image, ..v };
    if matches!(completion, Completion::Failed) || v.stage == Stage::Faulted
        || now < started || now < v.last_clock || !v.claiming && !clean && now > v.deadline {
        ProtectorView { stage: Stage::Faulted, ..attempted }
    } else {
        let latency = now - started;
        ProtectorView { sequence, last_clock: now,
            check_seconds: if latency >= 150 { 300u16 } else if latency < 3 { 5u16 } else { (latency * 2) as u16 },
            stage: if clean { Stage::NeedCleanFlush } else { Stage::NeedFlush }, ..attempted }
    }
}
pub open spec fn flush_result(v: ProtectorView, clean: bool, completion: Completion, started: u64, now: u64) -> ProtectorView {
    if matches!(completion, Completion::Failed) || v.stage == Stage::Faulted
        || now < started || now < v.last_clock || !v.claiming && !clean && now > v.deadline {
        ProtectorView { stage: Stage::Faulted, ..v }
    } else {
        let clocked = ProtectorView { last_clock: now, ..v };
        if clean { ProtectorView { stage: Stage::Stopped, ..clocked } }
        else if v.claiming {
            if now as nat + v.wait as nat > u64::MAX { ProtectorView { stage: Stage::Faulted, ..clocked } }
            else { ProtectorView { deadline: (now + v.wait) as u64, stage: Stage::WaitClaim, ..clocked } }
        } else { ready_result(clocked, now) }
    }
}
pub open spec fn quiesce_result(v: ProtectorView, completion: Completion, started: u64, now: u64) -> ProtectorView {
    if matches!(completion, Completion::Failed) || v.stage == Stage::Faulted || now < started || now < v.last_clock {
        ProtectorView { stage: Stage::Faulted, ..v }
    } else { ProtectorView { last_clock: now, stage: Stage::NeedStopRead, ..v } }
}


// These histories describe software commands offered to the adapter and the
// reports supplied by that adapter. They do not prove freshness, persistence,
// quiescence, clock provenance, or physical ownership.
#[verifier::ext_equal]
pub struct Origin {
    pub raw: Seq<u8>, pub physical: u64, pub first_data: u64, pub fs_blocks: u64,
    pub seed: u32, pub metadata: bool, pub update: u16, pub chosen: u32,
    pub now: u64, pub node: Seq<u8>, pub device: Seq<u8>,
}
pub open spec fn record_error(raw: Seq<u8>, seed: u32, metadata: bool) -> Option<Error> {
    if !block_size::accepted(raw.len()) || raw.len() < 1024 { Some(Error::Geometry) }
    else if bytes::le32(raw, 0) != MAGIC { Some(Error::Magic) }
    else if metadata && bytes::le32(raw, 1020) != checksum(raw, seed) { Some(Error::Checksum) }
    else { None }
}
pub open spec fn initial_check(o: Origin) -> u16 {
    let observed = bytes::le16(o.raw, 112) as u16;
    let maximum = if observed > o.update { observed } else { o.update };
    if maximum < MIN_CHECK_SECONDS { MIN_CHECK_SECONDS } else { maximum }
}
pub open spec fn modeled_wait(check: u16) -> u64 {
    if (check as nat) * 2 + 1 < check as nat + 60 { ((check as nat) * 2 + 1) as u64 }
    else { (check as nat + 60) as u64 }
}
pub open spec fn initial_delay(o: Origin) -> u64 {
    if bytes::le32(o.raw, 4) == SEQ_CLEAN { initial_check(o) as u64 }
    else { modeled_wait(initial_check(o)) }
}
pub open spec fn valid_origin(o: Origin) -> bool {
    &&& o.first_data <= o.physical < o.fs_blocks
    &&& o.node.len() <= 64 && o.device.len() <= 32
    &&& o.chosen <= SEQ_MAX && o.update > 0
    &&& record_error(o.raw, o.seed, o.metadata).is_none()
    &&& (bytes::le32(o.raw, 4) == SEQ_CLEAN
        || bytes::le32(o.raw, 4) <= SEQ_MAX && bytes::le32(o.raw, 4) != o.chosen)
    &&& o.now as nat + initial_delay(o) as nat <= u64::MAX
}
pub open spec fn initial_view(o: Origin) -> ProtectorView {
    ProtectorView { raw: o.raw, block: o.physical, seed: o.seed, metadata: o.metadata,
        node: o.node, device: o.device, sequence: bytes::le32(o.raw, 4) as u32, chosen: o.chosen,
        update_seconds: o.update, check_seconds: initial_check(o), wait: modeled_wait(initial_check(o)),
        deadline: (o.now as nat + initial_delay(o) as nat) as u64, next_update: o.now, last_clock: o.now,
        claiming: true, stage: if bytes::le32(o.raw, 4) == SEQ_CLEAN { Stage::NeedWrite } else { Stage::WaitOld },
        next_request: 1 }
}
pub open spec fn faulted(v: ProtectorView) -> ProtectorView {
    ProtectorView { stage: Stage::Faulted, ..v }
}
pub open spec fn read_result(v: ProtectorView, kind: ReadKind, started: u64,
    media: Option<Seq<u8>>, now: u64) -> (ProtectorView, Result<(), Error>)
{
    if v.stage == Stage::Faulted { (v, Err(Error::Phase)) }
    else if now < started || now < v.last_clock { (faulted(v), Err(Error::Clock)) }
    else {
        match media {
            None => (faulted(v), Err(Error::Io)),
            Some(raw) => {
                if raw.len() != v.raw.len() { (faulted(v), Err(Error::Geometry)) }
                else {
                    match record_error(raw, v.seed, v.metadata) {
                        Some(error) => (faulted(v), Err(error)),
                        None => {
                            if bytes::le32(raw, 4) != v.sequence
                                || kind != ReadKind::OldObservation
                                    && (raw.len() < 80 || v.raw.len() < 80
                                        || raw.subrange(16, 80) != v.raw.subrange(16, 80)) {
                                (faulted(v), Err(Error::Busy))
                            } else {
                                let clocked = ProtectorView { last_clock: now, ..v };
                                if kind == ReadKind::ClaimObservation {
                                    let next = ready_result(ProtectorView { claiming: false, ..clocked }, now);
                                    (next, if next.stage == Stage::Faulted { Err(Error::Clock) } else { Ok(()) })
                                } else {
                                    let copied = if kind == ReadKind::OldObservation {
                                        ProtectorView { raw, ..clocked }
                                    } else { clocked };
                                    if now as nat + v.check_seconds as nat > u64::MAX {
                                        (faulted(copied), Err(Error::Clock))
                                    } else {
                                        (ProtectorView { deadline: (now as nat + v.check_seconds as nat) as u64,
                                            stage: if kind == ReadKind::StopObservation { Stage::NeedCleanWrite }
                                                else { Stage::NeedWrite }, ..copied }, Ok(()))
                                    }
                                }
                            }
                        },
                    }
                }
            },
        }
    }
}

pub enum CommandView {
    Read { block: u64, kind: ReadKind, request: u64, started: u64 },
    Write { block: u64, image: Seq<u8>, sequence: u32, clean: bool, request: u64, started: u64 },
    Flush { clean: bool, request: u64, started: u64 },
    Quiesce { request: u64, started: u64 },
}
#[verifier::ext_equal]
pub struct ProtocolView { pub controller: ProtectorView, pub pending: Option<CommandView> }
pub enum DispatchChoice {
    Refuse(Error), Read(ReadKind), Write { sequence: u32, clean: bool }, Flush(bool), Quiesce,
}
pub open spec fn modeled_next_sequence(sequence: u32) -> u32 {
    if sequence >= SEQ_MAX { 1u32 } else { (sequence + 1) as u32 }
}
pub open spec fn dispatch_choice(v: ProtectorView, now: u64) -> DispatchChoice {
    if now < v.last_clock { DispatchChoice::Refuse(Error::Clock) }
    else if v.next_request == u64::MAX { DispatchChoice::Refuse(Error::Exhausted) }
    else if (v.stage == Stage::NeedWrite || v.stage == Stage::NeedCleanWrite) && now > v.deadline {
        DispatchChoice::Read(if v.stage == Stage::NeedCleanWrite { ReadKind::StopObservation }
            else if v.claiming { ReadKind::OldObservation } else { ReadKind::HeartbeatObservation })
    } else {
        match v.stage {
            Stage::WaitOld | Stage::WaitClaim | Stage::NeedStopRead => {
                if v.stage != Stage::NeedStopRead && now < v.deadline { DispatchChoice::Refuse(Error::Wait) }
                else { DispatchChoice::Read(if v.stage == Stage::WaitOld { ReadKind::OldObservation }
                    else if v.stage == Stage::WaitClaim { ReadKind::ClaimObservation } else { ReadKind::StopObservation }) }
            },
            Stage::Ready => {
                if now < v.next_update { DispatchChoice::Refuse(Error::Wait) }
                else if now > v.deadline { DispatchChoice::Read(ReadKind::HeartbeatObservation) }
                else { DispatchChoice::Write { sequence: if v.claiming { v.chosen } else { modeled_next_sequence(v.sequence) }, clean: false } }
            },
            Stage::NeedWrite => DispatchChoice::Write {
                sequence: if v.claiming { v.chosen } else { modeled_next_sequence(v.sequence) }, clean: false },
            Stage::NeedCleanWrite => DispatchChoice::Write { sequence: SEQ_CLEAN, clean: true },
            Stage::NeedFlush | Stage::NeedCleanFlush => DispatchChoice::Flush(v.stage == Stage::NeedCleanFlush),
            Stage::Quiesce => DispatchChoice::Quiesce,
            Stage::Stopped | Stage::Faulted => DispatchChoice::Refuse(Error::Phase),
        }
    }
}
pub open spec fn offered_owner(v: ProtectorView, now: u64) -> ProtectorView {
    ProtectorView { last_clock: now, next_request: (v.next_request + 1) as u64,
        stage: if v.stage == Stage::Ready && now <= v.deadline { Stage::NeedWrite } else { v.stage }, ..v }
}
pub open spec fn rewrite_error_bytes(raw: Seq<u8>, node: Seq<u8>, device: Seq<u8>) -> Option<Error> {
    if !block_size::accepted(raw.len()) || raw.len() < 1024 { Some(Error::Geometry) }
    else if node.len() > 64 || device.len() > 32 { Some(Error::Name) }
    else { None }
}
pub open spec fn rewrite_error(v: ProtectorView) -> Option<Error> {
    rewrite_error_bytes(v.raw, v.node, v.device)
}
pub open spec fn dispatch_relation(v: ProtectorView, now: u64, wall: u64,
    after: ProtocolView, error: Option<Error>) -> bool
{
    match dispatch_choice(v, now) {
        DispatchChoice::Refuse(expected) =>
            error == Some(expected) && after.pending.is_none()
            && after.controller == if now < v.last_clock { faulted(v) }
                else if v.next_request == u64::MAX { v }
                else { ProtectorView { last_clock: now, ..v } },
        DispatchChoice::Read(kind) =>
            error.is_none() && after.controller == offered_owner(v, now)
            && after.pending == Some(CommandView::Read { block: v.block, kind, request: v.next_request, started: now }),
        DispatchChoice::Write { sequence, clean } => {
            let owner = offered_owner(v, now);
            match rewrite_error(owner) {
                Some(expected) => error == Some(expected) && after.pending.is_none()
                    && after.controller == faulted(owner),
                None => error.is_none() && after.controller == owner
                    && (match after.pending {
                        Some(CommandView::Write { block, image, sequence: actual, clean: actual_clean, request, started }) =>
                            block == v.block && actual == sequence && actual_clean == clean
                            && request == v.next_request && started == now
                            && rewritten(v.raw, image, sequence, wall, v.node, v.device, v.check_seconds, v.seed, v.metadata),
                        _ => false,
                    }),
            }
        },
        DispatchChoice::Flush(clean) =>
            error.is_none() && after.controller == offered_owner(v, now)
            && after.pending == Some(CommandView::Flush { clean, request: v.next_request, started: now }),
        DispatchChoice::Quiesce =>
            error.is_none() && after.controller == offered_owner(v, now)
            && after.pending == Some(CommandView::Quiesce { request: v.next_request, started: now }),
    }
}

pub enum Action {
    Stop, AbortAvailable, AbortPending,
    Dispatch { now: u64, wall: u64, error: Option<Error> },
    ReadReport { media: Option<Seq<u8>>, now: u64, status: Result<(), Error> },
    WriteReport { completion: Completion, now: u64 },
    FlushReport { completion: Completion, now: u64 },
    QuiesceReport { completion: Completion, now: u64 },
}
#[verifier::ext_equal]
pub struct ProtocolEvent { pub before: ProtocolView, pub after: ProtocolView, pub action: Action }
pub open spec fn permitted(event: ProtocolEvent) -> bool {
    let a = event.before;
    let b = event.after;
    match event.action {
        Action::Stop => a.pending.is_none() && a.controller.stage == Stage::Ready
            && b.pending.is_none() && b.controller == (ProtectorView { stage: Stage::Quiesce, ..a.controller }),
        Action::AbortAvailable => a.pending.is_none() && b.pending.is_none() && b.controller == faulted(a.controller),
        Action::AbortPending => a.pending.is_some() && b.pending == a.pending && b.controller == faulted(a.controller),
        Action::Dispatch { now, wall, error } => a.pending.is_none() && dispatch_relation(a.controller, now, wall, b, error),
        Action::ReadReport { media, now, status } => b.pending.is_none() && (match a.pending {
            Some(CommandView::Read { block, kind, request, started }) =>
                b.controller == read_result(a.controller, kind, started, media, now).0
                    && status == read_result(a.controller, kind, started, media, now).1,
            _ => false,
        }),
        Action::WriteReport { completion, now } => b.pending.is_none() && (match a.pending {
            Some(CommandView::Write { block, image, sequence, clean, request, started }) =>
                b.controller == write_result(a.controller, image, sequence, clean, completion, started, now),
            _ => false,
        }),
        Action::FlushReport { completion, now } => b.pending.is_none() && (match a.pending {
            Some(CommandView::Flush { clean, request, started }) =>
                b.controller == flush_result(a.controller, clean, completion, started, now),
            _ => false,
        }),
        Action::QuiesceReport { completion, now } => b.pending.is_none() && (match a.pending {
            Some(CommandView::Quiesce { request, started }) =>
                b.controller == quiesce_result(a.controller, completion, started, now),
            _ => false,
        }),
    }
}
pub open spec fn initial_point(o: Origin) -> ProtocolView {
    ProtocolView { controller: initial_view(o), pending: None }
}
pub open spec fn history_tip(o: Origin, h: Seq<ProtocolEvent>) -> ProtocolView {
    if h.len() == 0 { initial_point(o) } else { h.last().after }
}
pub closed spec fn reachable(o: Origin, h: Seq<ProtocolEvent>, point: ProtocolView) -> bool {
    &&& valid_origin(o)
    &&& point == history_tip(o, h)
    &&& h.len() > 0 ==> h[0].before == initial_point(o)
    &&& forall|i: int| 0 <= i < h.len() ==> #[trigger] permitted(h[i])
    &&& forall|i: int| 0 <= i < h.len() - 1 ==> h[i].after == h[i + 1].before
}
proof fn append_reachable(o: Origin, h: Seq<ProtocolEvent>, event: ProtocolEvent)
    requires reachable(o, h, event.before), permitted(event),
    ensures reachable(o, h.push(event), event.after),
{
    reveal(reachable);
    let next = h.push(event);
    assert forall|i: int| 0 <= i < next.len() implies #[trigger] permitted(next[i]) by {
        if i < h.len() { assert(next[i] == h[i]); } else { assert(i == h.len()); }
    }
    assert forall|i: int| 0 <= i < next.len() - 1 implies next[i].after == next[i + 1].before by {
        if i < h.len() - 1 { assert(next[i] == h[i] && next[i + 1] == h[i + 1]); }
        else { assert(i == h.len() - 1); assert(h.len() > 0); }
    }
}

struct State {
    raw: Vec<u8>, block: u64, seed: u32, metadata: bool,
    node: Vec<u8>, device: Vec<u8>, sequence: u32, chosen: u32,
    update_seconds: u16, check_seconds: u16, wait: u64,
    deadline: u64, next_update: u64, last_clock: u64,
    claiming: bool, stage: Stage, next_request: u64,
}
struct StateReadPending { owner: State, kind: ReadKind, request: u64, started: u64 }
struct StateWritePending { owner: State, image: Vec<u8>, sequence: u32, clean: bool, request: u64, started: u64 }
struct StateFlushPending { owner: State, clean: bool, request: u64, started: u64 }
struct StateQuiescePending { owner: State, request: u64, started: u64 }
enum StateRequest {
    Read(StateReadPending), Write(StateWritePending), Flush(StateFlushPending), Quiesce(StateQuiescePending),
}

impl State {
    pub closed spec fn view(&self) -> ProtectorView {
        ProtectorView { raw: self.raw@, block: self.block, seed: self.seed, metadata: self.metadata,
            node: self.node@, device: self.device@, sequence: self.sequence, chosen: self.chosen,
            update_seconds: self.update_seconds, check_seconds: self.check_seconds, wait: self.wait,
            deadline: self.deadline, next_update: self.next_update, last_clock: self.last_clock,
            claiming: self.claiming, stage: self.stage, next_request: self.next_request }
    }
    fn state_stage(&self) -> (r: Stage) ensures r == self.view().stage { self.stage }
    fn state_sequence(&self) -> (r: u32) ensures r == self.view().sequence { self.sequence }
    fn state_block(&self) -> (r: u64) ensures r == self.view().block { self.block }
    fn state_deadlines(&self) -> (r: (u64, u64)) ensures r == (self.view().next_update, self.view().deadline) { (self.next_update, self.deadline) }
    fn state_intended_bytes(&self) -> (r: &[u8]) ensures r@ == self.view().raw { &self.raw }
    fn state_stop(mut self) -> (r: Result<Self, (Self, Error)>)
        ensures match r {
            Ok(owner) => self.view().stage == Stage::Ready
                && owner.view() == (ProtectorView { stage: Stage::Quiesce, ..self.view() }),
            Err((owner, error)) => owner.view() == self.view() && self.view().stage != Stage::Ready && error == Error::Phase,
        },
    {
        if !matches!(self.stage, Stage::Ready) { return Err((self, Error::Phase)); }
        self.stage = Stage::Quiesce; Ok(self)
    }
    fn state_abort(mut self) -> (r: Self)
        ensures r.view() == (ProtectorView { stage: Stage::Faulted, ..self.view() }),
    { self.stage = Stage::Faulted; self }
    fn state_ready(&mut self, now: u64) -> (r: bool)
        ensures final(self).view() == ready_result(old(self).view(), now),
            r == (now as nat + old(self).view().check_seconds as nat <= u64::MAX
                && now as nat + old(self).view().update_seconds as nat <= u64::MAX),
    {
        let end = match due(now, self.check_seconds as u64) {
            Some(value) => value, None => { self.stage = Stage::Faulted; return false; }
        };
        let next = match due(now, self.update_seconds as u64) {
            Some(value) => value, None => { self.stage = Stage::Faulted; return false; }
        };
        self.deadline = end; self.next_update = next; self.last_clock = now;
        self.stage = Stage::Ready; true
    }

    fn state_dispatch(mut self, monotonic_now: u64, wall_time: u64) -> (r: Result<StateRequest, (Self, Error)>)
        ensures match r {
            Ok(command) => dispatch_relation(self.view(), monotonic_now, wall_time, command.state_point(), None),
            Err((owner, error)) => dispatch_relation(self.view(), monotonic_now, wall_time,
                ProtocolView { controller: owner.view(), pending: None }, Some(error)),
        },
    {
        if monotonic_now < self.last_clock {
            self.stage = Stage::Faulted; return Err((self, Error::Clock));
        }
        if self.next_request == u64::MAX { return Err((self, Error::Exhausted)); }
        self.last_clock = monotonic_now;
        let request = self.next_request;
        if (matches!(self.stage, Stage::NeedWrite) || matches!(self.stage, Stage::NeedCleanWrite))
            && monotonic_now > self.deadline {
            let kind = if matches!(self.stage, Stage::NeedCleanWrite) { ReadKind::StopObservation }
                else if self.claiming { ReadKind::OldObservation } else { ReadKind::HeartbeatObservation };
            self.next_request += 1;
            return Ok(StateRequest::Read(StateReadPending { owner: self, kind, request, started: monotonic_now }));
        }
        match self.stage {
            Stage::WaitOld | Stage::WaitClaim | Stage::NeedStopRead => {
                if !matches!(self.stage, Stage::NeedStopRead) && monotonic_now < self.deadline { return Err((self, Error::Wait)); }
                let kind = if matches!(self.stage, Stage::WaitOld) { ReadKind::OldObservation }
                    else if matches!(self.stage, Stage::WaitClaim) { ReadKind::ClaimObservation }
                    else { ReadKind::StopObservation };
                self.next_request += 1;
                return Ok(StateRequest::Read(StateReadPending { owner: self, kind, request, started: monotonic_now }));
            },
            Stage::Ready => {
                if monotonic_now < self.next_update { return Err((self, Error::Wait)); }
                if monotonic_now > self.deadline {
                    self.next_request += 1;
                    return Ok(StateRequest::Read(StateReadPending { owner: self, kind: ReadKind::HeartbeatObservation,
                        request, started: monotonic_now }));
                }
                self.stage = Stage::NeedWrite;
            },
            Stage::NeedWrite | Stage::NeedFlush | Stage::Quiesce | Stage::NeedCleanWrite | Stage::NeedCleanFlush => {},
            Stage::Stopped | Stage::Faulted => { return Err((self, Error::Phase)); },
        }
        self.next_request += 1;
        match self.stage {
            Stage::NeedWrite | Stage::NeedCleanWrite => {
                let clean = matches!(self.stage, Stage::NeedCleanWrite);
                let sequence = if clean { SEQ_CLEAN } else if self.claiming { self.chosen } else { next_sequence(self.sequence) };
                let image = match rewrite(&self.raw, sequence, wall_time, &self.node, &self.device,
                    self.check_seconds, self.seed, self.metadata) {
                    Ok(value) => value, Err(error) => { self.stage = Stage::Faulted; return Err((self, error)); }
                };
                Ok(StateRequest::Write(StateWritePending { owner: self, image, sequence, clean, request, started: monotonic_now }))
            },
            Stage::NeedFlush | Stage::NeedCleanFlush => {
                let clean = matches!(self.stage, Stage::NeedCleanFlush);
                Ok(StateRequest::Flush(StateFlushPending { owner: self, clean, request, started: monotonic_now }))
            },
            Stage::Quiesce => Ok(StateRequest::Quiesce(StateQuiescePending { owner: self, request, started: monotonic_now })),
            _ => { self.stage = Stage::Faulted; Err((self, Error::Phase)) },
        }
    }
}

impl StateReadPending {
    pub closed spec fn read_owner(&self) -> ProtectorView { self.owner.view() }
    pub closed spec fn read_started(&self) -> u64 { self.started }
    pub closed spec fn read_variant(&self) -> ReadKind { self.kind }
    pub closed spec fn read_serial(&self) -> u64 { self.request }
    fn state_read_block(&self) -> (r: u64) ensures r == self.read_owner().block { self.owner.block }
    fn state_read_request(&self) -> (r: u64) ensures r == self.read_serial() { self.request }
    fn state_read_kind(&self) -> (r: ReadKind) ensures r == self.read_variant() { self.kind }
    fn state_abort_read(mut self) -> (r: Self)
        ensures r.read_owner() == (ProtectorView { stage: Stage::Faulted, ..self.read_owner() }), r.read_started() == self.read_started(), r.read_variant() == self.read_variant(), r.read_serial() == self.read_serial(),
    { self.owner.stage = Stage::Faulted; self }
    fn state_finish_read(self, bytes: Option<&[u8]>, monotonic_now: u64) -> (r: (State, Result<(), Error>))
        ensures r.0.view() == read_result(self.read_owner(), self.read_variant(), self.read_started(),
                match bytes { Some(raw) => Some(raw@), None => None }, monotonic_now).0,
            r.1 == read_result(self.read_owner(), self.read_variant(), self.read_started(),
                match bytes { Some(raw) => Some(raw@), None => None }, monotonic_now).1,
            fixed_parameters(self.read_owner(), r.0.view()),
            r.0.view().sequence == self.read_owner().sequence,
            r.0.view().next_request == self.read_owner().next_request,
            match r.1 {
                Ok(()) => monotonic_now >= self.read_started() && monotonic_now >= self.read_owner().last_clock
                    && r.0.view().last_clock == monotonic_now
                    && (match bytes { Some(media) =>
                        block_size::accepted(media.len() as nat) && media.len() == self.read_owner().raw.len()
                        && bytes::le32(media@, 0) == MAGIC && bytes::le32(media@, 4) == self.read_owner().sequence
                        && (self.read_owner().metadata ==> bytes::le32(media@, 1020) == checksum(media@, self.read_owner().seed))
                        && (self.read_variant() != ReadKind::OldObservation ==> media@.subrange(16, 80) == self.read_owner().raw.subrange(16, 80))
                        && r.0.view().raw == if self.read_variant() == ReadKind::OldObservation { media@ } else { self.read_owner().raw },
                        None => false })
                    && r.0.view().stage == match self.read_variant() {
                        ReadKind::ClaimObservation => Stage::Ready,
                        ReadKind::OldObservation | ReadKind::HeartbeatObservation => Stage::NeedWrite,
                        ReadKind::StopObservation => Stage::NeedCleanWrite,
                    }
                    && (self.read_variant() == ReadKind::ClaimObservation ==> !r.0.view().claiming),
                Err(_) => r.0.view().stage == Stage::Faulted,
            },
    {
        let StateReadPending { mut owner, kind, request: _, started } = self;
        if matches!(owner.stage, Stage::Faulted) { return (owner, Err(Error::Phase)); }
        if monotonic_now < started || monotonic_now < owner.last_clock {
            owner.stage = Stage::Faulted; return (owner, Err(Error::Clock));
        }
        let raw = match bytes {
            Some(value) => value, None => { owner.stage = Stage::Faulted; return (owner, Err(Error::Io)); }
        };
        if raw.len() != owner.raw.len() { owner.stage = Stage::Faulted; return (owner, Err(Error::Geometry)); }
        let seen = match parse(raw, owner.seed, owner.metadata) {
            Ok(value) => value, Err(error) => { owner.stage = Stage::Faulted; return (owner, Err(error)); }
        };
        if seen.sequence != owner.sequence {
            owner.stage = Stage::Faulted; return (owner, Err(Error::Busy));
        }
        if !matches!(kind, ReadKind::OldObservation) {
            if raw.len() < 80 || owner.raw.len() < 80
                || !bytes::equal(&raw[16..80], &owner.raw[16..80]) {
                owner.stage = Stage::Faulted; return (owner, Err(Error::Busy));
            }
        }
        owner.last_clock = monotonic_now;
        match kind {
            ReadKind::OldObservation => {
                owner.raw = seen.raw;
                owner.deadline = match due(monotonic_now, owner.check_seconds as u64) {
                    Some(value) => value, None => { owner.stage = Stage::Faulted; return (owner, Err(Error::Clock)); }
                };
                owner.stage = Stage::NeedWrite;
            },
            ReadKind::ClaimObservation => {
                owner.claiming = false;
                if !owner.state_ready(monotonic_now) { return (owner, Err(Error::Clock)); }
            },
            ReadKind::HeartbeatObservation | ReadKind::StopObservation => {
                owner.deadline = match due(monotonic_now, owner.check_seconds as u64) {
                    Some(value) => value, None => { owner.stage = Stage::Faulted; return (owner, Err(Error::Clock)); }
                };
                owner.stage = if matches!(kind, ReadKind::StopObservation) { Stage::NeedCleanWrite } else { Stage::NeedWrite };
            },
        }
        (owner, Ok(()))
    }
}
impl StateWritePending {
    pub closed spec fn write_owner(&self) -> ProtectorView { self.owner.view() }
    pub closed spec fn write_image(&self) -> Seq<u8> { self.image@ }
    pub closed spec fn write_sequence(&self) -> u32 { self.sequence }
    pub closed spec fn write_clean(&self) -> bool { self.clean }
    pub closed spec fn write_started(&self) -> u64 { self.started }
    pub closed spec fn write_serial(&self) -> u64 { self.request }
    fn state_write_block(&self) -> (r: u64) ensures r == self.write_owner().block { self.owner.block }
    fn state_write_request(&self) -> (r: u64) ensures r == self.write_serial() { self.request }
    fn state_write_bytes(&self) -> (r: &[u8]) ensures r@ == self.write_image() { &self.image }
    fn state_abort_write(mut self) -> (r: Self)
        ensures r.write_owner() == (ProtectorView { stage: Stage::Faulted, ..self.write_owner() }), r.write_image() == self.write_image(), r.write_sequence() == self.write_sequence(),
            r.write_clean() == self.write_clean(), r.write_started() == self.write_started(), r.write_serial() == self.write_serial(),
    { self.owner.stage = Stage::Faulted; self }
    fn state_finish_write(self, completion: Completion, monotonic_now: u64) -> (r: State)
        ensures r.view() == write_result(self.write_owner(), self.write_image(), self.write_sequence(),
            self.write_clean(), completion, self.write_started(), monotonic_now),
            r.view().raw == self.write_image(), fixed_parameters(self.write_owner(), r.view()),
    {
        let StateWritePending { mut owner, image, sequence, clean, request: _, started } = self;
        // Keep the immutable attempted image even on failure; failure is not
        // evidence that the issued physical write could not have persisted.
        owner.raw = image;
        if matches!(completion, Completion::Failed) || matches!(owner.stage, Stage::Faulted)
            || monotonic_now < started || monotonic_now < owner.last_clock {
            owner.stage = Stage::Faulted; return owner;
        }
        if !owner.claiming && !clean && monotonic_now > owner.deadline {
            owner.stage = Stage::Faulted; return owner;
        }
        let latency = monotonic_now - started;
        owner.check_seconds = if latency >= 150 { MAX_CHECK_SECONDS }
            else if latency < 3 { MIN_CHECK_SECONDS } else { (latency * 2) as u16 };
        owner.sequence = sequence; owner.last_clock = monotonic_now;
        owner.stage = if clean { Stage::NeedCleanFlush } else { Stage::NeedFlush };
        owner
    }
}
impl StateFlushPending {
    pub closed spec fn flush_owner(&self) -> ProtectorView { self.owner.view() }
    pub closed spec fn flush_clean(&self) -> bool { self.clean }
    pub closed spec fn flush_started(&self) -> u64 { self.started }
    pub closed spec fn flush_serial(&self) -> u64 { self.request }
    fn state_flush_request(&self) -> (r: u64) ensures r == self.flush_serial() { self.request }
    fn state_abort_flush(mut self) -> (r: Self)
        ensures r.flush_owner() == (ProtectorView { stage: Stage::Faulted, ..self.flush_owner() }), r.flush_clean() == self.flush_clean(), r.flush_started() == self.flush_started(), r.flush_serial() == self.flush_serial(),
    { self.owner.stage = Stage::Faulted; self }
    fn state_finish_flush(self, completion: Completion, monotonic_now: u64) -> (r: State)
        ensures r.view() == flush_result(self.flush_owner(), self.flush_clean(), completion, self.flush_started(), monotonic_now),
            fixed_parameters(self.flush_owner(), r.view()), r.view().raw == self.flush_owner().raw,
    {
        let StateFlushPending { mut owner, clean, request: _, started } = self;
        if matches!(completion, Completion::Failed) || matches!(owner.stage, Stage::Faulted)
            || monotonic_now < started || monotonic_now < owner.last_clock {
            owner.stage = Stage::Faulted; return owner;
        }
        if !owner.claiming && !clean && monotonic_now > owner.deadline {
            owner.stage = Stage::Faulted; return owner;
        }
        owner.last_clock = monotonic_now;
        if clean { owner.stage = Stage::Stopped; }
        else if owner.claiming {
            owner.deadline = match due(monotonic_now, owner.wait) {
                Some(value) => value, None => { owner.stage = Stage::Faulted; return owner; }
            };
            owner.stage = Stage::WaitClaim;
        } else { let _ = owner.state_ready(monotonic_now); }
        owner
    }
}
impl StateQuiescePending {
    pub closed spec fn quiesce_owner(&self) -> ProtectorView { self.owner.view() }
    pub closed spec fn quiesce_started(&self) -> u64 { self.started }
    pub closed spec fn quiesce_serial(&self) -> u64 { self.request }
    fn state_quiesce_request(&self) -> (r: u64) ensures r == self.quiesce_serial() { self.request }
    fn state_abort_quiesce(mut self) -> (r: Self)
        ensures r.quiesce_owner() == (ProtectorView { stage: Stage::Faulted, ..self.quiesce_owner() }), r.quiesce_started() == self.quiesce_started(), r.quiesce_serial() == self.quiesce_serial(),
    { self.owner.stage = Stage::Faulted; self }
    /// Succeeded means filesystem operations and their I/O are quiescent,
    /// established by the runtime adapter before writing the clean marker.
    fn state_finish_quiesce(self, completion: Completion, monotonic_now: u64) -> (r: State)
        ensures r.view() == quiesce_result(self.quiesce_owner(), completion, self.quiesce_started(), monotonic_now),
            fixed_parameters(self.quiesce_owner(), r.view()), r.view().raw == self.quiesce_owner().raw,
    {
        let StateQuiescePending { mut owner, request: _, started } = self;
        if matches!(completion, Completion::Failed) || matches!(owner.stage, Stage::Faulted)
            || monotonic_now < started || monotonic_now < owner.last_clock {
            owner.stage = Stage::Faulted;
        } else { owner.last_clock = monotonic_now; owner.stage = Stage::NeedStopRead; }
        owner
    }
}

/// The caller supplies a random/noncolliding active sequence and a fresh
/// validated MMP-block capture. No timestamp can override FSCK/unknown states.
fn state_start(raw: &[u8], physical: u64, first_data_block: u64, fs_blocks: u64,
    seed: u32, metadata: bool, update_seconds: u16, chosen_sequence: u32,
    monotonic_now: u64, node: &[u8], device: &[u8]) -> (r: Result<State, Error>)
    ensures match r {
        Ok(owner) => valid_origin(Origin { raw: raw@, physical, first_data: first_data_block, fs_blocks, seed, metadata,
            update: update_seconds, chosen: chosen_sequence, now: monotonic_now, node: node@, device: device@ }) && owner.view() == initial_view(Origin { raw: raw@, physical, first_data: first_data_block, fs_blocks, seed, metadata,
            update: update_seconds, chosen: chosen_sequence, now: monotonic_now, node: node@, device: device@ }),
        Err(_) => !valid_origin(Origin { raw: raw@, physical, first_data: first_data_block, fs_blocks, seed, metadata,
            update: update_seconds, chosen: chosen_sequence, now: monotonic_now, node: node@, device: device@ }),
    },
{
    if physical < first_data_block || physical >= fs_blocks { return Err(Error::Address); }
    if node.len() > 64 || device.len() > 32 { return Err(Error::Name); }
    if chosen_sequence > SEQ_MAX || update_seconds == 0 { return Err(Error::Sequence); }
    let record = match parse(raw, seed, metadata) { Ok(value) => value, Err(error) => { return Err(error); } };
    let clean = match classify(record.sequence) {
        Sequence::Clean => true,
        Sequence::Active(value) => {
            if value == chosen_sequence { return Err(Error::Sequence); }
            false
        },
        Sequence::Fsck | Sequence::Unknown(_) => { return Err(Error::Busy); },
    };
    let initial = if record.interval > update_seconds { record.interval } else { update_seconds };
    let check = if initial < MIN_CHECK_SECONDS { MIN_CHECK_SECONDS } else { initial };
    let wait = wait_seconds(check);
    let delay = if clean { check as u64 } else { wait };
    let deadline = match due(monotonic_now, delay) { Some(value) => value, None => { return Err(Error::Clock); } };
    Ok(State { raw: record.raw, block: physical, seed, metadata,
        node: copy(node), device: copy(device), sequence: record.sequence, chosen: chosen_sequence,
        update_seconds, check_seconds: check, wait, deadline, next_update: monotonic_now,
        last_clock: monotonic_now, claiming: true,
        stage: if clean { Stage::NeedWrite } else { Stage::WaitOld }, next_request: 1 })
}


impl StateReadPending {
    closed spec fn state_point(&self) -> ProtocolView {
        ProtocolView { controller: self.read_owner(), pending: Some(CommandView::Read { block: self.read_owner().block, kind: self.read_variant(), request: self.read_serial(), started: self.read_started() }) }
    }
}

impl StateWritePending {
    closed spec fn state_point(&self) -> ProtocolView {
        ProtocolView { controller: self.write_owner(), pending: Some(CommandView::Write { block: self.write_owner().block, image: self.write_image(), sequence: self.write_sequence(), clean: self.write_clean(), request: self.write_serial(), started: self.write_started() }) }
    }
}

impl StateFlushPending {
    closed spec fn state_point(&self) -> ProtocolView {
        ProtocolView { controller: self.flush_owner(), pending: Some(CommandView::Flush { clean: self.flush_clean(), request: self.flush_serial(), started: self.flush_started() }) }
    }
}

impl StateQuiescePending {
    closed spec fn state_point(&self) -> ProtocolView {
        ProtocolView { controller: self.quiesce_owner(), pending: Some(CommandView::Quiesce { request: self.quiesce_serial(), started: self.quiesce_started() }) }
    }
}

impl StateRequest {
    closed spec fn state_point(&self) -> ProtocolView {
        match self { Self::Read(p) => p.state_point(), Self::Write(p) => p.state_point(),
            Self::Flush(p) => p.state_point(), Self::Quiesce(p) => p.state_point() }
    }
}


pub struct Protector { state: State, origin: Ghost<Origin>, history: Ghost<Seq<ProtocolEvent>> }
pub struct ReadPending { inner: StateReadPending, origin: Ghost<Origin>, history: Ghost<Seq<ProtocolEvent>> }
pub struct WritePending { inner: StateWritePending, origin: Ghost<Origin>, history: Ghost<Seq<ProtocolEvent>> }
pub struct FlushPending { inner: StateFlushPending, origin: Ghost<Origin>, history: Ghost<Seq<ProtocolEvent>> }
pub struct QuiescePending { inner: StateQuiescePending, origin: Ghost<Origin>, history: Ghost<Seq<ProtocolEvent>> }
pub enum Request { Read(ReadPending), Write(WritePending), Flush(FlushPending), Quiesce(QuiescePending) }

pub open spec fn extended(origin: Origin, history: Seq<ProtocolEvent>, next_origin: Origin,
    next_history: Seq<ProtocolEvent>, before: ProtocolView, after: ProtocolView, action: Action) -> bool
{
    next_origin == origin && next_history == history.push(ProtocolEvent { before, after, action })
}

impl Protector {
    pub closed spec fn view(&self) -> ProtectorView { self.state.view() }
    pub closed spec fn origin(&self) -> Origin { self.origin@ }
    pub closed spec fn history(&self) -> Seq<ProtocolEvent> { self.history@ }
    pub closed spec fn point(&self) -> ProtocolView { ProtocolView { controller: self.view(), pending: None } }
    pub open spec fn wf(&self) -> bool { reachable(self.origin(), self.history(), self.point()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn stage(&self) -> (r: Stage) ensures r == self.view().stage { self.state.stage }
    pub fn sequence(&self) -> (r: u32) ensures r == self.view().sequence { self.state.sequence }
    pub fn block(&self) -> (r: u64) ensures r == self.view().block { self.state.block }
    pub fn deadlines(&self) -> (r: (u64, u64))
        ensures r == (self.view().next_update, self.view().deadline),
    { (self.state.next_update, self.state.deadline) }
    pub fn intended_bytes(&self) -> (r: &[u8]) ensures r@ == self.view().raw { &self.state.raw }
    pub fn stop(self) -> (r: Result<Self, (Self, Error)>)
        ensures match r {
            Ok(owner) => owner.wf() && self.view().stage == Stage::Ready
                && owner.view() == (ProtectorView { stage: Stage::Quiesce, ..self.view() })
                && extended(self.origin(), self.history(), owner.origin(), owner.history(), self.point(), owner.point(), Action::Stop),
            Err((owner, error)) => owner.wf() && owner.point() == self.point()
                && owner.origin() == self.origin() && owner.history() == self.history()
                && self.view().stage != Stage::Ready && error == Error::Phase,
        },
    {
        proof { use_type_invariant(&self); }
        let ghost before = self.point();
        let Protector { state, origin, history } = self;
        match state.state_stop() {
            Ok(state) => {
                let ghost after = ProtocolView { controller: state.view(), pending: None };
                let ghost event = ProtocolEvent { before, after, action: Action::Stop };
                proof { append_reachable(origin@, history@, event); }
                Ok(Protector { state, origin, history: Ghost(history@.push(event)) })
            },
            Err((state, error)) => Err((Protector { state, origin, history }, error)),
        }
    }
    pub fn abort(self) -> (r: Self)
        ensures r.wf(), r.view() == faulted(self.view()),
            extended(self.origin(), self.history(), r.origin(), r.history(), self.point(), r.point(), Action::AbortAvailable),
    {
        proof { use_type_invariant(&self); }
        let ghost before = self.point();
        let Protector { state, origin, history } = self;
        let state = state.state_abort();
        let ghost after = ProtocolView { controller: state.view(), pending: None };
        let ghost event = ProtocolEvent { before, after, action: Action::AbortAvailable };
        proof { append_reachable(origin@, history@, event); }
        Protector { state, origin, history: Ghost(history@.push(event)) }
    }
    /// Returns an owned software command. Dispatch does not perform device I/O.
    pub fn dispatch(self, monotonic_now: u64, wall_time: u64) -> (r: Result<Request, (Self, Error)>)
        ensures match r {
            Ok(command) => command.wf()
                && extended(self.origin(), self.history(), command.request_origin(), command.request_history(),
                    self.point(), command.request_point(), Action::Dispatch { now: monotonic_now, wall: wall_time, error: None })
                && dispatch_relation(self.view(), monotonic_now, wall_time, command.request_point(), None),
            Err((owner, error)) => owner.wf()
                && extended(self.origin(), self.history(), owner.origin(), owner.history(), self.point(), owner.point(),
                    Action::Dispatch { now: monotonic_now, wall: wall_time, error: Some(error) })
                && dispatch_relation(self.view(), monotonic_now, wall_time, owner.point(), Some(error)),
        },
    {
        proof { use_type_invariant(&self); }
        let ghost before = self.point();
        let Protector { state, origin, history } = self;
        match state.state_dispatch(monotonic_now, wall_time) {
            Ok(command) => {
                let ghost after = command.state_point();
                let ghost event = ProtocolEvent { before, after,
                    action: Action::Dispatch { now: monotonic_now, wall: wall_time, error: None } };
                proof { append_reachable(origin@, history@, event); }
                let history = Ghost(history@.push(event));
                match command {
                    StateRequest::Read(inner) => Ok(Request::Read(ReadPending { inner, origin, history })),
                    StateRequest::Write(inner) => Ok(Request::Write(WritePending { inner, origin, history })),
                    StateRequest::Flush(inner) => Ok(Request::Flush(FlushPending { inner, origin, history })),
                    StateRequest::Quiesce(inner) => Ok(Request::Quiesce(QuiescePending { inner, origin, history })),
                }
            },
            Err((state, error)) => {
                let ghost after = ProtocolView { controller: state.view(), pending: None };
                let ghost event = ProtocolEvent { before, after,
                    action: Action::Dispatch { now: monotonic_now, wall: wall_time, error: Some(error) } };
                proof { append_reachable(origin@, history@, event); }
                Err((Protector { state, origin, history: Ghost(history@.push(event)) }, error))
            },
        }
    }
}

impl Request {
    pub closed spec fn request_point(&self) -> ProtocolView {
        match self { Self::Read(p) => p.read_point(), Self::Write(p) => p.write_point(),
            Self::Flush(p) => p.flush_point(), Self::Quiesce(p) => p.quiesce_point() }
    }
    pub closed spec fn request_origin(&self) -> Origin {
        match self { Self::Read(p) => p.read_origin(), Self::Write(p) => p.write_origin(),
            Self::Flush(p) => p.flush_origin(), Self::Quiesce(p) => p.quiesce_origin() }
    }
    pub closed spec fn request_history(&self) -> Seq<ProtocolEvent> {
        match self { Self::Read(p) => p.read_history(), Self::Write(p) => p.write_history(),
            Self::Flush(p) => p.flush_history(), Self::Quiesce(p) => p.quiesce_history() }
    }
    pub open spec fn wf(&self) -> bool { reachable(self.request_origin(), self.request_history(), self.request_point()) }
}


impl ReadPending {
    pub closed spec fn read_owner(&self) -> ProtectorView { self.inner.read_owner() }
    pub closed spec fn read_started(&self) -> u64 { self.inner.read_started() }
    pub closed spec fn read_variant(&self) -> ReadKind { self.inner.read_variant() }
    pub closed spec fn read_serial(&self) -> u64 { self.inner.read_serial() }
    pub closed spec fn read_origin(&self) -> Origin { self.origin@ }
    pub closed spec fn read_history(&self) -> Seq<ProtocolEvent> { self.history@ }
    pub closed spec fn read_command(&self) -> CommandView { CommandView::Read { block: self.read_owner().block, kind: self.read_variant(), request: self.read_serial(), started: self.read_started() } }
    pub closed spec fn read_point(&self) -> ProtocolView {
        ProtocolView { controller: self.read_owner(), pending: Some(self.read_command()) }
    }
    pub open spec fn read_wf(&self) -> bool { reachable(self.read_origin(), self.read_history(), self.read_point()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.read_wf() }
    pub fn read_block(&self) -> (r: u64) ensures r == self.read_owner().block { self.inner.owner.block }
    pub fn read_request(&self) -> (r: u64) ensures r == self.read_serial() { self.inner.request }
    pub fn read_kind(&self) -> (r: ReadKind) ensures r == self.read_variant() { self.inner.kind }
    pub fn abort_read(self) -> (r: Self)
        ensures r.read_wf(), extended(self.read_origin(), self.read_history(), r.read_origin(), r.read_history(),
            self.read_point(), r.read_point(), Action::AbortPending),
            r.read_owner() == (ProtectorView { stage: Stage::Faulted, ..self.read_owner() }), r.read_started() == self.read_started(), r.read_variant() == self.read_variant(), r.read_serial() == self.read_serial(),
    {
        proof { use_type_invariant(&self); }
        let ghost before = self.read_point();
        let ReadPending { inner, origin, history } = self;
        let inner = inner.state_abort_read();
        let ghost after = inner.state_point();
        let ghost event = ProtocolEvent { before, after, action: Action::AbortPending };
        proof { append_reachable(origin@, history@, event); }
        ReadPending { inner, origin, history: Ghost(history@.push(event)) }
    }
    pub fn finish_read(self, bytes: Option<&[u8]>, monotonic_now: u64) -> (r: (Protector, Result<(), Error>))
        ensures r.0.wf(), extended(self.read_origin(), self.read_history(), r.0.origin(), r.0.history(),
            self.read_point(), r.0.point(), Action::ReadReport { media: match bytes { Some(raw) => Some(raw@), None => None }, now: monotonic_now, status: r.1 }),
            r.0.view() == read_result(self.read_owner(), self.read_variant(), self.read_started(),
                match bytes { Some(raw) => Some(raw@), None => None }, monotonic_now).0,
            r.1 == read_result(self.read_owner(), self.read_variant(), self.read_started(),
                match bytes { Some(raw) => Some(raw@), None => None }, monotonic_now).1,
            fixed_parameters(self.read_owner(), r.0.view()),
            r.0.view().sequence == self.read_owner().sequence,
            r.0.view().next_request == self.read_owner().next_request,
            match r.1 {
                Ok(()) => monotonic_now >= self.read_started() && monotonic_now >= self.read_owner().last_clock
                    && r.0.view().last_clock == monotonic_now
                    && (match bytes { Some(media) =>
                        block_size::accepted(media.len() as nat) && media.len() == self.read_owner().raw.len()
                        && bytes::le32(media@, 0) == MAGIC && bytes::le32(media@, 4) == self.read_owner().sequence
                        && (self.read_owner().metadata ==> bytes::le32(media@, 1020) == checksum(media@, self.read_owner().seed))
                        && (self.read_variant() != ReadKind::OldObservation ==> media@.subrange(16, 80) == self.read_owner().raw.subrange(16, 80))
                        && r.0.view().raw == if self.read_variant() == ReadKind::OldObservation { media@ } else { self.read_owner().raw },
                        None => false })
                    && r.0.view().stage == match self.read_variant() {
                        ReadKind::ClaimObservation => Stage::Ready,
                        ReadKind::OldObservation | ReadKind::HeartbeatObservation => Stage::NeedWrite,
                        ReadKind::StopObservation => Stage::NeedCleanWrite,
                    }
                    && (self.read_variant() == ReadKind::ClaimObservation ==> !r.0.view().claiming),
                Err(_) => r.0.view().stage == Stage::Faulted,
            },
    {
        proof { use_type_invariant(&self); }
        let ghost before = self.read_point();
        let ghost media = match bytes { Some(raw) => Some(raw@), None => None };
        let ReadPending { inner, origin, history } = self;
        let (state, status) = inner.state_finish_read(bytes, monotonic_now);
        let ghost after = ProtocolView { controller: state.view(), pending: None };
        let ghost event = ProtocolEvent { before, after, action: Action::ReadReport { media, now: monotonic_now, status } };
        proof { append_reachable(origin@, history@, event); }
        (Protector { state, origin, history: Ghost(history@.push(event)) }, status)
    }
}

impl WritePending {
    pub closed spec fn write_owner(&self) -> ProtectorView { self.inner.write_owner() }
    pub closed spec fn write_image(&self) -> Seq<u8> { self.inner.write_image() }
    pub closed spec fn write_sequence(&self) -> u32 { self.inner.write_sequence() }
    pub closed spec fn write_clean(&self) -> bool { self.inner.write_clean() }
    pub closed spec fn write_started(&self) -> u64 { self.inner.write_started() }
    pub closed spec fn write_serial(&self) -> u64 { self.inner.write_serial() }
    pub closed spec fn write_origin(&self) -> Origin { self.origin@ }
    pub closed spec fn write_history(&self) -> Seq<ProtocolEvent> { self.history@ }
    pub closed spec fn write_command(&self) -> CommandView { CommandView::Write { block: self.write_owner().block, image: self.write_image(), sequence: self.write_sequence(), clean: self.write_clean(), request: self.write_serial(), started: self.write_started() } }
    pub closed spec fn write_point(&self) -> ProtocolView {
        ProtocolView { controller: self.write_owner(), pending: Some(self.write_command()) }
    }
    pub open spec fn write_wf(&self) -> bool { reachable(self.write_origin(), self.write_history(), self.write_point()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.write_wf() }
    pub fn write_block(&self) -> (r: u64) ensures r == self.write_owner().block { self.inner.owner.block }
    pub fn write_request(&self) -> (r: u64) ensures r == self.write_serial() { self.inner.request }
    pub fn write_bytes(&self) -> (r: &[u8]) ensures r@ == self.write_image() { &self.inner.image }
    pub fn abort_write(self) -> (r: Self)
        ensures r.write_wf(), extended(self.write_origin(), self.write_history(), r.write_origin(), r.write_history(),
            self.write_point(), r.write_point(), Action::AbortPending),
            r.write_owner() == (ProtectorView { stage: Stage::Faulted, ..self.write_owner() }), r.write_image() == self.write_image(), r.write_sequence() == self.write_sequence(),
            r.write_clean() == self.write_clean(), r.write_started() == self.write_started(), r.write_serial() == self.write_serial(),
    {
        proof { use_type_invariant(&self); }
        let ghost before = self.write_point();
        let WritePending { inner, origin, history } = self;
        let inner = inner.state_abort_write();
        let ghost after = inner.state_point();
        let ghost event = ProtocolEvent { before, after, action: Action::AbortPending };
        proof { append_reachable(origin@, history@, event); }
        WritePending { inner, origin, history: Ghost(history@.push(event)) }
    }
    pub fn finish_write(self, completion: Completion, monotonic_now: u64) -> (r: Protector)
        ensures r.wf(), extended(self.write_origin(), self.write_history(), r.origin(), r.history(),
            self.write_point(), r.point(), Action::WriteReport { completion, now: monotonic_now }),

            r.view() == write_result(self.write_owner(), self.write_image(), self.write_sequence(),
            self.write_clean(), completion, self.write_started(), monotonic_now),
            r.view().raw == self.write_image(), fixed_parameters(self.write_owner(), r.view()),
    {
        proof { use_type_invariant(&self); }
        let ghost before = self.write_point();

        let WritePending { inner, origin, history } = self;
        let state = inner.state_finish_write(completion, monotonic_now);
        let ghost after = ProtocolView { controller: state.view(), pending: None };
        let ghost event = ProtocolEvent { before, after, action: Action::WriteReport { completion, now: monotonic_now } };
        proof { append_reachable(origin@, history@, event); }
        Protector { state, origin, history: Ghost(history@.push(event)) }
    }
}

impl FlushPending {
    pub closed spec fn flush_owner(&self) -> ProtectorView { self.inner.flush_owner() }
    pub closed spec fn flush_clean(&self) -> bool { self.inner.flush_clean() }
    pub closed spec fn flush_started(&self) -> u64 { self.inner.flush_started() }
    pub closed spec fn flush_serial(&self) -> u64 { self.inner.flush_serial() }
    pub closed spec fn flush_origin(&self) -> Origin { self.origin@ }
    pub closed spec fn flush_history(&self) -> Seq<ProtocolEvent> { self.history@ }
    pub closed spec fn flush_command(&self) -> CommandView { CommandView::Flush { clean: self.flush_clean(), request: self.flush_serial(), started: self.flush_started() } }
    pub closed spec fn flush_point(&self) -> ProtocolView {
        ProtocolView { controller: self.flush_owner(), pending: Some(self.flush_command()) }
    }
    pub open spec fn flush_wf(&self) -> bool { reachable(self.flush_origin(), self.flush_history(), self.flush_point()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.flush_wf() }
    pub fn flush_request(&self) -> (r: u64) ensures r == self.flush_serial() { self.inner.request }
    pub fn abort_flush(self) -> (r: Self)
        ensures r.flush_wf(), extended(self.flush_origin(), self.flush_history(), r.flush_origin(), r.flush_history(),
            self.flush_point(), r.flush_point(), Action::AbortPending),
            r.flush_owner() == (ProtectorView { stage: Stage::Faulted, ..self.flush_owner() }), r.flush_clean() == self.flush_clean(), r.flush_started() == self.flush_started(), r.flush_serial() == self.flush_serial(),
    {
        proof { use_type_invariant(&self); }
        let ghost before = self.flush_point();
        let FlushPending { inner, origin, history } = self;
        let inner = inner.state_abort_flush();
        let ghost after = inner.state_point();
        let ghost event = ProtocolEvent { before, after, action: Action::AbortPending };
        proof { append_reachable(origin@, history@, event); }
        FlushPending { inner, origin, history: Ghost(history@.push(event)) }
    }
    pub fn finish_flush(self, completion: Completion, monotonic_now: u64) -> (r: Protector)
        ensures r.wf(), extended(self.flush_origin(), self.flush_history(), r.origin(), r.history(),
            self.flush_point(), r.point(), Action::FlushReport { completion, now: monotonic_now }),

            r.view() == flush_result(self.flush_owner(), self.flush_clean(), completion, self.flush_started(), monotonic_now),
            fixed_parameters(self.flush_owner(), r.view()), r.view().raw == self.flush_owner().raw,
    {
        proof { use_type_invariant(&self); }
        let ghost before = self.flush_point();

        let FlushPending { inner, origin, history } = self;
        let state = inner.state_finish_flush(completion, monotonic_now);
        let ghost after = ProtocolView { controller: state.view(), pending: None };
        let ghost event = ProtocolEvent { before, after, action: Action::FlushReport { completion, now: monotonic_now } };
        proof { append_reachable(origin@, history@, event); }
        Protector { state, origin, history: Ghost(history@.push(event)) }
    }
}

impl QuiescePending {
    pub closed spec fn quiesce_owner(&self) -> ProtectorView { self.inner.quiesce_owner() }
    pub closed spec fn quiesce_started(&self) -> u64 { self.inner.quiesce_started() }
    pub closed spec fn quiesce_serial(&self) -> u64 { self.inner.quiesce_serial() }
    pub closed spec fn quiesce_origin(&self) -> Origin { self.origin@ }
    pub closed spec fn quiesce_history(&self) -> Seq<ProtocolEvent> { self.history@ }
    pub closed spec fn quiesce_command(&self) -> CommandView { CommandView::Quiesce { request: self.quiesce_serial(), started: self.quiesce_started() } }
    pub closed spec fn quiesce_point(&self) -> ProtocolView {
        ProtocolView { controller: self.quiesce_owner(), pending: Some(self.quiesce_command()) }
    }
    pub open spec fn quiesce_wf(&self) -> bool { reachable(self.quiesce_origin(), self.quiesce_history(), self.quiesce_point()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.quiesce_wf() }
    pub fn quiesce_request(&self) -> (r: u64) ensures r == self.quiesce_serial() { self.inner.request }
    pub fn abort_quiesce(self) -> (r: Self)
        ensures r.quiesce_wf(), extended(self.quiesce_origin(), self.quiesce_history(), r.quiesce_origin(), r.quiesce_history(),
            self.quiesce_point(), r.quiesce_point(), Action::AbortPending),
            r.quiesce_owner() == (ProtectorView { stage: Stage::Faulted, ..self.quiesce_owner() }), r.quiesce_started() == self.quiesce_started(), r.quiesce_serial() == self.quiesce_serial(),
    {
        proof { use_type_invariant(&self); }
        let ghost before = self.quiesce_point();
        let QuiescePending { inner, origin, history } = self;
        let inner = inner.state_abort_quiesce();
        let ghost after = inner.state_point();
        let ghost event = ProtocolEvent { before, after, action: Action::AbortPending };
        proof { append_reachable(origin@, history@, event); }
        QuiescePending { inner, origin, history: Ghost(history@.push(event)) }
    }
    pub fn finish_quiesce(self, completion: Completion, monotonic_now: u64) -> (r: Protector)
        ensures r.wf(), extended(self.quiesce_origin(), self.quiesce_history(), r.origin(), r.history(),
            self.quiesce_point(), r.point(), Action::QuiesceReport { completion, now: monotonic_now }),

            r.view() == quiesce_result(self.quiesce_owner(), completion, self.quiesce_started(), monotonic_now),
            fixed_parameters(self.quiesce_owner(), r.view()), r.view().raw == self.quiesce_owner().raw,
    {
        proof { use_type_invariant(&self); }
        let ghost before = self.quiesce_point();

        let QuiescePending { inner, origin, history } = self;
        let state = inner.state_finish_quiesce(completion, monotonic_now);
        let ghost after = ProtocolView { controller: state.view(), pending: None };
        let ghost event = ProtocolEvent { before, after, action: Action::QuiesceReport { completion, now: monotonic_now } };
        proof { append_reachable(origin@, history@, event); }
        Protector { state, origin, history: Ghost(history@.push(event)) }
    }
}


pub fn start(raw: &[u8], physical: u64, first_data_block: u64, fs_blocks: u64,
    seed: u32, metadata: bool, update_seconds: u16, chosen_sequence: u32,
    monotonic_now: u64, node: &[u8], device: &[u8]) -> (r: Result<Protector, Error>)
    ensures match r {
        Ok(owner) => owner.wf() && owner.origin() == (Origin { raw: raw@, physical, first_data: first_data_block, fs_blocks, seed, metadata,
            update: update_seconds, chosen: chosen_sequence, now: monotonic_now, node: node@, device: device@ })
            && owner.history().len() == 0 && owner.view() == initial_view(owner.origin()),
        Err(_) => !valid_origin(Origin { raw: raw@, physical, first_data: first_data_block, fs_blocks, seed, metadata,
            update: update_seconds, chosen: chosen_sequence, now: monotonic_now, node: node@, device: device@ }),
    },
{
    let ghost origin = Origin { raw: raw@, physical, first_data: first_data_block, fs_blocks, seed, metadata,
            update: update_seconds, chosen: chosen_sequence, now: monotonic_now, node: node@, device: device@ };
    match state_start(raw, physical, first_data_block, fs_blocks, seed, metadata,
        update_seconds, chosen_sequence, monotonic_now, node, device) {
        Ok(state) => {
            proof { reveal(reachable); }
            Ok(Protector { state, origin: Ghost(origin), history: Ghost(Seq::empty()) })
        },
        Err(error) => Err(error),
    }
}

pub proof fn fsck_and_unknown_sequences_never_become_claimable_from_wall_time(sequence: u32, wall_time: u64)
    requires sequence == SEQ_FSCK || sequence > SEQ_MAX && sequence != SEQ_CLEAN,
    ensures sequence_class(sequence) != Sequence::Clean
        && !(sequence_class(sequence) is Active),
{ }
pub proof fn rewriting_preserves_uninterpreted_padding_and_block_tail(before: Seq<u8>, after: Seq<u8>,
    sequence: u32, wall_time: u64, node: Seq<u8>, device: Seq<u8>, interval: u16, seed: u32, metadata: bool)
    requires rewritten(before, after, sequence, wall_time, node, device, interval, seed, metadata),
    ensures after.subrange(114, 1020) == before.subrange(114, 1020),
        after.subrange(1024, after.len() as int) == before.subrange(1024, before.len() as int),
{ }

pub proof fn failed_or_expired_heartbeat_writes_preserve_the_attempt_without_readiness(v: ProtectorView, image: Seq<u8>,
    sequence: u32, clean: bool, completion: Completion, started: u64, now: u64)
    requires completion == Completion::Failed || !v.claiming && !clean && now > v.deadline,
    ensures write_result(v, image, sequence, clean, completion, started, now).stage == Stage::Faulted,
        write_result(v, image, sequence, clean, completion, started, now).raw == image,
{ }
pub proof fn initial_claim_flush_still_requires_a_claim_observation(v: ProtectorView, completion: Completion, started: u64, now: u64)
    requires v.claiming,
    ensures flush_result(v, false, completion, started, now).stage != Stage::Ready,
{ }
pub proof fn a_clean_marker_is_not_stopped_before_successful_flush(v: ProtectorView, clean: bool, completion: Completion, started: u64, now: u64)
    requires flush_result(v, clean, completion, started, now).stage == Stage::Stopped,
    ensures clean && completion == Completion::Succeeded && v.stage != Stage::Faulted
        && now >= started && now >= v.last_clock,
{ }


pub proof fn a_pending_command_cannot_be_replaced_by_another_dispatch(event: ProtocolEvent)
    requires permitted(event), event.before.pending.is_some(),
    ensures !(event.action is Dispatch) && !(event.action is Stop) && !(event.action is AbortAvailable),
{
    match event.action {
        Action::Dispatch { .. } | Action::Stop | Action::AbortAvailable => { },
        _ => { },
    }
}
pub proof fn aborting_a_pending_command_retains_its_exact_descriptor(event: ProtocolEvent)
    requires permitted(event), event.action is AbortPending,
    ensures event.after.pending == event.before.pending,
        event.after.controller == faulted(event.before.controller),
        event.after.pending.is_some(),
{ }
pub proof fn an_offered_write_is_bound_to_the_source_image(event: ProtocolEvent,
    block: u64, image: Seq<u8>, sequence: u32, clean: bool, request: u64, started: u64,
    now: u64, wall: u64)
    requires permitted(event), event.action == (Action::Dispatch { now, wall, error: None }),
        event.after.pending == Some(CommandView::Write { block, image, sequence, clean, request, started }),
    ensures event.before.pending.is_none(),
        block == event.before.controller.block, request == event.before.controller.next_request, started == now,
        rewritten(event.before.controller.raw, image, sequence, wall, event.before.controller.node,
            event.before.controller.device, event.before.controller.check_seconds,
            event.before.controller.seed, event.before.controller.metadata),
{
    match dispatch_choice(event.before.controller, now) {
        DispatchChoice::Write { sequence: expected, clean: expected_clean } => { },
        _ => { },
    }
}


pub proof fn a_faulted_controller_cannot_regain_readiness_from_a_late_report(event: ProtocolEvent)
    requires permitted(event), event.before.controller.stage == Stage::Faulted,
    ensures event.after.controller.stage == Stage::Faulted,
{
    match event.action {
        Action::Stop => { },
        Action::AbortAvailable | Action::AbortPending => { },
        Action::Dispatch { now, wall, error } => {
            if now < event.before.controller.last_clock { }
            else if event.before.controller.next_request == u64::MAX { }
            else { assert(dispatch_choice(event.before.controller, now) == DispatchChoice::Refuse(Error::Phase)); }
        },
        Action::ReadReport { media, now, status } => {
            match event.before.pending {
                Some(CommandView::Read { block, kind, request, started }) => { },
                _ => { },
            }
        },
        Action::WriteReport { completion, now } => {
            match event.before.pending {
                Some(CommandView::Write { block, image, sequence, clean, request, started }) => { },
                _ => { },
            }
        },
        Action::FlushReport { completion, now } => {
            match event.before.pending {
                Some(CommandView::Flush { clean, request, started }) => { },
                _ => { },
            }
        },
        Action::QuiesceReport { completion, now } => {
            match event.before.pending {
                Some(CommandView::Quiesce { request, started }) => { },
                _ => { },
            }
        },
    }
}

}
