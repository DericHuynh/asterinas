// SPDX-License-Identifier: MPL-2.0

//! Linux MMP bytes and an owned observation/write/flush protocol. It needs
//! cooperative peers, noncolliding claim sequences, fresh device reads,
//! bounded write visibility and a monotonic clock. Disk wall time is only
//! diagnostic. Protocol state does not grant a mount or device lease.

use alloc::vec::Vec;

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
        assert(word@ == encoded16(value)) by (nonlinear_arith)
            requires bytes::le16(word@, 0) == value,
                0 <= word@[0] <= 255, 0 <= word@[1] <= 255;
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
    let low = (value & 0xffffffffu64) as u32;
    let high = (value >> 32) as u32;
    write32(raw, at, low);
    write32(raw, at + 4, high);
    proof {
        assert(raw@ =~= bytes::splice(before, at as int, encoded64(value)));
        assert((low as u64) | ((high as u64) << 32) == value) by (bit_vector);
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
    ensures match r {
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

pub fn rewrite(raw: &[u8], sequence: u32, wall_time: u64, node: &[u8], device: &[u8],
    interval: u16, seed: u32, metadata: bool) -> (r: Result<Vec<u8>, Error>)
    ensures match r {
        Ok(out) => rewritten(raw@, out@, sequence, wall_time, node@, device@, interval, seed, metadata),
        Err(_) => true,
    },
{
    if !block_size::valid(raw.len()) || raw.len() < STRUCT_BYTES { return Err(Error::Geometry); }
    if node.len() > 64 || device.len() > 32 { return Err(Error::Name); }
    let mut out = copy(raw);
    if !write32(&mut out, 0, MAGIC) || !write32(&mut out, 4, sequence)
        || !write64(&mut out, 8, wall_time) || !write16(&mut out, 112, interval) {
        return Err(Error::Geometry);
    }
    let ghost header = out@;
    let mut i = 0usize;
    while i < 64
        invariant i <= 64, out.len() == raw.len(), raw.len() >= STRUCT_BYTES, header.len() == raw.len(),
            out@.take(16) == header.take(16),
            out@.subrange(80, out.len() as int) == header.subrange(80, header.len() as int),
            forall|j: int| 0 <= j < i ==> #[trigger] out@[16 + j] == if j < node.len() { node@[j] } else { 0 },
        decreases 64 - i,
    { out.set(16 + i, if i < node.len() { node[i] } else { 0 }); i += 1; }
    let ghost named = out@;
    i = 0;
    while i < 32
        invariant i <= 32, out.len() == raw.len(), raw.len() >= STRUCT_BYTES, named.len() == raw.len(),
            out@.take(80) == named.take(80),
            out@.subrange(112, out.len() as int) == named.subrange(112, named.len() as int),
            forall|j: int| 0 <= j < i ==> #[trigger] out@[80 + j] == if j < device.len() { device@[j] } else { 0 },
        decreases 32 - i,
    { out.set(80 + i, if i < device.len() { device[i] } else { 0 }); i += 1; }
    if metadata {
        let checksum = crc::crc32c(seed, &out[..CHECKSUM_OFFSET]);
        let ghost prefix = out@.take(1020);
        if !write32(&mut out, CHECKSUM_OFFSET, checksum) { return Err(Error::Geometry); }
        proof { assert(out@.take(1020) =~= prefix); }
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

pub struct Protector {
    raw: Vec<u8>, block: u64, seed: u32, metadata: bool,
    node: Vec<u8>, device: Vec<u8>, sequence: u32, chosen: u32,
    update_seconds: u16, check_seconds: u16, wait: u64,
    deadline: u64, next_update: u64, last_clock: u64,
    claiming: bool, stage: Stage, next_request: u64,
}
pub struct ReadPending { owner: Protector, kind: ReadKind, request: u64, started: u64 }
pub struct WritePending { owner: Protector, image: Vec<u8>, sequence: u32, clean: bool, request: u64, started: u64 }
pub struct FlushPending { owner: Protector, clean: bool, request: u64, started: u64 }
pub struct QuiescePending { owner: Protector, request: u64, started: u64 }
pub enum Request {
    Read(ReadPending), Write(WritePending), Flush(FlushPending), Quiesce(QuiescePending),
}

impl Protector {
    pub closed spec fn view(&self) -> ProtectorView {
        ProtectorView { raw: self.raw@, block: self.block, seed: self.seed, metadata: self.metadata,
            node: self.node@, device: self.device@, sequence: self.sequence, chosen: self.chosen,
            update_seconds: self.update_seconds, check_seconds: self.check_seconds, wait: self.wait,
            deadline: self.deadline, next_update: self.next_update, last_clock: self.last_clock,
            claiming: self.claiming, stage: self.stage, next_request: self.next_request }
    }
    pub fn stage(&self) -> (r: Stage) ensures r == self.view().stage { self.stage }
    pub fn sequence(&self) -> (r: u32) ensures r == self.view().sequence { self.sequence }
    pub fn block(&self) -> (r: u64) ensures r == self.view().block { self.block }
    pub fn deadlines(&self) -> (r: (u64, u64)) ensures r == (self.view().next_update, self.view().deadline) { (self.next_update, self.deadline) }
    pub fn intended_bytes(&self) -> (r: &[u8]) ensures r@ == self.view().raw { &self.raw }
    pub fn stop(mut self) -> (r: Result<Self, (Self, Error)>)
        ensures match r {
            Ok(owner) => self.view().stage == Stage::Ready
                && owner.view() == (ProtectorView { stage: Stage::Quiesce, ..self.view() }),
            Err((owner, _)) => owner.view() == self.view() && self.view().stage != Stage::Ready,
        },
    {
        if !matches!(self.stage, Stage::Ready) { return Err((self, Error::Phase)); }
        self.stage = Stage::Quiesce; Ok(self)
    }
    pub fn abort(mut self) -> (r: Self)
        ensures r.view() == (ProtectorView { stage: Stage::Faulted, ..self.view() }),
    { self.stage = Stage::Faulted; self }
    fn ready(&mut self, now: u64) -> (r: bool)
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

    pub fn dispatch(mut self, monotonic_now: u64, wall_time: u64) -> Result<Request, (Self, Error)> {
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
            return Ok(Request::Read(ReadPending { owner: self, kind, request, started: monotonic_now }));
        }
        match self.stage {
            Stage::WaitOld | Stage::WaitClaim | Stage::NeedStopRead => {
                if !matches!(self.stage, Stage::NeedStopRead) && monotonic_now < self.deadline { return Err((self, Error::Wait)); }
                let kind = if matches!(self.stage, Stage::WaitOld) { ReadKind::OldObservation }
                    else if matches!(self.stage, Stage::WaitClaim) { ReadKind::ClaimObservation }
                    else { ReadKind::StopObservation };
                self.next_request += 1;
                return Ok(Request::Read(ReadPending { owner: self, kind, request, started: monotonic_now }));
            },
            Stage::Ready => {
                if monotonic_now < self.next_update { return Err((self, Error::Wait)); }
                if monotonic_now > self.deadline {
                    self.next_request += 1;
                    return Ok(Request::Read(ReadPending { owner: self, kind: ReadKind::HeartbeatObservation,
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
                Ok(Request::Write(WritePending { owner: self, image, sequence, clean, request, started: monotonic_now }))
            },
            Stage::NeedFlush | Stage::NeedCleanFlush => {
                let clean = matches!(self.stage, Stage::NeedCleanFlush);
                Ok(Request::Flush(FlushPending { owner: self, clean, request, started: monotonic_now }))
            },
            Stage::Quiesce => Ok(Request::Quiesce(QuiescePending { owner: self, request, started: monotonic_now })),
            _ => { self.stage = Stage::Faulted; Err((self, Error::Phase)) },
        }
    }
}

impl ReadPending {
    pub closed spec fn read_owner(&self) -> ProtectorView { self.owner.view() }
    pub closed spec fn read_started(&self) -> u64 { self.started }
    pub closed spec fn read_variant(&self) -> ReadKind { self.kind }
    pub closed spec fn read_serial(&self) -> u64 { self.request }
    pub fn read_block(&self) -> (r: u64) ensures r == self.read_owner().block { self.owner.block }
    pub fn read_request(&self) -> (r: u64) ensures r == self.read_serial() { self.request }
    pub fn read_kind(&self) -> (r: ReadKind) ensures r == self.read_variant() { self.kind }
    pub fn abort_read(mut self) -> (r: Self)
        ensures r.read_owner() == (ProtectorView { stage: Stage::Faulted, ..self.read_owner() }), r.read_started() == self.read_started(), r.read_variant() == self.read_variant(), r.read_serial() == self.read_serial(),
    { self.owner.stage = Stage::Faulted; self }
    pub fn finish_read(self, bytes: Option<&[u8]>, monotonic_now: u64) -> (r: (Protector, Result<(), Error>))
        ensures fixed_parameters(self.read_owner(), r.0.view()),
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
        let ReadPending { mut owner, kind, request: _, started } = self;
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
                if !owner.ready(monotonic_now) { return (owner, Err(Error::Clock)); }
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
impl WritePending {
    pub closed spec fn write_owner(&self) -> ProtectorView { self.owner.view() }
    pub closed spec fn write_image(&self) -> Seq<u8> { self.image@ }
    pub closed spec fn write_sequence(&self) -> u32 { self.sequence }
    pub closed spec fn write_clean(&self) -> bool { self.clean }
    pub closed spec fn write_started(&self) -> u64 { self.started }
    pub closed spec fn write_serial(&self) -> u64 { self.request }
    pub fn write_block(&self) -> (r: u64) ensures r == self.write_owner().block { self.owner.block }
    pub fn write_request(&self) -> (r: u64) ensures r == self.write_serial() { self.request }
    pub fn write_bytes(&self) -> (r: &[u8]) ensures r@ == self.write_image() { &self.image }
    pub fn abort_write(mut self) -> (r: Self)
        ensures r.write_owner() == (ProtectorView { stage: Stage::Faulted, ..self.write_owner() }), r.write_image() == self.write_image(), r.write_sequence() == self.write_sequence(),
            r.write_clean() == self.write_clean(), r.write_started() == self.write_started(), r.write_serial() == self.write_serial(),
    { self.owner.stage = Stage::Faulted; self }
    pub fn finish_write(self, completion: Completion, monotonic_now: u64) -> (r: Protector)
        ensures r.view() == write_result(self.write_owner(), self.write_image(), self.write_sequence(),
            self.write_clean(), completion, self.write_started(), monotonic_now),
            r.view().raw == self.write_image(), fixed_parameters(self.write_owner(), r.view()),
    {
        let WritePending { mut owner, image, sequence, clean, request: _, started } = self;
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
impl FlushPending {
    pub closed spec fn flush_owner(&self) -> ProtectorView { self.owner.view() }
    pub closed spec fn flush_clean(&self) -> bool { self.clean }
    pub closed spec fn flush_started(&self) -> u64 { self.started }
    pub closed spec fn flush_serial(&self) -> u64 { self.request }
    pub fn flush_request(&self) -> (r: u64) ensures r == self.flush_serial() { self.request }
    pub fn abort_flush(mut self) -> (r: Self)
        ensures r.flush_owner() == (ProtectorView { stage: Stage::Faulted, ..self.flush_owner() }), r.flush_clean() == self.flush_clean(), r.flush_started() == self.flush_started(), r.flush_serial() == self.flush_serial(),
    { self.owner.stage = Stage::Faulted; self }
    pub fn finish_flush(self, completion: Completion, monotonic_now: u64) -> (r: Protector)
        ensures r.view() == flush_result(self.flush_owner(), self.flush_clean(), completion, self.flush_started(), monotonic_now),
            fixed_parameters(self.flush_owner(), r.view()), r.view().raw == self.flush_owner().raw,
    {
        let FlushPending { mut owner, clean, request: _, started } = self;
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
        } else { let _ = owner.ready(monotonic_now); }
        owner
    }
}
impl QuiescePending {
    pub closed spec fn quiesce_owner(&self) -> ProtectorView { self.owner.view() }
    pub closed spec fn quiesce_started(&self) -> u64 { self.started }
    pub closed spec fn quiesce_serial(&self) -> u64 { self.request }
    pub fn quiesce_request(&self) -> (r: u64) ensures r == self.quiesce_serial() { self.request }
    pub fn abort_quiesce(mut self) -> (r: Self)
        ensures r.quiesce_owner() == (ProtectorView { stage: Stage::Faulted, ..self.quiesce_owner() }), r.quiesce_started() == self.quiesce_started(), r.quiesce_serial() == self.quiesce_serial(),
    { self.owner.stage = Stage::Faulted; self }
    /// Succeeded means filesystem operations and their I/O are quiescent,
    /// established by the runtime adapter before writing the clean marker.
    pub fn finish_quiesce(self, completion: Completion, monotonic_now: u64) -> (r: Protector)
        ensures r.view() == quiesce_result(self.quiesce_owner(), completion, self.quiesce_started(), monotonic_now),
            fixed_parameters(self.quiesce_owner(), r.view()), r.view().raw == self.quiesce_owner().raw,
    {
        let QuiescePending { mut owner, request: _, started } = self;
        if matches!(completion, Completion::Failed) || matches!(owner.stage, Stage::Faulted)
            || monotonic_now < started || monotonic_now < owner.last_clock {
            owner.stage = Stage::Faulted;
        } else { owner.last_clock = monotonic_now; owner.stage = Stage::NeedStopRead; }
        owner
    }
}

/// The caller supplies a random/noncolliding active sequence and a fresh
/// validated MMP-block capture. No timestamp can override FSCK/unknown states.
pub fn start(raw: &[u8], physical: u64, first_data_block: u64, fs_blocks: u64,
    seed: u32, metadata: bool, update_seconds: u16, chosen_sequence: u32,
    monotonic_now: u64, node: &[u8], device: &[u8]) -> Result<Protector, Error>
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
    Ok(Protector { raw: record.raw, block: physical, seed, metadata,
        node: copy(node), device: copy(device), sequence: record.sequence, chosen: chosen_sequence,
        update_seconds, check_seconds: check, wait, deadline, next_update: monotonic_now,
        last_clock: monotonic_now, claiming: true,
        stage: if clean { Stage::NeedWrite } else { Stage::WaitOld }, next_request: 1 })
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

}
