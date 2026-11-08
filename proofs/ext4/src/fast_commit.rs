// SPDX-License-Identifier: MPL-2.0

//! Linux ext4 fast-commit TLVs, complete-tail recognition and replay planning.
//! This is an implementation-first format engine. Its plans describe replay
//! work; they are not filesystem, allocation, device or durability capabilities.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, crc};

verus! {

pub const ADD_RANGE: u16 = 1;
pub const DEL_RANGE: u16 = 2;
pub const CREAT: u16 = 3;
pub const LINK: u16 = 4;
pub const UNLINK: u16 = 5;
pub const INODE: u16 = 6;
pub const PAD: u16 = 7;
pub const TAIL: u16 = 8;
pub const HEAD: u16 = 9;
pub const MAX_RECORDS: usize = 4096;
pub const MAX_LOG_BYTES: usize = 67108864;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Error {
    Geometry, Malformed, UnsupportedFeatures, BadChecksum, ResourceLimit,
    InvalidInode, InvalidRange, InvalidName, RecordTooLarge, NoChanges,
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Stop { EndOfArea, EmptyArea, TornSuffix, DifferentTransaction }

pub struct Record { pub tag: u16, pub value: Vec<u8> }
pub struct RecordView { pub tag: u16, pub value: Seq<u8> }
pub open spec fn record_views(records: Seq<Record>) -> Seq<RecordView> {
    Seq::new(records.len(), |i: int| RecordView { tag: records[i].tag, value: records[i].value@ })
}
pub open spec fn value_length_ok(tag: u16, length: nat, inode_bytes: nat) -> bool {
    match tag {
        ADD_RANGE => length == 16,
        DEL_RANGE => length == 12,
        CREAT | LINK | UNLINK => 9 <= length <= 263,
        INODE => length >= 132 && inode_bytes >= 128 && length <= inode_bytes + 4,
        PAD => true,
        TAIL => length >= 8,
        HEAD => length == 8,
        _ => false,
    }
}
pub open spec fn record_from_source(source: Seq<u8>, offset: usize,
    record: RecordView, block_bytes: nat, inode_bytes: nat) -> bool {
    &&& 1024 <= block_bytes <= 65536
    &&& offset as nat + 4 + record.value.len() <= source.len()
    &&& 4 + record.value.len() <= block_bytes - offset as nat % block_bytes
    &&& record.tag as nat == bytes::le16(source, offset as int)
    &&& record.value.len() == bytes::le16(source, offset as int + 2)
    &&& record.value == source.subrange(offset as int + 4, offset as int + 4 + record.value.len())
    &&& value_length_ok(record.tag, record.value.len(), inode_bytes)
}
#[verifier::opaque]
pub open spec fn prefix_crc(source: Seq<u8>, positions: Seq<usize>, count: nat) -> u32
    decreases count,
{
    if count == 0 { 0u32 } else {
        let at = positions[count as int - 1] as int;
        if bytes::le16(source, at) == TAIL {
            0u32
        } else {
            crc::fold(prefix_crc(source, positions, (count - 1) as nat),
                source.subrange(at, at + 4 + bytes::le16(source, at + 2)))
        }
    }
}
pub open spec fn valid_tail(source: Seq<u8>, positions: Seq<usize>, index: nat, tid: u32) -> bool {
    &&& index < positions.len()
    &&& positions[index as int] as nat + 12 <= source.len()
    &&& bytes::le16(source, positions[index as int] as int) == TAIL
    &&& bytes::le32(source, positions[index as int] as int + 4) == tid
    &&& bytes::le32(source, positions[index as int] as int + 8)
        == crc::fold(prefix_crc(source, positions, index),
            source.subrange(positions[index as int] as int, positions[index as int] as int + 8))
}
pub struct ScanView {
    pub source: Seq<u8>, pub positions: Seq<usize>, pub records: Seq<RecordView>,
    pub committed: nat, pub committed_end: nat, pub tid: u32, pub inode_bytes: nat,
    pub block_bytes: nat,
}
#[verifier::opaque]
pub open spec fn checked_prefix(v: ScanView, count: nat) -> bool {
    &&& count <= v.records.len()
    &&& forall|i: int| #![trigger v.records[i]] 0 <= i < count ==> {
        let record = v.records[i];
        &&& record.tag == HEAD ==> bytes::le32(record.value, 0) == 0 && bytes::le32(record.value, 4) == v.tid
        &&& record.tag == TAIL ==> valid_tail(v.source, v.positions, i as nat, v.tid)
    }
}
#[verifier::opaque]
pub open spec fn valid_scan(v: ScanView) -> bool {
    &&& crate::block_size::accepted(v.block_bytes) && 128 <= v.inode_bytes <= 65536
    &&& v.source.len() <= MAX_LOG_BYTES && v.source.len() % v.block_bytes == 0
    &&& v.positions.len() == v.records.len() <= MAX_RECORDS
    &&& v.committed <= v.records.len() && v.committed_end <= v.source.len()
    &&& (forall|i: int| 0 <= i < v.records.len() ==> #[trigger] record_from_source(
        v.source, v.positions[i], v.records[i], v.block_bytes, v.inode_bytes))
    &&& (forall|i: int| 0 < i < v.positions.len() ==> v.positions[i - 1] as nat + 4
        + v.records[i - 1].value.len() <= #[trigger] v.positions[i])
    &&& checked_prefix(v, v.committed)
    &&& if v.committed == 0 { v.committed_end == 0 } else {
        &&& v.records[v.committed as int - 1].tag == TAIL
        &&& valid_tail(v.source, v.positions, (v.committed - 1) as nat, v.tid)
        &&& v.committed_end == v.positions[v.committed as int - 1] as nat + 4
            + v.records[v.committed as int - 1].value.len()
    }
}
proof fn checked_prefix_index(v: ScanView, count: nat, index: int)
    requires checked_prefix(v, count), 0 <= index < count,
    ensures index < v.records.len(),
        v.records[index].tag == HEAD ==> bytes::le32(v.records[index].value, 0) == 0
            && bytes::le32(v.records[index].value, 4) == v.tid,
        v.records[index].tag == TAIL ==> valid_tail(v.source, v.positions, index as nat, v.tid),
{ reveal(checked_prefix); }

proof fn crc_prefix_extension(source: Seq<u8>, before: Seq<usize>, after: Seq<usize>, count: nat)
    requires count <= before.len(), before.len() <= after.len(), before == after.take(before.len() as int),
    ensures prefix_crc(source, before, count) == prefix_crc(source, after, count),
    decreases count,
{
    reveal(prefix_crc);
    if count > 0 { crc_prefix_extension(source, before, after, (count - 1) as nat); }
}
proof fn tail_positions_prefix_frame(source: Seq<u8>, before: Seq<usize>, after: Seq<usize>,
    index: nat, tid: u32)
    requires valid_tail(source, before, index, tid), index < before.len(), before.len() <= after.len(),
        before == after.take(before.len() as int),
    ensures valid_tail(source, after, index, tid),
{
    crc_prefix_extension(source, before, after, index);
    assert(before[index as int] == after[index as int]);
}
proof fn scan_push_preserves_committed(before: ScanView, after: ScanView, offset: usize, record: RecordView)
    requires valid_scan(before), before.records.len() < MAX_RECORDS,
        record_from_source(before.source, offset, record, before.block_bytes, before.inode_bytes),
        before.records.len() > 0 ==> before.positions.last() as nat + 4 + before.records.last().value.len() <= offset,
        after.source == before.source && after.block_bytes == before.block_bytes && after.inode_bytes == before.inode_bytes
            && after.tid == before.tid && after.committed == before.committed && after.committed_end == before.committed_end,
        after.records == before.records.push(record) && after.positions == before.positions.push(offset),
    ensures valid_scan(after),
{
    reveal(valid_scan); reveal(checked_prefix);
    assert(after.positions.take(before.positions.len() as int) =~= before.positions);
    assert forall|i: int| 0 <= i < after.records.len() implies #[trigger] record_from_source(
        after.source, after.positions[i], after.records[i], after.block_bytes, after.inode_bytes) by {
        if i < before.records.len() {
            assert(record_from_source(before.source, before.positions[i], before.records[i], before.block_bytes, before.inode_bytes));
        }
    }
    assert forall|i: int| 0 <= i < after.committed implies {
        let r = after.records[i];
        &&& r.tag == HEAD ==> bytes::le32(r.value, 0) == 0 && bytes::le32(r.value, 4) == after.tid
        &&& r.tag == TAIL ==> #[trigger] valid_tail(after.source, after.positions, i as nat, after.tid)
    } by {
        assert(i < before.records.len() && after.records[i] == before.records[i]);
        checked_prefix_index(before, before.committed, i);
        if after.records[i].tag == HEAD {
            assert(bytes::le32(before.records[i].value, 0) == 0);
            assert(bytes::le32(before.records[i].value, 4) == before.tid);
        }
        if after.records[i].tag == TAIL {
            tail_positions_prefix_frame(before.source, before.positions, after.positions, i as nat, before.tid);
        }
    }
    assert forall|i: int| 0 < i < after.positions.len() implies
        after.positions[i - 1] as nat + 4 + after.records[i - 1].value.len() <= #[trigger] after.positions[i] by {
        if i < before.positions.len() {
            assert(before.positions[i - 1] as nat + 4 + before.records[i - 1].value.len() <= before.positions[i]);
        } else {
            assert(i == before.positions.len());
            assert(after.positions[i] == offset);
        }
    }
    assert(checked_prefix(after, after.committed));
    if before.committed > 0 {
        let last = before.committed as int - 1;
        assert(after.records[last] == before.records[last] && after.positions[last] == before.positions[last]);
        tail_positions_prefix_frame(before.source, before.positions, after.positions, (before.committed - 1) as nat, before.tid);
    }
}

pub proof fn replay_access_is_confined_to_a_checksum_valid_tail(v: ScanView, index: int)
    requires valid_scan(v), 0 <= index < v.committed,
    ensures record_from_source(v.source, v.positions[index], v.records[index], v.block_bytes, v.inode_bytes),
        v.records[v.committed as int - 1].tag == TAIL,
        valid_tail(v.source, v.positions, (v.committed - 1) as nat, v.tid),
        v.positions[index] as nat + 4 + v.records[index].value.len() <= v.source.len(),
{
    reveal(valid_scan);
}


proof fn aligned_block_suffix(length: nat, offset: nat, block: nat)
    requires block > 0, offset < length, length % block == 0,
    ensures 0 < block - offset % block <= length - offset,
{
    let b = block as int; let at = offset as int; let end = length as int;
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(at, b);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(at, b);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(end, b);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(at, end, b);
    if at / b == end / b {
        assert(at >= end) by (nonlinear_arith)
            requires at == b * (at / b) + at % b,
                end == b * (end / b) + end % b, at % b >= 0, end % b == 0,
                at / b == end / b;
    }
    assert(at / b < end / b);
    assert(at + b - at % b <= end) by (nonlinear_arith)
        requires at == b * (at / b) + at % b,
            end == b * (end / b) + end % b, end % b == 0, b > 0, at / b < end / b;
}
proof fn equal_prefix_byte(before: Seq<u8>, after: Seq<u8>, prefix: int, index: int)
    requires 0 <= index < prefix <= before.len(), prefix <= after.len(),
        before.take(prefix) == after.take(prefix),
    ensures before[index] == after[index],
{
    assert(before.take(prefix)[index] == before[index]);
    assert(after.take(prefix)[index] == after[index]);
}
proof fn equal_prefix_span(before: Seq<u8>, after: Seq<u8>, prefix: int, first: int, end: int)
    requires 0 <= first <= end <= prefix <= before.len(), prefix <= after.len(),
        before.take(prefix) == after.take(prefix),
    ensures before.subrange(first, end) == after.subrange(first, end),
{
    assert forall|i: int| 0 <= i < end - first implies
        #[trigger] before.subrange(first, end)[i] == after.subrange(first, end)[i] by {
        equal_prefix_byte(before, after, prefix, first + i);
    }
    assert(before.subrange(first, end) =~= after.subrange(first, end));
}
proof fn equal_prefix_le16(before: Seq<u8>, after: Seq<u8>, prefix: int, word: int)
    requires 0 <= word, word + 2 <= prefix <= before.len(), prefix <= after.len(),
        before.take(prefix) == after.take(prefix),
    ensures bytes::le16(before, word) == bytes::le16(after, word),
{
    equal_prefix_byte(before, after, prefix, word);
    equal_prefix_byte(before, after, prefix, word + 1);
}
proof fn equal_prefix_le32(before: Seq<u8>, after: Seq<u8>, prefix: int, word: int)
    requires 0 <= word, word + 4 <= prefix <= before.len(), prefix <= after.len(),
        before.take(prefix) == after.take(prefix),
    ensures bytes::le32(before, word) == bytes::le32(after, word),
{
    equal_prefix_byte(before, after, prefix, word);
    equal_prefix_byte(before, after, prefix, word + 1);
    equal_prefix_byte(before, after, prefix, word + 2);
    equal_prefix_byte(before, after, prefix, word + 3);
}
proof fn equal_prefix_crc(seed: u32, before: Seq<u8>, after: Seq<u8>, prefix: int, first: int, end: int)
    requires 0 <= first <= end <= prefix <= before.len(), prefix <= after.len(),
        before.take(prefix) == after.take(prefix),
    ensures crc::fold(seed, before.subrange(first, end)) == crc::fold(seed, after.subrange(first, end)),
{
    hide(crc::fold);
    equal_prefix_span(before, after, prefix, first, end);
}
proof fn scan_bounds(v: ScanView)
    requires valid_scan(v),
    ensures v.committed <= v.records.len() <= MAX_RECORDS, 128 <= v.inode_bytes <= 65536,
        v.committed_end <= v.source.len(), v.positions.len() == v.records.len(),
{
    reveal(valid_scan);
}
proof fn checked_scan_record(v: ScanView, index: int)
    requires valid_scan(v), 0 <= index < v.records.len(),
    ensures record_from_source(v.source, v.positions[index], v.records[index], v.block_bytes, v.inode_bytes),
        value_length_ok(v.records[index].tag, v.records[index].value.len(), v.inode_bytes),
        v.committed <= v.records.len() <= MAX_RECORDS,
{
    reveal(valid_scan);
    assert(record_from_source(v.source, v.positions[index], v.records[index], v.block_bytes, v.inode_bytes));
}

fn copy(raw: &[u8]) -> (r: Vec<u8>)
    ensures r@ == raw@,
{
    let mut result = Vec::<u8>::new(); let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len(), result.len() == i, result@ == raw@.take(i as int),
        decreases raw.len() - i,
    { result.push(raw[i]); i += 1; }
    result
}

pub open spec fn encoded16(value: u16) -> Seq<u8> {
    seq![(value % 256) as u8, (value / 256) as u8]
}
proof fn local_writer_frames_reads(before: Seq<u8>, offset: int, data: Seq<u8>)
    requires 0 <= offset, offset + data.len() <= before.len(),
    ensures
        forall|i: int| 0 <= i < before.len() && !(offset <= i < offset + data.len()) ==>
            #[trigger] bytes::splice(before, offset, data)[i] == before[i],
        forall|word: int| 0 <= word && word + 2 <= before.len()
            && (word + 2 <= offset || word >= offset + data.len()) ==>
                #[trigger] bytes::le16(bytes::splice(before, offset, data), word) == bytes::le16(before, word),
        forall|word: int| 0 <= word && word + 4 <= before.len()
            && (word + 4 <= offset || word >= offset + data.len()) ==>
                #[trigger] bytes::le32(bytes::splice(before, offset, data), word) == bytes::le32(before, word),
{
    assert forall|i: int| 0 <= i < before.len() && !(offset <= i < offset + data.len())
        implies #[trigger] bytes::splice(before, offset, data)[i] == before[i] by {
        bytes::splice_frame(before, offset, data, i);
    }
}

fn put16(raw: &mut [u8], offset: usize, value: u16) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r == (offset as int + 2 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, offset as int, encoded16(value)) } else { old(raw)@ },
        r ==> bytes::le16(final(raw)@, offset as int) == value,
        forall|i: int| 0 <= i < old(raw).len() && !(offset <= i < offset as int + 2)
            ==> #[trigger] final(raw)@[i] == old(raw)@[i],
        forall|word: int| 0 <= word && word + 2 <= old(raw).len()
            && (word + 2 <= offset || word >= offset as int + 2) ==>
                #[trigger] bytes::le16(final(raw)@, word) == bytes::le16(old(raw)@, word),
        forall|word: int| 0 <= word && word + 4 <= old(raw).len()
            && (word + 4 <= offset || word >= offset as int + 2) ==>
                #[trigger] bytes::le32(final(raw)@, word) == bytes::le32(old(raw)@, word),
        forall|prefix: int| 0 <= prefix <= offset && prefix <= old(raw).len() ==>
            #[trigger] final(raw)@.take(prefix) == old(raw)@.take(prefix),
{
    let encoded = [(value % 256) as u8, (value / 256) as u8];
    proof { vstd::arithmetic::div_mod::lemma_fundamental_div_mod(value as int, 256); }
    let ghost before = raw@;
    let success = bytes::write_bytes(raw, offset, &encoded);
    proof { if success { local_writer_frames_reads(before, offset as int, encoded@); } }
    proof {
        if success {
            assert forall|prefix: int| 0 <= prefix <= offset && prefix <= before.len()
                implies #[trigger] raw@.take(prefix) == before.take(prefix) by {
                assert(raw@.take(prefix) =~= before.take(prefix));
            }
        }
    }
    success
}
fn put32(raw: &mut [u8], offset: usize, value: u32) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r == (offset as int + 4 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, offset as int, bytes::encoded_le(value)) } else { old(raw)@ },
        r ==> bytes::le32(final(raw)@, offset as int) == value,
        forall|i: int| 0 <= i < old(raw).len() && !(offset <= i < offset as int + 4)
            ==> #[trigger] final(raw)@[i] == old(raw)@[i],
        forall|word: int| 0 <= word && word + 2 <= old(raw).len()
            && (word + 2 <= offset || word >= offset as int + 4) ==>
                #[trigger] bytes::le16(final(raw)@, word) == bytes::le16(old(raw)@, word),
        forall|word: int| 0 <= word && word + 4 <= old(raw).len()
            && (word + 4 <= offset || word >= offset as int + 4) ==>
                #[trigger] bytes::le32(final(raw)@, word) == bytes::le32(old(raw)@, word),
        forall|prefix: int| 0 <= prefix <= offset && prefix <= old(raw).len() ==>
            #[trigger] final(raw)@.take(prefix) == old(raw)@.take(prefix),
{
    let ghost before = raw@;
    let success = bytes::write_le32(raw, offset, value);
    proof { if success { local_writer_frames_reads(before, offset as int, bytes::encoded_le(value)); } }
    proof {
        if success {
            assert forall|prefix: int| 0 <= prefix <= offset && prefix <= before.len()
                implies #[trigger] raw@.take(prefix) == before.take(prefix) by {
                assert(raw@.take(prefix) =~= before.take(prefix));
            }
        }
    }
    success
}

fn copy_span(raw: &mut [u8], offset: usize, data: &[u8]) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r == (offset as int + data.len() <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, offset as int, data@) } else { old(raw)@ },
        r ==> final(raw)@.subrange(offset as int, offset as int + data.len()) == data@,
        forall|prefix: int| 0 <= prefix <= offset && prefix <= old(raw).len() ==>
            #[trigger] final(raw)@.take(prefix) == old(raw)@.take(prefix),
        forall|i: int| 0 <= i < old(raw).len() && !(offset <= i < offset as int + data.len()) ==>
            #[trigger] final(raw)@[i] == old(raw)@[i],
{
    let ghost before = raw@;
    let success = bytes::write_bytes(raw, offset, data);
    proof {
        if success {
            local_writer_frames_reads(before, offset as int, data@);
            assert(raw@.subrange(offset as int, offset as int + data.len()) =~= data@);
            assert forall|prefix: int| 0 <= prefix <= offset && prefix <= before.len()
                implies #[trigger] raw@.take(prefix) == before.take(prefix) by {
                assert(raw@.take(prefix) =~= before.take(prefix));
            }
        }
    }
    success
}
proof fn crc_empty(seed: u32)
    ensures crc::fold(seed, Seq::<u8>::empty()) == seed,
{ reveal(crc::fold); }

pub fn value_length_valid(tag: u16, length: usize, inode_bytes: usize) -> (r: bool)
    ensures r == value_length_ok(tag, length as nat, inode_bytes as nat),
{
    match tag {
        ADD_RANGE => length == 16,
        DEL_RANGE => length == 12,
        CREAT | LINK | UNLINK => 9 <= length && length <= 263,
        INODE => length >= 132 && inode_bytes >= 128 && length - 4 <= inode_bytes,
        PAD => true,
        TAIL => length >= 8,
        HEAD => length == 8,
        _ => false,
    }
}

pub struct Scan {
    records: Vec<Record>, committed: usize, committed_end: usize,
    tid: u32, inode_bytes: usize, stop: Stop,
    source: Ghost<Seq<u8>>, positions: Ghost<Seq<usize>>, block_bytes: Ghost<usize>,
}
impl Scan {
    pub closed spec fn view(&self) -> ScanView {
        ScanView { source: self.source@, positions: self.positions@,
            records: record_views(self.records@), committed: self.committed as nat,
            committed_end: self.committed_end as nat, tid: self.tid,
            inode_bytes: self.inode_bytes as nat, block_bytes: self.block_bytes@ as nat }
    }
    pub open spec fn wf(&self) -> bool { valid_scan(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn scan_transaction(&self) -> (r: u32)
        ensures self.wf(), r == self.view().tid,
    { proof { use_type_invariant(self); } self.tid }
    pub fn scan_committed_records(&self) -> (r: usize)
        ensures self.wf(), r == self.view().committed,
    { proof { use_type_invariant(self); } self.committed }
    pub fn scan_committed_end(&self) -> (r: usize)
        ensures self.wf(), r == self.view().committed_end,
    { proof { use_type_invariant(self); } self.committed_end }
    pub fn scan_stop(&self) -> Stop
        ensures self.wf(),
    { proof { use_type_invariant(self); } self.stop }
    pub fn scanned_record(&self, index: usize) -> (r: Option<&Record>)
        ensures self.wf(), match r {
            Some(record) => index < self.view().committed
                && record.tag == self.view().records[index as int].tag
                && record.value@ == self.view().records[index as int].value,
            None => index >= self.view().committed,
        },
    {
        proof { use_type_invariant(self); reveal(valid_scan); }
        if index >= self.committed || index >= self.records.len() { None }
        else { Some(&self.records[index]) }
    }
}

// Unsealed local state may be mutated or dropped while parsing. It becomes a
// public Scan only through finish_scan after the complete invariant is proved.
struct ScanDraft {
    records: Vec<Record>, committed: usize, committed_end: usize,
    tid: u32, inode_bytes: usize, stop: Stop,
    source: Ghost<Seq<u8>>, positions: Ghost<Seq<usize>>, block_bytes: Ghost<usize>,
}
impl ScanDraft {
    spec fn view(&self) -> ScanView {
        ScanView { source: self.source@, positions: self.positions@,
            records: record_views(self.records@), committed: self.committed as nat,
            committed_end: self.committed_end as nat, tid: self.tid,
            inode_bytes: self.inode_bytes as nat, block_bytes: self.block_bytes@ as nat }
    }
    spec fn wf(&self) -> bool { valid_scan(self.view()) }
}
fn finish_scan(draft: ScanDraft) -> (r: Scan)
    requires draft.wf(),
    ensures r.wf(), r.view() == draft.view(),
{
    let ScanDraft { records, committed, committed_end, tid, inode_bytes, stop,
        source, positions, block_bytes } = draft;
    Scan { records, committed, committed_end, tid, inode_bytes, stop, source, positions, block_bytes }
}

proof fn empty_scan_checked(v: ScanView)
    requires crate::block_size::accepted(v.block_bytes), 128 <= v.inode_bytes <= 65536,
        v.source.len() <= MAX_LOG_BYTES, v.source.len() % v.block_bytes == 0,
        v.records.len() == 0, v.positions.len() == 0, v.committed == 0, v.committed_end == 0,
    ensures valid_scan(v), checked_prefix(v, 0), prefix_crc(v.source, v.positions, 0) == 0,
{
    reveal(valid_scan); reveal(checked_prefix); reveal(prefix_crc);
}
proof fn pending_checked_prefix_frame(before: ScanView, after: ScanView)
    requires checked_prefix(before, before.records.len()),
        after.source == before.source, after.tid == before.tid,
        after.records.len() == before.records.len() + 1,
        after.records.take(before.records.len() as int) == before.records,
        after.positions.len() == before.positions.len() + 1,
        after.positions.take(before.positions.len() as int) == before.positions,
        before.positions.len() == before.records.len(),
    ensures checked_prefix(after, before.records.len()),
{
    reveal(checked_prefix);
    assert forall|i: int| #![trigger after.records[i]] 0 <= i < before.records.len() implies {
        let r = after.records[i];
        &&& r.tag == HEAD ==> bytes::le32(r.value, 0) == 0 && bytes::le32(r.value, 4) == after.tid
        &&& r.tag == TAIL ==> valid_tail(after.source, after.positions, i as nat, after.tid)
    } by {
        assert(after.records[i] == before.records[i]);
        checked_prefix_index(before, before.records.len(), i);
        if after.records[i].tag == TAIL {
            tail_positions_prefix_frame(before.source, before.positions, after.positions, i as nat, before.tid);
        }
    }
    assert(checked_prefix(after, before.records.len()));
}

// This helper owns one complete record transition. A checksum rejection may
// retain the uncommitted record internally; the sealed committed prefix stays
// exactly at its previous valid tail.
fn scan_record_step(result: &mut ScanDraft, raw: &[u8], offset: usize,
    tag: u16, value: &[u8], checksum: u32) -> (r: Result<u32, ()>)
    requires old(result).wf(), old(result).source@ == raw@,
        old(result).records.len() < MAX_RECORDS,
        old(result).positions@.len() == old(result).records.len(),
        checked_prefix(old(result).view(), old(result).records.len() as nat),
        checksum == prefix_crc(raw@, old(result).positions@, old(result).records.len() as nat),
        record_from_source(raw@, offset, RecordView { tag, value: value@ },
            old(result).block_bytes@ as nat, old(result).inode_bytes as nat),
        old(result).records.len() > 0 ==> old(result).positions@.last() as nat + 4
            + record_views(old(result).records@).last().value.len() <= offset,
        tag == HEAD ==> bytes::le32(value@, 0) == 0 && bytes::le32(value@, 4) == old(result).tid,
    ensures final(result).wf(),
        final(result).source@ == old(result).source@,
        final(result).block_bytes@ == old(result).block_bytes@,
        final(result).tid == old(result).tid, final(result).inode_bytes == old(result).inode_bytes,
        record_views(final(result).records@) == record_views(old(result).records@).push(RecordView { tag, value: value@ }),
        final(result).positions@ == old(result).positions@.push(offset),
        final(result).records.len() == old(result).records.len() + 1,
        final(result).positions@.len() == final(result).records.len(),
        final(result).records.len() > 0,
        final(result).positions@[final(result).records.len() as int - 1] == offset,
        final(result).records@[final(result).records.len() as int - 1].value@ == value@,
        final(result).committed <= final(result).records.len(), final(result).committed_end <= raw.len(),
        match r {
            Ok(next_crc) => checked_prefix(final(result).view(), final(result).records.len() as nat)
                && next_crc == prefix_crc(raw@, final(result).positions@, final(result).records.len() as nat),
            Err(()) => final(result).committed == old(result).committed
                && final(result).committed_end == old(result).committed_end,
        },
{
    hide(crc::fold);
    let ghost previous_positions = result.positions@;
    let ghost previous_records = record_views(result.records@);
    let ghost previous_view = result.view();
    proof {
        scan_bounds(previous_view);
        assert(record_from_source(raw@, offset, RecordView { tag, value: value@ },
            previous_view.block_bytes, previous_view.inode_bytes));
        assert(offset as int + 4 + value.len() <= raw.len());
    }
    result.records.push(Record { tag, value: copy(value) });
    result.positions = Ghost(previous_positions.push(offset));
    proof {
        assert(result.positions@.take(previous_positions.len() as int) =~= previous_positions);
        assert(result.positions@[result.records.len() as int - 1] == offset);
        assert(result.records@[result.records.len() as int - 1].value@ == value@);
        crc_prefix_extension(raw@, previous_positions, result.positions@, previous_positions.len());
        assert(record_from_source(raw@, offset, record_views(result.records@).last(),
            result.block_bytes@ as nat, result.inode_bytes as nat));
        assert(record_views(result.records@) =~= previous_records.push(record_views(result.records@).last()));
        scan_push_preserves_committed(previous_view, result.view(), offset, record_views(result.records@).last());
        assert(result.view().records.take(previous_records.len() as int) =~= previous_records);
        pending_checked_prefix_frame(previous_view, result.view());
    }
    let end = offset + 4 + value.len();
    let next_crc;
    if tag == TAIL {
        // Only the TLV header and TID participate in a TAIL checksum.
        let tail_crc = crc::crc32c(checksum, &raw[offset..offset + 8]);
        if bytes::read_le32(value, 0).unwrap() != result.tid
            || bytes::read_le32(value, 4).unwrap() != tail_crc {
            proof { scan_bounds(result.view()); }
            return Err(());
        }
        proof {
            assert(valid_tail(raw@, result.positions@, previous_records.len(), result.tid));
            reveal(checked_prefix);
            assert(checked_prefix(result.view(), result.records.len() as nat));
        }
        result.committed = result.records.len(); result.committed_end = end;
        next_crc = 0;
    } else {
        next_crc = crc::crc32c(checksum, &raw[offset..end]);
    }
    proof {
        reveal(prefix_crc); reveal(checked_prefix); reveal(valid_scan);
        assert(checked_prefix(result.view(), result.records.len() as nat));
        assert(next_crc == prefix_crc(raw@, result.positions@, result.records.len() as nat));
    }
    Ok(next_crc)
}

/// Scan a complete captured fast-commit area. CRC starts at zero and resets
/// after each tail. Only records through a matching checksum-valid TAIL are
/// exposed. Exhausted resources reject the area rather than silently losing a
/// later committed prefix. A malformed suffix can retain a prior valid tail.
pub fn scan(raw: &[u8], block_bytes: usize, inode_bytes: usize,
    expected_tid: u32, record_budget: usize) -> (r: Result<Scan, Error>)
    ensures match r {
        Ok(scanned) => scanned.wf() && scanned.view().source == raw@
            && scanned.view().tid == expected_tid && scanned.view().block_bytes == block_bytes
            && scanned.view().inode_bytes == inode_bytes && scanned.view().records.len() <= record_budget,
        Err(_) => true,
    },
{
    if !crate::block_size::valid(block_bytes) || inode_bytes < 128 || inode_bytes > 65536
        || raw.len() > MAX_LOG_BYTES || raw.len() % block_bytes != 0 {
        return Err(Error::Geometry);
    }
    if record_budget == 0 || record_budget > MAX_RECORDS { return Err(Error::ResourceLimit); }
    let mut result = ScanDraft { records: Vec::new(), committed: 0, committed_end: 0,
        tid: expected_tid, inode_bytes, stop: Stop::EndOfArea,
        source: Ghost(raw@), positions: Ghost(Seq::empty()), block_bytes: Ghost(block_bytes) };
    proof { empty_scan_checked(result.view()); }
    if raw.len() == 0 { result.stop = Stop::EmptyArea; return Ok(finish_scan(result)); }
    if bytes::read_le16(raw, 0).unwrap() != HEAD {
        result.stop = Stop::EmptyArea; return Ok(finish_scan(result));
    }
    let mut offset = 0usize; let mut checksum = 0u32;
    while offset < raw.len()
        invariant offset <= raw.len() <= MAX_LOG_BYTES, raw.len() % block_bytes == 0,
            1024 <= block_bytes <= 65536, result.records.len() <= record_budget <= MAX_RECORDS,
            result.committed <= result.records.len(), result.committed_end <= raw.len(),
            result.wf(), result.source@ == raw@, result.block_bytes@ == block_bytes,
            result.tid == expected_tid, result.inode_bytes == inode_bytes,
            result.positions@.len() == result.records.len(),
            result.records.len() == 0 ==> offset == 0,
            result.records.len() > 0 ==> result.positions@[result.records.len() as int - 1] as nat
                + 4 + result.records@[result.records.len() as int - 1].value@.len() <= offset,
            checked_prefix(result.view(), result.records.len() as nat),
            checksum == prefix_crc(raw@, result.positions@, result.records.len() as nat),
        decreases raw.len() - offset,
    {
        proof { aligned_block_suffix(raw.len() as nat, offset as nat, block_bytes as nat); }
        let remaining = block_bytes - offset % block_bytes;
        assert(remaining > 0 && remaining <= raw.len() - offset);
        if remaining < 4 {
            proof {
                if result.records.len() == 0 {
                    assert(offset == 0);
                    vstd::arithmetic::div_mod::lemma_small_mod(0nat, block_bytes as nat);
                    assert(offset % block_bytes == 0);
                    assert(remaining == block_bytes);
                    assert(remaining >= 1024);
                }
                assert(result.records.len() > 0);
            }
            offset += remaining;
            continue;
        }
        let tag = bytes::read_le16(raw, offset).unwrap();
        let length = bytes::read_le16(raw, offset + 2).unwrap() as usize;
        if length > remaining - 4 || !value_length_valid(tag, length, inode_bytes) {
            if result.committed == 0 { return Err(Error::Malformed); }
            result.stop = Stop::TornSuffix; return Ok(finish_scan(result));
        }
        if result.records.len() >= record_budget { return Err(Error::ResourceLimit); }
        let end = offset + 4 + length;
        let value = &raw[offset + 4..end];
        if tag == HEAD {
            if bytes::read_le32(value, 0).unwrap() != 0 { return Err(Error::UnsupportedFeatures); }
            if bytes::read_le32(value, 4).unwrap() != expected_tid {
                result.stop = Stop::DifferentTransaction; return Ok(finish_scan(result));
            }
        }
        match scan_record_step(&mut result, raw, offset, tag, value, checksum) {
            Ok(next_crc) => { checksum = next_crc; }
            Err(()) => {
                if result.committed == 0 { return Err(Error::BadChecksum); }
                result.stop = Stop::TornSuffix; return Ok(finish_scan(result));
            }
        }
        assert(result.positions@[result.records.len() as int - 1] as nat + 4
            + result.records@[result.records.len() as int - 1].value@.len() == end);
        offset = end;
    }
    Ok(finish_scan(result))
}

pub struct SegmentView { pub begin: nat, pub tail: nat, pub end: nat }
#[verifier::opaque]
pub open spec fn segment_valid(raw: Seq<u8>, segment: SegmentView, tid: u32) -> bool {
    &&& segment.begin <= segment.tail
    &&& segment.tail + 12 <= segment.end <= raw.len()
    &&& bytes::le16(raw, segment.tail as int) == TAIL
    &&& bytes::le16(raw, segment.tail as int + 2) == segment.end - segment.tail - 4
    &&& bytes::le32(raw, segment.tail as int + 4) == tid
    &&& bytes::le32(raw, segment.tail as int + 8)
        == crc::fold(0, raw.subrange(segment.begin as int, segment.tail as int + 8))
}
proof fn segment_checked(raw: Seq<u8>, segment: SegmentView, tid: u32)
    requires segment.begin <= segment.tail, segment.tail + 12 <= segment.end <= raw.len(),
        bytes::le16(raw, segment.tail as int) == TAIL,
        bytes::le16(raw, segment.tail as int + 2) == segment.end - segment.tail - 4,
        bytes::le32(raw, segment.tail as int + 4) == tid,
        bytes::le32(raw, segment.tail as int + 8)
            == crc::fold(0, raw.subrange(segment.begin as int, segment.tail as int + 8)),
    ensures segment_valid(raw, segment, tid),
{ reveal(segment_valid); }
proof fn segment_prefix_frame(before: Seq<u8>, after: Seq<u8>, segment: SegmentView, tid: u32, prefix: nat)
    requires segment_valid(before, segment, tid), segment.end <= prefix <= before.len(), prefix <= after.len(),
        before.take(prefix as int) == after.take(prefix as int),
    ensures segment_valid(after, segment, tid),
{
    hide(crc::fold);
    reveal(segment_valid);
    equal_prefix_span(before, after, prefix as int, segment.begin as int, segment.tail as int + 8);
    equal_prefix_le16(before, after, prefix as int, segment.tail as int);
    equal_prefix_le16(before, after, prefix as int, segment.tail as int + 2);
    equal_prefix_le32(before, after, prefix as int, segment.tail as int + 4);
    equal_prefix_le32(before, after, prefix as int, segment.tail as int + 8);
}

pub struct BuilderView {
    pub raw: Seq<u8>, pub cursor: nat, pub checksum: u32, pub records: nat,
    pub committed_end: nat, pub pending: nat, pub tid: u32,
    pub block_bytes: nat, pub inode_bytes: nat, pub byte_budget: nat,
    pub segments: Seq<SegmentView>,
}
#[verifier::opaque]
pub open spec fn valid_builder(v: BuilderView) -> bool {
    &&& crate::block_size::accepted(v.block_bytes) && 128 <= v.inode_bytes <= 65536
    &&& v.block_bytes <= v.byte_budget <= MAX_LOG_BYTES
    &&& v.block_bytes <= v.raw.len() <= v.byte_budget && v.raw.len() % v.block_bytes == 0
    &&& v.committed_end <= v.cursor <= v.raw.len() && v.cursor >= 12
    &&& (v.cursor == v.raw.len() ==> v.pending == 0 && v.committed_end == v.raw.len())
    &&& v.raw.len() - v.cursor < v.block_bytes
    &&& (v.cursor == v.raw.len() || v.raw.len() - v.cursor >= 4)
    &&& v.committed_end % v.block_bytes == 0
    &&& 1 <= v.records <= MAX_RECORDS && v.pending <= v.records
    &&& (v.pending == 0 && v.committed_end != 0 ==> v.cursor == v.committed_end)
    &&& v.checksum == crc::fold(0, v.raw.subrange(v.committed_end as int, v.cursor as int))
    &&& (forall|i: int| v.cursor <= i < v.raw.len() ==> #[trigger] v.raw[i] == 0)
    &&& bytes::le16(v.raw, 0) == HEAD && bytes::le16(v.raw, 2) == 8
    &&& bytes::le32(v.raw, 4) == 0 && bytes::le32(v.raw, 8) == v.tid
    &&& if v.committed_end == 0 { v.segments.len() == 0 } else {
        v.segments.len() > 0 && v.segments.last().end == v.committed_end
    }
    &&& (forall|i: int| #![trigger v.segments[i]] 0 <= i < v.segments.len() ==> {
        &&& segment_valid(v.raw, v.segments[i], v.tid)
        &&& v.segments[i].end <= v.committed_end && v.segments[i].end % v.block_bytes == 0
        &&& v.segments[i].begin == if i == 0 { 0nat } else { v.segments[i - 1].end }
    })
}
proof fn crc_adjacent_subranges(seed: u32, raw: Seq<u8>, first: int, middle: int, end: int)
    requires 0 <= first <= middle <= end <= raw.len(),
    ensures crc::fold(crc::fold(seed, raw.subrange(first, middle)), raw.subrange(middle, end))
        == crc::fold(seed, raw.subrange(first, end)),
{
    assert(raw.subrange(first, middle) + raw.subrange(middle, end) =~= raw.subrange(first, end));
    crc::streaming(seed, raw.subrange(first, middle), raw.subrange(middle, end));
}

// Writes one exact TLV in place and advances the running CRC over those bytes.
// This helper cannot grow buffers or grant any storage or allocation authority.
fn write_record_bytes(raw: &mut [u8], start: usize, at: usize, checksum: u32,
    tag: u16, value: &[u8]) -> (r: (usize, u32))
    requires start <= at, at as int + 4 + value.len() <= old(raw).len(),
        value.len() <= 65535,
        checksum == crc::fold(0, old(raw)@.subrange(start as int, at as int)),
    ensures final(raw).len() == old(raw).len(), r.0 == at as int + 4 + value.len(),
        bytes::le16(final(raw)@, at as int) == tag,
        bytes::le16(final(raw)@, at as int + 2) == value.len(),
        final(raw)@.subrange(at as int + 4, r.0 as int) == value@,
        r.1 == crc::fold(0, final(raw)@.subrange(start as int, r.0 as int)),
        forall|prefix: int| 0 <= prefix <= at ==>
            #[trigger] final(raw)@.take(prefix) == old(raw)@.take(prefix),
        forall|i: int| 0 <= i < old(raw).len() && (i < at || i >= r.0) ==>
            #[trigger] final(raw)@[i] == old(raw)@[i],
{
    hide(crc::fold);
    let ghost before = raw@;
    put16(raw, at, tag);
    put16(raw, at + 2, value.len() as u16);
    let ghost before_copy = raw@;
    proof {
        equal_prefix_crc(0, before, raw@, at as int, start as int, at as int);
    }
    let copied = copy_span(raw, at + 4, value);
    assert(copied);
    proof {
        equal_prefix_crc(0, before_copy, raw@, at as int + 4, start as int, at as int);
        equal_prefix_le16(before_copy, raw@, at as int + 4, at as int);
        equal_prefix_le16(before_copy, raw@, at as int + 4, at as int + 2);
    }
    let end = at + 4 + value.len();
    proof { crc_adjacent_subranges(0, raw@, start as int, at as int, end as int); }
    let next_crc = crc::crc32c(checksum, &raw[at..end]);
    proof {
        assert forall|prefix: int| 0 <= prefix <= at implies
            #[trigger] raw@.take(prefix) == before.take(prefix) by {
            assert(before_copy.take(prefix) == before.take(prefix));
        }
        assert forall|i: int| 0 <= i < before.len() && (i < at || i >= end) implies
            #[trigger] raw@[i] == before[i] by {
            assert(before_copy[i] == before[i]);
        }
    }
    (end, next_crc)
}

// PAD consumes the captured suffix; its payload bytes are retained verbatim.
// The running CRC includes its whole TLV, including that unchanged payload.
fn write_pad_bytes(raw: &mut [u8], begin: usize, at: usize, checksum: u32) -> (r: u32)
    requires begin <= at, at as int + 4 <= old(raw).len(),
        old(raw).len() - at <= 65536,
        checksum == crc::fold(0, old(raw)@.subrange(begin as int, at as int)),
    ensures final(raw).len() == old(raw).len(),
        bytes::le16(final(raw)@, at as int) == PAD,
        bytes::le16(final(raw)@, at as int + 2) == final(raw).len() - at - 4,
        r == crc::fold(0, final(raw)@.subrange(begin as int, final(raw).len() as int)),
        forall|prefix: int| 0 <= prefix <= at ==>
            #[trigger] final(raw)@.take(prefix) == old(raw)@.take(prefix),
        forall|i: int| 0 <= i < old(raw).len() && (i < at || i >= at as int + 4) ==>
            #[trigger] final(raw)@[i] == old(raw)@[i],
{
    hide(crc::fold);
    let ghost before = raw@;
    let length = raw.len() - at - 4;
    put16(raw, at, PAD);
    put16(raw, at + 2, length as u16);
    proof {
        assert(raw@.take(at as int) == before.take(at as int));
        equal_prefix_crc(0, before, raw@, at as int, begin as int, at as int);
        crc_adjacent_subranges(0, raw@, begin as int, at as int, raw.len() as int);
        assert forall|prefix: int| 0 <= prefix <= at implies
            #[trigger] raw@.take(prefix) == before.take(prefix) by {}
        assert forall|i: int| 0 <= i < before.len() && (i < at || i >= at as int + 4) implies
            #[trigger] raw@[i] == before[i] by {}
    }
    crc::crc32c(checksum, &raw[at..])
}

// A TAIL seals the segment ending at the captured buffer end. Its CRC covers
// the prior segment and exactly the TAIL header plus TID, excluding the stored
// CRC word and all TAIL padding.
fn write_tail_bytes(raw: &mut [u8], begin: usize, at: usize, checksum: u32, tid: u32)
    requires begin <= at, at as int + 12 <= old(raw).len(),
        old(raw).len() - at <= 65536,
        checksum == crc::fold(0, old(raw)@.subrange(begin as int, at as int)),
    ensures final(raw).len() == old(raw).len(),
        segment_valid(final(raw)@, SegmentView { begin: begin as nat, tail: at as nat,
            end: final(raw).len() as nat }, tid),
        forall|prefix: int| 0 <= prefix <= at ==>
            #[trigger] final(raw)@.take(prefix) == old(raw)@.take(prefix),
        forall|i: int| 0 <= i < old(raw).len() && (i < at || i >= at as int + 12) ==>
            #[trigger] final(raw)@[i] == old(raw)@[i],
{
    hide(crc::fold);
    let ghost before = raw@;
    let length = raw.len() - at - 4;
    put16(raw, at, TAIL);
    put16(raw, at + 2, length as u16);
    put32(raw, at + 4, tid);
    proof {
        assert(raw@.take(at as int) == before.take(at as int));
        equal_prefix_crc(0, before, raw@, at as int, begin as int, at as int);
        crc_adjacent_subranges(0, raw@, begin as int, at as int, at as int + 8);
    }
    let tail_crc = crc::crc32c(checksum, &raw[at..at + 8]);
    let ghost before_crc_word = raw@;
    put32(raw, at + 8, tail_crc);
    proof {
        equal_prefix_crc(0, before_crc_word, raw@, at as int + 8, begin as int, at as int + 8);
        segment_checked(raw@, SegmentView { begin: begin as nat, tail: at as nat,
            end: raw.len() as nat }, tid);
        assert forall|prefix: int| 0 <= prefix <= at implies
            #[trigger] raw@.take(prefix) == before.take(prefix) by {
            assert(before_crc_word.take(prefix) == before.take(prefix));
        }
        assert forall|i: int| 0 <= i < before.len() && (i < at || i >= at as int + 12) implies
            #[trigger] raw@[i] == before[i] by {
            assert(before_crc_word[i] == before[i]);
        }
    }
}

proof fn splice_prefix(before: Seq<u8>, offset: nat, data: Seq<u8>, length: nat)
    requires length <= offset, offset + data.len() <= before.len(),
    ensures bytes::splice(before, offset as int, data).take(length as int) == before.take(length as int),
{
    assert(bytes::splice(before, offset as int, data).take(length as int) =~= before.take(length as int));
}
proof fn sealed_segments_frame(before: Seq<u8>, after: Seq<u8>,
    segments: Seq<SegmentView>, tid: u32, prefix: nat)
    requires prefix <= before.len(), prefix <= after.len(),
        before.take(prefix as int) == after.take(prefix as int),
        forall|i: int| #![trigger segments[i]] 0 <= i < segments.len() ==> segment_valid(before, segments[i], tid)
            && segments[i].end <= prefix,
    ensures forall|i: int| #![trigger segments[i]] 0 <= i < segments.len() ==> segment_valid(after, segments[i], tid),
{
    assert forall|i: int| 0 <= i < segments.len() implies #[trigger] segment_valid(after, segments[i], tid) by {
        assert(segment_valid(before, segments[i], tid) && segments[i].end <= prefix);
        segment_prefix_frame(before, after, segments[i], tid, prefix);
    }
}
pub proof fn every_exposed_builder_segment_has_its_exact_tail_crc(v: BuilderView, index: int)
    requires valid_builder(v), 0 <= index < v.segments.len(),
    ensures segment_valid(v.raw.take(v.committed_end as int), v.segments[index], v.tid),
{
    reveal(valid_builder);
    assert(v.raw.take(v.committed_end as int).take(v.committed_end as int) =~= v.raw.take(v.committed_end as int));
    sealed_segments_frame(v.raw, v.raw.take(v.committed_end as int), v.segments, v.tid, v.committed_end);
}

spec fn builder_config_same(before: BuilderView, after: BuilderView) -> bool {
    after.tid == before.tid && after.block_bytes == before.block_bytes
        && after.inode_bytes == before.inode_bytes && after.byte_budget == before.byte_budget
}
proof fn builder_scalar_facts(v: BuilderView)
    requires valid_builder(v),
    ensures crate::block_size::accepted(v.block_bytes), 128 <= v.inode_bytes <= 65536,
        v.block_bytes <= v.byte_budget <= MAX_LOG_BYTES,
        v.block_bytes <= v.raw.len() <= v.byte_budget, v.raw.len() % v.block_bytes == 0,
        v.committed_end <= v.cursor <= v.raw.len(), v.cursor >= 12,
        v.cursor == v.raw.len() ==> v.pending == 0 && v.committed_end == v.raw.len(),
        v.raw.len() - v.cursor < v.block_bytes,
        v.cursor == v.raw.len() || v.raw.len() - v.cursor >= 4,
        v.committed_end % v.block_bytes == 0, 1 <= v.records <= MAX_RECORDS, v.pending <= v.records,
        v.pending == 0 && v.committed_end != 0 ==> v.cursor == v.committed_end,
        v.checksum == crc::fold(0, v.raw.subrange(v.committed_end as int, v.cursor as int)),
        forall|i: int| v.cursor <= i < v.raw.len() ==> #[trigger] v.raw[i] == 0,
{ reveal(valid_builder); }
proof fn completed_builder_exhausts_bytes(v: BuilderView)
    requires valid_builder(v), v.committed_end > 0, v.pending == 0, v.cursor == v.committed_end,
    ensures v.committed_end == v.raw.len(),
{
    builder_scalar_facts(v);
    if v.committed_end < v.raw.len() {
        aligned_block_suffix(v.raw.len(), v.committed_end, v.block_bytes);
        assert(v.block_bytes - v.committed_end % v.block_bytes == v.block_bytes);
        assert(v.block_bytes <= v.raw.len() - v.cursor);
        assert(false);
    }
    reveal(valid_builder);
    assert(v.segments.len() > 0);
    every_exposed_builder_segment_has_its_exact_tail_crc(v, v.segments.len() as int - 1);
}

proof fn builder_append_closed(before: BuilderView, after: BuilderView)
    requires valid_builder(before), builder_config_same(before, after),
        before.raw.len() <= after.raw.len() <= after.byte_budget,
        after.raw.len() % after.block_bytes == 0,
        after.committed_end == before.committed_end && after.segments == before.segments,
        before.cursor < after.cursor && after.cursor + 4 <= after.raw.len(),
        after.raw.len() - after.cursor < after.block_bytes,
        before.records < after.records <= MAX_RECORDS, after.pending == before.pending + 1,
        after.raw.take(before.cursor as int) == before.raw.take(before.cursor as int),
        after.checksum == crc::fold(0, after.raw.subrange(after.committed_end as int, after.cursor as int)),
        forall|i: int| after.cursor <= i < after.raw.len() ==> #[trigger] after.raw[i] == 0,
    ensures valid_builder(after),
{
    hide(crc::fold);
    reveal(valid_builder); reveal(builder_config_same);
    equal_prefix_span(before.raw, after.raw, before.cursor as int, 0, before.committed_end as int);
    assert(before.raw.take(before.committed_end as int) =~= after.raw.take(before.committed_end as int));
    sealed_segments_frame(before.raw, after.raw, before.segments, before.tid, before.committed_end);
    equal_prefix_le16(before.raw, after.raw, before.cursor as int, 0);
    equal_prefix_le16(before.raw, after.raw, before.cursor as int, 2);
    equal_prefix_le32(before.raw, after.raw, before.cursor as int, 4);
    equal_prefix_le32(before.raw, after.raw, before.cursor as int, 8);
}
proof fn builder_commit_closed(before: BuilderView, after: BuilderView, tail: SegmentView)
    requires valid_builder(before), builder_config_same(before, after),
        before.raw.len() <= after.raw.len() <= after.byte_budget,
        after.raw.len() % after.block_bytes == 0,
        after.cursor == after.raw.len() && after.committed_end == after.raw.len(),
        after.pending == 0 && after.checksum == 0,
        before.records < after.records <= MAX_RECORDS,
        after.raw.take(before.cursor as int) == before.raw.take(before.cursor as int),
        after.segments == before.segments.push(tail), tail.begin == before.committed_end,
        tail.end == after.raw.len(), segment_valid(after.raw, tail, after.tid),
    ensures valid_builder(after),
{
    hide(crc::fold);
    reveal(valid_builder); reveal(builder_config_same);
    equal_prefix_span(before.raw, after.raw, before.cursor as int, 0, before.committed_end as int);
    assert(before.raw.take(before.committed_end as int) =~= after.raw.take(before.committed_end as int));
    sealed_segments_frame(before.raw, after.raw, before.segments, before.tid, before.committed_end);
    equal_prefix_le16(before.raw, after.raw, before.cursor as int, 0);
    equal_prefix_le16(before.raw, after.raw, before.cursor as int, 2);
    equal_prefix_le32(before.raw, after.raw, before.cursor as int, 4);
    equal_prefix_le32(before.raw, after.raw, before.cursor as int, 8);
    crc_empty(0);
    assert(after.raw.subrange(after.cursor as int, after.cursor as int) =~= Seq::<u8>::empty());
    assert forall|i: int| 0 <= i < after.segments.len() implies {
        &&& #[trigger] segment_valid(after.raw, after.segments[i], after.tid)
        &&& after.segments[i].end <= after.committed_end && after.segments[i].end % after.block_bytes == 0
        &&& after.segments[i].begin == if i == 0 { 0nat } else { after.segments[i - 1].end }
    } by {
        if i < before.segments.len() {
            assert(after.segments[i] == before.segments[i]);
            assert(segment_valid(after.raw, before.segments[i], before.tid));
        } else {
            assert(i == before.segments.len() && after.segments[i] == tail);
            if i == 0 { assert(before.committed_end == 0); }
            else { assert(before.segments.last().end == before.committed_end); }
        }
    }
}

pub struct Builder {
    raw: Vec<u8>, cursor: usize, checksum: u32, records: usize,
    committed_end: usize, pending_records: usize,
    tid: u32, block_bytes: usize, inode_bytes: usize, byte_budget: usize,
    segments: Ghost<Seq<SegmentView>>,
}

// Consuming a sealed builder transfers its bytes into this private draft.
// Every ordinary outcome is checked again before a Builder is returned.
struct BuilderDraft {
    raw: Vec<u8>, cursor: usize, checksum: u32, records: usize,
    committed_end: usize, pending_records: usize,
    tid: u32, block_bytes: usize, inode_bytes: usize, byte_budget: usize,
    segments: Ghost<Seq<SegmentView>>,
}
impl BuilderDraft {
    spec fn view(&self) -> BuilderView {
        BuilderView { raw: self.raw@, cursor: self.cursor as nat, checksum: self.checksum,
            records: self.records as nat, committed_end: self.committed_end as nat,
            pending: self.pending_records as nat, tid: self.tid, block_bytes: self.block_bytes as nat,
            inode_bytes: self.inode_bytes as nat, byte_budget: self.byte_budget as nat, segments: self.segments@ }
    }
    spec fn wf(&self) -> bool { valid_builder(self.view()) }

    fn append_raw(&mut self, tag: u16, value: &[u8]) -> (r: Result<(), Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
            final(self).view().tid == old(self).view().tid
                && final(self).view().block_bytes == old(self).view().block_bytes
                && final(self).view().inode_bytes == old(self).view().inode_bytes
                && final(self).view().byte_budget == old(self).view().byte_budget
                && final(self).view().segments == old(self).view().segments,
            final(self).view().committed_end == old(self).view().committed_end,
            final(self).view().raw.take(old(self).view().committed_end as int)
                == old(self).view().raw.take(old(self).view().committed_end as int),
            match r {
                Ok(()) => final(self).view().pending == old(self).view().pending + 1,
                Err(_) => final(self).view() == old(self).view(),
            },
    {
        hide(crc::fold);
        proof { builder_scalar_facts(self.view()); }
        let ghost before = self.view();
        if tag < ADD_RANGE || tag > INODE || !value_length_valid(tag, value.len(), self.inode_bytes) {
            return Err(Error::Malformed);
        }
        if value.len() > 65535 || value.len() + 4 > self.block_bytes - 4 {
            return Err(Error::RecordTooLarge);
        }
        let size = value.len() + 4;
        let at_end = self.cursor == self.raw.len();
        let remaining = if at_end { self.block_bytes } else { self.raw.len() - self.cursor };
        let needs_pad = !at_end && size > remaining - 4;
        let added_records = if needs_pad { 2usize } else { 1usize };
        if self.records > MAX_RECORDS - added_records - 2 { return Err(Error::ResourceLimit); }
        if (at_end || needs_pad)
            && (self.raw.len() > self.byte_budget || self.block_bytes > self.byte_budget - self.raw.len()) {
            return Err(Error::ResourceLimit);
        }
        if needs_pad {
            let ghost before_pad = self.raw@;
            put16(&mut self.raw, self.cursor, PAD);
            put16(&mut self.raw, self.cursor + 2, (remaining - 4) as u16);
            proof {
                assert(self.raw@.take(self.cursor as int) == before_pad.take(self.cursor as int));
                equal_prefix_crc(0, before_pad, self.raw@, self.cursor as int,
                    before.committed_end as int, self.cursor as int);
                assert(self.checksum == crc::fold(0, self.raw@.subrange(before.committed_end as int, self.cursor as int)));
                crc_adjacent_subranges(0, self.raw@, before.committed_end as int, self.cursor as int, self.raw.len() as int);
            }
            self.checksum = crc::crc32c(self.checksum, &self.raw[self.cursor..]);
            self.cursor = self.raw.len(); self.records += 1;
        }
        if at_end || needs_pad {
            let ghost before_growth = self.raw@;
            if !grow_block(&mut self.raw, self.block_bytes, self.byte_budget) { return Err(Error::ResourceLimit); }
            proof {
                equal_prefix_crc(0, before_growth, self.raw@, before_growth.len() as int,
                    before.committed_end as int, self.cursor as int);
            }
        }
        assert(self.raw.len() - self.cursor >= size + 4);
        assert(self.raw.len() - self.cursor <= self.block_bytes);
        assert forall|j: int| self.cursor <= j < self.raw.len() implies #[trigger] self.raw@[j] == 0 by {}
        let ghost before_record = self.raw@;
        let (end, next_crc) = write_record_bytes(&mut self.raw, self.committed_end, self.cursor,
            self.checksum, tag, value);
        self.checksum = next_crc;
        assert(self.raw@.take(before.cursor as int) == before.raw.take(before.cursor as int));
        self.cursor = end; self.records += 1; self.pending_records += 1;
        proof {
            assert forall|j: int| self.cursor <= j < self.raw.len() implies #[trigger] self.raw@[j] == 0 by {
                assert(before_record[j] == 0);
            }
            builder_append_closed(before, self.view());
        }
        Ok(())
    }

    fn commit_raw(&mut self) -> (r: Result<(), Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
            final(self).view().tid == old(self).view().tid
                && final(self).view().block_bytes == old(self).view().block_bytes
                && final(self).view().inode_bytes == old(self).view().inode_bytes
                && final(self).view().byte_budget == old(self).view().byte_budget,
            final(self).view().raw.take(old(self).view().committed_end as int)
                == old(self).view().raw.take(old(self).view().committed_end as int),
            match r {
                Ok(()) => final(self).view().committed_end == final(self).view().raw.len()
                    && final(self).view().pending == 0
                    && final(self).view().segments.len() == old(self).view().segments.len() + 1,
                Err(_) => final(self).view() == old(self).view(),
            },
    {
        hide(crc::fold);
        proof { builder_scalar_facts(self.view()); }
        let ghost before = self.view();
        if self.pending_records == 0 && self.committed_end != 0 { return Err(Error::NoChanges); }
        let remaining = self.raw.len() - self.cursor;
        let needs_pad = remaining < 16;
        let added_records = if needs_pad { 2usize } else { 1usize };
        if self.records > MAX_RECORDS - added_records { return Err(Error::ResourceLimit); }
        if needs_pad && (self.raw.len() > self.byte_budget
            || self.block_bytes > self.byte_budget - self.raw.len()) { return Err(Error::ResourceLimit); }
        if needs_pad {
            self.checksum = write_pad_bytes(&mut self.raw, self.committed_end, self.cursor, self.checksum);
            self.cursor = self.raw.len(); self.records += 1;
            let ghost before_growth = self.raw@;
            if !grow_block(&mut self.raw, self.block_bytes, self.byte_budget) { return Err(Error::ResourceLimit); }
            proof {
                equal_prefix_crc(0, before_growth, self.raw@, before_growth.len() as int,
                    before.committed_end as int, self.cursor as int);
            }
        }
        let ghost tail_position = self.cursor;
        write_tail_bytes(&mut self.raw, self.committed_end, self.cursor, self.checksum, self.tid);
        self.records += 1; self.checksum = 0; self.cursor = self.raw.len();
        self.committed_end = self.raw.len(); self.pending_records = 0;
        assert(self.raw@.take(before.committed_end as int) == before.raw.take(before.committed_end as int));
        self.segments = Ghost(before.segments.push(SegmentView {
            begin: before.committed_end, tail: tail_position as nat, end: self.committed_end as nat }));
        proof {
            assert(self.raw@.take(before.cursor as int) == before.raw.take(before.cursor as int));
            builder_commit_closed(before, self.view(), SegmentView {
                begin: before.committed_end, tail: tail_position as nat, end: self.committed_end as nat });
        }
        Ok(())
    }

}

fn builder_into_draft(owner: Builder) -> (r: BuilderDraft)
    ensures owner.wf(), r.wf(), r.view() == owner.view(),
{
    proof { use_type_invariant(&owner); }
    let Builder { raw, cursor, checksum, records, committed_end, pending_records,
        tid, block_bytes, inode_bytes, byte_budget, segments } = owner;
    BuilderDraft { raw, cursor, checksum, records, committed_end, pending_records,
        tid, block_bytes, inode_bytes, byte_budget, segments }
}
fn finish_builder(draft: BuilderDraft) -> (r: Builder)
    requires draft.wf(),
    ensures r.wf(), r.view() == draft.view(),
{
    let BuilderDraft { raw, cursor, checksum, records, committed_end, pending_records,
        tid, block_bytes, inode_bytes, byte_budget, segments } = draft;
    Builder { raw, cursor, checksum, records, committed_end, pending_records,
        tid, block_bytes, inode_bytes, byte_budget, segments }
}

fn grow(raw: &mut Vec<u8>, block_bytes: usize, byte_budget: usize) -> (r: bool)
    ensures r == (old(raw).len() <= byte_budget && block_bytes <= byte_budget - old(raw).len()),
        final(raw)@ == if r { old(raw)@ + Seq::new(block_bytes as nat, |i: int| 0u8) } else { old(raw)@ },
        final(raw).len() as nat <= if r { byte_budget as nat } else { old(raw).len() as nat },
        forall|prefix: int| 0 <= prefix <= old(raw).len() ==>
        #[trigger] final(raw)@.take(prefix) == old(raw)@.take(prefix),

{
    let ghost before = raw@;
    if raw.len() > byte_budget || block_bytes > byte_budget - raw.len() { return false; }
    let mut i = 0usize;
    while i < block_bytes
        invariant i <= block_bytes, raw.len() == before.len() + i, raw.len() <= byte_budget,
            before.len() + block_bytes <= byte_budget,
            raw@ == before + Seq::new(i as nat, |j: int| 0u8),
        decreases block_bytes - i,
    { raw.push(0); i += 1; }
    true
}

fn grow_block(raw: &mut Vec<u8>, block_bytes: usize, byte_budget: usize) -> (r: bool)
    requires crate::block_size::accepted(block_bytes as nat),
    ensures r == (old(raw).len() <= byte_budget && block_bytes <= byte_budget - old(raw).len()),
        final(raw)@ == if r { old(raw)@ + Seq::new(block_bytes as nat, |i: int| 0u8) } else { old(raw)@ },
        final(raw).len() as nat <= if r { byte_budget as nat } else { old(raw).len() as nat },
        r ==> final(raw).len() % block_bytes == old(raw).len() % block_bytes,
        r && old(raw).len() == 0 ==> final(raw).len() % block_bytes == 0,
        forall|prefix: int| 0 <= prefix <= old(raw).len() ==>
            #[trigger] final(raw)@.take(prefix) == old(raw)@.take(prefix),
{
    let ghost before = raw@;
    let success = grow(raw, block_bytes, byte_budget);
    proof {
        if success {
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(before.len() as int, block_bytes as int);
            if before.len() == 0 {
                vstd::arithmetic::div_mod::lemma_small_mod(0nat, block_bytes as nat);
            }
        }
    }
    success
}

impl Builder {
    pub closed spec fn view(&self) -> BuilderView {
        BuilderView { raw: self.raw@, cursor: self.cursor as nat, checksum: self.checksum,
            records: self.records as nat, committed_end: self.committed_end as nat,
            pending: self.pending_records as nat, tid: self.tid, block_bytes: self.block_bytes as nat,
            inode_bytes: self.inode_bytes as nat, byte_budget: self.byte_budget as nat, segments: self.segments@ }
    }
    pub open spec fn wf(&self) -> bool { valid_builder(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn new(block_bytes: usize, inode_bytes: usize, tid: u32, byte_budget: usize)
        -> (r: Result<Self, Error>)
        ensures match r {
            Ok(builder) => builder.wf() && builder.view().tid == tid
                && builder.view().block_bytes == block_bytes && builder.view().inode_bytes == inode_bytes
                && builder.view().byte_budget == byte_budget && builder.view().committed_end == 0
                && builder.view().pending == 0 && builder.view().records == 1 && builder.view().segments.len() == 0,
            Err(_) => true,
        },
    {
        proof { reveal(valid_builder); }
        if !crate::block_size::valid(block_bytes) || inode_bytes < 128 || inode_bytes > 65536
            || byte_budget < block_bytes || byte_budget > MAX_LOG_BYTES { return Err(Error::Geometry); }
        let mut raw = Vec::<u8>::new();
        if !grow_block(&mut raw, block_bytes, byte_budget) { return Err(Error::ResourceLimit); }
        put16(&mut raw, 0, HEAD); put16(&mut raw, 2, 8);
        put32(&mut raw, 4, 0); put32(&mut raw, 8, tid);
        assert(bytes::le16(raw@, 0) == HEAD && bytes::le16(raw@, 2) == 8);
        assert(bytes::le32(raw@, 4) == 0 && bytes::le32(raw@, 8) == tid);
        let checksum = crc::crc32c(0, &raw[..12]);
        Ok(Builder { raw, cursor: 12, checksum, records: 1, committed_end: 0,
            pending_records: 0, tid, block_bytes, inode_bytes, byte_budget,
            segments: Ghost(Seq::empty()) })
    }

    /// Caller-supplied records may not inject HEAD, TAIL or PAD markers.
    /// Space for a possible PAD and final TAIL is reserved in the tag budget.
    /// Consumes the current owner. Rejection returns that owner unchanged.
    pub fn append(self, tag: u16, value: &[u8]) -> (r: Result<Self, (Self, Error)>)
        ensures self.wf(), match r {
            Ok(next) => next.wf()
                && next.view().tid == self.view().tid
                && next.view().block_bytes == self.view().block_bytes
                && next.view().inode_bytes == self.view().inode_bytes
                && next.view().byte_budget == self.view().byte_budget
                && next.view().segments == self.view().segments
                && next.view().committed_end == self.view().committed_end
                && next.view().raw.take(self.view().committed_end as int)
                    == self.view().raw.take(self.view().committed_end as int)
                && next.view().pending == self.view().pending + 1,
            Err((owner, _)) => owner.wf() && owner.view() == self.view(),
        },
    {
        let mut draft = builder_into_draft(self);
        let result = draft.append_raw(tag, value);
        let owner = finish_builder(draft);
        match result { Ok(()) => Ok(owner), Err(error) => Err((owner, error)) }
    }

    /// Consumes the current owner. Rejection returns that owner unchanged.
    pub fn commit(self) -> (r: Result<Self, (Self, Error)>)
        ensures self.wf(), match r {
            Ok(next) => next.wf()
                && next.view().tid == self.view().tid
                && next.view().block_bytes == self.view().block_bytes
                && next.view().inode_bytes == self.view().inode_bytes
                && next.view().byte_budget == self.view().byte_budget
                && next.view().raw.take(self.view().committed_end as int)
                    == self.view().raw.take(self.view().committed_end as int)
                && next.view().committed_end == next.view().raw.len()
                && next.view().pending == 0 && next.view().segments.len() == self.view().segments.len() + 1,
            Err((owner, _)) => owner.wf() && owner.view() == self.view(),
        },
    {
        let mut draft = builder_into_draft(self);
        let result = draft.commit_raw();
        let owner = finish_builder(draft);
        match result { Ok(()) => Ok(owner), Err(error) => Err((owner, error)) }
    }

    pub fn committed_bytes(&self) -> (r: &[u8])
        ensures self.wf(), r@ == self.view().raw.take(self.view().committed_end as int),
    { proof { use_type_invariant(self); reveal(valid_builder); } &self.raw[..self.committed_end] }
    pub fn pending_records(&self) -> (r: usize) ensures self.wf(), r == self.view().pending,
    { proof { use_type_invariant(self); } self.pending_records }
    pub fn committed_length(&self) -> (r: usize) ensures self.wf(), r == self.view().committed_end,
    { proof { use_type_invariant(self); } self.committed_end }
    pub fn builder_transaction(&self) -> (r: u32) ensures self.wf(), r == self.view().tid,
    { proof { use_type_invariant(self); } self.tid }
    pub fn finish(self) -> (r: Result<Vec<u8>, Self>)
        ensures match r {
            Ok(raw) => self.wf() && raw@ == self.view().raw && self.view().committed_end == raw.len()
                && self.view().pending == 0,
            Err(builder) => builder.wf() && builder.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); }
        if self.committed_end != 0 && self.pending_records == 0 && self.cursor == self.committed_end {
            proof { completed_builder_exhausts_bytes(self.view()); }
            Ok(self.raw)
        } else { Err(self) }
    }
}

pub fn encode_transaction(records: &[Record], block_bytes: usize, inode_bytes: usize,
    tid: u32, byte_budget: usize) -> (r: Result<Vec<u8>, Error>)
    ensures match r {
        Ok(raw) => crate::block_size::accepted(block_bytes as nat) && 128 <= inode_bytes <= 65536
            && block_bytes <= raw.len() <= byte_budget <= MAX_LOG_BYTES && raw.len() % block_bytes == 0
            && bytes::le16(raw@, 0) == HEAD && bytes::le16(raw@, 2) == 8
            && bytes::le32(raw@, 4) == 0 && bytes::le32(raw@, 8) == tid
            && exists|segment: SegmentView| segment.begin == 0 && segment.end == raw.len()
                && #[trigger] segment_valid(raw@, segment, tid),
        Err(_) => true,
    },
{
    let mut builder = match Builder::new(block_bytes, inode_bytes, tid, byte_budget) {
        Ok(builder) => builder, Err(error) => { return Err(error); }
    };
    let mut i = 0usize;
    while i < records.len()
        invariant i <= records.len(), builder.wf(), builder.view().tid == tid,
            builder.view().block_bytes == block_bytes && builder.view().inode_bytes == inode_bytes
                && builder.view().byte_budget == byte_budget && builder.view().committed_end == 0
                && builder.view().segments.len() == 0,
        decreases records.len() - i,
    {
        builder = match builder.append(records[i].tag, &records[i].value) {
            Ok(next) => next, Err((_, error)) => { return Err(error); }
        };
        i += 1;
    }
    builder = match builder.commit() { Ok(next) => next, Err((_, error)) => { return Err(error); } };
    proof { use_type_invariant(&builder); reveal(valid_builder); }
    let ghost sealed = builder.view();
    match builder.finish() {
        Ok(raw) => {
            proof {
                assert(exists|segment: SegmentView| segment.begin == 0 && segment.end == raw.len()
                    && #[trigger] segment_valid(raw@, segment, tid)) by {
                    assert(segment_valid(raw@, sealed.segments[0], tid));
                }
            }
            Ok(raw)
        },
        Err(_) => Err(Error::Malformed),
    }
}

#[derive(Clone, Copy)]
pub struct Region {
    pub inode: u32, pub logical: u32, pub physical: u64,
    pub length: u32, pub initialized: bool,
}

pub enum Intent {
    SetExtent(Region),
    ClearExtent { inode: u32, logical: u32, length: u32 },
    EnsureDentry { parent: u32, inode: u32, name: Vec<u8>, create: bool },
    RemoveDentryIfMatches { parent: u32, inode: u32, name: Vec<u8> },
    MergeInode { inode: u32, raw: Vec<u8> },
}

pub enum IntentView {
    SetExtent(Region),
    ClearExtent { inode: u32, logical: u32, length: u32 },
    EnsureDentry { parent: u32, inode: u32, name: Seq<u8>, create: bool },
    RemoveDentryIfMatches { parent: u32, inode: u32, name: Seq<u8> },
    MergeInode { inode: u32, raw: Seq<u8> },
}
pub open spec fn intent_view(intent: Intent) -> IntentView {
    match intent {
        Intent::SetExtent(region) => IntentView::SetExtent(region),
        Intent::ClearExtent { inode, logical, length } => IntentView::ClearExtent { inode, logical, length },
        Intent::EnsureDentry { parent, inode, name, create } => IntentView::EnsureDentry { parent, inode, name: name@, create },
        Intent::RemoveDentryIfMatches { parent, inode, name } => IntentView::RemoveDentryIfMatches { parent, inode, name: name@ },
        Intent::MergeInode { inode, raw } => IntentView::MergeInode { inode, raw: raw@ },
    }
}
pub open spec fn intent_views(intents: Seq<Intent>) -> Seq<IntentView> {
    Seq::new(intents.len(), |i: int| intent_view(intents[i]))
}
pub open spec fn inode_number_valid(inode: u32, inodes: u32) -> bool { 0 < inode <= inodes }
pub open spec fn name_admitted(name: Seq<u8>) -> bool {
    &&& 1 <= name.len() <= 255 && name != seq![46u8] && name != seq![46u8, 46u8]
    &&& forall|i: int| 0 <= i < name.len() ==> #[trigger] name[i] != 0 && name[i] != 47
}
pub open spec fn region_admitted(region: Region, inodes: u32, blocks: u64) -> bool {
    &&& inode_number_valid(region.inode, inodes)
    &&& 0 < region.length <= if region.initialized { 32768nat } else { 32767nat }
    &&& region.logical as nat + region.length as nat <= 0xffff_ffff
    &&& 0 < region.physical < 281474976710656
    &&& region.physical as nat + region.length as nat <= blocks
}
#[verifier::opaque]
pub open spec fn decoded_intent(record: RecordView, inodes: u32, blocks: u64) -> Option<IntentView> {
    let value = record.value;
    let inode = bytes::le32(value, 0) as u32;
    if record.tag == ADD_RANGE {
        let encoded = bytes::le16(value, 8);
        let region = Region { inode, logical: bytes::le32(value, 4) as u32,
            length: if encoded <= 32768 { encoded as u32 } else { (encoded - 32768) as u32 },
            physical: (bytes::le32(value, 12) + 4294967296 * bytes::le16(value, 10)) as u64,
            initialized: encoded <= 32768 };
        if value.len() == 16 && region_admitted(region, inodes, blocks) { Some(IntentView::SetExtent(region)) } else { None }
    } else if record.tag == DEL_RANGE {
        let logical = bytes::le32(value, 4) as u32;
        let length = bytes::le32(value, 8) as u32;
        if value.len() == 12 && inode_number_valid(inode, inodes) && length > 0
            && logical as nat + length as nat <= 0xffff_ffff {
            Some(IntentView::ClearExtent { inode, logical, length })
        } else { None }
    } else if record.tag == CREAT || record.tag == LINK || record.tag == UNLINK {
        let parent = inode; let target = bytes::le32(value, 4) as u32;
        let name = value.subrange(8, value.len() as int);
        if value.len() >= 9 && inode_number_valid(parent, inodes)
            && inode_number_valid(target, inodes) && name_admitted(name) {
            if record.tag == UNLINK { Some(IntentView::RemoveDentryIfMatches { parent, inode: target, name }) }
            else { Some(IntentView::EnsureDentry { parent, inode: target, name, create: record.tag == CREAT }) }
        } else { None }
    } else if record.tag == INODE {
        if value.len() >= 132 && inode_number_valid(inode, inodes) {
            Some(IntentView::MergeInode { inode, raw: value.subrange(4, value.len() as int) })
        } else { None }
    } else { None }
}
pub open spec fn intent_admitted(intent: IntentView, inodes: u32, blocks: u64) -> bool {
    match intent {
        IntentView::SetExtent(region) => region_admitted(region, inodes, blocks),
        IntentView::ClearExtent { inode, logical, length } => inode_number_valid(inode, inodes)
            && length > 0 && logical as nat + length as nat <= 0xffff_ffff,
        IntentView::EnsureDentry { parent, inode, name, .. }
        | IntentView::RemoveDentryIfMatches { parent, inode, name } =>
            inode_number_valid(parent, inodes) && inode_number_valid(inode, inodes) && name_admitted(name),
        IntentView::MergeInode { inode, raw } => inode_number_valid(inode, inodes) && raw.len() >= 128,
    }
}
proof fn physical_extent_halves(high: u16, low: u32)
    ensures ((high as u64) << 32) | low as u64
            == ((high as u64) * 4294967296u64 + low as u64) as u64,
        (((high as u64) << 32) | low as u64) < 281474976710656u64,
{
    assert(((high as u64) << 32) | low as u64
        == ((high as u64) * 4294967296u64 + low as u64) as u64) by (bit_vector);
    assert((((high as u64) << 32) | low as u64) < 281474976710656u64) by (bit_vector);
}

pub open spec fn insert_modified(ids: Seq<u32>, inode: u32) -> Seq<u32> {
    if ids.contains(inode) { ids } else { ids.push(inode) }
}
pub open spec fn intent_modified(ids: Seq<u32>, intent: IntentView) -> Seq<u32> {
    match intent {
        IntentView::SetExtent(region) => insert_modified(ids, region.inode),
        IntentView::ClearExtent { inode, .. } | IntentView::MergeInode { inode, .. } => insert_modified(ids, inode),
        IntentView::EnsureDentry { parent, inode, .. } | IntentView::RemoveDentryIfMatches { parent, inode, .. } =>
            insert_modified(insert_modified(ids, parent), inode),
    }
}
#[verifier::opaque]
pub open spec fn modified_projection(intents: Seq<IntentView>) -> Seq<u32>
    decreases intents.len(),
{
    if intents.len() == 0 { Seq::empty() }
    else { intent_modified(modified_projection(intents.drop_last()), intents.last()) }
}
#[verifier::opaque]
pub open spec fn exclusion_projection(intents: Seq<IntentView>) -> Seq<Region>
    decreases intents.len(),
{
    if intents.len() == 0 { Seq::empty() }
    else {
        let before = exclusion_projection(intents.drop_last());
        match intents.last() { IntentView::SetExtent(region) => before.push(region), _ => before }
    }
}
pub open spec fn exclusion_contains(regions: Seq<Region>, block: u64) -> bool {
    exists|i: int| #![trigger regions[i]] 0 <= i < regions.len() && regions[i].physical <= block
        < regions[i].physical as nat + regions[i].length as nat
}
pub struct ReplayView {
    pub intents: Seq<IntentView>, pub exclusions: Seq<Region>, pub modified: Seq<u32>,
    pub source: ScanView, pub origins: Seq<usize>, pub inodes: u32, pub blocks: u64,
    pub tid: u32, pub committed_end: nat,
}
#[verifier::opaque]
pub open spec fn replay_prefix(source: ScanView, origins: Seq<usize>, intents: Seq<IntentView>,
    exclusions: Seq<Region>, modified: Seq<u32>, inodes: u32, blocks: u64, processed: nat) -> bool {
    &&& valid_scan(source) && 0 < source.committed && processed <= source.committed
    &&& origins.len() == intents.len() <= processed
    &&& (forall|j: int| #![trigger origins[j]] 0 <= j < origins.len() ==> origins[j] < processed
        && decoded_intent(source.records[origins[j] as int], inodes, blocks) == Some(intents[j]))
    &&& (forall|j: int| 0 < j < origins.len() ==> origins[j - 1] < #[trigger] origins[j])
    &&& (forall|i: int| #![trigger source.records[i]] 0 <= i < processed && ADD_RANGE <= source.records[i].tag <= INODE ==>
        origins.contains(i as usize))
    &&& exclusions == exclusion_projection(intents) && modified == modified_projection(intents)
    &&& (forall|j: int| 0 <= j < exclusions.len() ==> #[trigger] region_admitted(exclusions[j], inodes, blocks))
    &&& (forall|j: int| 0 <= j < modified.len() ==> #[trigger] inode_number_valid(modified[j], inodes))
    &&& modified.no_duplicates()
}
#[verifier::opaque]
pub open spec fn valid_replay(v: ReplayView) -> bool {
    replay_prefix(v.source, v.origins, v.intents, v.exclusions, v.modified, v.inodes, v.blocks, v.source.committed)
        && v.tid == v.source.tid && v.committed_end == v.source.committed_end
}
proof fn insert_modified_preserves_admission(ids: Seq<u32>, inode: u32, inodes: u32)
    requires ids.no_duplicates(), inode_number_valid(inode, inodes),
        forall|i: int| 0 <= i < ids.len() ==> #[trigger] inode_number_valid(ids[i], inodes),
    ensures insert_modified(ids, inode).no_duplicates(),
        forall|i: int| 0 <= i < insert_modified(ids, inode).len()
            ==> #[trigger] inode_number_valid(insert_modified(ids, inode)[i], inodes),
{
    if !ids.contains(inode) {
        assert forall|i: int, j: int| 0 <= i < j < ids.push(inode).len()
            implies #[trigger] ids.push(inode)[i] != #[trigger] ids.push(inode)[j] by {
            if j < ids.len() { assert(ids[i] != ids[j]); }
            else { assert(ids[i] != inode); }
        }
    }
}
proof fn intent_modified_preserves_admission(ids: Seq<u32>, intent: IntentView, inodes: u32, blocks: u64)
    requires ids.no_duplicates(), intent_admitted(intent, inodes, blocks),
        forall|i: int| 0 <= i < ids.len() ==> #[trigger] inode_number_valid(ids[i], inodes),
    ensures intent_modified(ids, intent).no_duplicates(),
        forall|i: int| 0 <= i < intent_modified(ids, intent).len()
            ==> #[trigger] inode_number_valid(intent_modified(ids, intent)[i], inodes),
{
    match intent {
        IntentView::SetExtent(region) => insert_modified_preserves_admission(ids, region.inode, inodes),
        IntentView::ClearExtent { inode, .. } | IntentView::MergeInode { inode, .. } =>
            insert_modified_preserves_admission(ids, inode, inodes),
        IntentView::EnsureDentry { parent, inode, .. } | IntentView::RemoveDentryIfMatches { parent, inode, .. } => {
            insert_modified_preserves_admission(ids, parent, inodes);
            insert_modified_preserves_admission(insert_modified(ids, parent), inode, inodes);
        },
    }
}
proof fn replay_prefix_empty(source: ScanView, inodes: u32, blocks: u64)
    requires valid_scan(source), source.committed > 0,
    ensures replay_prefix(source, Seq::<usize>::empty(), Seq::<IntentView>::empty(),
        Seq::<Region>::empty(), Seq::<u32>::empty(), inodes, blocks, 0),
{
    reveal(replay_prefix); reveal(modified_projection); reveal(exclusion_projection);
}
proof fn replay_projection_push(intents: Seq<IntentView>, intent: IntentView)
    ensures modified_projection(intents.push(intent)) == intent_modified(modified_projection(intents), intent),
        exclusion_projection(intents.push(intent)) == match intent {
            IntentView::SetExtent(region) => exclusion_projection(intents).push(region),
            _ => exclusion_projection(intents),
        },
{
    reveal(modified_projection); reveal(exclusion_projection);
    assert(intents.push(intent).drop_last() =~= intents);
    assert(intents.push(intent).last() == intent);
}

proof fn replay_prefix_append(source: ScanView, origins: Seq<usize>, intents: Seq<IntentView>,
    exclusions: Seq<Region>, modified: Seq<u32>, inodes: u32, blocks: u64, processed: nat,
    decoded: Option<IntentView>, next_origins: Seq<usize>, next_intents: Seq<IntentView>,
    next_exclusions: Seq<Region>, next_modified: Seq<u32>)
    requires replay_prefix(source, origins, intents, exclusions, modified, inodes, blocks, processed),
        processed < source.committed,
        match decoded {
            Some(intent) => intent_admitted(intent, inodes, blocks)
                && ADD_RANGE <= source.records[processed as int].tag <= INODE
                && decoded_intent(source.records[processed as int], inodes, blocks) == Some(intent)
                && next_origins == origins.push(processed as usize) && next_intents == intents.push(intent)
                && next_modified == intent_modified(modified, intent)
                && next_exclusions == match intent { IntentView::SetExtent(region) => exclusions.push(region), _ => exclusions },
            None => !(ADD_RANGE <= source.records[processed as int].tag <= INODE)
                && next_origins == origins && next_intents == intents
                && next_modified == modified && next_exclusions == exclusions,
        },
    ensures replay_prefix(source, next_origins, next_intents, next_exclusions, next_modified,
        inodes, blocks, processed + 1),
{
    reveal(replay_prefix);
    scan_bounds(source);
    assert(processed < MAX_RECORDS);
    match decoded {
        Some(intent) => {
            intent_modified_preserves_admission(modified, intent, inodes, blocks);
            replay_projection_push(intents, intent);
            assert(next_exclusions == exclusion_projection(next_intents));
            assert(next_modified == modified_projection(next_intents));
            assert forall|j: int| 0 <= j < next_origins.len() implies next_origins[j] < processed + 1
                && #[trigger] decoded_intent(source.records[next_origins[j] as int], inodes, blocks) == Some(next_intents[j]) by {
                if j < origins.len() {
                    assert(decoded_intent(source.records[origins[j] as int], inodes, blocks) == Some(intents[j]));
                } else { assert(next_origins[j] == processed as usize && next_intents[j] == intent); }
            }
            assert forall|j: int| 0 < j < next_origins.len() implies
                next_origins[j - 1] < #[trigger] next_origins[j] by {
                if j < origins.len() { assert(origins[j - 1] < origins[j]); }
                else if j > 0 {
                    assert(0 <= j - 1 < origins.len());
                    assert(origins[j - 1] < processed);
                }
            }
            assert forall|i: int| #![trigger source.records[i]]
                0 <= i < processed + 1 && ADD_RANGE <= source.records[i].tag <= INODE
                implies next_origins.contains(i as usize) by {
                if i < processed {
                    assert(origins.contains(i as usize));
                    let at = choose|at: int| 0 <= at < origins.len() && origins[at] == i as usize;
                    assert(next_origins[at] == i as usize);
                } else { assert(next_origins[origins.len() as int] == i as usize); }
            }
            assert forall|j: int| 0 <= j < next_exclusions.len() implies
                #[trigger] region_admitted(next_exclusions[j], inodes, blocks) by {
                if j < exclusions.len() { assert(region_admitted(exclusions[j], inodes, blocks)); }
                else { assert(intent is SetExtent); }
            }
        },
        None => {
            assert forall|i: int| #![trigger source.records[i]]
                0 <= i < processed + 1 && ADD_RANGE <= source.records[i].tag <= INODE
                implies next_origins.contains(i as usize) by {
                assert(i < processed);
            }
        },
    }
    assert(valid_scan(source) && source.committed > 0 && processed + 1 <= source.committed);
    assert(next_origins.len() == next_intents.len() <= processed + 1);
    assert(next_exclusions == exclusion_projection(next_intents));
    assert(next_modified == modified_projection(next_intents));
    assert(next_modified.no_duplicates());
    assert forall|j: int| 0 <= j < next_modified.len() implies
        #[trigger] inode_number_valid(next_modified[j], inodes) by {}
    assert(replay_prefix(source, next_origins, next_intents, next_exclusions, next_modified,
        inodes, blocks, processed + 1));

}

pub proof fn replay_intent_has_a_committed_source(v: ReplayView, index: int)
    requires valid_replay(v), 0 <= index < v.intents.len(),
    ensures 0 <= v.origins[index] < v.source.committed,
        decoded_intent(v.source.records[v.origins[index] as int], v.inodes, v.blocks) == Some(v.intents[index]),
        valid_tail(v.source.source, v.source.positions, (v.source.committed - 1) as nat, v.tid),
{
    reveal(valid_replay); reveal(replay_prefix); reveal(valid_scan);
}
pub proof fn every_set_extent_is_excluded_from_allocation(v: ReplayView, index: int, region: Region, block: u64)
    requires valid_replay(v), 0 <= index < v.intents.len(), v.intents[index] == IntentView::SetExtent(region),
        region.physical <= block < region.physical as nat + region.length as nat,
    ensures exclusion_contains(v.exclusions, block),
{
    reveal(valid_replay); reveal(replay_prefix);
    exclusion_projection_contains(v.intents, index);
}
proof fn exclusion_projection_contains(intents: Seq<IntentView>, index: int)
    requires 0 <= index < intents.len(),
    ensures match intents[index] {
        IntentView::SetExtent(region) => exclusion_projection(intents).contains(region),
        _ => true,
    },
    decreases intents.len(),
{
    reveal(exclusion_projection);
    if let IntentView::SetExtent(region) = intents[index] {
        let prefix = exclusion_projection(intents.drop_last());
        if index < intents.len() - 1 {
            exclusion_projection_contains(intents.drop_last(), index);
            assert(prefix.contains(region));
            if let IntentView::SetExtent(last) = intents.last() {
                let at = choose|at: int| 0 <= at < prefix.len() && prefix[at] == region;
                assert(prefix.push(last)[at] == region);
                assert(prefix.push(last).contains(region));
            }
        } else {
            assert(index == intents.len() - 1);
            assert(intents.last() == intents[index]);
            assert(exclusion_projection(intents) == prefix.push(region));
            assert(prefix.push(region)[prefix.len() as int] == region);
            assert(prefix.push(region).contains(region));
        }
    }
}

/// A per-key effect model: namespace replacement needs an absent or matching
/// existing binding. This is a specification, not replay or credential authority.
pub open spec fn extent_intent_at(intent: IntentView, inode: u32, logical: u32,
    before: crate::extent_edit::Mapping) -> crate::extent_edit::Mapping {
    match intent {
        IntentView::SetExtent(region) => {
            if region.inode == inode && region.logical <= logical
                < region.logical as nat + region.length as nat {
                let physical = (region.physical as nat + logical as nat - region.logical as nat) as u64;
                if region.initialized { crate::extent_edit::Mapping::Written(physical) }
                else { crate::extent_edit::Mapping::Unwritten(physical) }
            } else { before }
        },
        IntentView::ClearExtent { inode: target, logical: first, length } => {
            if target == inode && first <= logical < first as nat + length as nat { crate::extent_edit::Mapping::Hole }
            else { before }
        },
        _ => before,
    }
}
pub open spec fn namespace_intent_at(intent: IntentView, parent: u32, name: Seq<u8>,
    before: Option<u32>) -> Option<Option<u32>> {
    match intent {
        IntentView::EnsureDentry { parent: target, inode, name: target_name, .. } => {
            if target == parent && target_name == name {
                if before is None || before == Some(inode) { Some(Some(inode)) } else { None }
            } else { Some(before) }
        },
        IntentView::RemoveDentryIfMatches { parent: target, inode, name: target_name } => {
            if target == parent && target_name == name && before == Some(inode) { Some(None) } else { Some(before) }
        },
        _ => Some(before),
    }
}
pub proof fn extent_replay_intentions_are_idempotent(intent: IntentView, inode: u32, logical: u32,
    before: crate::extent_edit::Mapping)
    ensures extent_intent_at(intent, inode, logical, extent_intent_at(intent, inode, logical, before))
        == extent_intent_at(intent, inode, logical, before),
{}
pub proof fn admitted_namespace_replay_intentions_are_idempotent(intent: IntentView, parent: u32,
    name: Seq<u8>, before: Option<u32>, after: Option<u32>)
    requires namespace_intent_at(intent, parent, name, before) == Some(after),
    ensures namespace_intent_at(intent, parent, name, after) == Some(after),
{}

pub open spec fn writes_extent_key(intent: IntentView, inode: u32, logical: u32) -> bool {
    match intent {
        IntentView::SetExtent(region) => region.inode == inode
            && region.logical <= logical < region.logical as nat + region.length as nat,
        IntentView::ClearExtent { inode: target, logical: first, length } => target == inode
            && first <= logical < first as nat + length as nat,
        _ => false,
    }
}
pub open spec fn extent_sequence_at(intents: Seq<IntentView>, inode: u32, logical: u32,
    before: crate::extent_edit::Mapping) -> crate::extent_edit::Mapping
    decreases intents.len(),
{
    if intents.len() == 0 { before }
    else { extent_intent_at(intents.last(), inode, logical,
        extent_sequence_at(intents.drop_last(), inode, logical, before)) }
}
pub open spec fn sequence_writes_extent_key(intents: Seq<IntentView>, inode: u32, logical: u32) -> bool {
    exists|i: int| 0 <= i < intents.len() && #[trigger] writes_extent_key(intents[i], inode, logical)
}
proof fn an_extent_intent_is_identity_or_an_absolute_value(intent: IntentView, inode: u32, logical: u32,
    first: crate::extent_edit::Mapping, second: crate::extent_edit::Mapping)
    ensures if writes_extent_key(intent, inode, logical) {
        extent_intent_at(intent, inode, logical, first) == extent_intent_at(intent, inode, logical, second)
    } else { extent_intent_at(intent, inode, logical, first) == first },
{}
proof fn an_extent_sequence_is_identity_or_an_absolute_value(intents: Seq<IntentView>, inode: u32,
    logical: u32, first: crate::extent_edit::Mapping, second: crate::extent_edit::Mapping)
    ensures if sequence_writes_extent_key(intents, inode, logical) {
        extent_sequence_at(intents, inode, logical, first) == extent_sequence_at(intents, inode, logical, second)
    } else { extent_sequence_at(intents, inode, logical, first) == first },
    decreases intents.len(),
{
    if intents.len() > 0 {
        let prefix = intents.drop_last();
        an_extent_sequence_is_identity_or_an_absolute_value(prefix, inode, logical, first, second);
        an_extent_intent_is_identity_or_an_absolute_value(intents.last(), inode, logical,
            extent_sequence_at(prefix, inode, logical, first), extent_sequence_at(prefix, inode, logical, second));
        if sequence_writes_extent_key(intents, inode, logical) && !writes_extent_key(intents.last(), inode, logical) {
            let i = choose|i: int| 0 <= i < intents.len() && #[trigger] writes_extent_key(intents[i], inode, logical);
            assert(i < prefix.len());
            assert(prefix[i] == intents[i]);
            assert(writes_extent_key(prefix[i], inode, logical));
            assert(sequence_writes_extent_key(prefix, inode, logical)) by {
                assert(exists|j: int| 0 <= j < prefix.len() && #[trigger] writes_extent_key(prefix[j], inode, logical)) by {
                    assert(writes_extent_key(prefix[i], inode, logical));
                }
            }
        }
    }
}
pub proof fn complete_absolute_extent_replay_sequences_are_idempotent(intents: Seq<IntentView>,
    inode: u32, logical: u32, before: crate::extent_edit::Mapping)
    ensures extent_sequence_at(intents, inode, logical, extent_sequence_at(intents, inode, logical, before))
        == extent_sequence_at(intents, inode, logical, before),
{
    an_extent_sequence_is_identity_or_an_absolute_value(intents, inode, logical,
        before, extent_sequence_at(intents, inode, logical, before));
}

pub struct ReplayPlan {
    intents: Vec<Intent>, exclusions: Vec<Region>, modified: Vec<u32>,
    tid: u32, committed_end: usize,
    source: Ghost<ScanView>, origins: Ghost<Seq<usize>>, inodes: Ghost<u32>, blocks: Ghost<u64>,
}
fn valid_inode(inode: u32, inodes: u32) -> (r: bool)
    ensures r == inode_number_valid(inode, inodes),
{ inode != 0 && inode <= inodes }

fn add_modified(modified: &mut Vec<u32>, inode: u32)
    ensures final(modified)@ == insert_modified(old(modified)@, inode),
        final(modified).len() <= old(modified).len() + 1,
{
    let ghost before = modified@;
    let mut i = 0usize;
    while i < modified.len()
        invariant i <= modified.len(), modified@ == before,
            forall|j: int| 0 <= j < i ==> #[trigger] modified@[j] != inode,
        decreases modified.len() - i,
    {
        if modified[i] == inode { return; }
        i += 1;
    }
    modified.push(inode);
}

fn name_valid(name: &[u8]) -> (r: bool)
    ensures r == name_admitted(name@),
{
    if name.len() == 0 || name.len() > 255 { return false; }
    if name.len() == 1 && name[0] == 46 {
        assert(name@ =~= seq![46u8]); return false;
    }
    if name.len() == 2 && name[0] == 46 && name[1] == 46 {
        assert(name@ =~= seq![46u8, 46u8]); return false;
    }
    let mut i = 0usize;
    while i < name.len()
        invariant i <= name.len(), 1 <= name.len() <= 255,
            name@ != seq![46u8], name@ != seq![46u8, 46u8],
            forall|j: int| 0 <= j < i ==> #[trigger] name@[j] != 0 && name@[j] != 47,
        decreases name.len() - i,
    {
        if name[i] == 0 || name[i] == 47 { return false; }
        i += 1;
    }
    true
}

fn decode_replay_record(record: &Record, inode_bytes: usize, inodes: u32, filesystem_blocks: u64)
    -> (r: Result<Option<Intent>, Error>)
    requires 128 <= inode_bytes <= 65536,
        value_length_ok(record.tag, record.value.len() as nat, inode_bytes as nat),
    ensures match r {
        Ok(Some(intent)) => ADD_RANGE <= record.tag <= INODE
            && decoded_intent(RecordView { tag: record.tag, value: record.value@ }, inodes, filesystem_blocks) == Some(intent_view(intent))
            && intent_admitted(intent_view(intent), inodes, filesystem_blocks),
        Ok(None) => !(ADD_RANGE <= record.tag <= INODE),
        Err(_) => true,
    },
{
    hide(crc::fold);
    reveal(decoded_intent);
    let value = &record.value;
    if record.tag == ADD_RANGE {
        let inode = bytes::read_le32(value, 0).unwrap();
        if !valid_inode(inode, inodes) { return Err(Error::InvalidInode); }
        let logical = bytes::read_le32(value, 4).unwrap();
        let encoded = bytes::read_le16(value, 8).unwrap();
        if encoded == 0 { return Err(Error::InvalidRange); }
        let initialized = encoded <= 32768;
        let length = if initialized { encoded as u32 } else { encoded as u32 - 32768 };
        let high = bytes::read_le16(value, 10).unwrap();
        let low = bytes::read_le32(value, 12).unwrap();
        let physical = ((high as u64) << 32) | low as u64;
        proof { physical_extent_halves(high, low); }
        if logical as u64 + length as u64 > 0xffff_ffffu64 || physical == 0
            || physical >= filesystem_blocks || length as u64 > filesystem_blocks - physical {
            return Err(Error::InvalidRange);
        }
        Ok(Some(Intent::SetExtent(Region { inode, logical, physical, length, initialized })))
    } else if record.tag == DEL_RANGE {
        let inode = bytes::read_le32(value, 0).unwrap();
        if !valid_inode(inode, inodes) { return Err(Error::InvalidInode); }
        let logical = bytes::read_le32(value, 4).unwrap(); let length = bytes::read_le32(value, 8).unwrap();
        if length == 0 || logical as u64 + length as u64 > 0xffff_ffffu64 { return Err(Error::InvalidRange); }
        Ok(Some(Intent::ClearExtent { inode, logical, length }))
    } else if record.tag == CREAT || record.tag == LINK || record.tag == UNLINK {
        let parent = bytes::read_le32(value, 0).unwrap(); let inode = bytes::read_le32(value, 4).unwrap();
        if !valid_inode(parent, inodes) || !valid_inode(inode, inodes) { return Err(Error::InvalidInode); }
        let name = &value[8..]; if !name_valid(name) { return Err(Error::InvalidName); }
        if record.tag == UNLINK {
            Ok(Some(Intent::RemoveDentryIfMatches { parent, inode, name: copy(name) }))
        } else {
            Ok(Some(Intent::EnsureDentry { parent, inode, name: copy(name), create: record.tag == CREAT }))
        }
    } else if record.tag == INODE {
        let inode = bytes::read_le32(value, 0).unwrap();
        if !valid_inode(inode, inodes) { return Err(Error::InvalidInode); }
        Ok(Some(Intent::MergeInode { inode, raw: copy(&value[4..]) }))
    } else { Ok(None) }
}
fn include_replay_metadata(intent: &Intent, exclusions: &mut Vec<Region>, modified: &mut Vec<u32>)
    ensures final(exclusions)@ == match intent_view(*intent) {
            IntentView::SetExtent(region) => old(exclusions)@.push(region), _ => old(exclusions)@ },
        final(modified)@ == intent_modified(old(modified)@, intent_view(*intent)),
{
    match intent {
        Intent::SetExtent(region) => { exclusions.push(*region); add_modified(modified, region.inode); },
        Intent::ClearExtent { inode, .. } | Intent::MergeInode { inode, .. } => add_modified(modified, *inode),
        Intent::EnsureDentry { parent, inode, .. } | Intent::RemoveDentryIfMatches { parent, inode, .. } => {
            add_modified(modified, *parent); add_modified(modified, *inode);
        },
    }
}

/// Turn only the recognized committed prefix into absolute replay intentions.
/// The allocator must exclude every recorded physical region before applying
/// any intent. Actual bitmap ownership and source-image admission are separate.
pub fn plan_replay(scanned: &Scan, inodes: u32, filesystem_blocks: u64)
    -> (r: Result<ReplayPlan, Error>)
    ensures scanned.wf(), match r {
        Ok(plan) => plan.wf() && plan.view().source == scanned.view()
            && plan.view().inodes == inodes && plan.view().blocks == filesystem_blocks,
        Err(_) => true,
    },
{
    proof { use_type_invariant(scanned); scan_bounds(scanned.view()); }
    if scanned.committed == 0 { return Err(Error::NoChanges); }
    let mut intents = Vec::<Intent>::new(); let mut exclusions = Vec::<Region>::new();
    let mut modified = Vec::<u32>::new(); let ghost mut origins = Seq::<usize>::empty();
    let mut i = 0usize;
    proof {
        assert(intent_views(intents@) =~= Seq::<IntentView>::empty());
        assert(origins =~= Seq::<usize>::empty());
        assert(exclusions@ =~= Seq::<Region>::empty());
        assert(modified@ =~= Seq::<u32>::empty());
        replay_prefix_empty(scanned.view(), inodes, filesystem_blocks);
    }
    while i < scanned.committed
        invariant scanned.wf(), i <= scanned.committed <= scanned.records.len(), scanned.records.len() <= MAX_RECORDS,
            128 <= scanned.inode_bytes <= 65536,
            replay_prefix(scanned.view(), origins, intent_views(intents@), exclusions@, modified@,
                inodes, filesystem_blocks, i as nat),
        decreases scanned.committed - i,
    {
        proof { checked_scan_record(scanned.view(), i as int); }
        let record = &scanned.records[i];
        let decoded = match decode_replay_record(record, scanned.inode_bytes, inodes, filesystem_blocks) {
            Ok(decoded) => decoded, Err(error) => { return Err(error); }
        };
        let ghost old_origins = origins; let ghost old_intents = intent_views(intents@);
        let ghost old_exclusions = exclusions@; let ghost old_modified = modified@;
        match decoded {
            Some(intent) => {
                let ghost decoded_view = intent_view(intent);
                include_replay_metadata(&intent, &mut exclusions, &mut modified);
                intents.push(intent);
                proof {
                    origins = old_origins.push(i);
                    assert(intent_views(intents@) =~= old_intents.push(decoded_view));
                    replay_prefix_append(scanned.view(), old_origins, old_intents, old_exclusions, old_modified,
                        inodes, filesystem_blocks, i as nat, Some(decoded_view), origins,
                        intent_views(intents@), exclusions@, modified@);
                }
            },
            None => {
                proof {
                    replay_prefix_append(scanned.view(), old_origins, old_intents, old_exclusions, old_modified,
                        inodes, filesystem_blocks, i as nat, None, origins,
                        intent_views(intents@), exclusions@, modified@);
                }
            },
        }
        i += 1;
    }
    proof { reveal(valid_replay); }
    Ok(ReplayPlan { intents, exclusions, modified, tid: scanned.tid,
        committed_end: scanned.committed_end, source: Ghost(scanned.view()),
        origins: Ghost(origins), inodes: Ghost(inodes), blocks: Ghost(filesystem_blocks) })
}

impl ReplayPlan {
    pub closed spec fn view(&self) -> ReplayView {
        ReplayView { intents: intent_views(self.intents@), exclusions: self.exclusions@,
            modified: self.modified@, source: self.source@, origins: self.origins@,
            inodes: self.inodes@, blocks: self.blocks@, tid: self.tid, committed_end: self.committed_end as nat }
    }
    pub open spec fn wf(&self) -> bool { valid_replay(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn replay_transaction(&self) -> (r: u32) ensures self.wf(), r == self.view().tid,
    { proof { use_type_invariant(self); } self.tid }
    pub fn replay_committed_end(&self) -> (r: usize) ensures self.wf(), r == self.view().committed_end,
    { proof { use_type_invariant(self); } self.committed_end }
    pub fn replay_len(&self) -> (r: usize) ensures self.wf(), r == self.view().intents.len(),
    { proof { use_type_invariant(self); } self.intents.len() }
    pub fn replay_intent(&self, index: usize) -> (r: Option<&Intent>)
        ensures self.wf(), match r {
            Some(intent) => index < self.view().intents.len() && intent_view(*intent) == self.view().intents[index as int],
            None => index >= self.view().intents.len(),
        },
    {
        proof { use_type_invariant(self); }
        if index >= self.intents.len() { None } else { Some(&self.intents[index]) }
    }
    pub fn excluded_regions(&self) -> (r: &[Region]) ensures self.wf(), r@ == self.view().exclusions,
    { proof { use_type_invariant(self); } &self.exclusions }
    pub fn modified_inodes(&self) -> (r: &[u32]) ensures self.wf(), r@ == self.view().modified,
    { proof { use_type_invariant(self); } &self.modified }
    pub fn allocation_block_excluded(&self, block: u64) -> (r: bool)
        ensures self.wf(), r == exclusion_contains(self.view().exclusions, block),
    {
        proof { use_type_invariant(self); }
        let mut i = 0usize;
        while i < self.exclusions.len()
            invariant self.wf(), i <= self.exclusions.len(),
                forall|j: int| #![trigger self.exclusions@[j]] 0 <= j < i ==> !(self.exclusions@[j].physical <= block
                    < self.exclusions@[j].physical as nat + self.exclusions@[j].length as nat),
            decreases self.exclusions.len() - i,
        {
            let region = self.exclusions[i];
            if block >= region.physical && block - region.physical < region.length as u64 {
                proof {
                    assert(region.physical <= block < region.physical as nat + region.length as nat);
                    assert(exclusion_contains(self.view().exclusions, block)) by {
                        assert(self.view().exclusions[i as int] == region);
                    }
                }
                return true;
            }
            i += 1;
        }
        false
    }
}

pub open spec fn replay_inode_admitted(current: Seq<u8>, logged: Seq<u8>) -> bool {
    &&& 128 <= logged.len() <= current.len() <= 65536
    &&& !(bytes::le32(logged, 32) as u32 & 0x0008_0000u32 != 0
        && bytes::le32(logged, 32) as u32 & 0x1000_0000u32 != 0)
}
pub open spec fn canonical_empty_extent_header() -> Seq<u8> {
    seq![10u8, 243u8, 0u8, 0u8, 4u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]
}
pub open spec fn merged_inode_byte(current: Seq<u8>, logged: Seq<u8>, index: int) -> u8 {
    let flags = bytes::le32(logged, 32) as u32;
    if 40 <= index < 100 {
        if flags & 0x1000_0000u32 != 0 { logged[index] }
        else if flags & 0x0008_0000u32 != 0 && bytes::le16(current, 40) != 0xf30a && index < 52 {
            canonical_empty_extent_header()[index - 40]
        } else { current[index] }
    } else if index < logged.len() { logged[index] } else { current[index] }
}
pub open spec fn merged_inode_image(current: Seq<u8>, logged: Seq<u8>) -> Seq<u8> {
    Seq::new(current.len(), |i: int| merged_inode_byte(current, logged, i))
}
pub proof fn inode_replay_preserves_the_current_valid_extent_root(current: Seq<u8>, logged: Seq<u8>)
    requires replay_inode_admitted(current, logged), bytes::le16(current, 40) == 0xf30a,
        bytes::le32(logged, 32) as u32 & 0x0008_0000u32 != 0,
    ensures merged_inode_image(current, logged).subrange(40, 100) == current.subrange(40, 100),
{
    assert(merged_inode_image(current, logged).subrange(40, 100) =~= current.subrange(40, 100));
}
pub proof fn replaying_the_same_inode_image_is_idempotent(current: Seq<u8>, logged: Seq<u8>)
    requires replay_inode_admitted(current, logged),
    ensures replay_inode_admitted(merged_inode_image(current, logged), logged),
        merged_inode_image(merged_inode_image(current, logged), logged) == merged_inode_image(current, logged),
{
    let after = merged_inode_image(current, logged);
    assert(after.subrange(32, 36) =~= logged.subrange(32, 36));
    if bytes::le32(logged, 32) as u32 & 0x0008_0000u32 != 0 && bytes::le16(current, 40) != 0xf30a {
        assert(after.subrange(40, 52) =~= canonical_empty_extent_header());
        assert(bytes::le16(after, 40) == 0xf30a);
    }
    assert(merged_inode_image(after, logged) =~= after);
}

/// Linux FC inode replay preserves the current extent root, not the journaled
/// root. Inline data is the exception. The result still needs storage-accounting,
/// inode-seed/checksum recomputation and complete filesystem validation.
pub fn inode_replay_image(current: &[u8], logged: &[u8]) -> (r: Option<Vec<u8>>)
    ensures match r {
        Some(raw) => replay_inode_admitted(current@, logged@) && raw@ == merged_inode_image(current@, logged@),
        None => !replay_inode_admitted(current@, logged@),
    },
{
    if current.len() < 128 || current.len() > 65536 || logged.len() < 128
        || logged.len() > current.len() { return None; }
    let flags = bytes::read_le32(logged, 32).unwrap();
    if flags & 0x0008_0000u32 != 0 && flags & 0x1000_0000u32 != 0 { return None; }
    let mut result = copy(current); let mut i = 0usize;
    let ghost flags_spec = flags;
    while i < logged.len()
        invariant i <= logged.len() <= current.len(), result.len() == current.len(), logged.len() >= 128,
            flags == flags_spec, flags as nat == bytes::le32(logged@, 32),
            replay_inode_admitted(current@, logged@),
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result@[j]
                == if j < i && (j < 40 || j >= 100) { logged@[j] } else { current@[j] },
        decreases logged.len() - i,
    {
        if i < 40 || i >= 100 { result[i] = logged[i]; }
        i += 1;
    }
    if flags & 0x0008_0000u32 != 0 {
        if bytes::read_le16(&result, 40).unwrap() != 0xf30a {
            i = 40;
            while i < 52
                invariant 40 <= i <= 52, result.len() == current.len() >= 128,
                    replay_inode_admitted(current@, logged@),
                    forall|j: int| 0 <= j < result.len() ==> #[trigger] result@[j]
                        == if 40 <= j < i { 0u8 }
                        else if j < logged.len() && (j < 40 || j >= 100) { logged@[j] } else { current@[j] },
                decreases 52 - i,
            { result[i] = 0; i += 1; }
            put16(&mut result, 40, 0xf30a); put16(&mut result, 44, 4);
        }
    } else if flags & 0x1000_0000u32 != 0 {
        i = 40;
        while i < 100
            invariant 40 <= i <= 100, logged.len() >= 128, result.len() == current.len() >= 128,
                replay_inode_admitted(current@, logged@),
                forall|j: int| 0 <= j < result.len() ==> #[trigger] result@[j]
                    == if j < logged.len() && (j < 40 || j >= 100 || 40 <= j < i) { logged@[j] } else { current@[j] },
            decreases 100 - i,
        { result[i] = logged[i]; i += 1; }
    }
    assert(result@ =~= merged_inode_image(current@, logged@));
    Some(result)
}

/// The bit order follows Linux EXT4_FC_REASON_* in fast_commit.h. This policy
/// result is not proof that a caller has quiesced operations or completed I/O.
pub const INELIGIBLE_REASON_MASK: u32 = 0x3fff;
pub fn requires_full_commit(reason_bits: u32, has_full_commit_baseline: bool,
    journal_data: bool, encrypted_names: bool) -> (r: bool)
    ensures r == (reason_bits != 0 || !has_full_commit_baseline || journal_data || encrypted_names),
{
    reason_bits != 0 || !has_full_commit_baseline || journal_data || encrypted_names
}

}
