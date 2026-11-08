// SPDX-License-Identifier: MPL-2.0

//! Linux quota v2 (vfsv0/vfsv1) disk records and four-level radix lookup.
//! Quota blocks are 1024 bytes regardless of the filesystem block size.
//! This format has no checksum. These codecs do not grant inode, journal,
//! CortenMM frame or quota-administration authority.

use vstd::prelude::*;
use crate::bytes;

verus! {

pub const BLOCK_BYTES: usize = 1024;
pub const ROOT_BLOCK: u32 = 1;
pub const DATA_HEADER_BYTES: usize = 16;
pub const MAX_BUILD_BLOCKS: u32 = 65536;

#[derive(Clone, Copy)]
pub enum QuotaType { User, Group, Project }

pub fn same_type(a: QuotaType, b: QuotaType) -> (r: bool) ensures r == (a == b) {
    match (a, b) {
        (QuotaType::User, QuotaType::User) => true,
        (QuotaType::Group, QuotaType::Group) => true,
        (QuotaType::Project, QuotaType::Project) => true,
        _ => false,
    }
}

pub fn magic(kind: QuotaType) -> (r: u32) ensures r == type_magic(kind) {
    match kind {
        QuotaType::User => 0xd9c01f11,
        QuotaType::Group => 0xd9c01927,
        QuotaType::Project => 0xd9c03f14,
    }
}

#[derive(Clone, Copy)]
pub struct Header { pub kind: QuotaType, pub version: u32 }

#[derive(Clone, Copy)]
pub struct Info {
    pub block_grace: u32, pub inode_grace: u32, pub flags: u32,
    pub blocks: u32, pub free_block: u32, pub free_entry: u32,
}

/// Limits retain their on-disk 1024-byte units. Current space is exact bytes.
#[derive(Clone, Copy)]
pub struct Record {
    pub id: u32, pub inode_hard: u64, pub inode_soft: u64, pub current_inodes: u64,
    pub block_hard: u64, pub block_soft: u64, pub current_space: u64,
    pub block_time: u64, pub inode_time: u64,
}

#[derive(Clone, Copy)]
pub struct DataHeader { pub next_free: u32, pub previous_free: u32, pub entries: u16 }

#[derive(Clone, Copy)]
pub struct Located { pub record: Record, pub block: u32, pub slot: usize, pub offset: usize }

#[derive(Clone, Copy)]
pub enum Error { Header, Version, Bounds, TreeCycle, DataHeader, MissingRecord, DuplicateId, Budget }


pub open spec fn type_magic(kind: QuotaType) -> u32 {
    match kind { QuotaType::User => 0xd9c01f11, QuotaType::Group => 0xd9c01927, QuotaType::Project => 0xd9c03f14 }
}
pub open spec fn width(version: u32) -> Option<nat> {
    if version == 0 { Some(48) } else if version == 1 { Some(72) } else { None }
}
pub open spec fn le64(raw: Seq<u8>, at: int) -> nat {
    bytes::le32(raw, at) + 4294967296 * bytes::le32(raw, at + 4)
}
#[verifier::opaque]
pub open spec fn encoded64(value: u64) -> Seq<u8> {
    bytes::encoded_le(value as u32) + bytes::encoded_le((value / 4294967296) as u32)
}
pub open spec fn zero_record(record: Record) -> bool {
    record.id == 0 && record.inode_hard == 0 && record.inode_soft == 0 && record.current_inodes == 0
        && record.block_hard == 0 && record.block_soft == 0 && record.current_space == 0
        && record.block_time == 0 && record.inode_time == 0
}
pub open spec fn sentinel_record(record: Record) -> bool {
    record.id == 0 && record.inode_hard == 0 && record.inode_soft == 0 && record.current_inodes == 0
        && record.block_hard == 0 && record.block_soft == 0 && record.current_space == 0
        && record.block_time == 0 && record.inode_time == 1
}
/// Linux deliberately aliases the ID-zero itime=1 escape to the zero record.
/// Hence round trips normalize this one record and never assert bijectivity.
pub open spec fn normalized_record(record: Record) -> Record {
    if sentinel_record(record) { Record { inode_time: 0, ..record } } else { record }
}
pub open spec fn representable(record: Record, version: u32) -> bool {
    version <= 1 && (version != 0 || (record.inode_hard <= 0xffff_ffff && record.inode_soft <= 0xffff_ffff
        && record.current_inodes <= 0xffff_ffff && record.block_hard <= 0xffff_ffff && record.block_soft <= 0xffff_ffff))
}
#[verifier::opaque]
pub open spec fn record_image(record: Record, version: u32) -> Seq<u8> {
    if version == 0 {
        bytes::encoded_le(record.id) + bytes::encoded_le(record.inode_hard as u32)
            + bytes::encoded_le(record.inode_soft as u32) + bytes::encoded_le(record.current_inodes as u32)
            + bytes::encoded_le(record.block_hard as u32) + bytes::encoded_le(record.block_soft as u32)
            + encoded64(record.current_space) + encoded64(record.block_time) + encoded64(record.inode_time)
    } else {
        bytes::encoded_le(record.id) + seq![0u8, 0u8, 0u8, 0u8]
            + encoded64(record.inode_hard) + encoded64(record.inode_soft) + encoded64(record.current_inodes)
            + encoded64(record.block_hard) + encoded64(record.block_soft)
            + encoded64(record.current_space) + encoded64(record.block_time) + encoded64(record.inode_time)
    }
}
/// Exact successful write trace, used only to refine the executable stores.
#[verifier::opaque]
spec fn record_writes(record: Record, version: u32) -> Seq<u8> {
    let initial = Seq::<u8>::new(if version == 0 { 48nat } else { 72nat }, |i: int| 0u8);
    let id = bytes::splice(initial, 0, bytes::encoded_le(record.id));
    if version == 0 {
        let ih = bytes::splice(id, 4, bytes::encoded_le(record.inode_hard as u32));
        let soft_i = bytes::splice(ih, 8, bytes::encoded_le(record.inode_soft as u32));
        let ci = bytes::splice(soft_i, 12, bytes::encoded_le(record.current_inodes as u32));
        let bh = bytes::splice(ci, 16, bytes::encoded_le(record.block_hard as u32));
        let bs = bytes::splice(bh, 20, bytes::encoded_le(record.block_soft as u32));
        let cs = bytes::splice(bs, 24, encoded64(record.current_space));
        let bt = bytes::splice(cs, 32, encoded64(record.block_time));
        bytes::splice(bt, 40, encoded64(record.inode_time))
    } else {
        let ih = bytes::splice(id, 8, encoded64(record.inode_hard));
        let soft_i = bytes::splice(ih, 16, encoded64(record.inode_soft));
        let ci = bytes::splice(soft_i, 24, encoded64(record.current_inodes));
        let bh = bytes::splice(ci, 32, encoded64(record.block_hard));
        let bs = bytes::splice(bh, 40, encoded64(record.block_soft));
        let cs = bytes::splice(bs, 48, encoded64(record.current_space));
        let bt = bytes::splice(cs, 56, encoded64(record.block_time));
        bytes::splice(bt, 64, encoded64(record.inode_time))
    }
}

#[verifier::opaque]
pub open spec fn canonical_image(record: Record, version: u32) -> Seq<u8> {
    record_image(if zero_record(record) { Record { inode_time: 1, ..record } } else { record }, version)
}
#[verifier::opaque]
pub open spec fn fields(raw: Seq<u8>, version: u32) -> Record {
    if version == 0 { Record {
        id: bytes::le32(raw, 0) as u32, inode_hard: bytes::le32(raw, 4) as u64,
        inode_soft: bytes::le32(raw, 8) as u64, current_inodes: bytes::le32(raw, 12) as u64,
        block_hard: bytes::le32(raw, 16) as u64, block_soft: bytes::le32(raw, 20) as u64,
        current_space: le64(raw, 24) as u64, block_time: le64(raw, 32) as u64, inode_time: le64(raw, 40) as u64,
    } } else { Record {
        id: bytes::le32(raw, 0) as u32, inode_hard: le64(raw, 8) as u64,
        inode_soft: le64(raw, 16) as u64, current_inodes: le64(raw, 24) as u64,
        block_hard: le64(raw, 32) as u64, block_soft: le64(raw, 40) as u64,
        current_space: le64(raw, 48) as u64, block_time: le64(raw, 56) as u64, inode_time: le64(raw, 64) as u64,
    } }
}
#[verifier::opaque]
pub open spec fn parsed_record(raw: Seq<u8>, version: u32) -> Option<Record> {
    if width(version).is_none() || raw.len() != width(version).unwrap()
        || (forall|i: int| 0 <= i < raw.len() ==> raw[i] == 0) { None }
    else {
        let value = fields(raw, version);
        Some(if version == 0 || bytes::le32(raw, 4) == 0 { normalized_record(value) } else { value })
    }
}
pub open spec fn info_image(info: Info) -> Seq<u8> {
    bytes::encoded_le(info.block_grace) + bytes::encoded_le(info.inode_grace)
        + bytes::encoded_le(info.flags) + bytes::encoded_le(info.blocks)
        + bytes::encoded_le(info.free_block) + bytes::encoded_le(info.free_entry)
}
pub open spec fn tree_refs(raw: Seq<u8>) -> Seq<u32> {
    Seq::new(256, |i: int| bytes::le32(raw, i * 4) as u32)
}
pub open spec fn build_storage(raw: Seq<u8>, budget: u32) -> bool {
    2 <= budget <= MAX_BUILD_BLOCKS && raw.len() % (BLOCK_BYTES as nat) == 0
        && raw.len() <= budget as nat * BLOCK_BYTES
}
pub open spec fn tree_bounded(raw: Seq<u8>, nodes: Set<u32>) -> bool {
    forall|node: u32| #[trigger] nodes.contains(node) ==> node > 0
        && (node as nat + 1) * BLOCK_BYTES <= raw.len()
        && forall|i: int| 0 <= i < 256 ==> #[trigger] bytes::le32(raw, node as int * BLOCK_BYTES + i * 4)
            < raw.len() / (BLOCK_BYTES as nat)
}
/// Every allocated non-header block has exactly one role. Node levels increase
/// on every edge, so references are bounded and the radix graph is acyclic.
#[verifier::opaque]
pub open spec fn radix_layout(raw: Seq<u8>, levels: Map<u32, nat>, data: Set<u32>) -> bool {
    &&& raw.len() >= 2 * BLOCK_BYTES && raw.len() % (BLOCK_BYTES as nat) == 0
    &&& raw.len() / (BLOCK_BYTES as nat) <= MAX_BUILD_BLOCKS
    &&& levels.dom().contains(ROOT_BLOCK) && levels[ROOT_BLOCK] == 0
    &&& (forall|node: u32| #[trigger] levels.dom().contains(node) ==> node > 0
        && (node as nat + 1) * BLOCK_BYTES <= raw.len() && levels[node] < 4
        && !data.contains(node))
    &&& (forall|block: u32| #[trigger] data.contains(block) ==> ROOT_BLOCK < block
        && (block as nat + 1) * BLOCK_BYTES <= raw.len() && !levels.dom().contains(block))
    &&& (forall|block: u32| 0 < block < raw.len() / (BLOCK_BYTES as nat)
        ==> #[trigger] levels.dom().contains(block) || data.contains(block))
    &&& (forall|node: u32, index: int| levels.dom().contains(node) && 0 <= index < 256
        ==> #[trigger] radix_link(raw, levels, data, node, index))
}

#[verifier::opaque]
pub open spec fn radix_link(raw: Seq<u8>, levels: Map<u32, nat>, data: Set<u32>, node: u32, index: int) -> bool {
    let next = bytes::le32(raw, node as int * BLOCK_BYTES + index * 4);
    next == 0 || (next < raw.len() / (BLOCK_BYTES as nat)
        && if levels[node] < 3 {
            levels.dom().contains(next as u32) && levels[next as u32] == levels[node] + 1
        } else { data.contains(next as u32) })
}

proof fn radix_root_properties(raw: Seq<u8>, levels: Map<u32, nat>, data: Set<u32>)
    requires radix_layout(raw, levels, data),
    ensures levels.dom().contains(ROOT_BLOCK), levels[ROOT_BLOCK] == 0,
{
    reveal(radix_layout);
}

proof fn radix_node_properties(raw: Seq<u8>, levels: Map<u32, nat>, data: Set<u32>, node: u32, index: int)
    requires radix_layout(raw, levels, data), levels.dom().contains(node), 0 <= index < 256,
    ensures node > 0, (node as nat + 1) * BLOCK_BYTES <= raw.len(), levels[node] < 4,
        radix_link(raw, levels, data, node, index),
        bytes::le32(raw, node as int * BLOCK_BYTES + index * 4) < raw.len() / (BLOCK_BYTES as nat),
        bytes::le32(raw, node as int * BLOCK_BYTES + index * 4) != 0 ==> {
            let next = bytes::le32(raw, node as int * BLOCK_BYTES + index * 4) as u32;
            if levels[node] < 3 { levels.dom().contains(next) && levels[next] == levels[node] + 1 }
            else { data.contains(next) }
        },
{
    reveal(radix_layout);
    reveal(radix_link);
}

proof fn radix_data_properties(raw: Seq<u8>, levels: Map<u32, nat>, data: Set<u32>, block: u32)
    requires radix_layout(raw, levels, data), data.contains(block),
    ensures ROOT_BLOCK < block, (block as nat + 1) * BLOCK_BYTES <= raw.len(),
{
    reveal(radix_layout);
}

proof fn radix_empty(raw: Seq<u8>)
    requires raw == Seq::<u8>::new(2 * BLOCK_BYTES as nat, |i: int| 0u8),
    ensures radix_layout(raw, Map::<u32, nat>::empty().insert(ROOT_BLOCK, 0), Set::<u32>::empty()),
{
    reveal(radix_layout);
    reveal(radix_link);
}

/// Appending a private zero block preserves old pointers and creates one fresh
/// owner. None allocates data; Some(depth) allocates a radix node.
proof fn radix_append(raw: Seq<u8>, levels: Map<u32, nat>, data: Set<u32>, number: u32, level: Option<nat>)
    requires radix_layout(raw, levels, data), raw.len() == number as nat * BLOCK_BYTES,
        number < MAX_BUILD_BLOCKS, level.is_some() ==> level.unwrap() < 4,
    ensures radix_layout(raw + Seq::<u8>::new(BLOCK_BYTES as nat, |i: int| 0u8),
        if level.is_some() { levels.insert(number, level.unwrap()) } else { levels },
        if level.is_some() { data } else { data.insert(number) }),
        !levels.dom().contains(number), !data.contains(number), ROOT_BLOCK < number,
{
    reveal(radix_layout);
    reveal(radix_link);
    let after = raw + Seq::<u8>::new(BLOCK_BYTES as nat, |i: int| 0u8);
    let new_levels = if level.is_some() { levels.insert(number, level.unwrap()) } else { levels };
    let new_data = if level.is_some() { data } else { data.insert(number) };
    assert(ROOT_BLOCK < number);
    assert(!levels.dom().contains(number));
    assert(!data.contains(number));
    assert(after.len() == (number as nat + 1) * BLOCK_BYTES);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(raw.len() as int, BLOCK_BYTES as int);
    assert(raw.len() / (BLOCK_BYTES as nat) == number as nat);
    assert forall|node: u32| #[trigger] new_levels.dom().contains(node)
        implies node > 0 && (node as nat + 1) * BLOCK_BYTES <= after.len()
            && new_levels[node] < 4 && !new_data.contains(node) by {
        if node == number { assert(level.is_some()); }
        else { assert(levels.dom().contains(node)); }
    }
    assert forall|block: u32| #[trigger] new_data.contains(block)
        implies ROOT_BLOCK < block && (block as nat + 1) * BLOCK_BYTES <= after.len()
            && !new_levels.dom().contains(block) by {
        if block == number { assert(level.is_none()); }
        else { assert(data.contains(block)); }
    }
    assert forall|block: u32| 0 < block < after.len() / (BLOCK_BYTES as nat)
        implies #[trigger] new_levels.dom().contains(block) || new_data.contains(block) by {
        if block == number {
            if level.is_some() { assert(new_levels.dom().contains(block)); }
            else { assert(new_data.contains(block)); }
        } else {
            assert(block < number);
            assert(block < raw.len() / (BLOCK_BYTES as nat));
            assert(levels.dom().contains(block) || data.contains(block));
        }
    }
    assert forall|node: u32, index: int| new_levels.dom().contains(node) && 0 <= index < 256
        implies #[trigger] radix_link(after, new_levels, new_data, node, index) by {
        if node == number {
            assert(bytes::le32(after, node as int * BLOCK_BYTES + index * 4) == 0);
        } else {
            let at = node as int * BLOCK_BYTES + index * 4;
            assert(bytes::le32(after, at) == bytes::le32(raw, at));
            assert(radix_link(raw, levels, data, node, index));
        }
    }
}

/// Frame a write wholly contained in the header or one owned data block.
proof fn radix_non_node_write(before: Seq<u8>, after: Seq<u8>, levels: Map<u32, nat>, data: Set<u32>, block: u32)
    requires radix_layout(before, levels, data), before.len() == after.len(),
        block == 0 || data.contains(block),
        forall|at: int| 0 <= at < before.len()
            && (at < block as int * BLOCK_BYTES || (block as int + 1) * BLOCK_BYTES <= at)
            ==> #[trigger] after[at] == before[at],
    ensures radix_layout(after, levels, data),
{
    reveal(radix_layout);
    reveal(radix_link);
    assert forall|node: u32, index: int| levels.dom().contains(node) && 0 <= index < 256
        implies #[trigger] radix_link(after, levels, data, node, index) by {
        assert(node != block);
        let at = node as int * BLOCK_BYTES + index * 4;
        assert(bytes::le32(after, at) == bytes::le32(before, at));
        assert(radix_link(before, levels, data, node, index));
    }
}

proof fn radix_non_node_splice(raw: Seq<u8>, levels: Map<u32, nat>, data: Set<u32>, block: u32, at: int, value: Seq<u8>)
    requires radix_layout(raw, levels, data), block == 0 || data.contains(block),
        block as int * BLOCK_BYTES <= at, at + value.len() <= (block as int + 1) * BLOCK_BYTES,
        (block as int + 1) * BLOCK_BYTES <= raw.len(),
    ensures radix_layout(bytes::splice(raw, at, value), levels, data),
{
    let after = bytes::splice(raw, at, value);
    assert forall|i: int| 0 <= i < raw.len()
        && (i < block as int * BLOCK_BYTES || (block as int + 1) * BLOCK_BYTES <= i)
        implies #[trigger] after[i] == raw[i] by {
        bytes::splice_frame(raw, at, value, i);
    }
    radix_non_node_write(raw, after, levels, data, block);
}

proof fn radix_data_byte(raw: Seq<u8>, levels: Map<u32, nat>, data: Set<u32>, block: u32, at: int, value: u8)
    requires radix_layout(raw, levels, data), data.contains(block),
        block as int * BLOCK_BYTES <= at < (block as int + 1) * BLOCK_BYTES,
    ensures radix_layout(raw.update(at, value), levels, data),
{
    radix_data_properties(raw, levels, data, block);
    radix_non_node_write(raw, raw.update(at, value), levels, data, block);
}

proof fn radix_pointer_write(raw: Seq<u8>, levels: Map<u32, nat>, data: Set<u32>, node: u32, index: int, target: u32)
    requires radix_layout(raw, levels, data), levels.dom().contains(node), 0 <= index < 256,
        if levels[node] < 3 { levels.dom().contains(target) && levels[target] == levels[node] + 1 }
        else { data.contains(target) },
    ensures radix_layout(bytes::splice(raw, node as int * BLOCK_BYTES + index * 4, bytes::encoded_le(target)), levels, data),
{
    radix_node_properties(raw, levels, data, node, index);
    reveal(radix_layout);
    reveal(radix_link);
    bytes::little_endian_encoding_recovers_every_word(target);
    let at = node as int * BLOCK_BYTES + index * 4;
    let after = bytes::splice(raw, at, bytes::encoded_le(target));
    assert forall|other: u32, slot: int| levels.dom().contains(other) && 0 <= slot < 256
        implies #[trigger] radix_link(after, levels, data, other, slot) by {
        let word = other as int * BLOCK_BYTES + slot * 4;
        if other == node && slot == index {
            assert(bytes::le32(after, word) == target as nat);
        } else {
            assert(word + 4 <= at || at + 4 <= word);
            bytes::splice_frame(raw, at, bytes::encoded_le(target), word);
            bytes::splice_frame(raw, at, bytes::encoded_le(target), word + 1);
            bytes::splice_frame(raw, at, bytes::encoded_le(target), word + 2);
            bytes::splice_frame(raw, at, bytes::encoded_le(target), word + 3);
            assert(radix_link(raw, levels, data, other, slot));
        }
    }
}

pub proof fn encoded64_recovers(value: u64)
    ensures encoded64(value).len() == 8, le64(encoded64(value), 0) == value as nat,
{
    reveal(encoded64);
    bytes::little_endian_encoding_recovers_every_word(value as u32);
    bytes::little_endian_encoding_recovers_every_word((value / 4294967296) as u32);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(value as int, 4294967296);
    assert((value as u32) as nat == value as nat % 4294967296) by (bit_vector);
}
proof fn encoded64_length(value: u64)
    ensures encoded64(value).len() == 8,
{
    reveal(encoded64);
}

proof fn encoded64_zero()
    ensures encoded64(0) == Seq::<u8>::new(8, |i: int| 0u8),
{
    reveal(encoded64);
    assert(encoded64(0) =~= Seq::<u8>::new(8, |i: int| 0u8));
}

proof fn record64_lengths(record: Record)
    ensures encoded64(record.inode_hard).len() == 8, encoded64(record.inode_soft).len() == 8,
        encoded64(record.current_inodes).len() == 8, encoded64(record.block_hard).len() == 8,
        encoded64(record.block_soft).len() == 8, encoded64(record.current_space).len() == 8,
        encoded64(record.block_time).len() == 8, encoded64(record.inode_time).len() == 8,
{
    encoded64_length(record.inode_hard); encoded64_length(record.inode_soft);
    encoded64_length(record.current_inodes); encoded64_length(record.block_hard);
    encoded64_length(record.block_soft); encoded64_length(record.current_space);
    encoded64_length(record.block_time); encoded64_length(record.inode_time);
}

#[verifier::opaque]
spec fn v0_word(record: Record, index: nat) -> u32 {
    if index == 0 { record.id } else if index == 1 { record.inode_hard as u32 }
    else if index == 2 { record.inode_soft as u32 } else if index == 3 { record.current_inodes as u32 }
    else if index == 4 { record.block_hard as u32 } else { record.block_soft as u32 }
}

#[verifier::opaque]
spec fn v0_tail(record: Record, index: nat) -> u64 {
    if index == 0 { record.current_space } else if index == 1 { record.block_time }
    else { record.inode_time }
}

/// Fixed-width framing stays separate from interpreting any encoded word.
proof fn record_image_v0_word_bytes(record: Record, index: nat)
    requires index < 6,
    ensures record_image(record, 0).len() == 48,
        record_image(record, 0).subrange(index as int * 4, 4 + index as int * 4)
            == bytes::encoded_le(v0_word(record, index)),
{
    record64_lengths(record);
    reveal(record_image);
    reveal(v0_word);
    assert(record_image(record, 0).subrange(index as int * 4, 4 + index as int * 4)
        =~= bytes::encoded_le(v0_word(record, index)));
}

proof fn record_image_v0_word_recovers(record: Record, index: nat)
    requires index < 6,
    ensures record_image(record, 0).len() == 48,
        bytes::le32(record_image(record, 0), index as int * 4) == v0_word(record, index) as nat,
{
    record_image_v0_word_bytes(record, index);
    bytes::little_endian_encoding_recovers_every_word(v0_word(record, index));
    let image = record_image(record, 0);
    assert(bytes::le32(image.subrange(index as int * 4, 4 + index as int * 4), 0)
        == bytes::le32(image, index as int * 4));
}

proof fn record_image_v0_tail_bytes(record: Record, index: nat)
    requires index < 3,
    ensures record_image(record, 0).len() == 48,
        record_image(record, 0).subrange(24 + index as int * 8, 32 + index as int * 8)
            == encoded64(v0_tail(record, index)),
{
    record64_lengths(record);
    reveal(record_image);
    reveal(v0_tail);
    assert(record_image(record, 0).subrange(24 + index as int * 8, 32 + index as int * 8)
        =~= encoded64(v0_tail(record, index)));
}

proof fn record_image_v0_tail_recovers(record: Record, index: nat)
    requires index < 3,
    ensures record_image(record, 0).len() == 48,
        le64(record_image(record, 0), 24 + index as int * 8) == v0_tail(record, index) as nat,
{
    record_image_v0_tail_bytes(record, index);
    encoded64_recovers(v0_tail(record, index));
    le64_subrange(record_image(record, 0), 24 + index as int * 8);
}

/// Each format's recovery proof unfolds only its own fixed wire layout.
proof fn record_image_v0_recovers(record: Record)
    requires representable(record, 0),
    ensures record_image(record, 0).len() == 48,
        fields(record_image(record, 0), 0) == record,
{
    record_image_v0_word_recovers(record, 0);
    record_image_v0_word_recovers(record, 1);
    record_image_v0_word_recovers(record, 2);
    record_image_v0_word_recovers(record, 3);
    record_image_v0_word_recovers(record, 4);
    record_image_v0_word_recovers(record, 5);
    record_image_v0_tail_recovers(record, 0);
    record_image_v0_tail_recovers(record, 1);
    record_image_v0_tail_recovers(record, 2);
    reveal(v0_word);
    reveal(v0_tail);
    reveal(fields);
}

#[verifier::opaque]
spec fn v1_field(record: Record, index: nat) -> u64 {
    if index == 0 { record.inode_hard } else if index == 1 { record.inode_soft }
    else if index == 2 { record.current_inodes } else if index == 3 { record.block_hard }
    else if index == 4 { record.block_soft } else if index == 5 { record.current_space }
    else if index == 6 { record.block_time } else { record.inode_time }
}

/// Framing is proved on eight-byte slices before interpreting any words.
proof fn record_image_v1_field_bytes(record: Record, index: nat)
    requires index < 8,
    ensures record_image(record, 1).len() == 72,
        record_image(record, 1).subrange(8 + index as int * 8, 16 + index as int * 8)
            == encoded64(v1_field(record, index)),
{
    record64_lengths(record);
    reveal(record_image);
    reveal(v1_field);
    assert(record_image(record, 1).subrange(8 + index as int * 8, 16 + index as int * 8)
        =~= encoded64(v1_field(record, index)));
}

proof fn le64_subrange(raw: Seq<u8>, at: int)
    requires 0 <= at, at + 8 <= raw.len(),
    ensures le64(raw.subrange(at, at + 8), 0) == le64(raw, at),
{
}

proof fn record_image_v1_field_recovers(record: Record, index: nat)
    requires index < 8,
    ensures record_image(record, 1).len() == 72,
        le64(record_image(record, 1), 8 + index as int * 8) == v1_field(record, index) as nat,
{
    record_image_v1_field_bytes(record, index);
    encoded64_recovers(v1_field(record, index));
    le64_subrange(record_image(record, 1), 8 + index as int * 8);
}

proof fn record_image_v1_header_recovers(record: Record)
    ensures record_image(record, 1).len() == 72,
        bytes::le32(record_image(record, 1), 0) == record.id as nat,
        bytes::le32(record_image(record, 1), 4) == 0,
{
    record64_lengths(record);
    bytes::little_endian_encoding_recovers_every_word(record.id);
    reveal(record_image);
}

proof fn record_image_v1_recovers(record: Record)
    ensures record_image(record, 1).len() == 72,
        fields(record_image(record, 1), 1) == record,
        bytes::le32(record_image(record, 1), 4) == 0,
{
    record_image_v1_header_recovers(record);
    record_image_v1_field_recovers(record, 0);
    record_image_v1_field_recovers(record, 1);
    record_image_v1_field_recovers(record, 2);
    record_image_v1_field_recovers(record, 3);
    record_image_v1_field_recovers(record, 4);
    record_image_v1_field_recovers(record, 5);
    record_image_v1_field_recovers(record, 6);
    record_image_v1_field_recovers(record, 7);
    reveal(v1_field);
    reveal(fields);
}

proof fn record_image_recovers(record: Record, version: u32)
    requires representable(record, version),
    ensures record_image(record, version).len() == width(version).unwrap(),
        fields(record_image(record, version), version) == record,
        version == 1 ==> bytes::le32(record_image(record, version), 4) == 0,
{
    if version == 0 { record_image_v0_recovers(record); }
    else { record_image_v1_recovers(record); }
}

proof fn zero_bytes_have_zero_fields(raw: Seq<u8>, version: u32)
    requires version <= 1, raw.len() == width(version).unwrap(),
        forall|i: int| 0 <= i < raw.len() ==> #[trigger] raw[i] == 0,
    ensures zero_record(fields(raw, version)),
{
    reveal(fields);
}

proof fn record_image_zero_iff(record: Record, version: u32)
    requires representable(record, version),
    ensures (forall|i: int| 0 <= i < record_image(record, version).len()
        ==> #[trigger] record_image(record, version)[i] == 0) == zero_record(record),
{
    record_image_recovers(record, version);
    let image = record_image(record, version);
    if forall|i: int| 0 <= i < image.len() ==> #[trigger] image[i] == 0 {
        zero_bytes_have_zero_fields(image, version);
    }
    if zero_record(record) {
        encoded64_zero();
        assert(image =~= Seq::<u8>::new(width(version).unwrap(), |i: int| 0u8)) by {
            reveal(record_image);
        }
    }
}

proof fn splice_zero_suffix(prefix: Seq<u8>, value: Seq<u8>, tail: nat)
    ensures bytes::splice(prefix + Seq::<u8>::new(value.len() + tail, |i: int| 0u8),
        prefix.len() as int, value) == prefix + value + Seq::<u8>::new(tail, |i: int| 0u8),
{
    assert(bytes::splice(prefix + Seq::<u8>::new(value.len() + tail, |i: int| 0u8),
        prefix.len() as int, value) =~= prefix + value + Seq::<u8>::new(tail, |i: int| 0u8));
}

proof fn split_zero_suffix(prefix: Seq<u8>, first: nat, last: nat)
    ensures prefix + Seq::<u8>::new(first + last, |i: int| 0u8)
        == prefix + Seq::<u8>::new(first, |i: int| 0u8) + Seq::<u8>::new(last, |i: int| 0u8),
{
    assert(prefix + Seq::<u8>::new(first + last, |i: int| 0u8)
        =~= prefix + Seq::<u8>::new(first, |i: int| 0u8) + Seq::<u8>::new(last, |i: int| 0u8));
}

proof fn record_writes_v0_are_image(record: Record)
    ensures record_writes(record, 0) == record_image(record, 0),
{
    record64_lengths(record);
    reveal(record_writes);
    reveal(record_image);
    splice_zero_suffix(Seq::<u8>::empty(), bytes::encoded_le(record.id), 44);
    splice_zero_suffix(bytes::encoded_le(record.id), bytes::encoded_le(record.inode_hard as u32), 40);
    splice_zero_suffix(bytes::encoded_le(record.id) + bytes::encoded_le(record.inode_hard as u32), bytes::encoded_le(record.inode_soft as u32), 36);
    splice_zero_suffix(bytes::encoded_le(record.id) + bytes::encoded_le(record.inode_hard as u32) + bytes::encoded_le(record.inode_soft as u32), bytes::encoded_le(record.current_inodes as u32), 32);
    splice_zero_suffix(bytes::encoded_le(record.id) + bytes::encoded_le(record.inode_hard as u32) + bytes::encoded_le(record.inode_soft as u32) + bytes::encoded_le(record.current_inodes as u32), bytes::encoded_le(record.block_hard as u32), 28);
    splice_zero_suffix(bytes::encoded_le(record.id) + bytes::encoded_le(record.inode_hard as u32) + bytes::encoded_le(record.inode_soft as u32) + bytes::encoded_le(record.current_inodes as u32) + bytes::encoded_le(record.block_hard as u32), bytes::encoded_le(record.block_soft as u32), 24);
    splice_zero_suffix(bytes::encoded_le(record.id) + bytes::encoded_le(record.inode_hard as u32) + bytes::encoded_le(record.inode_soft as u32) + bytes::encoded_le(record.current_inodes as u32) + bytes::encoded_le(record.block_hard as u32) + bytes::encoded_le(record.block_soft as u32), encoded64(record.current_space), 16);
    splice_zero_suffix(bytes::encoded_le(record.id) + bytes::encoded_le(record.inode_hard as u32) + bytes::encoded_le(record.inode_soft as u32) + bytes::encoded_le(record.current_inodes as u32) + bytes::encoded_le(record.block_hard as u32) + bytes::encoded_le(record.block_soft as u32) + encoded64(record.current_space), encoded64(record.block_time), 8);
    splice_zero_suffix(bytes::encoded_le(record.id) + bytes::encoded_le(record.inode_hard as u32) + bytes::encoded_le(record.inode_soft as u32) + bytes::encoded_le(record.current_inodes as u32) + bytes::encoded_le(record.block_hard as u32) + bytes::encoded_le(record.block_soft as u32) + encoded64(record.current_space) + encoded64(record.block_time), encoded64(record.inode_time), 0);
}

proof fn record_writes_v1_are_image(record: Record)
    ensures record_writes(record, 1) == record_image(record, 1),
{
    record64_lengths(record);
    reveal(record_writes);
    reveal(record_image);
    splice_zero_suffix(Seq::<u8>::empty(), bytes::encoded_le(record.id), 68);
    split_zero_suffix(bytes::encoded_le(record.id), 4, 64);
    assert(Seq::<u8>::new(4, |i: int| 0u8) =~= seq![0u8, 0u8, 0u8, 0u8]);
    splice_zero_suffix(bytes::encoded_le(record.id) + seq![0u8, 0u8, 0u8, 0u8], encoded64(record.inode_hard), 56);
    splice_zero_suffix(bytes::encoded_le(record.id) + seq![0u8, 0u8, 0u8, 0u8] + encoded64(record.inode_hard), encoded64(record.inode_soft), 48);
    splice_zero_suffix(bytes::encoded_le(record.id) + seq![0u8, 0u8, 0u8, 0u8] + encoded64(record.inode_hard) + encoded64(record.inode_soft), encoded64(record.current_inodes), 40);
    splice_zero_suffix(bytes::encoded_le(record.id) + seq![0u8, 0u8, 0u8, 0u8] + encoded64(record.inode_hard) + encoded64(record.inode_soft) + encoded64(record.current_inodes), encoded64(record.block_hard), 32);
    splice_zero_suffix(bytes::encoded_le(record.id) + seq![0u8, 0u8, 0u8, 0u8] + encoded64(record.inode_hard) + encoded64(record.inode_soft) + encoded64(record.current_inodes) + encoded64(record.block_hard), encoded64(record.block_soft), 24);
    splice_zero_suffix(bytes::encoded_le(record.id) + seq![0u8, 0u8, 0u8, 0u8] + encoded64(record.inode_hard) + encoded64(record.inode_soft) + encoded64(record.current_inodes) + encoded64(record.block_hard) + encoded64(record.block_soft), encoded64(record.current_space), 16);
    splice_zero_suffix(bytes::encoded_le(record.id) + seq![0u8, 0u8, 0u8, 0u8] + encoded64(record.inode_hard) + encoded64(record.inode_soft) + encoded64(record.current_inodes) + encoded64(record.block_hard) + encoded64(record.block_soft) + encoded64(record.current_space), encoded64(record.block_time), 8);
    splice_zero_suffix(bytes::encoded_le(record.id) + seq![0u8, 0u8, 0u8, 0u8] + encoded64(record.inode_hard) + encoded64(record.inode_soft) + encoded64(record.current_inodes) + encoded64(record.block_hard) + encoded64(record.block_soft) + encoded64(record.current_space) + encoded64(record.block_time), encoded64(record.inode_time), 0);
}

proof fn record_writes_are_image(record: Record, version: u32)
    requires version <= 1,
    ensures record_writes(record, version) == record_image(record, version),
{
    if version == 0 { record_writes_v0_are_image(record); }
    else { record_writes_v1_are_image(record); }
}

/// The Linux ID-zero escape changes only the final inode-time word pair.
proof fn zero_image_escape(record: Record, version: u32)
    requires representable(record, version), zero_record(record),
    ensures bytes::splice(record_image(record, version),
        if version == 0 { 40int } else { 64int }, encoded64(1)) == canonical_image(record, version),
{
    encoded64_zero();
    encoded64_length(1);
    reveal(record_image);
    reveal(canonical_image);
    assert(bytes::splice(record_image(record, version),
        if version == 0 { 40int } else { 64int }, encoded64(1)) =~= canonical_image(record, version));
}

pub proof fn canonical_encoding_has_documented_alias(record: Record, version: u32)
    requires representable(record, version),
    ensures parsed_record(canonical_image(record, version), version) == Some(normalized_record(record)),
{
    let escaped = if zero_record(record) { Record { inode_time: 1, ..record } } else { record };
    record_image_recovers(escaped, version);
    record_image_zero_iff(escaped, version);
    assert(!zero_record(escaped));
    assert(normalized_record(escaped) == normalized_record(record));
    reveal(canonical_image);
    reveal(parsed_record);
}

pub fn record_bytes(version: u32) -> (r: Option<usize>)
    ensures match r { Some(n) => width(version) == Some(n as nat) && (n == 48 || n == 72),
        None => width(version).is_none() },
{
    if version == 0 { Some(48) } else if version == 1 { Some(72) } else { None }
}

pub fn records_per_block(version: u32) -> (r: Option<usize>)
    ensures match r { Some(n) => (version == 0 && n == 21) || (version == 1 && n == 14),
        None => version > 1 },
{
    match record_bytes(version) { Some(width) => Some((BLOCK_BYTES - DATA_HEADER_BYTES) / width), None => None }
}

pub fn read_u64(raw: &[u8], offset: usize) -> (r: Option<u64>)
    ensures match r { Some(value) => offset as int + 8 <= raw.len() && value as nat == le64(raw@, offset as int),
        None => offset as int + 8 > raw.len() },
{
    if offset > raw.len() || raw.len() - offset < 8 { return None; }
    let low = match bytes::read_le32(raw, offset) { Some(v) => v, None => { return None; } };
    let high = match bytes::read_le32(raw, offset + 4) { Some(v) => v, None => { return None; } };
    Some(low as u64 + (high as u64) * 4294967296)
}

fn put_u32(raw: &mut [u8], offset: usize, value: u32) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r == (offset as int + 4 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, offset as int, bytes::encoded_le(value)) } else { old(raw)@ },
{
    if offset > raw.len() || raw.len() - offset < 4 { return false; }
    let encoded = bytes::encode_le32(value);
    let ghost before = raw@;
    let mut i = 0usize;
    while i < 4
        invariant i <= 4, offset <= raw.len(), raw.len() - offset >= 4,
            raw.len() == before.len(), encoded@ == bytes::encoded_le(value),
            raw@ == bytes::splice(before, offset as int, bytes::encoded_le(value).subrange(0, i as int)),
        decreases 4 - i,
    {
        raw[offset + i] = encoded[i];
        proof {
            assert(raw@ =~= bytes::splice(before, offset as int,
                bytes::encoded_le(value).subrange(0, i as int + 1)));
        }
        i += 1;
    }
    proof {
        assert(bytes::encoded_le(value).subrange(0, 4) =~= bytes::encoded_le(value));
    }
    true
}

/// The ghost arguments retain the node frame through ordinary data/header writes.
fn put_non_node_u32(raw: &mut [u8], offset: usize, value: u32, block: u32,
    Ghost(levels): Ghost<Map<u32, nat>>, Ghost(data): Ghost<Set<u32>>) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r == (offset as int + 4 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, offset as int, bytes::encoded_le(value)) } else { old(raw)@ },
        radix_layout(old(raw)@, levels, data) && (block == 0 || data.contains(block))
            && block as int * BLOCK_BYTES <= offset
            && offset as int + 4 <= (block as int + 1) * BLOCK_BYTES
            && (block as int + 1) * BLOCK_BYTES <= old(raw).len()
            ==> radix_layout(final(raw)@, levels, data),
{
    let ghost before = raw@;
    let result = put_u32(raw, offset, value);
    proof {
        if radix_layout(before, levels, data) && (block == 0 || data.contains(block))
            && block as int * BLOCK_BYTES <= offset
            && offset as int + 4 <= (block as int + 1) * BLOCK_BYTES
            && (block as int + 1) * BLOCK_BYTES <= before.len() {
            radix_non_node_splice(before, levels, data, block, offset as int, bytes::encoded_le(value));
        }
    }
    result
}

/// Publish one aligned header word while exposing only decoded word framing.
/// This proof boundary keeps the eight final stores out of the tree builder's
/// solver context; the executable operation remains the same checked store.
fn put_header_word(raw: &mut [u8], offset: usize, value: u32,
    Ghost(levels): Ghost<Map<u32, nat>>, Ghost(data): Ghost<Set<u32>>) -> (r: bool)
    requires old(raw).len() >= 2 * BLOCK_BYTES, offset <= 28, offset % 4 == 0,
        radix_layout(old(raw)@, levels, data),
    ensures r, final(raw).len() == old(raw).len(),
        radix_layout(final(raw)@, levels, data),
        bytes::le32(final(raw)@, offset as int) == value as nat,
        forall|word: int| 0 <= word <= 28 && word % 4 == 0 && word != offset
            ==> #[trigger] bytes::le32(final(raw)@, word) == bytes::le32(old(raw)@, word),
{
    let ghost before = raw@;
    let result = put_non_node_u32(raw, offset, value, 0, Ghost(levels), Ghost(data));
    proof {
        bytes::little_endian_encoding_recovers_every_word(value);
        assert(bytes::le32(raw@, offset as int) == value as nat);
        assert forall|word: int| 0 <= word <= 28 && word % 4 == 0 && word != offset
            implies #[trigger] bytes::le32(raw@, word) == bytes::le32(before, word) by {
            assert(word + 4 <= offset || offset as int + 4 <= word);
            bytes::splice_frame(before, offset as int, bytes::encoded_le(value), word);
            bytes::splice_frame(before, offset as int, bytes::encoded_le(value), word + 1);
            bytes::splice_frame(before, offset as int, bytes::encoded_le(value), word + 2);
            bytes::splice_frame(before, offset as int, bytes::encoded_le(value), word + 3);
        }
    }
    result
}

/// Seal the file header after all private data/tree/free-list edits.
fn finish_build_header(raw: &mut [u8], kind: QuotaType, version: u32,
    block_grace: u32, inode_grace: u32, free_entry: u32,
    Ghost(levels): Ghost<Map<u32, nat>>, Ghost(data): Ghost<Set<u32>>) -> (r: bool)
    requires old(raw).len() >= 2 * BLOCK_BYTES,
        old(raw).len() / BLOCK_BYTES <= MAX_BUILD_BLOCKS,
        radix_layout(old(raw)@, levels, data),
    ensures r, final(raw).len() == old(raw).len(),
        radix_layout(final(raw)@, levels, data),
        bytes::le32(final(raw)@, 0) == type_magic(kind),
        bytes::le32(final(raw)@, 4) == version,
        bytes::le32(final(raw)@, 8) == block_grace,
        bytes::le32(final(raw)@, 12) == inode_grace,
        bytes::le32(final(raw)@, 16) == 0,
        bytes::le32(final(raw)@, 20) == final(raw).len() / BLOCK_BYTES,
        bytes::le32(final(raw)@, 24) == 0,
        bytes::le32(final(raw)@, 28) == free_entry,
{
    let blocks = (raw.len() / BLOCK_BYTES) as u32;
    if !put_header_word(raw, 0, magic(kind), Ghost(levels), Ghost(data))
        || !put_header_word(raw, 4, version, Ghost(levels), Ghost(data))
        || !put_header_word(raw, 8, block_grace, Ghost(levels), Ghost(data))
        || !put_header_word(raw, 12, inode_grace, Ghost(levels), Ghost(data))
        || !put_header_word(raw, 16, 0, Ghost(levels), Ghost(data))
        || !put_header_word(raw, 20, blocks, Ghost(levels), Ghost(data))
        || !put_header_word(raw, 24, 0, Ghost(levels), Ghost(data))
        || !put_header_word(raw, 28, free_entry, Ghost(levels), Ghost(data)) { return false; }
    true
}

fn put_u64(raw: &mut [u8], offset: usize, value: u64) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r == (offset as int + 8 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, offset as int, encoded64(value)) } else { old(raw)@ },
{
    proof { reveal(encoded64); }
    if offset > raw.len() || raw.len() - offset < 8 { return false; }
    put_u32(raw, offset, value as u32) && put_u32(raw, offset + 4, (value / 4294967296) as u32)
}

pub fn parse_header(raw: &[u8], kind: QuotaType) -> (r: Option<Header>)
    ensures match r {
        Some(header) => raw.len() >= 8 && bytes::le32(raw@, 0) == type_magic(kind)
            && header.kind == kind && header.version == bytes::le32(raw@, 4) && header.version <= 1,
        None => raw.len() < 8 || bytes::le32(raw@, 0) != type_magic(kind) || bytes::le32(raw@, 4) > 1,
    },
{
    let m = match bytes::read_le32(raw, 0) { Some(v) => v, None => { return None; } };
    let version = match bytes::read_le32(raw, 4) { Some(v) => v, None => { return None; } };
    if m != magic(kind) || version > 1 { return None; }
    Some(Header { kind, version })
}

pub fn encode_header(header: Header) -> (r: Option<[u8; 8]>)
    ensures match r {
        Some(raw) => header.version <= 1
            && raw@ == bytes::encoded_le(type_magic(header.kind)) + bytes::encoded_le(header.version),
        None => header.version > 1,
    },
{
    if header.version > 1 { return None; }
    let m = bytes::encode_le32(magic(header.kind)); let v = bytes::encode_le32(header.version);
    Some([m[0], m[1], m[2], m[3], v[0], v[1], v[2], v[3]])
}

/// Encode the 24-byte information structure, not its surrounding file header.
/// Flags are retained as bytes, without interpreting unsupported flag bits.
pub fn encode_info(info: Info) -> (r: Vec<u8>) ensures r@ == info_image(info), r.len() == 24 {
    let mut raw = Vec::<u8>::new(); let mut i = 0usize;
    while i < 24 invariant i <= 24, raw.len() == i,
        raw@ == Seq::<u8>::new(i as nat, |j: int| 0u8), decreases 24 - i,
    { raw.push(0); i += 1; }
    let _ = put_u32(raw.as_mut_slice(), 0, info.block_grace);
    let _ = put_u32(raw.as_mut_slice(), 4, info.inode_grace);
    let _ = put_u32(raw.as_mut_slice(), 8, info.flags);
    let _ = put_u32(raw.as_mut_slice(), 12, info.blocks);
    let _ = put_u32(raw.as_mut_slice(), 16, info.free_block);
    let _ = put_u32(raw.as_mut_slice(), 20, info.free_entry);
    raw
}

pub fn parse_info(raw: &[u8]) -> (r: Option<Info>)
    ensures match r { Some(info) => raw.len() >= 32 && info.blocks > ROOT_BLOCK
        && info.blocks as nat * BLOCK_BYTES <= raw.len()
        && (info.free_block == 0 || ROOT_BLOCK < info.free_block < info.blocks)
        && (info.free_entry == 0 || ROOT_BLOCK < info.free_entry < info.blocks)
        && info.block_grace == bytes::le32(raw@, 8) && info.inode_grace == bytes::le32(raw@, 12)
        && info.flags == bytes::le32(raw@, 16) && info.blocks == bytes::le32(raw@, 20)
        && info.free_block == bytes::le32(raw@, 24) && info.free_entry == bytes::le32(raw@, 28),
        None => true },
{
    if raw.len() < 32 { return None; }
    let block_grace = bytes::read_le32(raw, 8).unwrap();
    let inode_grace = bytes::read_le32(raw, 12).unwrap();
    let flags = bytes::read_le32(raw, 16).unwrap();
    let blocks = bytes::read_le32(raw, 20).unwrap();
    let free_block = bytes::read_le32(raw, 24).unwrap();
    let free_entry = bytes::read_le32(raw, 28).unwrap();
    if blocks <= ROOT_BLOCK || blocks as u64 * 1024 > raw.len() as u64 { return None; }
    if (free_block != 0 && (free_block <= ROOT_BLOCK || free_block >= blocks))
        || (free_entry != 0 && (free_entry <= ROOT_BLOCK || free_entry >= blocks)) { return None; }
    Some(Info { block_grace, inode_grace, flags, blocks, free_block, free_entry })
}

fn all_zero(raw: &[u8]) -> (r: bool)
    ensures r == (forall|i: int| 0 <= i < raw.len() ==> raw@[i] == 0),
{
    let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len(), forall|j: int| 0 <= j < i ==> raw@[j] == 0,
        decreases raw.len() - i,
    { if raw[i] != 0 { return false; } i += 1; }
    true
}

/// None identifies an unused all-zero slot or invalid byte length/version.
pub fn parse_record(raw: &[u8], version: u32) -> (r: Option<Record>)
    ensures r == parsed_record(raw@, version),
{
    proof { reveal(parsed_record); reveal(fields); }
    let width = match record_bytes(version) { Some(v) => v, None => { return None; } };
    if raw.len() != width || all_zero(raw) { return None; }
    let id = bytes::read_le32(raw, 0).unwrap();
    let (inode_hard, inode_soft, current_inodes, block_hard, block_soft,
        current_space, block_time, mut inode_time) = if version == 0 {
        (bytes::read_le32(raw, 4).unwrap() as u64, bytes::read_le32(raw, 8).unwrap() as u64,
         bytes::read_le32(raw, 12).unwrap() as u64, bytes::read_le32(raw, 16).unwrap() as u64,
         bytes::read_le32(raw, 20).unwrap() as u64, read_u64(raw, 24).unwrap(),
         read_u64(raw, 32).unwrap(), read_u64(raw, 40).unwrap())
    } else {
        (read_u64(raw, 8).unwrap(), read_u64(raw, 16).unwrap(), read_u64(raw, 24).unwrap(),
         read_u64(raw, 32).unwrap(), read_u64(raw, 40).unwrap(), read_u64(raw, 48).unwrap(),
         read_u64(raw, 56).unwrap(), read_u64(raw, 64).unwrap())
    };
    // Linux escapes the otherwise-unused zero record for ID zero with itime=1.
    if id == 0 && inode_hard == 0 && inode_soft == 0 && current_inodes == 0
        && block_hard == 0 && block_soft == 0 && current_space == 0 && block_time == 0 && inode_time == 1
        && (version == 0 || bytes::read_le32(raw, 4).unwrap() == 0) { inode_time = 0; }
    Some(Record { id, inode_hard, inode_soft, current_inodes, block_hard, block_soft,
        current_space, block_time, inode_time })
}

pub fn encode_record(record: Record, version: u32) -> (r: Option<Vec<u8>>)
    ensures match r {
        Some(raw) => representable(record, version) && raw@ == canonical_image(record, version)
            && raw.len() == width(version).unwrap()
            && parsed_record(raw@, version) == Some(normalized_record(record)),
        None => !representable(record, version),
    },
{
    let width = match record_bytes(version) { Some(v) => v, None => { return None; } };
    if version == 0 && (record.inode_hard > 0xffff_ffff || record.inode_soft > 0xffff_ffff
        || record.current_inodes > 0xffff_ffff || record.block_hard > 0xffff_ffff || record.block_soft > 0xffff_ffff) { return None; }
    let mut raw = Vec::<u8>::new(); let mut i = 0usize;
    while i < width invariant i <= width, raw.len() == i, width == 48 || width == 72,
        raw@ == Seq::<u8>::new(i as nat, |j: int| 0u8),
        decreases width - i,
    { raw.push(0); i += 1; }
    if !put_u32(raw.as_mut_slice(), 0, record.id) { return None; }
    if version == 0 {
        if !put_u32(raw.as_mut_slice(), 4, record.inode_hard as u32)
            || !put_u32(raw.as_mut_slice(), 8, record.inode_soft as u32)
            || !put_u32(raw.as_mut_slice(), 12, record.current_inodes as u32)
            || !put_u32(raw.as_mut_slice(), 16, record.block_hard as u32)
            || !put_u32(raw.as_mut_slice(), 20, record.block_soft as u32)
            || !put_u64(raw.as_mut_slice(), 24, record.current_space)
            || !put_u64(raw.as_mut_slice(), 32, record.block_time)
            || !put_u64(raw.as_mut_slice(), 40, record.inode_time) { return None; }
    } else {
        if !put_u64(raw.as_mut_slice(), 8, record.inode_hard)
            || !put_u64(raw.as_mut_slice(), 16, record.inode_soft)
            || !put_u64(raw.as_mut_slice(), 24, record.current_inodes)
            || !put_u64(raw.as_mut_slice(), 32, record.block_hard)
            || !put_u64(raw.as_mut_slice(), 40, record.block_soft)
            || !put_u64(raw.as_mut_slice(), 48, record.current_space)
            || !put_u64(raw.as_mut_slice(), 56, record.block_time)
            || !put_u64(raw.as_mut_slice(), 64, record.inode_time) { return None; }
    }
    proof {
        assert(raw@ == record_writes(record, version)) by { reveal(record_writes); }
        record_writes_are_image(record, version);
        record_image_zero_iff(record, version);
    }
    if all_zero(raw.as_slice()) {
        proof { zero_image_escape(record, version); }
        let offset = if version == 0 { 40usize } else { 64usize };
        if !put_u64(raw.as_mut_slice(), offset, 1) { return None; }
    } else {
        proof { reveal(canonical_image); }
    }
    proof { canonical_encoding_has_documented_alias(record, version); }
    Some(raw)
}

pub fn parse_data_header(raw: &[u8], version: u32, blocks: u32) -> (r: Option<DataHeader>)
    ensures match r {
        Some(header) => raw.len() == BLOCK_BYTES && blocks > ROOT_BLOCK && version <= 1
            && header.next_free == bytes::le32(raw@, 0) && header.previous_free == bytes::le32(raw@, 4)
            && header.entries == bytes::le16(raw@, 8)
            && header.next_free < blocks && header.previous_free < blocks
            && header.entries as nat <= if version == 0 { 21nat } else { 14nat },
        None => true,
    },
{
    let slots = match records_per_block(version) { Some(v) => v, None => { return None; } };
    if raw.len() != BLOCK_BYTES || blocks <= ROOT_BLOCK { return None; }
    let next_free = bytes::read_le32(raw, 0).unwrap();
    let previous_free = bytes::read_le32(raw, 4).unwrap();
    let entries = bytes::read_le16(raw, 8).unwrap();
    if next_free >= blocks || previous_free >= blocks || entries as usize > slots { return None; }
    Some(DataHeader { next_free, previous_free, entries })
}

pub fn parse_tree_block(raw: &[u8], blocks: u32) -> (r: Option<Vec<u32>>)
    ensures match r {
        Some(refs) => raw.len() == BLOCK_BYTES && blocks > ROOT_BLOCK
            && refs.len() == 256 && refs@ == tree_refs(raw@)
            && forall|i: int| 0 <= i < refs.len() ==> refs@[i] < blocks,
        None => true,
    },
{
    if raw.len() != BLOCK_BYTES || blocks <= ROOT_BLOCK { return None; }
    let mut refs = Vec::<u32>::new(); let mut i = 0usize;
    while i < 256 invariant i <= 256, refs.len() == i, raw.len() == BLOCK_BYTES,
        forall|j: int| 0 <= j < i ==> refs@[j] < blocks && refs@[j] == bytes::le32(raw@, j * 4),
        decreases 256 - i,
    {
        let block = bytes::read_le32(raw, i * 4).unwrap();
        if block >= blocks { return None; }
        refs.push(block); i += 1;
    }
    Some(refs)
}

fn block<'a>(file: &'a [u8], number: u32, blocks: u32) -> (r: Option<&'a [u8]>)
    ensures match r {
        Some(raw) => number < blocks && raw.len() == BLOCK_BYTES
            && (number as nat + 1) * BLOCK_BYTES <= file.len()
            && raw@ == file@.subrange(number as int * BLOCK_BYTES, (number as int + 1) * BLOCK_BYTES),
        None => number >= blocks || (number as nat + 1) * BLOCK_BYTES > file.len(),
    },
{
    if number >= blocks { return None; }
    let at = number as u64 * 1024;
    if at > file.len() as u64 || file.len() as u64 - at < 1024 { return None; }
    Some(&file[at as usize..at as usize + 1024])
}

proof fn record_slice_in_file(file: Seq<u8>, raw: Seq<u8>, block: u32, at: nat, count: nat, version: u32)
    requires (block as nat + 1) * BLOCK_BYTES <= file.len(),
        raw == file.subrange(block as int * BLOCK_BYTES, (block as int + 1) * BLOCK_BYTES),
        at + count <= BLOCK_BYTES,
    ensures raw.subrange(at as int, (at + count) as int)
        == file.subrange(block as int * BLOCK_BYTES + at, block as int * BLOCK_BYTES + at + count),
        parsed_record(raw.subrange(at as int, (at + count) as int), version)
            == parsed_record(file.subrange(block as int * BLOCK_BYTES + at,
                block as int * BLOCK_BYTES + at + count), version),
{
    assert(raw.subrange(at as int, (at + count) as int)
        =~= file.subrange(block as int * BLOCK_BYTES + at, block as int * BLOCK_BYTES + at + count));
}

/// A path lookup validates every pointer in each traversed tree block, rejects
/// cycles, and checks the complete selected data block's occupancy and IDs.
pub fn lookup(file: &[u8], kind: QuotaType, id: u32) -> (r: Result<Option<Located>, Error>)
    ensures match r {
        Ok(Some(found)) => found.record.id == id && found.block > ROOT_BLOCK
            && found.offset as nat + width(bytes::le32(file@, 4) as u32).unwrap() <= file.len()
            && found.offset as nat == found.block as nat * BLOCK_BYTES + DATA_HEADER_BYTES
                + found.slot * width(bytes::le32(file@, 4) as u32).unwrap()
            && parsed_record(file@.subrange(found.offset as int,
                found.offset as int + width(bytes::le32(file@, 4) as u32).unwrap() as int),
                bytes::le32(file@, 4) as u32) == Some(found.record),
        _ => true,
    },
{
    let header = match parse_header(file, kind) { Some(v) => v, None => { return Err(Error::Header); } };
    let info = match parse_info(file) { Some(v) => v, None => { return Err(Error::Bounds); } };
    let width = record_bytes(header.version).unwrap();
    let slots = records_per_block(header.version).unwrap();
    let mut path = Vec::<u32>::new(); path.push(ROOT_BLOCK);
    let mut current = ROOT_BLOCK; let mut depth = 0usize;
    while depth < 4
        invariant depth <= 4, path.len() == depth + 1,
            header.version <= 1, header.version == bytes::le32(file@, 4) as u32,
            info.blocks > ROOT_BLOCK,
            0 < current < info.blocks, path@[0] == ROOT_BLOCK, path@[depth as int] == current,
            width == if header.version == 0 { 48usize } else { 72usize },
            slots == if header.version == 0 { 21usize } else { 14usize },
            forall|p: int, q: int| 0 <= p < q < path.len() ==> path@[p] != path@[q],
        decreases 4 - depth,
    {
        let raw = match block(file, current, info.blocks) { Some(v) => v, None => { return Err(Error::Bounds); } };
        let refs = match parse_tree_block(raw, info.blocks) { Some(v) => v, None => { return Err(Error::Bounds); } };
        let shift = (3 - depth) * 8;
        proof { assert(((id >> shift) & 255) <= 255) by (bit_vector); }
        let index = ((id >> shift) & 255) as usize;
        let next = refs[index];
        if next == 0 { return Ok(None); }
        let mut p = 0usize;
        while p < path.len() invariant p <= path.len(),
            depth < 4, path.len() == depth + 1,
            path@[0] == ROOT_BLOCK, path@[depth as int] == current,
            next != 0, next < info.blocks,
            forall|q: int, r: int| 0 <= q < r < path.len() ==> path@[q] != path@[r],
            forall|q: int| 0 <= q < p ==> path@[q] != next,
            decreases path.len() - p,
        { if path[p] == next { return Err(Error::TreeCycle); } p += 1; }
        path.push(next); current = next; depth += 1;
    }
    let raw = match block(file, current, info.blocks) { Some(v) => v, None => { return Err(Error::Bounds); } };
    let dh = match parse_data_header(raw, header.version, info.blocks) { Some(v) => v, None => { return Err(Error::DataHeader); } };
    let mut seen = Vec::<u32>::new(); let mut found: Option<Located> = None; let mut i = 0usize;
    while i < slots
        invariant i <= slots, raw.len() == BLOCK_BYTES, current > ROOT_BLOCK,
            header.version <= 1, header.version == bytes::le32(file@, 4) as u32,
            width == if header.version == 0 { 48usize } else { 72usize },
            slots == if header.version == 0 { 21usize } else { 14usize },
            current < info.blocks, (current as nat + 1) * BLOCK_BYTES <= file.len(),
            raw@ == file@.subrange(current as int * BLOCK_BYTES, (current as int + 1) * BLOCK_BYTES),
            match found {
                Some(located) => located.record.id == id && located.slot < i && located.block == current
                    && located.offset as nat == current as nat * BLOCK_BYTES + DATA_HEADER_BYTES + located.slot * width
                    && parsed_record(raw@.subrange((DATA_HEADER_BYTES + located.slot * width) as int,
                        (DATA_HEADER_BYTES + located.slot * width + width) as int), header.version) == Some(located.record),
                None => true,
            },
        decreases slots - i,
    {
        let at = DATA_HEADER_BYTES + i * width;
        if let Some(record) = parse_record(&raw[at..at + width], header.version) {
            let mut j = 0usize;
            while j < seen.len() invariant j <= seen.len(), decreases seen.len() - j,
            { if seen[j] == record.id { return Err(Error::DuplicateId); } j += 1; }
            seen.push(record.id);
            if record.id == id {
                found = Some(Located { record, block: current, slot: i, offset: current as usize * 1024 + at });
            }
        }
        i += 1;
    }
    if seen.len() != dh.entries as usize { return Err(Error::DataHeader); }
    match found {
        Some(v) => {
            proof {
                assert(v.slot < slots);
                assert(DATA_HEADER_BYTES + v.slot * width + width <= BLOCK_BYTES);
                record_slice_in_file(file@, raw@, current,
                    (DATA_HEADER_BYTES + v.slot * width) as nat, width as nat, header.version);
                assert(crate::quota_v2::width(bytes::le32(file@, 4) as u32) == Some(width as nat));
                assert(v.offset as nat + width <= file.len());
            }
            Ok(Some(v))
        },
        None => Err(Error::MissingRecord),
    }
}

fn add_block(file: &mut Vec<u8>, budget: u32) -> (r: Option<u32>)
    ensures match r {
        Some(number) => 2 <= budget <= MAX_BUILD_BLOCKS && number < budget
            && old(file).len() == number as nat * BLOCK_BYTES
            && final(file)@ == old(file)@ + Seq::<u8>::new(BLOCK_BYTES as nat, |i: int| 0u8)
            && build_storage(final(file)@, budget),
        None => final(file)@ == old(file)@,
    },
{
    let count = file.len() / BLOCK_BYTES;
    if budget < 2 || budget > MAX_BUILD_BLOCKS || count >= budget as usize || file.len() % BLOCK_BYTES != 0 { return None; }
    let ghost before = file@;
    let mut i = 0usize;
    while i < BLOCK_BYTES invariant i <= BLOCK_BYTES,
        2 <= budget <= MAX_BUILD_BLOCKS, count < budget,
        before.len() == count * BLOCK_BYTES,
        file@ == before + Seq::<u8>::new(i as nat, |j: int| 0u8),
        decreases BLOCK_BYTES - i,
    { file.push(0); i += 1; }
    Some(count as u32)
}

proof fn pushed_blocks_set(blocks: Seq<u32>, block: u32)
    ensures blocks.push(block).to_set() == blocks.to_set().insert(block),
{
    blocks.to_set_ensures();
    blocks.push(block).to_set_ensures();
    assert(blocks.push(block).to_set() =~= blocks.to_set().insert(block)) by {
        assert forall|item: u32| #[trigger] blocks.push(block).to_set().contains(item)
            == blocks.to_set().insert(block).contains(item) by {
            vstd::seq_lib::lemma_seq_contains_after_push(blocks, block, item);
        }
    }
}

/// Build a complete canonical quota file. New data and radix blocks are
/// privately zeroed, all references are bounded, IDs are unique, and the free
/// entry list links every non-full data block. No filesystem blocks are
/// allocated or published by this byte-image builder.
pub fn build(kind: QuotaType, version: u32, block_grace: u32, inode_grace: u32,
    records: &[Record], block_budget: u32) -> (r: Result<Vec<u8>, Error>)
    ensures match r {
        Ok(raw) => build_storage(raw@, block_budget) && raw.len() >= 2 * BLOCK_BYTES
            && bytes::le32(raw@, 0) == type_magic(kind) && bytes::le32(raw@, 4) == version
            && bytes::le32(raw@, 8) == block_grace && bytes::le32(raw@, 12) == inode_grace
            && bytes::le32(raw@, 16) == 0 && bytes::le32(raw@, 20) == raw.len() / BLOCK_BYTES
            && bytes::le32(raw@, 24) == 0
            && exists|levels: Map<u32, nat>, data: Set<u32>| #[trigger] radix_layout(raw@, levels, data),
        Err(_) => true,
    },
{
    let width = match record_bytes(version) { Some(v) => v, None => { return Err(Error::Version); } };
    let slots = records_per_block(version).unwrap();
    if block_budget < 2 || block_budget > MAX_BUILD_BLOCKS || records.len() > 65536 { return Err(Error::Budget); }
    let mut raw = Vec::<u8>::new();
    if add_block(&mut raw, block_budget).is_none() || add_block(&mut raw, block_budget).is_none() { return Err(Error::Budget); }
    let ghost mut levels = Map::<u32, nat>::empty().insert(ROOT_BLOCK, 0);
    let ghost mut data_set = Set::<u32>::empty();
    proof {
        assert(raw@ =~= Seq::<u8>::new(2 * BLOCK_BYTES as nat, |i: int| 0u8));
        radix_empty(raw@);
    }
    let mut data_blocks = Vec::<u32>::new();
    let mut ids = Vec::<u32>::new();
    let mut data = 0u32; let mut used = 0usize; let mut i = 0usize;
    while i < records.len()
        invariant i <= records.len() <= 65536, used <= slots, version <= 1,
            build_storage(raw@, block_budget), raw.len() >= 2 * BLOCK_BYTES,
            radix_layout(raw@, levels, data_set), data_set == data_blocks@.to_set(),
            data == 0 || data_set.contains(data),
            width == if version == 0 { 48usize } else { 72usize },
            slots == if version == 0 { 21usize } else { 14usize },
            ids.len() == i,
            data == 0 || (ROOT_BLOCK < data && (data as nat + 1) * BLOCK_BYTES <= raw.len()),
            forall|d: int| 0 <= d < data_blocks.len()
                ==> ROOT_BLOCK < data_blocks@[d] && (data_blocks@[d] as nat + 1) * BLOCK_BYTES <= raw.len(),
        decreases records.len() - i,
    {
        let record = records[i]; let mut j = 0usize;
        while j < ids.len() invariant j <= ids.len(), decreases ids.len() - j,
        { if ids[j] == record.id { return Err(Error::DuplicateId); } j += 1; }
        ids.push(record.id);
        let encoded = match encode_record(record, version) { Some(v) => v, None => { return Err(Error::Version); } };
        if data == 0 || used == slots {
            let ghost previous_blocks = data_blocks@;
            let ghost before = raw@;
            data = match add_block(&mut raw, block_budget) { Some(v) => v, None => { return Err(Error::Budget); } };
            proof {
                radix_append(before, levels, data_set, data, None);
                data_set = data_set.insert(data);
            }
            data_blocks.push(data);
            proof {
                pushed_blocks_set(previous_blocks, data);
                assert(data_set =~= data_blocks@.to_set());
            }
            used = 0;
        }
        proof { radix_data_properties(raw@, levels, data_set, data); }
        let at = data as usize * BLOCK_BYTES + DATA_HEADER_BYTES + used * width;
        proof { assert(at as nat + width <= (data as nat + 1) * BLOCK_BYTES); }
        let mut k = 0usize;
        while k < width
            invariant k <= width, encoded.len() == width, at as nat + width <= raw.len(),
                at as nat == data as nat * BLOCK_BYTES + DATA_HEADER_BYTES + used * width,
                at as nat + width <= (data as nat + 1) * BLOCK_BYTES,
                build_storage(raw@, block_budget), ROOT_BLOCK < data,
                radix_layout(raw@, levels, data_set), data_set.contains(data),
                data_set == data_blocks@.to_set(),
                (data as nat + 1) * BLOCK_BYTES <= raw.len(),
                used < slots,
                width == if version == 0 { 48usize } else { 72usize },
                slots == if version == 0 { 21usize } else { 14usize },
            decreases width - k,
        {
            proof { radix_data_byte(raw@, levels, data_set, data, (at + k) as int, encoded@[k as int]); }
            raw[at + k] = encoded[k]; k += 1;
        }
        used += 1;
        let count = bytes::encode_le16(used as u16);
        proof { radix_data_byte(raw@, levels, data_set, data, data as int * BLOCK_BYTES + 8, count@[0]); }
        raw[data as usize * BLOCK_BYTES + 8] = count[0];
        proof { radix_data_byte(raw@, levels, data_set, data, data as int * BLOCK_BYTES + 9, count@[1]); }
        raw[data as usize * BLOCK_BYTES + 9] = count[1];
        proof {
            radix_root_properties(raw@, levels, data_set);
            radix_node_properties(raw@, levels, data_set, ROOT_BLOCK, 0);
        }
        let mut node = ROOT_BLOCK; let mut depth = 0usize;
        while depth < 4
            invariant depth <= 4, build_storage(raw@, block_budget), raw.len() >= 2 * BLOCK_BYTES,
                radix_layout(raw@, levels, data_set), data_set.contains(data),
                data_set == data_blocks@.to_set(),
                levels.dom().contains(node), depth < 4 ==> levels[node] == depth,
                node > 0, (node as nat + 1) * BLOCK_BYTES <= raw.len(),
                ROOT_BLOCK < data, (data as nat + 1) * BLOCK_BYTES <= raw.len(),
            decreases 4 - depth,
        {
            let identifier = record.id;
            let shift = (3 - depth) * 8;
            proof { assert(((identifier >> shift) & 255) <= 255) by (bit_vector); }
            let index = ((identifier >> shift) & 255) as usize;
            proof { radix_node_properties(raw@, levels, data_set, node, index as int); }
            let at = node as usize * BLOCK_BYTES + index * 4;
            let next = bytes::read_le32(raw.as_slice(), at).unwrap();
            if depth == 3 {
                if next != 0 { return Err(Error::DuplicateId); }
                proof { radix_pointer_write(raw@, levels, data_set, node, index as int, data); }
                if !put_u32(raw.as_mut_slice(), at, data) { return Err(Error::Bounds); }
            } else if next == 0 {
                let ghost before = raw@;
                let new_node = match add_block(&mut raw, block_budget) { Some(v) => v, None => { return Err(Error::Budget); } };
                proof {
                    radix_append(before, levels, data_set, new_node, Some(depth as nat + 1));
                    levels = levels.insert(new_node, depth as nat + 1);
                    radix_pointer_write(raw@, levels, data_set, node, index as int, new_node);
                }
                if !put_u32(raw.as_mut_slice(), at, new_node) { return Err(Error::Bounds); }
                node = new_node;
            } else { node = next; }
            proof {
                radix_node_properties(raw@, levels, data_set, node, 0);
                radix_data_properties(raw@, levels, data_set, data);
            }
            depth += 1;
        }
        proof {
            assert forall|d: int| 0 <= d < data_blocks.len()
                implies ROOT_BLOCK < data_blocks@[d] && (data_blocks@[d] as nat + 1) * BLOCK_BYTES <= raw.len() by {
                assert(data_set.contains(data_blocks@[d]));
                radix_data_properties(raw@, levels, data_set, data_blocks@[d]);
            }
        }
        i += 1;
    }
    let mut free_entry = 0u32; let mut previous = 0u32; let mut b = 0usize;
    while b < data_blocks.len()
        invariant b <= data_blocks.len(), build_storage(raw@, block_budget), raw.len() >= 2 * BLOCK_BYTES,
            radix_layout(raw@, levels, data_set), data_set == data_blocks@.to_set(),
            previous == 0 || data_set.contains(previous),
            slots == if version == 0 { 21usize } else { 14usize },
            previous == 0 || (ROOT_BLOCK < previous && (previous as nat + 1) * BLOCK_BYTES <= raw.len()),
            forall|d: int| 0 <= d < data_blocks.len()
                ==> ROOT_BLOCK < data_blocks@[d] && (data_blocks@[d] as nat + 1) * BLOCK_BYTES <= raw.len(),
        decreases data_blocks.len() - b,
    {
        let n = data_blocks[b]; let at = n as usize * BLOCK_BYTES;
        let entries = bytes::read_le16(raw.as_slice(), at + 8).unwrap() as usize;
        if entries < slots {
            if free_entry == 0 { free_entry = n; }
            if !put_non_node_u32(raw.as_mut_slice(), at + 4, previous, n, Ghost(levels), Ghost(data_set)) { return Err(Error::Bounds); }
            if previous != 0 && !put_non_node_u32(raw.as_mut_slice(), previous as usize * BLOCK_BYTES, n,
                previous, Ghost(levels), Ghost(data_set)) { return Err(Error::Bounds); }
            previous = n;
        }
        b += 1;
    }
    if !finish_build_header(raw.as_mut_slice(), kind, version, block_grace, inode_grace, free_entry,
        Ghost(levels), Ghost(data_set)) { return Err(Error::Bounds); }
    proof { assert(exists|l: Map<u32, nat>, d: Set<u32>| #[trigger] radix_layout(raw@, l, d)); }
    Ok(raw)
}

}
