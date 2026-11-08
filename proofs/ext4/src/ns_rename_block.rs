// SPDX-License-Identifier: MPL-2.0

//! Rename one live non-dot name in an existing directory-leaf record span.
//! This is a framed byte codec, not namespace or device authority. Source-bound
//! absence, complete HTree routing and final namespace admission are separate.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, crc, directory, directory_block::{self, BlockView},
    directory_piece::{self, Piece, PieceView}};

verus! {

pub open spec fn view(raw: Seq<u8>, inodes: u32, seed: u32, indexed: bool,
    logical: u32, blocks: u32, large: bool) -> PieceView {
    PieceView { block: BlockView { raw, records: directory_piece::canonical_records(raw, inodes, indexed, logical),
        inodes, seed }, indexed, logical, blocks, large }
}

pub open spec fn name(piece: PieceView, record: int) -> Seq<u8> {
    let entry = piece.block.records[record];
    piece.block.raw.subrange(entry.name_offset as int,
        entry.name_offset as int + entry.name_length as int)
}

pub open spec fn proper_name(value: Seq<u8>) -> bool {
    &&& 0 < value.len() <= 255
    &&& !(value.len() == 1 && value[0] == 46)
    &&& !(value.len() == 2 && value[0] == 46 && value[1] == 46)
    &&& (forall|i: int| 0 <= i < value.len() ==> (#[trigger] value[i]) != 0 && value[i] != 47)
}

pub struct Change { pub before: PieceView, pub after: PieceView, pub record: usize, pub new_name: Seq<u8> }
pub open spec fn start(c: Change) -> nat { c.before.block.records[c.record as int].name_offset as nat }
pub open spec fn end(c: Change) -> nat { c.before.block.records[c.record as int].next as nat }
pub open spec fn allowed(first: nat, limit: nat, i: int) -> bool {
    i == first as int - 2 || first <= i < limit || 4092 <= i < 4096
}
pub open spec fn record_relation(c: Change, i: int) -> bool {
    let old = c.before.block.records[i]; let new = c.after.block.records[i];
    &&& new.inode == old.inode && new.next == old.next && new.name_offset == old.name_offset
    &&& new.file_type == old.file_type
    &&& new.name_length as nat == if i == c.record { c.new_name.len() } else { old.name_length as nat }
    &&& name(c.after, i) == if i == c.record { c.new_name } else { name(c.before, i) }
}

#[verifier::opaque]
pub open spec fn valid(c: Change) -> bool {
    &&& directory_piece::valid(c.before) && directory_piece::valid(c.after)
    &&& c.before.block.inodes == c.after.block.inodes && c.before.block.seed == c.after.block.seed
    &&& c.before.indexed == c.after.indexed && c.before.logical == c.after.logical
    &&& c.before.blocks == c.after.blocks && c.before.large == c.after.large
    &&& (!c.before.indexed || c.before.logical != 0)
    &&& c.before.block.raw.len() == 4096 && c.after.block.raw.len() == 4096
    &&& directory_block::tail(c.before.block.raw, c.before.block.seed)
    &&& directory_block::tail(c.after.block.raw, c.after.block.seed)
    &&& c.record < c.before.block.records.len() && c.before.block.records[c.record as int].inode != 0
    &&& proper_name(name(c.before, c.record as int)) && proper_name(c.new_name)
    &&& 8 <= start(c) <= end(c) <= 4084 && c.new_name.len() <= end(c) - start(c)
    &&& c.after.block.records.len() == c.before.block.records.len()
    &&& (forall|i: int| 0 <= i < c.before.block.records.len() ==> #[trigger] record_relation(c, i))
    &&& (forall|i: int| 0 <= i < 4096 && !allowed(start(c), end(c), i) ==>
        (#[trigger] c.after.block.raw[i]) == c.before.block.raw[i])
    &&& (forall|i: int| start(c) + c.new_name.len() <= i < end(c) ==>
        (#[trigger] c.after.block.raw[i]) == 0)
}

fn check_name(value: &[u8]) -> (r: bool)
    ensures r == proper_name(value@),
{
    if value.len() == 0 || value.len() > 255 { return false; }
    if value.len() == 1 && value[0] == 46 || value.len() == 2 && value[0] == 46 && value[1] == 46 { return false; }
    let mut i = 0usize;
    while i < value.len()
        invariant 0 < value.len() <= 255, i <= value.len(),
            !(value.len() == 1 && value@[0] == 46),
            !(value.len() == 2 && value@[0] == 46 && value@[1] == 46),
            forall|j: int| 0 <= j < i ==> (#[trigger] value@[j]) != 0 && value@[j] != 47,
        decreases value.len() - i,
    {
        if value[i] == 0 || value[i] == 47 { return false; }
        i += 1;
    }
    true
}

fn check_records(before: &Piece<'_>, after: &Piece<'_>, record: usize, new_name: &[u8]) -> (r: bool)
    requires before.wf(), after.wf(), new_name.len() <= 255,
    ensures before.wf(), after.wf(), r ==> after.view().block.records.len() == before.view().block.records.len()
        && (forall|i: int| 0 <= i < before.view().block.records.len() ==>
            #[trigger] record_relation(Change { before: before.view(), after: after.view(), record, new_name: new_name@ }, i)),
{
    let count = before.len(); if after.len() != count { return false; }
    let ghost change = Change { before: before.view(), after: after.view(), record, new_name: new_name@ };
    let mut i = 0usize;
    while i < count
        invariant before.wf(), after.wf(), new_name.len() <= 255,
            change == (Change { before: before.view(), after: after.view(), record, new_name: new_name@ }),
            count == before.view().block.records.len(), count == after.view().block.records.len(), i <= count,
            forall|j: int| 0 <= j < i ==> #[trigger] record_relation(change, j),
        decreases count - i,
    {
        let old = before.get(i).unwrap(); let next = after.get(i).unwrap();
        if next.inode != old.inode || next.next != old.next || next.name_offset != old.name_offset
            || next.file_type != old.file_type { return false; }
        let expected = if i == record { new_name.len() as u8 } else { old.name_length };
        if next.name_length != expected { return false; }
        let previous_name = before.name(i).unwrap(); let next_name = after.name(i).unwrap();
        if i == record {
            if !bytes::equal(next_name, new_name) { return false; }
        } else if !bytes::equal(next_name, previous_name) { return false; }
        assert(record_relation(change, i as int));
        i += 1;
    }
    true
}

fn check_frame(before: &[u8], after: &[u8], first: usize, limit: usize, length: usize) -> (r: bool)
    requires 8 <= first <= limit <= 4084, length <= limit - first,
    ensures r ==> before.len() == 4096 && after.len() == 4096
        && (forall|i: int| 0 <= i < 4096 && !allowed(first as nat, limit as nat, i) ==>
            (#[trigger] after@[i]) == before@[i])
        && (forall|i: int| first as nat + length <= i < limit ==> (#[trigger] after@[i]) == 0),
{
    if before.len() != 4096 || after.len() != 4096 { return false; }
    let mut i = 0usize;
    while i < 4096
        invariant before.len() == 4096, after.len() == 4096,
            8 <= first <= limit <= 4084, length <= limit - first, i <= 4096,
            forall|j: int| 0 <= j < i && !allowed(first as nat, limit as nat, j) ==>
                (#[trigger] after@[j]) == before@[j],
            forall|j: int| 0 <= j < i && first as nat + length <= j < limit ==> (#[trigger] after@[j]) == 0,
        decreases 4096 - i,
    {
        let mutable = i == first - 2 || first <= i && i < limit || 4092 <= i;
        if !mutable && after[i] != before[i] { return false; }
        if first + length <= i && i < limit && after[i] != 0 { return false; }
        i += 1;
    }
    true
}

pub fn encode(raw: &[u8], inodes: u32, seed: u32, indexed: bool, logical: u32, blocks: u32,
    large: bool, record: usize, new_name: &[u8]) -> (r: Option<Vec<u8>>)
    ensures match r { Some(after) => valid(Change { before: view(raw@, inodes, seed, indexed, logical, blocks, large),
        after: view(after@, inodes, seed, indexed, logical, blocks, large), record, new_name: new_name@ }), None => true },
{
    hide(crate::crc::fold);
    if raw.len() != 4096 || indexed && logical == 0 || !check_name(new_name) { return None; }
    if !directory::valid_tail(raw, seed) { return None; }
    let before = match directory_piece::parse(raw, inodes, seed, indexed, logical, blocks, large) {
        Some(before) => before, None => { return None; }
    };
    let entry = match before.get(record) { Some(entry) => entry, None => { return None; } };
    if entry.inode == 0 { return None; }
    let old_name = before.name(record).unwrap(); if !check_name(old_name) { return None; }
    let first = entry.name_offset; let limit = entry.next;
    if first < 8 || first > limit || limit > 4084 || new_name.len() > limit - first { return None; }
    let mut after = Vec::new(); let mut i = 0usize;
    while i < 4096
        invariant raw.len() == 4096, i <= 4096, after@ == raw@.take(i as int),
        decreases 4096 - i,
    { after.push(raw[i]); assert(after@ =~= raw@.take(i as int + 1)); i += 1; }
    let mut cursor = first;
    while cursor < limit
        invariant after.len() == 4096, 8 <= first <= cursor <= limit <= 4084,
        decreases limit - cursor,
    { after.set(cursor, 0); cursor += 1; }
    after.set(first - 2, new_name.len() as u8);
    let copied = bytes::write_bytes(after.as_mut_slice(), first, new_name); if !copied { return None; }
    let checksum = crc::crc32c(seed, &after[..4084]); bytes::write_le32(after.as_mut_slice(), 4092, checksum);
    if !directory::valid_tail(&after, seed) { return None; }
    let parsed = match directory_piece::parse(&after, inodes, seed, indexed, logical, blocks, large) {
        Some(parsed) => parsed, None => { return None; }
    };
    if !check_records(&before, &parsed, record, new_name) { return None; }
    if !check_frame(raw, &after, first, limit, new_name.len()) { return None; }
    let ghost change = Change { before: before.view(), after: parsed.view(), record, new_name: new_name@ };
    assert(start(change) == first && end(change) == limit);
    assert(valid(change)) by { reveal(valid); }
    Some(after)
}

pub proof fn rename_preserves_record_targets_types_and_locations(c: Change, i: int)
    requires valid(c), 0 <= i < c.before.block.records.len(),
    ensures c.after.block.records[i].inode == c.before.block.records[i].inode,
        c.after.block.records[i].file_type == c.before.block.records[i].file_type,
        c.after.block.records[i].name_offset == c.before.block.records[i].name_offset,
        c.after.block.records[i].next == c.before.block.records[i].next,
{ reveal(valid); assert(record_relation(c, i)); }

pub proof fn rename_preserves_every_other_record_and_full_name(c: Change, i: int)
    requires valid(c), 0 <= i < c.before.block.records.len(), i != c.record,
    ensures c.after.block.records[i] == c.before.block.records[i], name(c.after, i) == name(c.before, i),
{ reveal(valid); assert(record_relation(c, i)); }

pub proof fn rename_frames_all_unrelated_directory_bytes(c: Change, i: int)
    requires valid(c), 0 <= i < 4096, !allowed(start(c), end(c), i),
    ensures c.after.block.raw[i] == c.before.block.raw[i],
{ reveal(valid); }

pub proof fn rename_replaces_one_live_non_dot_name_and_preserves_leaf_checksums(c: Change)
    requires valid(c),
    ensures c.after.block.records[c.record as int].inode != 0,
        name(c.after, c.record as int) == c.new_name, proper_name(c.new_name),
        directory_block::tail(c.before.block.raw, c.before.block.seed),
        directory_block::tail(c.after.block.raw, c.after.block.seed),
        forall|i: int| start(c) + c.new_name.len() <= i < end(c) ==> (#[trigger] c.after.block.raw[i]) == 0,
{ reveal(valid); assert(record_relation(c, c.record as int)); }

}
