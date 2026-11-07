// SPDX-License-Identifier: MPL-2.0

//! Retargets one live non-dot directory record without moving its name or span.
//! This framed byte codec reseals and reparses the leaf. Namespace admission and
//! source binding remain the responsibility of its caller.

use vstd::prelude::*;
use crate::{bytes, crc, directory, directory_block,
    directory_piece::{self, Piece, PieceView}, ns_dir_edit, ns_rename_block};

verus! {

pub open spec fn view(raw: Seq<u8>, inodes: u32, seed: u32, indexed: bool,
    logical: u32, blocks: u32, large: bool) -> PieceView {
    ns_rename_block::view(raw, inodes, seed, indexed, logical, blocks, large)
}

pub open spec fn name(piece: PieceView, record: int) -> Seq<u8> {
    ns_rename_block::name(piece, record)
}

pub struct Change {
    pub before: PieceView, pub after: PieceView, pub record: usize,
    pub target: u32, pub file_type: u8,
}

pub open spec fn start(c: Change) -> nat {
    (c.before.block.records[c.record as int].name_offset - 8) as nat
}

pub open spec fn frame(first: nat, i: int) -> bool {
    first <= i < first + 4 || i == first + 7 || 4092 <= i < 4096
}

pub open spec fn record_relation(c: Change, i: int) -> bool {
    let old = c.before.block.records[i];
    let next = c.after.block.records[i];
    &&& next.inode == if i == c.record { c.target } else { old.inode }
    &&& next.file_type == if i == c.record { c.file_type } else { old.file_type }
    &&& next.next == old.next && next.name_offset == old.name_offset
    &&& next.name_length == old.name_length && name(c.after, i) == name(c.before, i)
}

#[verifier::opaque]
pub open spec fn valid(c: Change) -> bool {
    let old = c.before.block.records[c.record as int];
    &&& ns_dir_edit::same_context(c.before, c.after)
    &&& c.record < c.before.block.records.len() && old.inode != 0
    &&& ns_rename_block::proper_name(name(c.before, c.record as int))
    &&& 0 < c.target <= c.before.block.inodes && (c.file_type == 1 || c.file_type == 2)
    &&& 8 <= old.name_offset <= old.next <= 4084
    &&& c.after.block.records.len() == c.before.block.records.len()
    &&& (forall|i: int| 0 <= i < c.before.block.records.len() ==> #[trigger] record_relation(c, i))
    &&& (forall|i: int| 0 <= i < 4096 && !frame(start(c), i) ==>
        (#[trigger] c.after.block.raw[i]) == c.before.block.raw[i])
}

fn check_name(value: &[u8]) -> (r: bool)
    ensures r == ns_rename_block::proper_name(value@),
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

fn check_records(before: &Piece<'_>, after: &Piece<'_>, record: usize, target: u32,
    file_type: u8) -> (r: bool)
    requires before.wf(), after.wf(),
    ensures before.wf(), after.wf(), r ==> after.view().block.records.len() == before.view().block.records.len()
        && (forall|i: int| 0 <= i < before.view().block.records.len() ==>
            #[trigger] record_relation(Change { before: before.view(), after: after.view(), record, target, file_type }, i)),
{
    let count = before.len();
    if after.len() != count { return false; }
    let ghost change = Change { before: before.view(), after: after.view(), record, target, file_type };
    let mut i = 0usize;
    while i < count
        invariant before.wf(), after.wf(),
            change == (Change { before: before.view(), after: after.view(), record, target, file_type }),
            count == before.view().block.records.len(), count == after.view().block.records.len(), i <= count,
            forall|j: int| 0 <= j < i ==> #[trigger] record_relation(change, j),
        decreases count - i,
    {
        let old = before.get(i).unwrap(); let next = after.get(i).unwrap();
        let expected_target = if i == record { target } else { old.inode };
        let expected_type = if i == record { file_type } else { old.file_type };
        if next.inode != expected_target || next.file_type != expected_type || next.next != old.next
            || next.name_offset != old.name_offset || next.name_length != old.name_length { return false; }
        let previous_name = before.name(i).unwrap(); let next_name = after.name(i).unwrap();
        if !bytes::equal(next_name, previous_name) { return false; }
        assert(record_relation(change, i as int));
        i += 1;
    }
    true
}

fn check_frame(before: &[u8], after: &[u8], first: usize) -> (r: bool)
    requires first <= 4076,
    ensures r ==> before.len() == 4096 && after.len() == 4096
        && (forall|i: int| 0 <= i < 4096 && !frame(first as nat, i) ==>
            (#[trigger] after@[i]) == before@[i]),
{
    if before.len() != 4096 || after.len() != 4096 { return false; }
    let mut i = 0usize;
    while i < 4096
        invariant before.len() == 4096, after.len() == 4096, first <= 4076, i <= 4096,
            forall|j: int| 0 <= j < i && !frame(first as nat, j) ==> (#[trigger] after@[j]) == before@[j],
        decreases 4096 - i,
    {
        if !(first <= i && i < first + 4 || i == first + 7 || 4092 <= i) && after[i] != before[i] { return false; }
        i += 1;
    }
    true
}

/// Updates only a live record's inode word and type byte, then its leaf checksum.
/// Record ordinals, spans, full names and every unrelated byte remain exact.
pub fn replace(raw: &[u8], inodes: u32, seed: u32, indexed: bool, logical: u32,
    blocks: u32, large: bool, record: usize, target: u32, file_type: u8) -> (r: Option<Vec<u8>>)
    ensures match r { Some(after) => valid(Change {
        before: view(raw@, inodes, seed, indexed, logical, blocks, large),
        after: view(after@, inodes, seed, indexed, logical, blocks, large), record, target, file_type }), None => true },
{
    hide(crc::fold);
    if raw.len() != 4096 || indexed && logical == 0 || target == 0 || target > inodes
        || file_type != 1 && file_type != 2 { return None; }
    if !directory::valid_tail(raw, seed) { return None; }
    let before = match directory_piece::parse(raw, inodes, seed, indexed, logical, blocks, large) {
        Some(before) => before, None => { return None; }
    };
    let entry = match before.get(record) { Some(entry) => entry, None => { return None; } };
    let old_name = before.name(record).unwrap();
    if entry.inode == 0 || !check_name(old_name) { return None; }
    let first = entry.name_offset; let limit = entry.next;
    if first < 8 || first > limit || limit > 4084 { return None; }
    let mut after = Vec::new(); let mut i = 0usize;
    while i < 4096
        invariant raw.len() == 4096, i <= 4096, after@ == raw@.take(i as int),
        decreases 4096 - i,
    { after.push(raw[i]); assert(after@ =~= raw@.take(i as int + 1)); i += 1; }
    bytes::write_le32(after.as_mut_slice(), first - 8, target);
    after.set(first - 1, file_type);
    let checksum = crc::crc32c(seed, &after[..4084]);
    bytes::write_le32(after.as_mut_slice(), 4092, checksum);
    if !directory::valid_tail(&after, seed) { return None; }
    let parsed = match directory_piece::parse(&after, inodes, seed, indexed, logical, blocks, large) {
        Some(parsed) => parsed, None => { return None; }
    };
    if !check_records(&before, &parsed, record, target, file_type) { return None; }
    if !check_frame(raw, &after, first - 8) { return None; }
    let ghost change = Change { before: before.view(), after: parsed.view(), record, target, file_type };
    assert(start(change) == first - 8);
    assert(valid(change)) by { reveal(valid); }
    Some(after)
}

pub proof fn replacement_sets_exact_target_type_and_preserves_leaf_checksums(c: Change)
    requires valid(c),
    ensures c.after.block.records[c.record as int].inode == c.target,
        c.after.block.records[c.record as int].file_type == c.file_type,
        c.after.block.records[c.record as int].inode != 0,
        directory_block::tail(c.before.block.raw, c.before.block.seed),
        directory_block::tail(c.after.block.raw, c.after.block.seed),
{ reveal(valid); assert(record_relation(c, c.record as int)); }

pub proof fn replacement_preserves_record_ordinals_full_names_and_spans(c: Change, i: int)
    requires valid(c), 0 <= i < c.before.block.records.len(),
    ensures c.after.block.records.len() == c.before.block.records.len(),
        c.after.block.records[i].name_offset == c.before.block.records[i].name_offset,
        c.after.block.records[i].next == c.before.block.records[i].next,
        c.after.block.records[i].name_length == c.before.block.records[i].name_length,
        name(c.after, i) == name(c.before, i),
{ reveal(valid); assert(record_relation(c, i)); }

pub proof fn replacement_preserves_every_other_record(c: Change, i: int)
    requires valid(c), 0 <= i < c.before.block.records.len(), i != c.record,
    ensures c.after.block.records[i] == c.before.block.records[i],
        name(c.after, i) == name(c.before, i),
{ reveal(valid); assert(record_relation(c, i)); }

pub proof fn replacement_frames_every_other_directory_byte(c: Change, i: int)
    requires valid(c), 0 <= i < 4096, !frame(start(c), i),
    ensures c.after.block.raw[i] == c.before.block.raw[i],
{ reveal(valid); }

}
