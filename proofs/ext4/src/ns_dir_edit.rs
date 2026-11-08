// SPDX-License-Identifier: MPL-2.0

//! Framed, total directory-leaf insertion, removal and dotdot codecs.
//! These codecs preserve every unrelated live binding and byte. Source-bound
//! lookup, absence, complete HTree routing and namespace authority are separate.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, crc, directory, directory_piece::{self, Piece, PieceView},
    directory_block, ns_rename_block};

verus! {

pub open spec fn view(raw: Seq<u8>, inodes: u32, seed: u32, indexed: bool,
    logical: u32, blocks: u32, large: bool) -> PieceView {
    ns_rename_block::view(raw, inodes, seed, indexed, logical, blocks, large)
}
pub open spec fn name(v: PieceView, i: int) -> Seq<u8> { ns_rename_block::name(v, i) }
pub open spec fn proper_name(value: Seq<u8>) -> bool { ns_rename_block::proper_name(value) }

pub open spec fn same_context(a: PieceView, b: PieceView) -> bool {
    &&& directory_piece::valid(a) && directory_piece::valid(b)
    &&& a.block.inodes == b.block.inodes && a.block.seed == b.block.seed
    &&& a.indexed == b.indexed && a.logical == b.logical
    &&& a.blocks == b.blocks && a.large == b.large
    &&& (!a.indexed || a.logical != 0)
    &&& a.block.raw.len() == 4096 && b.block.raw.len() == 4096
    &&& directory_block::tail(a.block.raw, a.block.seed)
    &&& directory_block::tail(b.block.raw, b.block.seed)
}

/// Binding identity follows the physical record position, never its ordinal.
/// A split may shrink the old record's rec_len without changing its binding.
pub open spec fn same_binding(a: PieceView, i: int, b: PieceView, j: int) -> bool {
    &&& a.block.records[i].name_offset == b.block.records[j].name_offset
    &&& a.block.records[i].inode == b.block.records[j].inode
    &&& a.block.records[i].file_type == b.block.records[j].file_type
    &&& name(a, i) == name(b, j)
}
pub open spec fn retained(a: PieceView, b: PieceView, removed: int, added: int) -> bool {
    &&& (forall|i: int| 0 <= i < a.block.records.len() && i != removed
        && a.block.records[i].inode != 0 ==> exists|j: int| 0 <= j < b.block.records.len()
            && j != added && b.block.records[j].inode != 0 && #[trigger] same_binding(a, i, b, j))
    &&& (forall|j: int| 0 <= j < b.block.records.len() && j != added
        && b.block.records[j].inode != 0 ==> exists|i: int| 0 <= i < a.block.records.len()
            && i != removed && a.block.records[i].inode != 0 && #[trigger] same_binding(b, j, a, i))
}
pub open spec fn inode_frame(first: nat, i: int) -> bool {
    first <= i < first + 4 || 4092 <= i < 4096
}
pub open spec fn insert_frame(c: InsertChange, i: int) -> bool {
    let old = c.before.block.records[c.record as int];
    let added = c.after.block.records[c.added as int];
    if old.inode == 0 {
        old.name_offset as int - 8 <= i < old.next || 4092 <= i < 4096
    } else {
        i == old.name_offset as int - 4 || i == old.name_offset as int - 3
            || added.name_offset as int - 8 <= i < old.next || 4092 <= i < 4096
    }
}

pub struct InsertChange {
    pub before: PieceView, pub after: PieceView, pub record: usize, pub added: usize,
    pub target: u32, pub file_type: u8, pub new_name: Seq<u8>,
}
#[verifier::opaque]
pub open spec fn insert_valid(c: InsertChange) -> bool {
    let old = c.before.block.records[c.record as int];
    let added = c.after.block.records[c.added as int];
    &&& same_context(c.before, c.after)
    &&& c.record < c.before.block.records.len() && c.added < c.after.block.records.len()
    &&& 0 < c.target <= c.before.block.inodes && (c.file_type == 1 || c.file_type == 2)
    &&& proper_name(c.new_name)
    &&& added.inode == c.target && added.file_type == c.file_type && name(c.after, c.added as int) == c.new_name
    &&& 8 <= old.name_offset <= old.next <= 4084
    &&& 8 <= added.name_offset <= added.next <= 4084
    &&& added.next == old.next
    &&& if old.inode == 0 { added.name_offset == old.name_offset }
        else { old.name_offset as nat + old.name_length as nat <= added.name_offset as nat - 8 }
    &&& retained(c.before, c.after, c.before.block.records.len() as int, c.added as int)
    &&& (forall|i: int| 0 <= i < c.before.block.records.len() && c.before.block.records[i].inode != 0 ==>
        c.before.block.records[i].name_offset != added.name_offset)
    &&& (forall|i: int| 0 <= i < 4096 && !insert_frame(c, i) ==>
        (#[trigger] c.after.block.raw[i]) == c.before.block.raw[i])
    &&& (forall|i: int| added.name_offset as nat + c.new_name.len() <= i < added.next ==>
        (#[trigger] c.after.block.raw[i]) == 0)
}

#[verifier::opaque]
pub open spec fn inserted(before: PieceView, after: PieceView, target: u32, file_type: u8, new_name: Seq<u8>) -> bool {
    exists|record: usize, added: usize| insert_valid(InsertChange { before, after, record, added, target, file_type, new_name })
}

pub struct RemoveChange { pub before: PieceView, pub after: PieceView, pub record: usize }
#[verifier::opaque]
pub open spec fn remove_valid(c: RemoveChange) -> bool {
    let old = c.before.block.records[c.record as int];
    &&& same_context(c.before, c.after)
    &&& c.record < c.before.block.records.len() && c.record < c.after.block.records.len()
    &&& old.inode != 0 && proper_name(name(c.before, c.record as int))
    &&& 8 <= old.name_offset <= old.next <= 4084
    &&& c.after.block.records.len() == c.before.block.records.len()
    &&& c.after.block.records[c.record as int] == (directory::Entry { inode: 0,
        next: old.next, name_offset: old.name_offset, name_length: old.name_length, file_type: old.file_type })
    &&& retained(c.before, c.after, c.record as int, c.after.block.records.len() as int)
    &&& (forall|i: int| 0 <= i < c.after.block.records.len() && c.after.block.records[i].inode != 0 ==>
        c.after.block.records[i].name_offset != old.name_offset)
    &&& (forall|i: int| 0 <= i < 4096 && !inode_frame((old.name_offset - 8) as nat, i) ==>
        (#[trigger] c.after.block.raw[i]) == c.before.block.raw[i])
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

fn find_binding(a: &Piece<'_>, i: usize, b: &Piece<'_>, skip: usize) -> (r: Option<usize>)
    requires a.wf(), b.wf(), i < a.view().block.records.len(),
    ensures a.wf(), b.wf(), match r { Some(j) => j < b.view().block.records.len() && j != skip
        && b.view().block.records[j as int].inode != 0 && same_binding(a.view(), i as int, b.view(), j as int),
        None => true },
{
    let old = a.get(i).unwrap(); let old_name = a.name(i).unwrap();
    let count = b.len(); let mut j = 0usize;
    while j < count
        invariant a.wf(), b.wf(), i < a.view().block.records.len(),
            *old == a.view().block.records[i as int], old_name@ == name(a.view(), i as int),
            count == b.view().block.records.len(), j <= count,
        decreases count - j,
    {
        let next = b.get(j).unwrap();
        if j != skip && next.inode != 0 && next.inode == old.inode && next.file_type == old.file_type
            && next.name_offset == old.name_offset {
            let next_name = b.name(j).unwrap();
            if bytes::equal(old_name, next_name) { return Some(j); }
        }
        j += 1;
    }
    None
}

fn check_retained(a: &Piece<'_>, b: &Piece<'_>, removed: usize, added: usize) -> (r: bool)
    requires a.wf(), b.wf(),
    ensures a.wf(), b.wf(), r ==> retained(a.view(), b.view(), removed as int, added as int),
{
    let old_count = a.len(); let new_count = b.len();
    let mut i = 0usize;
    while i < old_count
        invariant a.wf(), b.wf(), old_count == a.view().block.records.len(),
            new_count == b.view().block.records.len(), i <= old_count,
            forall|k: int| 0 <= k < i && k != removed && a.view().block.records[k].inode != 0 ==>
                exists|j: int| 0 <= j < new_count && j != added && b.view().block.records[j].inode != 0
                    && #[trigger] same_binding(a.view(), k, b.view(), j),
        decreases old_count - i,
    {
        let old = a.get(i).unwrap();
        if i != removed && old.inode != 0 {
            let j = match find_binding(a, i, b, added) { Some(j) => j, None => { return false; } };
            assert(exists|j: int| 0 <= j < new_count && j != added && b.view().block.records[j].inode != 0
                && #[trigger] same_binding(a.view(), i as int, b.view(), j));
        }
        i += 1;
    }
    let mut j = 0usize;
    while j < new_count
        invariant a.wf(), b.wf(), old_count == a.view().block.records.len(),
            new_count == b.view().block.records.len(), j <= new_count,
            forall|k: int| 0 <= k < old_count && k != removed && a.view().block.records[k].inode != 0 ==>
                exists|q: int| 0 <= q < new_count && q != added && b.view().block.records[q].inode != 0
                    && #[trigger] same_binding(a.view(), k, b.view(), q),
            forall|k: int| 0 <= k < j && k != added && b.view().block.records[k].inode != 0 ==>
                exists|q: int| 0 <= q < old_count && q != removed && a.view().block.records[q].inode != 0
                    && #[trigger] same_binding(b.view(), k, a.view(), q),
        decreases new_count - j,
    {
        let next = b.get(j).unwrap();
        if j != added && next.inode != 0 {
            let i = match find_binding(b, j, a, removed) { Some(i) => i, None => { return false; } };
            assert(exists|i: int| 0 <= i < old_count && i != removed && a.view().block.records[i].inode != 0
                && #[trigger] same_binding(b.view(), j as int, a.view(), i));
        }
        j += 1;
    }
    true
}

fn copy_block(raw: &[u8]) -> (r: Vec<u8>)
    requires raw.len() == 4096,
    ensures r@ == raw@,
{
    let mut r = Vec::new(); let mut i = 0usize;
    while i < 4096
        invariant raw.len() == 4096, i <= 4096, r@ == raw@.take(i as int),
        decreases 4096 - i,
    { r.push(raw[i]); assert(r@ =~= raw@.take(i as int + 1)); i += 1; }
    r
}

fn check_insert_frame(a: &[u8], b: &[u8], first: usize, limit: usize, offset: usize,
    length: usize, reuse: bool) -> (r: bool)
    requires 8 <= first <= limit <= 4084, 8 <= offset <= limit, length <= limit - offset,
    ensures r ==> a.len() == 4096 && b.len() == 4096
        && (forall|i: int| 0 <= i < 4096
            && !(if reuse { first as int - 8 <= i < limit || 4092 <= i < 4096 }
                else { i == first as int - 4 || i == first as int - 3
                    || offset as int - 8 <= i < limit || 4092 <= i < 4096 }) ==>
            (#[trigger] b@[i]) == a@[i])
        && (forall|i: int| offset as nat + length <= i < limit ==> (#[trigger] b@[i]) == 0),
{
    if a.len() != 4096 || b.len() != 4096 { return false; }
    let mut i = 0usize;
    while i < 4096
        invariant a.len() == 4096, b.len() == 4096, 8 <= first <= limit <= 4084,
            8 <= offset <= limit, length <= limit - offset, i <= 4096,
            forall|j: int| 0 <= j < i
                && !(if reuse { first as int - 8 <= j < limit || 4092 <= j < 4096 }
                    else { j == first as int - 4 || j == first as int - 3
                        || offset as int - 8 <= j < limit || 4092 <= j < 4096 }) ==>
                (#[trigger] b@[j]) == a@[j],
            forall|j: int| 0 <= j < i && offset as nat + length <= j < limit ==> (#[trigger] b@[j]) == 0,
        decreases 4096 - i,
    {
        let mutable = if reuse { first - 8 <= i && i < limit || 4092 <= i }
            else { i == first - 4 || i == first - 3 || offset - 8 <= i && i < limit || 4092 <= i };
        if !mutable && b[i] != a[i] { return false; }
        if offset + length <= i && i < limit && b[i] != 0 { return false; }
        i += 1;
    }
    true
}

fn check_inode_frame(a: &[u8], b: &[u8], first: usize) -> (r: bool)
    requires first <= 4080,
    ensures r ==> a.len() == 4096 && b.len() == 4096
        && (forall|i: int| 0 <= i < 4096 && !inode_frame(first as nat, i) ==> (#[trigger] b@[i]) == a@[i]),
{
    if a.len() != 4096 || b.len() != 4096 { return false; }
    let mut i = 0usize;
    while i < 4096
        invariant a.len() == 4096, b.len() == 4096, first <= 4080, i <= 4096,
            forall|j: int| 0 <= j < i && !inode_frame(first as nat, j) ==> (#[trigger] b@[j]) == a@[j],
        decreases 4096 - i,
    {
        if !(first <= i && i < first + 4 || 4092 <= i) && b[i] != a[i] { return false; }
        i += 1;
    }
    true
}

fn no_live_offset(before: &Piece<'_>, offset: usize) -> (r: bool)
    requires before.wf(),
    ensures before.wf(), r ==> (forall|i: int| 0 <= i < before.view().block.records.len()
        && before.view().block.records[i].inode != 0 ==> before.view().block.records[i].name_offset != offset),
{
    let count = before.len(); let mut i = 0usize;
    while i < count
        invariant before.wf(), count == before.view().block.records.len(), i <= count,
            forall|j: int| 0 <= j < i && before.view().block.records[j].inode != 0 ==>
                before.view().block.records[j].name_offset != offset,
        decreases count - i,
    {
        let entry = before.get(i).unwrap();
        if entry.inode != 0 && entry.name_offset == offset { return false; }
        i += 1;
    }
    true
}


fn find_slot(before: &Piece<'_>, needed: usize) -> (r: Option<usize>)
    requires before.wf(), needed <= 264,
    ensures before.wf(), match r { Some(i) => i < before.view().block.records.len(), None => true },
{
    let count = before.len(); let mut i = 0usize;
    while i < count
        invariant before.wf(), count == before.view().block.records.len(), i <= count, needed <= 264,
        decreases count - i,
    {
        let entry = before.get(i).unwrap();
        let first = entry.name_offset; let limit = entry.next;
        if first < 8 || first > limit || limit > 4084 { return None; }
        let used = ((8 + entry.name_length as usize + 3) / 4) * 4;
        let start = first - 8;
        if entry.inode == 0 {
            if needed <= limit - start { return Some(i); }
        } else if used <= limit - start && needed <= limit - start - used { return Some(i); }
        i += 1;
    }
    None
}

/// Reuse one unused record or split one live record's aligned slack.
/// The complete directory validator must still check absence and HTree ranges.
#[verifier::rlimit(30)]
pub fn insert(raw: &[u8], inodes: u32, seed: u32, indexed: bool, logical: u32, blocks: u32,
    large: bool, target: u32, file_type: u8, new_name: &[u8]) -> (r: Option<Vec<u8>>)
    ensures match r { Some(after) => inserted(view(raw@, inodes, seed, indexed, logical, blocks, large),
        view(after@, inodes, seed, indexed, logical, blocks, large), target, file_type, new_name@), None => true },
{
    hide(crc::fold);
    if raw.len() != 4096 || indexed && logical == 0 || target == 0 || target > inodes
        || file_type != 1 && file_type != 2 || !check_name(new_name) { return None; }
    if !directory::valid_tail(raw, seed) { return None; }
    let before = match directory_piece::parse(raw, inodes, seed, indexed, logical, blocks, large) {
        Some(before) => before, None => { return None; }
    };
    let count = before.len(); let needed = ((8 + new_name.len() + 3) / 4) * 4;
    let record = match find_slot(&before, needed) { Some(record) => record, None => { return None; } };
    let entry = before.get(record).unwrap();
    let first = entry.name_offset; let limit = entry.next;
    if first < 8 || first > limit || limit > 4084 { return None; }
    let used = ((8 + entry.name_length as usize + 3) / 4) * 4;
    let start = first - 8;
    let reuse = entry.inode == 0;
    let insertion = if reuse { start } else {
        if used > limit - start { return None; }
        start + used
    };
    if insertion > limit || needed > limit - insertion { return None; }
    let offset = insertion + 8;
    if offset > limit || new_name.len() > limit - offset { return None; }
    if !no_live_offset(&before, offset) { return None; }
    let mut after = copy_block(raw);
    let mut cursor = insertion;
    while cursor < limit
        invariant after.len() == 4096, insertion <= cursor <= limit <= 4084,
        decreases limit - cursor,
    { after.set(cursor, 0); cursor += 1; }
    if !reuse {
        let encoded = bytes::encode_le16(used as u16);
        bytes::write_bytes(after.as_mut_slice(), first - 4, &encoded);
    }
    bytes::write_le32(after.as_mut_slice(), insertion, target);
    let encoded = bytes::encode_le16((limit - insertion) as u16);
    bytes::write_bytes(after.as_mut_slice(), insertion + 4, &encoded);
    after.set(insertion + 6, new_name.len() as u8);
    after.set(insertion + 7, file_type);
    if !bytes::write_bytes(after.as_mut_slice(), offset, new_name) { return None; }
    let checksum = crc::crc32c(seed, &after[..4084]);
    bytes::write_le32(after.as_mut_slice(), 4092, checksum);
    if !directory::valid_tail(&after, seed) { return None; }
    let parsed = match directory_piece::parse(&after, inodes, seed, indexed, logical, blocks, large) {
        Some(parsed) => parsed, None => { return None; }
    };
    let added = if reuse { record } else { record + 1 };
    let added_entry = match parsed.get(added) { Some(entry) => entry, None => { return None; } };
    let added_name = parsed.name(added).unwrap();
    if added_entry.inode != target || added_entry.file_type != file_type
        || added_entry.name_offset != offset || added_entry.next != limit
        || !bytes::equal(added_name, new_name) { return None; }
    if !reuse && first + entry.name_length as usize > offset - 8 { return None; }
    if !check_retained(&before, &parsed, count, added) { return None; }
    if !check_insert_frame(raw, &after, first, limit, offset, new_name.len(), reuse) { return None; }
    let ghost change = InsertChange { before: before.view(), after: parsed.view(),
        record, added, target, file_type, new_name: new_name@ };
    assert(insert_valid(change)) by { reveal(insert_valid); }
    assert(inserted(view(raw@, inodes, seed, indexed, logical, blocks, large),
        view(after@, inodes, seed, indexed, logical, blocks, large), target, file_type, new_name@)) by {
        reveal(inserted);
    }
    Some(after)
}

/// Delete exactly one non-dot live binding, preserving its full record span.
pub fn remove(raw: &[u8], inodes: u32, seed: u32, indexed: bool, logical: u32, blocks: u32,
    large: bool, record: usize) -> (r: Option<Vec<u8>>)
    ensures match r { Some(after) => remove_valid(RemoveChange {
        before: view(raw@, inodes, seed, indexed, logical, blocks, large),
        after: view(after@, inodes, seed, indexed, logical, blocks, large), record }), None => true },
{
    hide(crc::fold);
    if raw.len() != 4096 || indexed && logical == 0 { return None; }
    if !directory::valid_tail(raw, seed) { return None; }
    let before = match directory_piece::parse(raw, inodes, seed, indexed, logical, blocks, large) {
        Some(before) => before, None => { return None; }
    };
    let entry = match before.get(record) { Some(entry) => entry, None => { return None; } };
    let old_name = before.name(record).unwrap();
    if entry.inode == 0 || !check_name(old_name) { return None; }
    let first = entry.name_offset; let limit = entry.next;
    if first < 8 || first > limit || limit > 4084 { return None; }
    let mut after = copy_block(raw);
    bytes::write_le32(after.as_mut_slice(), first - 8, 0);
    let checksum = crc::crc32c(seed, &after[..4084]);
    bytes::write_le32(after.as_mut_slice(), 4092, checksum);
    if !directory::valid_tail(&after, seed) { return None; }
    let parsed = match directory_piece::parse(&after, inodes, seed, indexed, logical, blocks, large) {
        Some(parsed) => parsed, None => { return None; }
    };
    if parsed.len() != before.len() { return None; }
    let next = match parsed.get(record) { Some(entry) => entry, None => { return None; } };
    if next.inode != 0 || next.next != limit || next.name_offset != first
        || next.name_length != entry.name_length || next.file_type != entry.file_type { return None; }
    let new_count = parsed.len();
    if !check_retained(&before, &parsed, record, new_count) { return None; }
    if !no_live_offset(&parsed, first) { return None; }
    if !check_inode_frame(raw, &after, first - 8) { return None; }
    let ghost change = RemoveChange { before: before.view(), after: parsed.view(), record };
    assert(remove_valid(change)) by { reveal(remove_valid); }
    Some(after)
}

pub proof fn insertion_adds_exactly_one_live_binding_without_ordinal_assumptions(c: InsertChange)
    requires insert_valid(c),
    ensures retained(c.before, c.after, c.before.block.records.len() as int, c.added as int),
        c.after.block.records[c.added as int].inode == c.target,
        c.after.block.records[c.added as int].file_type == c.file_type,
        name(c.after, c.added as int) == c.new_name,
        proper_name(c.new_name),
{ reveal(insert_valid); }

pub proof fn removal_deletes_exactly_one_live_non_dot_binding(c: RemoveChange)
    requires remove_valid(c),
    ensures retained(c.before, c.after, c.record as int, c.after.block.records.len() as int),
        c.before.block.records[c.record as int].inode != 0,
        c.after.block.records[c.record as int].inode == 0,
        proper_name(name(c.before, c.record as int)),
{ reveal(remove_valid); }

pub proof fn insertion_frames_every_unrelated_byte(c: InsertChange, i: int)
    requires insert_valid(c), 0 <= i < 4096, !insert_frame(c, i),
    ensures c.after.block.raw[i] == c.before.block.raw[i],
{ reveal(insert_valid); }

pub proof fn removal_frames_every_byte_outside_inode_word_and_checksum(c: RemoveChange, i: int)
    requires remove_valid(c), 0 <= i < 4096,
        !inode_frame((c.before.block.records[c.record as int].name_offset - 8) as nat, i),
    ensures c.after.block.raw[i] == c.before.block.raw[i],
{ reveal(remove_valid); }

pub struct DotDotChange {
    pub before: PieceView, pub after: PieceView, pub record: usize,
    pub old_parent: u32, pub new_parent: u32,
}
#[verifier::opaque]
pub open spec fn dotdot_valid(c: DotDotChange) -> bool {
    let old = c.before.block.records[c.record as int];
    &&& same_context(c.before, c.after)
    &&& !c.before.indexed && c.before.logical == 0 && c.record == 1
    &&& c.before.block.records.len() > 1 && c.after.block.records.len() == c.before.block.records.len()
    &&& 0 < c.old_parent <= c.before.block.inodes && 0 < c.new_parent <= c.before.block.inodes
    &&& old.inode == c.old_parent && old.name_offset == 20 && old.file_type == 2
    &&& name(c.before, 1) == seq![46u8, 46u8]
    &&& c.before.block.records[0].inode != 0 && c.before.block.records[0].file_type == 2
    &&& c.before.block.records[0].name_offset == 8 && c.before.block.records[0].next == 12
    &&& name(c.before, 0) == seq![46u8]
    &&& c.after.block.records[1] == (directory::Entry { inode: c.new_parent, next: old.next,
        name_offset: old.name_offset, name_length: old.name_length, file_type: old.file_type })
    &&& name(c.after, 1) == seq![46u8, 46u8]
    &&& retained(c.before, c.after, 1, 1)
    &&& (forall|i: int| 0 <= i < 4096 && !inode_frame(12, i) ==>
        (#[trigger] c.after.block.raw[i]) == c.before.block.raw[i])
}

/// Retarget the canonical dotdot record in the first linear directory block.
/// Indexed roots need a different checksum domain and are rejected here.
pub fn retarget_dotdot(raw: &[u8], inodes: u32, seed: u32, indexed: bool, logical: u32,
    blocks: u32, large: bool, old_parent: u32, new_parent: u32) -> (r: Option<Vec<u8>>)
    ensures match r { Some(after) => dotdot_valid(DotDotChange {
        before: view(raw@, inodes, seed, indexed, logical, blocks, large),
        after: view(after@, inodes, seed, indexed, logical, blocks, large), record: 1,
        old_parent, new_parent }), None => true },
{
    hide(crc::fold);
    if raw.len() != 4096 || indexed || logical != 0 || old_parent == 0 || old_parent > inodes
        || new_parent == 0 || new_parent > inodes { return None; }
    if !directory::valid_tail(raw, seed) { return None; }
    let before = match directory_piece::parse(raw, inodes, seed, indexed, logical, blocks, large) {
        Some(before) => before, None => { return None; }
    };
    let dot = match before.get(0) { Some(entry) => entry, None => { return None; } };
    let dot_name = before.name(0).unwrap();
    if dot.inode == 0 || dot.file_type != 2 || dot.name_offset != 8 || dot.next != 12
        || dot_name.len() != 1 || dot_name[0] != 46 { return None; }
    let entry = match before.get(1) { Some(entry) => entry, None => { return None; } };
    let old_name = before.name(1).unwrap();
    if entry.inode != old_parent || entry.name_offset != 20 || entry.file_type != 2
        || old_name.len() != 2 || old_name[0] != 46 || old_name[1] != 46 { return None; }
    proof {
        assert(dot_name@ =~= seq![46u8]);
        assert(old_name@ =~= seq![46u8, 46u8]);
    }
    let mut after = copy_block(raw);
    bytes::write_le32(after.as_mut_slice(), 12, new_parent);
    let checksum = crc::crc32c(seed, &after[..4084]);
    bytes::write_le32(after.as_mut_slice(), 4092, checksum);
    if !directory::valid_tail(&after, seed) { return None; }
    let parsed = match directory_piece::parse(&after, inodes, seed, indexed, logical, blocks, large) {
        Some(parsed) => parsed, None => { return None; }
    };
    if parsed.len() != before.len() { return None; }
    let next = match parsed.get(1) { Some(entry) => entry, None => { return None; } };
    let next_name = parsed.name(1).unwrap();
    if next.inode != new_parent || next.next != entry.next || next.name_offset != entry.name_offset
        || next.name_length != entry.name_length || next.file_type != entry.file_type
        || !bytes::equal(next_name, old_name) { return None; }
    if !check_retained(&before, &parsed, 1, 1) { return None; }
    if !check_inode_frame(raw, &after, 12) { return None; }
    let ghost change = DotDotChange { before: before.view(), after: parsed.view(), record: 1, old_parent, new_parent };
    assert(dotdot_valid(change)) by { reveal(dotdot_valid); }
    Some(after)
}

pub proof fn dotdot_retargets_exactly_one_parent_and_frames_the_other_bindings(c: DotDotChange)
    requires dotdot_valid(c),
    ensures c.before.block.records[1].inode == c.old_parent,
        c.after.block.records[1].inode == c.new_parent,
        name(c.before, 1) == seq![46u8, 46u8], name(c.after, 1) == seq![46u8, 46u8],
        retained(c.before, c.after, 1, 1), !c.before.indexed,
        directory_block::tail(c.before.block.raw, c.before.block.seed),
        directory_block::tail(c.after.block.raw, c.after.block.seed),
{ reveal(dotdot_valid); }


}
