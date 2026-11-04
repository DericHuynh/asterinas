// SPDX-License-Identifier: MPL-2.0

//! Source-derived namespace entries and bounded enumeration predicates.
//! Canonical directory record uniqueness fixes the stream independently of
//! the traversal. Link counts, dot/parent relations and rooted topology are
//! separate obligations beyond this source/target/unique-name layer.

use vstd::prelude::*;
use crate::{allocated_inode, allocation::AllocationView, directory_source, name_set};

verus! {

pub const MAX_DIRECTORY_BLOCKS: u32 = 4096;

pub struct EntryView {
    pub directory: u32, pub logical: u32, pub record: usize, pub target: u32,
    pub generation: u32, pub file_type: u8, pub name: Seq<u8>,
}

pub open spec fn is_directory(v: AllocationView, n: u32) -> bool {
    allocated_inode::live(v.index, n) && allocated_inode::source_view(v, n).mode & 0xf000 == 0x4000
}

pub open spec fn block_count(v: AllocationView, n: u32) -> nat {
    allocated_inode::source_view(v, n).size as nat / 4096
}

pub open spec fn entry(v: AllocationView, n: u32, logical: u32, record: int) -> EntryView {
    let e = directory_source::records(v, n, logical)[record];
    let raw = directory_source::raw(v, n, logical);
    EntryView { directory: n, logical, record: record as usize, target: e.inode,
        generation: allocated_inode::source_view(v, e.inode).generation, file_type: e.file_type,
        name: raw.subrange(e.name_offset as int, e.name_offset as int + e.name_length as int) }
}

#[verifier::opaque]
pub open spec fn block_entries(v: AllocationView, n: u32, logical: u32, count: nat) -> Seq<EntryView>
    decreases count,
{
    if count == 0 { Seq::empty() }
    else {
        let prefix = block_entries(v, n, logical, (count - 1) as nat);
        if directory_source::records(v, n, logical)[count as int - 1].inode == 0 { prefix }
        else { prefix.push(entry(v, n, logical, count as int - 1)) }
    }
}

#[verifier::opaque]
pub open spec fn directory_entries(v: AllocationView, n: u32, count: nat) -> Seq<EntryView>
    decreases count,
{
    if count == 0 { Seq::empty() }
    else { directory_entries(v, n, (count - 1) as nat)
        + block_entries(v, n, (count - 1) as u32, directory_source::records(v, n, (count - 1) as u32).len()) }
}

#[verifier::opaque]
pub open spec fn entries(v: AllocationView, count: nat) -> Seq<EntryView>
    decreases count,
{
    if count == 0 { Seq::empty() }
    else { entries(v, (count - 1) as nat) + if is_directory(v, count as u32) {
        directory_entries(v, count as u32, block_count(v, count as u32))
    } else { Seq::empty() } }
}

pub open spec fn entry_ok(v: AllocationView, e: EntryView) -> bool {
    let target = allocated_inode::source_view(v, e.target);
    &&& allocated_inode::live(v.index, e.directory)
    &&& allocated_inode::source_view(v, e.directory).mode & 0xf000 == 0x4000
    &&& allocated_inode::live(v.index, e.target)
    &&& e.generation == target.generation
    &&& if e.file_type == 1 { target.mode & 0xf000 == 0x8000 }
        else { e.file_type == 2 && target.mode & 0xf000 == 0x4000 }
}

#[verifier::opaque]
pub open spec fn entries_typed(v: AllocationView, entries: Seq<EntryView>) -> bool {
    forall|i: int| 0 <= i < entries.len() ==> #[trigger] entry_ok(v, entries[i])
}

pub open spec fn keys(entries: Seq<EntryView>) -> Seq<name_set::KeyView> {
    Seq::new(entries.len(), |i: int| (entries[i].directory, entries[i].name))
}

#[verifier::opaque]
pub open spec fn blocks_valid(v: AllocationView, n: u32, count: nat) -> bool {
    forall|logical: u32| logical < count ==> #[trigger] directory_source::valid_block(v, n, logical)
}

pub open spec fn directory_valid(v: AllocationView, n: u32) -> bool {
    let node = allocated_inode::source_view(v, n);
    node.size > 0 && node.size % 4096 == 0 && blocks_valid(v, n, block_count(v, n))
}

#[verifier::opaque]
pub open spec fn directories_valid(v: AllocationView, count: nat) -> bool {
    forall|n: u32| 0 < n <= count && is_directory(v, n) ==> #[trigger] directory_valid(v, n)
}

#[verifier::opaque]
pub open spec fn total_blocks(v: AllocationView, count: nat) -> nat
    decreases count,
{
    if count == 0 { 0nat }
    else { total_blocks(v, (count - 1) as nat) + if is_directory(v, count as u32) { block_count(v, count as u32) } else { 0nat } }
}

pub open spec fn has_name(entries: Seq<EntryView>, directory: u32, name: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < entries.len() && (#[trigger] entries[i]).directory == directory && entries[i].name == name
}

}
