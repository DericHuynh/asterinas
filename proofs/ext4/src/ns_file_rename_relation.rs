// SPDX-License-Identifier: MPL-2.0

//! Exact full-key semantics for replacing and exchanging regular-file names.
//! Enumeration coordinates may change when a directory record is split or
//! merged. Inode edits and byte framing are certified by the constructor.

use vstd::prelude::*;
use crate::{bytes, ea_directory_index::DirectoryIndex, namespace_model::{self, EntryView},
    ns_namespace_relation as edges};

verus! {

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Operation { Replace, Exchange }

pub(crate) fn is_exchange(operation: Operation) -> (r: bool)
    ensures r == (operation == Operation::Exchange),
{ match operation { Operation::Exchange => true, Operation::Replace => false } }

pub struct Request {
    pub operation: Operation, pub source_directory: u32, pub old_name: Seq<u8>,
    pub destination_directory: u32, pub new_name: Seq<u8>,
    pub target: u32, pub generation: u32, pub displaced: u32, pub displaced_generation: u32,
    pub source_parent_generation: u32, pub destination_parent_generation: u32,
}
pub open spec fn same_inode(q: Request) -> bool { q.target == q.displaced }
pub open spec fn affected(q: Request, e: EntryView) -> bool {
    edges::key(e, q.source_directory, q.old_name)
        || edges::key(e, q.destination_directory, q.new_name)
}
pub open spec fn before_entry(after: Seq<EntryView>, q: Request, e: EntryView) -> bool {
    if !same_inode(q) && affected(q, e) { true } else { edges::retains(after, e) }
}
pub open spec fn after_entry(before: Seq<EntryView>, q: Request, e: EntryView) -> bool {
    if same_inode(q) { edges::retains(before, e) }
    else if edges::key(e, q.source_directory, q.old_name) {
        q.operation == Operation::Exchange && e.target == q.displaced
            && e.generation == q.displaced_generation && e.file_type == 1
    } else if edges::key(e, q.destination_directory, q.new_name) {
        e.target == q.target && e.generation == q.generation && e.file_type == 1
    } else { edges::retains(before, e) }
}
pub open spec fn linked(entries: Seq<EntryView>, target: u32, generation: u32) -> bool {
    exists|i: int| 0 <= i < entries.len() && (#[trigger] entries[i]).target == target
        && entries[i].generation == generation && entries[i].file_type == 1
}

#[verifier::opaque]
pub open spec fn relation(before: Seq<EntryView>, after: Seq<EntryView>, operation: Operation,
    source_directory: u32, old_name: Seq<u8>, destination_directory: u32, new_name: Seq<u8>,
    target: u32, generation: u32, displaced: u32, displaced_generation: u32,
    source_parent_generation: u32, destination_parent_generation: u32) -> bool {
    let q = Request { operation, source_directory, old_name, destination_directory, new_name,
        target, generation, displaced, displaced_generation,
        source_parent_generation, destination_parent_generation };
    &&& edges::binding(before, source_directory, old_name, target, generation, 1)
    &&& edges::binding(before, destination_directory, new_name, displaced, displaced_generation, 1)
    &&& (same_inode(q) ==> generation == displaced_generation)
    &&& (!same_inode(q) ==> source_directory != destination_directory || old_name != new_name)
    &&& edges::binding(after, destination_directory, new_name, target, generation, 1)
    &&& if same_inode(q) || operation == Operation::Exchange {
        edges::binding(after, source_directory, old_name, displaced, displaced_generation, 1)
            && before.len() == after.len()
    } else {
        !namespace_model::has_name(after, source_directory, old_name)
            && before.len() == after.len() + 1 && linked(after, displaced, displaced_generation)
    }
    &&& (forall|i: int| 0 <= i < before.len() ==> before_entry(after, q, #[trigger] before[i]))
    &&& (forall|i: int| 0 <= i < after.len() ==> after_entry(before, q, #[trigger] after[i]))
}

struct Arguments<'a> {
    operation: Operation, source_directory: u32, old_name: &'a [u8],
    destination_directory: u32, new_name: &'a [u8], target: u32, generation: u32,
    displaced: u32, displaced_generation: u32,
    source_parent_generation: u32, destination_parent_generation: u32,
}
impl<'a> Arguments<'a> {
    closed spec fn view(&self) -> Request {
        Request { operation: self.operation, source_directory: self.source_directory, old_name: self.old_name@,
            destination_directory: self.destination_directory, new_name: self.new_name@,
            target: self.target, generation: self.generation,
            displaced: self.displaced, displaced_generation: self.displaced_generation,
            source_parent_generation: self.source_parent_generation,
            destination_parent_generation: self.destination_parent_generation }
    }
}

fn contains_binding(index: &DirectoryIndex<'_>, directory: u32, name: &[u8],
    target: u32, generation: u32, file_type: u8) -> (r: bool)
    ensures index.wf(), r ==> edges::binding(index.view().entries, directory, name@, target, generation, file_type),
{
    let found = match index.lookup(directory, name) { Some(e) => e, None => { return false; } };
    let (parent, inode, version, kind) = found.identity();
    if parent != directory || inode != target || version != generation || kind != file_type { return false; }
    assert(index.view().entries.contains(found.view()));
    let ghost i = choose|i: int| 0 <= i < index.view().entries.len() && index.view().entries[i] == found.view();
    assert(edges::binding(index.view().entries, directory, name@, target, generation, file_type));
    true
}

fn check_linked(index: &DirectoryIndex<'_>, target: u32, generation: u32) -> (r: bool)
    ensures index.wf(), r ==> linked(index.view().entries, target, generation),
{
    let count = index.len(); let mut i = 0usize;
    while i < count
        invariant index.wf(), count == index.view().entries.len(), i <= count,
        decreases count - i,
    {
        let e = index.get(i).unwrap(); let (_, inode, version, kind) = e.identity();
        if inode == target && version == generation && kind == 1 {
            assert(linked(index.view().entries, target, generation)); return true;
        }
        i += 1;
    }
    false
}

fn check_before(before: &DirectoryIndex<'_>, after: &DirectoryIndex<'_>, args: &Arguments<'_>) -> (r: bool)
    ensures before.wf(), after.wf(), r ==> (forall|i: int| 0 <= i < before.view().entries.len() ==>
        before_entry(after.view().entries, args.view(), #[trigger] before.view().entries[i])),
{
    let count = before.len(); let _ = after.len(); let ghost q = args.view(); let mut i = 0usize;
    while i < count
        invariant before.wf(), after.wf(), count == before.view().entries.len(), i <= count, q == args.view(),
            forall|j: int| 0 <= j < i ==> before_entry(after.view().entries, q, #[trigger] before.view().entries[j]),
        decreases count - i,
    {
        let e = before.get(i).unwrap(); let (directory, target, generation, file_type) = e.identity();
        let name = e.name();
        let changed = args.target != args.displaced
            && ((directory == args.source_directory && bytes::equal(name, args.old_name))
                || (directory == args.destination_directory && bytes::equal(name, args.new_name)));
        if !changed && !contains_binding(after, directory, name, target, generation, file_type) { return false; }
        assert(before_entry(after.view().entries, q, before.view().entries[i as int]));
        i += 1;
    }
    true
}

fn check_after(before: &DirectoryIndex<'_>, after: &DirectoryIndex<'_>, args: &Arguments<'_>) -> (r: bool)
    ensures before.wf(), after.wf(), r ==> (forall|i: int| 0 <= i < after.view().entries.len() ==>
        after_entry(before.view().entries, args.view(), #[trigger] after.view().entries[i])),
{
    let _ = before.len(); let count = after.len(); let ghost q = args.view(); let mut i = 0usize;
    while i < count
        invariant before.wf(), after.wf(), count == after.view().entries.len(), i <= count, q == args.view(),
            forall|j: int| 0 <= j < i ==> after_entry(before.view().entries, q, #[trigger] after.view().entries[j]),
        decreases count - i,
    {
        let e = after.get(i).unwrap(); let (directory, target, generation, file_type) = e.identity();
        let name = e.name();
        if args.target == args.displaced {
            if !contains_binding(before, directory, name, target, generation, file_type) { return false; }
        } else if directory == args.source_directory && bytes::equal(name, args.old_name) {
            if !is_exchange(args.operation) || target != args.displaced
                || generation != args.displaced_generation || file_type != 1 { return false; }
        } else if directory == args.destination_directory && bytes::equal(name, args.new_name) {
            if target != args.target || generation != args.generation || file_type != 1 { return false; }
        } else {
            if !contains_binding(before, directory, name, target, generation, file_type) { return false; }
        }
        assert(after_entry(before.view().entries, q, after.view().entries[i as int]));
        i += 1;
    }
    true
}

pub fn check(before: &DirectoryIndex<'_>, after: &DirectoryIndex<'_>, operation: Operation,
    source_directory: u32, old_name: &[u8], destination_directory: u32, new_name: &[u8],
    target: u32, generation: u32, displaced: u32, displaced_generation: u32,
    source_parent_generation: u32, destination_parent_generation: u32) -> (r: bool)
    ensures before.wf(), after.wf(), r ==> relation(before.view().entries, after.view().entries, operation,
        source_directory, old_name@, destination_directory, new_name@, target, generation,
        displaced, displaced_generation, source_parent_generation, destination_parent_generation),
{
    hide(crate::ea_directory_index::source_has_name); hide(namespace_model::has_name);
    let before_count = before.len(); let after_count = after.len();
    if !contains_binding(before, source_directory, old_name, target, generation, 1)
        || !contains_binding(before, destination_directory, new_name, displaced, displaced_generation, 1) { return false; }
    if target == displaced {
        if generation != displaced_generation { return false; }
    } else if source_directory == destination_directory && bytes::equal(old_name, new_name) { return false; }
    if !contains_binding(after, destination_directory, new_name, target, generation, 1) { return false; }
    if target == displaced || is_exchange(operation) {
        if !contains_binding(after, source_directory, old_name, displaced, displaced_generation, 1)
            || before_count != after_count { return false; }
    } else {
        if after.lookup(source_directory, old_name).is_some() || after_count == usize::MAX
            || before_count != after_count + 1 || !check_linked(after, displaced, displaced_generation) { return false; }
    }
    let args = Arguments { operation, source_directory, old_name, destination_directory, new_name,
        target, generation, displaced, displaced_generation, source_parent_generation, destination_parent_generation };
    if !check_before(before, after, &args) || !check_after(before, after, &args) { return false; }
    assert(relation(before.view().entries, after.view().entries, operation, source_directory, old_name@,
        destination_directory, new_name@, target, generation, displaced, displaced_generation,
        source_parent_generation, destination_parent_generation)) by { reveal(relation); }
    true
}

pub proof fn every_unrelated_full_key_retains_its_exact_binding(before: Seq<EntryView>, after: Seq<EntryView>,
    q: Request, i: int)
    requires relation(before, after, q.operation, q.source_directory, q.old_name, q.destination_directory, q.new_name,
        q.target, q.generation, q.displaced, q.displaced_generation,
        q.source_parent_generation, q.destination_parent_generation),
        0 <= i < before.len(), !affected(q, before[i]),
    ensures edges::retains(after, before[i]),
{ reveal(relation); assert(before_entry(after, q, before[i])); }

pub proof fn same_inode_rename_preserves_every_full_key(before: Seq<EntryView>, after: Seq<EntryView>,
    q: Request, i: int)
    requires relation(before, after, q.operation, q.source_directory, q.old_name, q.destination_directory, q.new_name,
        q.target, q.generation, q.displaced, q.displaced_generation,
        q.source_parent_generation, q.destination_parent_generation),
        same_inode(q), 0 <= i < before.len(),
    ensures before.len() == after.len(), edges::retains(after, before[i]),
{ reveal(relation); assert(before_entry(after, q, before[i])); }

pub proof fn replacing_rename_removes_only_the_source_and_keeps_the_victim_linked(
    before: Seq<EntryView>, after: Seq<EntryView>, q: Request)
    requires relation(before, after, q.operation, q.source_directory, q.old_name, q.destination_directory, q.new_name,
        q.target, q.generation, q.displaced, q.displaced_generation,
        q.source_parent_generation, q.destination_parent_generation),
        q.operation == Operation::Replace, !same_inode(q),
    ensures !namespace_model::has_name(after, q.source_directory, q.old_name),
        edges::binding(after, q.destination_directory, q.new_name, q.target, q.generation, 1),
        linked(after, q.displaced, q.displaced_generation), before.len() == after.len() + 1,
{ reveal(relation); }

pub proof fn exchange_swaps_both_exact_inode_generations(before: Seq<EntryView>, after: Seq<EntryView>, q: Request)
    requires relation(before, after, q.operation, q.source_directory, q.old_name, q.destination_directory, q.new_name,
        q.target, q.generation, q.displaced, q.displaced_generation,
        q.source_parent_generation, q.destination_parent_generation),
        q.operation == Operation::Exchange,
    ensures edges::binding(after, q.source_directory, q.old_name, q.displaced, q.displaced_generation, 1),
        edges::binding(after, q.destination_directory, q.new_name, q.target, q.generation, 1),
        before.len() == after.len(),
{ reveal(relation); }

}
