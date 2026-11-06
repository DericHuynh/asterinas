// SPDX-License-Identifier: MPL-2.0

//! Exact namespace edge transformations, independent of record ordinals.
//! Repacking/splitting a canonical record can shift enumeration coordinates;
//! every full key must nevertheless retain its exact typed inode generation.

use vstd::prelude::*;
use crate::{bytes, ea_directory_index::DirectoryIndex, namespace_model::{self, EntryView}};

verus! {

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Operation { Rename, Link, Unlink }


pub(crate) fn is_rename(operation: Operation) -> (r: bool)
    ensures r == (operation == Operation::Rename),
{ match operation { Operation::Rename => true, _ => false } }
pub(crate) fn is_link(operation: Operation) -> (r: bool)
    ensures r == (operation == Operation::Link),
{ match operation { Operation::Link => true, _ => false } }
pub(crate) fn is_unlink(operation: Operation) -> (r: bool)
    ensures r == (operation == Operation::Unlink),
{ match operation { Operation::Unlink => true, _ => false } }

pub struct Request {
    pub operation: Operation, pub source_directory: u32, pub old_name: Seq<u8>,
    pub destination_directory: u32, pub new_name: Seq<u8>, pub target: u32,
    pub generation: u32, pub file_type: u8,
    pub source_parent_generation: u32, pub destination_parent_generation: u32,
}
pub open spec fn key(e: EntryView, directory: u32, name: Seq<u8>) -> bool {
    e.directory == directory && e.name == name
}
pub open spec fn same_binding(a: EntryView, b: EntryView) -> bool {
    a.directory == b.directory && a.name == b.name && a.target == b.target
        && a.generation == b.generation && a.file_type == b.file_type
}
pub open spec fn binding(entries: Seq<EntryView>, directory: u32, name: Seq<u8>,
    target: u32, generation: u32, file_type: u8) -> bool {
    exists|i: int| 0 <= i < entries.len() && key(#[trigger] entries[i], directory, name)
        && entries[i].target == target && entries[i].generation == generation && entries[i].file_type == file_type
}
pub open spec fn retains(entries: Seq<EntryView>, e: EntryView) -> bool {
    binding(entries, e.directory, e.name, e.target, e.generation, e.file_type)
}
pub open spec fn dotdot(name: Seq<u8>) -> bool {
    name.len() == 2 && name[0] == 46 && name[1] == 46
}
pub open spec fn moved_parent(q: Request, e: EntryView) -> bool {
    q.operation == Operation::Rename && q.file_type == 2 && q.source_directory != q.destination_directory
        && e.directory == q.target && dotdot(e.name)
}
pub open spec fn before_entry(after: Seq<EntryView>, q: Request, e: EntryView) -> bool {
    if q.operation != Operation::Link && key(e, q.source_directory, q.old_name) { true }
    else if moved_parent(q, e) {
        binding(after, e.directory, e.name, q.destination_directory, q.destination_parent_generation, 2)
    } else { retains(after, e) }
}
pub open spec fn after_entry(before: Seq<EntryView>, q: Request, e: EntryView) -> bool {
    if q.operation != Operation::Unlink && key(e, q.destination_directory, q.new_name) {
        e.target == q.target && e.generation == q.generation && e.file_type == q.file_type
    } else if moved_parent(q, e) {
        binding(before, e.directory, e.name, q.source_directory, q.source_parent_generation, 2)
    } else { retains(before, e) }
}
#[verifier::opaque]
pub open spec fn relation(before: Seq<EntryView>, after: Seq<EntryView>, operation: Operation,
    source_directory: u32, old_name: Seq<u8>, destination_directory: u32, new_name: Seq<u8>,
    target: u32, generation: u32, file_type: u8,
    source_parent_generation: u32, destination_parent_generation: u32) -> bool {
    let q = Request { operation, source_directory, old_name, destination_directory, new_name, target,
        generation, file_type, source_parent_generation, destination_parent_generation };
    &&& (file_type == 1 || file_type == 2 && operation == Operation::Rename)
    &&& binding(before, source_directory, old_name, target, generation, file_type)
    &&& (operation == Operation::Unlink || !namespace_model::has_name(before, destination_directory, new_name))
    &&& (operation == Operation::Link || !namespace_model::has_name(after, source_directory, old_name))
    &&& (operation == Operation::Unlink || binding(after, destination_directory, new_name, target, generation, file_type))
    &&& after.len() + (if operation == Operation::Unlink { 1nat } else { 0nat })
        == before.len() + (if operation == Operation::Link { 1nat } else { 0nat })
    &&& (forall|i: int| 0 <= i < before.len() ==> before_entry(after, q, #[trigger] before[i]))
    &&& (forall|i: int| 0 <= i < after.len() ==> after_entry(before, q, #[trigger] after[i]))
}

struct Arguments<'a> {
    operation: Operation, source_directory: u32, old_name: &'a [u8], destination_directory: u32,
    new_name: &'a [u8], target: u32, generation: u32, file_type: u8,
    source_parent_generation: u32, destination_parent_generation: u32,
}
impl<'a> Arguments<'a> {
    closed spec fn view(&self) -> Request {
        Request { operation: self.operation, source_directory: self.source_directory, old_name: self.old_name@,
            destination_directory: self.destination_directory, new_name: self.new_name@,
            target: self.target, generation: self.generation, file_type: self.file_type,
            source_parent_generation: self.source_parent_generation, destination_parent_generation: self.destination_parent_generation }
    }
}
fn is_dotdot(name: &[u8]) -> (r: bool) ensures r == dotdot(name@) {
    name.len() == 2 && name[0] == 46 && name[1] == 46
}
fn contains_binding(index: &DirectoryIndex<'_>, directory: u32, name: &[u8],
    target: u32, generation: u32, file_type: u8) -> (r: bool)
    ensures index.wf(), r ==> binding(index.view().entries, directory, name@, target, generation, file_type),
{
    let found = match index.lookup(directory, name) { Some(e) => e, None => { return false; } };
    let (parent, inode, version, kind) = found.identity();
    if parent != directory || inode != target || version != generation || kind != file_type { return false; }
    assert(index.view().entries.contains(found.view()));
    let ghost i = choose|i: int| 0 <= i < index.view().entries.len() && index.view().entries[i] == found.view();
    assert(binding(index.view().entries, directory, name@, target, generation, file_type));
    true
}
fn check_before(before: &DirectoryIndex<'_>, after: &DirectoryIndex<'_>, args: &Arguments<'_>) -> (r: bool)
    ensures before.wf(), after.wf(), r ==> (forall|i: int| 0 <= i < before.view().entries.len() ==>
        before_entry(after.view().entries, args.view(), #[trigger] before.view().entries[i])),
{
    let count = before.len(); let _ = after.len(); let ghost q = args.view();
    let mut i = 0usize;
    while i < count
        invariant before.wf(), after.wf(), count == before.view().entries.len(), i <= count, q == args.view(),
            forall|j: int| 0 <= j < i ==> before_entry(after.view().entries, q, #[trigger] before.view().entries[j]),
        decreases count - i,
    {
        let e = before.get(i).unwrap(); let (directory, target, generation, file_type) = e.identity();
        let name = e.name();
        let removed = !is_link(args.operation) && directory == args.source_directory
            && bytes::equal(name, args.old_name);
        if !removed {
            let parent = is_rename(args.operation) && args.file_type == 2
                && args.source_directory != args.destination_directory && directory == args.target && is_dotdot(name);
            if parent {
                if !contains_binding(after, directory, name, args.destination_directory, args.destination_parent_generation, 2) { return false; }
            } else {
                if !contains_binding(after, directory, name, target, generation, file_type) { return false; }
            }
        }
        assert(before_entry(after.view().entries, q, before.view().entries[i as int]));
        i += 1;
    }
    true
}
fn check_after(before: &DirectoryIndex<'_>, after: &DirectoryIndex<'_>, args: &Arguments<'_>) -> (r: bool)
    ensures before.wf(), after.wf(), r ==> (forall|i: int| 0 <= i < after.view().entries.len() ==>
        after_entry(before.view().entries, args.view(), #[trigger] after.view().entries[i])),
{
    let _ = before.len(); let count = after.len(); let ghost q = args.view();
    let mut i = 0usize;
    while i < count
        invariant before.wf(), after.wf(), count == after.view().entries.len(), i <= count, q == args.view(),
            forall|j: int| 0 <= j < i ==> after_entry(before.view().entries, q, #[trigger] after.view().entries[j]),
        decreases count - i,
    {
        let e = after.get(i).unwrap(); let (directory, target, generation, file_type) = e.identity();
        let name = e.name();
        let added = !is_unlink(args.operation) && directory == args.destination_directory
            && bytes::equal(name, args.new_name);
        if added {
            if target != args.target || generation != args.generation || file_type != args.file_type { return false; }
        } else {
            let parent = is_rename(args.operation) && args.file_type == 2
                && args.source_directory != args.destination_directory && directory == args.target && is_dotdot(name);
            if parent {
                if !contains_binding(before, directory, name, args.source_directory, args.source_parent_generation, 2) { return false; }
            } else {
                if !contains_binding(before, directory, name, target, generation, file_type) { return false; }
            }
        }
        assert(after_entry(before.view().entries, q, after.view().entries[i as int]));
        i += 1;
    }
    true
}

pub fn check(before: &DirectoryIndex<'_>, after: &DirectoryIndex<'_>, operation: Operation,
    source_directory: u32, old_name: &[u8], destination_directory: u32, new_name: &[u8],
    target: u32, generation: u32, file_type: u8,
    source_parent_generation: u32, destination_parent_generation: u32) -> (r: bool)
    ensures before.wf(), after.wf(), r ==> relation(before.view().entries, after.view().entries, operation,
        source_directory, old_name@, destination_directory, new_name@, target, generation, file_type,
        source_parent_generation, destination_parent_generation),
{
    hide(crate::ea_directory_index::source_has_name);
    hide(namespace_model::has_name);
    let before_count = before.len(); let after_count = after.len();
    if file_type != 1 && !(file_type == 2 && is_rename(operation)) { return false; }
    if !contains_binding(before, source_directory, old_name, target, generation, file_type) { return false; }
    if !is_unlink(operation) && before.lookup(destination_directory, new_name).is_some() { return false; }
    if !is_link(operation) && after.lookup(source_directory, old_name).is_some() { return false; }
    if !is_unlink(operation) && !contains_binding(after, destination_directory, new_name, target, generation, file_type) { return false; }
    if is_link(operation) {
        if before_count == usize::MAX || after_count != before_count + 1 { return false; }
    } else if is_unlink(operation) {
        if after_count == usize::MAX || before_count != after_count + 1 { return false; }
    } else if before_count != after_count { return false; }
    let args = Arguments { operation, source_directory, old_name, destination_directory, new_name, target,
        generation, file_type, source_parent_generation, destination_parent_generation };
    if !check_before(before, after, &args) || !check_after(before, after, &args) { return false; }
    assert(relation(before.view().entries, after.view().entries, operation, source_directory, old_name@,
        destination_directory, new_name@, target, generation, file_type, source_parent_generation,
        destination_parent_generation)) by { reveal(relation); }
    true
}

pub proof fn every_unrelated_full_key_retains_its_exact_binding(before: Seq<EntryView>, after: Seq<EntryView>,
    q: Request, i: int)
    requires relation(before, after, q.operation, q.source_directory, q.old_name, q.destination_directory,
        q.new_name, q.target, q.generation, q.file_type, q.source_parent_generation, q.destination_parent_generation),
        0 <= i < before.len(), !key(before[i], q.source_directory, q.old_name), !moved_parent(q, before[i]),
    ensures retains(after, before[i]),
{ reveal(relation); assert(before_entry(after, q, before[i])); }

pub proof fn accepted_removals_leave_no_old_name(before: Seq<EntryView>, after: Seq<EntryView>, q: Request)
    requires relation(before, after, q.operation, q.source_directory, q.old_name, q.destination_directory,
        q.new_name, q.target, q.generation, q.file_type, q.source_parent_generation, q.destination_parent_generation),
        q.operation != Operation::Link,
    ensures !namespace_model::has_name(after, q.source_directory, q.old_name),
{ reveal(relation); }

pub proof fn accepted_additions_have_the_exact_target_generation(before: Seq<EntryView>, after: Seq<EntryView>, q: Request)
    requires relation(before, after, q.operation, q.source_directory, q.old_name, q.destination_directory,
        q.new_name, q.target, q.generation, q.file_type, q.source_parent_generation, q.destination_parent_generation),
        q.operation != Operation::Unlink,
    ensures binding(after, q.destination_directory, q.new_name, q.target, q.generation, q.file_type),
{ reveal(relation); }

}
