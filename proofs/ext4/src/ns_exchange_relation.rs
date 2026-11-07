// SPDX-License-Identifier: MPL-2.0

//! Exact typed full-key semantics for regular and directory exchanges.
//! Record coordinates may change. The constructor separately certifies inode
//! edits, byte framing, and admission of the complete resulting namespace.
//! This relation does not grant credential or VFS authority.

use vstd::prelude::*;
use crate::{bytes, ea_directory_index::DirectoryIndex, namespace_model::EntryView,
    ns_file_rename_relation::{is_exchange, Operation}, ns_namespace_relation as edges};

verus! {

pub struct Request {
    pub operation: Operation, pub source_directory: u32, pub old_name: Seq<u8>,
    pub destination_directory: u32, pub new_name: Seq<u8>,
    pub target: u32, pub generation: u32, pub target_type: u8,
    pub displaced: u32, pub displaced_generation: u32, pub displaced_type: u8,
    pub source_parent_generation: u32, pub destination_parent_generation: u32,
}
pub open spec fn same_inode(q: Request) -> bool { q.target == q.displaced }
pub open spec fn same_key(q: Request) -> bool {
    q.source_directory == q.destination_directory && q.old_name == q.new_name
}
pub open spec fn moved_source_parent(q: Request, e: EntryView) -> bool {
    !same_inode(q) && q.target_type == 2 && q.source_directory != q.destination_directory
        && e.directory == q.target && edges::dotdot(e.name)
}
pub open spec fn moved_displaced_parent(q: Request, e: EntryView) -> bool {
    !same_inode(q) && q.displaced_type == 2 && q.source_directory != q.destination_directory
        && e.directory == q.displaced && edges::dotdot(e.name)
}
pub open spec fn affected(q: Request, e: EntryView) -> bool {
    edges::key(e, q.source_directory, q.old_name)
        || edges::key(e, q.destination_directory, q.new_name)
        || moved_source_parent(q, e) || moved_displaced_parent(q, e)
}
pub open spec fn before_entry(after: Seq<EntryView>, q: Request, e: EntryView) -> bool {
    if same_inode(q) { edges::retains(after, e) }
    else if edges::key(e, q.source_directory, q.old_name) {
        e.target == q.target && e.generation == q.generation && e.file_type == q.target_type
    } else if edges::key(e, q.destination_directory, q.new_name) {
        e.target == q.displaced && e.generation == q.displaced_generation && e.file_type == q.displaced_type
    } else if moved_source_parent(q, e) {
        e.target == q.source_directory && e.generation == q.source_parent_generation && e.file_type == 2
            && edges::binding(after, e.directory, e.name, q.destination_directory, q.destination_parent_generation, 2)
    } else if moved_displaced_parent(q, e) {
        e.target == q.destination_directory && e.generation == q.destination_parent_generation && e.file_type == 2
            && edges::binding(after, e.directory, e.name, q.source_directory, q.source_parent_generation, 2)
    } else { edges::retains(after, e) }
}
pub open spec fn after_entry(before: Seq<EntryView>, q: Request, e: EntryView) -> bool {
    if same_inode(q) { edges::retains(before, e) }
    else if edges::key(e, q.source_directory, q.old_name) {
        e.target == q.displaced && e.generation == q.displaced_generation && e.file_type == q.displaced_type
    } else if edges::key(e, q.destination_directory, q.new_name) {
        e.target == q.target && e.generation == q.generation && e.file_type == q.target_type
    } else if moved_source_parent(q, e) {
        e.target == q.destination_directory && e.generation == q.destination_parent_generation && e.file_type == 2
            && edges::binding(before, e.directory, e.name, q.source_directory, q.source_parent_generation, 2)
    } else if moved_displaced_parent(q, e) {
        e.target == q.source_directory && e.generation == q.source_parent_generation && e.file_type == 2
            && edges::binding(before, e.directory, e.name, q.destination_directory, q.destination_parent_generation, 2)
    } else { edges::retains(before, e) }
}
pub open spec fn parent_bindings(before: Seq<EntryView>, after: Seq<EntryView>, q: Request) -> bool {
    &&& (!same_inode(q) && q.source_directory != q.destination_directory && q.target_type == 2 ==>
        edges::binding(before, q.target, seq![46u8, 46u8], q.source_directory, q.source_parent_generation, 2)
            && edges::binding(after, q.target, seq![46u8, 46u8], q.destination_directory, q.destination_parent_generation, 2))
    &&& (!same_inode(q) && q.source_directory != q.destination_directory && q.displaced_type == 2 ==>
        edges::binding(before, q.displaced, seq![46u8, 46u8], q.destination_directory, q.destination_parent_generation, 2)
            && edges::binding(after, q.displaced, seq![46u8, 46u8], q.source_directory, q.source_parent_generation, 2))
}

#[verifier::opaque]
pub open spec fn relation(before: Seq<EntryView>, after: Seq<EntryView>, operation: Operation,
    source_directory: u32, old_name: Seq<u8>, destination_directory: u32, new_name: Seq<u8>,
    target: u32, generation: u32, target_type: u8,
    displaced: u32, displaced_generation: u32, displaced_type: u8,
    source_parent_generation: u32, destination_parent_generation: u32) -> bool {
    let q = Request { operation, source_directory, old_name, destination_directory, new_name,
        target, generation, target_type, displaced, displaced_generation, displaced_type,
        source_parent_generation, destination_parent_generation };
    &&& operation == Operation::Exchange
    &&& (target_type == 1 || target_type == 2) && (displaced_type == 1 || displaced_type == 2)
    &&& edges::binding(before, source_directory, old_name, target, generation, target_type)
    &&& edges::binding(before, destination_directory, new_name, displaced, displaced_generation, displaced_type)
    &&& (same_inode(q) ==> generation == displaced_generation && target_type == displaced_type
        && (target_type == 1 || same_key(q)))
    &&& (!same_inode(q) ==> !same_key(q))
    &&& edges::binding(after, source_directory, old_name, displaced, displaced_generation, displaced_type)
    &&& edges::binding(after, destination_directory, new_name, target, generation, target_type)
    &&& before.len() == after.len()
    &&& parent_bindings(before, after, q)
    &&& (forall|i: int| 0 <= i < before.len() ==> before_entry(after, q, #[trigger] before[i]))
    &&& (forall|i: int| 0 <= i < after.len() ==> after_entry(before, q, #[trigger] after[i]))
}

struct Arguments<'a> {
    operation: Operation, source_directory: u32, old_name: &'a [u8],
    destination_directory: u32, new_name: &'a [u8], target: u32, generation: u32, target_type: u8,
    displaced: u32, displaced_generation: u32, displaced_type: u8,
    source_parent_generation: u32, destination_parent_generation: u32,
}
impl<'a> Arguments<'a> {
    closed spec fn view(&self) -> Request {
        Request { operation: self.operation, source_directory: self.source_directory, old_name: self.old_name@,
            destination_directory: self.destination_directory, new_name: self.new_name@,
            target: self.target, generation: self.generation, target_type: self.target_type,
            displaced: self.displaced, displaced_generation: self.displaced_generation, displaced_type: self.displaced_type,
            source_parent_generation: self.source_parent_generation,
            destination_parent_generation: self.destination_parent_generation }
    }
}
fn is_dotdot(name: &[u8]) -> (r: bool) ensures r == edges::dotdot(name@) {
    name.len() == 2 && name[0] == 46 && name[1] == 46
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
fn check_parents(before: &DirectoryIndex<'_>, after: &DirectoryIndex<'_>, args: &Arguments<'_>) -> (r: bool)
    ensures before.wf(), after.wf(), r ==> parent_bindings(before.view().entries, after.view().entries, args.view()),
{
    let _ = before.len(); let _ = after.len();
    let name = [46u8, 46u8];
    proof { assert(name@ =~= seq![46u8, 46u8]); }
    if args.target != args.displaced && args.source_directory != args.destination_directory {
        if args.target_type == 2 {
            if !contains_binding(before, args.target, &name, args.source_directory, args.source_parent_generation, 2)
                || !contains_binding(after, args.target, &name, args.destination_directory, args.destination_parent_generation, 2) { return false; }
        }
        if args.displaced_type == 2 {
            if !contains_binding(before, args.displaced, &name, args.destination_directory, args.destination_parent_generation, 2)
                || !contains_binding(after, args.displaced, &name, args.source_directory, args.source_parent_generation, 2) { return false; }
        }
    }
    true
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
        if args.target == args.displaced {
            if !contains_binding(after, directory, name, target, generation, file_type) { return false; }
        } else if directory == args.source_directory && bytes::equal(name, args.old_name) {
            if target != args.target || generation != args.generation || file_type != args.target_type { return false; }
        } else if directory == args.destination_directory && bytes::equal(name, args.new_name) {
            if target != args.displaced || generation != args.displaced_generation || file_type != args.displaced_type { return false; }
        } else if args.target_type == 2 && args.source_directory != args.destination_directory
            && directory == args.target && is_dotdot(name) {
            if target != args.source_directory || generation != args.source_parent_generation || file_type != 2
                || !contains_binding(after, directory, name, args.destination_directory, args.destination_parent_generation, 2) { return false; }
        } else if args.displaced_type == 2 && args.source_directory != args.destination_directory
            && directory == args.displaced && is_dotdot(name) {
            if target != args.destination_directory || generation != args.destination_parent_generation || file_type != 2
                || !contains_binding(after, directory, name, args.source_directory, args.source_parent_generation, 2) { return false; }
        } else {
            if !contains_binding(after, directory, name, target, generation, file_type) { return false; }
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
            if target != args.displaced || generation != args.displaced_generation || file_type != args.displaced_type { return false; }
        } else if directory == args.destination_directory && bytes::equal(name, args.new_name) {
            if target != args.target || generation != args.generation || file_type != args.target_type { return false; }
        } else if args.target_type == 2 && args.source_directory != args.destination_directory
            && directory == args.target && is_dotdot(name) {
            if target != args.destination_directory || generation != args.destination_parent_generation || file_type != 2
                || !contains_binding(before, directory, name, args.source_directory, args.source_parent_generation, 2) { return false; }
        } else if args.displaced_type == 2 && args.source_directory != args.destination_directory
            && directory == args.displaced && is_dotdot(name) {
            if target != args.source_directory || generation != args.source_parent_generation || file_type != 2
                || !contains_binding(before, directory, name, args.destination_directory, args.destination_parent_generation, 2) { return false; }
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
    target: u32, generation: u32, target_type: u8,
    displaced: u32, displaced_generation: u32, displaced_type: u8,
    source_parent_generation: u32, destination_parent_generation: u32) -> (r: bool)
    ensures before.wf(), after.wf(), r ==> relation(before.view().entries, after.view().entries, operation,
        source_directory, old_name@, destination_directory, new_name@, target, generation, target_type,
        displaced, displaced_generation, displaced_type, source_parent_generation, destination_parent_generation),
{
    hide(crate::ea_directory_index::source_has_name);
    let before_count = before.len(); let after_count = after.len();
    if !is_exchange(operation) || (target_type != 1 && target_type != 2)
        || (displaced_type != 1 && displaced_type != 2) { return false; }
    if !contains_binding(before, source_directory, old_name, target, generation, target_type)
        || !contains_binding(before, destination_directory, new_name, displaced, displaced_generation, displaced_type) { return false; }
    if target == displaced {
        if generation != displaced_generation || target_type != displaced_type
            || (target_type == 2 && !(source_directory == destination_directory && bytes::equal(old_name, new_name))) { return false; }
    } else if source_directory == destination_directory && bytes::equal(old_name, new_name) { return false; }
    if !contains_binding(after, source_directory, old_name, displaced, displaced_generation, displaced_type)
        || !contains_binding(after, destination_directory, new_name, target, generation, target_type)
        || before_count != after_count { return false; }
    let args = Arguments { operation, source_directory, old_name, destination_directory, new_name,
        target, generation, target_type, displaced, displaced_generation, displaced_type,
        source_parent_generation, destination_parent_generation };
    if !check_parents(before, after, &args) || !check_before(before, after, &args) || !check_after(before, after, &args) { return false; }
    assert(relation(before.view().entries, after.view().entries, operation, source_directory, old_name@,
        destination_directory, new_name@, target, generation, target_type, displaced, displaced_generation, displaced_type,
        source_parent_generation, destination_parent_generation)) by { reveal(relation); }
    true
}

pub proof fn every_unrelated_full_key_retains_its_exact_binding(before: Seq<EntryView>, after: Seq<EntryView>,
    q: Request, i: int)
    requires relation(before, after, q.operation, q.source_directory, q.old_name, q.destination_directory, q.new_name,
        q.target, q.generation, q.target_type, q.displaced, q.displaced_generation, q.displaced_type,
        q.source_parent_generation, q.destination_parent_generation),
        0 <= i < before.len(), !affected(q, before[i]),
    ensures edges::retains(after, before[i]),
{ reveal(relation); assert(before_entry(after, q, before[i])); }

pub proof fn every_unrelated_full_key_has_an_exact_predecessor(before: Seq<EntryView>, after: Seq<EntryView>,
    q: Request, i: int)
    requires relation(before, after, q.operation, q.source_directory, q.old_name, q.destination_directory, q.new_name,
        q.target, q.generation, q.target_type, q.displaced, q.displaced_generation, q.displaced_type,
        q.source_parent_generation, q.destination_parent_generation),
        0 <= i < after.len(), !affected(q, after[i]),
    ensures edges::retains(before, after[i]),
{ reveal(relation); assert(after_entry(before, q, after[i])); }

pub proof fn same_inode_exchange_preserves_every_full_key(before: Seq<EntryView>, after: Seq<EntryView>, q: Request)
    requires relation(before, after, q.operation, q.source_directory, q.old_name, q.destination_directory, q.new_name,
        q.target, q.generation, q.target_type, q.displaced, q.displaced_generation, q.displaced_type,
        q.source_parent_generation, q.destination_parent_generation), same_inode(q),
    ensures before.len() == after.len(), q.generation == q.displaced_generation, q.target_type == q.displaced_type,
        q.target_type == 1 || same_key(q),
        forall|i: int| 0 <= i < before.len() ==> edges::retains(after, #[trigger] before[i]),
        forall|i: int| 0 <= i < after.len() ==> edges::retains(before, #[trigger] after[i]),
{ reveal(relation); }

pub proof fn exchange_swaps_both_exact_typed_inode_generations(before: Seq<EntryView>, after: Seq<EntryView>, q: Request)
    requires relation(before, after, q.operation, q.source_directory, q.old_name, q.destination_directory, q.new_name,
        q.target, q.generation, q.target_type, q.displaced, q.displaced_generation, q.displaced_type,
        q.source_parent_generation, q.destination_parent_generation),
    ensures q.operation == Operation::Exchange,
        edges::binding(before, q.source_directory, q.old_name, q.target, q.generation, q.target_type),
        edges::binding(before, q.destination_directory, q.new_name, q.displaced, q.displaced_generation, q.displaced_type),
        edges::binding(after, q.source_directory, q.old_name, q.displaced, q.displaced_generation, q.displaced_type),
        edges::binding(after, q.destination_directory, q.new_name, q.target, q.generation, q.target_type),
        before.len() == after.len(),
{ reveal(relation); }

pub proof fn exchanged_directories_have_the_exact_new_parents(before: Seq<EntryView>, after: Seq<EntryView>, q: Request)
    requires relation(before, after, q.operation, q.source_directory, q.old_name, q.destination_directory, q.new_name,
        q.target, q.generation, q.target_type, q.displaced, q.displaced_generation, q.displaced_type,
        q.source_parent_generation, q.destination_parent_generation),
    ensures parent_bindings(before, after, q),
{ reveal(relation); }

}
