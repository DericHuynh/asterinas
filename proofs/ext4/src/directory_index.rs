// SPDX-License-Identifier: MPL-2.0

//! Complete source-bound linear-directory enumeration and typed unique names.
//! Every allocated directory block is checked, including empty preallocation.
//! This index does not yet certify dot/parent topology, link counts, recovery,
//! a mount, credentials or OSTD/device authority.

use vstd::prelude::*;
use crate::{allocated_inode::{self, AllocatedInode}, allocation::{self, Allocation, AllocationView}, directory_file,
    directory_source, name_set::{self, NameSet}, namespace_model::{self as model, EntryView}};

verus! {

pub struct Entry {
    directory: u32, logical: u32, record: usize, target: u32, generation: u32, file_type: u8, name: Vec<u8>,
}

impl Entry {
    pub closed spec fn view(&self) -> EntryView {
        EntryView { directory: self.directory, logical: self.logical, record: self.record, target: self.target,
            generation: self.generation, file_type: self.file_type, name: self.name@ }
    }

    pub fn identity(&self) -> (r: (u32, u32, u32, u8))
        ensures r == (self.view().directory, self.view().target, self.view().generation, self.view().file_type),
    { (self.directory, self.target, self.generation, self.file_type) }

    pub fn name(&self) -> (r: &[u8]) ensures r@ == self.view().name { self.name.as_slice() }

    pub fn location(&self) -> (r: (u32, usize)) ensures r == (self.view().logical, self.view().record) {
        (self.logical, self.record)
    }
}

pub open spec fn views(entries: Seq<Entry>) -> Seq<EntryView> { Seq::new(entries.len(), |i: int| entries[i].view()) }

fn capture(directory: u32, logical: u32, record: usize, target: u32, generation: u32, file_type: u8, name: &[u8]) -> (r: Entry)
    requires name.len() <= 255,
    ensures r.view() == (EntryView { directory, logical, record, target, generation, file_type, name: name@ }),
{
    let mut copy = Vec::new();
    let mut i = 0usize;
    while i < name.len()
        invariant i <= name.len() <= 255, copy@ == name@.subrange(0, i as int),
        decreases name.len() - i,
    {
        copy.push(name[i]);
        assert(copy@ =~= name@.subrange(0, i as int + 1));
        i += 1;
    }
    assert(copy@ =~= name@);
    Entry { directory, logical, record, target, generation, file_type, name: copy }
}

proof fn append_typed_entry(v: AllocationView, before: Seq<EntryView>, next: EntryView)
    requires model::entries_typed(v, before), model::entry_ok(v, next),
    ensures model::entries_typed(v, before.push(next)),
{
    reveal(model::entries_typed);
    assert forall|i: int| 0 <= i < before.len() + 1 implies #[trigger] model::entry_ok(v, before.push(next)[i]) by {
        if i < before.len() { assert(model::entry_ok(v, before[i])); }
    }
}

fn append_block(node: &AllocatedInode<'_, '_>, logical: u32, mut entries: Vec<Entry>, mut names: NameSet)
    -> (r: Option<(Vec<Entry>, NameSet)>)
    requires model::entries_typed(node.view().volume, views(entries@)), names.wf(), names.view().keys == model::keys(views(entries@)),
    ensures node.wf(), match r {
        Some((next, index)) => model::entries_typed(node.view().volume, views(next@)) && index.wf()
            && index.view().keys == model::keys(views(next@))
            && directory_source::valid_block(node.view().volume, node.view().number, logical)
            && views(next@) == views(entries@) + model::block_entries(node.view().volume, node.view().number, logical,
                directory_source::records(node.view().volume, node.view().number, logical).len()),
        None => true,
    },
{
    let number = node.number();
    let volume = node.volume();
    let block = match directory_file::read(node, logical) { Some(block) => block, None => { return None; } };
    let count = block.len();
    let ghost original = views(entries@);
    assert(model::block_entries(volume.view(), number, logical, 0) == Seq::<EntryView>::empty()) by { reveal(model::block_entries); }
    let mut i = 0usize;
    while i < count
        invariant node.wf(), volume.view() == node.view().volume, number == node.view().number,
            block.wf(), block.view().raw == directory_source::raw(volume.view(), number, logical),
            block.view().records == directory_source::records(volume.view(), number, logical),
            directory_source::valid_block(volume.view(), number, logical), i <= count <= 510, count == block.view().records.len(),
            model::entries_typed(volume.view(), views(entries@)), names.wf(), names.view().keys == model::keys(views(entries@)),
            views(entries@) == original + model::block_entries(volume.view(), number, logical, i as nat),
        decreases count - i,
    {
        let e = block.get(i).unwrap();
        if e.inode != 0 {
            let target = match allocated_inode::get(volume, e.inode) { Some(target) => target, None => { return None; } };
            let info = target.info();
            if (e.file_type == 1 && info.mode & 0xf000 != 0x8000)
                || (e.file_type == 2 && info.mode & 0xf000 != 0x4000) || (e.file_type != 1 && e.file_type != 2) { return None; }
            let name = block.name(i).unwrap();
            assert(name.len() <= 255);
            names = match names.insert(number, name) { Ok(next) => next, Err(_) => { return None; } };
            proof { allocated_inode::checked_view_is_the_source_projection(target.view()); }
            let next = capture(number, logical, i, e.inode, info.generation, e.file_type, name);
            assert(next.view() == model::entry(volume.view(), number, logical, i as int));
            assert(model::entry_ok(volume.view(), next.view())) by { reveal(allocated_inode::valid); reveal(directory_source::valid_block); }
            let ghost previous = views(entries@);
            let ghost value = next.view();
            proof { append_typed_entry(volume.view(), previous, value); }
            entries.push(next);
            assert(views(entries@) =~= previous.push(value));
            assert(model::keys(views(entries@)) =~= model::keys(previous).push((number, name@)));
        }
        assert(model::block_entries(volume.view(), number, logical, i as nat + 1) ==
            if e.inode == 0 { model::block_entries(volume.view(), number, logical, i as nat) }
            else { model::block_entries(volume.view(), number, logical, i as nat).push(model::entry(volume.view(), number, logical, i as int)) })
            by { reveal(model::block_entries); }
        i += 1;
    }
    Some((entries, names))
}

pub struct IndexView { pub volume: AllocationView, pub entries: Seq<EntryView>, pub names: name_set::SetView, pub blocks: u32 }

#[verifier::opaque]
pub open spec fn valid(v: IndexView) -> bool {
    &&& allocation::valid(v.volume) && model::directories_valid(v.volume, v.volume.index.inodes as nat)
    &&& v.entries == model::entries(v.volume, v.volume.index.inodes as nat)
    &&& model::entries_typed(v.volume, v.entries)
    &&& name_set::valid(v.names) && v.names.keys == model::keys(v.entries)
    &&& v.blocks as nat == model::total_blocks(v.volume, v.volume.index.inodes as nat) && v.blocks <= model::MAX_DIRECTORY_BLOCKS
}

pub struct DirectoryIndex<'v, 'a> { volume: &'v Allocation<'a>, entries: Vec<Entry>, names: NameSet, blocks: u32 }

impl<'v, 'a> DirectoryIndex<'v, 'a> {
    pub closed spec fn view(&self) -> IndexView {
        IndexView { volume: self.volume.view(), entries: views(self.entries@), names: self.names.view(), blocks: self.blocks }
    }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn volume(&self) -> (r: &'v Allocation<'a>) ensures self.wf(), r.view() == self.view().volume {
        proof { use_type_invariant(self); }
        self.volume
    }

    pub fn len(&self) -> (r: usize) ensures self.wf(), r == self.view().entries.len(), r <= name_set::MAX_KEYS {
        proof { use_type_invariant(self); reveal(valid); reveal(name_set::valid); }
        self.entries.len()
    }

    pub fn block_count(&self) -> (r: u32) ensures self.wf(), r == self.view().blocks, r <= model::MAX_DIRECTORY_BLOCKS {
        proof { use_type_invariant(self); reveal(valid); }
        self.blocks
    }

    pub fn get(&self, index: usize) -> (r: Option<&Entry>)
        ensures self.wf(), match r {
            Some(e) => index < self.view().entries.len() && e.view() == self.view().entries[index as int],
            None => index >= self.view().entries.len(),
        },
    {
        proof { use_type_invariant(self); }
        if index >= self.entries.len() { None } else { Some(&self.entries[index]) }
    }

    pub fn lookup(&self, directory: u32, name: &[u8]) -> (r: Option<&Entry>)
        ensures self.wf(), match r {
            Some(e) => self.view().entries.contains(e.view()) && e.view().directory == directory && e.view().name == name@
                && model::entry_ok(self.view().volume, e.view()),
            None => !model::has_name(self.view().entries, directory, name@),
        },
    {
        proof { use_type_invariant(self); reveal(valid); }
        match self.names.find(directory, name) {
            Some(index) => {
                let e = &self.entries[index as usize];
                assert(self.view().entries.contains(e.view())) by { assert(self.view().entries[index as int] == e.view()); }
                proof { reveal(model::entries_typed); }
                Some(e)
            },
            None => {
                assert(!model::has_name(self.view().entries, directory, name@)) by {
                    if model::has_name(self.view().entries, directory, name@) {
                        let i = choose|i: int| 0 <= i < self.view().entries.len() && (#[trigger] self.view().entries[i]).directory == directory
                            && self.view().entries[i].name == name@;
                        assert(self.names.view().keys[i] == (directory, name@));
                        assert(self.names.view().keys.contains((directory, name@)));
                    }
                }
                None
            }
        }
    }
}

pub fn build<'v, 'a>(volume: &'v Allocation<'a>) -> (r: Option<DirectoryIndex<'v, 'a>>)
    ensures volume.wf(), match r { Some(index) => index.wf() && index.view().volume == volume.view(), None => true },
{
    let (_, inodes, _, _) = volume.index().parameters();
    let mut entries = Vec::<Entry>::new();
    let mut names = NameSet::new();
    let mut blocks = 0u32;
    let mut completed = 0u32;
    assert(views(entries@) =~= Seq::<EntryView>::empty());
    assert(model::keys(views(entries@)) =~= Seq::<name_set::KeyView>::empty());
    assert(model::entries(volume.view(), 0) == Seq::<EntryView>::empty() && model::total_blocks(volume.view(), 0) == 0)
        by { reveal(model::entries); reveal(model::total_blocks); }
    assert(model::entries_typed(volume.view(), Seq::empty())) by { reveal(model::entries_typed); }
    assert(model::directories_valid(volume.view(), 0)) by { reveal(model::directories_valid); }
    while completed < inodes
        invariant volume.wf(), inodes == volume.view().index.inodes, completed <= inodes,
            views(entries@) == model::entries(volume.view(), completed as nat),
            names.wf(), names.view().keys == model::keys(views(entries@)), model::entries_typed(volume.view(), views(entries@)),
            blocks <= model::MAX_DIRECTORY_BLOCKS, blocks as nat == model::total_blocks(volume.view(), completed as nat),
            model::directories_valid(volume.view(), completed as nat),
        decreases inodes - completed,
    {
        let number = completed + 1;
        match allocated_inode::get(volume, number) {
            Some(node) => {
                proof { allocated_inode::checked_view_is_the_source_projection(node.view()); }
                let info = node.info();
                if info.mode & 0xf000 == 0x4000 {
                    assert(model::is_directory(volume.view(), number)) by { reveal(allocated_inode::valid); }
                    if info.size == 0 || info.size % 4096 != 0 { return None; }
                    let count = info.size / 4096;
                    if count > model::MAX_DIRECTORY_BLOCKS - blocks { return None; }
                    let ghost base = views(entries@);
                    let mut logical = 0u32;
                    assert(model::directory_entries(volume.view(), number, 0) == Seq::<EntryView>::empty()) by { reveal(model::directory_entries); }
                    assert(model::blocks_valid(volume.view(), number, 0)) by { reveal(model::blocks_valid); }
                    while logical < count
                        invariant volume.wf(), node.wf(), node.view().volume == volume.view(), node.view().number == number,
                            model::is_directory(volume.view(), number), logical <= count <= model::MAX_DIRECTORY_BLOCKS,
                            count > 0, allocated_inode::source_view(volume.view(), number).size as nat == count as nat * 4096,
                            count as nat == model::block_count(volume.view(), number),
                            base == model::entries(volume.view(), completed as nat),
                            model::directories_valid(volume.view(), completed as nat),
                            blocks <= model::MAX_DIRECTORY_BLOCKS, count <= model::MAX_DIRECTORY_BLOCKS - blocks,
                            blocks as nat == model::total_blocks(volume.view(), completed as nat),
                            views(entries@) == base + model::directory_entries(volume.view(), number, logical as nat),
                            names.wf(), names.view().keys == model::keys(views(entries@)), model::entries_typed(volume.view(), views(entries@)),
                            model::blocks_valid(volume.view(), number, logical as nat),
                        decreases count - logical,
                    {
                        let (next, next_names) = match append_block(&node, logical, entries, names) { Some(pair) => pair, None => { return None; } };
                        entries = next;
                        names = next_names;
                        assert(model::directory_entries(volume.view(), number, logical as nat + 1) == model::directory_entries(volume.view(), number, logical as nat)
                            + model::block_entries(volume.view(), number, logical, directory_source::records(volume.view(), number, logical).len()))
                            by { reveal(model::directory_entries); }
                        assert(model::blocks_valid(volume.view(), number, logical as nat + 1)) by {
                            reveal(model::blocks_valid);
                            assert forall|b: u32| b < logical as nat + 1 implies #[trigger] directory_source::valid_block(volume.view(), number, b) by {
                                if b < logical { assert(directory_source::valid_block(volume.view(), number, b)); }
                            }
                        }
                        logical += 1;
                    }
                    blocks += count;
                    assert(model::directory_valid(volume.view(), number));
                }
            },
            None => { assert(!model::is_directory(volume.view(), number)); }
        }
        proof {
            assert(model::entries(volume.view(), completed as nat + 1) == model::entries(volume.view(), completed as nat)
                + if model::is_directory(volume.view(), number) { model::directory_entries(volume.view(), number, model::block_count(volume.view(), number)) }
                    else { Seq::empty() }) by { reveal(model::entries); }
            assert(model::total_blocks(volume.view(), completed as nat + 1) == model::total_blocks(volume.view(), completed as nat)
                + if model::is_directory(volume.view(), number) { model::block_count(volume.view(), number) } else { 0nat }) by { reveal(model::total_blocks); }
            assert(model::directories_valid(volume.view(), completed as nat + 1)) by {
                reveal(model::directories_valid);
                assert forall|n: u32| 0 < n <= completed as nat + 1 && model::is_directory(volume.view(), n) implies
                    #[trigger] model::directory_valid(volume.view(), n) by {
                    if n <= completed { assert(model::directory_valid(volume.view(), n)); }
                }
            }
        }
        completed += 1;
    }
    let ghost assembled = IndexView { volume: volume.view(), entries: views(entries@), names: names.view(), blocks };
    assert(valid(assembled)) by { reveal(valid); }
    Some(DirectoryIndex { volume, entries, names, blocks })
}

}
