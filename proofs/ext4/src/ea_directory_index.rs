// SPDX-License-Identifier: MPL-2.0

//! Complete EA-enabled source directory enumeration and typed unique names.
//! Namespace links, parent topology, mount/recovery and runtime authority are
//! separate; this catalogue retains the actual EA-enabled allocation view.

use vstd::prelude::*;
use crate::{ea_allocation::{self, Allocation, AllocationView}, ea_directory::{self, Directory, DirectoryView},
    ea_namespace_nodes::{self as nodes, Nodes, TableView}, ea_ordinary,
    name_set::{self, NameSet}, namespace_model::{self as model, EntryView}};

verus! {

pub const MAX_DIRECTORY_BLOCKS: u32 = 4096;

pub struct Entry {
    directory: u32, logical: u32, record: usize, target: u32, generation: u32, file_type: u8, name: Vec<u8>,
}
impl Entry {
    pub closed spec fn view(&self) -> EntryView {
        EntryView { directory: self.directory, logical: self.logical, record: self.record,
            target: self.target, generation: self.generation, file_type: self.file_type, name: self.name@ }
    }
    pub fn identity(&self) -> (r: (u32, u32, u32, u8))
        ensures r == (self.view().directory, self.view().target, self.view().generation, self.view().file_type),
    { (self.directory, self.target, self.generation, self.file_type) }
    pub fn name(&self) -> (r: &[u8]) ensures r@ == self.view().name { &self.name }
    pub fn location(&self) -> (r: (u32, usize)) ensures r == (self.view().logical, self.view().record) {
        (self.logical, self.record)
    }
}
pub open spec fn views(entries: Seq<Entry>) -> Seq<EntryView> {
    Seq::new(entries.len(), |i: int| entries[i].view())
}
pub open spec fn directory_views(directories: Seq<Directory>) -> Seq<DirectoryView> {
    Seq::new(directories.len(), |i: int| directories[i].view())
}
pub open spec fn typed_node_entry(table: TableView, e: EntryView) -> bool {
    &&& nodes::is_directory(table, e.directory)
    &&& nodes::active(table, e.target)
    &&& e.generation == table.slots[e.target as int].generation
    &&& if e.file_type == 1 { table.slots[e.target as int].mode & 0xf000 == 0x8000 }
        else { e.file_type == 2 && table.slots[e.target as int].mode & 0xf000 == 0x4000 }
}
pub open spec fn typed_entries(table: TableView, entries: Seq<EntryView>) -> bool {
    forall|i: int| 0 <= i < entries.len() ==> #[trigger] typed_node_entry(table, entries[i])
}
pub open spec fn source_entry(table: TableView, directory: DirectoryView, logical: u32, record: int) -> EntryView {
    let piece = directory.pieces[logical as int]; let e = piece.block.records[record];
    EntryView { directory: ea_directory::owner(directory), logical, record: record as usize,
        target: e.inode, generation: table.slots[e.inode as int].generation, file_type: e.file_type,
        name: piece.block.raw.subrange(e.name_offset as int, e.name_offset as int + e.name_length as int) }
}
#[verifier::opaque]
pub open spec fn block_entries(table: TableView, directory: DirectoryView, logical: u32, count: nat) -> Seq<EntryView>
    decreases count,
{
    if count == 0 { Seq::empty() } else {
        let previous = block_entries(table, directory, logical, (count - 1) as nat);
        if directory.pieces[logical as int].block.records[count as int - 1].inode == 0 { previous }
        else { previous.push(source_entry(table, directory, logical, count as int - 1)) }
    }
}
#[verifier::opaque]
pub open spec fn directory_entries(table: TableView, directory: DirectoryView, count: nat) -> Seq<EntryView>
    decreases count,
{
    if count == 0 { Seq::empty() } else {
        directory_entries(table, directory, (count - 1) as nat)
            + block_entries(table, directory, (count - 1) as u32, directory.pieces[count as int - 1].block.records.len())
    }
}
pub open spec fn catalogue_directories(catalogue: Seq<Option<DirectoryView>>) -> Seq<DirectoryView>
    decreases catalogue.len(),
{
    if catalogue.len() == 0 { Seq::empty() } else {
        let previous = catalogue_directories(catalogue.drop_last());
        match catalogue.last() { Some(directory) => previous.push(directory), None => previous }
    }
}
pub open spec fn catalogue_entries(table: TableView, catalogue: Seq<Option<DirectoryView>>) -> Seq<EntryView>
    decreases catalogue.len(),
{
    if catalogue.len() == 0 { Seq::empty() } else {
        catalogue_entries(table, catalogue.drop_last()) + match catalogue.last() {
            Some(directory) => directory_entries(table, directory, directory.pieces.len()), None => Seq::empty() }
    }
}
pub open spec fn catalogue_blocks(catalogue: Seq<Option<DirectoryView>>) -> nat decreases catalogue.len() {
    if catalogue.len() == 0 { 0nat } else {
        catalogue_blocks(catalogue.drop_last()) + match catalogue.last() { Some(directory) => directory.pieces.len(), None => 0nat }
    }
}
#[verifier::opaque]
pub open spec fn catalogue_valid(volume: AllocationView, catalogue: Seq<Option<DirectoryView>>, count: nat) -> bool {
    catalogue.len() == count <= volume.ordinary.len()
        && forall|i: int| 0 <= i < count ==> match (#[trigger] catalogue[i]) {
            Some(directory) => ea_directory::valid(directory) && directory.volume == volume && directory.ordinal == i
                && ea_ordinary::directory(volume.ordinary[i].parent),
            None => !ea_ordinary::directory(volume.ordinary[i].parent),
        }
}

fn capture(directory: u32, logical: u32, record: usize, target: u32, generation: u32, file_type: u8, name: &[u8]) -> (r: Entry)
    requires name.len() <= 255,
    ensures r.view() == (EntryView { directory, logical, record, target, generation, file_type, name: name@ }),
{
    let mut copy = Vec::new(); let mut i = 0usize;
    while i < name.len()
        invariant i <= name.len() <= 255, copy@ == name@.take(i as int),
        decreases name.len() - i,
    { copy.push(name[i]); assert(copy@ =~= name@.take(i as int + 1)); i += 1; }
    assert(name@.take(i as int) =~= name@);
    Entry { directory, logical, record, target, generation, file_type, name: copy }
}
proof fn append_typed_entry(table: TableView, before: Seq<EntryView>, next: EntryView)
    requires typed_entries(table, before), typed_node_entry(table, next),
    ensures typed_entries(table, before.push(next)),
{
    assert forall|i: int| 0 <= i < before.len() + 1 implies #[trigger] typed_node_entry(table, before.push(next)[i]) by {
        if i < before.len() { assert(typed_node_entry(table, before[i])); }
    }
}

fn append_block(table: &Nodes, directory: &Directory<'_>, logical: u32, mut entries: Vec<Entry>, mut names: NameSet)
    -> (r: Option<(Vec<Entry>, NameSet)>)
    requires table.wf(), directory.wf(), directory.view().volume == table.view().volume,
        logical < directory.view().pieces.len(), typed_entries(table.view(), views(entries@)),
        names.wf(), names.view().keys == model::keys(views(entries@)),
    ensures table.wf(), directory.wf(), match r {
        Some((next, next_names)) => typed_entries(table.view(), views(next@)) && next_names.wf()
            && next_names.view().keys == model::keys(views(next@))
            && views(next@) == views(entries@) + block_entries(table.view(), directory.view(), logical,
                directory.view().pieces[logical as int].block.records.len()),
        None => true,
    },
{
    let number = directory.number();
    let source = match table.get(number) { Some(source) => source, None => { return None; } };
    if source.mode & 0xf000 != 0x4000 { return None; }
    let block = directory.piece(logical).unwrap(); let count = block.len(); let ghost original = views(entries@);
    assert(block_entries(table.view(), directory.view(), logical, 0) =~= Seq::<EntryView>::empty()) by { reveal(block_entries); }
    let mut i = 0usize;
    while i < count
        invariant table.wf(), nodes::valid(table.view()), directory.wf(), ea_directory::valid(directory.view()),
            directory.view().volume == table.view().volume, number == ea_directory::owner(directory.view()),
            nodes::is_directory(table.view(), number), block.wf(), logical < directory.view().pieces.len(),
            block.view() == directory.view().pieces[logical as int], count == block.view().block.records.len(), i <= count <= 510,
            typed_entries(table.view(), views(entries@)), names.wf(), names.view().keys == model::keys(views(entries@)),
            views(entries@) == original + block_entries(table.view(), directory.view(), logical, i as nat),
        decreases count - i,
    {
        let e = block.get(i).unwrap();
        if e.inode != 0 {
            let target = match table.get(e.inode) { Some(target) => target, None => { return None; } };
            if (e.file_type == 1 && target.mode & 0xf000 != 0x8000)
                || (e.file_type == 2 && target.mode & 0xf000 != 0x4000) || (e.file_type != 1 && e.file_type != 2) { return None; }
            let name = block.name(i).unwrap();
            names = match names.insert(number, name) { Ok(next) => next, Err(_) => { return None; } };
            let next = capture(number, logical, i, e.inode, target.generation, e.file_type, name);
            assert(next.view() == source_entry(table.view(), directory.view(), logical, i as int));
            assert(typed_node_entry(table.view(), next.view()));
            let ghost previous = views(entries@); let ghost value = next.view();
            proof { append_typed_entry(table.view(), previous, value); }
            entries.push(next);
            assert(views(entries@) =~= previous.push(value));
            assert(model::keys(views(entries@)) =~= model::keys(previous).push((number, name@)));
        }
        assert(block_entries(table.view(), directory.view(), logical, i as nat + 1) ==
            if e.inode == 0 { block_entries(table.view(), directory.view(), logical, i as nat) }
            else { block_entries(table.view(), directory.view(), logical, i as nat).push(source_entry(table.view(), directory.view(), logical, i as int)) })
            by { reveal(block_entries); }
        i += 1;
    }
    Some((entries, names))
}

pub struct IndexView {
    pub volume: AllocationView, pub nodes: TableView, pub catalogue: Seq<Option<DirectoryView>>,
    pub directories: Seq<DirectoryView>, pub entries: Seq<EntryView>, pub names: name_set::SetView, pub blocks: u32,
}
pub open spec fn entry_ok(index: IndexView, e: EntryView) -> bool { typed_node_entry(index.nodes, e) }
pub open spec fn entries_typed(index: IndexView) -> bool { typed_entries(index.nodes, index.entries) }
#[verifier::opaque]
pub open spec fn valid(v: IndexView) -> bool {
    &&& ea_allocation::valid(v.volume) && nodes::valid(v.nodes) && v.nodes.volume == v.volume
    &&& catalogue_valid(v.volume, v.catalogue, v.volume.ordinary.len())
    &&& v.directories == catalogue_directories(v.catalogue)
    &&& v.entries == catalogue_entries(v.nodes, v.catalogue) && entries_typed(v)
    &&& name_set::valid(v.names) && v.names.keys == model::keys(v.entries)
    &&& v.blocks as nat == catalogue_blocks(v.catalogue) && v.blocks <= MAX_DIRECTORY_BLOCKS
}

pub struct DirectoryIndex<'a> {
    nodes: Nodes, directories: Vec<Directory<'a>>, entries: Vec<Entry>, names: NameSet, blocks: u32,
    checked: Ghost<IndexView>,
}
impl<'a> DirectoryIndex<'a> {
    pub closed spec fn view(&self) -> IndexView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        valid(self.view()) && self.nodes.view() == self.view().nodes
            && directory_views(self.directories@) == self.view().directories && views(self.entries@) == self.view().entries
            && self.names.view() == self.view().names && self.blocks == self.view().blocks
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn nodes(&self) -> (r: &Nodes)
        ensures self.wf(), valid(self.view()), r.wf(), nodes::valid(r.view()), r.view() == self.view().nodes,
    { proof { use_type_invariant(self); } let _ = self.nodes.len(); &self.nodes }
    pub fn len(&self) -> (r: usize)
        ensures self.wf(), valid(self.view()), r == self.view().entries.len(), r <= name_set::MAX_KEYS,
    { proof { use_type_invariant(self); reveal(valid); reveal(name_set::valid); } self.entries.len() }
    pub fn block_count(&self) -> (r: u32)
        ensures self.wf(), valid(self.view()), r == self.view().blocks, r <= MAX_DIRECTORY_BLOCKS,
    { proof { use_type_invariant(self); reveal(valid); } self.blocks }
    pub fn directory_count(&self) -> (r: usize)
        ensures self.wf(), valid(self.view()), r == self.view().directories.len(),
    { proof { use_type_invariant(self); } self.directories.len() }
    pub fn directory(&self, index: usize) -> (r: Option<&Directory<'a>>)
        ensures self.wf(), valid(self.view()), match r { Some(directory) => index < self.view().directories.len()
            && directory.wf() && ea_directory::valid(directory.view()) && directory.view() == self.view().directories[index as int],
            None => index >= self.view().directories.len() },
    {
        proof { use_type_invariant(self); }
        if index >= self.directories.len() { return None; }
        let directory = &self.directories[index]; let _ = directory.block_count(); Some(directory)
    }
    pub fn get(&self, index: usize) -> (r: Option<&Entry>)
        ensures self.wf(), valid(self.view()), match r { Some(e) => index < self.view().entries.len()
            && e.view() == self.view().entries[index as int] && entry_ok(self.view(), e.view()),
            None => index >= self.view().entries.len() },
    {
        proof { use_type_invariant(self); }
        if index >= self.entries.len() { return None; }
        proof { reveal(valid); assert(typed_node_entry(self.view().nodes, self.view().entries[index as int])); }
        Some(&self.entries[index])
    }
    pub fn lookup(&self, directory: u32, name: &[u8]) -> (r: Option<&Entry>)
        ensures self.wf(), valid(self.view()), match r {
            Some(e) => self.view().entries.contains(e.view()) && e.view().directory == directory && e.view().name == name@ && entry_ok(self.view(), e.view()),
            None => !model::has_name(self.view().entries, directory, name@) && !source_has_name(self.view(), directory, name@),
        },
    {
        proof { use_type_invariant(self); reveal(valid); }
        match self.names.find(directory, name) {
            Some(index) => {
                let e = &self.entries[index as usize];
                assert(self.view().entries.contains(e.view())) by { assert(self.view().entries[index as int] == e.view()); }
                assert(typed_node_entry(self.view().nodes, e.view())); Some(e)
            },
            None => {
                assert(!model::has_name(self.view().entries, directory, name@)) by {
                    if model::has_name(self.view().entries, directory, name@) {
                        let i = choose|i: int| 0 <= i < self.view().entries.len() && (#[trigger] self.view().entries[i]).directory == directory && self.view().entries[i].name == name@;
                        assert(self.names.view().keys[i] == (directory, name@));
                        assert(self.names.view().keys.contains((directory, name@)));
                    }
                }
                proof { no_catalogue_name_means_no_live_source_name(self.view(), directory, name@); }
                None
            },
        }
    }
}

pub fn build<'a>(volume: &Allocation<'_, 'a>) -> (r: Option<DirectoryIndex<'a>>)
    ensures volume.wf(), ea_allocation::valid(volume.view()), match r {
        Some(index) => index.wf() && valid(index.view()) && index.view().volume == volume.view(), None => true },
{
    let _ = volume.ordinary_count();
    let nodes = match nodes::build(volume) { Some(nodes) => nodes, None => { return None; } };
    let mut entries = Vec::<Entry>::new(); let mut names = NameSet::new();
    let mut directories = Vec::<Directory<'a>>::new(); let mut blocks = 0u32; let mut completed = 0usize;
    let count = volume.ordinary_count(); let ghost mut catalogue: Seq<Option<DirectoryView>> = Seq::empty();
    assert(views(entries@) =~= Seq::<EntryView>::empty());
    assert(directory_views(directories@) =~= Seq::<DirectoryView>::empty());
    assert(model::keys(views(entries@)) =~= Seq::<name_set::KeyView>::empty());
    assert(catalogue_valid(volume.view(), catalogue, 0)) by { reveal(catalogue_valid); }
    assert(typed_entries(nodes.view(), views(entries@)));
    while completed < count
        invariant volume.wf(), ea_allocation::valid(volume.view()), count == volume.view().ordinary.len(), completed <= count,
            nodes.wf(), nodes::valid(nodes.view()), nodes.view().volume == volume.view(),
            names.wf(), names.view().keys == model::keys(views(entries@)), typed_entries(nodes.view(), views(entries@)),
            catalogue.len() == completed, catalogue_valid(volume.view(), catalogue, completed as nat),
            directory_views(directories@) == catalogue_directories(catalogue), views(entries@) == catalogue_entries(nodes.view(), catalogue),
            blocks as nat == catalogue_blocks(catalogue), blocks <= MAX_DIRECTORY_BLOCKS,
        decreases count - completed,
    {
        let ordinary = volume.ordinary(completed).unwrap(); let directory = ordinary.is_directory();
        let ghost previous_catalogue = catalogue; let ghost mut item: Option<DirectoryView> = None;
        if directory {
            let source = match ea_directory::inspect(volume, completed) { Some(source) => source, None => { return None; } };
            let number_of_blocks = source.block_count();
            if number_of_blocks > MAX_DIRECTORY_BLOCKS - blocks { return None; }
            let ghost base = views(entries@); let mut logical = 0u32;
            assert(directory_entries(nodes.view(), source.view(), 0) =~= Seq::<EntryView>::empty()) by { reveal(directory_entries); }
            while logical < number_of_blocks
                invariant volume.wf(), ea_allocation::valid(volume.view()), source.wf(), ea_directory::valid(source.view()), source.view().volume == volume.view(), source.view().ordinal == completed,
                    nodes.wf(), nodes::valid(nodes.view()), nodes.view().volume == volume.view(), logical <= number_of_blocks <= MAX_DIRECTORY_BLOCKS,
                    number_of_blocks as nat == source.view().pieces.len(), blocks <= MAX_DIRECTORY_BLOCKS,
                    number_of_blocks <= MAX_DIRECTORY_BLOCKS - blocks,
                    names.wf(), names.view().keys == model::keys(views(entries@)), typed_entries(nodes.view(), views(entries@)),
                    views(entries@) == base + directory_entries(nodes.view(), source.view(), logical as nat),
                decreases number_of_blocks - logical,
            {
                let (next, next_names) = match append_block(&nodes, &source, logical, entries, names) { Some(pair) => pair, None => { return None; } };
                entries = next; names = next_names;
                assert(directory_entries(nodes.view(), source.view(), logical as nat + 1)
                    == directory_entries(nodes.view(), source.view(), logical as nat)
                        + block_entries(nodes.view(), source.view(), logical, source.view().pieces[logical as int].block.records.len())) by { reveal(directory_entries); }
                logical += 1;
            }
            blocks += number_of_blocks;
            proof { item = Some(source.view()); }
            let ghost old = directory_views(directories@); directories.push(source);
            assert(directory_views(directories@) =~= old.push(item.unwrap()));
        }
        proof { catalogue = catalogue.push(item); }
        assert(catalogue.drop_last() =~= previous_catalogue); assert(catalogue.last() == item);
        assert(directory_views(directories@) == catalogue_directories(catalogue));
        assert(views(entries@) == catalogue_entries(nodes.view(), catalogue));
        assert(blocks as nat == catalogue_blocks(catalogue));
        assert(catalogue_valid(volume.view(), catalogue, completed as nat + 1)) by {
            reveal(catalogue_valid);
            assert forall|i: int| 0 <= i < completed + 1 implies match (#[trigger] catalogue[i]) {
                Some(directory) => ea_directory::valid(directory) && directory.volume == volume.view() && directory.ordinal == i
                    && ea_ordinary::directory(volume.view().ordinary[i].parent),
                None => !ea_ordinary::directory(volume.view().ordinary[i].parent),
            } by { if i < completed { assert(catalogue[i] == previous_catalogue[i]); } }
        }
        completed += 1;
    }
    let ghost view = IndexView { volume: volume.view(), nodes: nodes.view(), catalogue,
        directories: directory_views(directories@), entries: views(entries@), names: names.view(), blocks };
    assert(valid(view)) by { reveal(valid); }
    Some(DirectoryIndex { nodes, directories, entries, names, blocks, checked: Ghost(view) })
}

pub proof fn every_ordinary_directory_has_exactly_its_source_catalogue_slot(v: IndexView, ordinal: int)
    requires valid(v), 0 <= ordinal < v.volume.ordinary.len(),
    ensures match v.catalogue[ordinal] { Some(directory) => ea_directory::valid(directory) && directory.volume == v.volume && directory.ordinal == ordinal
        && ea_ordinary::directory(v.volume.ordinary[ordinal].parent), None => !ea_ordinary::directory(v.volume.ordinary[ordinal].parent) },
{ reveal(valid); reveal(catalogue_valid); }
pub proof fn every_named_target_is_an_actual_ordinary_source_inode(v: IndexView, index: int)
    requires valid(v), 0 <= index < v.entries.len(),
    ensures entry_ok(v, v.entries[index]),
{ reveal(valid); assert(typed_node_entry(v.nodes, v.entries[index])); }
pub proof fn full_namespace_keys_are_unique_without_a_hash_identity_assumption(v: IndexView)
    requires valid(v),
    ensures model::keys(v.entries).no_duplicates(),
{ reveal(valid); reveal(name_set::valid); }
pub proof fn namespace_entry_enumeration_is_the_complete_source_record_projection(v: IndexView)
    requires valid(v),
    ensures v.entries == catalogue_entries(v.nodes, v.catalogue), v.directories == catalogue_directories(v.catalogue),
{ reveal(valid); }

proof fn concatenated_membership_left(a: Seq<EntryView>, b: Seq<EntryView>, e: EntryView)
    requires a.contains(e), ensures (a + b).contains(e),
{
    let i = choose|i: int| 0 <= i < a.len() && #[trigger] a[i] == e;
    assert((a + b)[i] == e);
    assert(exists|j: int| 0 <= j < (a + b).len() && #[trigger] (a + b)[j] == e);
}
proof fn concatenated_membership_right(a: Seq<EntryView>, b: Seq<EntryView>, e: EntryView)
    requires b.contains(e), ensures (a + b).contains(e),
{
    let i = choose|i: int| 0 <= i < b.len() && #[trigger] b[i] == e;
    assert((a + b)[a.len() as int + i] == e);
    assert(exists|j: int| 0 <= j < (a + b).len() && #[trigger] (a + b)[j] == e);
}
proof fn every_live_block_record_is_in_the_block_projection(table: TableView, directory: DirectoryView, logical: u32, count: nat, record: int)
    requires logical < directory.pieces.len(), 0 <= record < count <= directory.pieces[logical as int].block.records.len(),
        directory.pieces[logical as int].block.records[record].inode != 0,
    ensures block_entries(table, directory, logical, count).contains(source_entry(table, directory, logical, record)),
    decreases count,
{
    reveal(block_entries);
    let previous = block_entries(table, directory, logical, (count - 1) as nat);
    let e = source_entry(table, directory, logical, record);
    if record < count - 1 {
        every_live_block_record_is_in_the_block_projection(table, directory, logical, (count - 1) as nat, record);
        let i = choose|i: int| 0 <= i < previous.len() && #[trigger] previous[i] == e;
        if directory.pieces[logical as int].block.records[count as int - 1].inode != 0 {
            assert(block_entries(table, directory, logical, count)[i] == e);
        }
        assert(exists|j: int| 0 <= j < block_entries(table, directory, logical, count).len() && #[trigger] block_entries(table, directory, logical, count)[j] == e);
    } else {
        assert(record == count - 1);
        assert(block_entries(table, directory, logical, count) == previous.push(e));
        assert(block_entries(table, directory, logical, count)[previous.len() as int] == e);
        assert(exists|j: int| 0 <= j < block_entries(table, directory, logical, count).len() && #[trigger] block_entries(table, directory, logical, count)[j] == e);
    }
    assert(block_entries(table, directory, logical, count).contains(e));
}
proof fn every_live_directory_record_is_in_the_directory_projection(table: TableView, directory: DirectoryView, count: nat, logical: u32, record: int)
    requires logical < count <= directory.pieces.len(),
        0 <= record < directory.pieces[logical as int].block.records.len(),
        directory.pieces[logical as int].block.records[record].inode != 0,
    ensures directory_entries(table, directory, count).contains(source_entry(table, directory, logical, record)),
    decreases count,
{
    reveal(directory_entries);
    let previous = directory_entries(table, directory, (count - 1) as nat);
    let last = block_entries(table, directory, (count - 1) as u32, directory.pieces[count as int - 1].block.records.len());
    let e = source_entry(table, directory, logical, record);
    if logical < count - 1 {
        every_live_directory_record_is_in_the_directory_projection(table, directory, (count - 1) as nat, logical, record);
        concatenated_membership_left(previous, last, e);
    } else {
        assert(logical as nat == count - 1);
        every_live_block_record_is_in_the_block_projection(table, directory, logical, directory.pieces[logical as int].block.records.len(), record);
        concatenated_membership_right(previous, last, e);
    }
}
proof fn every_live_catalogue_record_is_in_the_complete_projection(table: TableView, catalogue: Seq<Option<DirectoryView>>,
    ordinal: int, directory: DirectoryView, logical: u32, record: int)
    requires 0 <= ordinal < catalogue.len(), catalogue[ordinal] == Some(directory),
        logical < directory.pieces.len(), 0 <= record < directory.pieces[logical as int].block.records.len(),
        directory.pieces[logical as int].block.records[record].inode != 0,
    ensures catalogue_entries(table, catalogue).contains(source_entry(table, directory, logical, record)),
    decreases catalogue.len(),
{
    let previous = catalogue.drop_last(); let e = source_entry(table, directory, logical, record);
    if ordinal < previous.len() {
        assert(previous[ordinal] == Some(directory));
        every_live_catalogue_record_is_in_the_complete_projection(table, previous, ordinal, directory, logical, record);
        match catalogue.last() {
            Some(last) => concatenated_membership_left(catalogue_entries(table, previous), directory_entries(table, last, last.pieces.len()), e),
            None => { },
        }
    } else {
        assert(ordinal == catalogue.len() - 1 && catalogue.last() == Some(directory));
        every_live_directory_record_is_in_the_directory_projection(table, directory, directory.pieces.len(), logical, record);
        concatenated_membership_right(catalogue_entries(table, previous), directory_entries(table, directory, directory.pieces.len()), e);
    }
    assert(catalogue_entries(table, catalogue).contains(e));
}

pub open spec fn live_source_location(v: IndexView, ordinal: int, logical: u32, record: int) -> bool {
    0 <= ordinal < v.catalogue.len() && v.catalogue[ordinal].is_some() && {
        let directory = v.catalogue[ordinal].unwrap();
        logical < directory.pieces.len() && 0 <= record < directory.pieces[logical as int].block.records.len()
            && directory.pieces[logical as int].block.records[record].inode != 0
    }
}
pub open spec fn source_has_name(v: IndexView, directory: u32, name: Seq<u8>) -> bool {
    exists|w: (int, u32, int)| #[trigger] live_source_location(v, w.0, w.1, w.2)
        && source_entry(v.nodes, v.catalogue[w.0].unwrap(), w.1, w.2).directory == directory
        && source_entry(v.nodes, v.catalogue[w.0].unwrap(), w.1, w.2).name == name
}
pub proof fn every_live_source_record_appears_in_namespace_catalogue(v: IndexView, ordinal: int, logical: u32, record: int)
    requires valid(v), live_source_location(v, ordinal, logical, record),
    ensures v.entries.contains(source_entry(v.nodes, v.catalogue[ordinal].unwrap(), logical, record)),
{
    reveal(valid);
    every_live_catalogue_record_is_in_the_complete_projection(v.nodes, v.catalogue, ordinal, v.catalogue[ordinal].unwrap(), logical, record);
}
pub proof fn no_catalogue_name_means_no_live_source_name(v: IndexView, directory: u32, name: Seq<u8>)
    requires valid(v), !model::has_name(v.entries, directory, name),
    ensures !source_has_name(v, directory, name),
{
    if source_has_name(v, directory, name) {
        let w = choose|w: (int, u32, int)| #[trigger] live_source_location(v, w.0, w.1, w.2)
            && source_entry(v.nodes, v.catalogue[w.0].unwrap(), w.1, w.2).directory == directory
            && source_entry(v.nodes, v.catalogue[w.0].unwrap(), w.1, w.2).name == name;
        every_live_source_record_appears_in_namespace_catalogue(v, w.0, w.1, w.2);
        let e = source_entry(v.nodes, v.catalogue[w.0].unwrap(), w.1, w.2);
        let i = choose|i: int| 0 <= i < v.entries.len() && #[trigger] v.entries[i] == e;
        assert(exists|j: int| 0 <= j < v.entries.len() && (#[trigger] v.entries[j]).directory == directory && v.entries[j].name == name);
        assert(model::has_name(v.entries, directory, name));
    }
}

}
