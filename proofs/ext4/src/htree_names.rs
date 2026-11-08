// SPDX-License-Identifier: MPL-2.0

//! Complete source-bound HTree name enumeration, hash-range validation and
//! full-key lookup. Target allocation/VFS authority and physical source binding
//! are separate from the supplied immutable logical-block snapshot.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, dir_hash::{self, State}, directory_block::{self, DirectoryBlock}, htree::{self, Index},
    htree_range::{self as range, Bounds}, htree_topology::{self as topology, Graph, GraphView}, name_set::{self, NameSet}};

verus! {

pub struct Parameters { pub tree: topology::Context, pub hash_seed: State, pub version: u8 }
pub open spec fn parameters_valid(p: Parameters) -> bool {
    topology::geometry(p.tree) && p.tree.source[0][28] <= 2 && p.version <= 5
        && (p.version == p.tree.source[0][28] || p.version as nat == p.tree.source[0][28] as nat + 3)
}
pub open spec fn owner(p: Parameters) -> u32 { bytes::le32(p.tree.source[0], 0) as u32 }
pub struct EntryView { pub logical: u32, pub record: usize, pub target: u32, pub file_type: u8, pub name: Seq<u8> }
pub open spec fn records(p: Parameters, logical: u32) -> Seq<crate::directory::Entry> {
    directory_block::canonical_records(p.tree.source[logical as int], p.tree.inodes)
}
pub open spec fn entry(p: Parameters, logical: u32, record: int) -> EntryView {
    let r = records(p, logical)[record];
    EntryView { logical, record: record as usize, target: r.inode, file_type: r.file_type,
        name: p.tree.source[logical as int].subrange(r.name_offset as int, r.name_offset as int + r.name_length as int) }
}
pub open spec fn root_entry(p: Parameters, i: usize) -> EntryView {
    EntryView { logical: 0, record: i, target: bytes::le32(p.tree.source[0], if i == 0 { 0int } else { 12int }) as u32,
        file_type: 2, name: if i == 0 { p.tree.source[0].subrange(8, 9) } else { p.tree.source[0].subrange(20, 22) } }
}
pub open spec fn root_entries(p: Parameters) -> Seq<EntryView> { seq![root_entry(p, 0), root_entry(p, 1)] }
#[verifier::opaque]
pub open spec fn block_entries(p: Parameters, logical: u32, length: nat) -> Seq<EntryView> decreases length {
    if length == 0 { Seq::empty() } else {
        let before = block_entries(p, logical, (length - 1) as nat);
        if records(p, logical)[length as int - 1].inode == 0 { before } else { before.push(entry(p, logical, length as int - 1)) }
    }
}
#[verifier::opaque]
pub open spec fn tree_entries(p: Parameters, number: u32, depth: u8, length: nat) -> Seq<EntryView>
    decreases depth, length,
{
    if length == 0 { Seq::empty() } else {
        let target = topology::child(p.tree, number, (length - 1) as nat);
        tree_entries(p, number, depth, (length - 1) as nat) + if depth == 0 { block_entries(p, target, records(p, target).len()) }
            else { tree_entries(p, target, (depth - 1) as u8, topology::count(p.tree, target)) }
    }
}
pub open spec fn keys(p: Parameters, entries: Seq<EntryView>) -> Seq<name_set::KeyView> { Seq::new(entries.len(), |i: int| (owner(p), entries[i].name)) }
pub open spec fn source_record(p: Parameters, e: EntryView) -> bool {
    if e.logical == 0 { e == root_entry(p, 0) || e == root_entry(p, 1) }
    else { e.logical < p.tree.source.len() && topology::leaf(p.tree, e.logical)
        && e.record < records(p, e.logical).len() && records(p, e.logical)[e.record as int].inode != 0 && e == entry(p, e.logical, e.record as int) }
}
#[verifier::opaque]
pub open spec fn entries_valid(p: Parameters, entries: Seq<EntryView>) -> bool {
    forall|i: int| 0 <= i < entries.len() ==> #[trigger] source_record(p, entries[i])
}
#[verifier::opaque]
pub open spec fn leaf_hashes(p: Parameters, logical: u32, bounds: Bounds, length: nat) -> bool decreases length {
    if length == 0 { true } else { leaf_hashes(p, logical, bounds, (length - 1) as nat)
        && (records(p, logical)[length as int - 1].inode != 0 ==> range::contains(bounds,
            dir_hash::value(entry(p, logical, length as int - 1).name, p.hash_seed, p.version).major)) }
}
#[verifier::opaque]
pub open spec fn ranges(p: Parameters, number: u32, depth: u8, bounds: Bounds, length: nat) -> bool
    decreases depth, length,
{
    if length == 0 { topology::subtree(p.tree, number, depth) && range::valid(bounds) && parameters_valid(p) }
    else {
        let i = (length - 1) as nat;
        let target = topology::child(p.tree, number, i);
        let next = range::child(topology::index_view(p.tree, number), bounds, i);
        ranges(p, number, depth, bounds, i) && range::fits(bounds, next)
            && if depth == 0 { leaf_hashes(p, target, next, records(p, target).len()) }
                else { ranges(p, target, (depth - 1) as u8, next, topology::count(p.tree, target)) }
    }
}

pub struct Entry<'a> { logical: u32, record: usize, target: u32, file_type: u8, name: &'a [u8] }
impl<'a> Entry<'a> {
    pub closed spec fn view(&self) -> EntryView { EntryView { logical: self.logical, record: self.record, target: self.target, file_type: self.file_type, name: self.name@ } }
    pub fn identity(&self) -> (r: (u32, usize, u32, u8)) ensures r == (self.view().logical, self.view().record, self.view().target, self.view().file_type) {
        (self.logical, self.record, self.target, self.file_type)
    }
    pub fn name_bytes(&self) -> (r: &'a [u8]) ensures r@ == self.view().name { self.name }
}
pub open spec fn views(entries: Seq<Entry>) -> Seq<EntryView> { Seq::new(entries.len(), |i: int| entries[i].view()) }
fn capture<'a>(logical: u32, record: usize, target: u32, file_type: u8, name: &'a [u8]) -> (r: Entry<'a>)
    ensures r.view() == (EntryView { logical, record, target, file_type, name: name@ }),
{ Entry { logical, record, target, file_type, name } }
proof fn append_entry(p: Parameters, before: Seq<EntryView>, e: EntryView)
    requires entries_valid(p, before), source_record(p, e), ensures entries_valid(p, before.push(e)),
{
    reveal(entries_valid);
    assert forall|i: int| 0 <= i < before.push(e).len() implies #[trigger] source_record(p, before.push(e)[i]) by {
        if i < before.len() { assert(source_record(p, before[i])); }
    }
}

fn append_leaf<'a>(raw: &'a [u8], logical: u32, bounds: Bounds, inodes: u32, seed: u32, hash_seed: State, version: u8, directory: u32,
    mut entries: Vec<Entry<'a>>, mut names: NameSet, Ghost(p): Ghost<Parameters>) -> (r: Option<(Vec<Entry<'a>>, NameSet)>)
    requires parameters_valid(p), p.tree.inodes == inodes, p.tree.seed == seed, p.hash_seed == hash_seed, p.version == version, directory == owner(p),
        0 < logical < p.tree.source.len(), raw@ == p.tree.source[logical as int], topology::leaf(p.tree, logical), range::valid(bounds),
        entries_valid(p, views(entries@)), names.wf(), names.view().keys == keys(p, views(entries@)),
    ensures match r { Some((next, index)) => entries_valid(p, views(next@)) && index.wf() && index.view().keys == keys(p, views(next@))
        && views(next@) == views(entries@) + block_entries(p, logical, records(p, logical).len())
        && leaf_hashes(p, logical, bounds, records(p, logical).len()), None => true },
{
    hide(dir_hash::value);
    let block = match directory_block::parse(raw, inodes, seed) { Some(block) => block, None => { return None; } };
    proof { directory_block::checked_block_has_canonical_records(block.view()); }
    let count = block.len();
    let ghost original = views(entries@);
    let mut i = 0usize;
    assert(block_entries(p, logical, 0) == Seq::<EntryView>::empty()) by { reveal(block_entries); }
    assert(leaf_hashes(p, logical, bounds, 0)) by { reveal(leaf_hashes); }
    while i < count
        invariant parameters_valid(p), p.tree.inodes == inodes, p.tree.seed == seed, p.hash_seed == hash_seed, p.version == version, directory == owner(p),
            0 < logical < p.tree.source.len(), raw@ == p.tree.source[logical as int], topology::leaf(p.tree, logical), range::valid(bounds),
            block.wf(), block.view().raw == raw@, block.view().inodes == inodes, block.view().records == records(p, logical),
            i <= count <= 510, count == block.view().records.len(),
            entries_valid(p, views(entries@)), names.wf(), names.view().keys == keys(p, views(entries@)),
            views(entries@) == original + block_entries(p, logical, i as nat), leaf_hashes(p, logical, bounds, i as nat),
        decreases count - i,
    {
        let e = block.get(i).unwrap();
        if e.inode != 0 {
            let name = block.name(i).unwrap();
            assert(name.len() <= 255);
            let hash = dir_hash::calculate(name, hash_seed, version).unwrap();
            if !range::includes(&bounds, hash.major) { return None; }
            names = match names.insert(directory, name) { Ok(next) => next, Err(_) => { return None; } };
            let next = capture(logical, i, e.inode, e.file_type, name);
            assert(next.view() == entry(p, logical, i as int));
            let ghost before = views(entries@);
            let ghost value = next.view();
            proof { append_entry(p, before, value); }
            entries.push(next);
            assert(views(entries@) =~= before.push(value));
            assert(keys(p, views(entries@)) =~= keys(p, before).push((directory, name@)));
        }
        assert(block_entries(p, logical, i as nat + 1) == if e.inode == 0 { block_entries(p, logical, i as nat) }
            else { block_entries(p, logical, i as nat).push(entry(p, logical, i as int)) }) by { reveal(block_entries); }
        assert(leaf_hashes(p, logical, bounds, i as nat + 1)) by { reveal(leaf_hashes); }
        i += 1;
    }
    Some((entries, names))
}

fn collect<'a>(blocks: &[&'a [u8]], index: &Index<'a>, number: u32, depth: u8, bounds: Bounds,
    inodes: u32, seed: u32, hash_seed: State, version: u8, directory: u32,
    mut entries: Vec<Entry<'a>>, mut names: NameSet, Ghost(p): Ghost<Parameters>) -> (r: Option<(Vec<Entry<'a>>, NameSet)>)
    requires parameters_valid(p), p.tree.source == topology::source_views(blocks@), p.tree.inodes == inodes, p.tree.seed == seed,
        p.hash_seed == hash_seed, p.version == version, directory == owner(p), depth <= 2, number < p.tree.source.len(),
        index.wf(), index.view() == topology::index_view(p.tree, number), topology::subtree(p.tree, number, depth), range::valid(bounds),
        entries_valid(p, views(entries@)), names.wf(), names.view().keys == keys(p, views(entries@)),
    ensures index.wf(), match r { Some((next, set)) => entries_valid(p, views(next@)) && set.wf() && set.view().keys == keys(p, views(next@))
        && views(next@) == views(entries@) + tree_entries(p, number, depth, topology::count(p.tree, number))
        && ranges(p, number, depth, bounds, topology::count(p.tree, number)), None => true },
    decreases depth,
{
    let count = index.child_count();
    let ghost original = views(entries@);
    let mut i = 0usize;
    assert(tree_entries(p, number, depth, 0) == Seq::<EntryView>::empty()) by { reveal(tree_entries); }
    assert(ranges(p, number, depth, bounds, 0)) by { reveal(ranges); }
    while i < count
        invariant parameters_valid(p), p.tree.source == topology::source_views(blocks@), p.tree.inodes == inodes, p.tree.seed == seed,
            p.hash_seed == hash_seed, p.version == version, directory == owner(p), depth <= 2, number < p.tree.source.len(),
            index.wf(), index.view() == topology::index_view(p.tree, number), topology::subtree(p.tree, number, depth), range::valid(bounds),
            i <= count == topology::count(p.tree, number), entries_valid(p, views(entries@)), names.wf(), names.view().keys == keys(p, views(entries@)),
            views(entries@) == original + tree_entries(p, number, depth, i as nat), ranges(p, number, depth, bounds, i as nat),
        decreases count - i,
    {
        let e = index.child(i).unwrap();
        let next_bounds = match range::subdivide(index, &bounds, i) { Some(next) => next, None => { return None; } };
        proof { topology::a_checked_node_retains_its_header_and_every_source_child(p.tree, number, depth, i as nat); }
        let pair = if depth == 0 {
            append_leaf(blocks[e.block as usize], e.block, next_bounds, inodes, seed, hash_seed, version, directory, entries, names, Ghost(p))
        } else {
            let nested = match htree::parse_node(blocks[e.block as usize], blocks.len() as u32, seed, true) { Some(nested) => nested, None => { return None; } };
            collect(blocks, &nested, e.block, depth - 1, next_bounds, inodes, seed, hash_seed, version, directory, entries, names, Ghost(p))
        };
        let (next, set) = match pair { Some(pair) => pair, None => { return None; } };
        entries = next; names = set;
        assert(tree_entries(p, number, depth, i as nat + 1) == tree_entries(p, number, depth, i as nat)
            + if depth == 0 { block_entries(p, e.block, records(p, e.block).len()) }
                else { tree_entries(p, e.block, (depth - 1) as u8, topology::count(p.tree, e.block)) }) by { reveal(tree_entries); }
        assert(ranges(p, number, depth, bounds, i as nat + 1)) by { reveal(ranges); }
        i += 1;
    }
    Some((entries, names))
}

pub struct DirectoryView { pub graph: GraphView, pub entries: Seq<EntryView>, pub names: name_set::SetView, pub hash_seed: State, pub version: u8 }
pub open spec fn parameters(v: DirectoryView) -> Parameters { Parameters { tree: v.graph.context, hash_seed: v.hash_seed, version: v.version } }
#[verifier::opaque]
pub open spec fn valid(v: DirectoryView) -> bool {
    let p = parameters(v);
    &&& topology::valid(v.graph) && parameters_valid(p)
    &&& v.entries == root_entries(p) + tree_entries(p, 0, v.graph.depth, topology::count(p.tree, 0)) && entries_valid(p, v.entries)
    &&& name_set::valid(v.names) && v.names.keys == keys(p, v.entries)
    &&& ranges(p, 0, v.graph.depth, Bounds { lower: 0, upper: 4294967296, inclusive: false }, topology::count(p.tree, 0))
}
pub open spec fn has_name(entries: Seq<EntryView>, name: Seq<u8>) -> bool { exists|i: int| 0 <= i < entries.len() && (#[trigger] entries[i]).name == name }
pub struct Directory<'a> { graph: Graph<'a>, entries: Vec<Entry<'a>>, names: NameSet, hash_seed: State, version: u8, owner: u32 }
impl<'a> Directory<'a> {
    pub closed spec fn view(&self) -> DirectoryView { DirectoryView { graph: self.graph.view(), entries: views(self.entries@), names: self.names.view(), hash_seed: self.hash_seed, version: self.version } }
    pub closed spec fn stored_owner(&self) -> u32 { self.owner }
    pub open spec fn wf(&self) -> bool { valid(self.view()) && self.stored_owner() == owner(parameters(self.view())) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn len(&self) -> (r: usize) ensures self.wf(), r == self.view().entries.len(), r <= name_set::MAX_KEYS {
        proof { use_type_invariant(self); reveal(valid); reveal(name_set::valid); } self.entries.len()
    }
    pub fn get(&self, i: usize) -> (r: Option<&Entry<'a>>)
        ensures self.wf(), match r { Some(e) => i < self.view().entries.len() && e.view() == self.view().entries[i as int] && source_record(parameters(self.view()), e.view()), None => i >= self.view().entries.len() },
    {
        proof { use_type_invariant(self); reveal(valid); reveal(entries_valid); }
        if i < self.entries.len() { Some(&self.entries[i]) } else { None }
    }
    pub fn lookup(&self, name: &[u8]) -> (r: Option<&Entry<'a>>)
        ensures self.wf(), match r { Some(e) => self.view().entries.contains(e.view()) && e.view().name == name@ && source_record(parameters(self.view()), e.view()),
            None => !has_name(self.view().entries, name@) && absent(self.view(), name@) },
    {
        proof { use_type_invariant(self); reveal(valid); }
        match self.names.find(self.owner, name) {
            Some(i) => {
                let e = &self.entries[i as usize];
                assert(self.view().entries.contains(e.view())) by { assert(self.view().entries[i as int] == e.view()); }
                proof { reveal(entries_valid); }
                Some(e)
            },
            None => {
                assert(!has_name(self.view().entries, name@)) by {
                    if has_name(self.view().entries, name@) {
                        let i = choose|i: int| 0 <= i < self.view().entries.len() && (#[trigger] self.view().entries[i]).name == name@;
                        assert(self.names.view().keys[i] == (self.owner, name@));
                        assert(self.names.view().keys.contains((self.owner, name@)));
                    }
                }
                proof { cache_absence_is_complete_source_absence(self.view(), name@); }
                None
            },
        }
    }
}

pub fn build<'a>(blocks: &[&'a [u8]], inodes: u32, seed: u32, hash_seed: State, unsigned: bool, large: bool) -> (r: Option<Directory<'a>>)
    ensures match r { Some(directory) => directory.wf() && directory.view().graph.context == (topology::Context { source: topology::source_views(blocks@), inodes, seed, large })
        && directory.view().hash_seed == hash_seed && directory.view().version as nat == blocks@[0]@[28] as nat + if unsigned { 3nat } else { 0nat }, None => true },
{
    let graph = match topology::parse(blocks, inodes, seed, large) { Some(graph) => graph, None => { return None; } };
    let root = graph.checked_root();
    let (hash, depth) = root.hash_and_levels();
    let count = root.routing_index().child_count();
    proof {
        reveal(topology::valid);
        topology::a_checked_node_retains_its_header_and_every_source_child(graph.view().context, 0, graph.view().depth, 0);
        reveal(topology::local);
    }
    if hash > 2 { return None; }
    let version = hash + if unsigned { 3u8 } else { 0u8 };
    let directory = bytes::read_le32(blocks[0], 0).unwrap();
    let parent = bytes::read_le32(blocks[0], 12).unwrap();
    let ghost p = Parameters { tree: graph.view().context, hash_seed, version };
    let mut entries = Vec::<Entry>::new();
    let dot = &blocks[0][8..9];
    let dotdot = &blocks[0][20..22];
    entries.push(capture(0, 0, directory, 2, dot)); entries.push(capture(0, 1, parent, 2, dotdot));
    let mut names = NameSet::new();
    names = match names.insert(directory, dot) { Ok(next) => next, Err(_) => { return None; } };
    names = match names.insert(directory, dotdot) { Ok(next) => next, Err(_) => { return None; } };
    assert(views(entries@) =~= root_entries(p));
    assert(keys(p, views(entries@)) =~= names.view().keys);
    assert(entries_valid(p, views(entries@))) by { reveal(entries_valid); }
    let count = root.routing_index().child_count();
    proof {
        reveal(topology::valid);
        topology::a_checked_node_retains_its_header_and_every_source_child(p.tree, 0, depth, 0);
    }
    let (entries, names) = match collect(blocks, root.routing_index(), 0, depth, range::full(), inodes, seed, hash_seed, version, directory, entries, names, Ghost(p)) {
        Some(pair) => pair, None => { return None; }
    };
    let ghost view = DirectoryView { graph: graph.view(), entries: views(entries@), names: names.view(), hash_seed, version };
    assert(valid(view)) by { reveal(valid); }
    Some(Directory { graph, entries, names, hash_seed, version, owner: directory })
}

pub proof fn full_name_lookup_has_at_most_one_source_record(v: DirectoryView, i: int, j: int)
    requires valid(v), 0 <= i < v.entries.len(), 0 <= j < v.entries.len(), v.entries[i].name == v.entries[j].name,
    ensures i == j,
{
    reveal(valid); reveal(name_set::valid);
    if i != j { assert(v.names.keys[i] == v.names.keys[j]); }
}

proof fn a_live_record_is_in_its_complete_block(p: Parameters, logical: u32, length: nat, record: int)
    requires 0 <= record < length <= records(p, logical).len(), records(p, logical)[record].inode != 0,
    ensures block_entries(p, logical, length).contains(entry(p, logical, record)),
    decreases length,
{
    reveal(block_entries);
    if record < length - 1 { a_live_record_is_in_its_complete_block(p, logical, (length - 1) as nat, record); }
    let before = block_entries(p, logical, (length - 1) as nat);
    if records(p, logical)[length as int - 1].inode != 0 {
        vstd::seq_lib::lemma_seq_contains_after_push(before, entry(p, logical, length as int - 1), entry(p, logical, record));
    }
}
proof fn a_leaf_claim_contributes_every_live_record(p: Parameters, number: u32, depth: u8, length: nat, i: nat, logical: u32, record: int)
    requires i < topology::claims(p.tree, number, depth, length).len(), topology::claims(p.tree, number, depth, length)[i as int] == topology::owned(logical, 3),
        0 <= record < records(p, logical).len(), records(p, logical)[record].inode != 0,
    ensures tree_entries(p, number, depth, length).contains(entry(p, logical, record)),
    decreases depth, length,
{
    reveal(topology::claims); reveal(tree_entries);
    if length > 0 {
        let target = topology::child(p.tree, number, (length - 1) as nat);
        let before = topology::claims(p.tree, number, depth, (length - 1) as nat);
        let before_names = tree_entries(p, number, depth, (length - 1) as nat);
        if i < before.len() {
            a_leaf_claim_contributes_every_live_record(p, number, depth, (length - 1) as nat, i, logical, record);
            let k = choose|k: int| 0 <= k < before_names.len() && before_names[k] == entry(p, logical, record);
            assert(tree_entries(p, number, depth, length)[k] == entry(p, logical, record));
        } else {
            if depth == 0 {
                assert(target == logical);
                a_live_record_is_in_its_complete_block(p, logical, records(p, logical).len(), record);
            } else {
                a_leaf_claim_contributes_every_live_record(p, target, (depth - 1) as u8, topology::count(p.tree, target), (i - before.len()) as nat, logical, record);
            }
            let suffix = if depth == 0 { block_entries(p, target, records(p, target).len()) }
                else { tree_entries(p, target, (depth - 1) as u8, topology::count(p.tree, target)) };
            let k = choose|k: int| 0 <= k < suffix.len() && suffix[k] == entry(p, logical, record);
            assert(tree_entries(p, number, depth, length)[before_names.len() as int + k] == entry(p, logical, record));
        }
    }
}

pub proof fn every_live_source_leaf_record_appears_in_lookup(v: DirectoryView, logical: u32, record: int)
    requires valid(v), logical < v.graph.context.source.len(), v.graph.census.roles[logical as int].kind == 3,
        0 <= record < records(parameters(v), logical).len(), records(parameters(v), logical)[record].inode != 0,
    ensures v.entries.contains(entry(parameters(v), logical, record)),
{
    reveal(valid);
    let p = parameters(v);
    topology::every_leaf_role_has_a_checked_source_leaf_claim(v.graph, logical);
    let i = choose|i: int| 0 <= i < topology::claims(p.tree, 0, v.graph.depth, topology::count(p.tree, 0)).len()
        && (#[trigger] topology::claims(p.tree, 0, v.graph.depth, topology::count(p.tree, 0))[i]) == topology::owned(logical, 3);
    a_leaf_claim_contributes_every_live_record(p, 0, v.graph.depth, topology::count(p.tree, 0), i as nat, logical, record);
    let catalog = tree_entries(p, 0, v.graph.depth, topology::count(p.tree, 0));
    let k = choose|k: int| 0 <= k < catalog.len() && catalog[k] == entry(p, logical, record);
    assert(v.entries[root_entries(p).len() as int + k] == entry(p, logical, record));
}
#[verifier::opaque]
pub open spec fn absent(v: DirectoryView, name: Seq<u8>) -> bool {
    !has_name(root_entries(parameters(v)), name) && (forall|logical: u32, record: int| logical < v.graph.context.source.len()
        && v.graph.census.roles[logical as int].kind == 3 && 0 <= record < records(parameters(v), logical).len()
        && records(parameters(v), logical)[record].inode != 0 ==> (#[trigger] entry(parameters(v), logical, record)).name != name)
}
proof fn cache_absence_is_complete_source_absence(v: DirectoryView, name: Seq<u8>)
    requires valid(v), !has_name(v.entries, name), ensures absent(v, name),
{
    reveal(valid);
    if has_name(root_entries(parameters(v)), name) {
        let k = choose|k: int| 0 <= k < root_entries(parameters(v)).len() && (#[trigger] root_entries(parameters(v))[k]).name == name;
        assert(v.entries[k].name == name);
        assert(has_name(v.entries, name));
    }
    assert forall|logical: u32, record: int| logical < v.graph.context.source.len() && v.graph.census.roles[logical as int].kind == 3
        && 0 <= record < records(parameters(v), logical).len() && records(parameters(v), logical)[record].inode != 0
        implies (#[trigger] entry(parameters(v), logical, record)).name != name by {
        if entry(parameters(v), logical, record).name == name {
            every_live_source_leaf_record_appears_in_lookup(v, logical, record);
            let e = entry(parameters(v), logical, record);
            let k = choose|k: int| 0 <= k < v.entries.len() && v.entries[k] == e;
            assert(has_name(v.entries, name));
        }
    }
    reveal(absent);
}

#[verifier::opaque]
pub open spec fn routed(p: Parameters, number: u32, depth: u8, hash: u32, logical: u32, length: nat) -> bool
    decreases depth, length,
{
    if length == 0 { false } else {
        let i = (length - 1) as nat;
        let target = topology::child(p.tree, number, i);
        routed(p, number, depth, hash, logical, i) || range::possible(topology::index_view(p.tree, number), hash, i)
            && if depth == 0 { target == logical } else { routed(p, target, (depth - 1) as u8, hash, logical, topology::count(p.tree, target)) }
    }
}
proof fn ranges_retain_the_checked_header_and_parent_bounds(p: Parameters, number: u32, depth: u8, bounds: Bounds, length: nat)
    requires ranges(p, number, depth, bounds, length),
    ensures parameters_valid(p), range::valid(bounds), topology::subtree(p.tree, number, depth),
    decreases length,
{
    reveal(ranges);
    if length > 0 { ranges_retain_the_checked_header_and_parent_bounds(p, number, depth, bounds, (length - 1) as nat); }
}
proof fn checked_leaf_hashes_include_each_live_record(p: Parameters, logical: u32, bounds: Bounds, length: nat, record: int)
    requires leaf_hashes(p, logical, bounds, length), 0 <= record < length, records(p, logical)[record].inode != 0,
    ensures range::contains(bounds, dir_hash::value(entry(p, logical, record).name, p.hash_seed, p.version).major),
    decreases length,
{
    reveal(leaf_hashes);
    if record < length - 1 { checked_leaf_hashes_include_each_live_record(p, logical, bounds, (length - 1) as nat, record); }
    else { assert(record == length - 1); }
}
proof fn an_even_contained_hash_has_a_candidate_edge(p: Parameters, number: u32, depth: u8, bounds: Bounds, i: nat, hash: u32)
    requires topology::subtree(p.tree, number, depth), i < topology::count(p.tree, number), hash & 1u32 == 0,
        range::fits(bounds, range::child(topology::index_view(p.tree, number), bounds, i)),
        range::contains(range::child(topology::index_view(p.tree, number), bounds, i), hash),
    ensures range::possible(topology::index_view(p.tree, number), hash, i), range::contains(bounds, hash),
{
    topology::a_checked_node_retains_its_header_and_every_source_child(p.tree, number, depth, i);
    reveal(topology::local);
    let v = topology::index_view(p.tree, number);
    range::every_checked_index_has_a_linux_probe_selection(v, hash);
    let start = choose|start: nat| #[trigger] htree::selected(v, hash, start);
    range::every_contained_hash_is_in_the_linux_probe_continuation_set(v, bounds, i, hash, start);
    assert(range::possible(v, hash, i));
    range::a_checked_child_interval_cannot_escape_its_parent(bounds, range::child(v, bounds, i), hash);
}
proof fn a_checked_leaf_claim_is_on_a_linux_candidate_path(p: Parameters, number: u32, depth: u8, bounds: Bounds, length: nat, claim: nat, logical: u32, record: int, hash: u32)
    requires ranges(p, number, depth, bounds, length), length <= topology::count(p.tree, number),
        claim < topology::claims(p.tree, number, depth, length).len(), topology::claims(p.tree, number, depth, length)[claim as int] == topology::owned(logical, 3),
        0 <= record < records(p, logical).len(), records(p, logical)[record].inode != 0,
        hash == dir_hash::value(entry(p, logical, record).name, p.hash_seed, p.version).major, hash & 1u32 == 0,
    ensures range::contains(bounds, hash), routed(p, number, depth, hash, logical, length),
    decreases depth, length,
{
    reveal(ranges); reveal(topology::claims); reveal(routed);
    ranges_retain_the_checked_header_and_parent_bounds(p, number, depth, bounds, length);
    if length > 0 {
        let i = (length - 1) as nat;
        let target = topology::child(p.tree, number, i);
        let before = topology::claims(p.tree, number, depth, i);
        let next = range::child(topology::index_view(p.tree, number), bounds, i);
        if claim < before.len() {
            a_checked_leaf_claim_is_on_a_linux_candidate_path(p, number, depth, bounds, i, claim, logical, record, hash);
        } else {
            if depth == 0 {
                assert(target == logical);
                checked_leaf_hashes_include_each_live_record(p, logical, next, records(p, logical).len(), record);
            } else {
                a_checked_leaf_claim_is_on_a_linux_candidate_path(p, target, (depth - 1) as u8, next,
                    topology::count(p.tree, target), (claim - before.len()) as nat, logical, record, hash);
            }
            an_even_contained_hash_has_a_candidate_edge(p, number, depth, bounds, i, hash);
        }
    }
}

pub proof fn every_live_source_record_is_reachable_by_linux_hash_probe_and_continuations(v: DirectoryView, logical: u32, record: int)
    requires valid(v), logical < v.graph.context.source.len(), v.graph.census.roles[logical as int].kind == 3,
        0 <= record < records(parameters(v), logical).len(), records(parameters(v), logical)[record].inode != 0,
    ensures routed(parameters(v), 0, v.graph.depth, dir_hash::value(entry(parameters(v), logical, record).name, v.hash_seed, v.version).major,
        logical, topology::count(v.graph.context, 0)),
{
    hide(dir_hash::value);
    reveal(valid);
    let p = parameters(v);
    topology::every_leaf_role_has_a_checked_source_leaf_claim(v.graph, logical);
    reveal(topology::leaf); reveal(directory_block::valid); reveal(directory_block::chain);
    assert(directory_block::record(p.tree.source[logical as int], p.tree.inodes, records(p, logical)[record]));
    assert(entry(p, logical, record).name.len() <= 255);
    dir_hash::every_unkeyed_hash_reserves_the_collision_bit_and_eof_value(entry(p, logical, record).name, p.hash_seed, p.version);
    let i = choose|i: int| 0 <= i < topology::claims(p.tree, 0, v.graph.depth, topology::count(p.tree, 0)).len()
        && (#[trigger] topology::claims(p.tree, 0, v.graph.depth, topology::count(p.tree, 0))[i]) == topology::owned(logical, 3);
    a_checked_leaf_claim_is_on_a_linux_candidate_path(p, 0, v.graph.depth, Bounds { lower: 0, upper: 4294967296, inclusive: false },
        topology::count(p.tree, 0), i as nat, logical, record, dir_hash::value(entry(p, logical, record).name, p.hash_seed, p.version).major);
}

// dx_probe descends by binary search. dx_next_block descends from the first
// entry after moving to a continued subtree; it does not probe that subtree.
pub open spec fn edge_candidate(v: htree::IndexView, hash: u32, first: bool, i: nat) -> bool {
    if first { i < htree::count(v) && (forall|j: nat| 0 < j <= i ==> #[trigger] htree::continuation(v, hash, j)) }
    else { range::possible(v, hash, i) }
}
#[verifier::opaque]
pub open spec fn linux_routed(p: Parameters, number: u32, depth: u8, hash: u32, logical: u32, first: bool, length: nat) -> bool
    decreases depth, length,
{
    if length == 0 { false } else {
        let i = (length - 1) as nat;
        let target = topology::child(p.tree, number, i);
        let index = topology::index_view(p.tree, number);
        linux_routed(p, number, depth, hash, logical, first, i) || edge_candidate(index, hash, first, i)
            && if depth == 0 { target == logical } else {
                linux_routed(p, target, (depth - 1) as u8, hash, logical, first || !htree::selected(index, hash, i), topology::count(p.tree, target))
            }
    }
}
proof fn every_checked_prefix_child_has_fitting_bounds(p: Parameters, number: u32, depth: u8, bounds: Bounds, length: nat, i: nat)
    requires ranges(p, number, depth, bounds, length), i < length,
    ensures range::fits(bounds, range::child(topology::index_view(p.tree, number), bounds, i)),
    decreases length,
{
    reveal(ranges);
    if i < length - 1 { every_checked_prefix_child_has_fitting_bounds(p, number, depth, bounds, (length - 1) as nat, i); }
    else { assert(i == length - 1); }
}
proof fn monotone_boundary_bases_stay_at_the_inherited_query(left: u32, right: u32, hash: u32)
    requires left <= right, left & !1u32 >= hash, right & !1u32 <= hash,
    ensures left & !1u32 == hash,
{
    assert(left <= right && left & !1u32 >= hash && right & !1u32 <= hash ==> left & !1u32 == hash) by (bit_vector);
}
proof fn a_continued_probe_edge_starts_at_the_query_hash(index: htree::IndexView, bounds: Bounds, i: nat, hash: u32)
    requires range::possible(index, hash, i), !htree::selected(index, hash, i), range::contains(range::child(index, bounds, i), hash),
    ensures range::child(index, bounds, i).lower == hash,
{
    let start = choose|start: nat| #[trigger] range::candidate(index, hash, start, i);
    assert(start < i);
    let boundary = htree::edge(index.raw, index.first as nat, i).hash;
    assert(boundary > hash && boundary & !1u32 <= hash);
    assert(boundary > hash && boundary & !1u32 <= hash ==> boundary & !1u32 == hash) by (bit_vector);
}
proof fn checked_intervals_support_both_linux_entry_modes(p: Parameters, number: u32, depth: u8, bounds: Bounds, length: nat, i: nat, hash: u32, first: bool)
    requires ranges(p, number, depth, bounds, length), length <= topology::count(p.tree, number), i < length,
        range::contains(range::child(topology::index_view(p.tree, number), bounds, i), hash), hash & 1u32 == 0,
        first ==> hash == bounds.lower,
    ensures edge_candidate(topology::index_view(p.tree, number), hash, first, i),
        first || !htree::selected(topology::index_view(p.tree, number), hash, i) ==> range::child(topology::index_view(p.tree, number), bounds, i).lower == hash,
{
    ranges_retain_the_checked_header_and_parent_bounds(p, number, depth, bounds, length);
    every_checked_prefix_child_has_fitting_bounds(p, number, depth, bounds, length, i);
    an_even_contained_hash_has_a_candidate_edge(p, number, depth, bounds, i, hash);
    let index = topology::index_view(p.tree, number);
    topology::a_checked_node_retains_its_header_and_every_source_child(p.tree, number, depth, i);
    reveal(topology::local);
    if first {
        assert forall|j: nat| 0 < j <= i implies #[trigger] htree::continuation(index, hash, j) by {
            every_checked_prefix_child_has_fitting_bounds(p, number, depth, bounds, length, j);
            htree::monotone(index, j, i);
            monotone_boundary_bases_stay_at_the_inherited_query(htree::edge(index.raw, index.first as nat, j).hash,
                htree::edge(index.raw, index.first as nat, i).hash, hash);
        }
    } else if !htree::selected(index, hash, i) { a_continued_probe_edge_starts_at_the_query_hash(index, bounds, i, hash); }
}
proof fn a_checked_leaf_claim_follows_both_linux_entry_modes(p: Parameters, number: u32, depth: u8, bounds: Bounds, length: nat,
    claim: nat, logical: u32, record: int, hash: u32, first: bool)
    requires ranges(p, number, depth, bounds, length), length <= topology::count(p.tree, number),
        claim < topology::claims(p.tree, number, depth, length).len(), topology::claims(p.tree, number, depth, length)[claim as int] == topology::owned(logical, 3),
        0 <= record < records(p, logical).len(), records(p, logical)[record].inode != 0,
        hash == dir_hash::value(entry(p, logical, record).name, p.hash_seed, p.version).major, hash & 1u32 == 0,
        first ==> hash == bounds.lower,
    ensures linux_routed(p, number, depth, hash, logical, first, length),
    decreases depth, length,
{
    reveal(ranges); reveal(topology::claims); reveal(linux_routed);
    if length > 0 {
        let i = (length - 1) as nat;
        let target = topology::child(p.tree, number, i);
        let before = topology::claims(p.tree, number, depth, i);
        let next = range::child(topology::index_view(p.tree, number), bounds, i);
        if claim < before.len() {
            a_checked_leaf_claim_follows_both_linux_entry_modes(p, number, depth, bounds, i, claim, logical, record, hash, first);
        } else {
            if depth == 0 {
                assert(target == logical);
                checked_leaf_hashes_include_each_live_record(p, logical, next, records(p, logical).len(), record);
            } else {
                a_checked_leaf_claim_is_on_a_linux_candidate_path(p, target, (depth - 1) as u8, next,
                    topology::count(p.tree, target), (claim - before.len()) as nat, logical, record, hash);
            }
            checked_intervals_support_both_linux_entry_modes(p, number, depth, bounds, length, i, hash, first);
            if depth > 0 {
                a_checked_leaf_claim_follows_both_linux_entry_modes(p, target, (depth - 1) as u8, next, topology::count(p.tree, target),
                    (claim - before.len()) as nat, logical, record, hash, first || !htree::selected(topology::index_view(p.tree, number), hash, i));
            }
        }
    }
}

pub proof fn every_live_record_follows_linux_probe_and_first_entry_continuation_descent(v: DirectoryView, logical: u32, record: int)
    requires valid(v), logical < v.graph.context.source.len(), v.graph.census.roles[logical as int].kind == 3,
        0 <= record < records(parameters(v), logical).len(), records(parameters(v), logical)[record].inode != 0,
    ensures linux_routed(parameters(v), 0, v.graph.depth, dir_hash::value(entry(parameters(v), logical, record).name, v.hash_seed, v.version).major,
        logical, false, topology::count(v.graph.context, 0)),
{
    hide(dir_hash::value);
    reveal(valid);
    let p = parameters(v);
    topology::every_leaf_role_has_a_checked_source_leaf_claim(v.graph, logical);
    reveal(topology::leaf); reveal(directory_block::valid); reveal(directory_block::chain);
    assert(directory_block::record(p.tree.source[logical as int], p.tree.inodes, records(p, logical)[record]));
    assert(entry(p, logical, record).name.len() <= 255);
    dir_hash::every_unkeyed_hash_reserves_the_collision_bit_and_eof_value(entry(p, logical, record).name, p.hash_seed, p.version);
    let i = choose|i: int| 0 <= i < topology::claims(p.tree, 0, v.graph.depth, topology::count(p.tree, 0)).len()
        && (#[trigger] topology::claims(p.tree, 0, v.graph.depth, topology::count(p.tree, 0))[i]) == topology::owned(logical, 3);
    a_checked_leaf_claim_follows_both_linux_entry_modes(p, 0, v.graph.depth, Bounds { lower: 0, upper: 4294967296, inclusive: false },
        topology::count(p.tree, 0), i as nat, logical, record, dir_hash::value(entry(p, logical, record).name, p.hash_seed, p.version).major, false);
}

}
