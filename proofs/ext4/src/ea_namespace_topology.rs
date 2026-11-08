// SPDX-License-Identifier: MPL-2.0

//! Rooted parent-graph validation with bounded, nonrecursive execution.
//! Each new path is marked, assigned depths, then resolved. Ghost path
//! certificates prove coverage; no runtime path stack is allocated.

use vstd::prelude::*;
use crate::{block_claims, ea_namespace_parent::{self as parent_table, ParentTable, TableView}, ea_directory_index::{DirectoryIndex, IndexView}, tree_model::{self as model, MAX_DEPTH}};

verus! {

pub struct TreeView { pub index: IndexView, pub parents: Seq<u32>, pub depths: Seq<u32> }

/// A declarative bounded rank for the raw parent graph. This predicate does
/// not mention the validator, colors, execution trace, or a Tree certificate.
#[verifier::opaque]
pub open spec fn rank_witness(parents: Seq<u32>, ranks: Seq<u32>) -> bool {
    &&& ranks.len() == parents.len()
    &&& (forall|n: int| model::active(parents, n) ==> #[trigger] model::node_rank(parents, ranks, n))
    &&& (forall|n: int| 0 <= n < ranks.len() && !model::active(parents, n) ==> #[trigger] ranks[n] == 0)
}

#[verifier::opaque]
pub open spec fn bounded_rooted(parents: Seq<u32>) -> bool {
    model::shape(parents) && exists|ranks: Seq<u32>| rank_witness(parents, ranks)
}

proof fn path_rank_distance_from(parents: Seq<u32>, ranks: Seq<u32>, path: Seq<u32>,
    start: u32, end: u32, index: nat)
    requires rank_witness(parents, ranks), model::path_chain(parents, path, start, end),
        index < path.len(), forall|i: int| 0 <= i < path.len() ==> (#[trigger] path[i]) != 2,
    ensures ranks[path[index as int] as int] as nat == ranks[end as int] as nat + path.len() - index,
    decreases path.len() - index,
{
    reveal(rank_witness); reveal(model::path_chain);
    let n = path[index as int];
    assert(model::node_rank(parents, ranks, n as int));
    if index + 1 < path.len() {
        path_rank_distance_from(parents, ranks, path, start, end, index + 1);
        assert(parents[n as int] == path[index as int + 1]);
    } else {
        assert(index + 1 == path.len() && parents[n as int] == end);
    }
}

proof fn gathered_path_has_rank_distance(parents: Seq<u32>, ranks: Seq<u32>,
    old: Seq<u8>, now: Seq<u8>, path: Seq<u32>, start: u32, end: u32)
    requires rank_witness(parents, ranks), model::shape(parents),
        model::path_chain(parents, path, start, end), model::gathered(old, now, path),
        old.len() == parents.len(), old[2] == 2,
    ensures ranks[start as int] as nat == ranks[end as int] as nat + path.len(),
        !path.contains(end),
{
    reveal(model::path_chain); reveal(model::gathered);
    assert forall|i: int| 0 <= i < path.len() implies (#[trigger] path[i]) != 2 by {
        assert(old[path[i] as int] == 0);
    }
    if path.len() > 0 {
        path_rank_distance_from(parents, ranks, path, start, end, 0);
    }
    assert(!path.contains(end)) by {
        if path.contains(end) {
            let i = choose|i: int| 0 <= i < path.len() && (#[trigger] path[i]) == end;
            path_rank_distance_from(parents, ranks, path, start, end, i as nat);
            assert(path.len() - i > 0);
        }
    }
}

proof fn resolved_depth_matches_rank(parents: Seq<u32>, ranks: Seq<u32>,
    colors: Seq<u8>, depths: Seq<u32>, number: u32)
    requires model::shape(parents), rank_witness(parents, ranks),
        model::ranked(parents, colors, depths), model::closed(parents, colors),
        number < colors.len(), colors[number as int] == 2,
    ensures depths[number as int] == ranks[number as int],
    decreases depths[number as int],
{
    reveal(model::shape); reveal(rank_witness); reveal(model::ranked); reveal(model::closed);
    assert(model::node_rank(parents, depths, number as int));
    assert(model::node_rank(parents, ranks, number as int));
    if number != 2 {
        let parent = parents[number as int];
        assert(colors[parent as int] == 2);
        resolved_depth_matches_rank(parents, ranks, colors, depths, parent);
    }
}

#[verifier::opaque]
pub open spec fn valid(v: TreeView) -> bool {
    &&& parent_table::valid(TableView { index: v.index, parents: v.parents }) && model::shape(v.parents)
    &&& v.depths.len() == v.parents.len()
    &&& (forall|n: int| model::active(v.parents, n) ==> #[trigger] model::node_rank(v.parents, v.depths, n))
    &&& (forall|n: int| 0 <= n < v.depths.len() && !model::active(v.parents, n) ==> #[trigger] v.depths[n] == 0)
}

pub open spec fn walk(parents: Seq<u32>, number: u32, count: nat) -> u32
    decreases count,
{
    if count == 0 { number } else { walk(parents, parents[number as int], (count - 1) as nat) }
}

pub proof fn every_directory_reaches_root(v: TreeView, number: u32)
    requires valid(v), model::active(v.parents, number as int),
    ensures walk(v.parents, number, v.depths[number as int] as nat) == 2,
    decreases v.depths[number as int],
{
    reveal(valid); reveal(model::shape);
    assert(model::node_rank(v.parents, v.depths, number as int));
    if number != 2 {
        let parent = v.parents[number as int];
        assert(model::node_rank(v.parents, v.depths, parent as int));
        every_directory_reaches_root(v, parent);
    }
}

pub struct Tree { table: ParentTable, depths: Vec<u32> }

impl Tree {
    pub closed spec fn view(&self) -> TreeView { TreeView { index: self.table.view().index, parents: self.table.view().parents, depths: self.depths@ } }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn depth(&self, number: u32) -> (r: Option<u32>)
        ensures self.wf(), match r {
            Some(depth) => model::active(self.view().parents, number as int) && depth == self.view().depths[number as int]
                && depth <= MAX_DEPTH && (number == 2 <==> depth == 0),
            None => !model::active(self.view().parents, number as int),
        },
    {
        proof { use_type_invariant(self); reveal(valid); }
        match self.table.parent(number) {
            None => None,
            Some(_) => {
                assert(model::node_rank(self.view().parents, self.view().depths, number as int));
                Some(self.depths[number as usize])
            },
        }
    }

    pub fn parent(&self, number: u32) -> (r: Option<u32>)
        ensures self.wf(), match r {
            Some(parent) => model::active(self.view().parents, number as int) && parent == self.view().parents[number as int],
            None => !model::active(self.view().parents, number as int),
        },
    {
        proof { use_type_invariant(self); }
        self.table.parent(number)
    }
}

proof fn checked_parent_table_has_graph_shape(v: TableView)
    requires parent_table::valid(v),
    ensures model::shape(v.parents),
{ reveal(parent_table::valid); reveal(model::shape); }

/// Validate an already checked parent table. A bounded rooted parent graph
/// is accepted; rejection proves that no bounded rank witness exists.
pub fn build_parent_table(table: ParentTable) -> (r: Option<Tree>)
    ensures match r {
        Some(tree) => tree.wf() && tree.view().index == table.view().index
            && tree.view().parents == table.view().parents && bounded_rooted(table.view().parents),
        None => !bounded_rooted(table.view().parents),
    },
{
    let capacity = table.len() as u32;
    proof { checked_parent_table_has_graph_shape(table.view()); }
    let ghost mut witness = Seq::<u32>::empty();
    proof {
        if bounded_rooted(table.view().parents) {
            reveal(bounded_rooted);
            witness = choose|ranks: Seq<u32>| rank_witness(table.view().parents, ranks);
            assert(rank_witness(table.view().parents, witness));
        }
    }
    assert(bounded_rooted(table.view().parents) ==> rank_witness(table.view().parents, witness));
    let mut colors = Vec::<u8>::new();
    let mut depths = Vec::<u32>::new();
    let mut i = 0u32;
    while i < capacity
        invariant table.wf(), model::shape(table.view().parents), capacity == table.view().parents.len(),
            bounded_rooted(table.view().parents) ==> rank_witness(table.view().parents, witness),
            3 <= capacity <= block_claims::MAX_BLOCKS as nat + 1, i <= capacity, colors.len() == i, depths.len() == i,
            forall|n: int| 0 <= n < i ==> (#[trigger] colors@[n]) == 0 && depths@[n] == 0,
        decreases capacity - i,
    {
        colors.push(0);
        depths.push(0);
        i += 1;
    }
    assert(i == capacity && colors.len() == capacity && depths.len() == capacity);
    assert(colors@[2] == 0 && depths@[2] == 0) by {
        assert(0 <= 2 < i);
    }
    let ghost zero_colors = colors@;
    colors.set(2, 2u8);
    assert forall|n: int| 0 <= n < colors.len() implies ((#[trigger] colors@[n]) == (if n == 2 { 2u8 } else { 0u8 }))
        && depths@[n] == 0 by {
        assert(zero_colors[n] == 0 && depths@[n] == 0);
    }
    assert(colors@[2] == 2 && depths@[2] == 0);
    assert(model::node_rank(table.view().parents, depths@, 2)) by { reveal(model::shape); }
    assert(model::ranked(table.view().parents, colors@, depths@)) by { reveal(model::ranked); reveal(model::shape); }
    assert(model::closed(table.view().parents, colors@)) by { reveal(model::closed); reveal(model::shape); }
    assert(model::no_pending(colors@)) by { reveal(model::no_pending); }
    assert(model::processed(table.view().parents, colors@, 0)) by { reveal(model::processed); }
    let mut number = 0u32;
    while number < capacity
        invariant table.wf(), model::shape(table.view().parents), capacity == table.view().parents.len(),
            bounded_rooted(table.view().parents) ==> rank_witness(table.view().parents, witness),
            3 <= capacity <= block_claims::MAX_BLOCKS as nat + 1, number <= capacity,
            model::ranked(table.view().parents, colors@, depths@), model::closed(table.view().parents, colors@), model::no_pending(colors@),
            model::processed(table.view().parents, colors@, number as nat), colors.len() == capacity, depths.len() == capacity,
        decreases capacity - number,
    {
        let is_directory = table.parent(number).is_some();
        assert(is_directory == model::active(table.view().parents, number as int));
        if is_directory && colors[number as usize] == 0 {
            let ghost old_colors = colors@;
            let ghost old_depths = depths@;
            let ghost mut path = Seq::<u32>::empty();
            let mut path_length = 0u32;
            let mut cursor = number;
            proof { model::empty_path_is_ready(table.view().parents, colors@, number); }
            while colors[cursor as usize] == 0
                invariant table.wf(), model::shape(table.view().parents), capacity == table.view().parents.len(),
                    bounded_rooted(table.view().parents) ==> rank_witness(table.view().parents, witness),
                    3 <= capacity <= block_claims::MAX_BLOCKS as nat + 1,
                    colors.len() == capacity, depths@ == old_depths, old_depths.len() == capacity, old_colors.len() == capacity,
                    model::ranked(table.view().parents, old_colors, old_depths), model::closed(table.view().parents, old_colors), model::no_pending(old_colors),
                    model::processed(table.view().parents, old_colors, number as nat),
                    model::path_chain(table.view().parents, path, number, cursor), model::gathered(old_colors, colors@, path),
                    model::active(table.view().parents, cursor as int),
                    model::active(table.view().parents, number as int), number < capacity,
                    old_colors[number as int] == 0, path_length == path.len(), path_length <= MAX_DEPTH,
                decreases MAX_DEPTH - path_length,
            {
                if path_length == MAX_DEPTH {
                    proof {
                        if bounded_rooted(table.view().parents) {
                            reveal(model::ranked);
                            gathered_path_has_rank_distance(table.view().parents, witness,
                                old_colors, colors@, path, number, cursor);
                            reveal(rank_witness); reveal(model::ranked); reveal(model::gathered);
                            assert(colors@[cursor as int] == old_colors[cursor as int]);
                            assert(cursor != 2);
                            assert(model::node_rank(table.view().parents, witness, cursor as int));
                            assert(number != 2);
                            assert(model::node_rank(table.view().parents, witness, number as int));
                            assert(false);
                        }
                    }
                    return None;
                }
                let next = table.parent(cursor).unwrap();
                let ghost previous = colors@;
                proof { model::append_fresh_path_node(table.view().parents, old_colors, previous, path, number, cursor, next); }
                colors.set(cursor as usize, 1u8);
                proof { path = path.push(cursor); }
                path_length += 1;
                cursor = next;
            }
            if colors[cursor as usize] != 2 || path_length == 0 {
                proof {
                    if bounded_rooted(table.view().parents) {
                        reveal(model::ranked);
                        gathered_path_has_rank_distance(table.view().parents, witness,
                            old_colors, colors@, path, number, cursor);
                        reveal(model::ranked); reveal(model::no_pending);
                        reveal(model::gathered); reveal(model::path_chain);
                        assert(colors@[cursor as int] == old_colors[cursor as int]);
                        assert(colors@[cursor as int] == 2);
                        if path_length == 0 {
                            assert(cursor == number && old_colors[number as int] == 0);
                            assert(false);
                        }
                    }
                }
                return None;
            }
            let anchor = cursor;
            let base = depths[anchor as usize];
            assert(old_colors[anchor as int] == 2 && !path.contains(anchor)) by { reveal(model::gathered); }
            if base > MAX_DEPTH - path_length {
                proof {
                    if bounded_rooted(table.view().parents) {
                        reveal(model::ranked);
                        gathered_path_has_rank_distance(table.view().parents, witness,
                            old_colors, colors@, path, number, anchor);
                        resolved_depth_matches_rank(table.view().parents, witness,
                            old_colors, old_depths, anchor);
                        reveal(rank_witness); reveal(model::ranked);
                        assert(number != 2);
                        assert(model::node_rank(table.view().parents, witness, number as int));
                        assert(false);
                    }
                }
                return None;
            }
            let mut done = 0u32;
            cursor = number;
            assert(path[0] == number && path.no_duplicates()) by { reveal(model::path_chain); }
            assert(model::depth_prefix(old_depths, depths@, path, base, 0)) by { reveal(model::depth_prefix); reveal(model::path_chain); }
            while done < path_length
                invariant table.wf(), model::shape(table.view().parents), capacity == table.view().parents.len(),
                    bounded_rooted(table.view().parents) ==> rank_witness(table.view().parents, witness),
                    3 <= capacity <= block_claims::MAX_BLOCKS as nat + 1, anchor < capacity,
                    colors.len() == capacity, depths.len() == capacity, old_colors.len() == capacity, old_depths.len() == capacity,
                    model::ranked(table.view().parents, old_colors, old_depths), model::closed(table.view().parents, old_colors), model::no_pending(old_colors),
                    model::processed(table.view().parents, old_colors, number as nat),
                    model::path_chain(table.view().parents, path, number, anchor), path.no_duplicates(), model::gathered(old_colors, colors@, path),
                    colors[anchor as int] == 2, old_colors[anchor as int] == 2, base == old_depths[anchor as int],
                    0 < path_length == path.len() <= MAX_DEPTH, base as nat + path_length <= MAX_DEPTH, done <= path_length,
                    cursor == if done < path_length { path[done as int] } else { anchor },
                    model::depth_prefix(old_depths, depths@, path, base, done as nat),
                decreases path_length - done,
            {
                proof { model::path_successor(table.view().parents, path, number, anchor, done as nat); }
                let next = table.parent(cursor).unwrap();
                proof { model::assign_next_depth(old_depths, depths@, path, base, done as nat); }
                depths.set(cursor as usize, base + (path_length - done));
                cursor = next;
                done += 1;
            }
            proof { model::full_depth_assignment_has_parent_ranks(table.view().parents, old_colors, old_depths, colors@, depths@, path, number, anchor, base); }
            proof { model::gathered_path_starts_resolution(old_colors, colors@, path); }
            done = 0;
            cursor = number;
            assert(path[0] == number) by { reveal(model::path_chain); }
            while done < path_length
                invariant table.wf(), model::shape(table.view().parents), capacity == table.view().parents.len(),
                    bounded_rooted(table.view().parents) ==> rank_witness(table.view().parents, witness),
                    3 <= capacity <= block_claims::MAX_BLOCKS as nat + 1, anchor < capacity, old_colors.len() == capacity,
                    colors.len() == capacity, depths.len() == capacity,
                    model::no_pending(old_colors), model::closed(table.view().parents, old_colors), old_colors[anchor as int] == 2,
                    model::processed(table.view().parents, old_colors, number as nat),
                    model::path_chain(table.view().parents, path, number, anchor), path.no_duplicates(),
                    model::ranked(table.view().parents, colors@, depths@), model::path_ranked(table.view().parents, depths@, path),
                    0 < path_length == path.len() <= MAX_DEPTH, done <= path_length,
                    cursor == if done < path_length { path[done as int] } else { anchor },
                    model::resolved_prefix(old_colors, colors@, path, done as nat),
                decreases path_length - done,
            {
                proof { model::path_successor(table.view().parents, path, number, anchor, done as nat); }
                let next = table.parent(cursor).unwrap();
                proof { model::resolve_next_node(table.view().parents, old_colors, colors@, depths@, path, done as nat); }
                colors.set(cursor as usize, 2u8);
                cursor = next;
                done += 1;
            }
            proof { model::completed_path_restores_closed_resolution(table.view().parents, old_colors, colors@, path, number, anchor); }
            assert(colors[number as int] == 2) by { reveal(model::path_chain); reveal(model::resolved_prefix); }
            assert(model::processed(table.view().parents, colors@, number as nat)) by {
                reveal(model::processed);
                assert forall|n: u32| n < number && model::active(table.view().parents, n as int) implies (#[trigger] colors@[n as int]) == 2 by {
                    assert(old_colors[n as int] == 2);
                }
            }
        }
        assert(is_directory ==> colors[number as int] == 2) by { reveal(model::no_pending); }
        assert(model::processed(table.view().parents, colors@, number as nat + 1)) by {
            reveal(model::processed);
            assert forall|n: u32| n < number as nat + 1 && model::active(table.view().parents, n as int) implies (#[trigger] colors@[n as int]) == 2 by {
                if n < number { assert(colors@[n as int] == 2); }
            }
        }
        number += 1;
    }
    let ghost assembled = TreeView { index: table.view().index, parents: table.view().parents, depths: depths@ };
    assert(valid(assembled)) by {
        reveal(valid); reveal(model::processed); reveal(model::ranked);
        assert forall|n: int| model::active(table.view().parents, n) implies #[trigger] model::node_rank(table.view().parents, depths@, n) by {
            assert(0 <= n < capacity && n as u32 as int == n);
            assert(colors@[n as u32 as int] == 2);
        }
        assert forall|n: int| 0 <= n < depths.len() && !model::active(table.view().parents, n) implies #[trigger] depths@[n] == 0 by {
            assert(colors@[n] == 0);
        }
    }
    proof { every_valid_tree_has_a_bounded_rank_witness(assembled); }
    Some(Tree { table, depths })
}


/// Local graph admission over the complete, already captured directory index.
/// Entry counts and parents are declarative source projections.
#[verifier::opaque]
pub open spec fn admissible(index: IndexView) -> bool {
    parent_table::admissible(index) && bounded_rooted(parent_table::parent_projection(index))
}

pub fn build(index: &DirectoryIndex<'_>) -> (r: Option<Tree>)
    ensures index.wf(), match r {
        Some(tree) => tree.wf() && valid(tree.view()) && tree.view().index == index.view()
            && admissible(index.view())
            && tree.view().parents == parent_table::parent_projection(index.view()),
        None => !admissible(index.view()),
    },
{
    let table = match parent_table::build(index) {
        Some(table) => table,
        None => { proof { reveal(admissible); } return None; }
    };
    match build_parent_table(table) {
        Some(tree) => { proof { reveal(admissible); } Some(tree) },
        None => { proof { reveal(admissible); } None },
    }
}


/// Soundness and acceptance completeness use the same mathematical graph
/// property. The witness is the tree's exact computed depths on success.
pub proof fn every_valid_tree_has_a_bounded_rank_witness(v: TreeView)
    requires valid(v),
    ensures bounded_rooted(v.parents), rank_witness(v.parents, v.depths),
{
    reveal(valid); reveal(rank_witness); reveal(bounded_rooted);
    assert(exists|ranks: Seq<u32>| rank_witness(v.parents, ranks)) by {
        assert(rank_witness(v.parents, v.depths));
    }
}

pub proof fn every_source_directory_reaches_root(v: TreeView, number: u32)
    requires valid(v), crate::ea_namespace_nodes::is_directory(v.index.nodes, number),
    ensures walk(v.parents, number, v.depths[number as int] as nat) == 2,
{
    reveal(valid); reveal(parent_table::valid);
    assert(model::active(v.parents, number as int));
    every_directory_reaches_root(v, number);
}

pub proof fn positive_namespace_reference_counts_have_a_source_entry(entries: Seq<crate::namespace_model::EntryView>, count: nat, number: u32)
    requires count <= entries.len(), crate::namespace_counts::fold(entries, count, number).references > 0,
    ensures exists|i: int| 0 <= i < count && (#[trigger] entries[i]).target == number,
    decreases count,
{
    reveal(crate::namespace_counts::fold);
    if count == 0 {
        assert(crate::namespace_counts::fold(entries, count, number).references == 0);
        assert(false);
    } else {
        let last = count as int - 1;
        if entries[last].target == number {
            assert(exists|i: int| 0 <= i < count && (#[trigger] entries[i]).target == number);
        } else {
            assert(crate::namespace_counts::fold(entries, (count - 1) as nat, number).references > 0);
            positive_namespace_reference_counts_have_a_source_entry(entries, (count - 1) as nat, number);
            let i = choose|i: int| 0 <= i < count - 1 && (#[trigger] entries[i]).target == number;
            assert(exists|j: int| 0 <= j < count && (#[trigger] entries[j]).target == number);
        }
    }
}

// Keep the local source-node and entry checks in separate proof contexts.
// Revealing the complete directory catalogue in the main existential proof
// would introduce unrelated recursive enumeration facts.
proof fn checked_regular_inode_has_a_positive_namespace_reference(v: TableView, number: u32)
    requires parent_table::valid(v), crate::ea_namespace_nodes::active(v.index.nodes, number),
        v.index.nodes.slots[number as int].mode & 0xf000 == 0x8000,
    ensures crate::namespace_counts::fold(v.index.entries, v.index.entries.len(), number).references > 0,
{
    parent_table::every_active_namespace_inode_has_its_linux_link_count(v, number);
    assert(crate::ea_namespace_nodes::valid(v.index.nodes)) by {
        reveal(parent_table::valid); reveal(crate::ea_directory_index::valid);
    }
    crate::ea_namespace_nodes::ordinary_namespace_nodes_have_positive_links_and_supported_types(v.index.nodes, number);
    assert(v.index.nodes.slots[number as int].links > 0);
}

proof fn checked_regular_reference_is_a_named_directory_entry(v: TreeView, number: u32, i: int)
    requires valid(v), crate::ea_namespace_nodes::active(v.index.nodes, number),
        v.index.nodes.slots[number as int].mode & 0xf000 == 0x8000,
        0 <= i < v.index.entries.len(), v.index.entries[i].target == number,
    ensures v.index.entries[i].file_type == 1,
        crate::ea_namespace_nodes::is_directory(v.index.nodes, v.index.entries[i].directory),
        !crate::namespace_counts::is_dot(v.index.entries[i].name),
        !crate::namespace_counts::is_dotdot(v.index.entries[i].name),
{
    let e = v.index.entries[i];
    assert(crate::ea_directory_index::entry_ok(v.index, e)) by {
        reveal(valid); reveal(parent_table::valid); reveal(crate::ea_directory_index::valid);
    }
    assert(crate::namespace_counts::dot_ok(e)) by {
        reveal(valid); reveal(parent_table::valid); reveal(crate::namespace_counts::dots_valid);
    }
    assert(e.file_type == 1);
    assert(crate::ea_namespace_nodes::is_directory(v.index.nodes, e.directory));
    assert(!crate::namespace_counts::is_dot(e.name) && !crate::namespace_counts::is_dotdot(e.name));
}

pub proof fn every_source_regular_file_has_a_rooted_namespace_entry(v: TreeView, number: u32)
    requires valid(v), crate::ea_namespace_nodes::active(v.index.nodes, number),
        v.index.nodes.slots[number as int].mode & 0xf000 == 0x8000,
    ensures exists|i: int| 0 <= i < v.index.entries.len()
        && (#[trigger] v.index.entries[i]).target == number
        && v.index.entries[i].file_type == 1
        && !crate::namespace_counts::is_dot(v.index.entries[i].name)
        && !crate::namespace_counts::is_dotdot(v.index.entries[i].name)
        && walk(v.parents, v.index.entries[i].directory,
            v.depths[v.index.entries[i].directory as int] as nat) == 2,
{
    let table = parent_table::TableView { index: v.index, parents: v.parents };
    assert(parent_table::valid(table)) by { reveal(valid); }
    checked_regular_inode_has_a_positive_namespace_reference(table, number);
    positive_namespace_reference_counts_have_a_source_entry(v.index.entries, v.index.entries.len(), number);
    let i = choose|i: int| 0 <= i < v.index.entries.len() && (#[trigger] v.index.entries[i]).target == number;
    checked_regular_reference_is_a_named_directory_entry(v, number, i);
    let e = v.index.entries[i];
    every_source_directory_reaches_root(v, e.directory);
    assert(exists|j: int| 0 <= j < v.index.entries.len()
        && (#[trigger] v.index.entries[j]).target == number
        && v.index.entries[j].file_type == 1
        && !crate::namespace_counts::is_dot(v.index.entries[j].name)
        && !crate::namespace_counts::is_dotdot(v.index.entries[j].name)
        && walk(v.parents, v.index.entries[j].directory,
            v.depths[v.index.entries[j].directory as int] as nat) == 2);
}

}
