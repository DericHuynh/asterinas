// SPDX-License-Identifier: MPL-2.0

//! Rooted parent-graph validation with bounded, nonrecursive execution.
//! Each new path is marked, assigned depths, then resolved. Ghost path
//! certificates prove coverage; no runtime path stack is allocated.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{block_claims, parent_table::{self, ParentTable, TableView}, tree_model::{self as model, MAX_DEPTH}};

verus! {

pub struct TreeView { pub table: TableView, pub depths: Seq<u32> }

#[verifier::opaque]
pub open spec fn valid(v: TreeView) -> bool {
    &&& parent_table::valid(v.table) && model::shape(v.table.parents)
    &&& v.depths.len() == v.table.parents.len()
    &&& forall|n: int| model::active(v.table.parents, n) ==> #[trigger] model::node_rank(v.table.parents, v.depths, n)
    &&& forall|n: int| 0 <= n < v.depths.len() && !model::active(v.table.parents, n) ==> #[trigger] v.depths[n] == 0
}

pub open spec fn walk(parents: Seq<u32>, number: u32, count: nat) -> u32
    decreases count,
{
    if count == 0 { number } else { walk(parents, parents[number as int], (count - 1) as nat) }
}

pub proof fn every_directory_reaches_root(v: TreeView, number: u32)
    requires valid(v), model::active(v.table.parents, number as int),
    ensures walk(v.table.parents, number, v.depths[number as int] as nat) == 2,
    decreases v.depths[number as int],
{
    reveal(valid); reveal(model::shape);
    assert(model::node_rank(v.table.parents, v.depths, number as int));
    if number != 2 {
        let parent = v.table.parents[number as int];
        assert(model::node_rank(v.table.parents, v.depths, parent as int));
        every_directory_reaches_root(v, parent);
    }
}

pub struct Tree { table: ParentTable, depths: Vec<u32> }

impl Tree {
    pub closed spec fn view(&self) -> TreeView { TreeView { table: self.table.view(), depths: self.depths@ } }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn depth(&self, number: u32) -> (r: Option<u32>)
        ensures self.wf(), match r {
            Some(depth) => model::active(self.view().table.parents, number as int) && depth == self.view().depths[number as int]
                && depth <= MAX_DEPTH && (number == 2 <==> depth == 0),
            None => !model::active(self.view().table.parents, number as int),
        },
    {
        proof { use_type_invariant(self); reveal(valid); }
        match self.table.parent(number) {
            None => None,
            Some(_) => {
                assert(model::node_rank(self.view().table.parents, self.view().depths, number as int));
                Some(self.depths[number as usize])
            },
        }
    }

    pub fn parent(&self, number: u32) -> (r: Option<u32>)
        ensures self.wf(), match r {
            Some(parent) => model::active(self.view().table.parents, number as int) && parent == self.view().table.parents[number as int],
            None => !model::active(self.view().table.parents, number as int),
        },
    {
        proof { use_type_invariant(self); }
        self.table.parent(number)
    }
}

pub fn build(table: ParentTable) -> (r: Option<Tree>)
    ensures match r { Some(tree) => tree.wf() && tree.view().table == table.view(), None => true },
{
    let capacity = table.len() as u32;
    proof { model::checked_parent_table_has_graph_shape(table.view()); }
    let mut colors = Vec::<u8>::new();
    let mut depths = Vec::<u32>::new();
    let mut i = 0u32;
    while i < capacity
        invariant table.wf(), model::shape(table.view().parents), capacity == table.view().parents.len(),
            3 <= capacity <= block_claims::MAX_BLOCKS as nat + 1, i <= capacity, colors.len() == i, depths.len() == i,
            forall|n: int| 0 <= n < i ==> (#[trigger] colors@[n]) == 0 && depths@[n] == 0,
        decreases capacity - i,
    {
        colors.push(0);
        depths.push(0);
        i += 1;
    }
    assert(colors@[2] == 0 && depths@[2] == 0);
    colors.set(2, 2u8);
    assert forall|n: int| 0 <= n < colors.len() implies ((#[trigger] colors@[n]) == (if n == 2 { 2u8 } else { 0u8 }))
        && depths@[n] == 0 by { }
    assert(colors@[2] == 2 && depths@[2] == 0);
    assert(model::node_rank(table.view().parents, depths@, 2)) by { reveal(model::shape); }
    assert(model::ranked(table.view().parents, colors@, depths@)) by { reveal(model::ranked); reveal(model::shape); }
    assert(model::closed(table.view().parents, colors@)) by { reveal(model::closed); reveal(model::shape); }
    assert(model::no_pending(colors@)) by { reveal(model::no_pending); }
    assert(model::processed(table.view().parents, colors@, 0)) by { reveal(model::processed); }
    let mut number = 0u32;
    while number < capacity
        invariant table.wf(), model::shape(table.view().parents), capacity == table.view().parents.len(),
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
                    3 <= capacity <= block_claims::MAX_BLOCKS as nat + 1,
                    colors.len() == capacity, depths@ == old_depths, old_depths.len() == capacity, old_colors.len() == capacity,
                    model::ranked(table.view().parents, old_colors, old_depths), model::closed(table.view().parents, old_colors), model::no_pending(old_colors),
                    model::processed(table.view().parents, old_colors, number as nat),
                    model::path_chain(table.view().parents, path, number, cursor), model::gathered(old_colors, colors@, path),
                    model::active(table.view().parents, cursor as int), path_length == path.len(), path_length <= MAX_DEPTH,
                decreases MAX_DEPTH - path_length,
            {
                if path_length == MAX_DEPTH { return None; }
                let next = table.parent(cursor).unwrap();
                let ghost previous = colors@;
                proof { model::append_fresh_path_node(table.view().parents, old_colors, previous, path, number, cursor, next); }
                colors.set(cursor as usize, 1u8);
                proof { path = path.push(cursor); }
                path_length += 1;
                cursor = next;
            }
            if colors[cursor as usize] != 2 || path_length == 0 { return None; }
            let anchor = cursor;
            let base = depths[anchor as usize];
            assert(old_colors[anchor as int] == 2 && !path.contains(anchor)) by { reveal(model::gathered); }
            if base > MAX_DEPTH - path_length { return None; }
            let mut done = 0u32;
            cursor = number;
            assert(path[0] == number && path.no_duplicates()) by { reveal(model::path_chain); }
            assert(model::depth_prefix(old_depths, depths@, path, base, 0)) by { reveal(model::depth_prefix); reveal(model::path_chain); }
            while done < path_length
                invariant table.wf(), model::shape(table.view().parents), capacity == table.view().parents.len(),
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
    let ghost assembled = TreeView { table: table.view(), depths: depths@ };
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
    Some(Tree { table, depths })
}

}
