// SPDX-License-Identifier: MPL-2.0

//! EA namespace link counts and unique directory parents from source entries.
//! A locally consistent parent table can still contain a disconnected cycle;
//! rootedness/depth validation is deliberately a separate layer.

use vstd::prelude::*;
use crate::{block_claims, ea_directory_index::{self as directory_index, DirectoryIndex, IndexView},
    ea_namespace_counts as counts, ea_namespace_nodes as nodes, namespace_counts as pure};

verus! {

#[verifier::opaque]
pub open spec fn node_ok(index: IndexView, n: u32) -> bool {
    let slot = pure::fold(index.entries, index.entries.len(), n);
    let node = index.nodes.slots[n as int];
    if !nodes::active(index.nodes, n) { slot.references == 0 }
    else {
        &&& crate::link_count::matches(node.mode, node.links, slot.references, crate::feature_policy::dir_nlink(index.volume.integrity.references.index.header.source.subrange(1024, 2048)))
        &&& if nodes::is_directory(index.nodes, n) {
            &&& slot.dots == 1 && slot.dotdots == 1
            &&& if n == 2 { slot.parent == 2 && slot.incoming == 0 }
                else { slot.incoming == 1 && slot.named_parent > 0 && slot.parent == slot.named_parent }
            &&& nodes::is_directory(index.nodes, slot.parent)
        } else { true }
    }
}

#[verifier::opaque]
pub open spec fn nodes_ok(index: IndexView, count: nat) -> bool {
    forall|n: u32| n < count ==> #[trigger] node_ok(index, n)
}

#[verifier::opaque]
pub open spec fn parents_match(index: IndexView, parents: Seq<u32>) -> bool {
    forall|n: u32| n < parents.len() ==> #[trigger] parents[n as int] == if nodes::is_directory(index.nodes, n) {
        pure::fold(index.entries, index.entries.len(), n).parent
    } else { 0u32 }
}

proof fn checked_directory_has_a_live_parent(index: IndexView, n: u32)
    requires node_ok(index, n), nodes::is_directory(index.nodes, n),
    ensures 0 < pure::fold(index.entries, index.entries.len(), n).parent < index.nodes.slots.len(),
        nodes::is_directory(index.nodes, pure::fold(index.entries, index.entries.len(), n).parent),
{
    reveal(node_ok);
}

pub struct TableView { pub index: IndexView, pub parents: Seq<u32> }

#[verifier::opaque]
pub open spec fn valid(v: TableView) -> bool {
    &&& directory_index::valid(v.index) && nodes::is_directory(v.index.nodes, 2)
    &&& v.parents.len() == v.index.nodes.slots.len() && 3 <= v.parents.len() <= block_claims::MAX_BLOCKS as nat + 1
    &&& pure::dots_valid(v.index.entries, v.index.entries.len())
    &&& nodes_ok(v.index, v.parents.len()) && parents_match(v.index, v.parents)
    &&& v.parents[2] == 2
    &&& (forall|n: int| 0 <= n < v.parents.len() ==> ((#[trigger] v.parents[n]) != 0 <==> nodes::is_directory(v.index.nodes, n as u32)))
    &&& (forall|n: int| 0 <= n < v.parents.len() && (#[trigger] v.parents[n]) != 0 ==>
        0 < v.parents[n] < v.parents.len() && v.parents[v.parents[n] as int] != 0)
}

pub struct ParentTable { index: Ghost<IndexView>, parents: Vec<u32> }

impl ParentTable {
    pub closed spec fn view(&self) -> TableView { TableView { index: self.index@, parents: self.parents@ } }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn len(&self) -> (r: usize) ensures self.wf(), r == self.view().parents.len(), 3 <= r <= block_claims::MAX_BLOCKS as nat + 1 {
        proof { use_type_invariant(self); reveal(valid); }
        self.parents.len()
    }

    pub fn parent(&self, number: u32) -> (r: Option<u32>)
        ensures self.wf(), match r {
            Some(parent) => number < self.view().parents.len() && parent == self.view().parents[number as int]
                && 0 < parent < self.view().parents.len() && self.view().parents[parent as int] != 0,
            None => number >= self.view().parents.len() || self.view().parents[number as int] == 0,
        },
    {
        proof { use_type_invariant(self); reveal(valid); }
        if number as usize >= self.parents.len() || self.parents[number as usize] == 0 { None }
        else { Some(self.parents[number as usize]) }
    }
}

pub fn build(index: &DirectoryIndex<'_>) -> (r: Option<ParentTable>)
    ensures index.wf(), match r { Some(table) => table.wf() && table.view().index == index.view(), None => true },
{
    let source_nodes = index.nodes();
    let length = source_nodes.len();
    if length < 3 || length > block_claims::MAX_BLOCKS as usize + 1 { return None; }
    let inodes = (length - 1) as u32;
    let root = match source_nodes.get(2) { Some(root) => root, None => { return None; } };
    if root.mode & 0xf000 != 0x4000 { return None; }
    assert(nodes::is_directory(index.view().nodes, 2));
    let nlink_feature = source_nodes.dir_nlink();
    assert(source_nodes.view().volume == index.view().volume) by {
        reveal(directory_index::valid);
    }
    assert(nlink_feature == crate::feature_policy::dir_nlink(index.view().volume.integrity.references.index.header.source.subrange(1024, 2048)));
    let counts = match counts::collect(index) { Some(counts) => counts, None => { return None; } };
    let capacity = inodes as u32 + 1;
    assert(counts.view().slots.len() == capacity) by { reveal(counts::valid); }
    let mut parents = Vec::<u32>::new();
    let mut number = 0u32;
    assert(nodes_ok(index.view(), 0)) by { reveal(nodes_ok); }
    assert(parents_match(index.view(), parents@)) by { reveal(parents_match); }
    while number < capacity
        invariant index.wf(), directory_index::valid(index.view()), source_nodes.wf(), source_nodes.view() == index.view().nodes,
            length == index.view().nodes.slots.len(), inodes as nat + 1 == length,
            capacity as nat == inodes as nat + 1, inodes <= block_claims::MAX_BLOCKS,
            number <= capacity, parents.len() == number,
            counts.wf(), counts.view().index == index.view(), counts.view().slots.len() == capacity,
            nlink_feature == crate::feature_policy::dir_nlink(index.view().volume.integrity.references.index.header.source.subrange(1024, 2048)),
            nodes::is_directory(index.view().nodes, 2),
            nodes_ok(index.view(), number as nat), parents_match(index.view(), parents@),
        decreases capacity - number,
    {
        let slot = counts.get(number).unwrap();
        assert(slot.view() == pure::fold(index.view().entries, index.view().entries.len(), number)) by {
            reveal(counts::valid); reveal(pure::matching);
        }
        let mut parent = 0u32;
        match source_nodes.get(number) {
            Some(info) => {
                if !crate::link_count::agrees(info.mode, info.links, slot.references, nlink_feature) { return None; }
                if info.mode & 0xf000 == 0x4000 {
                    if slot.dots != 1 || slot.dotdots != 1 { return None; }
                    if number == 2 {
                        if slot.parent != 2 || slot.incoming != 0 { return None; }
                    } else if slot.incoming != 1 || slot.named_parent == 0 || slot.parent != slot.named_parent { return None; }
                    let up = match source_nodes.get(slot.parent) { Some(up) => up, None => { return None; } };
                    if up.mode & 0xf000 != 0x4000 { return None; }
                    assert(nodes::is_directory(index.view().nodes, slot.parent));
                    parent = slot.parent;
                }
                assert(parent == if nodes::is_directory(index.view().nodes, number) { slot.parent } else { 0u32 });
                assert(node_ok(index.view(), number)) by { reveal(node_ok); }
            },
            None => {
                if slot.references != 0 { return None; }
                assert(!nodes::is_directory(index.view().nodes, number));
                assert(node_ok(index.view(), number)) by { reveal(node_ok); }
            }
        }
        assert(parent == if nodes::is_directory(index.view().nodes, number) {
            pure::fold(index.view().entries, index.view().entries.len(), number).parent
        } else { 0u32 });
        let ghost before = parents@;
        parents.push(parent);
        assert(nodes_ok(index.view(), number as nat + 1)) by {
            reveal(nodes_ok);
            assert forall|n: u32| n < number as nat + 1 implies #[trigger] node_ok(index.view(), n) by {
                if n < number { assert(node_ok(index.view(), n)); }
            }
        }
        assert(parents_match(index.view(), parents@)) by {
            reveal(parents_match);
            assert forall|n: u32| n < parents.len() implies #[trigger] parents@[n as int] == if nodes::is_directory(index.view().nodes, n) {
                pure::fold(index.view().entries, index.view().entries.len(), n).parent
            } else { 0u32 } by {
                if n < number {
                    assert(before[n as int] == if nodes::is_directory(index.view().nodes, n) {
                        pure::fold(index.view().entries, index.view().entries.len(), n).parent
                    } else { 0u32 });
                    assert(parents@[n as int] == before[n as int]);
                } else { assert(n == number && parents@[n as int] == parent); }
            }
        }
        number += 1;
    }
    let ghost assembled = TableView { index: index.view(), parents: parents@ };
    assert(valid(assembled)) by {
        reveal(valid); reveal(nodes_ok); reveal(parents_match); reveal(counts::valid);
        assert forall|n: int| 0 <= n < parents.len() implies ((#[trigger] parents@[n]) != 0 <==> nodes::is_directory(index.view().nodes, n as u32)) by {
            if nodes::is_directory(index.view().nodes, n as u32) {
                checked_directory_has_a_live_parent(index.view(), n as u32);
            }
        }
        assert forall|n: int| 0 <= n < parents.len() && (#[trigger] parents@[n]) != 0 implies
            0 < parents@[n] < parents.len() && parents@[parents@[n] as int] != 0 by {
            checked_directory_has_a_live_parent(index.view(), n as u32);
        }
        assert(node_ok(index.view(), 2));
        reveal(node_ok);
    }
    Some(ParentTable { index: Ghost(index.view()), parents })
}


pub proof fn every_active_namespace_inode_has_its_linux_link_count(v: TableView, number: u32)
    requires valid(v), nodes::active(v.index.nodes, number),
    ensures crate::link_count::matches(v.index.nodes.slots[number as int].mode, v.index.nodes.slots[number as int].links,
        pure::fold(v.index.entries, v.index.entries.len(), number).references,
        crate::feature_policy::dir_nlink(v.index.volume.integrity.references.index.header.source.subrange(1024, 2048))),
{
    reveal(valid); reveal(nodes_ok);
    assert(node_ok(v.index, number));
    reveal(node_ok);
}

pub proof fn non_namespace_inodes_have_no_directory_references(v: TableView, number: u32)
    requires valid(v), number < v.parents.len(), !nodes::active(v.index.nodes, number),
    ensures pure::fold(v.index.entries, v.index.entries.len(), number).references == 0,
{
    reveal(valid); reveal(nodes_ok);
    assert(node_ok(v.index, number));
    reveal(node_ok);
}

pub proof fn every_source_directory_has_matching_dot_and_named_parents(v: TableView, number: u32)
    requires valid(v), nodes::is_directory(v.index.nodes, number),
    ensures pure::fold(v.index.entries, v.index.entries.len(), number).dots == 1,
        pure::fold(v.index.entries, v.index.entries.len(), number).dotdots == 1,
        v.parents[number as int] == pure::fold(v.index.entries, v.index.entries.len(), number).parent,
        number == 2 ==> v.parents[number as int] == 2 && pure::fold(v.index.entries, v.index.entries.len(), number).incoming == 0,
        number != 2 ==> pure::fold(v.index.entries, v.index.entries.len(), number).incoming == 1
            && pure::fold(v.index.entries, v.index.entries.len(), number).named_parent == v.parents[number as int],
{
    reveal(valid); reveal(nodes_ok); reveal(parents_match);
    assert(node_ok(v.index, number));
    reveal(node_ok);
}

}
