// SPDX-License-Identifier: MPL-2.0

//! Link counts and unique directory parents from complete source entries.
//! A locally consistent parent table can still contain a disconnected cycle;
//! rootedness/depth validation is deliberately a separate layer.

use vstd::prelude::*;
use crate::{allocated_inode, block_claims, directory_index::{self, DirectoryIndex, IndexView},
    namespace_counts as counts, namespace_model as model};

verus! {

#[verifier::opaque]
pub open spec fn node_ok(index: IndexView, n: u32) -> bool {
    let slot = counts::fold(index.entries, index.entries.len(), n);
    let node = allocated_inode::source_view(index.volume, n);
    if !allocated_inode::live(index.volume.index, n) { slot.references == 0 }
    else {
        &&& crate::link_count::matches(node.mode, node.links, slot.references, crate::feature_policy::dir_nlink(index.volume.index.source.subrange(1024, 2048)))
        &&& if model::is_directory(index.volume, n) {
            &&& slot.dots == 1 && slot.dotdots == 1
            &&& if n == 2 { slot.parent == 2 && slot.incoming == 0 }
                else { slot.incoming == 1 && slot.named_parent > 0 && slot.parent == slot.named_parent }
            &&& model::is_directory(index.volume, slot.parent)
        } else { true }
    }
}

#[verifier::opaque]
pub open spec fn nodes_ok(index: IndexView, count: nat) -> bool {
    forall|n: u32| n < count ==> #[trigger] node_ok(index, n)
}

#[verifier::opaque]
pub open spec fn parents_match(index: IndexView, parents: Seq<u32>) -> bool {
    forall|n: u32| n < parents.len() ==> #[trigger] parents[n as int] == if model::is_directory(index.volume, n) {
        counts::fold(index.entries, index.entries.len(), n).parent
    } else { 0u32 }
}

proof fn checked_directory_has_a_live_parent(index: IndexView, n: u32)
    requires node_ok(index, n), model::is_directory(index.volume, n),
    ensures 0 < counts::fold(index.entries, index.entries.len(), n).parent <= index.volume.index.inodes,
        model::is_directory(index.volume, counts::fold(index.entries, index.entries.len(), n).parent),
{
    reveal(node_ok);
}

pub struct TableView { pub index: IndexView, pub parents: Seq<u32> }

#[verifier::opaque]
pub open spec fn valid(v: TableView) -> bool {
    &&& directory_index::valid(v.index) && model::is_directory(v.index.volume, 2)
    &&& v.parents.len() == v.index.volume.index.inodes as nat + 1 && 3 <= v.parents.len() <= block_claims::MAX_BLOCKS as nat + 1
    &&& counts::dots_valid(v.index.entries, v.index.entries.len())
    &&& nodes_ok(v.index, v.parents.len()) && parents_match(v.index, v.parents)
    &&& v.parents[2] == 2
    &&& forall|n: int| 0 <= n < v.parents.len() ==> ((#[trigger] v.parents[n]) != 0 <==> model::is_directory(v.index.volume, n as u32))
    &&& forall|n: int| 0 <= n < v.parents.len() && (#[trigger] v.parents[n]) != 0 ==>
        0 < v.parents[n] < v.parents.len() && v.parents[v.parents[n] as int] != 0
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

pub fn build(index: &DirectoryIndex<'_, '_>) -> (r: Option<ParentTable>)
    ensures index.wf(), match r { Some(table) => table.wf() && table.view().index == index.view(), None => true },
{
    let volume = index.volume();
    let (_, inodes, _, _) = volume.index().parameters();
    if inodes > block_claims::MAX_BLOCKS { return None; }
    let root = match allocated_inode::get(volume, 2) { Some(root) => root, None => { return None; } };
    if root.info().mode & 0xf000 != 0x4000 { return None; }
    proof { allocated_inode::checked_view_is_the_source_projection(root.view()); }
    assert(model::is_directory(index.view().volume, 2)) by { reveal(allocated_inode::valid); }
    assert(volume.view().index.source.len() >= 4096) by { reveal(crate::allocation::valid); reveal(crate::group_index::valid); }
    let primary = volume.index().source().block(0).unwrap();
    let raw_primary = primary.range(1024, 1024).unwrap();
    assert(raw_primary@ =~= index.view().volume.index.source.subrange(1024, 2048));
    let nlink_feature = crate::feature_policy::has_dir_nlink(raw_primary).unwrap();
    let counts = match counts::collect(index) { Some(counts) => counts, None => { return None; } };
    let capacity = inodes as u32 + 1;
    assert(counts.view().slots.len() == capacity) by { reveal(counts::valid); }
    let mut parents = Vec::<u32>::new();
    let mut number = 0u32;
    assert(nodes_ok(index.view(), 0)) by { reveal(nodes_ok); }
    assert(parents_match(index.view(), parents@)) by { reveal(parents_match); }
    while number < capacity
        invariant index.wf(), volume.view() == index.view().volume, inodes == index.view().volume.index.inodes,
            capacity as nat == inodes as nat + 1, inodes <= block_claims::MAX_BLOCKS,
            number <= capacity, parents.len() == number,
            counts.wf(), counts.view().index == index.view(), counts.view().slots.len() == capacity,
            nlink_feature == crate::feature_policy::dir_nlink(index.view().volume.index.source.subrange(1024, 2048)),
            model::is_directory(index.view().volume, 2),
            nodes_ok(index.view(), number as nat), parents_match(index.view(), parents@),
        decreases capacity - number,
    {
        let slot = counts.get(number).unwrap();
        assert(slot.view() == counts::fold(index.view().entries, index.view().entries.len(), number)) by {
            reveal(counts::valid); reveal(counts::matching);
        }
        let mut parent = 0u32;
        match allocated_inode::get(volume, number) {
            Some(node) => {
                proof { allocated_inode::checked_view_is_the_source_projection(node.view()); }
                let info = node.info();
                if !crate::link_count::agrees(info.mode, info.links, slot.references, nlink_feature) { return None; }
                if info.mode & 0xf000 == 0x4000 {
                    if slot.dots != 1 || slot.dotdots != 1 { return None; }
                    if number == 2 {
                        if slot.parent != 2 || slot.incoming != 0 { return None; }
                    } else if slot.incoming != 1 || slot.named_parent == 0 || slot.parent != slot.named_parent { return None; }
                    let up = match allocated_inode::get(volume, slot.parent) { Some(up) => up, None => { return None; } };
                    if up.info().mode & 0xf000 != 0x4000 { return None; }
                    proof { allocated_inode::checked_view_is_the_source_projection(up.view()); }
                    assert(model::is_directory(index.view().volume, slot.parent)) by { reveal(allocated_inode::valid); }
                    parent = slot.parent;
                }
                assert(parent == if model::is_directory(index.view().volume, number) { slot.parent } else { 0u32 })
                    by { reveal(allocated_inode::valid); }
                assert(node_ok(index.view(), number)) by { reveal(node_ok); reveal(allocated_inode::valid); }
            },
            None => {
                if slot.references != 0 { return None; }
                assert(!model::is_directory(index.view().volume, number));
                assert(node_ok(index.view(), number)) by { reveal(node_ok); }
            }
        }
        assert(parent == if model::is_directory(index.view().volume, number) {
            counts::fold(index.view().entries, index.view().entries.len(), number).parent
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
            assert forall|n: u32| n < parents.len() implies #[trigger] parents@[n as int] == if model::is_directory(index.view().volume, n) {
                counts::fold(index.view().entries, index.view().entries.len(), n).parent
            } else { 0u32 } by {
                if n < number {
                    assert(before[n as int] == if model::is_directory(index.view().volume, n) {
                        counts::fold(index.view().entries, index.view().entries.len(), n).parent
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
        assert forall|n: int| 0 <= n < parents.len() implies ((#[trigger] parents@[n]) != 0 <==> model::is_directory(index.view().volume, n as u32)) by {
            if model::is_directory(index.view().volume, n as u32) {
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

}
