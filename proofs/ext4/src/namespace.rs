// SPDX-License-Identifier: MPL-2.0

//! A complete namespace certificate over one immutable allocation/directory
//! image: exact names/targets, link counts, dot/parent rules and rootedness.
//! Recovery/mount admission, VFS credentials, operations and OSTD/device
//! refinement remain separate; this does not enable a mounted filesystem.

use vstd::prelude::*;
use crate::{directory_index::{self, DirectoryIndex, Entry, IndexView}, namespace_model as model,
    namespace_tree::{self, Tree, TreeView}, parent_table};

verus! {

pub struct NamespaceView { pub index: IndexView, pub tree: TreeView }

#[verifier::opaque]
pub open spec fn valid(v: NamespaceView) -> bool {
    &&& directory_index::valid(v.index) && namespace_tree::valid(v.tree)
    &&& v.tree.table.index == v.index
}

pub proof fn every_directory_is_rooted(v: NamespaceView, number: u32)
    requires valid(v), model::is_directory(v.index.volume, number),
    ensures namespace_tree::walk(v.tree.table.parents, number, v.tree.depths[number as int] as nat) == 2,
{
    reveal(valid); reveal(namespace_tree::valid); reveal(parent_table::valid);
    assert(crate::tree_model::active(v.tree.table.parents, number as int));
    namespace_tree::every_directory_reaches_root(v.tree, number);
}

pub struct Namespace<'n, 'v, 'a> { index: &'n DirectoryIndex<'v, 'a>, tree: Tree }

impl<'n, 'v, 'a> Namespace<'n, 'v, 'a> {
    pub closed spec fn view(&self) -> NamespaceView { NamespaceView { index: self.index.view(), tree: self.tree.view() } }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn index(&self) -> (r: &'n DirectoryIndex<'v, 'a>) ensures self.wf(), r.view() == self.view().index {
        proof { use_type_invariant(self); }
        self.index
    }

    pub fn lookup(&self, directory: u32, name: &[u8]) -> (r: Option<&Entry>)
        ensures self.wf(), match r {
            Some(e) => self.view().index.entries.contains(e.view()) && e.view().directory == directory && e.view().name == name@
                && model::entry_ok(self.view().index.volume, e.view()),
            None => !model::has_name(self.view().index.entries, directory, name@),
        },
    {
        proof { use_type_invariant(self); }
        self.index.lookup(directory, name)
    }

    pub fn parent(&self, number: u32) -> (r: Option<u32>)
        ensures self.wf(), match r {
            Some(parent) => crate::tree_model::active(self.view().tree.table.parents, number as int)
                && parent == self.view().tree.table.parents[number as int],
            None => !crate::tree_model::active(self.view().tree.table.parents, number as int),
        },
    {
        proof { use_type_invariant(self); }
        self.tree.parent(number)
    }

    pub fn depth(&self, number: u32) -> (r: Option<u32>)
        ensures self.wf(), match r {
            Some(depth) => crate::tree_model::active(self.view().tree.table.parents, number as int)
                && depth == self.view().tree.depths[number as int] && depth <= crate::tree_model::MAX_DEPTH && (number == 2 <==> depth == 0),
            None => !crate::tree_model::active(self.view().tree.table.parents, number as int),
        },
    {
        proof { use_type_invariant(self); }
        self.tree.depth(number)
    }
}

pub fn validate<'n, 'v, 'a>(index: &'n DirectoryIndex<'v, 'a>) -> (r: Option<Namespace<'n, 'v, 'a>>)
    ensures index.wf(), match r { Some(namespace) => namespace.wf() && namespace.view().index == index.view(), None => true },
{
    let _ = index.len();
    let table = match parent_table::build(index) { Some(table) => table, None => { return None; } };
    let tree = match namespace_tree::build(table) { Some(tree) => tree, None => { return None; } };
    let ghost assembled = NamespaceView { index: index.view(), tree: tree.view() };
    assert(valid(assembled)) by { reveal(valid); }
    Some(Namespace { index, tree })
}

}
