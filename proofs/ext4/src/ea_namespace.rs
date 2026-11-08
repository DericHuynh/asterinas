// SPDX-License-Identifier: MPL-2.0

//! Static namespace admission over the unchanged EA-enabled source image.
//! Complete directory names, ordinary targets, link counts and rootedness
//! retain the physical allocation certificate. Mounted permissions, writes,
//! recovery composition and CortenMM/OSTD source refinement remain separate.

use vstd::prelude::*;
use crate::{ea_allocation::{self, Allocation, AllocationView},
    ea_directory_index::{self, DirectoryIndex, Entry, IndexView},
    ea_namespace_nodes as nodes, ea_namespace_topology::{self as topology, Tree, TreeView},
    namespace_model, snapshot::Snapshot, tree_model};

verus! {

pub struct NamespaceView { pub allocation: AllocationView, pub index: IndexView, pub tree: TreeView }
#[verifier::opaque]
pub open spec fn valid(v: NamespaceView) -> bool {
    &&& ea_allocation::valid(v.allocation) && ea_directory_index::valid(v.index) && topology::valid(v.tree)
    &&& v.index.volume == v.allocation && v.tree.index == v.index
}

pub struct Namespace<'s, 'a> { allocation: Allocation<'s, 'a>, index: DirectoryIndex<'a>, tree: Tree }
impl<'s, 'a> Namespace<'s, 'a> {
    pub closed spec fn view(&self) -> NamespaceView {
        NamespaceView { allocation: self.allocation.view(), index: self.index.view(), tree: self.tree.view() }
    }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn allocation(&self) -> (r: &Allocation<'s, 'a>)
        ensures self.wf(), valid(self.view()), r.wf(), ea_allocation::valid(r.view()), r.view() == self.view().allocation,
    { proof { use_type_invariant(self); reveal(valid); } let _ = self.allocation.ordinary_count(); &self.allocation }
    pub fn index(&self) -> (r: &DirectoryIndex<'a>)
        ensures self.wf(), valid(self.view()), r.wf(), ea_directory_index::valid(r.view()), r.view() == self.view().index,
    { proof { use_type_invariant(self); reveal(valid); } let _ = self.index.len(); &self.index }
    pub fn lookup(&self, directory: u32, name: &[u8]) -> (r: Option<&Entry>)
        ensures self.wf(), valid(self.view()), match r {
            Some(e) => self.view().index.entries.contains(e.view()) && e.view().directory == directory
                && e.view().name == name@ && ea_directory_index::entry_ok(self.view().index, e.view()),
            None => !namespace_model::has_name(self.view().index.entries, directory, name@)
                && !ea_directory_index::source_has_name(self.view().index, directory, name@),
        },
    { proof { use_type_invariant(self); } self.index.lookup(directory, name) }
    pub fn parent(&self, number: u32) -> (r: Option<u32>)
        ensures self.wf(), valid(self.view()), match r {
            Some(parent) => tree_model::active(self.view().tree.parents, number as int)
                && parent == self.view().tree.parents[number as int],
            None => !tree_model::active(self.view().tree.parents, number as int),
        },
    { proof { use_type_invariant(self); } self.tree.parent(number) }
    pub fn depth(&self, number: u32) -> (r: Option<u32>)
        ensures self.wf(), valid(self.view()), match r {
            Some(depth) => tree_model::active(self.view().tree.parents, number as int)
                && depth == self.view().tree.depths[number as int] && depth <= tree_model::MAX_DEPTH && (number == 2 <==> depth == 0),
            None => !tree_model::active(self.view().tree.parents, number as int),
        },
    { proof { use_type_invariant(self); } self.tree.depth(number) }
}

pub fn inspect_journal<'s, 'a>(source: &'s Snapshot<'a>, inode_budget: u32, node_budget: u64, byte_budget: u64)
    -> (r: Option<Namespace<'s, 'a>>)
    ensures match r { Some(namespace) => namespace.wf() && valid(namespace.view())
        && namespace.view().allocation.integrity.references.index.header.source == source.view()
        && namespace.view().allocation.integrity.inode_budget == inode_budget
        && namespace.view().allocation.integrity.node_budget == node_budget
        && namespace.view().allocation.integrity.byte_budget == byte_budget, None => true },
{
    let allocation = match ea_allocation::inspect(source, inode_budget, node_budget, byte_budget) {
        Some(allocation) => allocation, None => { return None; }
    };
    let index = match ea_directory_index::build(&allocation) { Some(index) => index, None => { return None; } };
    let tree = match topology::build(&index) { Some(tree) => tree, None => { return None; } };
    let ghost assembled = NamespaceView { allocation: allocation.view(), index: index.view(), tree: tree.view() };
    assert(valid(assembled)) by { reveal(valid); }
    Some(Namespace { allocation, index, tree })
}

/// Clean-image namespace inspection for volatile mutation preparation.
pub fn inspect<'s, 'a>(source: &'s Snapshot<'a>, inode_budget: u32, node_budget: u64, byte_budget: u64)
    -> (r: Option<Namespace<'s, 'a>>)
    ensures match r { Some(namespace) => namespace.wf() && valid(namespace.view())
        && namespace.view().allocation.integrity.references.index.header.source == source.view()
        && namespace.view().allocation.integrity.inode_budget == inode_budget
        && namespace.view().allocation.integrity.node_budget == node_budget
        && namespace.view().allocation.integrity.byte_budget == byte_budget
        && !crate::super_state::is_dirty(source.view()), None => true },
{
    let primary = match source.block(0) { Some(block) => block, None => { return None; } };
    let flags = match crate::bytes::read_le32(primary.as_slice(), 1120) {
        Some(flags) => flags, None => { return None; }
    };
    if flags & 4u32 != 0 { return None; }
    proof {
        assert(crate::bytes::le32(source.view(), 1120)
            == crate::bytes::le32(primary.bytes(), 1120));
    }
    inspect_journal(source, inode_budget, node_budget, byte_budget)
}

pub(crate) proof fn allocation_facts(v: NamespaceView)
    requires valid(v),
    ensures ea_allocation::valid(v.allocation),
        crate::ea_journal::valid(v.allocation.journal),
        v.allocation.journal.index == v.allocation.integrity.references.index,
        crate::ea_index::valid(v.allocation.integrity.references.index),
        crate::ea_source::header_valid(v.allocation.integrity.references.index.header),
        0 < v.allocation.integrity.references.index.groups.len(),
{
    hide(crate::crc::fold);
    reveal(valid);
    reveal(ea_allocation::valid);
    reveal(crate::ea_journal::valid);
    reveal(crate::ea_index::valid);
}

/// Link the existing full namespace certificate to the independent complete
/// stage profiles. This implication does not claim raw filesystem acceptance.
pub proof fn every_valid_namespace_satisfies_the_complete_stage_profiles(v: NamespaceView)
    requires valid(v),
    ensures crate::ea_source::source_admissible(v.allocation.integrity.references.index.header.source),
        crate::ea_index::admissible(v.allocation.integrity.references.index.header),
        crate::ea_namespace_counts::admissible(v.index),
        crate::ea_namespace_parent::admissible(v.index),
        topology::admissible(v.index),
{
    allocation_facts(v);
    crate::ea_index::every_declaratively_valid_index_is_admissible(v.allocation.integrity.references.index);
    crate::ea_source::every_valid_header_is_the_unique_source_projection(v.allocation.integrity.references.index.header);
    assert(topology::valid(v.tree) && v.tree.index == v.index) by { reveal(valid); }
    let table = crate::ea_namespace_parent::TableView { index: v.index, parents: v.tree.parents };
    assert(crate::ea_namespace_parent::valid(table)) by { reveal(topology::valid); }
    crate::ea_namespace_parent::parent_table_validity_characterizes_admission(table);
    topology::every_valid_tree_has_a_bounded_rank_witness(v.tree);
    reveal(crate::ea_namespace_parent::admissible);
    reveal(topology::admissible);
}

pub proof fn every_source_directory_is_rooted(v: NamespaceView, number: u32)
    requires valid(v), nodes::is_directory(v.index.nodes, number),
    ensures topology::walk(v.tree.parents, number, v.tree.depths[number as int] as nat) == 2,
{ reveal(valid); topology::every_source_directory_reaches_root(v.tree, number); }

pub proof fn namespace_targets_retain_the_source_inode_generation(v: NamespaceView, entry: int)
    requires valid(v), 0 <= entry < v.index.entries.len(),
    ensures nodes::active(v.index.nodes, v.index.entries[entry].target),
        v.index.entries[entry].generation as nat == crate::bytes::le32(
            v.allocation.ordinary[v.index.nodes.slots[v.index.entries[entry].target as int].ordinal as int].parent.node.raw, 100),
{
    reveal(valid); reveal(ea_directory_index::valid);
    assert(ea_directory_index::typed_node_entry(v.index.nodes, v.index.entries[entry]));
    nodes::namespace_node_generations_are_the_exact_source_inode_generation(v.index.nodes, v.index.entries[entry].target);
}

pub proof fn namespace_ea_values_and_journal_are_not_ordinary_targets(v: NamespaceView, value: int)
    requires valid(v), 0 <= value < v.allocation.integrity.values.len(),
    ensures !nodes::active(v.index.nodes, 8),
        !nodes::active(v.index.nodes, v.allocation.integrity.values[value].info.number),
{
    reveal(valid); reveal(ea_directory_index::valid);
    nodes::journal_and_reserved_slots_have_no_namespace_node(v.index.nodes, 8);
    nodes::ea_value_inodes_have_no_namespace_node(v.index.nodes, value);
}

pub proof fn absence_from_the_namespace_catalogue_is_actual_source_absence(v: NamespaceView, directory: u32, name: Seq<u8>)
    requires valid(v), !namespace_model::has_name(v.index.entries, directory, name),
    ensures !ea_directory_index::source_has_name(v.index, directory, name),
{ reveal(valid); ea_directory_index::no_catalogue_name_means_no_live_source_name(v.index, directory, name); }

}
