// SPDX-License-Identifier: MPL-2.0

//! Bounded, allocation-free cross-directory moves, regular hard links and
//! nonlast unlinks over complete EA-enabled host-image certificates.

use vstd::prelude::*;
use crate::{bytes, ea_directory::{self, DirectoryView}, ea_namespace::{self, NamespaceView},
    ea_source, feature_policy, inode, ns_dir_edit,
    ns_inode_links, ns_namespace_relation as relation, patch_set::{self, PatchSet},
    snapshot::Snapshot, transaction::ImageView};
pub use crate::ns_namespace_relation::Operation;

verus! {

pub const MAX_IMAGE_BYTES: usize = 268435456;
pub enum Error { Invalid, ReadOnly, NotFound, Exists, NoSpace, Rejected }

pub open spec fn certified(c: NamespaceView, source: Seq<u8>) -> bool {
    ea_namespace::valid(c) && c.allocation.integrity.references.index.header.source == source
}

pub struct InodeEditView { pub number:u32, pub ordinal:usize, pub position:u64, pub change:ns_inode_links::Change }
pub enum DirectoryChange {
    Insert(ns_dir_edit::InsertChange), Remove(ns_dir_edit::RemoveChange), DotDot(ns_dir_edit::DotDotChange),
}
pub struct DirectoryEditView { pub owner:u32, pub ordinal:usize, pub logical:u32, pub block:u32, pub change:DirectoryChange }
pub open spec fn directory_before(e: DirectoryEditView) -> crate::directory_piece::PieceView {
    match e.change { DirectoryChange::Insert(c) => c.before, DirectoryChange::Remove(c) => c.before, DirectoryChange::DotDot(c) => c.before }
}
pub open spec fn directory_after(e: DirectoryEditView) -> crate::directory_piece::PieceView {
    match e.change { DirectoryChange::Insert(c) => c.after, DirectoryChange::Remove(c) => c.after, DirectoryChange::DotDot(c) => c.after }
}
pub open spec fn inode_node(before:NamespaceView,e:InodeEditView)->ea_source::NodeView {
    before.allocation.ordinary[e.ordinal as int].parent.node
}
#[verifier::opaque]
pub open spec fn inode_bound(before:NamespaceView,e:InodeEditView)->bool {
    let node=inode_node(before,e);
    &&& ea_namespace::valid(before)
    &&& crate::ea_namespace_nodes::active(before.index.nodes,e.number)
    &&& e.ordinal==before.index.nodes.slots[e.number as int].ordinal
    &&& e.ordinal<before.allocation.ordinary.len()
    &&& ea_source::node_valid(node) && node.header==before.allocation.integrity.references.index.header
    &&& node.number==e.number && node.position==e.position
    &&& e.change.before==node.raw && e.change.number==e.number
    &&& e.change.inodes==node.header.inodes && e.change.seed==node.header.seed
    &&& e.change.huge==crate::ea_parent::huge(node.header)
    &&& ns_inode_links::valid(e.change)
}
pub open spec fn directory_source_matches(before:NamespaceView,e:DirectoryEditView,d:DirectoryView)->bool {
    &&& ea_directory::valid(d) && d.volume==before.allocation && d.ordinal==e.ordinal
    &&& ea_directory::owner(d)==e.owner
    &&& e.logical<d.pieces.len() && e.logical<d.physical.len()
    &&& e.block==d.physical[e.logical as int]
    &&& directory_before(e)==d.pieces[e.logical as int]
}
#[verifier::opaque]
pub open spec fn directory_bound(before:NamespaceView,e:DirectoryEditView)->bool {
    &&& ea_namespace::valid(before)
    &&& !directory_before(e).indexed
    &&& (exists|d:DirectoryView| #[trigger] directory_source_matches(before,e,d))
    &&& match e.change {
        DirectoryChange::Insert(c)=>ns_dir_edit::insert_valid(c),
        DirectoryChange::Remove(c)=>ns_dir_edit::remove_valid(c),
        DirectoryChange::DotDot(c)=>ns_dir_edit::dotdot_valid(c),
    }
}
pub struct UpdateView {
    pub source: Seq<u8>, pub result: Seq<u8>, pub before: NamespaceView, pub after: NamespaceView,
    pub operation: Operation, pub source_directory: u32, pub destination_directory: u32,
    pub old_name: Seq<u8>, pub new_name: Seq<u8>, pub target: u32, pub generation: u32, pub file_type: u8,
    pub source_parent_generation: u32, pub destination_parent_generation: u32,
    pub seconds: int, pub nanos: nat, pub patches: Seq<ImageView>,
    pub inode_edits: Seq<InodeEditView>, pub directory_edits: Seq<DirectoryEditView>,
    pub ancestry: Seq<u32>,
}
pub open spec fn exact_operation(v: UpdateView) -> bool {
    relation::relation(v.before.index.entries, v.after.index.entries, v.operation,
        v.source_directory, v.old_name, v.destination_directory, v.new_name,
        v.target, v.generation, v.file_type, v.source_parent_generation, v.destination_parent_generation)
}
#[verifier::opaque]
pub open spec fn requested_inode(v: UpdateView, e: InodeEditView) -> bool {
    let n = e.number;
    &&& inode_bound(v.before,e)
    &&& e.change.seconds == v.seconds && e.change.nanos == v.nanos
    &&& if n == v.target {
        !e.change.touch_mtime && e.change.delta == match v.operation { Operation::Rename => 0int, Operation::Link => 1int, Operation::Unlink => -1int }
    } else {
        e.change.touch_mtime && match v.operation {
            Operation::Rename => (n == v.source_directory && e.change.delta == if v.file_type == 2 { -1int } else { 0int })
                || (n == v.destination_directory && e.change.delta == if v.file_type == 2 { 1int } else { 0int }),
            Operation::Link => n == v.destination_directory && e.change.delta == 0,
            Operation::Unlink => n == v.source_directory && e.change.delta == 0,
        }
    }
}
#[verifier::opaque]
pub open spec fn requested_directory(v: UpdateView, e: DirectoryEditView) -> bool {
    &&& directory_bound(v.before,e)
    &&& match e.change {
        DirectoryChange::Insert(c) => v.operation != Operation::Unlink
            && e.owner == v.destination_directory
            && c.target == v.target && c.file_type == v.file_type && c.new_name == v.new_name,
        DirectoryChange::Remove(c) => v.operation != Operation::Link
            && e.owner == v.source_directory
            && c.record < c.before.block.records.len()
            && c.before.block.records[c.record as int].inode == v.target
            && c.before.block.records[c.record as int].file_type == v.file_type
            && crate::ns_rename_block::name(c.before,c.record as int) == v.old_name,
        DirectoryChange::DotDot(c) => v.operation == Operation::Rename && v.file_type == 2
            && e.owner == v.target
            && c.old_parent == v.source_directory && c.new_parent == v.destination_directory,
    }
}
pub open spec fn editable(i: int, inodes: Seq<InodeEditView>, directories: Seq<DirectoryEditView>) -> bool {
    (exists|j: int| 0 <= j < inodes.len() && (#[trigger] inodes[j]).position <= i < inodes[j].position as int + 256)
    || (exists|j: int| 0 <= j < directories.len() && (#[trigger] directories[j]).block as int * 4096 <= i < (directories[j].block as int + 1) * 4096)
}
pub open spec fn frame(v: UpdateView) -> bool {
    v.source.len() == v.result.len() &&
        forall|i: int| 0 <= i < v.source.len() && !editable(i,v.inode_edits,v.directory_edits) ==> #[trigger] v.result[i] == v.source[i]
}
pub open spec fn encoded_bytes(v: UpdateView) -> bool {
    &&& (forall|j: int| #![trigger v.inode_edits[j]] 0 <= j < v.inode_edits.len() ==> {
        let e = v.inode_edits[j]; let p = e.position as int;
        &&& 8192 <= p && p + 256 <= v.source.len()
        &&& e.change.before == v.source.subrange(p,p+256) && e.change.after == v.result.subrange(p,p+256)
    })
    &&& (forall|j: int| #![trigger v.directory_edits[j]] 0 <= j < v.directory_edits.len() ==> {
        let e = v.directory_edits[j]; let p = e.block as int * 4096;
        &&& 8192 <= p && p + 4096 <= v.source.len()
        &&& directory_before(e).block.raw == v.source.subrange(p,p+4096)
        &&& directory_after(e).block.raw == v.result.subrange(p,p+4096)
    })
    &&& frame(v)
}
pub open spec fn ancestry_excluded(v: UpdateView) -> bool {
    v.operation != Operation::Rename || v.file_type != 2 ||
        (0 < v.ancestry.len() <= crate::tree_model::MAX_DEPTH as nat + 1
            && v.ancestry[0] == v.destination_directory && v.ancestry.last() == 2
            && !v.ancestry.contains(v.target)
            && (forall|i: int| 0 <= i < v.ancestry.len()-1 ==> v.before.tree.parents[v.ancestry[i] as int] == v.ancestry[i+1]))
}
pub open spec fn covered(v: UpdateView) -> bool {
    &&& 2 <= v.inode_edits.len() <= 3 && 1 <= v.directory_edits.len() <= 3
    &&& (exists|j: int| 0 <= j < v.inode_edits.len() && (#[trigger] v.inode_edits[j]).number == v.target)
    &&& match v.operation {
        Operation::Rename => v.source_directory != v.destination_directory
            && (exists|j: int| 0 <= j < v.inode_edits.len() && (#[trigger] v.inode_edits[j]).number == v.source_directory)
            && (exists|j: int| 0 <= j < v.inode_edits.len() && (#[trigger] v.inode_edits[j]).number == v.destination_directory),
        Operation::Link => (exists|j: int| 0 <= j < v.inode_edits.len() && (#[trigger] v.inode_edits[j]).number == v.destination_directory),
        Operation::Unlink => (exists|j: int| 0 <= j < v.inode_edits.len() && (#[trigger] v.inode_edits[j]).number == v.source_directory),
    }
    &&& (forall|a: int,b: int| 0 <= a < b < v.inode_edits.len() ==> v.inode_edits[a].number != v.inode_edits[b].number)
}
#[verifier::opaque]
pub open spec fn valid(v:UpdateView)->bool {
    &&& planned(v) && certified(v.after,v.result) && exact_operation(v)
    &&& encoded_bytes(v) && patch_scope(v.patches,v.inode_edits,v.directory_edits)
    &&& patch_set::valid(v.patches) && v.result==patch_set::apply(v.source,v.patches)
}

pub struct Update { after: Vec<u8>, patches: PatchSet, checked: Ghost<Seq<UpdateView>> }
impl Update {
    pub closed spec fn view(&self) -> UpdateView { self.checked@[0] }
    pub closed spec fn wf(&self) -> bool { self.checked@.len() == 1 && valid(self.view()) && self.after@ == self.view().result && self.patches.view() == self.view().patches }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn bytes(&self) -> (r:&[u8]) ensures self.wf(), valid(self.view()), r@ == self.view().result {
        proof { use_type_invariant(self); } &self.after
    }
    pub fn patches(&self) -> (r:&PatchSet) ensures self.wf(),valid(self.view()),r.wf(),r.view() == self.view().patches {
        proof { use_type_invariant(self); } let _ = self.patches.len(); &self.patches
    }
    pub(crate) fn into_result(self) -> (r:(Vec<u8>,Ghost<NamespaceView>))
        ensures r.0@ == self.view().result,r.1@ == self.view().after,certified(r.1@,r.0@),
    { proof { use_type_invariant(&self); reveal(valid); } (self.after,Ghost(self.view().after)) }
}

struct InodeEdit { position:u64, number:u32, delta:i8, mtime:bool, before:Vec<u8>, after:Vec<u8>, checked:Ghost<InodeEditView> }
impl InodeEdit {
    closed spec fn view(&self)->InodeEditView { self.checked@ }
    closed spec fn wf(&self)->bool { ns_inode_links::valid(self.view().change)
        && self.position==self.view().position && self.number==self.view().number
        && self.number==self.view().change.number && self.delta==self.view().change.delta
        && self.mtime==self.view().change.touch_mtime && self.before@==self.view().change.before && self.after@==self.view().change.after }

}
struct DirectoryEdit { block:u32, before:Vec<u8>, after:Vec<u8>, checked:Ghost<DirectoryEditView> }
impl DirectoryEdit {
    closed spec fn view(&self)->DirectoryEditView { self.checked@ }
    closed spec fn wf(&self)->bool { change_valid(self.view().change) && !directory_before(self.view()).indexed && self.block == self.view().block
        && self.before@ == directory_before(self.view()).block.raw && self.after@ == directory_after(self.view()).block.raw }
}
spec fn inode_views(s:Seq<InodeEdit>)->Seq<InodeEditView> { Seq::new(s.len(),|i:int|s[i].view()) }
spec fn directory_views(s:Seq<DirectoryEdit>)->Seq<DirectoryEditView> { Seq::new(s.len(),|i:int|s[i].view()) }

fn copy(raw:&[u8])->(r:Vec<u8>)
    requires raw.len() <= MAX_IMAGE_BYTES,
    ensures r@ == raw@,
{
    let mut out=Vec::new(); let mut i=0usize;
    while i<raw.len()
        invariant i<=raw.len()<=MAX_IMAGE_BYTES,out@==raw@.take(i as int),
        decreases raw.len()-i,
    { out.push(raw[i]); assert(out@ =~= raw@.take(i as int+1)); i+=1; }
    assert(raw@.take(i as int) =~= raw@); out
}
fn materialize(source:&Snapshot<'_>)->(r:Option<Vec<u8>>)
    ensures match r {Some(raw)=>raw@==source.view() && raw.len()<=MAX_IMAGE_BYTES,None=>true},
{
    let length=source.partition_bytes(); if length>MAX_IMAGE_BYTES as u64 {return None;}
    let mut out=Vec::new(); let mut offset=0usize;
    while offset<length as usize
        invariant length==source.view().len(),length<=MAX_IMAGE_BYTES,offset<=length,out@==source.view().take(offset as int),
        decreases length-offset,
    {
        let amount=if length as usize-offset<65536 {length as usize-offset} else {65536usize};
        let raw=match source.capture_bytes(offset as u64,amount){Some(raw)=>raw,None=>{return None;}};
        let mut j=0usize; let ghost prior=out@;
        while j<raw.len()
            invariant j<=raw.len(),raw.len()==amount,prior==source.view().take(offset as int),
                raw@==source.view().subrange(offset as int,offset as int+amount),out@==prior+raw@.take(j as int),
            decreases raw.len()-j,
        {out.push(raw[j]);assert(out@ =~= prior+raw@.take(j as int+1));j+=1;}
        assert(out@ =~= source.view().take(offset as int+amount));offset+=amount;
    }
    assert(out@ =~= source.view());Some(out)
}
fn proper_name(name:&[u8])->(r:bool) ensures r==crate::ns_rename_block::proper_name(name@),
{
    if name.len()==0 || name.len()>255 {return false;}
    if name.len()==1 && name[0]==46 || name.len()==2 && name[0]==46 && name[1]==46 {return false;}
    let mut i=0usize;
    while i<name.len()
        invariant 0<name.len()<=255,i<=name.len(),!(name.len()==1 && name@[0]==46),
            !(name.len()==2 && name@[0]==46 && name@[1]==46),
            forall|j:int|0<=j<i ==> (#[trigger] name@[j])!=0 && name@[j]!=47,
        decreases name.len()-i,
    {if name[i]==0 || name[i]==47 {return false;}i+=1;}true
}
proof fn allocation_ordinary_at(v: crate::ea_allocation::AllocationView, ordinal: int)
    requires crate::ea_allocation::valid(v), 0 <= ordinal < v.ordinary.len(),
    ensures crate::ea_ordinary::valid(v.ordinary[ordinal]),
        v.ordinary[ordinal].index == v.integrity.references.index,
{
    reveal(crate::ea_allocation::valid);
    assert(crate::ea_ordinary::valid(v.ordinary[ordinal]));
    assert(v.ordinary[ordinal].index == v.integrity.references.index);
}

// Bind the captured inode to its exact admitted source slot.
proof fn namespace_inode_node_is_exact(namespace: crate::ea_namespace::NamespaceView,
    number: u32, node: crate::ea_source::NodeView)
    requires crate::ea_namespace::valid(namespace),
        crate::ea_namespace_nodes::active(namespace.index.nodes, number),
        crate::ea_source::node_valid(node), node.number == number,
        node.header == namespace.allocation.integrity.references.index.header,
    ensures namespace.index.nodes.slots[number as int].ordinal < namespace.allocation.ordinary.len(),
        crate::ea_ordinary::valid(namespace.allocation.ordinary[
            namespace.index.nodes.slots[number as int].ordinal as int]),
        namespace.allocation.ordinary[namespace.index.nodes.slots[number as int].ordinal as int].index
            == namespace.allocation.integrity.references.index,
        node == namespace.allocation.ordinary[
            namespace.index.nodes.slots[number as int].ordinal as int].parent.node,
{
    let table = namespace.index.nodes;
    assert(crate::ea_namespace_nodes::valid(table)
        && table.volume == namespace.allocation) by {
        reveal(crate::ea_namespace::valid);
        reveal(crate::ea_directory_index::valid);
    }
    crate::ea_namespace_nodes::every_active_namespace_node_matches_one_exact_source_ordinary_inode(table, number);
    let ordinal = table.slots[number as int].ordinal;
    let ordinary = namespace.allocation.ordinary[ordinal as int];
    assert(crate::ea_namespace_nodes::matches(table.slots[number as int], ordinary));
    assert(crate::ea_allocation::valid(namespace.allocation)) by { reveal(crate::ea_namespace::valid); }
    allocation_ordinary_at(namespace.allocation, ordinal as int);
    assert(crate::ea_ordinary::valid(namespace.allocation.ordinary[ordinal as int]));
    assert(namespace.allocation.ordinary[ordinal as int].index == namespace.allocation.integrity.references.index);
    assert(crate::ea_source::node_valid(ordinary.parent.node)
        && ordinary.parent.node.header == namespace.allocation.integrity.references.index.header
        && ordinary.parent.node.number == number) by {
        reveal(crate::ea_ordinary::valid);
        reveal(crate::ea_parent::valid);
    }
    crate::ea_integrity::same_source_ea_inode_number_identifies_one_exact_node(node, ordinary.parent.node);
}

// The binding is to the actual retained source tree and final ownership
// certificate, not to checksum equality or an independently supplied block.
proof fn captured_piece_is_encoder_view(v: ea_directory::DirectoryView, logical: u32, raw: Seq<u8>,
    inodes: u32, metadata_seed: u32, indexed: bool, large: bool)
    requires ea_directory::valid(v), logical < v.pieces.len(), logical < v.physical.len(),
        (v.physical[logical as int] as nat + 1) * 4096 <= v.volume.integrity.references.index.header.source.len(),
        raw == v.volume.integrity.references.index.header.source.subrange(v.physical[logical as int] as int * 4096,
            (v.physical[logical as int] as int + 1) * 4096),
        inodes == ea_directory::ordinary(v).index.header.inodes,
        metadata_seed == ea_directory::seed(ea_directory::ordinary(v)),
        indexed == ea_directory::indexed(ea_directory::ordinary(v)), large == ea_directory::large(v.volume),
    ensures ns_dir_edit::view(raw, inodes, metadata_seed, indexed, logical, v.pieces.len() as u32, large) == v.pieces[logical as int],
        v.pieces[logical as int].block.raw == raw,
        v.pieces[logical as int].block.inodes == inodes, v.pieces[logical as int].block.seed == metadata_seed,
        v.pieces[logical as int].indexed == indexed, v.pieces[logical as int].logical == logical,
        v.pieces[logical as int].blocks == v.pieces.len() as u32, v.pieces[logical as int].large == large,
{
    hide(crate::crc::fold);
    ea_directory::every_directory_piece_comes_from_its_initialized_owned_source_mapping(v, logical);
    assert(ea_directory::ordinary(v).index == v.volume.integrity.references.index) by { reveal(ea_directory::valid); }
    let piece = v.pieces[logical as int];
    assert(ea_directory::checked_piece(v.volume, ea_directory::ordinary(v), piece,
        v.physical[logical as int], logical, v.pieces.len() as u32));
    assert(piece.block.raw == raw && piece.block.inodes == inodes && piece.block.seed == metadata_seed
        && piece.indexed == indexed && piece.logical == logical && piece.blocks == v.pieces.len() as u32 && piece.large == large
        && crate::directory_piece::valid(piece)) by { reveal(ea_directory::checked_piece); }
    assert(piece.block.records == crate::directory_piece::canonical_records(raw, inodes, indexed, logical)) by {
        reveal(crate::directory_piece::valid);
    }
    assert(piece == ns_dir_edit::view(raw, inodes, metadata_seed, indexed, logical, v.pieces.len() as u32, large));
}


// Narrow summaries keep full allocation-validation facts in the source proof.
proof fn namespace_inode_node_identity(namespace: NamespaceView, number: u32, node: ea_source::NodeView)
    requires ea_namespace::valid(namespace),
        crate::ea_namespace_nodes::active(namespace.index.nodes, number),
        ea_source::node_valid(node), node.number == number,
        node.header == namespace.allocation.integrity.references.index.header,
    ensures namespace.index.nodes.slots[number as int].ordinal<namespace.allocation.ordinary.len(),
        node == namespace.allocation.ordinary[
        namespace.index.nodes.slots[number as int].ordinal as int].parent.node,
{
    namespace_inode_node_is_exact(namespace, number, node);
}


proof fn assemble_inode_binding(namespace:NamespaceView,node:ea_source::NodeView,change:ns_inode_links::Change,ordinal:usize)
    requires ea_namespace::valid(namespace),crate::ea_namespace_nodes::active(namespace.index.nodes,node.number),
        ordinal==namespace.index.nodes.slots[node.number as int].ordinal,ordinal<namespace.allocation.ordinary.len(),
        node==namespace.allocation.ordinary[ordinal as int].parent.node,ea_source::node_valid(node),
        node.header==namespace.allocation.integrity.references.index.header,
        change.before==node.raw,change.number==node.number,change.inodes==node.header.inodes,
        change.seed==node.header.seed,change.huge==crate::ea_parent::huge(node.header),ns_inode_links::valid(change),
    ensures inode_bound(namespace,InodeEditView{number:node.number,ordinal,position:node.position,change}),
{reveal(inode_bound);}
proof fn assemble_directory_binding(namespace:NamespaceView,directory:DirectoryView,logical:u32,block:u32,change:DirectoryChange)
    requires ea_namespace::valid(namespace),ea_directory::valid(directory),directory.volume==namespace.allocation,
        logical<directory.pieces.len(),logical<directory.physical.len(),block==directory.physical[logical as int],
        change_before(change)==directory.pieces[logical as int],!change_before(change).indexed,change_valid(change),
    ensures directory_bound(namespace,DirectoryEditView{owner:ea_directory::owner(directory),ordinal:directory.ordinal,logical,block,change}),
{
    let e=DirectoryEditView{owner:ea_directory::owner(directory),ordinal:directory.ordinal,logical,block,change};
    assert(directory_source_matches(namespace,e,directory));
    assert(exists|d:DirectoryView| #[trigger] directory_source_matches(namespace,e,d));
    reveal(directory_bound);
}
#[verifier::rlimit(20)]
#[verifier::spinoff_prover]
fn encode_inode(before:&ea_namespace::Namespace<'_,'_>,number:u32,mtime:bool,seconds:i64,nanos:u32,delta:i8)
    ->(r:Option<InodeEdit>)
    requires before.wf(),
    ensures match r {Some(e)=>e.wf() && inode_bound(before.view(),e.view()) && e.number==number
        && e.delta==delta && e.mtime==mtime && e.view().change.seconds==seconds && e.view().change.nanos==nanos,None=>true},
{
    hide(vstd::slice::axiom_spec_len);
    let nodes=before.index().nodes();
    let slot=match nodes.get(number){Some(n)=>n,None=>{return None;}};
    let index=before.allocation().integrity().reference_census().index();
    let node=match index.node(number){Some(n)=>n,None=>{return None;}};
    proof {namespace_inode_node_identity(before.view(),number,node.view());}
    let raw=node.raw();let position=node.position();
    proof {vstd::slice::axiom_spec_len(raw);}
    let (_,inodes,_,seed)=node.inode_parameters();let huge=index.header().huge_files();
    let changed=match ns_inode_links::encode(raw,number,inodes,seed,huge,mtime,seconds,nanos,delta){Some(c)=>c,None=>{return None;}};
    let ghost change=ns_inode_links::Change{before:raw@,after:changed@,number,inodes,seed,huge,touch_mtime:mtime,seconds:seconds as int,nanos:nanos as nat,delta:delta as int};
    let ghost view=InodeEditView{number,ordinal:slot.ordinal,position,change};
    proof {assemble_inode_binding(before.view(),node.view(),change,slot.ordinal);}
    Some(InodeEdit{position,number,delta,mtime,before:copy(raw),after:changed,checked:Ghost(view)})
}

spec fn change_before(c:DirectoryChange)->crate::directory_piece::PieceView {
    match c {DirectoryChange::Insert(e)=>e.before,DirectoryChange::Remove(e)=>e.before,DirectoryChange::DotDot(e)=>e.before}
}
spec fn change_after(c:DirectoryChange)->crate::directory_piece::PieceView {
    match c {DirectoryChange::Insert(e)=>e.after,DirectoryChange::Remove(e)=>e.after,DirectoryChange::DotDot(e)=>e.after}
}
spec fn change_valid(c:DirectoryChange)->bool {
    match c {DirectoryChange::Insert(e)=>ns_dir_edit::insert_valid(e),DirectoryChange::Remove(e)=>ns_dir_edit::remove_valid(e),DirectoryChange::DotDot(e)=>ns_dir_edit::dotdot_valid(e)}
}
spec fn change_request(c:DirectoryChange,action:u8,target:u32,file_type:u8,name:Seq<u8>,old_parent:u32,new_parent:u32)->bool {
    match c {
        DirectoryChange::Insert(e)=>action==1 && e.target==target && e.file_type==file_type && e.new_name==name,
        DirectoryChange::Remove(e)=>action==0 && e.record<e.before.block.records.len()
            && e.before.block.records[e.record as int].inode==target && e.before.block.records[e.record as int].file_type==file_type
            && crate::ns_rename_block::name(e.before,e.record as int)==name,
        DirectoryChange::DotDot(e)=>action==2 && e.old_parent==old_parent && e.new_parent==new_parent,
    }
}
#[verifier::rlimit(15)]
#[verifier::spinoff_prover]
fn encode_piece(raw:&[u8],inodes:u32,seed:u32,indexed:bool,logical:u32,count:u32,large:bool,
    record:usize,action:u8,target:u32,file_type:u8,name:&[u8],old_parent:u32,new_parent:u32)
    ->(r:Option<(Vec<u8>,Ghost<DirectoryChange>)>)
    ensures match r {Some((after,c))=>change_valid(c@)
        && change_before(c@)==ns_dir_edit::view(raw@,inodes,seed,indexed,logical,count,large)
        && change_after(c@).block.raw==after@
        && change_request(c@,action,target,file_type,name@,old_parent,new_parent),None=>true},
{
    hide(vstd::slice::axiom_spec_len);
    hide(ns_dir_edit::view); hide(crate::ns_rename_block::view);
    hide(crate::directory_piece::canonical_records); hide(crate::directory_block::canonical_records);
    let piece=match crate::directory_piece::parse(raw,inodes,seed,indexed,logical,count,large){Some(p)=>p,None=>{return None;}};
    assert(piece.view()==ns_dir_edit::view(raw@,inodes,seed,indexed,logical,count,large)) by {
        reveal(ns_dir_edit::view); reveal(crate::ns_rename_block::view);
    }
    if action==0 {
        let selected=match piece.get(record){Some(s)=>s,None=>{return None;}};
        let actual_name=match piece.name(record){Some(n)=>n,None=>{return None;}};
        if selected.inode!=target || selected.file_type!=file_type || !bytes::equal(actual_name,name){return None;}
        let changed=match ns_dir_edit::remove(raw,inodes,seed,indexed,logical,count,large,record){Some(c)=>c,None=>{return None;}};
        let ghost c=ns_dir_edit::RemoveChange{before:ns_dir_edit::view(raw@,inodes,seed,indexed,logical,count,large),
            after:ns_dir_edit::view(changed@,inodes,seed,indexed,logical,count,large),record};
        assert(ns_dir_edit::view(changed@,inodes,seed,indexed,logical,count,large).block.raw==changed@) by {
            reveal(ns_dir_edit::view); reveal(crate::ns_rename_block::view);
        }
        return Some((changed,Ghost(DirectoryChange::Remove(c))));
    }
    if action==1 {
        let changed=match ns_dir_edit::insert(raw,inodes,seed,indexed,logical,count,large,target,file_type,name){Some(c)=>c,None=>{return None;}};
        proof {reveal(ns_dir_edit::inserted);}
        let ghost (chosen_record,chosen_added)=choose|r:usize,a:usize|ns_dir_edit::insert_valid(ns_dir_edit::InsertChange{
            before:ns_dir_edit::view(raw@,inodes,seed,indexed,logical,count,large),
            after:ns_dir_edit::view(changed@,inodes,seed,indexed,logical,count,large),record:r,added:a,target,file_type,new_name:name@});
        let ghost c=ns_dir_edit::InsertChange{before:ns_dir_edit::view(raw@,inodes,seed,indexed,logical,count,large),
            after:ns_dir_edit::view(changed@,inodes,seed,indexed,logical,count,large),record:chosen_record,added:chosen_added,target,file_type,new_name:name@};
        assert(ns_dir_edit::view(changed@,inodes,seed,indexed,logical,count,large).block.raw==changed@) by {
            reveal(ns_dir_edit::view); reveal(crate::ns_rename_block::view);
        }
        return Some((changed,Ghost(DirectoryChange::Insert(c))));
    }
    if action==2 {
        let changed=match ns_dir_edit::retarget_dotdot(raw,inodes,seed,indexed,logical,count,large,old_parent,new_parent){Some(c)=>c,None=>{return None;}};
        let ghost c=ns_dir_edit::DotDotChange{before:ns_dir_edit::view(raw@,inodes,seed,indexed,logical,count,large),
            after:ns_dir_edit::view(changed@,inodes,seed,indexed,logical,count,large),record:1,old_parent,new_parent};
        assert(ns_dir_edit::view(changed@,inodes,seed,indexed,logical,count,large).block.raw==changed@) by {
            reveal(ns_dir_edit::view); reveal(crate::ns_rename_block::view);
        }
        return Some((changed,Ghost(DirectoryChange::DotDot(c))));
    }
    None
}

#[verifier::rlimit(25)]
#[verifier::spinoff_prover]
fn encode_directory(source:&Snapshot<'_>,before:&ea_namespace::Namespace<'_,'_>,owner:u32,
    logical:u32,record:usize,action:u8,target:u32,file_type:u8,name:&[u8],old_parent:u32,new_parent:u32)
    ->(r:Option<DirectoryEdit>)
    requires before.wf(),certified(before.view(),source.view()),
    ensures match r {Some(e)=>e.wf() && directory_bound(before.view(),e.view())
        && e.view().owner==owner
        && match e.view().change {
            DirectoryChange::Insert(c)=>action==1 && c.target==target && c.file_type==file_type && c.new_name==name@,
            DirectoryChange::Remove(c)=>action==0 && c.record< c.before.block.records.len()
                && c.before.block.records[c.record as int].inode==target
                && c.before.block.records[c.record as int].file_type==file_type
                && crate::ns_rename_block::name(c.before,c.record as int)==name@,
            DirectoryChange::DotDot(c)=>action==2 && c.old_parent==old_parent && c.new_parent==new_parent,
        },None=>true},
{
    hide(vstd::slice::axiom_spec_len);
    hide(ns_dir_edit::view); hide(crate::ns_rename_block::view); hide(crate::crc::fold);
    let slot=match before.index().nodes().get(owner){Some(n)=>n,None=>{return None;}};
    let directory=match ea_directory::inspect(before.allocation(),slot.ordinal){Some(d)=>d,None=>{return None;}};
    let block=match directory.physical_block(logical){Some(b)=>b,None=>{return None;}};
    let raw=match source.block(block){Some(b)=>b.as_slice(),None=>{return None;}};
    proof {vstd::slice::axiom_spec_len(raw);}
    let index=before.allocation().integrity().reference_census().index();
    let node=match index.node(owner){Some(n)=>n,None=>{return None;}};
    proof {namespace_inode_node_is_exact(before.view(),owner,node.view());}
    let nraw=node.raw();
    let (_,inodes,_,seed)=index.parameters();
    let indexed=bytes::read_le32(nraw,32).unwrap() & 0x1000 != 0;
    if indexed {return None;}
    let superblock=match source.capture_bytes(1024,1024){Some(s)=>s,None=>{return None;}};
    let large=match bytes::read_le32(&superblock,96){Some(flags)=>flags & 0x4000 != 0,None=>{return None;}};
    let generation=bytes::read_le32(nraw,100).unwrap();
    let metadata_seed=inode::inode_seed(seed,owner,generation);
    let count=directory.block_count();
    let piece=match directory.piece(logical){Some(p)=>p,None=>{return None;}};
    proof {captured_piece_is_encoder_view(directory.view(),logical,raw@,inodes,metadata_seed,indexed,large);}
    let (changed,c)=match encode_piece(raw,inodes,metadata_seed,indexed,logical,count,large,record,action,target,file_type,name,old_parent,new_parent){Some(c)=>c,None=>{return None;}};
    let ghost view=DirectoryEditView{owner,ordinal:slot.ordinal,logical,block,change:c@};
    proof {assemble_directory_binding(before.view(),directory.view(),logical,block,c@);}
    Some(DirectoryEdit{block,before:copy(raw),after:changed,checked:Ghost(view)})
}
fn insert_directory(source:&Snapshot<'_>,before:&ea_namespace::Namespace<'_,'_>,owner:u32,target:u32,file_type:u8,name:&[u8])
    ->(r:Option<DirectoryEdit>)
    requires before.wf(),certified(before.view(),source.view()),
    ensures match r {Some(e)=>e.wf() && directory_bound(before.view(),e.view())
        && e.view().owner==owner
        && match e.view().change {DirectoryChange::Insert(c)=>c.target==target && c.file_type==file_type && c.new_name==name@,_=>false},None=>true},
{
    let slot=match before.index().nodes().get(owner){Some(n)=>n,None=>{return None;}};
    let directory=match ea_directory::inspect(before.allocation(),slot.ordinal){Some(d)=>d,None=>{return None;}};
    let count=directory.block_count();let mut logical=0u32;
    while logical<count
        invariant before.wf(),certified(before.view(),source.view()),logical<=count<=4096,
        decreases count-logical,
    {
        match encode_directory(source,before,owner,logical,0,1,target,file_type,name,0,0){
            Some(e)=>{return Some(e);},None=>{}
        }
        logical+=1;
    }
    None
}
pub open spec fn ancestry_path(before:NamespaceView,path:Seq<u32>,target:u32,destination:u32)->bool {
    0<path.len()<=crate::tree_model::MAX_DEPTH as nat+1 && path[0]==destination && path.last()==2
        && !path.contains(target)
        && (forall|i:int|0<=i<path.len()-1 ==> before.tree.parents[path[i] as int]==path[i+1])
}
fn ancestry(before:&ea_namespace::Namespace<'_,'_>,target:u32,destination:u32)->(r:Option<Vec<u32>>)
    requires before.wf(),
    ensures match r {Some(path)=>ancestry_path(before.view(),path@,target,destination),None=>true},
{
    if target==destination{return None;}
    let mut path=Vec::new();path.push(destination);let mut current=destination;
    while current!=2
        invariant before.wf(),0<path.len()<=crate::tree_model::MAX_DEPTH as nat+1,
            path@[0]==destination,path@.last()==current,!path@.contains(target),
            forall|i:int|0<=i<path.len()-1 ==> before.view().tree.parents[path@[i] as int]==path@[i+1],
        decreases crate::tree_model::MAX_DEPTH as nat+1-path.len(),
    {
        if path.len()>=crate::tree_model::MAX_DEPTH as usize+1{return None;}
        let parent=match before.parent(current){Some(p)=>p,None=>{return None;}};
        if parent==target{return None;}
        let ghost prior=path@;path.push(parent);
        assert forall|i:int|0<=i<path.len()-1 implies before.view().tree.parents[path@[i] as int]==path@[i+1] by {
            if i<prior.len()-1{assert(path@[i]==prior[i] && path@[i+1]==prior[i+1]);}
            else{assert(i==prior.len()-1 && prior[i]==current && path@[i+1]==parent);}
        }
        assert(!path@.contains(target));current=parent;
    }
    Some(path)
}

fn push_inode(mut edits:Vec<InodeEdit>,edit:InodeEdit,request:Ghost<UpdateView>)->(r:Vec<InodeEdit>)
    requires edits.len()<3,edit.wf(),requested_inode(request@,edit.view()),
        forall|i:int|0<=i<edits.len() ==> edits@[i].wf() && requested_inode(request@,edits@[i].view()),
    ensures r.len()==edits.len()+1,inode_views(r@)==inode_views(edits@).push(edit.view()),
        forall|i:int|0<=i<r.len() ==> r@[i].wf() && requested_inode(request@,r@[i].view()),
{
    hide(InodeEdit::wf);
    let ghost prior=edits@;let ghost ev=edit.view();edits.push(edit);
    assert forall|i:int|0<=i<edits.len() implies edits@[i].wf() && requested_inode(request@,edits@[i].view()) by {
        if i<prior.len(){assert(edits@[i]==prior[i]);}else{assert(i==prior.len() && edits@[i].view()==ev);}
    }
    assert(inode_views(edits@) =~= inode_views(prior).push(ev));edits
}
fn push_directory(mut edits:Vec<DirectoryEdit>,edit:DirectoryEdit,request:Ghost<UpdateView>)->(r:Vec<DirectoryEdit>)
    requires edits.len()<3,edit.wf(),requested_directory(request@,edit.view()),
        forall|i:int|0<=i<edits.len() ==> edits@[i].wf() && requested_directory(request@,edits@[i].view()),
    ensures r.len()==edits.len()+1,directory_views(r@)==directory_views(edits@).push(edit.view()),
        forall|i:int|0<=i<r.len() ==> r@[i].wf() && requested_directory(request@,r@[i].view()),
{
    hide(DirectoryEdit::wf);
    let ghost prior=edits@;let ghost ev=edit.view();edits.push(edit);
    assert forall|i:int|0<=i<edits.len() implies edits@[i].wf() && requested_directory(request@,edits@[i].view()) by {
        if i<prior.len(){assert(edits@[i]==prior[i]);}else{assert(i==prior.len() && edits@[i].view()==ev);}
    }
    assert(directory_views(edits@) =~= directory_views(prior).push(ev));edits
}
fn stage_inode(source:&Snapshot<'_>,patches:PatchSet,position:u64,raw:&[u8])->(r:Option<PatchSet>)
    ensures match r {Some(p)=>p.wf(),None=>true},
{
    if raw.len()!=256 || position>source.partition_bytes() || 256>source.partition_bytes()-position
        || position%4096>3840 || position/4096>u32::MAX as u64{return None;}
    let block=(position/4096) as u32;let within=(position%4096) as usize;
    let mut raw_block=match patches.get(block){Some(image)=>copy(image.as_slice()),
        None=>match source.capture(block,1){Some(raw)=>raw,None=>{return None;}}};
    if !bytes::write_bytes(raw_block.as_mut_slice(),within,raw){return None;}
    match patches.upsert(block,&raw_block){Ok(p)=>Some(p),Err(_)=>None}
}
fn stage(source:&Snapshot<'_>,inodes:&[InodeEdit],directories:&[DirectoryEdit])->(r:Option<PatchSet>)
    requires inodes.len()<=3,directories.len()<=3,
    ensures match r {Some(p)=>p.wf(),None=>true},
{
    let mut patches=PatchSet::new();let mut i=0usize;
    while i<directories.len()
        invariant i<=directories.len()<=3,patches.wf(),
        decreases directories.len()-i,
    {
        patches=match patches.upsert(directories[i].block,&directories[i].after){Ok(p)=>p,Err(_)=>{return None;}};
        i+=1;
    }
    let mut i=0usize;
    while i<inodes.len()
        invariant i<=inodes.len()<=3,patches.wf(),
        decreases inodes.len()-i,
    {
        patches=match stage_inode(source,patches,inodes[i].position,&inodes[i].after){Some(p)=>p,None=>{return None;}};
        i+=1;
    }
    Some(patches)
}
fn is_editable(position:usize,inodes:&[InodeEdit],directories:&[DirectoryEdit])->(r:bool)
    requires forall|i:int|0<=i<inodes.len() ==> inodes@[i].wf(),
        forall|i:int|0<=i<directories.len() ==> directories@[i].wf(),
    ensures r==editable(position as int,inode_views(inodes@),directory_views(directories@)),
{
    hide(vstd::slice::axiom_spec_len);
    proof { vstd::slice::axiom_spec_len(inodes); vstd::slice::axiom_spec_len(directories); }
    assert(inode_views(inodes@).len()==inodes.len());
    assert(directory_views(directories@).len()==directories.len());
    let mut i=0usize;
    while i<inodes.len()
        invariant i<=inodes.len(),inode_views(inodes@).len()==inodes.len(),
            forall|j:int|0<=j<inodes.len() ==> inodes@[j].wf(),
            forall|j:int|#![trigger inode_views(inodes@)[j]] 0<=j<i ==> !(inode_views(inodes@)[j].position<=position<inode_views(inodes@)[j].position as int+256),
        decreases inodes.len()-i,
    {
        let p=inodes[i].position;
        assert(inode_views(inodes@)[i as int].position==p) by {
            assert(inodes@[i as int].wf());
            reveal(InodeEdit::wf);
            assert(inode_views(inodes@)[i as int]==inodes@[i as int].view());
        }
        if p<=position as u64 && (position as u64)-p<256 {
            assert(exists|j:int|0<=j<inodes.len() && (#[trigger] inode_views(inodes@)[j]).position<=position<inode_views(inodes@)[j].position as int+256);
            return true;
        }
        i+=1;
    }
    let mut i=0usize;
    while i<directories.len()
        invariant i<=directories.len(),inode_views(inodes@).len()==inodes.len(),
            directory_views(directories@).len()==directories.len(),
            forall|j:int|#![trigger inode_views(inodes@)[j]] 0<=j<inodes.len() ==> !(inode_views(inodes@)[j].position<=position<inode_views(inodes@)[j].position as int+256),
            forall|j:int|0<=j<directories.len() ==> directories@[j].wf(),
            forall|j:int|#![trigger directory_views(directories@)[j]] 0<=j<i ==> !(directory_views(directories@)[j].block as int*4096<=position<(directory_views(directories@)[j].block as int+1)*4096),
        decreases directories.len()-i,
    {
        let b=directories[i].block;
        assert(directory_views(directories@)[i as int].block==b) by {
            assert(directories@[i as int].wf());
            reveal(DirectoryEdit::wf);
            assert(directory_views(directories@)[i as int]==directories@[i as int].view());
        }
        if b as u64*4096<=position as u64 && (position as u64) < (b as u64+1)*4096 {
            assert(exists|j:int|0<=j<directories.len() && (#[trigger] directory_views(directories@)[j]).block as int*4096<=position<(directory_views(directories@)[j].block as int+1)*4096);
            return true;
        }
        i+=1;
    }
    false
}
#[verifier::rlimit(15)]
fn check_frame(source:&Snapshot<'_>,result:&[u8],inodes:&[InodeEdit],directories:&[DirectoryEdit])->(r:bool)
    requires forall|i:int|0<=i<inodes.len() ==> inodes@[i].wf(),
        forall|i:int|0<=i<directories.len() ==> directories@[i].wf(),
    ensures r ==> result.len()==source.view().len()
        && (forall|i:int|0<=i<source.view().len() && !editable(i,inode_views(inodes@),directory_views(directories@)) ==> #[trigger] result@[i]==source.view()[i]),
{
    hide(vstd::slice::axiom_spec_len);
    proof { vstd::slice::axiom_spec_len(result); vstd::slice::axiom_spec_len(inodes); vstd::slice::axiom_spec_len(directories); }
    if result.len()>MAX_IMAGE_BYTES || source.partition_bytes()!=result.len() as u64{return false;}
    let mut offset=0usize;
    while offset<result.len()
        invariant offset<=result.len()<=MAX_IMAGE_BYTES,result.len()==source.view().len(),
            forall|i:int|0<=i<inodes.len() ==> inodes@[i].wf(),
            forall|i:int|0<=i<directories.len() ==> directories@[i].wf(),
            forall|i:int|0<=i<offset && !editable(i,inode_views(inodes@),directory_views(directories@)) ==> #[trigger] result@[i]==source.view()[i],
        decreases result.len()-offset,
    {
        let amount=if result.len()-offset<65536 {result.len()-offset}else{65536usize};
        let raw=match source.capture_bytes(offset as u64,amount){Some(raw)=>raw,None=>{return false;}};
        assert(raw.len()==amount);
        let mut j=0usize;
        while j<amount
            invariant j<=amount,raw.len()==amount,offset+amount<=result.len()<=MAX_IMAGE_BYTES,
                result.len()==source.view().len(),
                raw@==source.view().subrange(offset as int,offset as int+amount),
                forall|i:int|0<=i<inodes.len() ==> inodes@[i].wf(),
                forall|i:int|0<=i<directories.len() ==> directories@[i].wf(),
                forall|i:int|0<=i<offset+j && !editable(i,inode_views(inodes@),directory_views(directories@)) ==> #[trigger] result@[i]==source.view()[i],
            decreases amount-j,
        {
            let editable_now=is_editable(offset+j,inodes,directories);
            if !editable_now && raw[j]!=result[offset+j]{return false;}
            assert forall|i:int|0<=i<offset+j+1 && !editable(i,inode_views(inodes@),directory_views(directories@))
                implies #[trigger] result@[i]==source.view()[i] by {
                if i<offset+j { }
                else {
                    assert(i==offset+j);
                    assert(raw@[j as int]==source.view()[i]);
                }
            }
            j+=1;
        }
        offset+=amount;
    }
    true
}
#[verifier::rlimit(15)]
fn check_encoded(source:&Snapshot<'_>,result:&[u8],inodes:&[InodeEdit],directories:&[DirectoryEdit],v:Ghost<UpdateView>)->(r:bool)
    requires v@.source==source.view(),v@.result==result@,v@.inode_edits==inode_views(inodes@),v@.directory_edits==directory_views(directories@),
        forall|i:int|0<=i<inodes.len() ==> inodes@[i].wf(),
        forall|i:int|0<=i<directories.len() ==> directories@[i].wf(),
    ensures r ==> encoded_bytes(v@),
{
    hide(vstd::slice::axiom_spec_len);
    proof { vstd::slice::axiom_spec_len(result); vstd::slice::axiom_spec_len(inodes); vstd::slice::axiom_spec_len(directories); }
    if result.len()>MAX_IMAGE_BYTES || source.partition_bytes()!=result.len() as u64{return false;}
    let mut i=0usize;
    while i<inodes.len()
        invariant i<=inodes.len(),result.len()==source.view().len(),result.len()<=MAX_IMAGE_BYTES,
            inodes@.len()==inodes.len(),directories@.len()==directories.len(),result@.len()==result.len(),
            v@.source==source.view(),v@.result==result@,v@.inode_edits==inode_views(inodes@),v@.directory_edits==directory_views(directories@),
            forall|j:int|0<=j<inodes.len() ==> inodes@[j].wf(),
            forall|j:int|0<=j<directories.len() ==> directories@[j].wf(),
            forall|j:int|#![trigger v@.inode_edits[j]] 0<=j<i ==> {
                let e=v@.inode_edits[j];let p=e.position as int;
                &&& 8192<=p && p+256<=v@.source.len()
                &&& e.change.before==v@.source.subrange(p,p+256) && e.change.after==v@.result.subrange(p,p+256)
            },
        decreases inodes.len()-i,
    {
        let e=&inodes[i];let p=e.position;
        assert(p==v@.inode_edits[i as int].position && e.before@==v@.inode_edits[i as int].change.before
            && e.after@==v@.inode_edits[i as int].change.after) by {
            assert(inode_views(inodes@)[i as int]==e.view());
            assert(e.wf()); reveal(InodeEdit::wf);
        }
        if p<8192 || p>result.len() as u64 || 256>result.len() as u64-p{return false;}
        let prior=match source.capture_bytes(p,256){Some(raw)=>raw,None=>{return false;}};
        if !bytes::equal(&prior,&e.before) || !bytes::equal(&result[p as usize..p as usize+256],&e.after){return false;}
        i+=1;
    }
    let mut i=0usize;
    while i<directories.len()
        invariant i<=directories.len(),result.len()==source.view().len(),result.len()<=MAX_IMAGE_BYTES,
            inodes@.len()==inodes.len(),directories@.len()==directories.len(),result@.len()==result.len(),
            v@.source==source.view(),v@.result==result@,v@.inode_edits==inode_views(inodes@),v@.directory_edits==directory_views(directories@),
            forall|j:int|0<=j<inodes.len() ==> inodes@[j].wf(),
            forall|j:int|0<=j<directories.len() ==> directories@[j].wf(),
            forall|j:int|#![trigger v@.inode_edits[j]] 0<=j<v@.inode_edits.len() ==> {
                let e=v@.inode_edits[j];let p=e.position as int;
                &&& 8192<=p && p+256<=v@.source.len()
                &&& e.change.before==v@.source.subrange(p,p+256) && e.change.after==v@.result.subrange(p,p+256)
            },
            forall|j:int|#![trigger v@.directory_edits[j]] 0<=j<i ==> {
                let e=v@.directory_edits[j];let p=e.block as int*4096;
                &&& 8192<=p && p+4096<=v@.source.len()
                &&& directory_before(e).block.raw==v@.source.subrange(p,p+4096)
                &&& directory_after(e).block.raw==v@.result.subrange(p,p+4096)
            },
        decreases directories.len()-i,
    {
        let e=&directories[i];let p=e.block as u64*4096;
        assert(e.block==v@.directory_edits[i as int].block
            && e.before@==directory_before(v@.directory_edits[i as int]).block.raw
            && e.after@==directory_after(v@.directory_edits[i as int]).block.raw) by {
            assert(directory_views(directories@)[i as int]==e.view());
            assert(e.wf()); reveal(DirectoryEdit::wf);
        }
        if p<8192 || p>result.len() as u64 || 4096>result.len() as u64-p{return false;}
        let prior=match source.capture_bytes(p,4096){Some(raw)=>raw,None=>{return false;}};
        if !bytes::equal(&prior,&e.before) || !bytes::equal(&result[p as usize..p as usize+4096],&e.after){return false;}
        i+=1;
    }
    if !check_frame(source,result,inodes,directories){return false;}true
}

#[verifier::opaque]
pub open spec fn patch_target_known(block:u32,inodes:Seq<InodeEditView>,directories:Seq<DirectoryEditView>)->bool {
    (exists|j:int|0<=j<inodes.len() && (#[trigger] inodes[j]).position/4096==block)
        || (exists|j:int|0<=j<directories.len() && (#[trigger] directories[j]).block==block)
}
pub open spec fn patch_scope(patches:Seq<ImageView>,inodes:Seq<InodeEditView>,directories:Seq<DirectoryEditView>)->bool {
    0<patches.len()<=6 && forall|i:int|#![trigger patches[i]] 0<=i<patches.len() ==>
        patch_target_known(patches[i].block,inodes,directories)
}
fn is_patch_target(block:u32,inodes:&[InodeEdit],directories:&[DirectoryEdit])->(r:bool)
    requires forall|j:int|0<=j<inodes.len() ==> inodes@[j].wf(),
        forall|j:int|0<=j<directories.len() ==> directories@[j].wf(),
    ensures r == ((exists|j:int|0<=j<inodes.len() && (#[trigger] inode_views(inodes@)[j]).position/4096==block)
        || (exists|j:int|0<=j<directories.len() && (#[trigger] directory_views(directories@)[j]).block==block)),
{
    hide(inode_views); hide(directory_views); hide(vstd::slice::axiom_spec_len);
    proof {
        vstd::slice::axiom_spec_len(inodes);
        vstd::slice::axiom_spec_len(directories);
    }
    let mut j=0usize;
    while j<inodes.len()
        invariant j<=inodes.len(),inodes@.len()==inodes.len(),directories@.len()==directories.len(),
            forall|i:int|0<=i<inodes.len() ==> inodes@[i].wf(),
            forall|i:int|0<=i<directories.len() ==> directories@[i].wf(),
            forall|i:int|0<=i<j ==> (#[trigger] inode_views(inodes@)[i]).position/4096!=block,
        decreases inodes.len()-j,
    {
        proof { inode_view_at(inodes@,j as int); }
        assert(inodes@[j as int].wf());
        assert(inode_views(inodes@)[j as int].position==inodes@[j as int].position);
        if inodes[j].position/4096==block as u64 {
            assert(exists|i:int|0<=i<inodes.len() && (#[trigger] inode_views(inodes@)[i]).position/4096==block);
            return true;
        }
        j+=1;
    }
    let mut j=0usize;
    while j<directories.len()
        invariant j<=directories.len(),inodes@.len()==inodes.len(),directories@.len()==directories.len(),
            forall|i:int|0<=i<directories.len() ==> directories@[i].wf(),
            forall|i:int|0<=i<inodes.len() ==> (#[trigger] inode_views(inodes@)[i]).position/4096!=block,
            forall|i:int|0<=i<j ==> (#[trigger] directory_views(directories@)[i]).block!=block,
        decreases directories.len()-j,
    {
        proof { directory_view_at(directories@,j as int); }
        assert(directories@[j as int].wf());
        assert(directory_views(directories@)[j as int].block==directories@[j as int].block);
        if directories[j].block==block {
            assert(exists|i:int|0<=i<directories.len() && (#[trigger] directory_views(directories@)[i]).block==block);
            return true;
        }
        j+=1;
    }
    false
}
fn check_patch_scope(patches:&PatchSet,inodes:&[InodeEdit],directories:&[DirectoryEdit])->(r:bool)
    requires forall|j:int|0<=j<inodes.len() ==> inodes@[j].wf(),
        forall|j:int|0<=j<directories.len() ==> directories@[j].wf(),
    ensures patches.wf(),r ==> patch_scope(patches.view(),inode_views(inodes@),directory_views(directories@)),
{
    hide(inode_views); hide(directory_views); hide(vstd::slice::axiom_spec_len);
    proof {
        vstd::slice::axiom_spec_len(inodes);
        vstd::slice::axiom_spec_len(directories);
        inode_view_length(inodes@);
        directory_view_length(directories@);
    }
    let count=patches.len();if count==0 || count>6{return false;}
    let mut i=0usize;
    while i<count
        invariant patches.wf(),count==patches.view().len(),0<count<=6,i<=count,
            inodes@.len()==inodes.len(),directories@.len()==directories.len(),
            inode_views(inodes@).len()==inodes.len(),directory_views(directories@).len()==directories.len(),
            forall|j:int|0<=j<inodes.len() ==> inodes@[j].wf(),
            forall|j:int|0<=j<directories.len() ==> directories@[j].wf(),
            forall|j:int|0<=j<i ==> #[trigger] patch_target_known(patches.view()[j].block,inode_views(inodes@),directory_views(directories@)),
        decreases count-i,
    {
        let block=patches.at(i).unwrap().block();
        if !is_patch_target(block,inodes,directories){return false;}
        assert(patch_target_known(patches.view()[i as int].block,inode_views(inodes@),directory_views(directories@))) by {
            reveal(patch_target_known);
        }
        i+=1;
    }
    assert forall|j:int|#![trigger patches.view()[j]] 0<=j<patches.view().len() implies
        patch_target_known(patches.view()[j].block,inode_views(inodes@),directory_views(directories@)) by {
        assert(0<=j<i);
        assert(patch_target_known(patches.view()[j].block,inode_views(inodes@),directory_views(directories@)));
    }
    assert(patch_scope(patches.view(),inode_views(inodes@),directory_views(directories@))) by {reveal(patch_scope);}
    true
}


#[verifier::opaque]
pub open spec fn discovered(v:UpdateView)->bool {
    &&& certified(v.before,v.source) && 8192<=v.source.len()<=MAX_IMAGE_BYTES
    &&& !feature_policy::readonly(v.source.subrange(1024,2048))
    &&& crate::ns_rename_block::proper_name(v.old_name)
    &&& (v.operation==Operation::Unlink || crate::ns_rename_block::proper_name(v.new_name))
    &&& (v.operation==Operation::Rename || v.file_type==1)
    &&& v.target!=v.source_directory && v.target!=v.destination_directory
    &&& (v.operation!=Operation::Rename || v.source_directory!=v.destination_directory)
    &&& ancestry_excluded(v)
    &&& (v.operation!=Operation::Rename || v.file_type!=2 ||
        (v.before.index.nodes.slots[v.source_directory as int].links>1 && v.before.index.nodes.slots[v.destination_directory as int].links>1))
}
#[verifier::opaque]
pub open spec fn planned(v:UpdateView)->bool {
    &&& discovered(v) && covered(v)
    &&& (forall|j:int|0<=j<v.inode_edits.len() ==> requested_inode(v,v.inode_edits[j]))
    &&& (forall|j:int|0<=j<v.directory_edits.len() ==> requested_directory(v,v.directory_edits[j]))
}
proof fn plan_survives_attachment(start:UpdateView,end:UpdateView)
    requires planned(start),end==(UpdateView{result:end.result,after:end.after,patches:end.patches,..start}),
    ensures planned(end),
{
    reveal(planned);reveal(discovered);reveal(requested_inode);reveal(requested_directory);
}
proof fn assemble_candidate(v:UpdateView)
    requires planned(v),certified(v.after,v.result),exact_operation(v),encoded_bytes(v),
        patch_scope(v.patches,v.inode_edits,v.directory_edits),patch_set::valid(v.patches),
        v.result==patch_set::apply(v.source,v.patches),
    ensures valid(v),
{reveal(valid);reveal(planned);reveal(discovered);}
struct Plan { inodes:Vec<InodeEdit>,directories:Vec<DirectoryEdit>,checked:Ghost<Seq<UpdateView>> }
impl Plan {
    closed spec fn view(&self)->UpdateView{self.checked@[0]}
    closed spec fn wf(&self)->bool {
        self.checked@.len()==1 && planned(self.view()) && inode_views(self.inodes@)==self.view().inode_edits
            && directory_views(self.directories@)==self.view().directory_edits
            && self.inodes.len()<=3 && self.directories.len()<=3
            && (forall|i:int|0<=i<self.inodes.len() ==> self.inodes@[i].wf())
            && (forall|i:int|0<=i<self.directories.len() ==> self.directories@[i].wf())
    }
}
fn coverage_has_inode_number(inodes: &[InodeEdit], number: u32) -> (r: bool)
    requires forall|j: int| 0 <= j < inodes.len() ==> (#[trigger] inodes@[j]).wf(),
    ensures r ==> (exists|j: int| 0 <= j < inode_views(inodes@).len()
        && (#[trigger] inode_views(inodes@)[j]).number == number),
{
    let mut i = 0usize;
    while i < inodes.len()
        invariant i <= inodes.len(),
            forall|j: int| 0 <= j < inodes.len() ==> (#[trigger] inodes@[j]).wf(),
        decreases inodes.len() - i,
    {
        if inodes[i].number == number {
            assert(inodes@[i as int].wf());
            assert(inode_views(inodes@)[i as int].number == number);
            assert(exists|j: int| 0 <= j < inode_views(inodes@).len()
                && (#[trigger] inode_views(inodes@)[j]).number == number);
            return true;
        }
        i += 1;
    }
    false
}

fn check_coverage(inodes: &[InodeEdit], directories: &[DirectoryEdit], v: Ghost<UpdateView>,
    operation: Operation, source_directory: u32, destination_directory: u32, target: u32) -> (r: bool)
    requires forall|j: int| 0 <= j < inodes.len() ==> (#[trigger] inodes@[j]).wf(),
        v@.inode_edits == inode_views(inodes@), v@.directory_edits == directory_views(directories@),
        v@.operation == operation, v@.source_directory == source_directory,
        v@.destination_directory == destination_directory, v@.target == target,
    ensures r ==> covered(v@),
{
    if inodes.len() < 2 || inodes.len() > 3 || directories.len() < 1 || directories.len() > 3 {
        return false;
    }
    if !coverage_has_inode_number(inodes, target) { return false; }
    match operation {
        Operation::Rename => {
            if source_directory == destination_directory { return false; }
            if !coverage_has_inode_number(inodes, source_directory)
                || !coverage_has_inode_number(inodes, destination_directory) { return false; }
        },
        Operation::Link => {
            if !coverage_has_inode_number(inodes, destination_directory) { return false; }
        },
        Operation::Unlink => {
            if !coverage_has_inode_number(inodes, source_directory) { return false; }
        },
    }
    if inodes[0].number == inodes[1].number { return false; }
    if inodes.len() == 3 {
        if inodes[0].number == inodes[2].number || inodes[1].number == inodes[2].number {
            return false;
        }
    }
    assert forall|a: int, b: int| 0 <= a < b < v@.inode_edits.len() implies
        v@.inode_edits[a].number != v@.inode_edits[b].number by {
        assert(inodes@[a].wf() && inodes@[b].wf());
        assert(v@.inode_edits[a].number == inodes@[a].number);
        assert(v@.inode_edits[b].number == inodes@[b].number);
        if a == 0 {
            if b == 1 { } else { assert(b == 2 && inodes.len() == 3); }
        } else { assert(a == 1 && b == 2 && inodes.len() == 3); }
    }
    assert(covered(v@));
    true
}



proof fn inode_view_length(s:Seq<InodeEdit>)
    ensures inode_views(s).len()==s.len(),
{reveal(inode_views);}
proof fn inode_view_at(s:Seq<InodeEdit>,i:int)
    requires 0<=i<s.len(),
    ensures inode_views(s)[i]==s[i].view(),
{reveal(inode_views);}
proof fn directory_view_length(s:Seq<DirectoryEdit>)
    ensures directory_views(s).len()==s.len(),
{reveal(directory_views);}
proof fn directory_view_at(s:Seq<DirectoryEdit>,i:int)
    requires 0<=i<s.len(),
    ensures directory_views(s)[i]==s[i].view(),
{reveal(directory_views);}
fn make_plan(inodes:Vec<InodeEdit>,directories:Vec<DirectoryEdit>,view:Ghost<UpdateView>)->(r:Plan)
    requires planned(view@),inode_views(inodes@)==view@.inode_edits,directory_views(directories@)==view@.directory_edits,
        inodes.len()<=3,directories.len()<=3,
        forall|i:int|0<=i<inodes.len() ==> inodes@[i].wf(),
        forall|i:int|0<=i<directories.len() ==> directories@[i].wf(),
    ensures r.wf(),r.view()==view@,
{
    let ghost sealed=Seq::<UpdateView>::empty().push(view@);
    Plan{inodes,directories,checked:Ghost(sealed)}
}
proof fn discovered_operand_ids(v:UpdateView)
    requires discovered(v),
    ensures v.target!=v.source_directory,v.target!=v.destination_directory,
        v.operation!=Operation::Rename || v.source_directory!=v.destination_directory,
{reveal(discovered);}
proof fn encoded_inode_is_requested(v:UpdateView,e:&InodeEdit)
    requires e.wf(),inode_bound(v.before,e.view()),
        e.view().change.seconds==v.seconds,e.view().change.nanos==v.nanos,
        if e.number==v.target {
            !e.mtime && e.delta==match v.operation {Operation::Rename=>0int,Operation::Link=>1int,Operation::Unlink=>-1int}
        }else{
            e.mtime && match v.operation {
                Operation::Rename=>(e.number==v.source_directory && e.delta==if v.file_type==2{-1int}else{0int})
                    || (e.number==v.destination_directory && e.delta==if v.file_type==2{1int}else{0int}),
                Operation::Link=>e.number==v.destination_directory && e.delta==0,
                Operation::Unlink=>e.number==v.source_directory && e.delta==0,
            }
        },
    ensures requested_inode(v,e.view()),
{reveal(InodeEdit::wf);reveal(requested_inode);}
proof fn encoded_directory_is_requested(v:UpdateView,e:&DirectoryEdit,owner:u32,action:u8,target:u32,file_type:u8,
    name:Seq<u8>,old_parent:u32,new_parent:u32)
    requires e.wf(),directory_bound(v.before,e.view()),e.view().owner==owner,
        change_request(e.view().change,action,target,file_type,name,old_parent,new_parent),
        if action==0 {v.operation!=Operation::Link && owner==v.source_directory && target==v.target && file_type==v.file_type && name==v.old_name}
        else if action==1 {v.operation!=Operation::Unlink && owner==v.destination_directory && target==v.target && file_type==v.file_type && name==v.new_name}
        else {action==2 && v.operation==Operation::Rename && v.file_type==2 && owner==v.target && old_parent==v.source_directory && new_parent==v.destination_directory},
    ensures requested_directory(v,e.view()),
{reveal(DirectoryEdit::wf);reveal(requested_directory);}

#[verifier::opaque]
spec fn attach_edits(start:UpdateView,inodes:Seq<InodeEditView>,directories:Seq<DirectoryEditView>)->UpdateView {
    UpdateView{inode_edits:inodes,directory_edits:directories,..start}
}
#[verifier::opaque]
spec fn edits_attached(start:UpdateView,end:UpdateView)->bool {
    end==(UpdateView{inode_edits:end.inode_edits,directory_edits:end.directory_edits,..start})
}
proof fn attached_edit_fields(start:UpdateView,inodes:Seq<InodeEditView>,directories:Seq<DirectoryEditView>)
    ensures edits_attached(start,attach_edits(start,inodes,directories)),
        attach_edits(start,inodes,directories).inode_edits==inodes,
        attach_edits(start,inodes,directories).directory_edits==directories,
        attach_edits(start,inodes,directories).operation==start.operation,
        attach_edits(start,inodes,directories).source_directory==start.source_directory,
        attach_edits(start,inodes,directories).destination_directory==start.destination_directory,
        attach_edits(start,inodes,directories).target==start.target,
{reveal(attach_edits);reveal(edits_attached);}
proof fn attached_request_fields(start:UpdateView,end:UpdateView)
    requires edits_attached(start,end),
    ensures end.source==start.source,end.before==start.before,
        end.operation==start.operation,end.source_directory==start.source_directory,
        end.destination_directory==start.destination_directory,end.old_name==start.old_name,end.new_name==start.new_name,
        end.target==start.target,end.generation==start.generation,end.file_type==start.file_type,
        end.source_parent_generation==start.source_parent_generation,end.destination_parent_generation==start.destination_parent_generation,
        end.seconds==start.seconds,end.nanos==start.nanos,end.ancestry==start.ancestry,
{reveal(edits_attached);}
proof fn inode_request_survives_edit_attachment(start:UpdateView,end:UpdateView,e:InodeEditView)
    requires edits_attached(start,end),requested_inode(start,e),
    ensures requested_inode(end,e),
{reveal(edits_attached);reveal(requested_inode);}
proof fn directory_request_survives_edit_attachment(start:UpdateView,end:UpdateView,e:DirectoryEditView)
    requires edits_attached(start,end),requested_directory(start,e),
    ensures requested_directory(end,e),
{reveal(edits_attached);reveal(requested_directory);}
proof fn discovery_survives_edit_attachment(start:UpdateView,end:UpdateView)
    requires edits_attached(start,end),discovered(start),
    ensures discovered(end),
{reveal(edits_attached);reveal(discovered);}
#[verifier::rlimit(30)]
#[verifier::spinoff_prover]
fn finish_encoded_edits(inode_edits:Vec<InodeEdit>,directory_edits:Vec<DirectoryEdit>,request:Ghost<UpdateView>,
    operation:Operation,source_directory:u32,destination_directory:u32,target:u32)->(r:Result<Plan,Error>)
    requires discovered(request@),request@.operation==operation,request@.source_directory==source_directory,
        request@.destination_directory==destination_directory,request@.target==target,
        inode_edits.len()<=3,directory_edits.len()<=3,
        forall|j:int|0<=j<inode_edits.len() ==> inode_edits@[j].wf() && requested_inode(request@,inode_edits@[j].view()),
        forall|j:int|0<=j<directory_edits.len() ==> directory_edits@[j].wf() && requested_directory(request@,directory_edits@[j].view()),
    ensures match r {Ok(p)=>p.wf() && edits_attached(request@,p.view()),Err(_)=>true},
{
    hide(vstd::slice::axiom_spec_len);hide(InodeEdit::wf);hide(DirectoryEdit::wf);
    hide(InodeEdit::view);hide(DirectoryEdit::view);hide(Plan::view);hide(Plan::wf);
    hide(inode_views);hide(directory_views);hide(covered);
    let ghost view=attach_edits(request@,inode_views(inode_edits@),directory_views(directory_edits@));
    proof {attached_edit_fields(request@,inode_views(inode_edits@),directory_views(directory_edits@));}
    let inode_slice=inode_edits.as_slice();let directory_slice=directory_edits.as_slice();
    proof {vstd::slice::axiom_spec_len(inode_slice);vstd::slice::axiom_spec_len(directory_slice);}
    if !check_coverage(inode_slice,directory_slice,Ghost(view),operation,source_directory,destination_directory,target){return Err(Error::Rejected);}
    proof {inode_view_length(inode_edits@);directory_view_length(directory_edits@);}
    assert forall|j:int|0<=j<view.inode_edits.len() implies requested_inode(view,view.inode_edits[j]) by {
        inode_view_at(inode_edits@,j);
        inode_request_survives_edit_attachment(request@,view,inode_edits@[j].view());
    }
    assert forall|j:int|0<=j<view.directory_edits.len() implies requested_directory(view,view.directory_edits[j]) by {
        directory_view_at(directory_edits@,j);
        directory_request_survives_edit_attachment(request@,view,directory_edits@[j].view());
    }
    proof {discovery_survives_edit_attachment(request@,view);}
    assert(planned(view)) by {reveal(planned);}
    Ok(make_plan(inode_edits,directory_edits,Ghost(view)))
}
#[verifier::rlimit(10)]
#[verifier::spinoff_prover]
fn build_inode_edits(before:&ea_namespace::Namespace<'_,'_>,operation:Operation,source_directory:u32,destination_directory:u32,
    target:u32,file_type:u8,seconds:i64,nanos:u32,request:Ghost<UpdateView>)->(r:Result<Vec<InodeEdit>,Error>)
    requires before.wf(),discovered(request@),request@.before==before.view(),request@.operation==operation,
        request@.source_directory==source_directory,request@.destination_directory==destination_directory,
        request@.target==target,request@.file_type==file_type,request@.seconds==seconds,request@.nanos==nanos,
    ensures match r {Ok(edits)=>edits.len()<=3 && (forall|j:int|0<=j<edits.len() ==> edits@[j].wf() && requested_inode(request@,edits@[j].view())),Err(_)=>true},
{
    hide(InodeEdit::wf);hide(InodeEdit::view);hide(inode_views);
    proof {discovered_operand_ids(request@);}
    let mut inode_edits:Vec<InodeEdit>=Vec::new();
    let delta=match operation{Operation::Rename=>0i8,Operation::Link=>1i8,Operation::Unlink=>-1i8};
    let target_edit=match encode_inode(&before,target,false,seconds,nanos,delta){Some(e)=>e,None=>{return Err(Error::Rejected);}};
    proof {encoded_inode_is_requested(request@,&target_edit);}
    inode_edits=push_inode(inode_edits,target_edit,request);
    if matches!(operation,Operation::Rename) {
        let delta=if file_type==2{-1i8}else{0i8};
        let parent=match encode_inode(&before,source_directory,true,seconds,nanos,delta){Some(e)=>e,None=>{return Err(Error::Rejected);}};
        proof {encoded_inode_is_requested(request@,&parent);}
        inode_edits=push_inode(inode_edits,parent,request);
        let delta=if file_type==2{1i8}else{0i8};
        let parent=match encode_inode(&before,destination_directory,true,seconds,nanos,delta){Some(e)=>e,None=>{return Err(Error::Rejected);}};
        proof {encoded_inode_is_requested(request@,&parent);}
        inode_edits=push_inode(inode_edits,parent,request);
    }else{
        let parent_number=if matches!(operation,Operation::Link){destination_directory}else{source_directory};
        let parent=match encode_inode(&before,parent_number,true,seconds,nanos,0){Some(e)=>e,None=>{return Err(Error::Rejected);}};
        proof {encoded_inode_is_requested(request@,&parent);}
        inode_edits=push_inode(inode_edits,parent,request);
    }
    Ok(inode_edits)
}
#[verifier::rlimit(10)]
#[verifier::spinoff_prover]
fn build_directory_edits(source:&Snapshot<'_>,before:&ea_namespace::Namespace<'_,'_>,operation:Operation,
    source_directory:u32,old_name:&[u8],destination_directory:u32,new_name:&[u8],target:u32,file_type:u8,
    logical:u32,record:usize,request:Ghost<UpdateView>)->(r:Result<Vec<DirectoryEdit>,Error>)
    requires before.wf(),certified(before.view(),source.view()),discovered(request@),request@.before==before.view(),
        request@.operation==operation,request@.source_directory==source_directory,request@.destination_directory==destination_directory,
        request@.target==target,request@.file_type==file_type,request@.old_name==old_name@,request@.new_name==new_name@,
    ensures match r {Ok(edits)=>edits.len()<=3 && (forall|j:int|0<=j<edits.len() ==> edits@[j].wf() && requested_directory(request@,edits@[j].view())),Err(_)=>true},
{
    hide(vstd::slice::axiom_spec_len);hide(DirectoryEdit::wf);hide(DirectoryEdit::view);hide(directory_views);
    let mut directory_edits:Vec<DirectoryEdit>=Vec::new();
    if !matches!(operation,Operation::Link) {
        let removed=match encode_directory(source,&before,source_directory,logical,record,0,target,file_type,old_name,0,0){
            Some(e)=>e,None=>{return Err(Error::Rejected);}};
        proof {encoded_directory_is_requested(request@,&removed,source_directory,0,target,file_type,old_name@,0,0);}
        directory_edits=push_directory(directory_edits,removed,request);
    }
    if !matches!(operation,Operation::Unlink) {
        let inserted=match insert_directory(source,&before,destination_directory,target,file_type,new_name){
            Some(e)=>e,None=>{return Err(Error::NoSpace);}};
        proof {encoded_directory_is_requested(request@,&inserted,destination_directory,1,target,file_type,new_name@,0,0);}
        directory_edits=push_directory(directory_edits,inserted,request);
    }
    if matches!(operation,Operation::Rename) && file_type==2 {
        let moved=match encode_directory(source,&before,target,0,1,2,target,2,new_name,source_directory,destination_directory){
            Some(e)=>e,None=>{return Err(Error::Rejected);}};
        proof {encoded_directory_is_requested(request@,&moved,target,2,target,2,new_name@,source_directory,destination_directory);}
        directory_edits=push_directory(directory_edits,moved,request);
    }
    Ok(directory_edits)
}
#[verifier::rlimit(15)]
#[verifier::spinoff_prover]
fn encode_plan(source:&Snapshot<'_>,before:&ea_namespace::Namespace<'_,'_>,operation:Operation,
    source_directory:u32,old_name:&[u8],destination_directory:u32,new_name:&[u8],target:u32,file_type:u8,
    logical:u32,record:usize,seconds:i64,nanos:u32,request:Ghost<UpdateView>)->(r:Result<Plan,Error>)
    requires before.wf(),certified(before.view(),source.view()),discovered(request@),
        request@.source==source.view(),request@.before==before.view(),request@.operation==operation,
        request@.source_directory==source_directory,request@.destination_directory==destination_directory,
        request@.old_name==old_name@,request@.new_name==new_name@,request@.target==target,request@.file_type==file_type,
        request@.seconds==seconds,request@.nanos==nanos,
    ensures match r {Ok(p)=>p.wf() && edits_attached(request@,p.view()),Err(_)=>true},
{
    hide(vstd::slice::axiom_spec_len);
    hide(InodeEdit::wf);hide(DirectoryEdit::wf);hide(InodeEdit::view);hide(DirectoryEdit::view);hide(Plan::view);hide(Plan::wf);hide(inode_views);hide(directory_views);
    let inode_edits=match build_inode_edits(before,operation,source_directory,destination_directory,target,file_type,seconds,nanos,request){Ok(e)=>e,Err(e)=>{return Err(e);}};
    let directory_edits=match build_directory_edits(source,before,operation,source_directory,old_name,destination_directory,new_name,target,file_type,logical,record,request){Ok(e)=>e,Err(e)=>{return Err(e);}};
    finish_encoded_edits(inode_edits,directory_edits,request,operation,source_directory,destination_directory,target)
}
#[verifier::rlimit(15)]
#[verifier::spinoff_prover]
fn admit_projection(before:&ea_namespace::Namespace<'_,'_>,result:&[u8],operation:Operation,
    source_directory:u32,old_name:&[u8],destination_directory:u32,new_name:&[u8],
    target:u32,generation:u32,file_type:u8,source_parent_generation:u32,destination_parent_generation:u32,
    inode_budget:u32,node_budget:u64,byte_budget:u64)->(r:Option<Ghost<NamespaceView>>)
    requires before.wf(),
    ensures before.wf(),match r {Some(a)=>certified(a@,result@)
        && relation::relation(before.view().index.entries,a@.index.entries,operation,
            source_directory,old_name@,destination_directory,new_name@,target,generation,file_type,
            source_parent_generation,destination_parent_generation),None=>true},
{
    let after_source=Snapshot::from_bytes(result);
    let after=match ea_namespace::inspect(&after_source,inode_budget,node_budget,byte_budget){Some(a)=>a,None=>{return None;}};
    if !relation::check(before.index(),after.index(),operation,source_directory,old_name,destination_directory,new_name,
        target,generation,file_type,source_parent_generation,destination_parent_generation){return None;}
    Some(Ghost(after.view()))
}

#[verifier::opaque]
spec fn attach_result(start:UpdateView,result:Seq<u8>,after:NamespaceView,patches:Seq<ImageView>)->UpdateView {
    UpdateView{result,after,patches,..start}
}
proof fn result_attachment_fields(start:UpdateView,result:Seq<u8>,after:NamespaceView,patches:Seq<ImageView>)
    requires planned(start),
    ensures planned(attach_result(start,result,after,patches)),
        attach_result(start,result,after,patches).result==result,
        attach_result(start,result,after,patches).after==after,
        attach_result(start,result,after,patches).patches==patches,
        attach_result(start,result,after,patches).source==start.source,
        attach_result(start,result,after,patches).before==start.before,
        attach_result(start,result,after,patches).inode_edits==start.inode_edits,
        attach_result(start,result,after,patches).directory_edits==start.directory_edits,
        attach_result(start,result,after,patches).operation==start.operation,
        attach_result(start,result,after,patches).source_directory==start.source_directory,
        attach_result(start,result,after,patches).destination_directory==start.destination_directory,
        attach_result(start,result,after,patches).old_name==start.old_name,
        attach_result(start,result,after,patches).new_name==start.new_name,
        attach_result(start,result,after,patches).target==start.target,
        attach_result(start,result,after,patches).generation==start.generation,
        attach_result(start,result,after,patches).file_type==start.file_type,
        attach_result(start,result,after,patches).source_parent_generation==start.source_parent_generation,
        attach_result(start,result,after,patches).destination_parent_generation==start.destination_parent_generation,
        attach_result(start,result,after,patches).seconds==start.seconds,
        attach_result(start,result,after,patches).nanos==start.nanos,
{
    reveal(attach_result);
    plan_survives_attachment(start,attach_result(start,result,after,patches));
}

#[verifier::rlimit(15)]
#[verifier::spinoff_prover]
fn check_candidate(source:&Snapshot<'_>,plan:&Plan,patches:&PatchSet,result:&[u8],after:Ghost<NamespaceView>)
    ->(r:bool)
    requires plan.wf(),source.view()==plan.view().source,patches.wf(),
        patch_scope(patches.view(),plan.view().inode_edits,plan.view().directory_edits),
        result@==patch_set::apply(source.view(),patches.view()),certified(after@,result@),
        relation::relation(plan.view().before.index.entries,after@.index.entries,plan.view().operation,
            plan.view().source_directory,plan.view().old_name,plan.view().destination_directory,plan.view().new_name,
            plan.view().target,plan.view().generation,plan.view().file_type,plan.view().source_parent_generation,
            plan.view().destination_parent_generation),
    ensures r ==> valid(attach_result(plan.view(),result@,after@,patches.view())),
{
    hide(vstd::slice::axiom_spec_len);
    let ghost start=plan.view();
    let ghost view=attach_result(start,result@,after@,patches.view());
    proof {result_attachment_fields(start,result@,after@,patches.view());}
    let inode_slice=plan.inodes.as_slice();let directory_slice=plan.directories.as_slice();
    proof {vstd::slice::axiom_spec_len(inode_slice);vstd::slice::axiom_spec_len(directory_slice);}
    if !check_encoded(source,result,inode_slice,directory_slice,Ghost(view)){return false;}
    proof {assemble_candidate(view);}
    true
}

#[verifier::rlimit(10)]
#[verifier::spinoff_prover]
fn finish_candidate(plan:Plan,patches:PatchSet,result:Vec<u8>,after:Ghost<NamespaceView>)->(r:Update)
    requires plan.wf(),patches.wf(),valid(attach_result(plan.view(),result@,after@,patches.view())),
    ensures r.wf(),valid(r.view()),r.view()==attach_result(plan.view(),result@,after@,patches.view()),
        r.view().result==result@,r.view().patches==patches.view(),
        r.view().source==plan.view().source,r.view().operation==plan.view().operation,
        r.view().source_directory==plan.view().source_directory,
        r.view().destination_directory==plan.view().destination_directory,
        r.view().old_name==plan.view().old_name,r.view().new_name==plan.view().new_name,
        r.view().seconds==plan.view().seconds,r.view().nanos==plan.view().nanos,
{
    let ghost view=attach_result(plan.view(),result@,after@,patches.view());
    proof {result_attachment_fields(plan.view(),result@,after@,patches.view());}
    let ghost sealed=Seq::<UpdateView>::empty().push(view);
    Update{after:result,patches,checked:Ghost(sealed)}
}



#[verifier::rlimit(10)]
#[verifier::spinoff_prover]
fn materialize_plan(source:&Snapshot<'_>,plan:&Plan)->(r:Result<(Vec<u8>,PatchSet),Error>)
    requires plan.wf(),source.view()==plan.view().source,
    ensures plan.wf(),match r {Ok((result,patches))=>patches.wf()
        && patch_scope(patches.view(),plan.view().inode_edits,plan.view().directory_edits)
        && result@==patch_set::apply(source.view(),patches.view()),Err(_)=>true},
{
    hide(vstd::slice::axiom_spec_len);
    proof {
        assert(plan.inodes.len()<=3 && plan.directories.len()<=3
            && (forall|j:int|0<=j<plan.inodes.len() ==> plan.inodes@[j].wf())
            && (forall|j:int|0<=j<plan.directories.len() ==> plan.directories@[j].wf())) by {reveal(Plan::wf);}
    }
    let inode_slice=plan.inodes.as_slice();let directory_slice=plan.directories.as_slice();
    proof {vstd::slice::axiom_spec_len(inode_slice);vstd::slice::axiom_spec_len(directory_slice);}
    let patches=match stage(source,inode_slice,directory_slice){Some(p)=>p,None=>{return Err(Error::NoSpace);}};
    if !check_patch_scope(&patches,inode_slice,directory_slice){return Err(Error::Rejected);}
    let shadow=match source.overlay(&patches){Some(s)=>s,None=>{return Err(Error::Rejected);}};
    let result=match materialize(&shadow){Some(r)=>r,None=>{return Err(Error::Rejected);}};
    Ok((result,patches))
}



struct ReturnRequest {
    source:Seq<u8>,operation:Operation,source_directory:u32,destination_directory:u32,
    old_name:Seq<u8>,new_name:Seq<u8>,seconds:int,nanos:nat,
}
#[verifier::opaque]
spec fn return_summary(r:Result<Update,Error>,request:ReturnRequest)->bool {
    match r {Ok(u)=>u.wf() && valid(u.view()) && u.view().source==request.source
        && u.view().operation==request.operation && u.view().source_directory==request.source_directory
        && u.view().destination_directory==request.destination_directory
        && u.view().old_name==request.old_name && u.view().new_name==request.new_name
        && u.view().seconds==request.seconds && u.view().nanos==request.nanos,Err(_)=>true}
}
proof fn errors_satisfy_return_summary(request:ReturnRequest)
    ensures forall|error:Error| #[trigger] return_summary(Err(error),request),
{
    assert forall|error:Error| #[trigger] return_summary(Err(error),request) by {
        reveal(return_summary);
    }
}
proof fn return_summary_has_exact_fields(r:Result<Update,Error>,request:ReturnRequest)
    requires return_summary(r,request),
    ensures match r {Ok(u)=>u.wf() && valid(u.view()) && u.view().source==request.source
        && u.view().operation==request.operation && u.view().source_directory==request.source_directory
        && u.view().destination_directory==request.destination_directory
        && u.view().old_name==request.old_name && u.view().new_name==request.new_name
        && u.view().seconds==request.seconds && u.view().nanos==request.nanos,Err(_)=>true},
{reveal(return_summary);}
#[verifier::rlimit(10)]
#[verifier::spinoff_prover]
fn finish_return(plan:Plan,patches:PatchSet,result:Vec<u8>,after:Ghost<NamespaceView>,request:Ghost<ReturnRequest>)
    ->(r:Result<Update,Error>)
    requires plan.wf(),patches.wf(),valid(attach_result(plan.view(),result@,after@,patches.view())),
        plan.view().source==request@.source,plan.view().operation==request@.operation,
        plan.view().source_directory==request@.source_directory,
        plan.view().destination_directory==request@.destination_directory,
        plan.view().old_name==request@.old_name,plan.view().new_name==request@.new_name,
        plan.view().seconds==request@.seconds,plan.view().nanos==request@.nanos,
    ensures return_summary(r,request@),
{
    let update=finish_candidate(plan,patches,result,after);
    proof {reveal(return_summary);}
    Ok(update)
}


#[verifier::opaque]
spec fn discovered_inputs(source:Seq<u8>,before:NamespaceView,operation:Operation,
    source_directory:u32,old_name:Seq<u8>,destination_directory:u32,new_name:Seq<u8>,
    target:u32,generation:u32,file_type:u8,source_parent_generation:u32,destination_parent_generation:u32,
    seconds:int,nanos:nat,path:Seq<u32>)->bool {
    discovered(UpdateView{source,result:source,before,after:before,operation,source_directory,destination_directory,
        old_name,new_name,target,generation,file_type,source_parent_generation,destination_parent_generation,
        seconds,nanos,patches:Seq::empty(),inode_edits:Seq::empty(),directory_edits:Seq::empty(),ancestry:path})
}
proof fn namespace_components_share_one_allocation(before:&ea_namespace::Namespace<'_,'_>)
    requires before.wf(),
    ensures before.view().index.volume==before.view().allocation,
        before.view().tree.index==before.view().index,
        before.view().index.nodes.volume==before.view().allocation,
{
    reveal(ea_namespace::valid);
    reveal(crate::ea_directory_index::valid);
}

#[verifier::rlimit(30)]
#[verifier::spinoff_prover]
fn prepare_discovered(source:&Snapshot<'_>,before:&ea_namespace::Namespace<'_,'_>,operation:Operation,
    source_directory:u32,old_name:&[u8],destination_directory:u32,new_name:&[u8],
    target:u32,generation:u32,file_type:u8,logical:u32,record:usize,
    source_parent_generation:u32,destination_parent_generation:u32,seconds:i64,nanos:u32,path:Ghost<Seq<u32>>,
    inode_budget:u32,node_budget:u64,byte_budget:u64)->(r:Result<Update,Error>)
    requires before.wf(),
        before.view().index.volume==before.view().allocation,
        before.view().tree.index==before.view().index,
        before.view().index.nodes.volume==before.view().allocation,
        discovered_inputs(source.view(),before.view(),operation,source_directory,old_name@,
        destination_directory,new_name@,target,generation,file_type,source_parent_generation,destination_parent_generation,
        seconds as int,nanos as nat,path@),
    ensures return_summary(r,ReturnRequest{source:source.view(),operation,source_directory,destination_directory,old_name:old_name@,new_name:new_name@,seconds:seconds as int,nanos:nanos as nat}),
{
    hide(certified);
    hide(Update::view);hide(Update::wf);
    hide(vstd::slice::axiom_spec_len);hide(Plan::wf);hide(Plan::view);
    let ghost returning=ReturnRequest{source:source.view(),operation,source_directory,destination_directory,old_name:old_name@,new_name:new_name@,seconds:seconds as int,nanos:nanos as nat};
    proof {errors_satisfy_return_summary(returning);}
    let ghost request=UpdateView{source:source.view(),result:source.view(),before:before.view(),after:before.view(),
        operation,source_directory,destination_directory,old_name:old_name@,new_name:new_name@,target,generation,file_type,
        source_parent_generation:source_parent_generation,destination_parent_generation:destination_parent_generation,
        seconds:seconds as int,nanos:nanos as nat,patches:Seq::empty(),inode_edits:Seq::empty(),directory_edits:Seq::empty(),ancestry:path@};
    assert(discovered(request) && certified(before.view(),source.view())) by {reveal(discovered_inputs);reveal(discovered);}
    let plan=match encode_plan(source,before,operation,source_directory,old_name,destination_directory,new_name,target,file_type,logical,record,seconds,nanos,Ghost(request)){Ok(p)=>p,Err(e)=>{return Err(e);}};
    let ghost plan_view=plan.view();
    proof {attached_request_fields(request,plan_view);}
    let (result,patches)=match materialize_plan(source,&plan){
        Ok(built)=>built,Err(error)=>{return Err(error);}
    };
    let result_slice=result.as_slice();
    proof {vstd::slice::axiom_spec_len(result_slice);}
    let after=match admit_projection(before,result_slice,operation,source_directory,old_name,destination_directory,new_name,
        target,generation,file_type,source_parent_generation,destination_parent_generation,inode_budget,node_budget,byte_budget){
        Some(a)=>a,None=>{return Err(Error::Rejected);}
    };
    if !check_candidate(source,&plan,&patches,result_slice,after){return Err(Error::Rejected);}
    finish_return(plan,patches,result,after,Ghost(returning))
}

#[verifier::rlimit(30)]
#[verifier::spinoff_prover]
fn prepare(source:&Snapshot<'_>,operation:Operation,source_directory:u32,old_name:&[u8],destination_directory:u32,new_name:&[u8],
    seconds:i64,nanos:u32,inode_budget:u32,node_budget:u64,byte_budget:u64)->(r:Result<Update,Error>)
    ensures return_summary(r,ReturnRequest{source:source.view(),operation,source_directory,destination_directory,old_name:old_name@,new_name:new_name@,seconds:seconds as int,nanos:nanos as nat}),
{
    hide(Update::view);
    hide(Update::wf);
    hide(vstd::slice::axiom_spec_len);
    hide(crate::ea_directory_index::source_has_name);
    hide(crate::namespace_model::has_name);
    let ghost returning=ReturnRequest{source:source.view(),operation,source_directory,destination_directory,old_name:old_name@,new_name:new_name@,seconds:seconds as int,nanos:nanos as nat};
    proof {errors_satisfy_return_summary(returning);}
    if source.partition_bytes()<8192 || source.partition_bytes()>MAX_IMAGE_BYTES as u64{return Err(Error::Invalid);}
    let before=match ea_namespace::inspect(source,inode_budget,node_budget,byte_budget){Some(b)=>b,None=>{return Err(Error::Invalid);}};
    let superblock=match source.capture_bytes(1024,1024){Some(b)=>b,None=>{return Err(Error::Invalid);}};
    match feature_policy::is_readonly(&superblock){Some(true)=>{return Err(Error::ReadOnly);},Some(false)=>{},None=>{return Err(Error::Invalid);}}
    if !proper_name(old_name) || !matches!(operation,Operation::Unlink) && !proper_name(new_name){return Err(Error::Invalid);}
    if matches!(operation,Operation::Rename) && source_directory==destination_directory{return Err(Error::Rejected);}
    let entry=match before.lookup(source_directory,old_name){Some(e)=>e,None=>{return Err(Error::NotFound);}};
    let (_,target,generation,file_type)=entry.identity();let (logical,record)=entry.location();
    if file_type!=1 && file_type!=2 || !matches!(operation,Operation::Rename) && file_type!=1{return Err(Error::Rejected);}
    if target==source_directory || target==destination_directory || target==2{return Err(Error::Rejected);}
    if !matches!(operation,Operation::Unlink) && before.lookup(destination_directory,new_name).is_some(){return Err(Error::Exists);}
    let nodes=before.index().nodes();
    let source_slot=match nodes.get(source_directory){Some(n)=>n,None=>{return Err(Error::Rejected);}};
    let destination_slot=match nodes.get(destination_directory){Some(n)=>n,None=>{return Err(Error::Rejected);}};
    let target_slot=match nodes.get(target){Some(n)=>n,None=>{return Err(Error::Rejected);}};
    if source_slot.mode & 0xf000!=0x4000 || destination_slot.mode & 0xf000!=0x4000{return Err(Error::Rejected);}
    if matches!(operation,Operation::Unlink) && target_slot.links<=1{return Err(Error::Rejected);}
    if matches!(operation,Operation::Rename) && file_type==2 && (source_slot.links<=1 || destination_slot.links<=1){return Err(Error::Rejected);}
    let path=if matches!(operation,Operation::Rename) && file_type==2 {
        match ancestry(&before,target,destination_directory){Some(p)=>p,None=>{return Err(Error::Rejected);}}
    }else{Vec::new()};
    assert(discovered_inputs(source.view(),before.view(),operation,source_directory,old_name@,
        destination_directory,new_name@,target,generation,file_type,source_slot.generation,destination_slot.generation,
        seconds as int,nanos as nat,path@)) by {reveal(discovered_inputs);reveal(discovered);}
    proof {namespace_components_share_one_allocation(&before);}
    prepare_discovered(source,&before,operation,source_directory,old_name,destination_directory,new_name,
        target,generation,file_type,logical,record,source_slot.generation,destination_slot.generation,seconds,nanos,Ghost(path@),
        inode_budget,node_budget,byte_budget)
}

pub fn prepare_rename(source:&Snapshot<'_>,old_dir:u32,old_name:&[u8],new_dir:u32,new_name:&[u8],
    seconds:i64,nanos:u32,inode_budget:u32,node_budget:u64,byte_budget:u64)->(r:Result<Update,Error>)
    ensures match r{Ok(u)=>u.wf() && valid(u.view()) && u.view().source==source.view()
        && u.view().operation==Operation::Rename && u.view().source_directory==old_dir && u.view().destination_directory==new_dir
        && u.view().old_name==old_name@ && u.view().new_name==new_name@ && u.view().seconds==seconds && u.view().nanos==nanos,Err(_)=>true},
{
    let result=prepare(source,Operation::Rename,old_dir,old_name,new_dir,new_name,seconds,nanos,inode_budget,node_budget,byte_budget);
    proof {return_summary_has_exact_fields(result,ReturnRequest{source:source.view(),operation:Operation::Rename,source_directory:old_dir,destination_directory:new_dir,old_name:old_name@,new_name:new_name@,seconds:seconds as int,nanos:nanos as nat});}
    result
}
pub fn prepare_link(source:&Snapshot<'_>,source_dir:u32,source_name:&[u8],dest_dir:u32,new_name:&[u8],
    seconds:i64,nanos:u32,inode_budget:u32,node_budget:u64,byte_budget:u64)->(r:Result<Update,Error>)
    ensures match r{Ok(u)=>u.wf() && valid(u.view()) && u.view().source==source.view()
        && u.view().operation==Operation::Link && u.view().source_directory==source_dir && u.view().destination_directory==dest_dir
        && u.view().old_name==source_name@ && u.view().new_name==new_name@ && u.view().seconds==seconds && u.view().nanos==nanos,Err(_)=>true},
{
    let result=prepare(source,Operation::Link,source_dir,source_name,dest_dir,new_name,seconds,nanos,inode_budget,node_budget,byte_budget);
    proof {return_summary_has_exact_fields(result,ReturnRequest{source:source.view(),operation:Operation::Link,source_directory:source_dir,destination_directory:dest_dir,old_name:source_name@,new_name:new_name@,seconds:seconds as int,nanos:nanos as nat});}
    result
}
pub fn prepare_unlink(source:&Snapshot<'_>,directory:u32,name:&[u8],seconds:i64,nanos:u32,
    inode_budget:u32,node_budget:u64,byte_budget:u64)->(r:Result<Update,Error>)
    ensures match r{Ok(u)=>u.wf() && valid(u.view()) && u.view().source==source.view()
        && u.view().operation==Operation::Unlink && u.view().source_directory==directory && u.view().destination_directory==directory
        && u.view().old_name==name@ && u.view().new_name==Seq::<u8>::empty() && u.view().seconds==seconds && u.view().nanos==nanos,Err(_)=>true},
{
    let empty:&[u8]=&[];
    proof {vstd::slice::axiom_spec_len(empty);assert(empty@ =~= Seq::<u8>::empty());}
    let result=prepare(source,Operation::Unlink,directory,name,directory,empty,seconds,nanos,inode_budget,node_budget,byte_budget);
    proof {return_summary_has_exact_fields(result,ReturnRequest{source:source.view(),operation:Operation::Unlink,source_directory:directory,destination_directory:directory,old_name:name@,new_name:empty@,seconds:seconds as int,nanos:nanos as nat});}
    result
}

pub proof fn candidate_images_are_certified_and_have_equal_length(v:UpdateView)
    requires valid(v),
    ensures certified(v.before,v.source),certified(v.after,v.result),v.result.len()==v.source.len(),8192<=v.source.len()<=MAX_IMAGE_BYTES,
{reveal(valid);reveal(planned);reveal(discovered);}
pub proof fn prepared_edits_have_exact_operation(v:UpdateView)
    requires valid(v),ensures exact_operation(v),
{reveal(valid);reveal(planned);reveal(discovered);}
pub proof fn prepared_edits_preserve_every_unrelated_source_byte(v:UpdateView,i:int)
    requires valid(v),0<=i<v.source.len(),!editable(i,v.inode_edits,v.directory_edits),
    ensures v.result[i]==v.source[i],
{reveal(valid);reveal(planned);reveal(discovered);}
pub proof fn prepared_inode_edits_have_exact_links_times_and_source_positions(v:UpdateView,j:int)
    requires valid(v),0<=j<v.inode_edits.len(),
    ensures requested_inode(v,v.inode_edits[j]),
        ns_inode_links::valid(v.inode_edits[j].change),
        bytes::le16(v.inode_edits[j].change.after,26) as int==bytes::le16(v.inode_edits[j].change.before,26) as int+v.inode_edits[j].change.delta,
        crate::inode_time_fields::seconds(v.inode_edits[j].change.after,crate::inode_time_fields::Field::Ctime)==v.seconds,
        crate::inode_time_fields::nanoseconds(v.inode_edits[j].change.after,crate::inode_time_fields::Field::Ctime)==v.nanos,
        v.inode_edits[j].change.seconds==v.seconds,v.inode_edits[j].change.nanos==v.nanos,
        v.inode_edits[j].ordinal==v.before.index.nodes.slots[v.inode_edits[j].number as int].ordinal,
        v.inode_edits[j].position==inode_node(v.before,v.inode_edits[j]).position,
        v.inode_edits[j].change.before==inode_node(v.before,v.inode_edits[j]).raw,
{reveal(valid);reveal(planned);reveal(discovered);reveal(requested_inode);reveal(inode_bound);
 ns_inode_links::namespace_link_changes_have_the_exact_positive_linux_count(v.inode_edits[j].change);
 ns_inode_links::namespace_link_changes_publish_the_exact_requested_times(v.inode_edits[j].change);
}
pub proof fn prepared_directory_moves_exclude_the_destination_ancestry(v:UpdateView)
    requires valid(v),v.operation==Operation::Rename,v.file_type==2,
    ensures ancestry_path(v.before,v.ancestry,v.target,v.destination_directory),
{reveal(valid);reveal(planned);reveal(discovered);}
pub proof fn prepared_edits_never_authorize_READONLY_source_images(v:UpdateView)
    requires valid(v),ensures !feature_policy::readonly(v.source.subrange(1024,2048)),
{reveal(valid);reveal(planned);reveal(discovered);}

pub proof fn prepared_patches_target_only_checked_directory_and_inode_table_blocks(v:UpdateView)
    requires valid(v),
    ensures patch_scope(v.patches,v.inode_edits,v.directory_edits),
{reveal(valid);reveal(planned);reveal(discovered);}
pub proof fn prepared_inode_edits_preserve_extent_sector_and_EA_bytes(v:UpdateView,j:int,i:int)
    requires valid(v),0<=j<v.inode_edits.len(),0<=i<256,
        !ns_inode_links::mutable(v.inode_edits[j].change.touch_mtime,i),
    ensures v.result[v.inode_edits[j].position as int+i]==v.source[v.inode_edits[j].position as int+i],
{
    reveal(valid);reveal(planned);reveal(discovered);reveal(requested_inode);reveal(inode_bound);
    let e=v.inode_edits[j];let p=e.position as int;
    ns_inode_links::namespace_link_changes_preserve_identity_extents_and_ea_billing_bytes(e.change,i);
    assert(e.change.before==v.source.subrange(p,p+256) && e.change.after==v.result.subrange(p,p+256));
}

pub proof fn every_prepared_patch_has_an_actual_inode_or_directory_block_witness(v:UpdateView,i:int)
    requires valid(v),0<=i<v.patches.len(),
    ensures (exists|j:int|0<=j<v.inode_edits.len() && (#[trigger] v.inode_edits[j]).position/4096==v.patches[i].block)
        || (exists|j:int|0<=j<v.directory_edits.len() && (#[trigger] v.directory_edits[j]).block==v.patches[i].block),
{
    reveal(valid);reveal(patch_scope);
    assert(patch_target_known(v.patches[i].block,v.inode_edits,v.directory_edits));
    reveal(patch_target_known);
}

}
