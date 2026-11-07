// SPDX-License-Identifier: MPL-2.0

//! Allocation-free regular replacing rename and exchange over certified images.
use vstd::prelude::*;
use crate::{bytes, ea_directory::{self, DirectoryView}, ea_namespace::{self, NamespaceView},
    ea_source, feature_policy, inode, ns_dir_edit, ns_inode_links, ns_record_target,
    ns_file_rename_relation as relation, ns_namespace_edit as source_binding,
    patch_set::{self, PatchSet}, snapshot::Snapshot, transaction::ImageView};
pub use crate::ns_file_rename_relation::Operation;
verus! {
pub const MAX_IMAGE_BYTES:usize=268435456;
pub enum Error { Invalid, ReadOnly, NotFound, Exists, NoSpace, Rejected }
pub open spec fn certified(c:NamespaceView,source:Seq<u8>)->bool { source_binding::certified(c,source) }
pub struct InodeEditView {
    pub number:u32,pub ordinal:usize,pub position:u64,pub change:ns_inode_links::Change,
    pub extra:Seq<ns_inode_links::Change>,
}
pub open spec fn inode_after(e:InodeEditView)->Seq<u8> {
    if e.extra.len()==0 {e.change.after} else {e.extra[0].after}
}
pub open spec fn base_inode(e:InodeEditView)->source_binding::InodeEditView {
    source_binding::InodeEditView{number:e.number,ordinal:e.ordinal,position:e.position,change:e.change}
}
#[verifier::opaque]
pub open spec fn inode_bound(before:NamespaceView,e:InodeEditView)->bool {
    source_binding::inode_bound(before,base_inode(e)) && e.extra.len()<=1 &&
        (e.extra.len()==1 ==> ns_inode_links::valid(e.extra[0]) && e.extra[0].before==e.change.after
            && e.extra[0].number==e.number && e.extra[0].inodes==e.change.inodes
            && e.extra[0].seed==e.change.seed && e.extra[0].huge==e.change.huge
            && e.extra[0].touch_mtime && e.extra[0].delta==0
            && e.extra[0].seconds==e.change.seconds && e.extra[0].nanos==e.change.nanos)
}
pub enum DirectoryChange { Remove(ns_dir_edit::RemoveChange), Target(ns_record_target::Change) }
pub open spec fn change_before(c:DirectoryChange)->crate::directory_piece::PieceView {
    match c {DirectoryChange::Remove(e)=>e.before,DirectoryChange::Target(e)=>e.before}
}
pub open spec fn change_after(c:DirectoryChange)->crate::directory_piece::PieceView {
    match c {DirectoryChange::Remove(e)=>e.after,DirectoryChange::Target(e)=>e.after}
}
pub open spec fn change_valid(c:DirectoryChange)->bool {
    match c {DirectoryChange::Remove(e)=>ns_dir_edit::remove_valid(e),DirectoryChange::Target(e)=>ns_record_target::valid(e)}
}
pub struct DirectoryEditView {
    pub owner:u32,pub ordinal:usize,pub logical:u32,pub block:u32,pub changes:Seq<DirectoryChange>,
}
pub open spec fn directory_before(e:DirectoryEditView)->crate::directory_piece::PieceView {change_before(e.changes[0])}
pub open spec fn directory_after(e:DirectoryEditView)->crate::directory_piece::PieceView {change_after(e.changes.last())}
pub open spec fn directory_source_matches(before:NamespaceView,e:DirectoryEditView,d:DirectoryView)->bool {
    ea_directory::valid(d) && d.volume==before.allocation && d.ordinal==e.ordinal
        && ea_directory::owner(d)==e.owner && e.logical<d.pieces.len() && e.logical<d.physical.len()
        && e.block==d.physical[e.logical as int] && directory_before(e)==d.pieces[e.logical as int]
}
#[verifier::opaque]
pub open spec fn directory_bound(before:NamespaceView,e:DirectoryEditView)->bool {
    ea_namespace::valid(before) && !directory_before(e).indexed && 1<=e.changes.len()<=2
        && (exists|d:DirectoryView| #[trigger] directory_source_matches(before,e,d))
        && (forall|i:int|0<=i<e.changes.len() ==> change_valid(e.changes[i]))
        && (e.changes.len()==2 ==> change_after(e.changes[0])==change_before(e.changes[1]))
}
pub struct UpdateView {
    pub source:Seq<u8>,pub result:Seq<u8>,pub before:NamespaceView,pub after:NamespaceView,
    pub operation:Operation,pub source_directory:u32,pub destination_directory:u32,
    pub old_name:Seq<u8>,pub new_name:Seq<u8>,pub target:u32,pub generation:u32,
    pub displaced:u32,pub displaced_generation:u32,pub source_parent_generation:u32,pub destination_parent_generation:u32,
    pub seconds:int,pub nanos:nat,pub patches:Seq<ImageView>,
    pub inode_edits:Seq<InodeEditView>,pub directory_edits:Seq<DirectoryEditView>,
}
pub open spec fn exact_operation(v:UpdateView)->bool {
    relation::relation(v.before.index.entries,v.after.index.entries,v.operation,
        v.source_directory,v.old_name,v.destination_directory,v.new_name,v.target,v.generation,
        v.displaced,v.displaced_generation,v.source_parent_generation,v.destination_parent_generation)
}
#[verifier::opaque]
pub open spec fn requested_inode(v:UpdateView,e:InodeEditView)->bool {
    inode_bound(v.before,e) && e.change.seconds==v.seconds && e.change.nanos==v.nanos &&
    if e.number==v.target { !e.change.touch_mtime && e.change.delta==0 && e.extra.len()==0 }
    else if e.number==v.displaced { !e.change.touch_mtime
        && e.change.delta==if v.operation==Operation::Replace {-1int}else{0int} && e.extra.len()==0 }
    else { e.change.touch_mtime && e.change.delta==0
        && (e.number==v.source_directory || e.number==v.destination_directory)
        && e.extra.len()==if v.source_directory==v.destination_directory {1int}else{0int} }
}
pub open spec fn requested_change(v:UpdateView,owner:u32,c:DirectoryChange)->bool {
    match c {
        DirectoryChange::Remove(e)=>v.operation==Operation::Replace && owner==v.source_directory
            && e.record<e.before.block.records.len() && e.before.block.records[e.record as int].inode==v.target
            && e.before.block.records[e.record as int].file_type==1 && crate::ns_rename_block::name(e.before,e.record as int)==v.old_name,
        DirectoryChange::Target(e)=> e.record<e.before.block.records.len() && e.file_type==1
            && e.before.block.records[e.record as int].file_type==1 &&
            ((owner==v.destination_directory && crate::ns_rename_block::name(e.before,e.record as int)==v.new_name
                && e.before.block.records[e.record as int].inode==v.displaced && e.target==v.target)
            || (v.operation==Operation::Exchange && owner==v.source_directory
                && crate::ns_rename_block::name(e.before,e.record as int)==v.old_name
                && e.before.block.records[e.record as int].inode==v.target && e.target==v.displaced)),
    }
}
#[verifier::opaque]
pub open spec fn requested_directory(v:UpdateView,e:DirectoryEditView)->bool {
    directory_bound(v.before,e) && (forall|i:int|0<=i<e.changes.len() ==> requested_change(v,e.owner,e.changes[i]))
}
#[verifier::opaque]
pub open spec fn discovered(v:UpdateView)->bool {
    certified(v.before,v.source) && 8192<=v.source.len()<=MAX_IMAGE_BYTES
        && !feature_policy::readonly(v.source.subrange(1024,2048))
        && crate::ns_rename_block::proper_name(v.old_name) && crate::ns_rename_block::proper_name(v.new_name)
        && v.target!=v.source_directory && v.target!=v.destination_directory
        && v.displaced!=v.source_directory && v.displaced!=v.destination_directory
}
pub open spec fn covered(v:UpdateView)->bool {
    if v.target==v.displaced { v.inode_edits.len()==0 && v.directory_edits.len()==0 }
    else { 3<=v.inode_edits.len()<=4 && 1<=v.directory_edits.len()<=2
        && (exists|j:int|0<=j<v.inode_edits.len() && (#[trigger] v.inode_edits[j]).number==v.target)
        && (exists|j:int|0<=j<v.inode_edits.len() && (#[trigger] v.inode_edits[j]).number==v.displaced)
        && (exists|j:int|0<=j<v.inode_edits.len() && (#[trigger] v.inode_edits[j]).number==v.source_directory)
        && (exists|j:int|0<=j<v.inode_edits.len() && (#[trigger] v.inode_edits[j]).number==v.destination_directory)
        && (forall|a:int,b:int|0<=a<b<v.inode_edits.len() ==> v.inode_edits[a].number!=v.inode_edits[b].number) }
}
#[verifier::opaque]
pub open spec fn planned(v:UpdateView)->bool {
    discovered(v) && covered(v)
        && (forall|i:int|0<=i<v.inode_edits.len() ==> requested_inode(v,v.inode_edits[i]))
        && (forall|i:int|0<=i<v.directory_edits.len() ==> requested_directory(v,v.directory_edits[i]))
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
        &&& e.change.before == v.source.subrange(p,p+256) && inode_after(e) == v.result.subrange(p,p+256)
    })
    &&& (forall|j: int| #![trigger v.directory_edits[j]] 0 <= j < v.directory_edits.len() ==> {
        let e = v.directory_edits[j]; let p = e.block as int * 4096;
        &&& 8192 <= p && p + 4096 <= v.source.len()
        &&& directory_before(e).block.raw == v.source.subrange(p,p+4096)
        &&& directory_after(e).block.raw == v.result.subrange(p,p+4096)
    })
    &&& frame(v)
}
#[verifier::opaque]
pub open spec fn valid(v:UpdateView)->bool {
    &&& planned(v) && (v.target==v.displaced ==> v.source==v.result && v.patches.len()==0) && certified(v.after,v.result) && exact_operation(v)
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

struct InodeEdit { position:u64, number:u32, inodes:u32,seed:u32,huge:bool, delta:i8, mtime:bool, before:Vec<u8>, after:Vec<u8>, checked:Ghost<InodeEditView> }
impl InodeEdit {
    closed spec fn view(&self)->InodeEditView { self.checked@ }
    closed spec fn wf(&self)->bool { ns_inode_links::valid(self.view().change) && self.view().extra.len()<=1 && (self.view().extra.len()==1 ==> ns_inode_links::valid(self.view().extra[0]) && self.view().extra[0].before==self.view().change.after)
        && self.position==self.view().position && self.number==self.view().number
        && self.number==self.view().change.number && self.inodes==self.view().change.inodes && self.seed==self.view().change.seed && self.huge==self.view().change.huge && self.delta==self.view().change.delta
        && self.mtime==self.view().change.touch_mtime && self.before@==self.view().change.before && self.after@==inode_after(self.view()) }

}
struct DirectoryEdit { block:u32, inodes:u32,seed:u32,logical:u32,count:u32,large:bool, before:Vec<u8>, after:Vec<u8>, checked:Ghost<DirectoryEditView> }
impl DirectoryEdit {
    closed spec fn view(&self)->DirectoryEditView { self.checked@ }
    closed spec fn wf(&self)->bool { 1<=self.view().changes.len()<=2 && (forall|i:int|0<=i<self.view().changes.len() ==> change_valid(self.view().changes[i])) && (self.view().changes.len()==2 ==> change_after(self.view().changes[0])==change_before(self.view().changes[1])) && !directory_before(self.view()).indexed && self.block == self.view().block
        && self.before@ == directory_before(self.view()).block.raw && self.after@ == directory_after(self.view()).block.raw
        && directory_after(self.view())==ns_dir_edit::view(self.after@,self.inodes,self.seed,false,self.logical,self.count,self.large) }
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
#[verifier::rlimit(20)]
#[verifier::spinoff_prover]
fn encode_inode(before:&ea_namespace::Namespace<'_,'_>,number:u32,mtime:bool,seconds:i64,nanos:u32,delta:i8)
    ->(r:Option<InodeEdit>)
    requires before.wf(),
    ensures match r {Some(e)=>e.wf() && inode_bound(before.view(),e.view()) && e.number==number && e.view().extra.len()==0
        && e.delta==delta && e.mtime==mtime && e.view().change.seconds==seconds && e.view().change.nanos==nanos,None=>true},
{
    hide(vstd::slice::axiom_spec_len);
    let nodes=before.index().nodes();
    let slot=match nodes.get(number){Some(n)=>n,None=>{return None;}};
    let index=before.allocation().integrity().reference_census().index();
    let node=match index.node(number){Some(n)=>n,None=>{return None;}};
    proof {source_binding::namespace_inode_node_is_exact(before.view(),number,node.view());}
    let raw=node.raw();let position=node.position();
    proof {vstd::slice::axiom_spec_len(raw);}
    let (_,inodes,_,seed)=node.inode_parameters();let huge=index.header().huge_files();
    let changed=match ns_inode_links::encode(raw,number,inodes,seed,huge,mtime,seconds,nanos,delta){Some(c)=>c,None=>{return None;}};
    let ghost change=ns_inode_links::Change{before:raw@,after:changed@,number,inodes,seed,huge,touch_mtime:mtime,seconds:seconds as int,nanos:nanos as nat,delta:delta as int};
    let ghost view=InodeEditView{number,ordinal:slot.ordinal,position,change,extra:Seq::empty()};
    proof {source_binding::assemble_inode_binding(before.view(),node.view(),change,slot.ordinal); reveal(inode_bound);}
    Some(InodeEdit{position,number,inodes,seed,huge,delta,mtime,before:copy(raw),after:changed,checked:Ghost(view)})
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
    requires inodes.len()<=4,directories.len()<=4,
    ensures match r {Some(p)=>p.wf(),None=>true},
{
    let mut patches=PatchSet::new();let mut i=0usize;
    while i<directories.len()
        invariant i<=directories.len()<=4,patches.wf(),
        decreases directories.len()-i,
    {
        patches=match patches.upsert(directories[i].block,&directories[i].after){Ok(p)=>p,Err(_)=>{return None;}};
        i+=1;
    }
    let mut i=0usize;
    while i<inodes.len()
        invariant i<=inodes.len()<=4,patches.wf(),
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
                &&& e.change.before==v@.source.subrange(p,p+256) && inode_after(e)==v@.result.subrange(p,p+256)
            },
        decreases inodes.len()-i,
    {
        let e=&inodes[i];let p=e.position;
        assert(p==v@.inode_edits[i as int].position && e.before@==v@.inode_edits[i as int].change.before
            && e.after@==inode_after(v@.inode_edits[i as int])) by {
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
                &&& e.change.before==v@.source.subrange(p,p+256) && inode_after(e)==v@.result.subrange(p,p+256)
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
    patches.len()<=6 && forall|i:int|#![trigger patches[i]] 0<=i<patches.len() ==>
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
    let count=patches.len();if count>6{return false;}
    let mut i=0usize;
    while i<count
        invariant patches.wf(),count==patches.view().len(),count<=6,i<=count,
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
fn push_inode(mut edits:Vec<InodeEdit>,edit:InodeEdit,request:Ghost<UpdateView>)->(r:Vec<InodeEdit>)
    requires edits.len()<4,edit.wf(),requested_inode(request@,edit.view()),
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
    requires edits.len()<4,edit.wf(),requested_directory(request@,edit.view()),
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

// A shared parent is resealed twice, matching the two changed directory words.
fn second_parent_change(mut e:InodeEdit,seconds:i64,nanos:u32,before:Ghost<NamespaceView>)->(r:Option<InodeEdit>)
    requires e.wf(),inode_bound(before@,e.view()),e.mtime,e.delta==0,e.view().extra.len()==0,
        e.view().change.seconds==seconds,e.view().change.nanos==nanos,
    ensures match r {Some(r)=>r.wf() && inode_bound(before@,r.view()) && r.number==e.number
        && r.delta==0 && r.mtime && r.view().extra.len()==1 && r.view().change==e.view().change
        && r.view().change.seconds==seconds && r.view().change.nanos==nanos,None=>true},
{
    let ghost first=e.view();
    let raw=e.after.as_slice();
    let changed=match ns_inode_links::encode(raw,e.number,e.inodes,e.seed,e.huge,true,seconds,nanos,0){Some(c)=>c,None=>{return None;}};
    let ghost c=ns_inode_links::Change{before:raw@,after:changed@,number:e.number,inodes:first.change.inodes,
        seed:first.change.seed,huge:first.change.huge,touch_mtime:true,seconds:seconds as int,nanos:nanos as nat,delta:0};
    let ghost view=InodeEditView{extra:Seq::empty().push(c),..first};
    proof {reveal(inode_bound);}
    Some(InodeEdit{position:e.position,number:e.number,inodes:e.inodes,seed:e.seed,huge:e.huge,delta:0,mtime:true,before:e.before,after:changed,checked:Ghost(view)})
}

pub open spec fn action_matches(c:DirectoryChange,record:usize,remove:bool,old_target:u32,new_target:u32,name:Seq<u8>)->bool {
    change_before(c).block.records.len()>record
        && change_before(c).block.records[record as int].inode==old_target
        && change_before(c).block.records[record as int].file_type==1
        && crate::ns_rename_block::name(change_before(c),record as int)==name
        && match c {DirectoryChange::Remove(e)=>remove && e.record==record,
            DirectoryChange::Target(e)=>!remove && e.record==record && e.target==new_target && e.file_type==1}
}
#[verifier::rlimit(20)]
#[verifier::spinoff_prover]
fn encode_piece(raw:&[u8],inodes:u32,seed:u32,logical:u32,count:u32,large:bool,
    record:usize,remove:bool,old_target:u32,new_target:u32,name:&[u8])->(r:Option<(Vec<u8>,Ghost<DirectoryChange>)>)
    ensures match r {Some((after,c))=>change_valid(c@)
        && change_before(c@)==ns_dir_edit::view(raw@,inodes,seed,false,logical,count,large)
        && change_after(c@)==ns_dir_edit::view(after@,inodes,seed,false,logical,count,large)
        && action_matches(c@,record,remove,old_target,new_target,name@),None=>true},
{
    hide(vstd::slice::axiom_spec_len);
    hide(ns_dir_edit::view);hide(crate::ns_rename_block::view);
    let piece=match crate::directory_piece::parse(raw,inodes,seed,false,logical,count,large){Some(p)=>p,None=>{return None;}};
    assert(piece.view()==ns_dir_edit::view(raw@,inodes,seed,false,logical,count,large)) by {reveal(ns_dir_edit::view);reveal(crate::ns_rename_block::view);}
    let selected=match piece.get(record){Some(s)=>s,None=>{return None;}};
    let actual_name=match piece.name(record){Some(n)=>n,None=>{return None;}};
    if selected.inode!=old_target || selected.file_type!=1 || !bytes::equal(actual_name,name){return None;}
    if remove {
        let changed=match ns_dir_edit::remove(raw,inodes,seed,false,logical,count,large,record){Some(c)=>c,None=>{return None;}};
        let ghost c=ns_dir_edit::RemoveChange{before:ns_dir_edit::view(raw@,inodes,seed,false,logical,count,large),
            after:ns_dir_edit::view(changed@,inodes,seed,false,logical,count,large),record};
        assert(change_valid(DirectoryChange::Remove(c)));
        assert(action_matches(DirectoryChange::Remove(c),record,remove,old_target,new_target,name@));
        Some((changed,Ghost(DirectoryChange::Remove(c))))
    }else{
        let changed=match ns_record_target::replace(raw,inodes,seed,false,logical,count,large,record,new_target,1){Some(c)=>c,None=>{return None;}};
        let ghost c=ns_record_target::Change{before:ns_dir_edit::view(raw@,inodes,seed,false,logical,count,large),
            after:ns_dir_edit::view(changed@,inodes,seed,false,logical,count,large),record,target:new_target,file_type:1};
        assert(ns_record_target::valid(c)) by {reveal(ns_record_target::view);reveal(ns_dir_edit::view);}
        assert(change_valid(DirectoryChange::Target(c)));
        assert(action_matches(DirectoryChange::Target(c),record,remove,old_target,new_target,name@));
        Some((changed,Ghost(DirectoryChange::Target(c))))
    }
}
proof fn assemble_directory_binding(namespace:NamespaceView,directory:DirectoryView,logical:u32,block:u32,change:DirectoryChange)
    requires ea_namespace::valid(namespace),ea_directory::valid(directory),directory.volume==namespace.allocation,
        logical<directory.pieces.len(),logical<directory.physical.len(),block==directory.physical[logical as int],
        change_before(change)==directory.pieces[logical as int],!change_before(change).indexed,change_valid(change),
    ensures directory_bound(namespace,DirectoryEditView{owner:ea_directory::owner(directory),ordinal:directory.ordinal,logical,block,changes:Seq::empty().push(change)}),
{
    let e=DirectoryEditView{owner:ea_directory::owner(directory),ordinal:directory.ordinal,logical,block,changes:Seq::empty().push(change)};
    assert(directory_source_matches(namespace,e,directory));
    assert(exists|d:DirectoryView| #[trigger] directory_source_matches(namespace,e,d));
    reveal(directory_bound);
}
#[verifier::rlimit(25)]
#[verifier::spinoff_prover]
fn encode_directory(source:&Snapshot<'_>,before:&ea_namespace::Namespace<'_,'_>,owner:u32,logical:u32,
    record:usize,remove:bool,old_target:u32,new_target:u32,name:&[u8])->(r:Option<DirectoryEdit>)
    requires before.wf(),certified(before.view(),source.view()),
    ensures match r {Some(e)=>e.wf() && directory_bound(before.view(),e.view()) && e.view().owner==owner
        && e.view().logical==logical && e.view().changes.len()==1
        && action_matches(e.view().changes[0],record,remove,old_target,new_target,name@),None=>true},
{
    hide(vstd::slice::axiom_spec_len);hide(ns_dir_edit::view);hide(crate::ns_rename_block::view);hide(crate::crc::fold);
    let slot=match before.index().nodes().get(owner){Some(n)=>n,None=>{return None;}};
    let directory=match ea_directory::inspect(before.allocation(),slot.ordinal){Some(d)=>d,None=>{return None;}};
    let block=match directory.physical_block(logical){Some(b)=>b,None=>{return None;}};
    let raw=match source.block(block){Some(b)=>b.as_slice(),None=>{return None;}};
    proof {vstd::slice::axiom_spec_len(raw);}
    let index=before.allocation().integrity().reference_census().index();
    let node=match index.node(owner){Some(n)=>n,None=>{return None;}};
    proof {source_binding::namespace_inode_node_is_exact(before.view(),owner,node.view());}
    let nraw=node.raw();let (_,inodes,_,seed)=index.parameters();
    let indexed=bytes::read_le32(nraw,32).unwrap() & 0x1000 != 0;if indexed{return None;}
    let superblock=match source.capture_bytes(1024,1024){Some(s)=>s,None=>{return None;}};
    let large=match bytes::read_le32(&superblock,96){Some(flags)=>flags & 0x4000 != 0,None=>{return None;}};
    let generation=bytes::read_le32(nraw,100).unwrap();let metadata_seed=inode::inode_seed(seed,owner,generation);
    let count=directory.block_count();let piece=match directory.piece(logical){Some(p)=>p,None=>{return None;}};
    proof {source_binding::captured_piece_is_encoder_view(directory.view(),logical,raw@,inodes,metadata_seed,indexed,large);}
    let (changed,c)=match encode_piece(raw,inodes,metadata_seed,logical,count,large,record,remove,old_target,new_target,name){Some(c)=>c,None=>{return None;}};
    let ghost view=DirectoryEditView{owner,ordinal:slot.ordinal,logical,block,changes:Seq::empty().push(c@)};
    proof {assemble_directory_binding(before.view(),directory.view(),logical,block,c@);}
    assert(change_after(c@).block.raw==changed@) by {reveal(ns_dir_edit::view);reveal(crate::ns_rename_block::view);}
    Some(DirectoryEdit{block,inodes,seed:metadata_seed,logical,count,large,before:copy(raw),after:changed,checked:Ghost(view)})
}
#[verifier::rlimit(20)]
#[verifier::spinoff_prover]
fn extend_directory(e:DirectoryEdit,before:Ghost<NamespaceView>,record:usize,remove:bool,old_target:u32,new_target:u32,name:&[u8])
    ->(r:Option<DirectoryEdit>)
    requires e.wf(),directory_bound(before@,e.view()),e.view().changes.len()==1,
    ensures match r {Some(r)=>r.wf() && directory_bound(before@,r.view()) && r.view().owner==e.view().owner
        && r.view().changes==e.view().changes.push(r.view().changes[1]) && r.view().changes.len()==2
        && action_matches(r.view().changes[1],record,remove,old_target,new_target,name@),None=>true},
{
    let ghost prior=e.view();
    let (changed,c)=match encode_piece(&e.after,e.inodes,e.seed,e.logical,e.count,e.large,record,remove,old_target,new_target,name){Some(c)=>c,None=>{return None;}};
    let ghost view=DirectoryEditView{changes:prior.changes.push(c@),..prior};
    proof {
        reveal(directory_bound);
        let directory=choose|d:DirectoryView| #[trigger] directory_source_matches(before@,prior,d);
        assert(directory_source_matches(before@,view,directory));
        assert(exists|d:DirectoryView| #[trigger] directory_source_matches(before@,view,d));
    }
    assert(change_after(c@).block.raw==changed@) by {reveal(ns_dir_edit::view);reveal(crate::ns_rename_block::view);}
    Some(DirectoryEdit{block:e.block,inodes:e.inodes,seed:e.seed,logical:e.logical,count:e.count,large:e.large,before:e.before,after:changed,checked:Ghost(view)})
}

proof fn inode_is_requested(q:UpdateView,e:&InodeEdit)
    requires e.wf(),inode_bound(q.before,e.view()),e.view().change.seconds==q.seconds,e.view().change.nanos==q.nanos,
        if e.number==q.target {!e.mtime && e.delta==0 && e.view().extra.len()==0}
        else if e.number==q.displaced {!e.mtime && e.delta==if q.operation==Operation::Replace {-1int}else{0int} && e.view().extra.len()==0}
        else {e.mtime && e.delta==0 && (e.number==q.source_directory || e.number==q.destination_directory)
            && e.view().extra.len()==if q.source_directory==q.destination_directory {1int}else{0int}},
    ensures requested_inode(q,e.view()),
{reveal(InodeEdit::wf);reveal(requested_inode);}
proof fn directory_is_requested(q:UpdateView,e:&DirectoryEdit)
    requires e.wf(),directory_bound(q.before,e.view()),
        forall|i:int|0<=i<e.view().changes.len() ==> requested_change(q,e.view().owner,e.view().changes[i]),
    ensures requested_directory(q,e.view()),
{reveal(requested_directory);}

#[verifier::rlimit(20)]
#[verifier::spinoff_prover]
fn build_inode_edits(before:&ea_namespace::Namespace<'_,'_>,operation:Operation,source_directory:u32,destination_directory:u32,
    target:u32,displaced:u32,seconds:i64,nanos:u32,q:Ghost<UpdateView>)->(r:Result<Vec<InodeEdit>,Error>)
    requires before.wf(),q@.before==before.view(),q@.operation==operation,q@.source_directory==source_directory,
        q@.destination_directory==destination_directory,q@.target==target,q@.displaced==displaced,
        q@.seconds==seconds,q@.nanos==nanos,target!=displaced,
        target!=source_directory,target!=destination_directory,displaced!=source_directory,displaced!=destination_directory,
    ensures match r {Ok(edits)=>edits.len()<=4
        && (forall|i:int|0<=i<edits.len() ==> edits@[i].wf() && requested_inode(q@,edits@[i].view())),Err(_)=>true},
{
    let mut edits=Vec::new();
    let target_edit=match encode_inode(before,target,false,seconds,nanos,0){Some(e)=>e,None=>{return Err(Error::Rejected);}};
    proof {inode_is_requested(q@,&target_edit);}
    edits=push_inode(edits,target_edit,q);
    let delta=if matches!(operation,Operation::Replace){-1i8}else{0i8};
    let displaced_edit=match encode_inode(before,displaced,false,seconds,nanos,delta){Some(e)=>e,None=>{return Err(Error::Rejected);}};
    proof {inode_is_requested(q@,&displaced_edit);}
    edits=push_inode(edits,displaced_edit,q);
    let parent=match encode_inode(before,source_directory,true,seconds,nanos,0){Some(e)=>e,None=>{return Err(Error::Rejected);}};
    let parent=if source_directory==destination_directory {
        match second_parent_change(parent,seconds,nanos,Ghost(before.view())){Some(e)=>e,None=>{return Err(Error::Rejected);}}
    }else{parent};
    proof {inode_is_requested(q@,&parent);}
    edits=push_inode(edits,parent,q);
    if source_directory!=destination_directory {
        let parent=match encode_inode(before,destination_directory,true,seconds,nanos,0){Some(e)=>e,None=>{return Err(Error::Rejected);}};
        proof {inode_is_requested(q@,&parent);}
        edits=push_inode(edits,parent,q);
    }
    Ok(edits)
}

#[verifier::rlimit(25)]
#[verifier::spinoff_prover]
fn build_directory_edits(source:&Snapshot<'_>,before:&ea_namespace::Namespace<'_,'_>,operation:Operation,
    source_directory:u32,old_name:&[u8],destination_directory:u32,new_name:&[u8],target:u32,displaced:u32,
    logical:u32,record:usize,destination_logical:u32,destination_record:usize,q:Ghost<UpdateView>)
    ->(r:Result<Vec<DirectoryEdit>,Error>)
    requires before.wf(),certified(before.view(),source.view()),q@.before==before.view(),q@.operation==operation,
        q@.source_directory==source_directory,q@.destination_directory==destination_directory,q@.target==target,q@.displaced==displaced,
        q@.old_name==old_name@,q@.new_name==new_name@,
    ensures match r {Ok(edits)=>edits.len()<=2
        && (forall|i:int|0<=i<edits.len() ==> edits@[i].wf() && requested_directory(q@,edits@[i].view())),Err(_)=>true},
{
    let remove=matches!(operation,Operation::Replace);
    let source_edit=match encode_directory(source,before,source_directory,logical,record,remove,target,displaced,old_name){Some(e)=>e,None=>{return Err(Error::Rejected);}};
    assert(requested_change(q@,source_directory,source_edit.view().changes[0]));
    proof {directory_is_requested(q@,&source_edit);}
    let mut edits=Vec::new();
    if source_directory==destination_directory && logical==destination_logical {
        let ghost prior=source_edit.view();
        let combined=match extend_directory(source_edit,Ghost(before.view()),destination_record,false,displaced,target,new_name){Some(e)=>e,None=>{return Err(Error::Rejected);}};
        assert(requested_change(q@,combined.view().owner,combined.view().changes[1]));
        assert forall|i:int|0<=i<combined.view().changes.len() implies requested_change(q@,combined.view().owner,combined.view().changes[i]) by {
            if i==0 {reveal(requested_directory);assert(combined.view().changes[0]==prior.changes[0]);}
            else {assert(i==1);}
        }
        proof {directory_is_requested(q@,&combined);}
        edits=push_directory(edits,combined,q);
    }else{
        let destination_edit=match encode_directory(source,before,destination_directory,destination_logical,destination_record,false,displaced,target,new_name){Some(e)=>e,None=>{return Err(Error::Rejected);}};
        if source_edit.block==destination_edit.block{return Err(Error::Rejected);}
        assert(requested_change(q@,destination_directory,destination_edit.view().changes[0]));
        proof {directory_is_requested(q@,&destination_edit);}
        edits=push_directory(edits,source_edit,q);
        edits=push_directory(edits,destination_edit,q);
    }
    Ok(edits)
}
fn coverage_has_inode_number(inodes:&[InodeEdit],number:u32)->(r:bool)
    requires forall|i:int|0<=i<inodes.len() ==> inodes@[i].wf(),
    ensures r ==> (exists|i:int|0<=i<inodes.len() && (#[trigger] inode_views(inodes@)[i]).number==number),
{
    let mut i=0usize;
    while i<inodes.len()
        invariant i<=inodes.len(),forall|j:int|0<=j<inodes.len() ==> inodes@[j].wf(),
        decreases inodes.len()-i,
    {
        if inodes[i].number==number {
            assert(inodes@[i as int].wf());
            assert(inode_views(inodes@)[i as int].number==number);
            assert(exists|j:int|0<=j<inodes.len() && (#[trigger] inode_views(inodes@)[j]).number==number);
            return true;
        }
        i+=1;
    }
    false
}
fn check_coverage(inodes:&[InodeEdit],directories:&[DirectoryEdit],q:Ghost<UpdateView>,
    target:u32,displaced:u32,source_directory:u32,destination_directory:u32)->(r:bool)
    requires forall|j:int|0<=j<inodes.len() ==> inodes@[j].wf(),
        q@.inode_edits==inode_views(inodes@),q@.directory_edits==directory_views(directories@),
        q@.target==target,q@.displaced==displaced,q@.source_directory==source_directory,q@.destination_directory==destination_directory,
    ensures r ==> covered(q@),
{
    if target==displaced{return inodes.len()==0 && directories.len()==0;}
    if inodes.len()<3 || inodes.len()>4 || directories.len()<1 || directories.len()>2{return false;}
    if !coverage_has_inode_number(inodes,target) || !coverage_has_inode_number(inodes,displaced)
        || !coverage_has_inode_number(inodes,source_directory) || !coverage_has_inode_number(inodes,destination_directory){return false;}
    let mut i=0usize;
    while i<inodes.len()
        invariant i<=inodes.len()<=4,3<=inodes.len(),
            forall|j:int|0<=j<inodes.len() ==> inodes@[j].wf(),
            forall|a:int,b:int|0<=a<i && a<b<inodes.len() ==> inodes@[a].number!=inodes@[b].number,
        decreases inodes.len()-i,
    {
        let mut j=i+1;
        while j<inodes.len()
            invariant i<inodes.len()<=4,i+1<=j<=inodes.len(),
                forall|a:int,b:int|0<=a<i && a<b<inodes.len() ==> inodes@[a].number!=inodes@[b].number,
                forall|b:int|i<b<j ==> inodes@[i as int].number!=inodes@[b].number,
            decreases inodes.len()-j,
        {if inodes[i].number==inodes[j].number{return false;}j+=1;}
        i+=1;
    }
    assert forall|a:int,b:int|0<=a<b<q@.inode_edits.len() implies q@.inode_edits[a].number!=q@.inode_edits[b].number by {
        assert(inodes@[a].wf() && inodes@[b].wf());
        assert(q@.inode_edits[a].number==inodes@[a].number && q@.inode_edits[b].number==inodes@[b].number);
    }
    true
}
struct Plan {inodes:Vec<InodeEdit>,directories:Vec<DirectoryEdit>,same_inode:bool,checked:Ghost<Seq<UpdateView>>}
impl Plan {
    closed spec fn view(&self)->UpdateView {self.checked@[0]}
    closed spec fn wf(&self)->bool {
        self.checked@.len()==1 && self.same_inode==(self.view().target==self.view().displaced) && planned(self.view()) && self.inodes.len()<=4 && self.directories.len()<=2
            && self.view().inode_edits==inode_views(self.inodes@) && self.view().directory_edits==directory_views(self.directories@)
            && (forall|i:int|0<=i<self.inodes.len() ==> self.inodes@[i].wf())
            && (forall|i:int|0<=i<self.directories.len() ==> self.directories@[i].wf())
    }
}
#[verifier::opaque]
spec fn attach_edits(start:UpdateView,inodes:Seq<InodeEditView>,directories:Seq<DirectoryEditView>)->UpdateView {
    UpdateView{inode_edits:inodes,directory_edits:directories,..start}
}
#[verifier::opaque]
spec fn edits_attached(start:UpdateView,end:UpdateView)->bool {
    end==(UpdateView{inode_edits:end.inode_edits,directory_edits:end.directory_edits,..start})
}
proof fn attached_request_fields(start:UpdateView,end:UpdateView)
    requires edits_attached(start,end),
    ensures end.source==start.source,end.before==start.before,end.operation==start.operation,
        end.source_directory==start.source_directory,end.destination_directory==start.destination_directory,
        end.old_name==start.old_name,end.new_name==start.new_name,end.target==start.target,end.generation==start.generation,
        end.displaced==start.displaced,end.displaced_generation==start.displaced_generation,
        end.source_parent_generation==start.source_parent_generation,end.destination_parent_generation==start.destination_parent_generation,
        end.seconds==start.seconds,end.nanos==start.nanos,
{reveal(edits_attached);}
proof fn discovered_operand_ids(q:UpdateView)
    requires discovered(q),
    ensures q.target!=q.source_directory,q.target!=q.destination_directory,
        q.displaced!=q.source_directory,q.displaced!=q.destination_directory,
{reveal(discovered);}
proof fn discovered_survives_attachment(start:UpdateView,end:UpdateView)
    requires discovered(start),edits_attached(start,end),
    ensures discovered(end),
{reveal(edits_attached);reveal(discovered);}
#[verifier::rlimit(20)]
#[verifier::spinoff_prover]
fn encode_plan(source:&Snapshot<'_>,before:&ea_namespace::Namespace<'_,'_>,operation:Operation,
    source_directory:u32,old_name:&[u8],destination_directory:u32,new_name:&[u8],target:u32,displaced:u32,
    logical:u32,record:usize,destination_logical:u32,destination_record:usize,seconds:i64,nanos:u32,q:Ghost<UpdateView>)
    ->(r:Result<Plan,Error>)
    requires before.wf(),certified(before.view(),source.view()),discovered(q@),q@.before==before.view(),q@.operation==operation,
        q@.source_directory==source_directory,q@.destination_directory==destination_directory,q@.target==target,q@.displaced==displaced,
        q@.old_name==old_name@,q@.new_name==new_name@,q@.seconds==seconds,q@.nanos==nanos,
    ensures match r {Ok(plan)=>plan.wf() && edits_attached(q@,plan.view()),Err(_)=>true},
{
    proof {discovered_operand_ids(q@);}
    let (inodes,directories)=if target==displaced {(Vec::new(),Vec::new())}else{
        let inodes=match build_inode_edits(before,operation,source_directory,destination_directory,target,displaced,seconds,nanos,q){Ok(e)=>e,Err(e)=>{return Err(e);}};
        let directories=match build_directory_edits(source,before,operation,source_directory,old_name,destination_directory,new_name,target,displaced,logical,record,destination_logical,destination_record,q){Ok(e)=>e,Err(e)=>{return Err(e);}};
        (inodes,directories)
    };
    let ghost view=attach_edits(q@,inode_views(inodes@),directory_views(directories@));
    proof {reveal(attach_edits);reveal(edits_attached);}
    let inode_slice=inodes.as_slice();let directory_slice=directories.as_slice();
    if !check_coverage(inode_slice,directory_slice,Ghost(view),target,displaced,source_directory,destination_directory){return Err(Error::Rejected);}
    proof {discovered_survives_attachment(q@,view);}
    assert(planned(view)) by {reveal(planned);reveal(requested_inode);reveal(requested_directory);}
    let ghost sealed=Seq::empty().push(view);
    Ok(Plan{inodes,directories,same_inode:target==displaced,checked:Ghost(sealed)})
}
#[verifier::rlimit(15)]
#[verifier::spinoff_prover]
fn admit_projection(before:&ea_namespace::Namespace<'_,'_>,result:&[u8],operation:Operation,
    source_directory:u32,old_name:&[u8],destination_directory:u32,new_name:&[u8],
    target:u32,generation:u32,displaced:u32,displaced_generation:u32,source_parent_generation:u32,destination_parent_generation:u32,
    inode_budget:u32,node_budget:u64,byte_budget:u64)->(r:Option<Ghost<NamespaceView>>)
    requires before.wf(),
    ensures before.wf(),match r {Some(a)=>certified(a@,result@)
        && relation::relation(before.view().index.entries,a@.index.entries,operation,
            source_directory,old_name@,destination_directory,new_name@,target,generation,displaced,displaced_generation,
            source_parent_generation,destination_parent_generation),None=>true},
{
    let after_source=Snapshot::from_bytes(result);
    let after=match ea_namespace::inspect(&after_source,inode_budget,node_budget,byte_budget){Some(a)=>a,None=>{return None;}};
    if !relation::check(before.index(),after.index(),operation,source_directory,old_name,destination_directory,new_name,
        target,generation,displaced,displaced_generation,source_parent_generation,destination_parent_generation){return None;}
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
        attach_result(start,result,after,patches).displaced==start.displaced,
        attach_result(start,result,after,patches).displaced_generation==start.displaced_generation,
        attach_result(start,result,after,patches).source_parent_generation==start.source_parent_generation,
        attach_result(start,result,after,patches).destination_parent_generation==start.destination_parent_generation,
        attach_result(start,result,after,patches).seconds==start.seconds,
        attach_result(start,result,after,patches).nanos==start.nanos,
{
    reveal(attach_result);
    reveal(planned);reveal(discovered);reveal(requested_inode);reveal(requested_directory);
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
            plan.view().target,plan.view().generation,plan.view().displaced,plan.view().displaced_generation,plan.view().source_parent_generation,
            plan.view().destination_parent_generation),
    ensures r ==> valid(attach_result(plan.view(),result@,after@,patches.view())),
{
    hide(vstd::slice::axiom_spec_len);
    let ghost start=plan.view();
    let ghost view=attach_result(start,result@,after@,patches.view());
    proof {result_attachment_fields(start,result@,after@,patches.view());}
    let inode_slice=plan.inodes.as_slice();let directory_slice=plan.directories.as_slice();
    proof {vstd::slice::axiom_spec_len(inode_slice);vstd::slice::axiom_spec_len(directory_slice);}
    if plan.same_inode && patches.len()!=0{return false;}
    if !check_encoded(source,result,inode_slice,directory_slice,Ghost(view)){return false;}
    proof {
        if view.target==view.displaced {
            reveal(planned); assert(covered(view)); assert(view.inode_edits.len()==0 && view.directory_edits.len()==0);
            assert(view.result =~= view.source);
        }
    }
    proof {reveal(valid);}
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
        assert(plan.inodes.len()<=4 && plan.directories.len()<=2
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
    target:u32,generation:u32,displaced:u32,displaced_generation:u32,source_parent_generation:u32,destination_parent_generation:u32,
    seconds:int,nanos:nat)->bool {
    discovered(UpdateView{source,result:source,before,after:before,operation,source_directory,destination_directory,
        old_name,new_name,target,generation,displaced,displaced_generation,source_parent_generation,destination_parent_generation,
        seconds,nanos,patches:Seq::empty(),inode_edits:Seq::empty(),directory_edits:Seq::empty()})
}
#[verifier::rlimit(30)]
#[verifier::spinoff_prover]
fn prepare_discovered(source:&Snapshot<'_>,before:&ea_namespace::Namespace<'_,'_>,operation:Operation,
    source_directory:u32,old_name:&[u8],destination_directory:u32,new_name:&[u8],
    target:u32,generation:u32,displaced:u32,displaced_generation:u32,logical:u32,record:usize,destination_logical:u32,destination_record:usize,
    source_parent_generation:u32,destination_parent_generation:u32,seconds:i64,nanos:u32,
    inode_budget:u32,node_budget:u64,byte_budget:u64)->(r:Result<Update,Error>)
    requires before.wf(),
        before.view().index.volume==before.view().allocation,before.view().tree.index==before.view().index,
        before.view().index.nodes.volume==before.view().allocation,
        discovered_inputs(source.view(),before.view(),operation,source_directory,old_name@,destination_directory,new_name@,
            target,generation,displaced,displaced_generation,source_parent_generation,destination_parent_generation,seconds as int,nanos as nat),
    ensures return_summary(r,ReturnRequest{source:source.view(),operation,source_directory,destination_directory,old_name:old_name@,new_name:new_name@,seconds:seconds as int,nanos:nanos as nat}),
{
    hide(Update::view);hide(Update::wf);hide(vstd::slice::axiom_spec_len);hide(Plan::view);hide(Plan::wf);hide(certified);
    let ghost returning=ReturnRequest{source:source.view(),operation,source_directory,destination_directory,old_name:old_name@,new_name:new_name@,seconds:seconds as int,nanos:nanos as nat};
    proof {errors_satisfy_return_summary(returning);}
    let ghost request=UpdateView{source:source.view(),result:source.view(),before:before.view(),after:before.view(),operation,
        source_directory,destination_directory,old_name:old_name@,new_name:new_name@,target,generation,displaced,displaced_generation,
        source_parent_generation,destination_parent_generation,seconds:seconds as int,nanos:nanos as nat,
        patches:Seq::empty(),inode_edits:Seq::empty(),directory_edits:Seq::empty()};
    assert(discovered(request) && certified(before.view(),source.view())) by {reveal(discovered_inputs);reveal(discovered);}
    let plan=match encode_plan(source,before,operation,source_directory,old_name,destination_directory,new_name,
        target,displaced,logical,record,destination_logical,destination_record,seconds,nanos,Ghost(request)){Ok(p)=>p,Err(e)=>{return Err(e);}};
    proof {attached_request_fields(request,plan.view());}
    let (result,patches)=match materialize_plan(source,&plan){Ok(p)=>p,Err(e)=>{return Err(e);}};
    let result_slice=result.as_slice();proof {vstd::slice::axiom_spec_len(result_slice);}
    let after=match admit_projection(before,result_slice,operation,source_directory,old_name,destination_directory,new_name,
        target,generation,displaced,displaced_generation,source_parent_generation,destination_parent_generation,
        inode_budget,node_budget,byte_budget){Some(a)=>a,None=>{return Err(Error::Rejected);}};
    if !check_candidate(source,&plan,&patches,result_slice,after){return Err(Error::Rejected);}
    finish_return(plan,patches,result,after,Ghost(returning))
}
#[verifier::rlimit(30)]
#[verifier::spinoff_prover]
fn prepare(source:&Snapshot<'_>,operation:Operation,source_directory:u32,old_name:&[u8],destination_directory:u32,new_name:&[u8],
    seconds:i64,nanos:u32,inode_budget:u32,node_budget:u64,byte_budget:u64)->(r:Result<Update,Error>)
    ensures return_summary(r,ReturnRequest{source:source.view(),operation,source_directory,destination_directory,old_name:old_name@,new_name:new_name@,seconds:seconds as int,nanos:nanos as nat}),
{
    hide(Update::view);hide(Update::wf);hide(vstd::slice::axiom_spec_len);
    hide(crate::ea_directory_index::source_has_name);hide(crate::namespace_model::has_name);
    let ghost returning=ReturnRequest{source:source.view(),operation,source_directory,destination_directory,old_name:old_name@,new_name:new_name@,seconds:seconds as int,nanos:nanos as nat};
    proof {errors_satisfy_return_summary(returning);}
    if source.partition_bytes()<8192 || source.partition_bytes()>MAX_IMAGE_BYTES as u64{return Err(Error::Invalid);}
    let before=match ea_namespace::inspect(source,inode_budget,node_budget,byte_budget){Some(b)=>b,None=>{return Err(Error::Invalid);}};
    let superblock=match source.capture_bytes(1024,1024){Some(b)=>b,None=>{return Err(Error::Invalid);}};
    match feature_policy::is_readonly(&superblock){Some(true)=>{return Err(Error::ReadOnly);},Some(false)=>{},None=>{return Err(Error::Invalid);}}
    if !proper_name(old_name) || !proper_name(new_name){return Err(Error::Invalid);}
    let entry=match before.lookup(source_directory,old_name){Some(e)=>e,None=>{return Err(Error::NotFound);}};
    let (_,target,generation,file_type)=entry.identity();let (logical,record)=entry.location();
    let destination=match before.lookup(destination_directory,new_name){Some(e)=>e,None=>{return Err(Error::NotFound);}};
    let (_,displaced,displaced_generation,destination_type)=destination.identity();let (destination_logical,destination_record)=destination.location();
    if file_type!=1 || destination_type!=1{return Err(Error::Rejected);}
    if target==source_directory || target==destination_directory || target==2 || displaced==source_directory || displaced==destination_directory || displaced==2{return Err(Error::Rejected);}
    let nodes=before.index().nodes();
    let source_slot=match nodes.get(source_directory){Some(n)=>n,None=>{return Err(Error::Rejected);}};
    let destination_slot=match nodes.get(destination_directory){Some(n)=>n,None=>{return Err(Error::Rejected);}};
    let displaced_slot=match nodes.get(displaced){Some(n)=>n,None=>{return Err(Error::Rejected);}};
    if source_slot.mode & 0xf000!=0x4000 || destination_slot.mode & 0xf000!=0x4000{return Err(Error::Rejected);}
    if target!=displaced && matches!(operation,Operation::Replace) && displaced_slot.links<=1{return Err(Error::Rejected);}
    assert(discovered_inputs(source.view(),before.view(),operation,source_directory,old_name@,destination_directory,new_name@,
        target,generation,displaced,displaced_generation,source_slot.generation,destination_slot.generation,seconds as int,nanos as nat)) by {reveal(discovered_inputs);reveal(discovered);}
    proof {source_binding::namespace_components_share_one_allocation(&before);}
    prepare_discovered(source,&before,operation,source_directory,old_name,destination_directory,new_name,target,generation,
        displaced,displaced_generation,logical,record,destination_logical,destination_record,source_slot.generation,destination_slot.generation,
        seconds,nanos,inode_budget,node_budget,byte_budget)
}

#[verifier::rlimit(10)]
#[verifier::spinoff_prover]
pub fn prepare_replace(source:&Snapshot<'_>,old_dir:u32,old_name:&[u8],new_dir:u32,new_name:&[u8],
    seconds:i64,nanos:u32,inode_budget:u32,node_budget:u64,byte_budget:u64)->(r:Result<Update,Error>)
    ensures match r {Ok(u)=>u.wf() && valid(u.view()) && u.view().source==source.view()
        && u.view().operation==Operation::Replace && u.view().source_directory==old_dir && u.view().destination_directory==new_dir
        && u.view().old_name==old_name@ && u.view().new_name==new_name@ && u.view().seconds==seconds && u.view().nanos==nanos,Err(_)=>true},
{
    hide(Update::view);hide(Update::wf);
    let result=prepare(source,Operation::Replace,old_dir,old_name,new_dir,new_name,seconds,nanos,inode_budget,node_budget,byte_budget);
    proof {return_summary_has_exact_fields(result,ReturnRequest{source:source.view(),operation:Operation::Replace,source_directory:old_dir,destination_directory:new_dir,old_name:old_name@,new_name:new_name@,seconds:seconds as int,nanos:nanos as nat});}
    result
}

#[verifier::rlimit(10)]
#[verifier::spinoff_prover]
pub fn prepare_exchange(source:&Snapshot<'_>,old_dir:u32,old_name:&[u8],new_dir:u32,new_name:&[u8],
    seconds:i64,nanos:u32,inode_budget:u32,node_budget:u64,byte_budget:u64)->(r:Result<Update,Error>)
    ensures match r {Ok(u)=>u.wf() && valid(u.view()) && u.view().source==source.view()
        && u.view().operation==Operation::Exchange && u.view().source_directory==old_dir && u.view().destination_directory==new_dir
        && u.view().old_name==old_name@ && u.view().new_name==new_name@ && u.view().seconds==seconds && u.view().nanos==nanos,Err(_)=>true},
{
    hide(Update::view);hide(Update::wf);
    let result=prepare(source,Operation::Exchange,old_dir,old_name,new_dir,new_name,seconds,nanos,inode_budget,node_budget,byte_budget);
    proof {return_summary_has_exact_fields(result,ReturnRequest{source:source.view(),operation:Operation::Exchange,source_directory:old_dir,destination_directory:new_dir,old_name:old_name@,new_name:new_name@,seconds:seconds as int,nanos:nanos as nat});}
    result
}

pub proof fn candidate_images_are_certified_and_have_equal_length(v:UpdateView)
    requires valid(v),ensures certified(v.before,v.source),certified(v.after,v.result),v.result.len()==v.source.len(),8192<=v.source.len()<=MAX_IMAGE_BYTES,
{reveal(valid);reveal(planned);reveal(discovered);}
pub proof fn prepared_edits_have_exact_operation(v:UpdateView)
    requires valid(v),ensures exact_operation(v),
{reveal(valid);}
pub proof fn same_inode_operations_preserve_every_source_byte(v:UpdateView)
    requires valid(v),v.target==v.displaced,
    ensures v.source==v.result,v.patches.len()==0,v.inode_edits.len()==0,v.directory_edits.len()==0,
{reveal(valid);reveal(planned);reveal(discovered);}
pub proof fn prepared_edits_preserve_every_unrelated_source_byte(v:UpdateView,i:int)
    requires valid(v),0<=i<v.source.len(),!editable(i,v.inode_edits,v.directory_edits),
    ensures v.result[i]==v.source[i],
{reveal(valid);}
pub proof fn prepared_edits_never_authorize_READONLY_source_images(v:UpdateView)
    requires valid(v),ensures !feature_policy::readonly(v.source.subrange(1024,2048)),
{reveal(valid);reveal(planned);reveal(discovered);}
pub proof fn prepared_patches_target_only_checked_directory_and_inode_table_blocks(v:UpdateView)
    requires valid(v),ensures patch_scope(v.patches,v.inode_edits,v.directory_edits),
{reveal(valid);}
proof fn inode_bound_supplies_codec_witness(before:NamespaceView,e:InodeEditView)
    requires inode_bound(before,e),
    ensures ns_inode_links::valid(e.change),e.extra.len()<=1,
        e.extra.len()==1 ==> ns_inode_links::valid(e.extra[0]) && e.extra[0].before==e.change.after
            && e.extra[0].delta==0 && e.extra[0].touch_mtime
            && e.extra[0].seconds==e.change.seconds && e.extra[0].nanos==e.change.nanos,
{reveal(inode_bound);reveal(source_binding::inode_bound);}
pub proof fn prepared_inode_edits_have_exact_links_times_and_versions(v:UpdateView,j:int)
    requires valid(v),0<=j<v.inode_edits.len(),
    ensures requested_inode(v,v.inode_edits[j]),
        bytes::le16(inode_after(v.inode_edits[j]),26) as int==bytes::le16(v.inode_edits[j].change.before,26) as int+v.inode_edits[j].change.delta,
        crate::inode_time_fields::seconds(inode_after(v.inode_edits[j]),crate::inode_time_fields::Field::Ctime)==v.seconds,
        crate::inode_time_fields::nanoseconds(inode_after(v.inode_edits[j]),crate::inode_time_fields::Field::Ctime)==v.nanos,
        crate::xattr_replace::version(inode_after(v.inode_edits[j]))==crate::xattr_replace::version(v.inode_edits[j].change.before)+1+v.inode_edits[j].extra.len(),
{
    reveal(valid);reveal(planned);reveal(requested_inode);
    let e=v.inode_edits[j];
    inode_bound_supplies_codec_witness(v.before,e);
    ns_inode_links::namespace_link_changes_have_the_exact_positive_linux_count(e.change);
    ns_inode_links::namespace_link_changes_publish_the_exact_requested_times(e.change);
    ns_inode_links::namespace_link_changes_increment_one_nonwrapping_ordinary_version(e.change);
    if e.extra.len()==1 {
        ns_inode_links::namespace_link_changes_have_the_exact_positive_linux_count(e.extra[0]);
        ns_inode_links::namespace_link_changes_publish_the_exact_requested_times(e.extra[0]);
        ns_inode_links::namespace_link_changes_increment_one_nonwrapping_ordinary_version(e.extra[0]);
    }
}

pub proof fn prepared_directory_edits_have_exact_source_and_requested_record_witnesses(v:UpdateView,j:int)
    requires valid(v),0<=j<v.directory_edits.len(),
    ensures requested_directory(v,v.directory_edits[j]),directory_bound(v.before,v.directory_edits[j]),
        1<=v.directory_edits[j].changes.len()<=2,
        exists|d:DirectoryView| #[trigger] directory_source_matches(v.before,v.directory_edits[j],d),
{reveal(valid);reveal(planned);reveal(requested_directory);reveal(directory_bound);}
pub proof fn prepared_inode_edits_preserve_extent_sector_and_EA_bytes(v:UpdateView,j:int,i:int)
    requires valid(v),0<=j<v.inode_edits.len(),0<=i<256,
        !ns_inode_links::mutable(v.inode_edits[j].change.touch_mtime,i),
    ensures v.result[v.inode_edits[j].position as int+i]==v.source[v.inode_edits[j].position as int+i],
{
    reveal(valid);reveal(planned);reveal(requested_inode);
    let e=v.inode_edits[j];let p=e.position as int;
    inode_bound_supplies_codec_witness(v.before,e);
    ns_inode_links::namespace_link_changes_preserve_identity_extents_and_ea_billing_bytes(e.change,i);
    if e.extra.len()==1 {
        assert(e.change.touch_mtime);
        ns_inode_links::namespace_link_changes_preserve_identity_extents_and_ea_billing_bytes(e.extra[0],i);
    }
    assert(e.change.before==v.source.subrange(p,p+256) && inode_after(e)==v.result.subrange(p,p+256));
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
