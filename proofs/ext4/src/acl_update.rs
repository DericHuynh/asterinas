// SPDX-License-Identifier: MPL-2.0

//! Source-bound access/default ACL transactions with atomic permission-mode
//! coupling. IDs, groups and scoped FOWNER/FSETID decisions are VFS inputs.
//! This host model establishes no authenticated caller, LSM or runtime lock.

use vstd::prelude::*;
use crate::{acl, acl_xattr, allocated_inode::{self, AllocatedInode, NodeView}, bytes, feature_policy,
    inode_mode, patch_set::PatchSet, transaction::ImageView, writer_admission::{self, CheckedWriter},
    xattr_inode::{self, AttributesView}, xattr_store::{self as store, ItemView}, xattr_transaction::{self as storage, StorageView}};

use crate::{disk_image, layout::JournalLayout, write_device::{self, Machine}, write_io::Images, write_media, write_recovery, writer_admission::AdmissionView};

verus! {

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Kind { Access, Default }
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Credentials { pub fsuid: u32, pub fowner: bool, pub fsetid: bool }
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Error { Permission, ReadOnly, InvalidAcl, NotDirectory, Storage(storage::Error) }
pub open spec fn number(kind: Kind) -> u8 { match kind { Kind::Access => 2u8, Kind::Default => 3u8 } }
fn namespace(kind: Kind) -> (r: u8) ensures r == number(kind) { match kind { Kind::Access => 2u8, Kind::Default => 3u8 } }
fn member(groups: &[u32], id: u32) -> (r: bool) ensures r == groups@.contains(id) {
    let mut i = 0usize;
    while i < groups.len() invariant i <= groups.len(), forall|j: int| 0 <= j < i ==> #[trigger] groups@[j] != id, decreases groups.len() - i,
    { if groups[i] == id { return true; } i += 1; }
    false
}
pub struct AuthorizationView { pub node: NodeView, pub credentials: Credentials, pub groups: Seq<u32>, pub in_group: bool,
    pub kind: Kind, pub attributes: AttributesView }
#[verifier::opaque]
pub open spec fn authorized(v: AuthorizationView) -> bool {
    allocated_inode::valid(v.node) && v.in_group == v.groups.contains(v.node.gid)
        && (v.credentials.fsuid == v.node.uid || v.credentials.fowner || v.kind == Kind::Default && v.node.mode & 0xf000 != 0x4000)
        && xattr_inode::valid(v.attributes) && v.attributes.index == v.node.volume.index && v.attributes.number == v.node.number
}
pub struct Authorization<'n, 'v, 'a> { node: &'n AllocatedInode<'v, 'a>, credentials: Credentials, kind: Kind, in_group: bool, certificate: Ghost<AuthorizationView> }
impl<'n, 'v, 'a> Authorization<'n, 'v, 'a> {
    pub closed spec fn view(&self) -> AuthorizationView { self.certificate@ }
    pub closed spec fn wf(&self) -> bool { authorized(self.view()) && self.node.view() == self.view().node && self.credentials == self.view().credentials
        && self.kind == self.view().kind && self.in_group == self.view().in_group }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    fn release(self) -> (r: (&'n AllocatedInode<'v, 'a>, Credentials, Kind, bool, Ghost<AuthorizationView>))
        ensures self.wf(), authorized(r.4@), r.4@ == self.view(), r.0.wf(), r.0.view() == self.view().node,
            r.1 == self.view().credentials, r.2 == self.view().kind, r.3 == self.view().in_group,
    { proof { use_type_invariant(&self); reveal(authorized); } (self.node, self.credentials, self.kind, self.in_group, self.certificate) }
}
pub fn authorize<'n, 'v, 'a>(node: &'n AllocatedInode<'v, 'a>, credentials: &Credentials, groups: &[u32], kind: Kind) -> (r: Option<Authorization<'n, 'v, 'a>>)
    ensures node.wf(), match r { Some(grant) => grant.wf() && authorized(grant.view()) && grant.view().node == node.view()
        && grant.view().credentials == *credentials && grant.view().groups == groups@ && grant.view().kind == kind, None => true },
{
    let info = node.info(); let in_group = member(groups, info.gid);
    if credentials.fsuid != info.uid && !credentials.fowner && !(matches!(kind, Kind::Default) && info.mode & 0xf000 != 0x4000) { return None; }
    let attributes = match xattr_inode::inspect(node.volume().index(), node.number()) { Some(attributes) => attributes, None => { return None; } };
    let copy = Credentials { fsuid: credentials.fsuid, fowner: credentials.fowner, fsetid: credentials.fsetid };
    let ghost view = AuthorizationView { node: node.view(), credentials: copy, groups: groups@, in_group, kind, attributes: attributes.view() };
    assert(allocated_inode::valid(view.node));
    assert(view.in_group == view.groups.contains(view.node.gid));
    assert(view.credentials.fsuid == view.node.uid || view.credentials.fowner || view.kind == Kind::Default && view.node.mode & 0xf000 != 0x4000);
    assert(xattr_inode::valid(view.attributes) && view.attributes.index == view.node.volume.index && view.attributes.number == view.node.number);
    assert(authorized(view)) by { reveal(authorized); }
    Some(Authorization { node, credentials: copy, kind, in_group, certificate: Ghost(view) })
}

pub open spec fn mode_for(old: u16, bits: u16, keep_gid: bool) -> u16 {
    let mode = (old & !0o777u16) | bits; if keep_gid { mode } else { mode & !0o2000u16 }
}
fn mode_after(old: u16, bits: u16, keep_gid: bool) -> (r: u16)
    requires bits <= 0o777, ensures r == mode_for(old, bits, keep_gid),
{ let mode = (old & !0o777u16) | bits; if keep_gid { mode } else { mode & !0o2000u16 } }

pub struct Plan { pub acl: Option<acl::AclView>, pub retained: bool, pub desired: Seq<ItemView>, pub mode: u16 }
pub open spec fn value(plan: Plan) -> Option<Seq<u8>> { if plan.retained { Some(plan.acl.unwrap().raw) } else { None } }
#[verifier::opaque]
pub open spec fn planned(a: AuthorizationView, input: Seq<u8>, p: Plan) -> bool {
    let before = store::source_items(a.attributes); let ns = number(a.kind); let name = Seq::<u8>::empty();
    &&& authorized(a) && store::valid(before) && store::valid(p.desired)
    &&& a.credentials.fsuid == a.node.uid || a.credentials.fowner
    &&& match p.acl {
        None => acl_xattr::removing(input) && !p.retained && p.mode == a.node.mode,
        Some(acl) => acl_xattr::represents(input, acl) && acl::permission_mode(acl.entries) <= 0o777
            && if a.kind == Kind::Access { p.retained == acl_xattr::non_equivalent(acl)
                && p.mode == mode_for(a.node.mode, acl::permission_mode(acl.entries), a.in_group || a.credentials.fsetid) }
            else { a.node.mode & 0xf000 == 0x4000 && p.retained && p.mode == a.node.mode },
    }
    &&& match value(p) {
        Some(raw) => store::set_error(before, ns, name, raw, 0).is_none() && p.desired == store::updated(before, ns, name, raw),
        None => p.desired == store::deleted(before, ns, name),
    }
}
pub open spec fn unchanged(a: AuthorizationView, input: Seq<u8>) -> bool {
    authorized(a) && (a.kind == Kind::Default && a.node.mode & 0xf000 != 0x4000 && acl_xattr::removing(input)
        || exists|p: Plan| planned(a, input, p) && p.mode == a.node.mode && store::same_contents(p.desired, store::source_items(a.attributes)))
}
pub struct UpdateView { pub authority: AuthorizationView, pub input: Seq<u8>, pub plan: Plan, pub storage: StorageView }
#[verifier::opaque]
pub open spec fn valid(v: UpdateView) -> bool {
    planned(v.authority, v.input, v.plan) && storage::valid(v.storage)
        && !feature_policy::readonly(v.authority.node.volume.index.source.subrange(1024, 2048))
        && v.storage.node == v.authority.node && v.storage.desired == v.plan.desired && v.storage.mode.mode == v.plan.mode
}
pub struct Candidate<'n, 'v, 'a> { node: &'n AllocatedInode<'v, 'a>, patches: PatchSet, certificate: Ghost<UpdateView> }
impl<'n, 'v, 'a> Candidate<'n, 'v, 'a> {
    pub closed spec fn view(&self) -> UpdateView { self.certificate@ }
    pub closed spec fn node_view(&self) -> NodeView { self.node.view() }
    pub closed spec fn images(&self) -> Seq<ImageView> { self.patches.view() }
    pub open spec fn wf(&self) -> bool { valid(self.view()) && self.node_view() == self.view().authority.node && self.images() == self.view().storage.patches }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn patches(&self) -> (r: &PatchSet) ensures self.wf(), r.wf(), r.view() == self.view().storage.patches {
        proof { use_type_invariant(self); } let _ = self.patches.len(); &self.patches
    }
    pub fn begin(self) -> (r: Option<CheckedWriter<'v, 'a>>)
        ensures self.wf(), match r { Some(writer) => writer.wf() && writer.view().boot.source == self.view().authority.node.volume.index.source
            && writer.owner().images().tx.original == self.view().storage.patches && writer.owner().images().tx.layout == self.view().authority.node.volume.journal, None => true },
    {
        proof { use_type_invariant(&self); }
        let volume = self.node.volume(); let batch = match crate::xattr_batch::freeze(&self.patches, volume.journal().duplicate()) { Some(batch) => batch, None => { return None; } };
        writer_admission::prepare(volume.index().source(), batch)
    }
}
pub fn prepare<'n, 'v, 'a>(grant: Authorization<'n, 'v, 'a>, input: &[u8], seconds: i64, nanos: u32) -> (r: Result<Option<Candidate<'n, 'v, 'a>>, Error>)
    ensures grant.wf(), match r { Ok(Some(candidate)) => candidate.wf() && candidate.view().authority == grant.view() && candidate.view().input == input@
        && candidate.view().storage.change.seconds == seconds as int && candidate.view().storage.change.nanos == nanos as nat,
        Ok(None) => unchanged(grant.view(), input@), Err(_) => true },
{
    let (node, credentials, kind, in_group, Ghost(authority)) = grant.release(); let info = node.info();
    let primary = match node.volume().index().source().block(0) { Some(primary) => primary, None => { return Err(Error::Storage(storage::Error::Admission)); } };
    if feature_policy::is_readonly(primary.range(1024, 1024).unwrap()).unwrap() { return Err(Error::ReadOnly); }
    let removing = acl_xattr::is_removal(input);
    let converted = if removing { None } else { match acl_xattr::decode(input) { Some(value) => Some(value), None => { return Err(Error::InvalidAcl); } } };
    if matches!(kind, Kind::Default) && info.mode & 0xf000 != 0x4000 {
        if removing { return Ok(None); } else { return Err(Error::NotDirectory); }
    }
    assert(credentials.fsuid == info.uid || credentials.fowner) by { reveal(authorized); }
    let mut mode = info.mode; let mut retained = false; let ghost mut acl_view: Option<acl::AclView> = None;
    if let Some(value) = &converted {
        let acl = match value.parsed() { Some(acl) => acl, None => { return Err(Error::InvalidAcl); } };
        let summary = match acl_xattr::summarize(&acl) { Some(summary) => summary, None => { return Err(Error::InvalidAcl); } };
        if matches!(kind, Kind::Access) { mode = mode_after(info.mode, summary.bits, in_group || credentials.fsetid); retained = summary.extended; }
        else { retained = true; }
        proof { acl_view = Some(acl.view()); }
    }
    let attributes = match xattr_inode::inspect(node.volume().index(), node.number()) { Some(attributes) => attributes, None => { return Err(Error::Storage(storage::Error::Admission)); } };
    proof { reveal(authorized); xattr_inode::same_source_has_identical_attributes(attributes.view(), authority.attributes); }
    let original = match store::capture(&attributes) { Some(original) => original, None => { return Err(Error::Storage(storage::Error::Unsupported)); } };
    let ghost before = original.view(); let ns = namespace(kind); let name: &[u8] = &[];
    assert(name@ =~= Seq::<u8>::empty());
    let updated = if retained {
        let disk = converted.as_ref().unwrap().as_slice();
        match original.set(ns, name, disk, 0) { Ok(next) => next, Err((_, error)) => { return Err(Error::Storage(storage::Error::Values(error))); } }
    } else if original.find(ns, name).is_some() {
        match original.remove(ns, name) { Ok(next) => next, Err(_) => { return Err(Error::Storage(storage::Error::Admission)); } }
    } else { original };
    let ghost plan = Plan { acl: acl_view, retained, desired: updated.view(), mode };
    assert(planned(authority, input@, plan)) by { reveal(planned); }
    // Linux folds a mode-only access ACL into i_mode and removes its xattr.
    if mode == info.mode {
        let original = match store::capture(&attributes) { Some(original) => original, None => { return Err(Error::Storage(storage::Error::Unsupported)); } };
        if updated.equivalent(&original) {
            assert(exists|p: Plan| planned(authority, input@, p) && p.mode == authority.node.mode && store::same_contents(p.desired, store::source_items(authority.attributes)));
            return Ok(None);
        }
    }
    let built = match storage::build(node, &updated, mode, seconds, nanos) { Ok(built) => built, Err(error) => { return Err(Error::Storage(error)); } };
    let (patches, Ghost(stored)) = built.into_parts();
    let ghost view = UpdateView { authority, input: input@, plan, storage: stored };
    assert(valid(view)) by { reveal(valid); }
    Ok(Some(Candidate { node, patches, certificate: Ghost(view) }))
}

pub proof fn only_an_owner_or_scoped_fowner_authority_can_produce_a_mutation(v: UpdateView)
    requires valid(v), ensures v.authority.credentials.fsuid == v.authority.node.uid || v.authority.credentials.fowner,
{ reveal(valid); reveal(planned); }
pub proof fn every_other_attribute_survives_an_acl_mutation(v: UpdateView, ns: u8, name: Seq<u8>)
    requires valid(v), ns != number(v.authority.kind) || name != Seq::<u8>::empty(),
    ensures store::get(store::source_items(v.storage.attributes), ns, name) == store::get(store::source_items(v.authority.attributes), ns, name),
{
    reveal(valid); reveal(planned); reveal(storage::valid);
    let before = store::source_items(v.authority.attributes);
    store::equivalent_stores_have_identical_full_key_lookup(store::source_items(v.storage.attributes), v.plan.desired, ns, name);
    match value(v.plan) { Some(raw) => { store::set_preserves_every_other_complete_key(before, number(v.authority.kind), Seq::empty(), raw, ns, name); },
        None => { store::removing_a_complete_key_removes_only_that_key(before, number(v.authority.kind), Seq::empty(), ns, name); } }
}
pub proof fn stored_acls_are_exact_or_folded_and_removed(v: UpdateView)
    requires valid(v),
    ensures store::get(store::source_items(v.storage.attributes), number(v.authority.kind), Seq::empty()) == value(v.plan),
{
    reveal(valid); reveal(planned); reveal(storage::valid);
    let before = store::source_items(v.authority.attributes);
    store::equivalent_stores_have_identical_full_key_lookup(store::source_items(v.storage.attributes), v.plan.desired, number(v.authority.kind), Seq::empty());
    match value(v.plan) { Some(raw) => { store::setting_a_complete_key_returns_the_requested_value(before, number(v.authority.kind), Seq::empty(), raw); },
        None => { store::removing_a_complete_key_removes_only_that_key(before, number(v.authority.kind), Seq::empty(), number(v.authority.kind), Seq::empty()); } }
}
pub proof fn default_and_removed_acls_preserve_the_inode_mode(v: UpdateView)
    requires valid(v), v.authority.kind == Kind::Default || v.plan.acl is None,
    ensures bytes::le16(v.storage.mode.after, 0) == v.authority.node.mode,
{ reveal(valid); reveal(planned); reveal(storage::valid); reveal(inode_mode::valid); }
pub proof fn access_acl_permissions_and_sgid_are_updated_together(v: UpdateView)
    requires valid(v), v.authority.kind == Kind::Access, v.plan.acl is Some,
    ensures bytes::le16(v.storage.mode.after, 0) as u16 & 0o777u16 == acl::permission_mode(v.plan.acl.unwrap().entries),
        !v.authority.in_group && !v.authority.credentials.fsetid ==> bytes::le16(v.storage.mode.after, 0) as u16 & 0o2000u16 == 0,
{
    reveal(valid); reveal(planned); reveal(storage::valid); reveal(inode_mode::valid);
    let old = v.authority.node.mode; let bits = acl::permission_mode(v.plan.acl.unwrap().entries); let keep = v.authority.in_group || v.authority.credentials.fsetid;
    assert(mode_for(old, bits, keep) & 0o777u16 == bits) by (bit_vector) requires bits <= 0o777u16;
    assert(!keep ==> mode_for(old, bits, keep) & 0o2000u16 == 0) by (bit_vector);
}

pub open spec fn admitted(v: UpdateView, a: AdmissionView, images: Images) -> bool {
    valid(v) && crate::xattr_commit::admitted(v.storage.patches, a, images) && a.boot.source == v.authority.node.volume.index.source
        && images.tx.layout == v.authority.node.volume.journal
}
pub proof fn every_writer_cut_recovers_acl_mode_and_storage_together(v: UpdateView, a: AdmissionView,
    images: Images, machine: Machine, layout: &JournalLayout, scan: &crate::scan::Scan, recovery: crate::recovery_device::Machine, tail: Seq<u8>)
    requires admitted(v, a, images), write_device::inv(machine, images.tx.payloads.len()), layout.wf(), layout.view() == images.tx.layout,
        write_recovery::returned(scan, write_recovery::source(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images, layout)),
        crate::recovery_device::inv(recovery, write_media::disk(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images), scan.plan(), images.journal_block, tail),
        recovery.io.phase == 4, !recovery.io.faulted, !recovery.io.pending,
    ensures forall|i: int| 0 <= i < v.storage.patches.len() ==> (if machine.stable.contains(6 + images.tx.payloads.len()) {
            #[trigger] recovery.stable[v.storage.patches[i].block] == v.storage.patches[i].image
        } else if v.storage.patches[i].block == 0 { crate::super_state::preserves(a.boot.source.subrange(0, 4096), recovery.stable[0]) }
        else { recovery.stable[v.storage.patches[i].block] == disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks)[v.storage.patches[i].block] }),
{ crate::xattr_commit::every_writer_cut_recovers_all_xattr_metadata_together(v.storage.patches, a, images, machine, layout, scan, recovery, tail); }

}
