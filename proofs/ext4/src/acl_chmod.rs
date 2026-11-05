// SPDX-License-Identifier: MPL-2.0

//! Source-bound chmod transactions. Ownership and scoped capabilities are
//! authenticated VFS inputs; this host object supplies no runtime lock.

use vstd::prelude::*;
use crate::{acl, acl_transform::{self, TransformView}, acl_update::{self, Kind, AuthorizationView},
    allocated_inode::{AllocatedInode, NodeView}, bytes, feature_policy, patch_set::PatchSet,
    transaction::ImageView, writer_admission::{self, CheckedWriter}, xattr_inode,
    xattr_store::{self as store, ItemView}, xattr_transaction::{self as storage, StorageView}};
use crate::{disk_image, layout::JournalLayout, write_device::{self, Machine}, write_io::Images,
    write_media, write_recovery, writer_admission::AdmissionView};

verus! {

pub use crate::acl_update::Credentials;
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Error { Permission, InvalidMode, ReadOnly, InvalidAcl, Storage(storage::Error) }

pub struct Authorization<'n, 'v, 'a> { grant: acl_update::Authorization<'n, 'v, 'a> }
impl<'n, 'v, 'a> Authorization<'n, 'v, 'a> {
    pub closed spec fn view(&self) -> AuthorizationView { self.grant.view() }
    pub closed spec fn wf(&self) -> bool { self.grant.wf() && self.view().kind == Kind::Access }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    fn release(self) -> (r: acl_update::Authorization<'n, 'v, 'a>)
        ensures self.wf(), r.wf(), r.view() == self.view(), r.view().kind == Kind::Access,
    { proof { use_type_invariant(&self); } self.grant }
}
pub fn authorize<'n, 'v, 'a>(node: &'n AllocatedInode<'v, 'a>, credentials: &Credentials, groups: &[u32])
    -> (r: Option<Authorization<'n, 'v, 'a>>)
    ensures node.wf(), match r { Some(grant) => grant.wf() && grant.view().node == node.view()
        && grant.view().credentials == *credentials && grant.view().groups == groups@, None => true },
{
    let grant = match acl_update::authorize(node, credentials, groups, Kind::Access) { Some(grant) => grant, None => { return None; } };
    Some(Authorization { grant })
}
pub open spec fn mode_for(old: u16, requested: u16, keep_gid: bool) -> u16 {
    (old & !0o7777u16) | (if keep_gid { requested } else { requested & !0o2000u16 })
}
fn requested_mode(old: u16, requested: u16, keep_gid: bool) -> (r: u16)
    ensures r == mode_for(old, requested, keep_gid),
{ (old & !0o7777u16) | (if keep_gid { requested } else { requested & !0o2000u16 }) }

pub struct Plan { pub transformed: Option<TransformView>, pub desired: Seq<ItemView>, pub mode: u16 }
#[verifier::opaque]
pub open spec fn planned(a: AuthorizationView, requested: u16, p: Plan) -> bool {
    let before = store::source_items(a.attributes);
    &&& acl_update::authorized(a) && a.kind == Kind::Access && requested <= 0o7777
    &&& store::valid(before) && store::valid(p.desired)
    &&& p.mode == mode_for(a.node.mode, requested, a.in_group || a.credentials.fsetid)
    &&& match p.transformed {
        None => store::get(before, 2, Seq::empty()).is_none() && p.desired == before,
        Some(t) => acl_transform::valid(t) && !t.inheritance && t.requested == p.mode
            && store::get(before, 2, Seq::empty()) == Some(t.before.raw)
            && if t.extended { store::set_error(before, 2, Seq::empty(), t.after.raw, 0).is_none()
                && p.desired == store::updated(before, 2, Seq::empty(), t.after.raw) }
                else { p.desired == store::deleted(before, 2, Seq::empty()) },
    }
}
pub struct UpdateView { pub authority: AuthorizationView, pub requested: u16, pub plan: Plan, pub storage: StorageView }
#[verifier::opaque]
pub open spec fn valid(v: UpdateView) -> bool {
    planned(v.authority, v.requested, v.plan) && storage::valid(v.storage) && v.storage.chmod
        && !feature_policy::readonly(v.authority.node.volume.index.source.subrange(1024, 2048))
        && v.storage.node == v.authority.node && v.storage.desired == v.plan.desired && v.storage.mode.mode == v.plan.mode
}
pub struct Candidate<'n, 'v, 'a> { node: &'n AllocatedInode<'v, 'a>, patches: PatchSet, checked: Ghost<UpdateView> }
impl<'n, 'v, 'a> Candidate<'n, 'v, 'a> {
    pub closed spec fn view(&self) -> UpdateView { self.checked@ }
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
pub open spec fn unchanged(a: AuthorizationView, requested: u16) -> bool {
    exists|p: Plan| planned(a, requested, p) && p.mode == a.node.mode && store::same_contents(p.desired, store::source_items(a.attributes))
}
pub fn prepare<'n, 'v, 'a>(grant: Authorization<'n, 'v, 'a>, requested: u16, seconds: i64, nanos: u32)
    -> (r: Result<Option<Candidate<'n, 'v, 'a>>, Error>)
    ensures grant.wf(), match r { Ok(Some(candidate)) => candidate.wf() && candidate.view().authority == grant.view() && candidate.view().requested == requested
        && candidate.view().storage.change.seconds == seconds as int && candidate.view().storage.change.nanos == nanos as nat,
        Ok(None) => unchanged(grant.view(), requested), Err(_) => true },
{
    let inner = grant.release();
    let (node, credentials, _, in_group, Ghost(authority)) = inner.release();
    if requested > 0o7777 { return Err(Error::InvalidMode); }
    let info = node.info(); let mode = requested_mode(info.mode, requested, in_group || credentials.fsetid);
    let primary = match node.volume().index().source().block(0) { Some(primary) => primary, None => { return Err(Error::Storage(storage::Error::Admission)); } };
    if feature_policy::is_readonly(primary.range(1024, 1024).unwrap()).unwrap() { return Err(Error::ReadOnly); }
    let attributes = match xattr_inode::inspect(node.volume().index(), node.number()) { Some(attributes) => attributes, None => { return Err(Error::Storage(storage::Error::Admission)); } };
    proof { reveal(acl_update::authorized); xattr_inode::same_source_has_identical_attributes(attributes.view(), authority.attributes); }
    let original = match store::capture(&attributes) { Some(original) => original, None => { return Err(Error::Storage(storage::Error::Unsupported)); } };
    let ghost before = original.view(); let name: &[u8] = &[]; assert(name@ =~= Seq::<u8>::empty());
    let mut transformed = None;
    if let Some(i) = original.find(2, name) {
        let raw = original.item(i).unwrap().bytes();
        assert(store::get(before, 2, Seq::empty()) == Some(raw@));
        let acl = match acl::parse(raw) { Some(acl) => acl, None => { return Err(Error::InvalidAcl); } };
        transformed = match acl_transform::chmod(&acl, mode) { Some(t) => Some(t), None => { return Err(Error::InvalidAcl); } };
    }
    let ghost mut transformation: Option<TransformView> = None;
    let desired = match transformed {
        Some(ref value) => {
            proof { transformation = Some(value.view()); }
            if value.extended() {
                match original.set(2, name, value.as_slice(), 0) { Ok(next) => next, Err((_, error)) => { return Err(Error::Storage(storage::Error::Values(error))); } }
            } else {
                match original.remove(2, name) { Ok(next) => next, Err(_) => { return Err(Error::Storage(storage::Error::Admission)); } }
            }
        }, None => original,
    };
    let ghost plan = Plan { transformed: transformation, desired: desired.view(), mode };
    assert(acl_update::authorized(authority) && authority.kind == Kind::Access);
    assert(plan.mode == mode_for(authority.node.mode, requested, authority.in_group || authority.credentials.fsetid));
    assert(match plan.transformed { None => store::get(before, 2, Seq::empty()).is_none() && plan.desired == before,
        Some(t) => acl_transform::valid(t) && !t.inheritance && t.requested == plan.mode && store::get(before, 2, Seq::empty()) == Some(t.before.raw) });
    assert(planned(authority, requested, plan)) by { reveal(planned); }
    let built = match storage::build_chmod(node, &desired, mode, seconds, nanos) { Ok(built) => built, Err(error) => { return Err(Error::Storage(error)); } };
    let (patches, Ghost(stored)) = built.into_parts();
    let ghost view = UpdateView { authority, requested, plan, storage: stored };
    assert(valid(view)) by { reveal(valid); }
    Ok(Some(Candidate { node, patches, checked: Ghost(view) }))
}
pub proof fn chmod_requires_owner_or_scoped_fowner_and_never_uses_fsetid_as_ownership(v: UpdateView)
    requires valid(v), ensures v.authority.credentials.fsuid == v.authority.node.uid || v.authority.credentials.fowner,
{ reveal(valid); reveal(planned); reveal(acl_update::authorized); }
pub proof fn chmod_special_bits_follow_the_requested_mode_and_scoped_group_policy(v: UpdateView)
    requires valid(v),
    ensures v.plan.mode & !0o7777u16 == v.authority.node.mode & !0o7777u16,
        v.plan.mode & 0o7777u16 == (if v.authority.in_group || v.authority.credentials.fsetid { v.requested } else { v.requested & !0o2000u16 }),
        !v.authority.in_group && !v.authority.credentials.fsetid ==> v.plan.mode & 0o2000u16 == 0,
{
    reveal(valid); reveal(planned); let old = v.authority.node.mode; let req = v.requested; let keep = v.authority.in_group || v.authority.credentials.fsetid;
    assert(mode_for(old, req, keep) & !0o7777u16 == old & !0o7777u16) by (bit_vector) requires req <= 0o7777u16;
    assert(mode_for(old, req, keep) & 0o7777u16 == (if keep { req } else { req & !0o2000u16 })) by (bit_vector) requires req <= 0o7777u16;
    assert(!keep ==> mode_for(old, req, keep) & 0o2000u16 == 0) by (bit_vector);
}
pub proof fn chmod_preserves_default_acls_and_every_other_attribute(v: UpdateView, ns: u8, name: Seq<u8>)
    requires valid(v), ns != 2 || name != Seq::<u8>::empty(),
    ensures store::get(store::source_items(v.storage.attributes), ns, name) == store::get(store::source_items(v.authority.attributes), ns, name),
{
    reveal(valid); reveal(planned); reveal(storage::valid); let before = store::source_items(v.authority.attributes);
    store::equivalent_stores_have_identical_full_key_lookup(store::source_items(v.storage.attributes), v.plan.desired, ns, name);
    if let Some(t) = v.plan.transformed {
        if t.extended { store::set_preserves_every_other_complete_key(before, 2, Seq::empty(), t.after.raw, ns, name); }
        else { store::removing_a_complete_key_removes_only_that_key(before, 2, Seq::empty(), ns, name); }
    }
}
pub proof fn chmod_publishes_the_exact_transformed_acl_or_folds_it_into_the_mode(v: UpdateView)
    requires valid(v),
    ensures match v.plan.transformed { Some(t) =>
        (store::get(store::source_items(v.storage.attributes), 2, Seq::empty()) == if t.extended { Some(t.after.raw) } else { None })
        && v.storage.mode.mode & 0o777u16 == acl::permission_mode(t.after.entries),
        None => store::get(store::source_items(v.storage.attributes), 2, Seq::empty()).is_none() },
{
    reveal(valid); reveal(planned); reveal(storage::valid); let before = store::source_items(v.authority.attributes);
    store::equivalent_stores_have_identical_full_key_lookup(store::source_items(v.storage.attributes), v.plan.desired, 2, Seq::empty());
    if let Some(t) = v.plan.transformed {
        if t.extended { store::setting_a_complete_key_returns_the_requested_value(before, 2, Seq::empty(), t.after.raw); }
        else { store::removing_a_complete_key_removes_only_that_key(before, 2, Seq::empty(), 2, Seq::empty()); }
    }
}
pub open spec fn admitted(v: UpdateView, a: AdmissionView, images: Images) -> bool {
    valid(v) && crate::xattr_commit::admitted(v.storage.patches, a, images) && a.boot.source == v.authority.node.volume.index.source
        && images.tx.layout == v.authority.node.volume.journal
}
pub proof fn every_writer_cut_recovers_chmod_acl_and_special_bits_together(v: UpdateView, a: AdmissionView,
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
