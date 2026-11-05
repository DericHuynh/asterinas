// SPDX-License-Identifier: MPL-2.0

//! Source-bound user-xattr create/replace/remove transactions, including
//! inline/external movement, exclusive reuse and shared-block copy-on-write.
//! Credential authentication, inode locks, frame ownership and device flush
//! refinement remain VFS/OSTD obligations. No kernel mount gate is opened.

use vstd::prelude::*;
use crate::{acl_access::{self, Authorization, AuthorizationView}, allocated_inode::{self, AllocatedInode},
    allocation::{self, AllocationView}, bytes, feature_policy, group_index, inode_table,
    patch_set::{self, PatchSet}, transaction::ImageView, writer_admission::{self, CheckedWriter},
    xattr, xattr_batch, xattr_block_update as block_update, xattr_inode::{self, AttributesView},
    xattr_inode_edit::{self as inode_edit, Change}, xattr_pack, xattr_source, xattr_store::{self as store, Store, ItemView}};

verus! {

pub use crate::xattr_transaction::Error;
pub struct UpdateView { pub grant: AuthorizationView, pub name: Seq<u8>, pub data: Option<Seq<u8>>, pub flags: u32,
    pub desired: Seq<ItemView>, pub region: crate::xattr_footprint::Region, pub change: Change, pub patches: Seq<ImageView>, pub after: AllocationView, pub attributes: AttributesView }
pub open spec fn requested(v: UpdateView) -> bool {
    let before = store::source_items(v.grant.detail.attributes);
    match v.data {
        Some(data) => store::set_error(before, 1, v.name, data, v.flags).is_none() && v.desired == store::updated(before, 1, v.name, data),
        None => store::remove_error(before, 1, v.name).is_none() && v.desired == store::deleted(before, 1, v.name),
    }
}
#[verifier::opaque]
pub open spec fn valid(v: UpdateView) -> bool {
    let node = v.grant.node; let before = node.volume.index;
    &&& acl_access::valid(v.grant) && v.grant.request == 2 && 0 < v.name.len() <= 255
    &&& node.mode & 0xf000 == 0x8000 || node.mode & 0xf000 == 0x4000 && (node.mode & 0o1000 == 0 || v.grant.credentials.fsuid == node.uid)
    &&& !feature_policy::readonly(before.source.subrange(1024, 2048))
    &&& store::valid(store::source_items(v.grant.detail.attributes)) && store::valid(v.desired) && requested(v)
    &&& inode_edit::valid(v.change) && v.change.before == inode_table::raw(before, node.number)
    &&& v.change.number == node.number && v.change.inodes == before.inodes && v.change.seed == before.seed && v.change.huge == group_index::has_huge_files(before)
    &&& crate::xattr_footprint::confined(v.region, v.grant.node, v.patches) && v.region.new == v.change.physical
    &&& patch_set::valid(v.patches) && 0 < v.patches.len() <= 6
    &&& allocation::valid(v.after) && v.after.index.source == patch_set::apply(before.source, v.patches)
    &&& xattr_inode::valid(v.attributes) && v.attributes.index == v.after.index && v.attributes.number == node.number
    &&& (match v.attributes.body.table { Some(table) => crate::xattr_canonical::canonical(table, false), None => true })
    &&& (match v.attributes.external { Some(table) => crate::xattr_canonical::canonical(table, true), None => true })
    &&& store::valid(store::source_items(v.attributes)) && store::same_contents(store::source_items(v.attributes), v.desired)
    &&& inode_table::raw(v.after.index, node.number) == v.change.after
}

pub struct Candidate<'n, 'v, 'a> { node: &'n AllocatedInode<'v, 'a>, patches: PatchSet, checked: Ghost<UpdateView> }
impl<'n, 'v, 'a> Candidate<'n, 'v, 'a> {
    pub closed spec fn view(&self) -> UpdateView { self.checked@ }
    pub closed spec fn node_view(&self) -> allocated_inode::NodeView { self.node.view() }
    pub closed spec fn images(&self) -> Seq<ImageView> { self.patches.view() }
    pub open spec fn wf(&self) -> bool { valid(self.view()) && self.node_view() == self.view().grant.node && self.images() == self.view().patches }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn patches(&self) -> (r: &PatchSet) ensures self.wf(), r.wf(), r.view() == self.view().patches {
        proof { use_type_invariant(self); }
        let _ = self.patches.len(); &self.patches
    }
    pub fn begin(self) -> (r: Option<CheckedWriter<'v, 'a>>)
        ensures self.wf(), match r { Some(writer) => writer.wf() && writer.view().boot.source == self.view().grant.node.volume.index.source
            && writer.owner().images().tx.original == self.view().patches && writer.owner().images().tx.layout == self.view().grant.node.volume.journal, None => true },
    {
        proof { use_type_invariant(&self); }
        let volume = self.node.volume(); let source = volume.index().source();
        let batch = match xattr_batch::freeze(&self.patches, volume.journal().duplicate()) { Some(batch) => batch, None => { return None; } };
        writer_admission::prepare(source, batch)
    }
}

fn prepare<'n, 'v, 'a>(grant: Authorization<'n, 'v, 'a>, name: &[u8], data: Option<&[u8]>, flags: u32, seconds: i64, nanos: u32)
    -> (r: Result<Option<Candidate<'n, 'v, 'a>>, Error>)
    ensures grant.wf(), match r { Ok(Some(candidate)) => candidate.wf() && candidate.view().grant == grant.view() && candidate.view().name == name@
        && candidate.view().data == match data { Some(bytes) => Some(bytes@), None => None } && candidate.view().flags == flags
        && candidate.view().change.seconds == seconds as int && candidate.view().change.nanos == nanos as nat,
        Ok(None) => data is Some && store::set_error(store::source_items(grant.view().detail.attributes), 1, name@, data.unwrap()@, flags).is_none()
            && store::get(store::source_items(grant.view().detail.attributes), 1, name@) == Some(data.unwrap()@), Err(_) => true },
{
    let (node, credentials, request, Ghost(authorization)) = grant.release();
    if request != 2 { return Err(Error::Permission); }
    if name.len() == 0 || name.len() > 255 { return Err(Error::InvalidName); }
    let info = node.info(); let kind = info.mode & 0xf000;
    if kind != 0x8000 && kind != 0x4000 || kind == 0x4000 && info.mode & 0o1000 != 0 && credentials.fsuid != info.uid { return Err(Error::Permission); }
    let volume = node.volume(); let index = volume.index(); let number = node.number(); let source_inode = node.raw(); let (blocks, inodes, _, seed) = index.parameters();
    let primary = match index.source().block(0) { Some(primary) => primary, None => { return Err(Error::Admission); } };
    if feature_policy::is_readonly(primary.range(1024, 1024).unwrap()).unwrap() { return Err(Error::ReadOnly); }
    let attributes = match xattr_inode::inspect(index, number) { Some(attributes) => attributes, None => { return Err(Error::Admission); } };
    proof { reveal(acl_access::valid); xattr_inode::same_source_has_identical_attributes(attributes.view(), authorization.detail.attributes); }
    let original = match store::capture(&attributes) { Some(original) => original, None => { return Err(Error::Unsupported); } };
    let ghost before_items = original.view();
    let ghost desired_data = match data { Some(bytes) => Some(bytes@), None => None };
    let updated = match data {
        Some(data) => {
            let old_position = original.find(1, name);
            let equal = match old_position { Some(i) => bytes::equal(original.item(i).unwrap().bytes(), data), None => false };
            let result = match original.set(1, name, data, flags) { Ok(updated) => updated, Err((_, error)) => { return Err(Error::Values(error)); } };
            if equal { return Ok(None); }
            result
        },
        None => match original.remove(1, name) { Ok(updated) => updated, Err((_, error)) => { return Err(Error::Values(error)); } },
    };
    let storage = match crate::xattr_transaction::build(node, &updated, info.mode, seconds, nanos) { Ok(storage) => storage, Err(error) => { return Err(error); } };
    let (patches, Ghost(stored)) = storage.into_parts();
    proof { crate::xattr_transaction::retaining_the_mode_retains_the_original_xattr_update_inode(stored); }
    let ghost view = UpdateView { grant: authorization, name: name@, data: desired_data, flags, desired: updated.view(), region: stored.region,
        change: stored.change, patches: patches.view(), after: stored.after, attributes: stored.attributes };
    assert(valid(view)) by { reveal(valid); reveal(crate::xattr_transaction::valid); }
    Ok(Some(Candidate { node, patches, checked: Ghost(view) }))
}

pub fn set_user<'n, 'v, 'a>(grant: Authorization<'n, 'v, 'a>, name: &[u8], data: &[u8], flags: u32, seconds: i64, nanos: u32)
    -> (r: Result<Option<Candidate<'n, 'v, 'a>>, Error>)
    ensures grant.wf(), match r { Ok(Some(candidate)) => candidate.wf() && candidate.view().grant == grant.view() && candidate.view().name == name@
        && candidate.view().data == Some(data@) && candidate.view().flags == flags && candidate.view().change.seconds == seconds as int && candidate.view().change.nanos == nanos as nat,
        Ok(None) => store::set_error(store::source_items(grant.view().detail.attributes), 1, name@, data@, flags).is_none()
            && store::get(store::source_items(grant.view().detail.attributes), 1, name@) == Some(data@), Err(_) => true },
{ prepare(grant, name, Some(data), flags, seconds, nanos) }
pub fn remove_user<'n, 'v, 'a>(grant: Authorization<'n, 'v, 'a>, name: &[u8], seconds: i64, nanos: u32)
    -> (r: Result<Candidate<'n, 'v, 'a>, Error>)
    ensures grant.wf(), match r { Ok(candidate) => candidate.wf() && candidate.view().grant == grant.view() && candidate.view().name == name@
        && candidate.view().data is None && candidate.view().change.seconds == seconds as int && candidate.view().change.nanos == nanos as nat, Err(_) => true },
{
    match prepare(grant, name, None, 0, seconds, nanos) { Ok(Some(candidate)) => Ok(candidate), Ok(None) => Err(Error::Encoding), Err(error) => Err(error) }
}

pub proof fn every_update_retains_every_other_complete_key(v: UpdateView, namespace: u8, name: Seq<u8>)
    requires valid(v), namespace != 1 || name != v.name,
    ensures store::get(store::source_items(v.attributes), namespace, name) == store::get(store::source_items(v.grant.detail.attributes), namespace, name),
{
    reveal(valid); let before = store::source_items(v.grant.detail.attributes);
    store::equivalent_stores_have_identical_full_key_lookup(store::source_items(v.attributes), v.desired, namespace, name);
    match v.data { Some(data) => { store::set_preserves_every_other_complete_key(before, 1, v.name, data, namespace, name); },
        None => { store::removing_a_complete_key_removes_only_that_key(before, 1, v.name, namespace, name); } }
}
pub proof fn created_or_replaced_values_are_exact_and_removed_keys_are_absent(v: UpdateView)
    requires valid(v),
    ensures store::get(store::source_items(v.attributes), 1, v.name) == v.data,
{
    reveal(valid); let before = store::source_items(v.grant.detail.attributes);
    store::equivalent_stores_have_identical_full_key_lookup(store::source_items(v.attributes), v.desired, 1, v.name);
    match v.data { Some(data) => { store::setting_a_complete_key_returns_the_requested_value(before, 1, v.name, data); },
        None => { store::removing_a_complete_key_removes_only_that_key(before, 1, v.name, 1, v.name); } }
}

}
