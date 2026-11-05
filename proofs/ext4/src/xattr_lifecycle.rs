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

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Error { InvalidName, Permission, ReadOnly, Values(store::Error), Unsupported, NoSpace, Encoding, Admission }
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

fn copy_block(source: &[u8]) -> (r: Option<Vec<u8>>)
    ensures match r { Some(next) => source.len() == 4096 && next@ == source@, None => source.len() != 4096 },
{
    if source.len() != 4096 { return None; }
    let mut next = bytes::zero_block(); bytes::write_bytes(next.as_mut_slice(), 0, source); Some(next)
}
fn prepare<'n, 'v, 'a>(grant: Authorization<'n, 'v, 'a>, name: &[u8], data: Option<&[u8]>, flags: u32, seconds: i64, nanos: u32)
    -> (r: Result<Option<Candidate<'n, 'v, 'a>>, Error>)
    ensures grant.wf(), match r { Ok(Some(candidate)) => candidate.wf() && candidate.view().grant == grant.view() && candidate.view().name == name@
        && candidate.view().data == match data { Some(bytes) => Some(bytes@), None => None } && candidate.view().flags == flags
        && candidate.view().change.seconds == seconds as int && candidate.view().change.nanos == nanos as nat,
        Ok(None) => data is Some && store::set_error(store::source_items(grant.view().detail.attributes), 1, name@, data.unwrap()@, flags).is_none()
            && store::get(store::source_items(grant.view().detail.attributes), 1, name@) == Some(data.unwrap()@), Err(_) => true },
{
    hide(crate::crc::fold);
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
    let old_address = xattr::inode_pointer(source_inode).unwrap(); if old_address >= blocks as u64 { return Err(Error::Admission); }
    let old_block = old_address as u32;
    let mut old_refs = 0u32;
    if old_block > 0 {
        let old = match xattr_source::inspect_block(index, old_address) { Some(old) => old, None => { return Err(Error::Admission); } }; old_refs = old.refcount();
    }
    // A dummy address lets the packer decide whether an external block is
    // necessary before requesting space; inline-only updates work on full disks.
    let tentative = if old_block > 0 && old_refs == 1 { old_block } else { 1u32 };
    let packed = match xattr_pack::encode(&updated, source_inode, tentative as u64, seed, inodes) { Some(packed) => packed, None => { return Err(Error::NoSpace); } };
    let (packed, new_block) = if packed.has_external() && tentative == 1 {
        let free = match block_update::free_block(volume) { Some(free) => free, None => { return Err(Error::NoSpace); } };
        let packed = match xattr_pack::encode(&updated, source_inode, free as u64, seed, inodes) { Some(packed) => packed, None => { return Err(Error::Encoding); } };
        (packed, free)
    } else { let physical = if packed.has_external() { tentative } else { 0u32 }; (packed, physical) };
    let (body, external) = packed.into_parts();
    let encoded = match inode_edit::encode(source_inode, &body, new_block, number, inodes, seed, index.huge_files(), seconds, nanos) { Some(raw) => raw, None => { return Err(Error::Encoding); } };
    let ghost change = Change { before: source_inode@, packed: body@, after: encoded@, physical: new_block, number, inodes, seed,
        huge: group_index::has_huge_files(index.view()), seconds: seconds as int, nanos: nanos as nat };
    let mut patches = PatchSet::new();
    if new_block > 0 && new_block != old_block {
        patches = match block_update::accounting(volume, new_block, true) { Some(patches) => patches, None => { return Err(Error::Admission); } };
    } else if new_block == 0 && old_block > 0 && old_refs == 1 {
        patches = match block_update::accounting(volume, old_block, false) { Some(patches) => patches, None => { return Err(Error::Admission); } };
    }
    if bytes::read_le32(primary.as_slice(), 1116).unwrap() & 8 == 0 {
        let mut promoted = match patches.get(0) { Some(image) => copy_block(image.as_slice()).unwrap(), None => copy_block(primary.as_slice()).unwrap() };
        let flags = bytes::read_le32(&promoted, 1116).unwrap() | 8u32; bytes::write_le32(promoted.as_mut_slice(), 1116, flags);
        let dirty = bytes::read_le32(&promoted, 1120).unwrap() | 4u32; bytes::write_le32(promoted.as_mut_slice(), 1120, dirty);
        let checksum = crate::crc::crc32c(0xffffffff, &promoted[1024..2044]); bytes::write_le32(promoted.as_mut_slice(), 2044, checksum);
        patches = match patches.upsert(0, &promoted) { Ok(patches) => patches, Err(_) => { return Err(Error::Admission); } };
    }
    if old_block > 0 && old_block != new_block && old_refs > 1 {
        let old = match index.source().block(old_block) { Some(old) => old, None => { return Err(Error::Admission); } };
        let detached = match block_update::detach_shared(old.as_slice(), old_block, seed, inodes) { Some(raw) => raw, None => { return Err(Error::Encoding); } };
        patches = match patches.insert(old_block, &detached) { Ok(patches) => patches, Err(_) => { return Err(Error::Admission); } };
    }
    match external {
        Some(raw) => { patches = match patches.insert(new_block, &raw) { Ok(patches) => patches, Err(_) => { return Err(Error::Admission); } }; },
        None => { if new_block != 0 { return Err(Error::Encoding); } },
    }
    let position = inode_table::position(index, number).unwrap();
    if position / 4096 > u32::MAX as u64 || position % 4096 > 3840 { return Err(Error::Admission); }
    let target = (position / 4096) as u32;
    let original_block = match index.source().block(target) { Some(block) => block, None => { return Err(Error::Admission); } };
    let mut inode_block = copy_block(original_block.as_slice()).unwrap();
    if !bytes::write_bytes(inode_block.as_mut_slice(), (position % 4096) as usize, &encoded) { return Err(Error::Encoding); }
    patches = match patches.insert(target, &inode_block) { Ok(patches) => patches, Err(_) => { return Err(Error::Admission); } };
    if patches.len() == 0 || patches.len() > 6 { return Err(Error::Admission); }
    let region = match crate::xattr_footprint::check(node, new_block, &patches) { Some(region) => region, None => { return Err(Error::Admission); } };
    let shadow = match index.source().overlay(&patches) { Some(shadow) => shadow, None => { return Err(Error::Admission); } };
    let after = match allocation::parse(shadow) { Some(after) => after, None => { return Err(Error::Admission); } };
    let after_attributes = match xattr_inode::inspect(after.index(), number) { Some(attributes) => attributes, None => { return Err(Error::Admission); } };
    let (first, second) = after_attributes.source_tables();
    if let Some(table) = first { if !crate::xattr_canonical::check(table, false) { return Err(Error::Admission); } }
    if let Some(table) = second { if !crate::xattr_canonical::check(table, true) { return Err(Error::Admission); } }
    let actual = match store::capture(&after_attributes) { Some(actual) => actual, None => { return Err(Error::Admission); } };
    if !actual.equivalent(&updated) { return Err(Error::Admission); }
    let after_raw = match inode_table::read(after.index(), number) { Some(raw) => raw, None => { return Err(Error::Admission); } };
    if !bytes::equal(after_raw, &encoded) { return Err(Error::Admission); }
    let ghost view = UpdateView { grant: authorization, name: name@, data: desired_data, flags, desired: updated.view(), region, change, patches: patches.view(),
        after: after.view(), attributes: after_attributes.view() };
    assert(valid(view)) by { reveal(valid); }
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
