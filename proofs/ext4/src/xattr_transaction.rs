// SPDX-License-Identifier: MPL-2.0

//! Shared checked xattr storage transaction builder. Its executable constructor
//! is crate-private; operation-specific factories must establish authority.
//! Owned source bytes confer no CortenMM, device or runtime-lock authority.

use vstd::prelude::*;
use crate::{allocated_inode::{self, AllocatedInode, NodeView}, allocation::{self, AllocationView}, bytes, group_index,
    inode_table, patch_set::{self, PatchSet}, transaction::ImageView, xattr, xattr_block_update as block_update,
    xattr_inode::{self, AttributesView}, xattr_inode_edit::{self as inode_edit, Change}, xattr_pack, xattr_source,
    xattr_store::{self as store, ItemView, Store}};

verus! {

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Error { InvalidName, Permission, ReadOnly, Values(store::Error), Unsupported, NoSpace, Encoding, Admission }

pub struct StorageView { pub node: NodeView, pub desired: Seq<ItemView>, pub change: Change, pub mode: crate::inode_mode::Change,
    pub region: crate::xattr_footprint::Region, pub patches: Seq<ImageView>, pub after: AllocationView, pub attributes: AttributesView }
#[verifier::opaque]
pub open spec fn valid(v: StorageView) -> bool {
    let before = v.node.volume.index;
    &&& allocated_inode::valid(v.node) && store::valid(v.desired)
    &&& inode_edit::valid(v.change) && v.change.before == inode_table::raw(before, v.node.number)
    &&& v.change.number == v.node.number && v.change.inodes == before.inodes && v.change.seed == before.seed && v.change.huge == group_index::has_huge_files(before)
    &&& crate::inode_mode::valid(v.mode) && v.mode.before == v.change.after && v.mode.number == v.change.number
        && v.mode.inodes == v.change.inodes && v.mode.seed == v.change.seed && v.mode.huge == v.change.huge
    &&& crate::xattr_footprint::confined(v.region, v.node, v.patches) && v.region.new == v.change.physical
    &&& patch_set::valid(v.patches) && 0 < v.patches.len() <= 6
    &&& allocation::valid(v.after) && v.after.index.source == patch_set::apply(before.source, v.patches)
    &&& xattr_inode::valid(v.attributes) && v.attributes.index == v.after.index && v.attributes.number == v.node.number
    &&& (match v.attributes.body.table { Some(table) => crate::xattr_canonical::canonical(table, false), None => true })
    &&& (match v.attributes.external { Some(table) => crate::xattr_canonical::canonical(table, true), None => true })
    &&& store::valid(store::source_items(v.attributes)) && store::same_contents(store::source_items(v.attributes), v.desired)
    &&& inode_table::raw(v.after.index, v.node.number) == v.mode.after
}
pub(crate) struct Storage { patches: PatchSet, checked: Ghost<StorageView> }
impl Storage {
    pub(crate) closed spec fn view(&self) -> StorageView { self.checked@ }
    pub(crate) closed spec fn wf(&self) -> bool { valid(self.view()) && self.patches.view() == self.view().patches }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub(crate) fn into_parts(self) -> (r: (PatchSet, Ghost<StorageView>))
        ensures self.wf(), r.0.wf(), r.0.view() == self.view().patches, r.1@ == self.view(), valid(r.1@),
    { proof { use_type_invariant(&self); } let _ = self.patches.len(); (self.patches, self.checked) }
}
fn copy_block(source: &[u8]) -> (r: Option<Vec<u8>>)
    ensures match r { Some(next) => source.len() == 4096 && next@ == source@, None => source.len() != 4096 },
{
    if source.len() != 4096 { return None; }
    let mut next = bytes::zero_block(); bytes::write_bytes(next.as_mut_slice(), 0, source); Some(next)
}
pub(crate) fn build(node: &AllocatedInode<'_, '_>, desired: &Store, mode: u16, seconds: i64, nanos: u32) -> (r: Result<Storage, Error>)
    ensures node.wf(), desired.wf(), match r { Ok(storage) => storage.wf() && valid(storage.view()) && storage.view().node == node.view() && storage.view().desired == desired.view()
        && storage.view().mode.mode == mode && storage.view().change.seconds == seconds as int && storage.view().change.nanos == nanos as nat, Err(_) => true },
{
    hide(crate::crc::fold);
    let _ = desired.len();
    let volume = node.volume(); let index = volume.index(); let number = node.number(); let source_inode = node.raw(); let (blocks, inodes, _, seed) = index.parameters();
    let primary = match index.source().block(0) { Some(primary) => primary, None => { return Err(Error::Admission); } };
    let old_address = xattr::inode_pointer(source_inode).unwrap(); if old_address >= blocks as u64 { return Err(Error::Admission); }
    let old_block = old_address as u32;
    let mut old_refs = 0u32;
    if old_block > 0 {
        let old = match xattr_source::inspect_block(index, old_address) { Some(old) => old, None => { return Err(Error::Admission); } }; old_refs = old.refcount();
    }
    // A dummy address lets the packer decide whether an external block is
    // necessary before requesting space; inline-only updates work on full disks.
    let tentative = if old_block > 0 && old_refs == 1 { old_block } else { 1u32 };
    let packed = match xattr_pack::encode(desired, source_inode, tentative as u64, seed, inodes) { Some(packed) => packed, None => { return Err(Error::NoSpace); } };
    let (packed, new_block) = if packed.has_external() && tentative == 1 {
        let free = match block_update::free_block(volume) { Some(free) => free, None => { return Err(Error::NoSpace); } };
        let packed = match xattr_pack::encode(desired, source_inode, free as u64, seed, inodes) { Some(packed) => packed, None => { return Err(Error::Encoding); } };
        (packed, free)
    } else { let physical = if packed.has_external() { tentative } else { 0u32 }; (packed, physical) };
    let (body, external) = packed.into_parts();
    let encoded = match inode_edit::encode(source_inode, &body, new_block, number, inodes, seed, index.huge_files(), seconds, nanos) { Some(raw) => raw, None => { return Err(Error::Encoding); } };
    let ghost change = Change { before: source_inode@, packed: body@, after: encoded@, physical: new_block, number, inodes, seed,
        huge: group_index::has_huge_files(index.view()), seconds: seconds as int, nanos: nanos as nat };
    let final_inode = match crate::inode_mode::encode(&encoded, mode, number, inodes, seed, index.huge_files()) { Some(raw) => raw, None => { return Err(Error::Encoding); } };
    let ghost mode_change = crate::inode_mode::Change { before: encoded@, after: final_inode@, mode, number, inodes, seed, huge: group_index::has_huge_files(index.view()) };
    let mut patches = PatchSet::new();
    if new_block > 0 && new_block != old_block {
        patches = match block_update::accounting(volume, new_block, true) { Some(patches) => patches, None => { return Err(Error::Admission); } };
    } else if new_block == 0 && old_block > 0 && old_refs == 1 {
        patches = match block_update::accounting(volume, old_block, false) { Some(patches) => patches, None => { return Err(Error::Admission); } };
    }
    if desired.len() > 0 && bytes::read_le32(primary.as_slice(), 1116).unwrap() & 8 == 0 {
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
    let position = match inode_table::position(index, number) { Some(position) => position, None => { return Err(Error::Admission); } };
    if position / 4096 > u32::MAX as u64 || position % 4096 > 3840 { return Err(Error::Admission); }
    let target = (position / 4096) as u32;
    let original_block = match index.source().block(target) { Some(block) => block, None => { return Err(Error::Admission); } };
    let mut inode_block = copy_block(original_block.as_slice()).unwrap();
    if !bytes::write_bytes(inode_block.as_mut_slice(), (position % 4096) as usize, &final_inode) { return Err(Error::Encoding); }
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
    if !actual.equivalent(desired) { return Err(Error::Admission); }
    let after_raw = match inode_table::read(after.index(), number) { Some(raw) => raw, None => { return Err(Error::Admission); } };
    if !bytes::equal(after_raw, &final_inode) { return Err(Error::Admission); }
    let ghost view = StorageView { node: node.view(), desired: desired.view(), change, mode: mode_change, region, patches: patches.view(), after: after.view(), attributes: after_attributes.view() };
    assert(valid(view)) by { reveal(valid); }
    Ok(Storage { patches, checked: Ghost(view) })
}

pub proof fn retaining_the_mode_retains_the_original_xattr_update_inode(v: StorageView)
    requires valid(v), v.mode.mode == v.node.mode,
    ensures v.mode.after == v.change.after,
{
    reveal(valid); reveal(crate::inode_mode::valid); reveal(allocated_inode::valid);
    inode_edit::xattr_updates_preserve_inode_identity_mode_owners_and_extent_root(v.change, 0);
    inode_edit::xattr_updates_preserve_inode_identity_mode_owners_and_extent_root(v.change, 1);
}

}
