// SPDX-License-Identifier: MPL-2.0

//! Source-bound ACL-authorized inode-body user-xattr transaction candidates.
//! One immutable snapshot, one owned metadata image and the existing sealed
//! journal writer. Authentication, xattr locks and CortenMM/device refinement
//! remain VFS/OSTD obligations; this is not a mounted setxattr syscall.

use vstd::prelude::*;
use crate::{acl_access::{self, Authorization, AuthorizationView}, allocated_inode::{self, AllocatedInode, NodeView}, allocation,
    bytes, edit_handles, feature_policy, inode_table, patch_set, transaction::{AfterImage, ImageView},
    writer_admission::{self, AdmissionView, CheckedWriter}, xattr::{self, BodyView}, xattr_replace::{self as replace, Change},
    xattr_table::{self as table, ValueView}, xattr_table_edit as edit, write_io::Images};

verus! {

pub struct UpdateView { pub grant: AuthorizationView, pub change: Change, pub image: ImageView }
pub open spec fn image_for(node: NodeView, change: Change) -> ImageView {
    let position = inode_table::start(node.volume.index, node.number);
    let block = (position / 4096) as u32;
    ImageView { block, image: bytes::splice(node.volume.index.source.subrange(block as int * 4096, (block as int + 1) * 4096),
        position as int % 4096, replace::result(change)) }
}
#[verifier::opaque]
pub open spec fn valid(v: UpdateView) -> bool {
    let n = v.grant.node;
    &&& acl_access::valid(v.grant) && v.grant.request == 2 && n.mode & 0xf000 == 0x8000
    &&& !feature_policy::readonly(n.volume.index.source.subrange(1024, 2048))
    &&& replace::allowed(v.change) && v.change.body == v.grant.detail.attributes.body
    &&& v.change.number == n.number && v.change.inodes == n.volume.index.inodes && v.change.seed == n.volume.index.seed
    &&& v.change.huge == crate::group_index::has_huge_files(n.volume.index)
    &&& v.image == image_for(n, v.change) && v.image.image.len() == 4096 && v.image.block < n.volume.index.blocks
    &&& replace::result(v.change).len() == 256
}

proof fn the_acl_source_and_a_fresh_body_parse_are_identical(grant: AuthorizationView, body: BodyView)
    requires acl_access::valid(grant), xattr::valid_body(body), body.raw == inode_table::raw(grant.node.volume.index, grant.node.number),
        !body.ea, body.inodes == grant.node.volume.index.inodes,
    ensures body == grant.detail.attributes.body,
{
    reveal(acl_access::valid);
    let other = grant.detail.attributes.body;
    if let Some(a) = body.table {
        let b = other.table.unwrap();
        edit::two_complete_tables_from_the_same_bytes_have_identical_records(a, b);
        assert(a == b);
    }
}

pub struct Candidate<'n, 'v, 'a> { node: &'n AllocatedInode<'v, 'a>, image: AfterImage, update: Ghost<UpdateView> }
impl<'n, 'v, 'a> Candidate<'n, 'v, 'a> {
    pub closed spec fn view(&self) -> UpdateView { self.update@ }
    pub closed spec fn node_view(&self) -> NodeView { self.node.view() }
    pub closed spec fn image_view(&self) -> ImageView { self.image.view() }
    pub open spec fn wf(&self) -> bool { valid(self.view()) && self.node_view() == self.view().grant.node && self.image_view() == self.view().image }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn after_image(&self) -> (r: &AfterImage) ensures self.wf(), r.view() == self.view().image {
        proof { use_type_invariant(self); } &self.image
    }
    pub fn begin(self) -> (r: Option<CheckedWriter<'v, 'a>>)
        ensures self.wf(), match r { Some(writer) => writer.wf() && writer.view().boot.source == self.view().grant.node.volume.index.source
            && writer.owner().images().tx.original == seq![self.view().image]
            && writer.owner().images().tx.layout == self.view().grant.node.volume.journal, None => true },
    {
        proof { use_type_invariant(&self); }
        let volume = self.node.volume();
        let source = volume.index().source();
        let target = self.image.block();
        let mut running = match edit_handles::reserve(&[target], volume.journal().duplicate()) { Some(running) => running, None => { return None; } };
        {
            let (mut part, empty) = match running.borrow_parts(1) { Some(parts) => parts, None => { return None; } };
            let mut handle = match part.handle_at(0) { Some(handle) => handle, None => { return None; } };
            if !handle.stage(self.image.as_slice()) { return None; }
            if !handle.close() { return None; }
            assert(part.part_view() == seq![edit_handles::EditView { target, stage: edit_handles::StageView {
                status: edit_handles::Status::Closed, image: Some(self.image.view()) } }]);
            part.release(); empty.release();
        }
        assert(running.edit_view() == seq![edit_handles::EditView { target, stage: edit_handles::StageView {
            status: edit_handles::Status::Closed, image: Some(self.image.view()) } }]);
        let frozen = match running.freeze() { Ok(frozen) => frozen, Err(_) => { return None; } };
        assert(frozen.frozen_view() == seq![self.image.view()]) by { reveal_with_fuel(edit_handles::selected, 2); }
        writer_admission::prepare(source, frozen)
    }
}

pub fn prepare<'n, 'v, 'a>(grant: Authorization<'n, 'v, 'a>, name: &[u8], data: &[u8], seconds: i64, nanos: u32)
    -> (r: Option<Candidate<'n, 'v, 'a>>)
    ensures grant.wf(), match r { Some(candidate) => candidate.wf() && candidate.view().grant == grant.view()
        && candidate.view().change.data == data@ && candidate.view().change.seconds == seconds as int && candidate.view().change.nanos == nanos as nat
        && crate::xattr_entry::name(candidate.view().change.body.raw, replace::selected(candidate.view().change)) == name@, None => true },
{
    let (node, _, request, Ghost(authorization)) = grant.release();
    if request != 2 || name.len() == 0 || name.len() > 255 { return None; }
    let info = node.info();
    if info.mode & 0xf000 != 0x8000 { return None; }
    let volume = node.volume(); let index = volume.index(); let number = node.number();
    let primary = match index.source().block(0) { Some(primary) => primary, None => { return None; } };
    if feature_policy::is_readonly(primary.range(1024, 1024).unwrap()).unwrap() { return None; }
    let (_, inodes, _, seed) = index.parameters();
    let body = match xattr::parse_body(node.raw(), false, inodes) { Some(body) => body, None => { return None; } };
    proof { the_acl_source_and_a_fresh_body_parse_are_identical(authorization, body.view()); }
    let table = match body.entry_table() { Some(table) => table, None => { return None; } };
    let slot = match table.find(1, name) { Some(slot) => slot, None => { return None; } };
    let huge = index.huge_files();
    let inode = match replace::encode(&body, slot, data, number, inodes, seed, huge, seconds, nanos) { Some(inode) => inode, None => { return None; } };
    let ghost change = Change { body: body.view(), index: slot, data: data@, number, inodes, seed, huge, seconds: seconds as int, nanos: nanos as nat };
    proof { replace::replacement_retains_inode_and_table_validity_and_every_other_attribute(change); }
    let position = inode_table::position(index, number).unwrap();
    if position / 4096 > u32::MAX as u64 || position % 4096 > 3840 { return None; }
    let block = (position / 4096) as u32;
    let original = match index.source().block(block) { Some(original) => original, None => { return None; } };
    let mut metadata = bytes::zero_block();
    if !bytes::write_bytes(metadata.as_mut_slice(), 0, original.as_slice()) { return None; }
    if !bytes::write_bytes(metadata.as_mut_slice(), (position % 4096) as usize, &inode) { return None; }
    let image = AfterImage::capture(block, &metadata).unwrap();
    let ghost view = UpdateView { grant: authorization, change, image: image.view() };
    assert(valid(view)) by { reveal(valid); }
    Some(Candidate { node, image, update: Ghost(view) })
}

pub proof fn every_candidate_has_the_exact_source_write_grant(v: UpdateView)
    requires valid(v),
    ensures acl_access::valid(v.grant), v.grant.request == 2,
        v.change.body.raw == inode_table::raw(v.grant.node.volume.index, v.grant.node.number),
{
    reveal(valid); reveal(acl_access::valid);
}
pub proof fn no_candidate_changes_another_inline_attribute(v: UpdateView, j: int)
    requires valid(v), 0 <= j < v.change.body.table.unwrap().entries.len(), j != v.change.index,
    ensures table::value_view(replace::result(v.change), v.change.body.table.unwrap().entries[j])
        == table::value_view(v.change.body.raw, v.change.body.table.unwrap().entries[j]),
{
    reveal(valid);
    replace::replacement_retains_inode_and_table_validity_and_every_other_attribute(v.change);
}
pub proof fn neighboring_inode_bytes_in_the_same_table_block_are_unchanged(v: UpdateView, i: int)
    requires valid(v), 0 <= i < 4096, !(inode_table::start(v.grant.node.volume.index, v.grant.node.number) % 4096 <= i
        < inode_table::start(v.grant.node.volume.index, v.grant.node.number) % 4096 + 256),
    ensures v.image.image[i] == v.grant.node.volume.index.source[v.image.block as int * 4096 + i],
{
    source_ownership_facts(v);
    reveal(valid);
    allocation::every_inode_table_position_has_a_metadata_role(v.grant.node.volume, v.grant.node.number);
}

pub open spec fn admitted(v: UpdateView, admission: AdmissionView, images: Images) -> bool {
    valid(v) && writer_admission::valid(admission, images) && admission.boot.source == v.grant.node.volume.index.source
        && images.tx.original == seq![v.image] && images.tx.layout == v.grant.node.volume.journal
}
proof fn source_ownership_facts(v: UpdateView)
    requires valid(v),
    ensures allocation::valid(v.grant.node.volume), 0 < v.grant.node.number <= v.grant.node.volume.index.inodes,
        v.grant.node.volume.census.roles.len() == v.grant.node.volume.index.blocks,
        v.grant.node.volume.census.roles[v.image.block as int].kind == 3,
        v.grant.node.volume.journal.fs_blocks == v.grant.node.volume.index.blocks,
        v.grant.node.volume.index.blocks as nat * 4096 <= v.grant.node.volume.index.source.len(),
{
    reveal(valid); reveal(acl_access::valid); reveal(allocated_inode::valid); reveal(allocation::valid);
    reveal(allocation::journal_matches); reveal(crate::group_index::valid);
    allocation::every_inode_table_position_has_a_metadata_role(v.grant.node.volume, v.grant.node.number);
}

pub proof fn admitted_updates_preserve_every_data_directory_extent_and_external_xattr_block(v: UpdateView, admission: AdmissionView, images: Images, block: u32)
    requires admitted(v, admission, images), block < v.grant.node.volume.census.roles.len(), 4 <= v.grant.node.volume.census.roles[block as int].kind <= 7,
    ensures writer_admission::final_source(admission.boot.source, images).subrange(block as int * 4096, (block as int + 1) * 4096)
        == v.grant.node.volume.index.source.subrange(block as int * 4096, (block as int + 1) * 4096),
{
    source_ownership_facts(v);
    let volume = v.grant.node.volume;
    allocation::the_primary_superblock_and_descriptor_have_reserved_roles(volume);
    if volume.journal.start <= block < volume.journal.start as nat + volume.journal.journal_blocks {
        allocation::the_internal_journal_has_only_journal_roles(volume, block); assert(false);
    }
    assert(patch_set::selected(images.tx.original, block as int).is_none());
    crate::writer_image::blocks_outside_the_home_journal_and_primary_targets_retain_their_source_bytes(admission, images, block);
}

pub proof fn an_admitted_update_has_the_exact_replaced_inode_home(v: UpdateView, admission: AdmissionView, images: Images)
    requires admitted(v, admission, images),
    ensures writer_admission::final_source(admission.boot.source, images).subrange(inode_table::start(v.grant.node.volume.index, v.grant.node.number) as int,
        inode_table::start(v.grant.node.volume.index, v.grant.node.number) as int + 256) == replace::result(v.change),
{
    source_ownership_facts(v);
    reveal(valid);
    let volume = v.grant.node.volume;
    let position = inode_table::start(volume.index, v.grant.node.number);
    allocation::every_inode_table_position_has_a_metadata_role(volume, v.grant.node.number);
    if volume.journal.start <= v.image.block < volume.journal.start as nat + volume.journal.journal_blocks {
        allocation::the_internal_journal_has_only_journal_roles(volume, v.image.block); assert(false);
    }
    assert(patch_set::valid(images.tx.original)) by { reveal(writer_admission::valid); }
    patch_set::one_target_has_one_image(images.tx.original, 0);
    crate::writer_image::a_selected_home_outside_the_journal_has_the_exact_final_bytes(admission, images, v.image.block, v.image.image);
    let after = writer_admission::final_source(admission.boot.source, images);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(position as int, 4096);
    vstd::seq::lemma_seq_subrange_composition(after, v.image.block as int * 4096, (v.image.block as int + 1) * 4096,
        position as int % 4096, position as int % 4096 + 256);
    assert(v.image.image.subrange(position as int % 4096, position as int % 4096 + 256) =~= replace::result(v.change));
}

pub proof fn a_successful_journalled_update_has_the_exact_durable_inode(v: UpdateView, admission: AdmissionView, images: Images, machine: crate::write_device::Machine)
    requires admitted(v, admission, images), crate::write_device::inv(machine, images.tx.payloads.len()),
        machine.io.phase is Done, !machine.io.pending, !machine.io.faulted,
    ensures crate::disk_image::flat_bytes(crate::write_media::disk(machine, crate::disk_image::initial_disk(admission.boot.source, images.tx.layout.fs_blocks), images),
        admission.boot.source, images.tx.layout.fs_blocks).subrange(inode_table::start(v.grant.node.volume.index, v.grant.node.number) as int,
            inode_table::start(v.grant.node.volume.index, v.grant.node.number) as int + 256) == replace::result(v.change),
{
    an_admitted_update_has_the_exact_replaced_inode_home(v, admission, images);
    crate::writer_image::successful_durable_writer_is_the_complete_validated_filesystem_image(admission, images, machine);
    reveal(writer_admission::valid);
}

proof fn old_and_updated_inode_slices_are_exact(v: UpdateView, admission: AdmissionView, images: Images)
    requires admitted(v, admission, images),
    ensures crate::disk_image::initial_disk(admission.boot.source, images.tx.layout.fs_blocks).dom().contains(v.image.block),
        crate::disk_image::initial_disk(admission.boot.source, images.tx.layout.fs_blocks)[v.image.block].subrange(
            inode_table::start(v.grant.node.volume.index, v.grant.node.number) as int % 4096,
            inode_table::start(v.grant.node.volume.index, v.grant.node.number) as int % 4096 + 256) == v.change.body.raw,
        v.image.image.subrange(inode_table::start(v.grant.node.volume.index, v.grant.node.number) as int % 4096,
            inode_table::start(v.grant.node.volume.index, v.grant.node.number) as int % 4096 + 256) == replace::result(v.change),
{
    source_ownership_facts(v);
    every_candidate_has_the_exact_source_write_grant(v);
    reveal(valid);
    let position = inode_table::start(v.grant.node.volume.index, v.grant.node.number);
    allocation::every_inode_table_position_has_a_metadata_role(v.grant.node.volume, v.grant.node.number);
    crate::disk_image::initial_block_map_has_the_exact_source_bytes(admission.boot.source, images.tx.layout.fs_blocks, v.image.block);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(position as int, 4096);
    vstd::seq::lemma_seq_subrange_composition(admission.boot.source, v.image.block as int * 4096,
        (v.image.block as int + 1) * 4096, position as int % 4096, position as int % 4096 + 256);
    assert(v.image.image.subrange(position as int % 4096, position as int % 4096 + 256) =~= replace::result(v.change));
}

pub proof fn every_successful_recovery_after_a_writer_cut_has_the_complete_old_or_new_inode(v: UpdateView, admission: AdmissionView,
    images: Images, machine: crate::write_device::Machine, layout: &crate::layout::JournalLayout, scan: &crate::scan::Scan,
    recovery: crate::recovery_device::Machine, tail: Seq<u8>)
    requires admitted(v, admission, images), crate::write_device::inv(machine, images.tx.payloads.len()), layout.wf(), layout.view() == images.tx.layout,
        crate::write_recovery::returned(scan, crate::write_recovery::source(machine,
            crate::disk_image::initial_disk(admission.boot.source, images.tx.layout.fs_blocks), images, layout)),
        crate::recovery_device::inv(recovery, crate::write_media::disk(machine,
            crate::disk_image::initial_disk(admission.boot.source, images.tx.layout.fs_blocks), images), scan.plan(), images.journal_block, tail),
        recovery.io.phase == 4, !recovery.io.faulted, !recovery.io.pending,
    ensures recovery.stable[v.image.block].subrange(inode_table::start(v.grant.node.volume.index, v.grant.node.number) as int % 4096,
        inode_table::start(v.grant.node.volume.index, v.grant.node.number) as int % 4096 + 256)
        == if machine.stable.contains(6 + images.tx.payloads.len()) { replace::result(v.change) } else { v.change.body.raw },
{
    source_ownership_facts(v);
    let before = crate::disk_image::initial_disk(admission.boot.source, images.tx.layout.fs_blocks);
    crate::writer_image::an_admitted_source_supplies_the_physical_writer_context(admission, images);
    old_and_updated_inode_slices_are_exact(v, admission, images);
    let volume = v.grant.node.volume;
    allocation::the_primary_superblock_and_descriptor_have_reserved_roles(volume);
    if volume.journal.start <= v.image.block < volume.journal.start as nat + volume.journal.journal_blocks {
        allocation::the_internal_journal_has_only_journal_roles(volume, v.image.block); assert(false);
    }
    assert(crate::write_recovery::home_block(before, images, v.image.block));
    crate::write_recovery::successful_recovery_of_every_writer_cut_has_before_or_after_home_bytes(machine, before, images, layout, scan, recovery, tail, v.image.block);
    let log = crate::transaction_refinement::log(images.tx);
    assert(log.len() == 1);
    assert(log.drop_last() =~= Seq::<crate::replay::WriteView>::empty());
    assert(crate::replay_refinement::chronological(before, log, Seq::empty())[v.image.block] == v.image.image);
}

}
