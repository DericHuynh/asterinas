// SPDX-License-Identifier: MPL-2.0

//! Source-bound initialized regular-file content replacement, one clipped
//! block at a time. These host candidates do not implement POSIX write/open,
//! timestamps, credential authentication or a CortenMM cache/extent lock.

use vstd::prelude::*;
use crate::{access::{self, Credentials}, allocated_inode::{self, AllocatedInode, NodeView}, bytes,
    edit_handles, file_read::{self, Resolution}, inode_size, transaction::{AfterImage, ImageView},
    writer_admission::{self, CheckedWriter}};

verus! {

pub struct WriteView {
    pub node: NodeView, pub offset: u64, pub data: Seq<u8>, pub image: ImageView, pub credentials: Credentials,
}

#[verifier::opaque]
pub open spec fn valid(v: WriteView) -> bool {
    &&& allocated_inode::valid(v.node) && v.node.mode & 0xf000 == 0x8000 && v.node.mode & 0o6000 == 0
    &&& access::permitted(v.node.mode, v.node.uid, &v.credentials, 2, false)
    &&& 0 < v.data.len() <= 4096 && v.offset < v.node.size && v.offset as nat + v.data.len() <= v.node.size
    &&& v.offset as nat % 4096 + v.data.len() <= 4096
    &&& v.image.image.len() == 4096 && (v.image.block as nat + 1) * 4096 <= v.node.volume.index.source.len()
    &&& file_read::maps(v.node, (v.offset / 4096) as u32, v.image.block)
    &&& file_read::owned(v.node, (v.offset / 4096) as u32, v.image.block)
    &&& v.image.image == bytes::splice(v.node.volume.index.source.subrange(v.image.block as int * 4096,
        (v.image.block as int + 1) * 4096), v.offset as int % 4096, v.data)
}

pub struct Candidate<'n, 'v, 'a> {
    node: &'n AllocatedInode<'v, 'a>, image: AfterImage, offset: u64, length: usize,
    data: Ghost<Seq<u8>>, credentials: Ghost<Credentials>,
}

impl<'n, 'v, 'a> Candidate<'n, 'v, 'a> {
    pub closed spec fn view(&self) -> WriteView {
        WriteView { node: self.node.view(), offset: self.offset, data: self.data@, image: self.image.view(), credentials: self.credentials@ }
    }
    pub closed spec fn wf(&self) -> bool { valid(self.view()) && self.length == self.data@.len() }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn written_prefix(&self) -> (r: usize) ensures self.wf(), r == self.view().data.len(), 0 < r <= 4096 {
        proof { use_type_invariant(self); reveal(valid); }
        self.length
    }

    pub fn after_image(&self) -> (r: &AfterImage) ensures self.wf(), r.view() == self.view().image {
        proof { use_type_invariant(self); }
        &self.image
    }

    pub fn begin(self) -> (r: Option<CheckedWriter<'v, 'a>>)
        ensures self.wf(), match r {
            Some(writer) => writer.wf() && writer.view().boot.source == self.view().node.volume.index.source
                && writer.owner().images().tx.original == seq![self.view().image],
            None => true,
        },
    {
        proof { use_type_invariant(&self); }
        let volume = self.node.volume();
        let source = volume.index().source();
        let target = self.image.block();
        let mut running = match edit_handles::reserve(&[target], volume.journal().duplicate()) {
            Some(running) => running, None => { return None; }
        };
        {
            let (mut part, empty) = match running.borrow_parts(1) { Some(parts) => parts, None => { return None; } };
            let mut handle = match part.handle_at(0) { Some(handle) => handle, None => { return None; } };
            if !handle.stage(self.image.as_slice()) { return None; }
            assert(handle.handle_view().stage.image == Some(self.image.view()));
            if !handle.close() { return None; }
            assert(part.part_view() == seq![edit_handles::EditView { target, stage: edit_handles::StageView {
                status: edit_handles::Status::Closed, image: Some(self.image.view()) } }]);
            part.release();
            empty.release();
        }
        assert(running.edit_view() == seq![edit_handles::EditView { target, stage: edit_handles::StageView {
            status: edit_handles::Status::Closed, image: Some(self.image.view()) } }]);
        let frozen = match running.freeze() { Ok(frozen) => frozen, Err(_) => { return None; } };
        assert(frozen.frozen_view() == seq![self.image.view()]) by { reveal_with_fuel(edit_handles::selected, 2); }
        writer_admission::prepare(source, frozen)
    }
}

pub fn prepare_chunk<'n, 'v, 'a>(node: &'n AllocatedInode<'v, 'a>, offset: u64, input: &[u8], credentials: &Credentials)
    -> (r: Option<Candidate<'n, 'v, 'a>>)
    ensures node.wf(), match r {
        Some(candidate) => candidate.wf() && candidate.view().node == node.view() && candidate.view().offset == offset
            && candidate.view().credentials == *credentials
            && candidate.view().data == input@.take(file_read::chunk_length(node.view(), offset, input.len()) as int)
            && candidate.view().data.len() == file_read::chunk_length(node.view(), offset, input.len()),
        None => true,
    },
{
    hide(file_read::maps);
    hide(file_read::owned);
    let info = node.info();
    if info.mode & 0xf000 != 0x8000 || info.mode & 0o6000 != 0
        || !access::allowed(info.mode, info.uid, credentials, 2, false)
        || input.len() == 0 || offset >= info.size { return None; }
    let huge = node.volume().index().huge_files();
    proof { inode_size::offsets_never_truncate_to_a_different_logical_block(4096, huge, info.size, offset); }
    let logical = (offset / 4096) as u32;
    let within = (offset % 4096) as usize;
    let remaining = info.size - offset;
    let mut length = 4096usize - within;
    if remaining < length as u64 { length = remaining as usize; }
    if input.len() < length { length = input.len(); }
    let physical = match file_read::resolve(node, logical) { Resolution::Data(block) => block, Resolution::Zero => { return None; } };
    let source = node.volume().index().source();
    let original = match source.block(physical) { Some(block) => block, None => { return None; } };
    let mut data = bytes::zero_block();
    if !bytes::write_bytes(data.as_mut_slice(), 0, original.as_slice()) { return None; }
    assert(data.len() == 4096);
    if !bytes::write_bytes(data.as_mut_slice(), within, &input[..length]) { return None; }
    assert(data.len() == 4096);
    let image = AfterImage::capture(physical, &data).unwrap();
    let ghost view = WriteView { node: node.view(), offset, data: input@.take(length as int), image: image.view(), credentials: *credentials };
    assert(valid(view)) by { reveal(valid); }
    Some(Candidate { node, image, offset, length, data: Ghost(input@.take(length as int)), credentials: Ghost(*credentials) })
}

pub proof fn an_initialized_content_write_cannot_touch_another_inode(v: WriteView)
    requires valid(v),
    ensures v.node.volume.census.roles[v.image.block as int].inode == v.node.number,
        v.node.volume.census.roles[v.image.block as int].generation == v.node.generation,
        v.node.volume.census.roles[v.image.block as int].kind == 4,
{
    hide(file_read::maps);
    reveal(valid);
}

pub proof fn bytes_outside_the_requested_content_span_are_preserved(v: WriteView, within: int)
    requires valid(v), 0 <= within < 4096,
        within < v.offset as int % 4096 || v.offset as int % 4096 + v.data.len() <= within,
    ensures v.image.image[within] == v.node.volume.index.source[v.image.block as int * 4096 + within],
{
    hide(file_read::maps);
    hide(file_read::owned);
    reveal(valid);
    let base = v.node.volume.index.source.subrange(v.image.block as int * 4096, (v.image.block as int + 1) * 4096);
    assert(base.len() == 4096);
    assert(bytes::splice(base, v.offset as int % 4096, v.data)[within] == base[within]);
}

pub proof fn replacement_bytes_equal_the_exact_requested_prefix(v: WriteView, within: int)
    requires valid(v), v.offset as int % 4096 <= within < v.offset as int % 4096 + v.data.len(),
    ensures v.image.image[within] == v.data[within - v.offset as int % 4096],
{
    hide(file_read::maps);
    hide(file_read::owned);
    reveal(valid);
}

pub proof fn every_replaced_byte_stays_in_the_same_logical_block(v: WriteView, index: int)
    requires valid(v), 0 <= index < v.data.len(),
    ensures (v.offset as int + index) / 4096 == v.offset / 4096,
        v.offset as int + index < v.node.size,
        v.image.image[(v.offset as int + index) % 4096] == v.data[index],
{
    hide(file_read::maps);
    hide(file_read::owned);
    reveal(valid);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(v.offset as int, 4096);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(v.offset as int + index, 4096,
        v.offset as int / 4096, v.offset as int % 4096 + index);
    replacement_bytes_equal_the_exact_requested_prefix(v, v.offset as int % 4096 + index);
}

pub proof fn candidates_for_distinct_physical_blocks_commute(left: WriteView, right: WriteView)
    requires valid(left), valid(right), left.node.volume.index.source == right.node.volume.index.source,
        left.image.block != right.image.block,
    ensures crate::patch_set::apply(crate::patch_set::apply(left.node.volume.index.source, seq![left.image]), seq![right.image])
        == crate::patch_set::apply(crate::patch_set::apply(left.node.volume.index.source, seq![right.image]), seq![left.image]),
{
    assert(crate::patch_set::apply(crate::patch_set::apply(left.node.volume.index.source, seq![left.image]), seq![right.image])
        =~= crate::patch_set::apply(crate::patch_set::apply(left.node.volume.index.source, seq![right.image]), seq![left.image]));
}

}
