// SPDX-License-Identifier: MPL-2.0

//! Freeze the complete sorted xattr patch set through disjoint journal edits.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, edit_handles::{self as edit, EditView, FrozenBatch, Status}, layout::JournalLayout,
    patch_set::PatchSet, transaction::ImageView};

verus! {

proof fn selected_all(edits: Seq<EditView>, images: Seq<ImageView>)
    requires edits.len() == images.len(), forall|i: int| 0 <= i < edits.len() ==> (#[trigger] edits[i]).stage.image == Some(images[i]),
    ensures edit::selected(edits) == images,
    decreases edits.len(),
{
    reveal(edit::selected);
    if edits.len() > 0 {
        selected_all(edits.drop_last(), images.drop_last());
        assert(images.drop_last() + seq![images.last()] =~= images);
    }
}
pub fn freeze(patches: &PatchSet, layout: JournalLayout) -> (r: Option<FrozenBatch>)
    ensures patches.wf(), match r { Some(batch) => batch.wf() && batch.frozen_view() == patches.view() && batch.frozen_layout() == layout.view(), None => true },
{
    let n = patches.len(); if n == 0 || n > edit::MAX_CREDITS { return None; }
    let mut keys = Vec::new(); let mut i = 0usize;
    while i < n
        invariant patches.wf(), n == patches.view().len(), n <= edit::MAX_CREDITS, i <= n, keys.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] keys@[j] == patches.view()[j].block,
        decreases n - i,
    { keys.push(patches.at(i).unwrap().block()); i += 1; }
    let mut running = match edit::reserve(&keys, layout) { Some(running) => running, None => { return None; } };
    let ghost wanted_layout = running.layout_view();
    {
        let (empty, mut part) = match running.borrow_parts(0) { Some(parts) => parts, None => { return None; } };
        let mut i = 0usize;
        while i < n
            invariant patches.wf(), n == patches.view().len(), n <= edit::MAX_CREDITS, i <= n, part.wf(), part.part_view().len() == n,
                forall|j: int| 0 <= j < n ==> (#[trigger] part.part_view()[j]).target == patches.view()[j].block
                    && (if j < i { part.part_view()[j].stage.status == Status::Closed && part.part_view()[j].stage.image == Some(patches.view()[j]) }
                        else { part.part_view()[j].stage.status == Status::Unused }),
            decreases n - i,
        {
            let image = patches.at(i).unwrap();
            let mut handle = match part.handle_at(i) { Some(handle) => handle, None => { return None; } };
            if !handle.stage(image.as_slice()) || !handle.close() { return None; }
            i += 1;
        }
        part.release(); empty.release();
    }
    let ghost edits = running.edit_view();
    let batch = match running.freeze() { Ok(batch) => batch, Err(_) => { return None; } };
    if batch.frozen_count() != n { return None; }
    let mut i = 0usize;
    while i < n
        invariant patches.wf(), batch.wf(), n == patches.view().len(), n == batch.frozen_view().len(), i <= n,
            forall|j: int| 0 <= j < i ==> #[trigger] batch.frozen_view()[j] == patches.view()[j],
        decreases n - i,
    {
        let (target, data) = batch.image_at(i).unwrap(); let expected = patches.at(i).unwrap();
        if target != expected.block() || !bytes::equal(data, expected.as_slice()) { return None; }
        i += 1;
    }
    assert(batch.frozen_view() =~= patches.view());
    Some(batch)
}

pub proof fn every_frozen_xattr_image_retains_its_target_and_complete_bytes(edits: Seq<EditView>, images: Seq<ImageView>)
    requires edits.len() == images.len(), forall|i: int| 0 <= i < edits.len() ==> (#[trigger] edits[i]).stage.image == Some(images[i]),
    ensures edit::selected(edits) == images,
{ selected_all(edits, images); }

}
