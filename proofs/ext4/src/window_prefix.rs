// SPDX-License-Identifier: MPL-2.0

//! Exact immutable cumulative home patches. Overwrite the latest owned image
//! instead of consuming a shadow layer per transaction in a 64-version window.

use vstd::prelude::*;
use crate::{journal_queue::FrozenVersion, journal_window::WindowView, patch_set::{self, PatchSet}, transaction::ImageView};

verus! {

pub open spec fn overlay(source: Seq<u8>, images: Seq<ImageView>) -> Seq<u8>
    decreases images.len(),
{
    if images.len() == 0 { source }
    else { patch_set::apply(overlay(source, images.drop_last()), seq![images.last()]) }
}

pub open spec fn marked(source: Seq<u8>, v: WindowView) -> Seq<u8> {
    patch_set::apply(source, seq![ImageView { block: 0, image: v.dirty }])
}

pub open spec fn prefix(source: Seq<u8>, v: WindowView, count: nat) -> Seq<u8>
    decreases count,
{
    if count == 0 { marked(source, v) }
    else { overlay(prefix(source, v, (count - 1) as nat), v.txs[count as int - 1].tx.original) }
}

pub proof fn cumulative_prefixes_keep_the_exact_partition_length(source: Seq<u8>, v: WindowView, count: nat)
    ensures prefix(source, v, count).len() == source.len(),
    decreases count,
{
    if count > 0 { cumulative_prefixes_keep_the_exact_partition_length(source, v, (count - 1) as nat); overlay_length(prefix(source, v, (count - 1) as nat), v.txs[count as int - 1].tx.original); }
}

proof fn overlay_length(source: Seq<u8>, images: Seq<ImageView>)
    ensures overlay(source, images).len() == source.len(),
    decreases images.len(),
{
    if images.len() > 0 { overlay_length(source, images.drop_last()); }
}

pub(crate) proof fn overlay_push(source: Seq<u8>, images: Seq<ImageView>, image: ImageView)
    ensures overlay(source, images.push(image)) == patch_set::apply(overlay(source, images), seq![image]),
{ assert(images.push(image).drop_last() =~= images); }

pub open spec fn upserted(before: Seq<ImageView>, after: Seq<ImageView>, block: u32, image: Seq<u8>) -> bool {
    (exists|i: int| 0 <= i < before.len() && before[i].block == block && after == before.update(i, ImageView { block, image }))
        || (exists|i: int| 0 <= i <= before.len() && after == before.insert(i, ImageView { block, image }))
}

proof fn updated_selection(before: Seq<ImageView>, after: Seq<ImageView>, block: u32, image: Seq<u8>, target: int)
    requires patch_set::valid(before), patch_set::valid(after), upserted(before, after, block, image),
    ensures patch_set::selected(after, target) == if target == block as int { Some(image) } else { patch_set::selected(before, target) },
{
    reveal(patch_set::valid);
    if exists|i: int| 0 <= i < before.len() && before[i].block == block && after == before.update(i, ImageView { block, image }) {
        let p = choose|i: int| 0 <= i < before.len() && before[i].block == block && after == before.update(i, ImageView { block, image });
        if target == block as int { patch_set::one_target_has_one_image(after, p); }
        else if let Some(old) = patch_set::selected(before, target) {
            let i = choose|i: int| 0 <= i < before.len() && (#[trigger] before[i]).block as int == target;
            assert(i != p);
            patch_set::one_target_has_one_image(before, i);
            patch_set::one_target_has_one_image(after, i);
        } else {
            assert forall|i: int| 0 <= i < after.len() implies (#[trigger] after[i]).block as int != target by {
                if i != p { assert(before[i].block as int != target); }
            }
        }
    } else {
        let p = choose|i: int| 0 <= i <= before.len() && after == before.insert(i, ImageView { block, image });
        if target == block as int { patch_set::one_target_has_one_image(after, p); }
        else if let Some(old) = patch_set::selected(before, target) {
            let i = choose|i: int| 0 <= i < before.len() && (#[trigger] before[i]).block as int == target;
            patch_set::one_target_has_one_image(before, i);
            let j = if i < p { i } else { i + 1 };
            patch_set::one_target_has_one_image(after, j);
        } else {
            assert forall|i: int| 0 <= i < after.len() implies (#[trigger] after[i]).block as int != target by {
                if i < p { assert(before[i].block as int != target); }
                else if i > p { assert(before[i - 1].block as int != target); }
            }
        }
    }
}

pub proof fn upserting_an_owned_image_is_exactly_one_shadow_block_update(source: Seq<u8>, before: Seq<ImageView>, after: Seq<ImageView>, block: u32, image: Seq<u8>)
    requires patch_set::valid(before), patch_set::valid(after), upserted(before, after, block, image),
    ensures patch_set::apply(source, after) == patch_set::apply(patch_set::apply(source, before), seq![ImageView { block, image }]),
{
    let next = patch_set::apply(source, after);
    let expected = patch_set::apply(patch_set::apply(source, before), seq![ImageView { block, image }]);
    assert(next =~= expected) by {
        assert forall|i: int| 0 <= i < source.len() implies #[trigger] next[i] == expected[i] by {
            updated_selection(before, after, block, image, i / 4096);
            patch_set::a_single_patch_selects_exactly_its_target(ImageView { block, image }, i / 4096);
        }
    }
}

pub(crate) fn append_version(homes: PatchSet, version: &FrozenVersion, Ghost(base): Ghost<Seq<u8>>) -> (r: Option<PatchSet>)
    ensures match r { Some(next) => next.wf() && patch_set::apply(base, next.view())
        == overlay(patch_set::apply(base, homes.view()), version.view().images), None => true },
{
    let _ = homes.len();
    let ghost start = patch_set::apply(base, homes.view());
    let count = version.image_count();
    let mut current = homes;
    let mut index = 0usize;
    while index < count
        invariant index <= count == version.view().images.len(), current.wf(),
            patch_set::apply(base, current.view()) == overlay(start, version.view().images.take(index as int)),
        decreases count - index,
    {
        let (block, bytes) = version.image_at(index).unwrap();
        let ghost old = current.view();
        current = match current.upsert(block, bytes) { Ok(current) => current, Err(_) => { return None; } };
        proof {
            upserting_an_owned_image_is_exactly_one_shadow_block_update(base, old, current.view(), block, bytes@);
            assert(version.view().images.take(index as int + 1) =~= version.view().images.take(index as int).push(version.view().images[index as int]));
            overlay_push(start, version.view().images.take(index as int), version.view().images[index as int]);
        }
        index += 1;
    }
    assert(version.view().images.take(count as int) =~= version.view().images);
    Some(current)
}

proof fn one_block_overlay(base: Seq<u8>, image: ImageView, target: u32)
    requires image.image.len() == 4096, (target as nat + 1) * 4096 <= base.len(),
    ensures patch_set::apply(base, seq![image]).subrange(target as int * 4096, (target as int + 1) * 4096)
        == if image.block == target { image.image } else { base.subrange(target as int * 4096, (target as int + 1) * 4096) },
{
    assert(patch_set::valid(seq![image])) by { reveal(patch_set::valid); }
    patch_set::a_single_patch_selects_exactly_its_target(image, target as int);
    patch_set::applying_a_patch_replaces_exactly_its_block(base, seq![image], target);
}

proof fn overlay_member(base: Seq<u8>, images: Seq<ImageView>, index: int)
    requires 0 <= index < images.len(), crate::transaction::distinct(images),
        forall|i: int| 0 <= i < images.len() ==> (#[trigger] images[i]).image.len() == 4096,
        (images[index].block as nat + 1) * 4096 <= base.len(),
    ensures overlay(base, images).subrange(images[index].block as int * 4096, (images[index].block as int + 1) * 4096) == images[index].image,
    decreases images.len(),
{
    let target = images[index].block;
    overlay_length(base, images.drop_last());
    one_block_overlay(overlay(base, images.drop_last()), images.last(), target);
    if index < images.len() - 1 {
        assert(crate::transaction::distinct(images.drop_last()));
        overlay_member(base, images.drop_last(), index);
        assert(images[index].block != images[images.len() as int - 1].block);
    }
}

#[verifier::rlimit(30)]
pub proof fn a_checkpoint_home_image_is_exactly_its_complete_prefix_block(source: Seq<u8>, v: WindowView, t: int, k: int)
    requires crate::journal_window::valid(v), source.len() == v.partition_bytes,
        0 <= t < v.txs.len(), 0 <= k < v.txs[t].tx.original.len(),
    ensures prefix(source, v, (t + 1) as nat).subrange(v.txs[t].tx.original[k].block as int * 4096,
        (v.txs[t].tx.original[k].block as int + 1) * 4096) == v.txs[t].tx.original[k].image,
{
    hide(crate::crc::fold);
    crate::journal_window::a_window_retains_its_geometry_and_bounded_counts(v);
    crate::journal_window::window_entry(v, t);
    reveal(crate::journal_window::positioned_valid);
    let tx = v.txs[t].tx;
    assert forall|i: int| 0 <= i < tx.original.len() implies (#[trigger] tx.original[i]).image.len() == 4096 by {
        assert(crate::replay::payload_for_layout(tx.tags[i], tx.payloads[i], tx.sequence, tx.seed, tx.layout));
    }
    assert(crate::replay::payload_for_layout(tx.tags[k], tx.payloads[k], tx.sequence, tx.seed, tx.layout));
    assert(tx.original[k].block == tx.tags[k].block && tx.original[k].block < v.layout.fs_blocks);
    assert((tx.original[k].block as nat + 1) * 4096 <= source.len());
    cumulative_prefixes_keep_the_exact_partition_length(source, v, t as nat);
    overlay_member(prefix(source, v, t as nat), tx.original, k);
}

}
