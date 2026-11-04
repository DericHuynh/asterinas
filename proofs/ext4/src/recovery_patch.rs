// SPDX-License-Identifier: MPL-2.0

//! Owns exactly the replay plan's selected home images as a sorted shadow
//! patch. Ordering changes, but target identities and bytes do not. The plan's
//! checked revoke/latest selection remains the source of truth.

use vstd::prelude::*;
use crate::{patch_set::{self, PatchSet}, replay::{self, ReplayPlan}, transaction::ImageView};

verus! {

pub open spec fn image(plan: &ReplayPlan, ordinal: int) -> ImageView {
    let write = plan.log()[plan.selection()[ordinal] as int];
    ImageView { block: write.block, image: write.image }
}

#[verifier::opaque]
pub open spec fn matches_prefix(plan: &ReplayPlan, images: Seq<ImageView>, count: nat) -> bool {
    &&& count <= plan.selection().len() && images.len() == count
    &&& (forall|i: int| 0 <= i < images.len() ==> exists|p: int| 0 <= p < count && (#[trigger] images[i]) == image(plan, p))
    &&& (forall|p: int| 0 <= p < count ==> images.contains(#[trigger] image(plan, p)))
}

proof fn next_target_is_absent(plan: &ReplayPlan, images: Seq<ImageView>, count: nat)
    requires plan.refines(), matches_prefix(plan, images, count), count < plan.selection().len(),
    ensures forall|i: int| 0 <= i < images.len() ==> (#[trigger] images[i]).block != image(plan, count as int).block,
{
    reveal(matches_prefix);
    assert forall|i: int| 0 <= i < images.len() implies (#[trigger] images[i]).block != image(plan, count as int).block by {
        let p = choose|p: int| 0 <= p < count && images[i] == image(plan, p);
        assert(replay::unique_targets(plan.log(), plan.selection()));
        assert(plan.log()[plan.selection()[p] as int].block != plan.log()[plan.selection()[count as int] as int].block);
    }
}

proof fn inserted_image_extends_prefix(plan: &ReplayPlan, before: Seq<ImageView>, count: nat, position: int)
    requires matches_prefix(plan, before, count), count < plan.selection().len(), 0 <= position <= before.len(),
    ensures matches_prefix(plan, before.insert(position, image(plan, count as int)), count + 1),
{
    reveal(matches_prefix);
    let result = before.insert(position, image(plan, count as int));
    assert forall|i: int| 0 <= i < result.len() implies exists|p: int| 0 <= p < count + 1 && (#[trigger] result[i]) == image(plan, p) by {
        if i == position { assert(result[i] == image(plan, count as int)); }
        else {
            let old = if i < position { i } else { i - 1 };
            assert(result[i] == before[old]);
            let p = choose|p: int| 0 <= p < count && before[old] == image(plan, p);
            assert(result[i] == image(plan, p));
        }
    }
    assert forall|p: int| 0 <= p < count + 1 implies result.contains(#[trigger] image(plan, p)) by {
        if p == count as int { assert(result[position] == image(plan, p)); }
        else {
            let old = choose|i: int| 0 <= i < before.len() && before[i] == image(plan, p);
            let next = if old < position { old } else { old + 1 };
            assert(result[next] == image(plan, p));
        }
    }
}

pub fn collect(plan: &ReplayPlan) -> (r: PatchSet)
    ensures r.wf(), matches_prefix(plan, r.view(), plan.selection().len()),
{
    let _ = plan.len();
    let mut patches = PatchSet::new();
    let mut count = 0usize;
    assert(matches_prefix(plan, patches.view(), 0)) by { reveal(matches_prefix); }
    while count < plan.len()
        invariant plan.refines(), count <= plan.selection().len() <= 4096,
            patches.wf(), matches_prefix(plan, patches.view(), count as nat),
        decreases plan.selection().len() - count,
    {
        assert(replay::latest(plan.log(), plan.revocations(), plan.selection()[count as int] as int));
        let write = plan.get(count).unwrap();
        let block = write.block();
        let bytes = write.image();
        assert(bytes.len() == 4096);
        assert(patches.view().len() == count) by { reveal(matches_prefix); }
        proof { next_target_is_absent(plan, patches.view(), count as nat); }
        let ghost before = patches.view();
        let ghost next_image = image(plan, count as int);
        patches = match patches.insert(block, bytes) {
            Ok(next) => next,
            Err(original) => { assert(false); return original; },
        };
        proof {
            let position = choose|position: int| 0 <= position <= before.len() && patches.view() == before.insert(position, next_image);
            inserted_image_extends_prefix(plan, before, count as nat, position);
        }
        count += 1;
    }
    patches
}

pub proof fn each_selected_image_is_the_exact_shadow_patch(plan: &ReplayPlan, images: Seq<ImageView>, ordinal: int)
    requires plan.refines(), patch_set::valid(images), matches_prefix(plan, images, plan.selection().len()),
        0 <= ordinal < plan.selection().len(),
    ensures patch_set::selected(images, image(plan, ordinal).block as int) == Some(image(plan, ordinal).image),
{
    reveal(matches_prefix);
    let i = choose|i: int| 0 <= i < images.len() && images[i] == image(plan, ordinal);
    patch_set::one_target_has_one_image(images, i);
}

pub proof fn unselected_targets_have_no_shadow_patch(plan: &ReplayPlan, images: Seq<ImageView>, block: u32)
    requires matches_prefix(plan, images, plan.selection().len()),
        forall|p: int| 0 <= p < plan.selection().len() ==> (#[trigger] image(plan, p)).block != block,
    ensures patch_set::selected(images, block as int).is_none(),
{
    reveal(matches_prefix);
    if exists|i: int| 0 <= i < images.len() && (#[trigger] images[i]).block == block {
        let i = choose|i: int| 0 <= i < images.len() && (#[trigger] images[i]).block == block;
        let p = choose|p: int| 0 <= p < plan.selection().len() && images[i] == image(plan, p);
        assert(image(plan, p).block != block);
    }
}

}
