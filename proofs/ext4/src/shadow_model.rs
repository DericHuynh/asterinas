// SPDX-License-Identifier: MPL-2.0

//! Byte semantics of bounded shadow layers. Later layers override earlier ones;
//! no checksum identity, storage authority or physical persistence is assumed.

use vstd::prelude::*;
use crate::{patch_set, transaction::ImageView};

verus! {

pub open spec fn selected(layers: Seq<Seq<ImageView>>, block: int) -> Option<Seq<u8>>
    decreases layers.len(),
{
    if layers.len() == 0 { None }
    else { match patch_set::selected(layers.last(), block) {
        Some(image) => Some(image), None => selected(layers.drop_last(), block),
    } }
}

pub open spec fn apply(base: Seq<u8>, layers: Seq<Seq<ImageView>>) -> Seq<u8> {
    Seq::new(base.len(), |i: int| match selected(layers, i / 4096) {
        Some(image) => image[i % 4096], None => base[i],
    })
}

pub proof fn layering_matches_patch_application(base: Seq<u8>, layers: Seq<Seq<ImageView>>, patch: Seq<ImageView>)
    ensures apply(base, layers.push(patch)) == patch_set::apply(apply(base, layers), patch),
{
    assert(layers.push(patch).drop_last() == layers);
    assert(apply(base, layers.push(patch)) =~= patch_set::apply(apply(base, layers), patch));
}

proof fn selected_image_has_size(layers: Seq<Seq<ImageView>>, block: int)
    requires forall|i: int| 0 <= i < layers.len() ==> patch_set::valid(#[trigger] layers[i]),
    ensures selected(layers, block).is_some() ==> selected(layers, block).unwrap().len() == 4096,
    decreases layers.len(),
{
    if layers.len() == 0 { return; }
    if let Some(image) = patch_set::selected(layers.last(), block) {
        let i = choose|i: int| 0 <= i < layers.last().len() && (#[trigger] layers.last()[i]).block as int == block;
        patch_set::one_target_has_one_image(layers.last(), i);
        reveal(patch_set::valid);
        assert(image == layers.last()[i].image);
    } else {
        assert forall|i: int| 0 <= i < layers.drop_last().len() implies patch_set::valid(#[trigger] layers.drop_last()[i]) by {
            assert(layers.drop_last()[i] == layers[i]);
        }
        selected_image_has_size(layers.drop_last(), block);
    }
}

pub proof fn a_block_has_exact_selected_bytes(base: Seq<u8>, layers: Seq<Seq<ImageView>>, block: u32)
    requires (block as nat + 1) * 4096 <= base.len(),
        forall|i: int| 0 <= i < layers.len() ==> patch_set::valid(#[trigger] layers[i]),
    ensures match selected(layers, block as int) {
        Some(image) => apply(base, layers).subrange(block as int * 4096, (block as int + 1) * 4096) == image,
        None => apply(base, layers).subrange(block as int * 4096, (block as int + 1) * 4096)
            == base.subrange(block as int * 4096, (block as int + 1) * 4096),
    },
{
    selected_image_has_size(layers, block as int);
    let start = block as int * 4096;
    if let Some(image) = selected(layers, block as int) {
        assert(apply(base, layers).subrange(start, start + 4096) =~= image) by {
            assert forall|j: int| 0 <= j < 4096 implies #[trigger] apply(base, layers)[start + j] == image[j] by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(start + j, 4096, block as int, j);
            }
        }
    } else {
        assert(apply(base, layers).subrange(start, start + 4096) =~= base.subrange(start, start + 4096)) by {
            assert forall|j: int| 0 <= j < 4096 implies #[trigger] apply(base, layers)[start + j] == base[start + j] by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(start + j, 4096, block as int, j);
            }
        }
    }
}

}
