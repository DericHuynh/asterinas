// SPDX-License-Identifier: MPL-2.0

//! Borrowed immutable input for host volume validation. Block identity is bound
//! to its exact byte range, independently of checksums. A kernel adapter must
//! refine the frozen CortenMM/OSTD source and partition identity before use.

use vstd::prelude::*;
use crate::{patch_set::{self, PatchSet}, shadow_model};

verus! {

pub const MAX_SHADOW_LAYERS: usize = 32;

pub struct Snapshot<'a> { bytes: &'a [u8], layers: Vec<&'a PatchSet> }
pub struct Block<'a> { bytes: &'a [u8], index: u32, source: Ghost<Seq<u8>> }

pub open spec fn layer_views(layers: Seq<&PatchSet>) -> Seq<Seq<crate::transaction::ImageView>> {
    Seq::new(layers.len(), |i: int| layers[i].view())
}

impl<'a> Block<'a> {
    pub closed spec fn bytes(&self) -> Seq<u8> { self.bytes@ }
    pub closed spec fn index(&self) -> u32 { self.index }
    pub closed spec fn source(&self) -> Seq<u8> { self.source@ }

    pub open spec fn wf(&self) -> bool {
        &&& self.bytes().len() == 4096
        &&& (self.index() as nat + 1) * 4096 <= self.source().len()
        &&& self.bytes() == self.source().subrange(self.index() as int * 4096, (self.index() as int + 1) * 4096)
    }

    #[verifier::type_invariant]
    spec fn valid(self) -> bool { self.wf() }

    pub fn as_slice(&self) -> (r: &'a [u8]) ensures self.wf(), r@ == self.bytes() {
        proof { use_type_invariant(self); }
        self.bytes
    }

    pub fn range(&self, start: usize, length: usize) -> (r: Option<&'a [u8]>)
        ensures self.wf(), match r {
            Some(bytes) => start as nat + length <= 4096 && bytes.len() == length
                && bytes@ == self.source().subrange(self.index() as int * 4096 + start,
                    self.index() as int * 4096 + start + length),
            None => start as nat + length > 4096,
        },
    {
        proof { use_type_invariant(self); }
        if start > 4096 || length > 4096 - start { return None; }
        let bytes = &self.bytes[start..start + length];
        proof {
            vstd::seq::lemma_seq_subrange_composition(self.source(), self.index() as int * 4096,
                (self.index() as int + 1) * 4096, start as int, (start + length) as int);
        }
        Some(bytes)
    }
}

impl<'a> Snapshot<'a> {
    pub closed spec fn view(&self) -> Seq<u8> { shadow_model::apply(self.bytes@, layer_views(self.layers@)) }
    pub closed spec fn depth(&self) -> nat { self.layers.len() as nat }

    pub closed spec fn wf(&self) -> bool {
        &&& self.layers.len() <= MAX_SHADOW_LAYERS
        &&& forall|i: int| 0 <= i < self.layers.len() ==> (#[trigger] self.layers@[i]).wf()
            && (forall|j: int| 0 <= j < self.layers@[i].view().len() ==>
                ((#[trigger] self.layers@[i].view()[j]).block as nat + 1) * 4096 <= self.bytes.len())
    }

    #[verifier::type_invariant]
    spec fn valid(self) -> bool { self.wf() }

    pub fn from_bytes(bytes: &'a [u8]) -> (r: Self) ensures r.view() == bytes@ {
        let layers = Vec::new();
        assert(layer_views(layers@) =~= Seq::empty());
        assert(shadow_model::apply(bytes@, layer_views(layers@)) =~= bytes@);
        Snapshot { bytes, layers }
    }

    pub fn partition_bytes(&self) -> (r: u64) ensures r as nat == self.view().len() { self.bytes.len() as u64 }

    pub fn shadow_depth(&self) -> (r: usize) ensures self.wf(), r == self.depth(), r <= MAX_SHADOW_LAYERS {
        proof { use_type_invariant(self); }
        self.layers.len()
    }

    pub fn overlay(&self, patches: &'a PatchSet) -> (r: Option<Self>)
        ensures match r {
            Some(next) => next.wf() && next.depth() == self.depth() + 1
                && next.view() == patch_set::apply(self.view(), patches.view()),
            None => self.depth() == MAX_SHADOW_LAYERS
                || exists|i: int| 0 <= i < patches.view().len()
                    && ((#[trigger] patches.view()[i]).block as nat + 1) * 4096 > self.view().len(),
        },
    {
        proof { use_type_invariant(self); }
        if self.layers.len() == MAX_SHADOW_LAYERS { return None; }
        let mut i = 0usize;
        while i < patches.len()
            invariant i <= patches.view().len(),
                forall|j: int| 0 <= j < i ==> ((#[trigger] patches.view()[j]).block as nat + 1) * 4096 <= self.bytes.len(),
            decreases patches.view().len() - i,
        {
            let patch = patches.at(i).unwrap();
            if (patch.block() as u64 + 1) * 4096 > self.bytes.len() as u64 { return None; }
            i += 1;
        }
        let mut layers = Vec::new();
        let mut j = 0usize;
        while j < self.layers.len()
            invariant j <= self.layers.len() < MAX_SHADOW_LAYERS,
                layers@ == self.layers@.subrange(0, j as int),
            decreases self.layers.len() - j,
        {
            layers.push(self.layers[j]);
            j += 1;
        }
        layers.push(patches);
        assert(layer_views(layers@) =~= layer_views(self.layers@).push(patches.view()));
        proof { shadow_model::layering_matches_patch_application(self.bytes@, layer_views(self.layers@), patches.view()); }
        Some(Snapshot { bytes: self.bytes, layers })
    }

    pub fn block(&self, index: u32) -> (r: Option<Block<'a>>)
        ensures match r {
            Some(block) => block.wf() && block.source() == self.view() && block.index() == index,
            None => (index as nat + 1) * 4096 > self.view().len(),
        },
    {
        proof { use_type_invariant(self); }
        let start = index as u64 * 4096;
        if start + 4096 > self.bytes.len() as u64 { return None; }
        proof {
            assert forall|i: int| 0 <= i < self.layers.len() implies patch_set::valid(#[trigger] layer_views(self.layers@)[i]) by {
                assert(self.layers@[i].wf());
            }
            shadow_model::a_block_has_exact_selected_bytes(self.bytes@, layer_views(self.layers@), index);
        }
        let mut cursor = self.layers.len();
        assert(layer_views(self.layers@).subrange(0, cursor as int) == layer_views(self.layers@));
        while cursor > 0
            invariant self.wf(), cursor <= self.layers.len() <= MAX_SHADOW_LAYERS,
                (index as nat + 1) * 4096 <= self.bytes.len(),
                match shadow_model::selected(layer_views(self.layers@), index as int) {
                    Some(image) => self.view().subrange(index as int * 4096, (index as int + 1) * 4096) == image,
                    None => self.view().subrange(index as int * 4096, (index as int + 1) * 4096)
                        == self.bytes@.subrange(index as int * 4096, (index as int + 1) * 4096),
                },
                shadow_model::selected(layer_views(self.layers@), index as int)
                    == shadow_model::selected(layer_views(self.layers@).subrange(0, cursor as int), index as int),
            decreases cursor,
        {
            let layer = self.layers[cursor - 1];
            assert(layer_views(self.layers@).subrange(0, cursor as int).last() == layer.view());
            assert(layer_views(self.layers@).subrange(0, cursor as int).drop_last()
                == layer_views(self.layers@).subrange(0, cursor as int - 1));
            if let Some(patch) = layer.get(index) {
                let bytes = patch.as_slice();
                assert(shadow_model::selected(layer_views(self.layers@), index as int) == Some(bytes@));
                return Some(Block { bytes, index, source: Ghost(self.view()) });
            }
            cursor -= 1;
        }
        assert(shadow_model::selected(layer_views(self.layers@), index as int).is_none());
        let bytes = &self.bytes[start as usize..(start + 4096) as usize];
        Some(Block { bytes, index, source: Ghost(self.view()) })
    }
}

}
