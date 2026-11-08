// SPDX-License-Identifier: MPL-2.0

//! Borrowed immutable input for host volume validation. Block identity is bound
//! to its exact byte range, independently of checksums. A kernel adapter must
//! refine the frozen CortenMM/OSTD source and partition identity before use.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{patch_set::{self, PatchSet}, shadow_model};

verus! {

pub const MAX_SHADOW_LAYERS: usize = 32;

pub struct Snapshot<'a> { bytes: &'a [u8], layers: Vec<&'a PatchSet> }
pub struct Block<'a> { bytes: &'a [u8], index: u32, source: Ghost<Seq<u8>> }
struct Piece<'a> { bytes: &'a [u8], offset: u64, source: Ghost<Seq<u8>> }

impl<'a> Piece<'a> {
    spec fn wf(&self) -> bool {
        &&& 0 < self.bytes.len() <= 4096
        &&& self.offset as nat + self.bytes.len() <= self.source@.len()
        &&& self.bytes@ == self.source@.subrange(self.offset as int, self.offset as int + self.bytes.len())
    }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
}

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

    pub fn duplicate(&self) -> (r: Self) ensures r.wf(), r.view() == self.view(), r.depth() == self.depth() {
        proof { use_type_invariant(self); }
        let mut layers = Vec::new();
        let mut index = 0usize;
        while index < self.layers.len()
            invariant index <= self.layers.len() <= MAX_SHADOW_LAYERS,
                layers@ == self.layers@.subrange(0, index as int),
            decreases self.layers.len() - index,
        {
            layers.push(self.layers[index]);
            index += 1;
        }
        assert(layers@ == self.layers@);
        Snapshot { bytes: self.bytes, layers }
    }

    pub fn overlay<'b>(&self, patches: &'b PatchSet) -> (r: Option<Snapshot<'b>>)
        where 'a: 'b,
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

    pub fn capture(&self, start: u32, count: u32) -> (r: Option<Vec<u8>>)
        ensures match r {
            Some(bytes) => 0 < count <= 32768 && start as nat + count <= 4294967296
                && (start as nat + count) * 4096 <= self.view().len()
                && bytes@ == self.view().subrange(start as int * 4096, (start as int + count) * 4096),
            None => count == 0 || count > 32768 || start as nat + count > 4294967296
                || (start as nat + count) * 4096 > self.view().len(),
        },
    {
        if count == 0 || count > 32768 || start as u64 + count as u64 > 4294967296
            || (start as u64 + count as u64) * 4096 > self.partition_bytes() { return None; }
        let mut bytes = Vec::new();
        let mut block = 0u32;
        while block < count
            invariant 0 < count <= 32768, block <= count, start as nat + count <= 4294967296,
                (start as nat + count) * 4096 <= self.view().len(),
                bytes@ == self.view().subrange(start as int * 4096, (start as int + block) * 4096),
            decreases count - block,
        {
            let raw = self.block(start + block).unwrap().as_slice();
            let mut offset = 0usize;
            while offset < 4096
                invariant offset <= 4096, raw.len() == 4096, block < count <= 32768,
                    start as nat + count <= 4294967296,
                    (start as nat + count) * 4096 <= self.view().len(),
                    raw@ == self.view().subrange((start as int + block) * 4096, (start as int + block + 1) * 4096),
                    bytes@ == self.view().subrange(start as int * 4096, (start as int + block) * 4096 + offset),
                decreases 4096 - offset,
            {
                bytes.push(raw[offset]);
                assert(bytes@ =~= self.view().subrange(start as int * 4096, (start as int + block) * 4096 + offset + 1));
                offset += 1;
            }
            block += 1;
        }
        Some(bytes)
    }

    fn piece(&self, offset: u64, requested: usize) -> (r: Option<Piece<'a>>)
        ensures match r {
            Some(piece) => piece.wf() && piece.offset == offset && piece.source@ == self.view()
                && piece.bytes.len() <= requested && piece.bytes.len() <= 4096 - offset % 4096,
            None => offset >= self.view().len() || requested == 0,
        },
    {
        proof { use_type_invariant(self); }
        if offset >= self.bytes.len() as u64 || requested == 0 { return None; }
        let within = (offset % 4096) as usize;
        let page = offset / 4096;
        let remaining = self.bytes.len() - offset as usize;
        let page_remaining = 4096usize - within;
        let amount = if requested < page_remaining { requested } else { page_remaining };
        let amount = if amount < remaining { amount } else { remaining };
        proof {
            assert forall|i: int| 0 <= i < self.layers.len() implies patch_set::valid(#[trigger] layer_views(self.layers@)[i]) by {
                assert(self.layers@[i].wf());
            }
            shadow_model::a_segment_has_exact_selected_bytes(self.bytes@, layer_views(self.layers@), offset as nat, amount as nat);
        }
        let mut cursor = self.layers.len();
        assert(layer_views(self.layers@).subrange(0, cursor as int) == layer_views(self.layers@));
        while cursor > 0
            invariant self.wf(), cursor <= self.layers.len() <= MAX_SHADOW_LAYERS,
                offset < self.bytes.len(), 0 < amount <= requested, amount <= remaining,
                remaining == self.bytes.len() - offset, within == offset % 4096, amount <= 4096 - within, page == offset / 4096,
                match shadow_model::selected(layer_views(self.layers@), page as int) {
                    Some(image) => self.view().subrange(offset as int, offset as int + amount)
                        == image.subrange(within as int, (within + amount) as int),
                    None => self.view().subrange(offset as int, offset as int + amount)
                        == self.bytes@.subrange(offset as int, offset as int + amount),
                },
                shadow_model::selected(layer_views(self.layers@), page as int)
                    == shadow_model::selected(layer_views(self.layers@).subrange(0, cursor as int), page as int),
            decreases cursor,
        {
            let layer = self.layers[cursor - 1];
            assert(layer_views(self.layers@).subrange(0, cursor as int).last() == layer.view());
            assert(layer_views(self.layers@).subrange(0, cursor as int).drop_last()
                == layer_views(self.layers@).subrange(0, cursor as int - 1));
            if page <= 4294967295 {
                if let Some(patch) = layer.get(page as u32) {
                    let image = patch.as_slice();
                    let bytes = &image[within..within + amount];
                    return Some(Piece { bytes, offset, source: Ghost(self.view()) });
                }
            } else {
                assert(!exists|i: int| 0 <= i < layer.view().len() && (#[trigger] layer.view()[i]).block as int == page as int);
            }
            cursor -= 1;
        }
        assert(shadow_model::selected(layer_views(self.layers@), page as int).is_none());
        let bytes = &self.bytes[offset as usize..offset as usize + amount];
        Some(Piece { bytes, offset, source: Ghost(self.view()) })
    }

    pub fn capture_bytes(&self, start: u64, length: usize) -> (r: Option<Vec<u8>>)
        ensures match r {
            Some(bytes) => length <= 65536 && start as nat + length <= self.view().len()
                && bytes@ == self.view().subrange(start as int, start as int + length),
            None => length > 65536 || start as nat + length > self.view().len(),
        },
    {
        if length > 65536 || start > self.partition_bytes() || length as u64 > self.partition_bytes() - start { return None; }
        let mut bytes = Vec::new();
        let mut index = 0usize;
        while index < length
            invariant index <= length <= 65536, start as nat + length <= self.view().len(),
                start as nat + length <= 18446744073709551615,
                bytes@ == self.view().subrange(start as int, start as int + index),
            decreases length - index,
        {
            let piece = self.piece(start + index as u64, length - index).unwrap();
            let mut i = 0usize;
            while i < piece.bytes.len()
                invariant index < length <= 65536, start as nat + length <= self.view().len(),
                    start as nat + length <= 18446744073709551615,
                    piece.wf(), piece.offset as nat == start as nat + index, piece.source@ == self.view(),
                    0 < piece.bytes.len() <= length - index, i <= piece.bytes.len(),
                    bytes@ == self.view().subrange(start as int, start as int + index + i),
                decreases piece.bytes.len() - i,
            {
                bytes.push(piece.bytes[i]);
                assert(bytes@ =~= self.view().subrange(start as int, start as int + index + i + 1));
                i += 1;
            }
            index += piece.bytes.len();
        }
        Some(bytes)
    }
}

}
