// SPDX-License-Identifier: MPL-2.0

//! Bounded sorted immutable block patches for shadow-image validation.
//! Exact bytes and block identity are retained; these candidate images do not
//! confer filesystem mutation or device authority. Lookup is binary search.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::transaction::{self, AfterImage, ImageView};

verus! {

pub const MAX_PATCHES: usize = 4096;

#[verifier::opaque]
pub open spec fn valid(images: Seq<ImageView>) -> bool {
    &&& images.len() <= MAX_PATCHES
    &&& forall|i: int| 0 <= i < images.len() ==> (#[trigger] images[i]).image.len() == 4096
    &&& forall|i: int, j: int| 0 <= i < j < images.len() ==> (#[trigger] images[i]).block < (#[trigger] images[j]).block
}

pub open spec fn selected(images: Seq<ImageView>, block: int) -> Option<Seq<u8>> {
    if exists|i: int| 0 <= i < images.len() && (#[trigger] images[i]).block as int == block {
        let i = choose|i: int| 0 <= i < images.len() && (#[trigger] images[i]).block as int == block;
        Some(images[i].image)
    } else { None }
}

pub open spec fn apply(base: Seq<u8>, images: Seq<ImageView>) -> Seq<u8> {
    Seq::new(base.len(), |i: int| match selected(images, i / 4096) {
        Some(image) => image[i % 4096], None => base[i],
    })
}

pub proof fn one_target_has_one_image(images: Seq<ImageView>, index: int)
    requires valid(images), 0 <= index < images.len(),
    ensures selected(images, images[index].block as int) == Some(images[index].image),
{
    reveal(valid);
    assert(exists|i: int| 0 <= i < images.len() && (#[trigger] images[i]).block == images[index].block);
    let i = choose|i: int| 0 <= i < images.len() && (#[trigger] images[i]).block == images[index].block;
    if i < index { assert(images[i].block < images[index].block); }
    if index < i { assert(images[index].block < images[i].block); }
    assert(i == index);
}

pub proof fn applying_a_patch_replaces_exactly_its_block(base: Seq<u8>, images: Seq<ImageView>, block: u32)
    requires valid(images), (block as nat + 1) * 4096 <= base.len(),
    ensures match selected(images, block as int) {
        Some(image) => apply(base, images).subrange(block as int * 4096, (block as int + 1) * 4096) == image,
        None => apply(base, images).subrange(block as int * 4096, (block as int + 1) * 4096)
            == base.subrange(block as int * 4096, (block as int + 1) * 4096),
    },
{
    reveal(valid);
    let start = block as int * 4096;
    if let Some(image) = selected(images, block as int) {
        let i = choose|i: int| 0 <= i < images.len() && (#[trigger] images[i]).block == block;
        one_target_has_one_image(images, i);
        assert(image.len() == 4096);
        assert(apply(base, images).subrange(start, start + 4096) =~= image) by {
            assert forall|j: int| 0 <= j < 4096 implies #[trigger] apply(base, images)[start + j] == image[j] by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(start + j, 4096, block as int, j);
            }
        }
    } else {
        assert(apply(base, images).subrange(start, start + 4096) =~= base.subrange(start, start + 4096)) by {
            assert forall|j: int| 0 <= j < 4096 implies #[trigger] apply(base, images)[start + j] == base[start + j] by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(start + j, 4096, block as int, j);
            }
        }
    }
}

proof fn inserting_between_sorted_neighbors(images: Seq<ImageView>, position: int, next: ImageView)
    requires valid(images), images.len() < MAX_PATCHES, 0 <= position <= images.len(), next.image.len() == 4096,
        forall|i: int| 0 <= i < position ==> (#[trigger] images[i]).block < next.block,
        forall|i: int| position <= i < images.len() ==> next.block < (#[trigger] images[i]).block,
    ensures valid(images.insert(position, next)),
{
    reveal(valid);
    let result = images.insert(position, next);
    assert forall|i: int, j: int| 0 <= i < j < result.len() implies (#[trigger] result[i]).block < (#[trigger] result[j]).block by {
        if i < position && j < position { assert(result[i] == images[i] && result[j] == images[j]); }
        else if i > position { assert(result[i] == images[i - 1] && result[j] == images[j - 1]); }
        else if i == position { assert(result[i] == next && result[j] == images[j - 1]); }
        else if j == position { assert(result[i] == images[i] && result[j] == next); }
        else { assert(result[i] == images[i] && result[j] == images[j - 1]); }
    }
}

pub struct PatchSet { images: Vec<AfterImage> }

impl PatchSet {
    pub closed spec fn view(&self) -> Seq<ImageView> { transaction::images(self.images@) }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn new() -> (r: Self) ensures r.wf(), r.view().len() == 0 {
        let images = Vec::new();
        assert(transaction::images(images@) =~= Seq::empty());
        assert(valid(Seq::empty())) by { reveal(valid); }
        PatchSet { images }
    }

    pub fn from_images(images: Vec<AfterImage>) -> (r: Result<Self, Vec<AfterImage>>)
        ensures match r {
            Ok(patches) => patches.wf() && patches.view() == transaction::images(images@),
            Err(original) => !valid(transaction::images(images@)) && original@ == images@,
        },
    {
        proof { reveal(valid); }
        if images.len() > MAX_PATCHES { return Err(images); }
        let mut index = 0usize;
        while index < images.len()
            invariant index <= images.len() <= MAX_PATCHES,
                forall|i: int| 0 <= i < index ==> (#[trigger] transaction::images(images@)[i]).image.len() == 4096,
                forall|i: int, j: int| 0 <= i < j < index ==> (#[trigger] transaction::images(images@)[i]).block < (#[trigger] transaction::images(images@)[j]).block,
            decreases images.len() - index,
        {
            let image = &images[index];
            let block = image.block();
            let _ = image.as_slice();
            if index > 0 && images[index - 1].block() >= block {
                assert(!valid(transaction::images(images@))) by {
                    reveal(valid);
                    if valid(transaction::images(images@)) {
                        assert(transaction::images(images@)[index as int - 1].block < transaction::images(images@)[index as int].block);
                    }
                }
                return Err(images);
            }
            assert forall|i: int| 0 <= i < index implies (#[trigger] transaction::images(images@)[i]).block < block by {
                if i < index as int - 1 { assert(transaction::images(images@)[i].block < transaction::images(images@)[index as int - 1].block); }
            }
            index += 1;
        }
        Ok(PatchSet { images })
    }

    pub fn len(&self) -> (r: usize) ensures self.wf(), r == self.view().len(), r <= MAX_PATCHES {
        proof { use_type_invariant(self); reveal(valid); }
        self.images.len()
    }

    pub fn at(&self, index: usize) -> (r: Option<&AfterImage>)
        ensures self.wf(), match r {
            Some(image) => index < self.view().len() && image.view() == self.view()[index as int],
            None => index >= self.view().len(),
        },
    {
        proof { use_type_invariant(self); }
        if index >= self.images.len() { None } else { Some(&self.images[index]) }
    }

    fn position(&self, block: u32) -> (r: Result<usize, usize>)
        ensures self.wf(), match r {
            Ok(index) => index < self.view().len() && self.view()[index as int].block == block,
            Err(position) => position <= self.view().len()
                && (forall|i: int| 0 <= i < position ==> (#[trigger] self.view()[i]).block < block)
                && (forall|i: int| position <= i < self.view().len() ==> block < (#[trigger] self.view()[i]).block),
        },
    {
        proof { use_type_invariant(self); reveal(valid); }
        let mut low = 0usize;
        let mut high = self.images.len();
        while low < high
            invariant self.wf(), low <= high <= self.images.len() <= MAX_PATCHES,
                forall|i: int| 0 <= i < low ==> (#[trigger] self.view()[i]).block < block,
                forall|i: int| high <= i < self.images.len() ==> block < (#[trigger] self.view()[i]).block,
            decreases high - low,
        {
            let middle = low + (high - low) / 2;
            let target = self.images[middle].block();
            if target == block { return Ok(middle); }
            if target < block {
                assert forall|i: int| 0 <= i < middle + 1 implies (#[trigger] self.view()[i]).block < block by {
                    if i < middle { assert(self.view()[i].block < self.view()[middle as int].block) by { reveal(valid); } }
                }
                low = middle + 1;
            } else {
                assert forall|i: int| middle <= i < self.images.len() implies block < (#[trigger] self.view()[i]).block by {
                    if middle < i { assert(self.view()[middle as int].block < self.view()[i].block) by { reveal(valid); } }
                }
                high = middle;
            }
        }
        Err(low)
    }

    pub fn get(&self, block: u32) -> (r: Option<&AfterImage>)
        ensures self.wf(), match r {
            Some(image) => image.view().block == block && self.view().contains(image.view())
                && selected(self.view(), block as int) == Some(image.view().image),
            None => selected(self.view(), block as int).is_none(),
        },
    {
        match self.position(block) {
            Ok(index) => {
                assert(self.view().contains(self.view()[index as int]));
                proof { one_target_has_one_image(self.view(), index as int); }
                Some(&self.images[index])
            },
            Err(position) => {
                assert(!exists|i: int| 0 <= i < self.view().len() && (#[trigger] self.view()[i]).block == block);
                None
            },
        }
    }

    pub fn insert(self, block: u32, bytes: &[u8]) -> (r: Result<Self, Self>)
        ensures match r {
            Ok(next) => next.wf() && next.view().len() == self.view().len() + 1
                && (exists|position: int| 0 <= position <= self.view().len() && next.view() == self.view().insert(position, ImageView { block, image: bytes@ })),
            Err(original) => original.view() == self.view() && (bytes.len() != 4096 || self.view().len() == MAX_PATCHES
                || exists|i: int| 0 <= i < self.view().len() && (#[trigger] self.view()[i]).block == block),
        },
    {
        proof { use_type_invariant(&self); reveal(valid); }
        if bytes.len() != 4096 || self.images.len() == MAX_PATCHES { return Err(self); }
        let position = match self.position(block) { Ok(_) => { return Err(self); }, Err(position) => position };
        let next = AfterImage::capture(block, bytes).unwrap();
        let ghost before = self.view();
        let ghost candidate = next.view();
        proof { inserting_between_sorted_neighbors(before, position as int, candidate); }
        let PatchSet { mut images } = self;
        images.insert(position, next);
        assert(transaction::images(images@) =~= before.insert(position as int, candidate));
        Ok(PatchSet { images })
    }

    pub fn into_images(self) -> (r: Vec<AfterImage>) ensures transaction::images(r@) == self.view() { self.images }

    pub fn upsert(self, block: u32, bytes: &[u8]) -> (r: Result<Self, Self>)
        ensures match r {
            Ok(next) => next.wf() && (exists|position: int| 0 <= position < self.view().len()
                && self.view()[position].block == block
                && next.view() == self.view().update(position, ImageView { block, image: bytes@ }))
                || next.wf() && (exists|position: int| 0 <= position <= self.view().len()
                    && next.view() == self.view().insert(position, ImageView { block, image: bytes@ })),
            Err(original) => original.view() == self.view() && (bytes.len() != 4096
                || self.view().len() == MAX_PATCHES && selected(self.view(), block as int).is_none()),
        },
    {
        proof { use_type_invariant(&self); reveal(valid); }
        if bytes.len() != 4096 { return Err(self); }
        match self.position(block) {
            Err(_) => self.insert(block, bytes),
            Ok(index) => {
                let next = AfterImage::capture(block, bytes).unwrap();
                let ghost before = self.view();
                let ghost image = next.view();
                assert(valid(before.update(index as int, image))) by { reveal(valid); }
                let PatchSet { mut images } = self;
                images.set(index, next);
                assert(transaction::images(images@) =~= before.update(index as int, image));
                Ok(PatchSet { images })
            },
        }
    }
}

pub proof fn applying_patches_preserves_the_source_length(source: Seq<u8>, patches: Seq<ImageView>)
    ensures apply(source, patches).len() == source.len(),
{
}


pub proof fn a_single_patch_selects_exactly_its_target(image: ImageView, block: int)
    ensures selected(seq![image], block) == if block == image.block as int { Some(image.image) } else { None },
{
    let entries = seq![image];
    if block == image.block as int {
        assert(entries.len() == 1 && entries[0] == image);
        assert(0 <= 0int < entries.len() && entries[0].block as int == block);
        assert(exists|i: int| 0 <= i < entries.len() && (#[trigger] entries[i]).block as int == block);
        let i = choose|i: int| 0 <= i < entries.len() && (#[trigger] entries[i]).block as int == block;
        assert(i == 0);
    } else {
        assert forall|i: int| 0 <= i < entries.len() implies (#[trigger] entries[i]).block as int != block by { assert(i == 0); }
    }
}



/// An exact raw primary marker can be projected without opening a filesystem
/// header predicate or the whole-image patch application in its caller.
pub(crate) proof fn a_primary_marker_replaces_exactly_block_zero(source: Seq<u8>, marker: Seq<u8>)
    requires source.len() >= 4096, marker.len() == 4096,
    ensures apply(source, seq![ImageView { block: 0, image: marker }]).len() == source.len(),
        apply(source, seq![ImageView { block: 0, image: marker }]).subrange(0, 4096) == marker,
{
    let image = ImageView { block: 0, image: marker };
    let patches = seq![image];
    assert(valid(patches)) by { reveal(valid); }
    a_single_patch_selects_exactly_its_target(image, 0);
    applying_a_patch_replaces_exactly_its_block(source, patches, 0);
}

}
