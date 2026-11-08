// SPDX-License-Identifier: MPL-2.0

//! Disjoint byte edits coalesced against one immutable source block.
//!
//! Quota's 1024-byte units may share one filesystem block. Independently
//! replacing full-block images would discard earlier edits; this owner keeps
//! their coverage until the final full-block candidate is captured. Preimages
//! always refer to the original source, and overlapping edits are rejected.
//! These candidates confer no allocation, journal, device or write authority.

use vstd::prelude::*;
use crate::{bytes, source_block::{self, BlockView, SourceBlock}, transaction::AfterImage};

verus! {

#[verifier::ext_equal]
pub struct EditView {
    pub source: BlockView,
    pub bytes: Seq<u8>,
    pub covered: Seq<bool>,
}

#[verifier::opaque]
pub open spec fn valid(v: EditView) -> bool {
    &&& source_block::valid(v.source)
    &&& v.bytes.len() == v.source.size
    &&& v.covered.len() == v.source.size
    &&& forall|i: int| 0 <= i < v.bytes.len() && !(#[trigger] v.covered[i])
        ==> v.bytes[i] == v.source.bytes[i]
}

pub open spec fn covered_after(covered: Seq<bool>, offset: int, length: nat) -> Seq<bool> {
    Seq::new(covered.len(), |i: int| covered[i] || offset <= i < offset + length)
}

#[verifier::opaque]
pub open spec fn can_edit(v: EditView, offset: int, expected: Seq<u8>, replacement: Seq<u8>) -> bool {
    &&& 0 <= offset
    &&& 0 < expected.len() == replacement.len()
    &&& offset + expected.len() <= v.bytes.len()
    &&& forall|i: int| 0 <= i < expected.len() ==> !(#[trigger] v.covered[offset + i])
        && v.source.bytes[offset + i] == expected[i]
}

// Re-index the acceptance clause through the preimage byte. This gives the
// caller a direct pointwise fact without solving for an offset under a
// sequence-index trigger in the executable loop's short-circuit branches.
proof fn accepted_edit_at(v: EditView, offset: int, expected: Seq<u8>,
    replacement: Seq<u8>, index: int)
    requires valid(v), can_edit(v, offset, expected, replacement),
        0 <= index < expected.len(),
    ensures !v.covered[offset + index],
        v.source.bytes[offset + index] == expected[index],
{
    reveal(valid);
    reveal(can_edit);
    assert forall|j: int| 0 <= j < expected.len()
        implies !v.covered[offset + j]
            && v.source.bytes[offset + j] == #[trigger] expected[j] by {
        assert(!v.covered[offset + j]);
        assert(v.source.bytes[offset + j] == expected[j]);
    }
}

proof fn successful_edit_preserves_frame(v: EditView, offset: int, replacement: Seq<u8>)
    requires valid(v), 0 <= offset, offset + replacement.len() <= v.bytes.len(),
    ensures valid(EditView {
        source: v.source,
        bytes: bytes::splice(v.bytes, offset, replacement),
        covered: covered_after(v.covered, offset, replacement.len()),
    }),
{
    reveal(valid);
    let next = EditView {
        source: v.source,
        bytes: bytes::splice(v.bytes, offset, replacement),
        covered: covered_after(v.covered, offset, replacement.len()),
    };
    assert forall|i: int| 0 <= i < next.bytes.len() && !(#[trigger] next.covered[i])
        implies next.bytes[i] == next.source.bytes[i] by {
        assert(i < offset || offset + replacement.len() <= i);
        bytes::splice_frame(v.bytes, offset, replacement, i);
        assert(!v.covered[i]);
    }
}


proof fn accepted_edit_keeps_prior_covered_bytes(v: EditView, offset: int,
    expected: Seq<u8>, replacement: Seq<u8>)
    requires valid(v), can_edit(v, offset, expected, replacement),
    ensures forall|i: int| 0 <= i < v.bytes.len() && (#[trigger] v.covered[i])
        ==> bytes::splice(v.bytes, offset, replacement)[i] == v.bytes[i]
            && covered_after(v.covered, offset, replacement.len())[i],
{
    reveal(valid);
    reveal(can_edit);
    assert forall|i: int| 0 <= i < v.bytes.len() && (#[trigger] v.covered[i])
        implies bytes::splice(v.bytes, offset, replacement)[i] == v.bytes[i]
            && covered_after(v.covered, offset, replacement.len())[i] by {
        if offset <= i < offset + replacement.len() {
            let relative = i - offset;
            assert(0 <= relative < expected.len());
            assert(!v.covered[offset + relative]);
            assert(false);
        }
        bytes::splice_frame(v.bytes, offset, replacement, i);
    }
}

/// Two nonoverlapping replacements commute; neither full-block image wins.
pub proof fn disjoint_splices_commute(base: Seq<u8>, first_offset: int, first: Seq<u8>,
    second_offset: int, second: Seq<u8>)
    requires 0 <= first_offset, first_offset + first.len() <= base.len(),
        0 <= second_offset, second_offset + second.len() <= base.len(),
        first_offset + first.len() <= second_offset
            || second_offset + second.len() <= first_offset,
    ensures bytes::splice(bytes::splice(base, first_offset, first), second_offset, second)
        == bytes::splice(bytes::splice(base, second_offset, second), first_offset, first),
{
    let left = bytes::splice(bytes::splice(base, first_offset, first), second_offset, second);
    let right = bytes::splice(bytes::splice(base, second_offset, second), first_offset, first);
    assert(left.len() == base.len() && right.len() == base.len());
    assert(left =~= right) by {
        assert forall|i: int| 0 <= i < base.len() implies #[trigger] left[i] == right[i] by {
            if first_offset <= i < first_offset + first.len() {
                assert(i < second_offset || second_offset + second.len() <= i);
            } else if second_offset <= i < second_offset + second.len() {
                assert(i < first_offset || first_offset + first.len() <= i);
            } else {
                bytes::splice_frame(base, first_offset, first, i);
                bytes::splice_frame(base, second_offset, second, i);
            }
        }
    }
}

/// Both requested intervals survive, and all bytes outside them are original.
pub proof fn two_disjoint_edits_survive(base: Seq<u8>, first_offset: int, first: Seq<u8>,
    second_offset: int, second: Seq<u8>)
    requires 0 <= first_offset, first_offset + first.len() <= base.len(),
        0 <= second_offset, second_offset + second.len() <= base.len(),
        first_offset + first.len() <= second_offset
            || second_offset + second.len() <= first_offset,
    ensures ({
        let output = bytes::splice(bytes::splice(base, first_offset, first), second_offset, second);
        &&& output.len() == base.len()
        &&& output.subrange(first_offset, first_offset + first.len()) == first
        &&& output.subrange(second_offset, second_offset + second.len()) == second
        &&& forall|i: int| 0 <= i < base.len()
            && (i < first_offset || first_offset + first.len() <= i)
            && (i < second_offset || second_offset + second.len() <= i)
            ==> #[trigger] output[i] == base[i]
    }),
{
    let output = bytes::splice(bytes::splice(base, first_offset, first), second_offset, second);
    disjoint_splices_commute(base, first_offset, first, second_offset, second);
    assert(output.subrange(first_offset, first_offset + first.len()) =~= first);
    assert(output.subrange(second_offset, second_offset + second.len()) =~= second);
    assert forall|i: int| 0 <= i < base.len()
        && (i < first_offset || first_offset + first.len() <= i)
        && (i < second_offset || second_offset + second.len() <= i)
        implies #[trigger] output[i] == base[i] by {
        bytes::splice_frame(base, first_offset, first, i);
        bytes::splice_frame(bytes::splice(base, first_offset, first), second_offset, second, i);
    }
}

pub struct BlockEditor {
    source: SourceBlock,
    bytes: Vec<u8>,
    covered: Vec<bool>,
}

impl BlockEditor {
    pub closed spec fn view(&self) -> EditView {
        EditView { source: self.source.view(), bytes: self.bytes@, covered: self.covered@ }
    }

    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    /// Starts from exactly the captured block, with no edited bytes.
    pub fn from_source(source: SourceBlock) -> (r: Self)
        ensures r.wf(), r.view().source == source.view(),
            r.view().bytes == source.view().bytes,
            r.view().covered == Seq::<bool>::new(source.view().size as nat, |i: int| false),
    {
        let input = source.raw();
        let mut bytes = Vec::new();
        let mut covered = Vec::<bool>::new();
        let mut i = 0usize;
        while i < input.len()
            invariant i <= input.len(), source.wf(), input@ == source.view().bytes,
                input.len() == source.view().size,
                bytes@ == input@.subrange(0, i as int), covered.len() == i,
                forall|j: int| 0 <= j < i ==> !(#[trigger] covered@[j]),
            decreases input.len() - i,
        {
            bytes.push(input[i]);
            covered.push(false);
            assert(bytes@ =~= input@.subrange(0, i as int + 1));
            i += 1;
        }
        assert(bytes@ =~= source.view().bytes);
        assert(covered@ =~= Seq::<bool>::new(source.view().size as nat, |i: int| false));
        proof { reveal(valid); }
        BlockEditor { source, bytes, covered }
    }

    pub fn raw(&self) -> (r: &[u8])
        ensures self.wf(), r@ == self.view().bytes,
    {
        proof { use_type_invariant(self); }
        self.bytes.as_slice()
    }

    /// Borrows the immutable preimage; edits never modify this capture.
    pub fn original(&self) -> (r: &SourceBlock)
        ensures self.wf(), r.view() == self.view().source,
    {
        proof { use_type_invariant(self); }
        &self.source
    }

    pub fn identity(&self) -> (r: (u64, u32))
        ensures self.wf(), r == (self.view().source.number, self.view().source.size),
    {
        proof { use_type_invariant(self); }
        self.source.identity()
    }

    fn accepts(&self, offset: usize, expected: &[u8], replacement: &[u8]) -> (r: bool)
        ensures self.wf(), r == can_edit(self.view(), offset as int, expected@, replacement@),
    {
        proof { use_type_invariant(self); reveal(valid); reveal(can_edit); }
        if expected.len() == 0 || expected.len() != replacement.len()
            || offset > self.bytes.len() || expected.len() > self.bytes.len() - offset {
            return false;
        }
        let input = self.source.raw();
        let ghost state = self.view();
        let mut i = 0usize;
        while i < expected.len()
            invariant self.wf(), self.view() == state, input@ == state.source.bytes,
                input.len() == self.bytes.len() == self.covered.len(),
                0 < expected.len() == replacement.len(),
                offset as int + expected.len() <= self.bytes.len(), i <= expected.len(),
                forall|j: int| 0 <= j < i ==> !(#[trigger] state.covered[offset + j])
                    && state.source.bytes[offset + j] == expected@[j],
            decreases expected.len() - i,
        {
            if self.covered[offset + i] || input[offset + i] != expected[i] {
                proof {
                    reveal(can_edit);
                    if can_edit(state, offset as int, expected@, replacement@) {
                        accepted_edit_at(state, offset as int, expected@, replacement@, i as int);
                        assert(!state.covered[offset as int + i as int]);
                        assert(state.source.bytes[offset as int + i as int] == expected@[i as int]);
                        assert(false);
                    }
                }
                return false;
            }
            i += 1;
        }
        proof {
            reveal(can_edit);
            assert forall|j: int| 0 <= j < expected.len()
                implies !(#[trigger] state.covered[offset as int + j])
                    && state.source.bytes[offset as int + j] == expected@[j] by {
                assert(j < i);
            }
            assert(can_edit(state, offset as int, expected@, replacement@));
        }
        true
    }

    /// Applies one disjoint replacement, returning the unchanged owner on error.
    pub fn apply(self, offset: usize, expected: &[u8], replacement: &[u8]) -> (r: Result<Self, Self>)
        ensures self.wf(), match r {
            Ok(next) => can_edit(self.view(), offset as int, expected@, replacement@)
                && next.wf() && next.view().source == self.view().source
                && next.view().bytes == bytes::splice(self.view().bytes, offset as int, replacement@)
                && next.view().covered == covered_after(self.view().covered, offset as int, replacement@.len())
                && (forall|i: int| 0 <= i < self.view().bytes.len() && (#[trigger] self.view().covered[i])
                    ==> next.view().bytes[i] == self.view().bytes[i] && next.view().covered[i]),
            Err(original) => original.wf() && original.view() == self.view()
                && !can_edit(self.view(), offset as int, expected@, replacement@),
        },
    {
        proof { use_type_invariant(&self); }
        if !self.accepts(offset, expected, replacement) { return Err(self); }
        let ghost before = self.view();
        proof { reveal(can_edit); reveal(valid); }
        let BlockEditor { source, mut bytes, mut covered } = self;
        let written = bytes::write_bytes(bytes.as_mut_slice(), offset, replacement);
        assert(written);
        assert(covered@ =~= covered_after(before.covered, offset as int, 0));
        let mut i = 0usize;
        while i < replacement.len()
            invariant before.source == source.view(), valid(before),
                bytes@ == bytes::splice(before.bytes, offset as int, replacement@),
                covered@ == covered_after(before.covered, offset as int, i as nat),
                offset as int + replacement.len() <= covered.len(),
                i <= replacement.len(),
            decreases replacement.len() - i,
        {
            covered.set(offset + i, true);
            assert(covered@ =~= covered_after(before.covered, offset as int, i as nat + 1));
            i += 1;
        }
        proof {
            successful_edit_preserves_frame(before, offset as int, replacement@);
            accepted_edit_keeps_prior_covered_bytes(before, offset as int, expected@, replacement@);
        }
        Ok(BlockEditor { source, bytes, covered })
    }

    /// Projects a candidate into the old 4096-byte/u32 profile without truncation.
    pub fn into_after_image(self) -> (r: Result<AfterImage, Self>)
        ensures match r {
            Ok(image) => self.view().source.size == 4096 && self.view().source.number <= u32::MAX
                && image.view().block as u64 == self.view().source.number
                && image.view().image == self.view().bytes,
            Err(original) => original.wf() && original.view() == self.view()
                && (self.view().source.size != 4096 || self.view().source.number > u32::MAX),
        },
    {
        proof { use_type_invariant(&self); reveal(valid); }
        let (number, size) = self.source.identity();
        if size != 4096 || number > u32::MAX as u64 { return Err(self); }
        Ok(AfterImage::capture(number as u32, self.bytes.as_slice()).unwrap())
    }
}

}
