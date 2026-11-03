// SPDX-License-Identifier: MPL-2.0

//! Borrowed immutable input for host volume validation. Block identity is bound
//! to its exact byte range, independently of checksums. A kernel adapter must
//! refine the frozen CortenMM/OSTD source and partition identity before use.

use vstd::prelude::*;

verus! {

pub struct Snapshot<'a> { bytes: &'a [u8] }
pub struct Block<'a> { bytes: &'a [u8], index: u32, source: Ghost<Seq<u8>> }

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
    pub closed spec fn view(&self) -> Seq<u8> { self.bytes@ }

    pub fn from_bytes(bytes: &'a [u8]) -> (r: Self) ensures r.view() == bytes@ { Snapshot { bytes } }

    pub fn partition_bytes(&self) -> (r: u64) ensures r as nat == self.view().len() { self.bytes.len() as u64 }

    pub fn block(&self, index: u32) -> (r: Option<Block<'a>>)
        ensures match r {
            Some(block) => block.wf() && block.source() == self.view() && block.index() == index,
            None => (index as nat + 1) * 4096 > self.view().len(),
        },
    {
        let start = index as u64 * 4096;
        if start + 4096 > self.bytes.len() as u64 { return None; }
        let bytes = &self.bytes[start as usize..(start + 4096) as usize];
        Some(Block { bytes, index, source: Ghost(self.view()) })
    }
}

}
