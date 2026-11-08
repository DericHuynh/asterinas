// SPDX-License-Identifier: MPL-2.0

//! Owned immutable filesystem-block bytes, bound to their exact range in one
//! host snapshot. Filesystem blocks may be smaller/larger than a 4 KiB shadow
//! page. This is byte provenance, not CortenMM, allocation or device authority.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{block_size, extent_node::{self, BlockChecksum, Node}, snapshot::Snapshot};

verus! {

pub struct BlockView { pub source: Seq<u8>, pub number: u64, pub size: u32, pub bytes: Seq<u8> }

pub open spec fn valid(v: BlockView) -> bool {
    &&& block_size::accepted(v.size as nat) && (v.number as nat + 1) * v.size <= v.source.len()
    &&& v.bytes.len() == v.size
    &&& v.bytes == v.source.subrange(v.number as int * v.size as int, (v.number as int + 1) * v.size as int)
}

pub proof fn whole_blocks_fit_exactly_below_the_partition_quotient(length: u64, size: u32, count: nat)
    requires size > 0,
    ensures (count * size <= length) == (count <= length as nat / size as nat),
{
    let q = length as int / size as int;
    let r = length as int % size as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(length as int, size as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(q, size as int);
    assert(length as int == q * size as int + r);
    if count as int <= q {
        vstd::arithmetic::mul::lemma_mul_inequality(count as int, q, size as int);
    } else {
        vstd::arithmetic::mul::lemma_mul_inequality(q + 1, count as int, size as int);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(size as int, q, 1);
    }
}

pub struct SourceBlock { bytes: Vec<u8>, number: u64, size: u32, partition_bytes: u64, source: Ghost<Seq<u8>> }

impl SourceBlock {
    pub closed spec fn view(&self) -> BlockView { BlockView { source: self.source@, number: self.number, size: self.size, bytes: self.bytes@ } }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() && self.partition_bytes as nat == self.source@.len() }

    pub fn raw(&self) -> (r: &[u8]) ensures self.wf(), r@ == self.view().bytes, r.len() == self.view().size {
        proof { use_type_invariant(self); }
        self.bytes.as_slice()
    }

    pub fn identity(&self) -> (r: (u64, u32)) ensures self.wf(), r == (self.view().number, self.view().size) {
        proof { use_type_invariant(self); }
        (self.number, self.size)
    }

    pub fn parse_extent_node(&self, filesystem_blocks: u64, checksum: BlockChecksum) -> (r: Option<Node<'_>>)
        ensures self.wf(), match r {
            Some(node) => node.wf() && node.view().raw == self.view().bytes && node.view().blocks == filesystem_blocks
                && node.view().kind == extent_node::block_kind(checksum)
                && filesystem_blocks as nat * self.view().size <= self.view().source.len(),
            None => filesystem_blocks as nat * self.view().size > self.view().source.len()
                || !extent_node::valid(extent_node::NodeView { raw: self.view().bytes, blocks: filesystem_blocks, kind: extent_node::block_kind(checksum) }),
        },
    {
        proof { use_type_invariant(self); }
        let length = self.source_length();
        proof { whole_blocks_fit_exactly_below_the_partition_quotient(length, self.size, filesystem_blocks as nat); }
        if filesystem_blocks > length / self.size as u64 { return None; }
        extent_node::parse_block(self.bytes.as_slice(), filesystem_blocks, checksum)
    }

    fn source_length(&self) -> (r: u64) ensures r as nat == self.view().source.len() {
        proof { use_type_invariant(self); }
        self.partition_bytes
    }
}

pub fn capture(source: &Snapshot<'_>, number: u64, size: u32) -> (r: Option<SourceBlock>)
    ensures match r {
        Some(block) => block.wf() && block.view().source == source.view() && block.view().number == number && block.view().size == size,
        None => !block_size::accepted(size as nat) || (number as nat + 1) * size > source.view().len(),
    },
{
    if !block_size::valid(size as usize) { return None; }
    let limit = source.partition_bytes();
    proof { whole_blocks_fit_exactly_below_the_partition_quotient(limit, size, number as nat + 1); }
    if number >= limit / size as u64 { return None; }
    proof {
        assert((number as int + 1) * size as int <= limit);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(size as int, number as int, 1);
    }
    let start = number * size as u64;
    let bytes = source.capture_bytes(start, size as usize).unwrap();
    Some(SourceBlock { bytes, number, size, partition_bytes: limit, source: Ghost(source.view()) })
}

}
