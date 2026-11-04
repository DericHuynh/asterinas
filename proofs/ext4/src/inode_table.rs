// SPDX-License-Identifier: MPL-2.0

//! Inode-table reads from the source retained by a checked group index.
//! The byte relation uses descriptor addresses and the inode's group/slot;
//! it does not infer identity from a successful inode checksum.

use vstd::prelude::*;
use crate::{group_index::{self, GroupIndex, IndexView}, group_metadata};

verus! {

pub open spec fn start(v: IndexView, number: u32) -> nat {
    let group = (number as int - 1) / v.ipg as int;
    let slot = (number as int - 1) % v.ipg as int;
    (v.groups[group].inode_table as int * 4096 + slot * 256) as nat
}

pub open spec fn raw(v: IndexView, number: u32) -> Seq<u8> {
    v.source.subrange(start(v, number) as int, start(v, number) as int + 256)
}

pub fn position(index: &GroupIndex<'_>, number: u32) -> (r: Option<u64>)
    ensures index.wf(), match r {
        Some(offset) => 0 < number <= index.view().inodes && offset as nat == start(index.view(), number)
            && offset as nat + 256 <= index.view().blocks as nat * 4096 <= index.view().source.len(),
        None => number == 0 || number > index.view().inodes,
    },
{
    let (_, inodes, ipg, _) = index.parameters();
    if number == 0 || number > inodes { return None; }
    proof { reveal(group_index::valid); }
    let group = (number - 1) / ipg;
    let slot = (number - 1) % ipg;
    proof {
        vstd::arithmetic::mul::lemma_mul_is_commutative(ipg as int, index.view().groups.len() as int);
        vstd::arithmetic::div_mod::lemma_multiply_divide_lt(number as int - 1, ipg as int, index.view().groups.len() as int);
    }
    let meta = index.get(group).unwrap();
    let table = meta.info().inode_table;
    proof { reveal(group_index::records_match); reveal(group_metadata::valid); reveal(crate::group::accepted_with_features); }
    Some(table as u64 * 4096 + slot as u64 * 256)
}

pub fn read<'a>(index: &GroupIndex<'a>, number: u32) -> (r: Option<&'a [u8]>)
    ensures index.wf(), match r {
        Some(bytes) => 0 < number <= index.view().inodes && bytes.len() == 256 && bytes@ == raw(index.view(), number),
        None => number == 0 || number > index.view().inodes,
    },
{
    let (blocks, inodes, ipg, seed) = index.parameters();
    if number == 0 || number > inodes { return None; }
    assert(0 < ipg <= 32768 && ipg % 16 == 0) by { reveal(group_index::valid); }
    let group = (number - 1) / ipg;
    let slot = (number - 1) % ipg;
    assert(group < index.view().groups.len()) by {
        reveal(group_index::valid);
        vstd::arithmetic::mul::lemma_mul_is_commutative(ipg as int, index.view().groups.len() as int);
        vstd::arithmetic::div_mod::lemma_multiply_divide_lt((number - 1) as int, ipg as int, index.view().groups.len() as int);
    }
    let meta = index.get(group).unwrap();
    let info = meta.info();
    assert(info.inode_table as nat + slot as nat / 16 < blocks) by {
        reveal(group_index::valid);
        reveal(group_index::records_match);
        reveal(group_metadata::valid);
        reveal(crate::group::accepted_with_features);
    }
    let block = info.inode_table + slot / 16;
    assert((block as nat + 1) * 4096 <= index.view().source.len()) by { reveal(group_index::valid); }
    let source = index.source();
    let table = source.block(block).unwrap();
    let offset = (slot % 16) as usize * 256;
    let bytes = table.range(offset, 256).unwrap();
    assert(block as int * 4096 + offset as int == info.inode_table as int * 4096 + slot as int * 256) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(slot as int, 16);
    }
    Some(bytes)
}

}
