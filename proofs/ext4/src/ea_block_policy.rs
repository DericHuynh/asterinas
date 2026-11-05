// SPDX-License-Identifier: MPL-2.0

//! Source-selected allocation and fixed-metadata exclusions for EA value
//! claims. Ordinary file/directory/journal extents remain a separate ownership
//! boundary; this checker supplies neither a full allocation census nor I/O.

use vstd::prelude::*;
use crate::{backup_layout, bitmap, block_claims::{self, Claim}, ea_census::{self, Census, CensusView},
    ea_index::{self, Index, IndexView}};

verus! {

pub open spec fn allocated(v: IndexView, block: u32) -> bool {
    block < v.header.blocks && block / 32768 < v.groups.len()
        && bitmap::set(v.groups[(block / 32768) as int].allocation.raw, (block % 32768) as int)
}
pub open spec fn group_fixed_metadata(v: IndexView, number: int, block: u32) -> bool {
    block == v.groups[number].block_bitmap || block == v.groups[number].inode_bitmap
        || ea_index::table_contains(v.groups[number], block)
        || backup_layout::present(v.header.source.subrange(1024, 2048), number as u32)
            && (block as nat == number * 32768 || block as nat == number * 32768 + 1)
}
pub open spec fn fixed_metadata(v: IndexView, block: u32) -> bool {
    exists|i: int| 0 <= i < v.groups.len() && #[trigger] group_fixed_metadata(v, i, block)
}
pub open spec fn usable(v: CensusView, block: u32) -> bool {
    allocated(v.index, block) && !fixed_metadata(v.index, block)
        && ea_census::external_count(v.external, block) == 0
}
pub open spec fn claim_storage(v: CensusView, claim: Claim) -> bool {
    claim.length > 0 && claim.start as nat + claim.length <= v.index.header.blocks
        && forall|block: u32| block_claims::covers(claim, block as int) ==> #[trigger] usable(v, block)
}
pub open spec fn valid_claim_storage(v: CensusView, claims: Seq<Claim>) -> bool {
    ea_census::valid(v) && forall|i: int| 0 <= i < claims.len() ==> #[trigger] claim_storage(v, claims[i])
}

pub fn block_is_allocated(index: &Index<'_, '_>, block: u32) -> (r: bool)
    ensures index.wf(), ea_index::valid(index.view()), r == allocated(index.view(), block),
{
    let (blocks, _, _, _) = index.parameters();
    if block >= blocks { return false; }
    let group_number = block / 32768;
    let group = match index.group(group_number) { Some(group) => group, None => { return false; } };
    let (bits, _) = group.bitmaps();
    let _ = bits.entry_count();
    let raw = bits.raw_image();
    assert(raw.len() == 4096);
    bitmap::read_bit(raw, block % 32768).unwrap()
}

pub fn is_fixed_metadata(index: &Index<'_, '_>, block: u32) -> (r: bool)
    ensures index.wf(), ea_index::valid(index.view()), r == fixed_metadata(index.view(), block),
{
    let count = index.group_count(); let source = index.source();
    assert(source.view().len() >= 4096) by { reveal(ea_index::valid); reveal(crate::ea_source::header_valid); }
    let mut i = 0usize;
    while i < count
        invariant index.wf(), ea_index::valid(index.view()), count == index.view().groups.len(), count <= 32,
            source.view() == index.view().header.source, source.view().len() >= 4096, i <= count,
            forall|j: int| 0 <= j < i ==> !#[trigger] group_fixed_metadata(index.view(), j, block),
        decreases count - i,
    {
        let group = index.group(i as u32).unwrap(); let info = group.info();
        let backup = backup_layout::source_group(source, i as u32).unwrap();
        let first = i as u64 * 32768;
        if block == info.block_bitmap || block == info.inode_bitmap
            || info.inode_table <= block && (block as u64) < info.inode_table as u64 + info.inode_table_blocks as u64
            || backup && (block as u64 == first || block as u64 == first + 1)
        {
            assert(group_fixed_metadata(index.view(), i as int, block));
            assert(exists|j: int| 0 <= j < index.view().groups.len() && #[trigger] group_fixed_metadata(index.view(), j, block));
            return true;
        }
        assert(!group_fixed_metadata(index.view(), i as int, block));
        i += 1;
    }
    assert(!fixed_metadata(index.view(), block));
    false
}

pub fn check(refs: &Census<'_, '_>, claims: &[Claim]) -> (r: bool)
    ensures refs.wf(), ea_census::valid(refs.view()), r ==> valid_claim_storage(refs.view(), claims@),
{
    let index = refs.index(); let (blocks, _, _, _) = index.parameters();
    let mut i = 0usize;
    while i < claims.len()
        invariant refs.wf(), ea_census::valid(refs.view()), index.wf(), ea_index::valid(index.view()),
            index.view() == refs.view().index, blocks == index.view().header.blocks <= 1048576,
            i <= claims.len(), forall|j: int| 0 <= j < i ==> #[trigger] claim_storage(refs.view(), claims@[j]),
        decreases claims.len() - i,
    {
        let claim = claims[i];
        if claim.length == 0 || claim.start as u64 + claim.length as u64 > blocks as u64 { return false; }
        let end = claim.start + claim.length; let mut block = claim.start;
        while block < end
            invariant refs.wf(), ea_census::valid(refs.view()), index.wf(), ea_index::valid(index.view()),
                index.view() == refs.view().index, blocks == index.view().header.blocks <= 1048576,
                claim.length > 0, end as nat == claim.start as nat + claim.length, end <= blocks,
                claim.start <= block <= end, i < claims.len(), claim == claims@[i as int],
                forall|j: int| 0 <= j < i ==> #[trigger] claim_storage(refs.view(), claims@[j]),
                forall|b: u32| claim.start <= b < block ==> #[trigger] usable(refs.view(), b),
            decreases end - block,
        {
            if !block_is_allocated(index, block) || is_fixed_metadata(index, block) || refs.external_parents(block) != 0 { return false; }
            assert(usable(refs.view(), block));
            assert forall|b: u32| claim.start <= b && (b as nat) < block as nat + 1 implies #[trigger] usable(refs.view(), b) by {
                if b == block { assert(usable(refs.view(), block)); }
            }
            block += 1;
        }
        assert(claim_storage(refs.view(), claim));
        assert forall|j: int| 0 <= j < i + 1 implies #[trigger] claim_storage(refs.view(), claims@[j]) by {
            if j == i { assert(claims@[j] == claim); }
        }
        i += 1;
    }
    true
}

pub proof fn every_checked_ea_claim_block_is_source_allocated_and_outside_fixed_metadata(v: CensusView, claims: Seq<Claim>, i: int, block: u32)
    requires valid_claim_storage(v, claims), 0 <= i < claims.len(), block_claims::covers(claims[i], block as int),
    ensures allocated(v.index, block), !fixed_metadata(v.index, block), ea_census::external_count(v.external, block) == 0,
{
    assert(claim_storage(v, claims[i]));
    assert(usable(v, block));
}

}
