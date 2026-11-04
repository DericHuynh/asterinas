// SPDX-License-Identifier: MPL-2.0

//! Canonical directory bytes/records as a function of one validated image.
//! Choices are guarded by existence and proved unique against executable
//! mappings and complete record chains; no checksum injectivity is assumed.

use vstd::prelude::*;
use crate::{allocated_inode::{self, NodeView}, allocation::AllocationView, crc,
    directory_block::{self, BlockView}, file_read, group};

verus! {

pub open spec fn initialized(v: AllocationView, n: u32, logical: u32) -> bool {
    exists|physical: u32| #[trigger] file_read::maps(allocated_inode::source_view(v, n), logical, physical)
}

pub open spec fn physical(v: AllocationView, n: u32, logical: u32) -> u32 {
    if initialized(v, n, logical) {
        choose|physical: u32| #[trigger] file_read::maps(allocated_inode::source_view(v, n), logical, physical)
    } else { 0u32 }
}

pub open spec fn raw(v: AllocationView, n: u32, logical: u32) -> Seq<u8> {
    if initialized(v, n, logical) {
        v.index.source.subrange(physical(v, n, logical) as int * 4096, (physical(v, n, logical) as int + 1) * 4096)
    } else { Seq::empty() }
}

pub open spec fn seed(v: AllocationView, n: u32) -> u32 {
    crc::fold(crc::fold(v.index.seed, group::encoded_le(n)), group::encoded_le(allocated_inode::source_view(v, n).generation))
}

pub open spec fn records(v: AllocationView, n: u32, logical: u32) -> Seq<crate::directory::Entry> {
    directory_block::canonical_records(raw(v, n, logical), v.index.inodes)
}

#[verifier::opaque]
pub open spec fn valid_block(v: AllocationView, n: u32, logical: u32) -> bool {
    let node = allocated_inode::source_view(v, n);
    &&& allocated_inode::valid(node) && node.mode & 0xf000 == 0x4000
    &&& node.size > 0 && node.size % 4096 == 0 && logical < node.size / 4096
    &&& initialized(v, n, logical)
    &&& directory_block::valid(BlockView { raw: raw(v, n, logical), records: records(v, n, logical), inodes: v.index.inodes, seed: seed(v, n) })
}

pub proof fn checked_mapping_and_records_are_the_canonical_source(node: NodeView, logical: u32, block: BlockView)
    requires allocated_inode::valid(node), directory_block::valid(block),
        node.mode & 0xf000 == 0x4000, node.size > 0, node.size % 4096 == 0, logical < node.size / 4096,
        block.inodes == node.volume.index.inodes, block.seed == seed(node.volume, node.number),
        exists|p: u32| #[trigger] file_read::maps(node, logical, p)
            && block.raw == node.volume.index.source.subrange(p as int * 4096, (p as int + 1) * 4096),
    ensures valid_block(node.volume, node.number, logical), block.raw == raw(node.volume, node.number, logical),
        block.records == records(node.volume, node.number, logical),
{
    hide(crc::fold);
    allocated_inode::checked_view_is_the_source_projection(node);
    let p = choose|p: u32| #[trigger] file_read::maps(node, logical, p)
        && block.raw == node.volume.index.source.subrange(p as int * 4096, (p as int + 1) * 4096);
    assert(initialized(node.volume, node.number, logical));
    let q = physical(node.volume, node.number, logical);
    assert(file_read::maps(node, logical, q));
    file_read::initialized_mapping_is_unique(node, logical, p, q);
    assert(block.raw == raw(node.volume, node.number, logical));
    directory_block::checked_block_has_canonical_records(block);
    assert(valid_block(node.volume, node.number, logical)) by { reveal(valid_block); }
}

}
