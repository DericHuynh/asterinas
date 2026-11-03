// SPDX-License-Identifier: MPL-2.0

//! Directory blocks read through an allocated inode's initialized mapping.
//! The checksum seed is derived from the checked filesystem/inode identity;
//! byte provenance is a source-range relation, not a checksum identity claim.

use vstd::prelude::*;
use crate::{allocated_inode::AllocatedInode, crc, directory_block::{self, DirectoryBlock}, directory_source, file_read::{self, Chunk}, group, inode};

verus! {

pub fn read<'a>(node: &AllocatedInode<'_, 'a>, logical: u32) -> (r: Option<DirectoryBlock<'a>>)
    ensures node.wf(), match r {
        Some(block) => block.wf() && node.view().mode & 0xf000 == 0x4000
            && directory_source::valid_block(node.view().volume, node.view().number, logical)
            && block.view().raw == directory_source::raw(node.view().volume, node.view().number, logical)
            && block.view().records == directory_source::records(node.view().volume, node.view().number, logical)
            && node.view().size > 0 && node.view().size % 4096 == 0 && logical < node.view().size / 4096
            && block.view().inodes == node.view().volume.index.inodes
            && block.view().seed == crc::fold(crc::fold(node.view().volume.index.seed, group::encoded_le(node.view().number)),
                group::encoded_le(node.view().generation))
            && exists|physical: u32| #[trigger] file_read::maps(node.view(), logical, physical)
                && file_read::owned(node.view(), logical, physical)
                && block.view().raw == node.view().volume.index.source.subrange(physical as int * 4096, (physical as int + 1) * 4096),
        None => true,
    },
{
    let info = node.info();
    if info.mode & 0xf000 != 0x4000 || info.size == 0 || info.size % 4096 != 0 || logical >= info.size / 4096 { return None; }
    let bytes = match file_read::chunk(node, logical as u64 * 4096, 4096) {
        Chunk::Data(bytes) => bytes,
        _ => { return None; }
    };
    assert(bytes.len() == 4096);
    let (_, inodes, _, uuid_seed) = node.volume().index().parameters();
    let seed = inode::inode_seed(uuid_seed, node.number(), info.generation);
    match directory_block::parse(bytes, inodes, seed) {
        Some(block) => {
            proof {
                crate::allocated_inode::checked_view_is_the_source_projection(node.view());
                directory_source::checked_mapping_and_records_are_the_canonical_source(node.view(), logical, block.view());
            }
            Some(block)
        },
        None => None,
    }
}

}
