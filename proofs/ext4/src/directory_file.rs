// SPDX-License-Identifier: MPL-2.0

//! Directory blocks read through an allocated inode's initialized mapping.
//! The checksum seed is derived from the checked filesystem/inode identity;
//! byte provenance is a source-range relation, not a checksum identity claim.

use vstd::prelude::*;
use crate::{allocated_inode::AllocatedInode, crc, directory_piece::{self, Piece}, directory_source, file_read::{self, Chunk}, group, inode};

verus! {

pub fn read<'a>(node: &AllocatedInode<'_, 'a>, logical: u32) -> (r: Option<Piece<'a>>)
    ensures node.wf(), match r {
        Some(block) => block.wf() && node.view().mode & 0xf000 == 0x4000
            && directory_source::valid_block(node.view().volume, node.view().number, logical)
            && block.view().block.raw == directory_source::raw(node.view().volume, node.view().number, logical)
            && block.view().block.records == directory_source::records(node.view().volume, node.view().number, logical)
            && node.view().size > 0 && node.view().size % 4096 == 0 && logical < node.view().size / 4096
            && block.view().block.inodes == node.view().volume.index.inodes
            && block.view().block.seed == crc::fold(crc::fold(node.view().volume.index.seed, group::encoded_le(node.view().number)),
                group::encoded_le(node.view().generation))
            && exists|physical: u32| #[trigger] file_read::maps(node.view(), logical, physical)
                && file_read::owned(node.view(), logical, physical)
                && block.view().block.raw == node.view().volume.index.source.subrange(physical as int * 4096, (physical as int + 1) * 4096),
        None => true,
    },
{
    let info = node.info();
    if info.mode & 0xf000 != 0x4000 || info.size == 0 || info.size % 4096 != 0 || info.size / 4096 > u32::MAX as u64 || logical as u64 >= info.size / 4096 { return None; }
    let bytes = match file_read::chunk(node, logical as u64 * 4096, 4096) {
        Chunk::Data(bytes) => bytes,
        _ => { return None; }
    };
    assert(bytes.len() == 4096);
    let (_, inodes, _, uuid_seed) = node.volume().index().parameters();
    let seed = inode::inode_seed(uuid_seed, node.number(), info.generation);
    let raw = node.raw();
    let indexed = crate::bytes::read_le32(raw, 32).unwrap() & 0x1000 != 0;
    let primary_block = match node.volume().index().source().block(0) { Some(primary) => primary, None => { return None; } };
    let primary = primary_block.as_slice();
    let large = crate::bytes::read_le32(primary, 1120).unwrap() & 0x4000 != 0;
    match directory_piece::parse(bytes, inodes, seed, indexed, logical, (info.size / 4096) as u32, large) {
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
