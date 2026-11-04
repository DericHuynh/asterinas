// SPDX-License-Identifier: MPL-2.0

//! Finite physical block maps and exact byte projections of an immutable source.
//! Disk addresses are not CortenMM memory-frame capabilities.

use vstd::prelude::*;
use crate::{journal_view, layout::LayoutView, replay_refinement::Disk};

verus! {

pub open spec fn source_block(source: Seq<u8>, block: u32) -> Seq<u8> {
    if (block as nat + 1) * 4096 <= source.len() { source.subrange(block as int * 4096, (block as int + 1) * 4096) }
    else { Seq::empty() }
}

pub open spec fn initial_disk(source: Seq<u8>, blocks: u32) -> Disk {
    Map::new(Seq::new(blocks as nat, |i: int| i as u32).to_set(), |block: u32| source_block(source, block))
}

pub proof fn initial_disk_addresses_are_exactly_the_filesystem_range(source: Seq<u8>, blocks: u32, block: u32)
    ensures initial_disk(source, blocks).dom().contains(block) == (block < blocks),
{
    let addresses = Seq::new(blocks as nat, |i: int| i as u32);
    if block < blocks {
        assert(addresses[block as int] == block);
        assert(addresses.contains(block));
    } else if addresses.contains(block) {
        let i = choose|i: int| 0 <= i < addresses.len() && addresses[i] == block;
        assert(i as u32 == i);
    }
}

pub open spec fn flat_bytes(disk: Disk, source: Seq<u8>, blocks: u32) -> Seq<u8> {
    Seq::new(source.len(), |i: int| {
        if i < blocks as nat * 4096 {
            let block = (i / 4096) as u32;
            if disk.dom().contains(block) && i % 4096 < disk[block].len() { disk[block][i % 4096] } else { 0u8 }
        } else { source[i] }
    })
}

pub proof fn initial_block_map_has_the_exact_source_bytes(source: Seq<u8>, blocks: u32, block: u32)
    requires blocks as nat * 4096 <= source.len(), block < blocks,
    ensures initial_disk(source, blocks).dom().contains(block), initial_disk(source, blocks)[block].len() == 4096,
        initial_disk(source, blocks)[block] == source.subrange(block as int * 4096, (block as int + 1) * 4096),
{
    initial_disk_addresses_are_exactly_the_filesystem_range(source, blocks, block);
}

pub proof fn flat_projection_preserves_partition_bytes_beyond_the_filesystem(disk: Disk, source: Seq<u8>, blocks: u32, index: int)
    requires blocks as nat * 4096 <= index < source.len(),
    ensures flat_bytes(disk, source, blocks).len() == source.len(), flat_bytes(disk, source, blocks)[index] == source[index],
{
}

pub proof fn a_flat_source_has_the_exact_mapped_journal(source: Seq<u8>, layout: LayoutView)
    requires journal_view::geometry(layout), layout.fs_blocks as nat * 4096 <= source.len(),
    ensures journal_view::mapped(initial_disk(source, layout.fs_blocks), layout),
        journal_view::snapshot(initial_disk(source, layout.fs_blocks), layout)
            == source.subrange(layout.start as int * 4096, (layout.start as int + layout.journal_blocks) * 4096),
{
    let disk = initial_disk(source, layout.fs_blocks);
    assert forall|logical: u32| logical < layout.journal_blocks implies
        #[trigger] disk.dom().contains((layout.start + logical) as u32)
        && disk[(layout.start + logical) as u32].len() == 4096 by {
        initial_block_map_has_the_exact_source_bytes(source, layout.fs_blocks, (layout.start + logical) as u32);
    }
    assert(journal_view::snapshot(disk, layout) =~= source.subrange(layout.start as int * 4096,
        (layout.start as int + layout.journal_blocks) * 4096)) by {
        assert forall|i: int| 0 <= i < layout.journal_blocks as nat * 4096 implies
            #[trigger] journal_view::snapshot(disk, layout)[i] == source[layout.start as int * 4096 + i] by {
            let logical = (i / 4096) as u32;
            initial_block_map_has_the_exact_source_bytes(source, layout.fs_blocks, (layout.start + logical) as u32);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, 4096);
        }
    }
}

}
