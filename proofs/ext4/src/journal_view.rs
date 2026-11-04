// SPDX-License-Identifier: MPL-2.0

//! Byte projection of a physical block map into the scanner's frozen journal.
//! The projection is total; mapped supplies the actual initialized disk relation.

use vstd::prelude::*;
use crate::{bytes, layout::LayoutView, replay_refinement::Disk, ring, scan};

verus! {

pub open spec fn geometry(layout: LayoutView) -> bool {
    layout.start > 1 && 1024 <= layout.journal_blocks <= 32768
        && layout.start as int + layout.journal_blocks <= layout.fs_blocks
}

pub open spec fn mapped(disk: Disk, layout: LayoutView) -> bool {
    &&& geometry(layout)
    &&& (forall|logical: u32| logical < layout.journal_blocks ==>
        #[trigger] disk.dom().contains((layout.start + logical) as u32)
        && disk[(layout.start + logical) as u32].len() == 4096)
}

pub open spec fn snapshot(disk: Disk, layout: LayoutView) -> Seq<u8> {
    Seq::new(layout.journal_blocks as nat * 4096, |i: int| {
        let block = (layout.start as int + i / 4096) as u32;
        if disk.dom().contains(block) && i % 4096 < disk[block].len() {
            disk[block][i % 4096]
        } else { 0u8 }
    })
}

pub proof fn equal_journal_blocks_have_equal_snapshots(a: Disk, b: Disk, layout: LayoutView)
    requires mapped(a, layout), mapped(b, layout),
        forall|logical: u32| logical < layout.journal_blocks ==>
            (#[trigger] a[(layout.start + logical) as u32]) == b[(layout.start + logical) as u32],
    ensures snapshot(a, layout) == snapshot(b, layout),
{
    assert(snapshot(a, layout) =~= snapshot(b, layout)) by {
        assert forall|i: int| 0 <= i < layout.journal_blocks as nat * 4096 implies
            #[trigger] snapshot(a, layout)[i] == snapshot(b, layout)[i] by {
            let logical = (i / 4096) as u32;
            assert(a[(layout.start + logical) as u32] == b[(layout.start + logical) as u32]);
        }
    }
}

pub proof fn snapshot_block_is_the_physical_image(disk: Disk, layout: LayoutView, logical: u32)
    requires mapped(disk, layout), logical < layout.journal_blocks,
    ensures snapshot(disk, layout).subrange(logical as int * 4096, (logical as int + 1) * 4096)
        == disk[(layout.start + logical) as u32],
{
    assert(disk.dom().contains((layout.start + logical) as u32));
    assert(snapshot(disk, layout).subrange(logical as int * 4096, (logical as int + 1) * 4096)
        =~= disk[(layout.start + logical) as u32]) by {
        assert forall|i: int| 0 <= i < 4096 implies
            snapshot(disk, layout)[logical as int * 4096 + i] == #[trigger] disk[(layout.start + logical) as u32][i] by {
            assert((logical as int * 4096 + i) / 4096 == logical);
            assert((logical as int * 4096 + i) % 4096 == i);
        }
    }
}

pub proof fn scanned_block_is_the_reserved_ring_image(disk: Disk, layout: LayoutView, start: u32, ordinal: u32)
    requires mapped(disk, layout), 1 <= start < layout.journal_blocks, ordinal < layout.journal_blocks - 1,
    ensures scan::block_at(snapshot(disk, layout), layout.journal_blocks, start, ordinal)
        == disk[(layout.start as int + ring::position(1, layout.journal_blocks, start, ordinal)) as u32],
{
    let logical = ring::position(1, layout.journal_blocks, start, ordinal);
    assert(1 <= logical < layout.journal_blocks);
    snapshot_block_is_the_physical_image(disk, layout, logical as u32);
}

pub proof fn writing_a_journal_block_splices_exactly_one_image(disk: Disk, layout: LayoutView, logical: u32, image: Seq<u8>)
    requires mapped(disk, layout), logical < layout.journal_blocks, image.len() == 4096,
    ensures mapped(disk.insert((layout.start + logical) as u32, image), layout),
        snapshot(disk.insert((layout.start + logical) as u32, image), layout)
            == bytes::splice(snapshot(disk, layout), logical as int * 4096, image),
{
    let after = disk.insert((layout.start + logical) as u32, image);
    assert forall|j: u32| j < layout.journal_blocks implies
        #[trigger] after.dom().contains((layout.start + j) as u32) && after[(layout.start + j) as u32].len() == 4096 by {
        assert(disk.dom().contains((layout.start + j) as u32));
    }
    assert(snapshot(after, layout) =~= bytes::splice(snapshot(disk, layout), logical as int * 4096, image)) by {
        assert forall|i: int| 0 <= i < layout.journal_blocks as int * 4096 implies
            #[trigger] snapshot(after, layout)[i]
                == bytes::splice(snapshot(disk, layout), logical as int * 4096, image)[i] by {
            assert(0 <= i / 4096 < layout.journal_blocks);
            assert(disk.dom().contains((layout.start as int + i / 4096) as u32));
            if i / 4096 == logical { assert(i % 4096 == i - logical as int * 4096); }
            else { assert((layout.start as int + i / 4096) as u32 != (layout.start + logical) as u32); }
        }
    }
}

pub proof fn nonjournal_write_preserves_every_journal_byte(disk: Disk, layout: LayoutView, block: u32, image: Seq<u8>)
    requires mapped(disk, layout), block < layout.start || block >= layout.start as int + layout.journal_blocks,
    ensures mapped(disk.insert(block, image), layout), snapshot(disk.insert(block, image), layout) == snapshot(disk, layout),
{
    let after = disk.insert(block, image);
    assert forall|j: u32| j < layout.journal_blocks implies
        #[trigger] after.dom().contains((layout.start + j) as u32) && after[(layout.start + j) as u32].len() == 4096 by {
        assert(disk.dom().contains((layout.start + j) as u32));
        assert(block != (layout.start + j) as u32);
    }
    assert(snapshot(after, layout) =~= snapshot(disk, layout)) by {
        assert forall|i: int| 0 <= i < layout.journal_blocks as int * 4096 implies
            #[trigger] snapshot(after, layout)[i] == snapshot(disk, layout)[i] by {
            assert(0 <= i / 4096 < layout.journal_blocks);
            assert(block != (layout.start as int + i / 4096) as u32);
        }
    }
}

}
