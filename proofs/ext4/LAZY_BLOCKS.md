<!-- SPDX-License-Identifier: MPL-2.0 -->

# Uninitialized block bitmaps

The bounded non-FLEX_BG/non-META_BG profile now implements Linux's
BLOCK_UNINIT interpretation. Physical bitmap bytes and their unused checksum
do not define allocation in this state. The checked descriptor instead defines
a canonical logical bitmap containing reserved metadata and allocated padding.

| Component | Checked relation |
| --- | --- |
| Base metadata | Sparse-super groups reserve the first two blocks for superblock/GDT. Other groups have no base header reservation. The bounded sparse-super set is already proved equivalent to Linux's power rule. |
| Group metadata | Block/inode bitmap addresses and the entire inode-table interval are allocated bits. Addresses come from the checked same-source descriptor. |
| Data and padding | Every other real group bit is free; bits beyond a partial group's end are allocated. The byte packing proof establishes the exact meaning of every bit. |
| Free count | The synthesizer computes the canonical buffer and validates its exact free count against the descriptor. Its public admission predicate is exact: admitted bounded descriptors with that count succeed; rejection means that predicate is false. |
| Metadata claims | Every set real bit has a covering reserved metadata claim. Whole-image disjoint claim/bitmap agreement then prevents interpreting those bits as ordinary file data, inode-owned extent metadata or journal storage. |
| Checksums | The descriptor checksum is always checked. Initialized bitmaps retain their physical source and 16/32-bit on-disk checksum relation. BLOCK_UNINIT selects the canonical buffer and its logical checksum; only that physical block-bitmap checksum is ignored. |
| Combined flags | Flags 0 through 7 admit initialized/uninitialized block and inode bitmaps plus optional INODE_ZEROED bookkeeping. INODE_UNINIT's group-zero and all-free-inode restrictions still apply. Unknown flags fail admission. |
| Composition | Complete allocation, source-derived metadata claims, aggregate counters, static namespace and sealed recovery admission all consume the same logical bitmap. |

Linux references are `ext4_init_block_bitmap`, `ext4_free_clusters_after_init`
and related reserved-region logic in pinned `fs/ext4/balloc.c`; exact blobs are
recorded in [sources.json](sources.json). The implementation is independent safe
Rust and introduces no Linux memory ownership model.

This is static interpretation. First allocation must atomically initialize the
physical bitmap, update allocation/free counters and clear BLOCK_UNINIT as part
of a proved filesystem transaction. Concurrent initialization, general allocator
operations, FLEX_BG/META_BG/BIGALLOC and legacy GDT_CSUM remain open. The host
buffers do not establish CortenMM/OSTD cache, guard, DMA or device refinement.
No mount or filesystem write path is enabled.

Host tests compare every bitmap bit against independently constructed reserved
address sets over 32/64-byte descriptors, sparse and non-sparse groups, four
inode geometries, full groups and partial-byte/group padding. Native four-group
fixtures cover all eight width/HUGE_FILE/CSUM_SEED combinations. They also cover
stale physical block/inode bitmap bytes, initialized-inode/uninitialized-block
combinations, restored physical checks after clearing BLOCK_UNINIT, and valid
local bitmap unions that global ownership rejects because of GDT aliases or
hidden allocated journal blocks. Tests complement the Verus proofs and do not
prove Linux execution or runtime durability.
