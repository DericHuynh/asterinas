<!-- SPDX-License-Identifier: MPL-2.0 -->

# Flexible metadata placement

The bounded profile now admits FLEX_BG. Bitmap and inode-table addresses can
lie outside their logical group's physical interval, while remaining within the
filesystem. This choice is always derived from the checked primary superblock.
All physical metadata, data, journal and reserved regions still enter one
disjoint ownership census.

| Boundary | Checked behavior |
| --- | --- |
| Feature selection | `superblock::flex_enabled` and the retained GroupIndex expose the actual source flag. Non-flex images require group-local metadata addresses; flex images require filesystem-wide bounds. |
| Descriptor fields | Both layouts retain descriptor checksums, full bounded address values, local bitmap/table distinctness, inode-table length and per-group counter limits. Allowing wider placement does not widen the logical block bitmap's free-count range. |
| Inode tables | The actual descriptor table address and logical inode group/slot determine the source byte range. Moving the table does not change inode numbering, generation, checksum seed or file ownership. |
| Reserved claims | Every descriptor contributes its actual bitmap/table physical ranges to the global census. Claims from separate logical groups must remain disjoint, including when their metadata is in the same physical group. |
| Logical bitmaps | A block bitmap describes its logical physical-group interval regardless of where the bitmap itself is stored. An initialized bitmap retains physical byte/checksum provenance. BLOCK_UNINIT marks base headers and this group's metadata only where those addresses lie within its physical interval, plus padding. |
| Foreign metadata | Whole-image claim/bitmap agreement still accounts for metadata belonging to other logical groups. A canonical UNINIT bitmap that omits such allocated blocks fails global admission; local bitmap construction is not a whole-volume certificate. |
| Recovery identity | All group address fields and the primary's non-RECOVER incompatibility bits stay fixed. Recovery cannot change the placement interpretation by toggling FLEX_BG. |
| Flex bookkeeping | Linux normalizes `s_log_groups_per_flex` outside 1..31 to zero. The total helper models this independently of metadata placement; no overflowing shift or runtime allocation is performed. |
| Caller boundary | GroupMetadata and GroupIndex sources remain sealed. Negative Rust compilation tests reject metadata forgery and replacement of the retained source. |

The pinned Linux `ext4_check_descriptors` uses global bounds when FLEX_BG is
set, independently of flex allocator bookkeeping. `ext4_fill_flex_info` supplies
the normalization rule. Exact source references are in
[sources.json](sources.json). The implementation is independent safe Rust and
retains the framekernel/CortenMM design boundary; it introduces no Linux
page/folio/buffer_head ownership.

The current geometry/resource limits remain: 4 KiB blocks, at most 32 groups,
32/64-byte descriptors and at most 1,048,576 blocks. META_BG, BIGALLOC, online
resize, allocation/initialization transactions, flex allocation policies,
concurrent filesystem operations and actual CortenMM/OSTD/device refinement
remain open. No mount or filesystem write path is enabled.

Native four-group fixtures cover 32/64-byte descriptors and optional HUGE_FILE
and CSUM_SEED. Bitmap and inode-table blocks for later logical groups lie in
physical group zero. A live file inode is moved to the later group's native
table, reconciled and checked by e2fsck, then read through the checked source
mapping. An external extent-tree file remains part of the complete allocation
and namespace certificate. Negative cases cover out-of-filesystem addresses,
per-group counter overflow, feature switching with a valid superblock checksum,
shared bitmap ownership and UNINIT hiding foreign metadata. All 256 raw flex
bookkeeping bytes are tested with the feature on/off. Tests complement the Verus
proofs and do not establish Linux execution, runtime concurrency or durability.
