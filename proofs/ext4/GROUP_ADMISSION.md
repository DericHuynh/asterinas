<!-- SPDX-License-Identifier: MPL-2.0 -->

# Complete source-derived group admission

`group_metadata::projection` derives a group's descriptor, physical metadata
addresses, counters, checksum domains and logical bitmaps from one retained
source. Initialized bitmaps use their exact physical bytes. `INODE_UNINIT`
selects the canonical empty inode bitmap with allocated padding;
`BLOCK_UNINIT` selects the canonical reserved-region bitmap. Physical stale
bytes cannot alter either lazy interpretation.

`group_index::projection` derives the geometry and the complete ordered group
sequence from that same source. Its validity predicate checks every group,
the source-selected descriptor width and FLEX_BG placement, and exact agreement
between the group free-counter sums and the primary superblock.

Both executable parsers have checked contracts in both directions:

| Result | Checked relation |
| --- | --- |
| Some | The returned view is valid and equals the unique projection of the requested source. |
| None | The requested source does not satisfy the declared group or index admissibility predicate. |

Every valid group/index view is its source's unique projection. The index loop
additionally proves that its accumulated sequence is exactly the corresponding
source-derived prefix. This connects every group-parser success or failure to
the complete index predicate, including the final free-counter comparisons.
The executable parsing decisions and accepted format are unchanged; the new
proofs establish completeness rather than weakening checks.

The Linux references remain the pinned v7.0 `fs/ext4/balloc.c`, `ialloc.c`,
`bitmap.c` and `super.c` entries in sources.json. In particular,
`ext4_init_block_bitmap` marks only metadata physically inside the selected
group and allocates padding; FLEX_BG does not turn logical group numbers into
physical metadata addresses. The existing global allocation census separately
checks cross-group ownership and aliases.

| Design obligation | Accomplished | Remaining |
| --- | --- | --- |
| F-PARSE | Unique exact descriptor/bitmap projections and complete total executable group/index parsers | Other ext4 features and layouts |
| F-ADMIT | Every source satisfying the declared bounded group/index predicate is accepted | Complete allocation, namespace and recovery-admission completeness |
| F-OWN | Exact initialized/lazy bitmap interpretation and global free-counter sums | Allocation/free/conversion operations and their preservation proofs |
| S-ENTRY | Retained-source, private typed validation results; no checksum-identity premise | CortenMM/OSTD capture, runtime exclusion, device and VFS refinement |

This is a prerequisite for reconstructing complete filesystem admission from
crash bytes. It does not discharge that full theorem. The bounds and feature
profile in FORMAT_PROFILE.md still apply, and kernel mount/write gates remain
closed.
