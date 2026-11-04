<!-- SPDX-License-Identifier: MPL-2.0 -->

# HUGE_FILE and normalized inode accounting

The bounded initialized-group profile admits the optional RO_COMPAT HUGE_FILE
bit (0x0008). It binds size and accounting policies to that bit in the same
checked primary source. Ordinary inode flags remain EXTENTS, optionally with
HUGE_FILE (0x00040000) when the filesystem feature is present. Other feature
masks remain rejected. Kernel mounting and filesystem writes remain disabled.

Linux reference: v7.0 commit `028ef9c96e96197026887c0f092424679298aae8`,
fs/ext4/inode.c blob `1123d995494b588744ba47fcee88e9cd0cc992dd`,
ext4_inode_blocks and ext4_inode_blocks_set.

| Filesystem feature | Inode flag | Decoded i_blocks |
| --- | --- | --- |
| Absent | Clear | Low 32 bits in 512-byte sectors; the current admission profile additionally requires zero high field |
| Present | Clear | Combined 48-bit low/high field in 512-byte sectors |
| Present | Set | Combined 48-bit count of filesystem blocks, normalized by multiplying by block_bytes / 512 |

The field decoder follows Linux's no-feature low-only interpretation. Metadata
admission separately rejects an inode HUGE_FILE flag without the filesystem
feature. Source-bound candidate collection compares normalized sectors with
eight times the complete data-plus-external-metadata block count in the 4 KiB
profile. A unit mismatch, stale high field, alias or bitmap inconsistency cannot
be hidden by setting the inode flag.

The encoder chooses low-only sectors, then 48-bit sectors, then filesystem-block
units. Its result represents the normalized input exactly. The final encoding
requires divisibility by the sectors-per-block factor and a representable
48-bit quotient. Nonaligned values are rejected; this makes explicit the block
alignment invariant expected by Linux's shift-based encoder. The codec proofs
cover all seven modeled block sizes, including overflow bounds and high fields.

HUGE_FILE also changes Linux's regular-file maximum from the 32-bit sector
policy to the extent logical limit. The current 4 KiB maximum is then
`(2^32 - 1) * 4096`, or **16 TiB minus 4 KiB**. Offset and EOF proofs use the
actual feature policy, including the final valid logical block and the reserved
terminal logical block. Directories keep their low-only size policy without
LARGEDIR. Journal inode 8 retains its separately checked ordinary-sector layout.

The physical census still caps the volume at 1,048,576 blocks. Large sparse
logical offsets do not expand that census or enumerate holes. Huge accounting
units do not establish physical write atomicity, frame ownership or DMA rights;
the existing explicit journal device contract and CortenMM integration work
remain separate.

Interoperability tests create a HUGE_FILE filesystem with mke2fs and a maximum
sparse inode with debugfs, then compare the checked reader and e2fsck. Other
cases exercise both accounting units, external-tree metadata, high fields,
alignment/encoding boundaries and inconsistent feature/flag/count combinations.
Mutation preservation, quota coupling, broader geometries and concurrent
runtime/device refinement remain open.
