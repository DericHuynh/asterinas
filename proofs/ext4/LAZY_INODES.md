<!-- SPDX-License-Identifier: MPL-2.0 -->

# Uninitialized inode bitmaps

Linux's `ext4_read_inode_bitmap` treats an INODE_UNINIT group as having no
allocated inodes. It synthesizes an empty logical bitmap with allocated padding
without trusting the physical bitmap. The checked core now implements that
rule in the bounded metadata-checksum profile, for 32- and 64-byte descriptors.

| Boundary | Checked behavior |
| --- | --- |
| Group flags | Flags 0/4 select the physical initialized inode bitmap; 1/5 select INODE_UNINIT, with optional INODE_ZEROED bookkeeping. BLOCK_UNINIT and unknown flags remain rejected. |
| Descriptor admission | Verify the descriptor checksum before using its flags. An uninitialized inode group must be nonzero, report all `inodes_per_group` inodes free, zero used directories and a fully unused inode-table suffix. |
| Logical bitmap | `bitmap::synthesize_free_inodes` returns 4096 initialized bytes, zero bits for every actual inode, allocated padding, and an exact free count. Invalid geometry returns None. Its checksum describes this logical buffer, rather than claiming equality with unused physical checksum fields. |
| Source relation | An initialized inode bitmap retains exact source-byte provenance and the on-disk checksum relation. An INODE_UNINIT bitmap instead equals the canonical synthesized bitmap derived from the same checked descriptor/superblock. Stored inode-bitmap checksums and stale physical bitmap bytes are ignored only in that branch. Block bitmap checks remain active. |
| Lookup | Theorems in bitmap.rs, group_metadata.rs and allocated_inode.rs prove that no inode in an uninitialized group is live. Both allocated inode lookup and bound extent-tree admission reject it before interpreting stale inode contents. |
| Namespace | Directory target admission uses that same logical allocation bitmap. A correctly checksummed directory entry cannot make a stale inode reachable. |
| Group zero | INODE_UNINIT is rejected for group zero, preserving the reserved inode markers and the root/internal journal boundary. |
| Composition | Aggregate inode counters, all reserved physical metadata claims, complete allocation/namespace validation and sealed recovery admission compose with the logical bitmap. The physical inode bitmap/table blocks remain reserved metadata. |

The synthesized buffer is owned safe Rust data. It is a checked host-core
representation, not a Linux page/folio/buffer_head or a CortenMM frame. Actual
CortenMM/OSTD cache, memory, locks and device refinement remain open.

This implements static interpretation. Allocating the first inode requires a
separate proved transaction that initializes the bitmap/table as necessary,
changes counters and clears INODE_UNINIT without exposing stale contents.
Concurrent initialization and background inode-table zeroing are unfinished;
no writable or mounted filesystem is enabled by this change. BLOCK_UNINIT and
legacy GDT_CSUM checksum handling also remain unfinished.

The Linux reference is pinned `fs/ext4/ialloc.c`, recorded in
[sources.json](sources.json). Host tests cover ordinary native two-group images
for all eight combinations of descriptor width, HUGE_FILE and CSUM_SEED.
Additional cases set every physical inode-bitmap bit and install a correctly
checksummed stale file inode; the logical group still has no live inode, and a
directory reference to it fails admission. Other cases cover all padding bits,
invalid geometry, reserved group-zero inodes, inconsistent counters, unknown
flags and restoration of physical bitmap checks after clearing INODE_UNINIT.
Tests complement the Verus proofs and do not prove Linux execution or runtime
filesystem operation preservation.
