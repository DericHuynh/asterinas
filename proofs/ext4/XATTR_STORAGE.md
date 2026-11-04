<!-- SPDX-License-Identifier: MPL-2.0 -->

# Source-bound extended attributes

The bounded host profile admits EXT_ATTR with immutable inode-body values and
single external blocks, including shared external blocks. This is structural
storage and lookup support. It does not implement setxattr/removexattr, ACL-aware
VFS authorization, LSM policy, EA_INODE lifetime, or a mounted filesystem.

The independent Rust implementation references Linux v7.0 commit
`028ef9c96e96197026887c0f092424679298aae8`, `fs/ext4/xattr.c`, `xattr.h`, and
`fs/ext4/ext4.h`. No Linux page, folio or buffer-head ownership is introduced.
CortenMM/OSTD source capture, locking, DMA and device refinement remain required.

| Component | Implemented contract | Remaining work |
| --- | --- | --- |
| `xattr_entry.rs` | Complete namespace/name keys, 16-byte entries, four-byte name/value padding, bounded local slices, no embedded NUL names, empty ACL names, bounded value-inode descriptors | Value inode data/reference/quota lifetime |
| `xattr_table.rs` | Contiguous terminated tables, full-key uniqueness, Linux external sorting, unsorted inode tables, values outside entry/terminator bytes, exact lookup and absence | Mutation, deduplication policy and operation-specific authorization |
| `xattr.rs` | Inode extra-size/body bases, block headers/refcount limits/reserved words, physical-address-bound CRC32C, 48-bit inode pointer and storage accounting | Multiple geometries in full volume admission and EA_INODE integration |
| `xattr_inode.rs` | Same-source inode/body/external-block binding, cross-location key separation, exact get and absent results, uniqueness of selected value | VFS namespace/credential/LSM policy |
| `xattr_source.rs` | Complete active-inode scan, exact shared-block reference count, one canonical claim per shared block, occupied-role preservation | Concurrent CortenMM lifetime and incremental census maintenance |
| `allocation.rs` | Attribute claims composed after data/extent/journal claims, exact bitmap/free counters, per-inode sectors include the external attribute block | Full allocation and mutation semantics |
| `content_write.rs` | Existing mode-only write candidates reject a present POSIX access ACL | ACL-aware writes and full security policy |

The block checksum covers little-endian 64-bit physical identity followed by the
entire block with only the checksum word zeroed. Inline value offsets are based
at the first entry; external offsets are based at the beginning of the block.
Hashes are not used as identity. Local values may overlap one another as Linux
permits; the immutable API grants no independent mutable ownership for them.

The complete global census counts every live ordinary inode and journal inode 8.
A referenced block must be allocated, correctly checksummed and marked EXT_ATTR;
its h_refcount must equal all actual source inode pointers. Canonical kind-7
claims go through the same disjoint physical ledger as data, extent metadata,
reserved tables and journal storage. A candidate parser alone grants no
allocation or filesystem authority.

Full initial/prefix/recovery-image admission uses this extended allocation
validator. Existing journal theorems continue to quantify over all admitted
prefix images under the documented atomic-block/flush/exclusive-source contract;
they do not prove an xattr mutation algorithm or runtime locks.

Native regressions generate Linux inline/external xattrs with debugfs, validate
an explicitly shared-block image with e2fsck, and check source lookup, exact
references, checksum address binding, duplicate cross-location keys, invalid
sector counts, bounds, terminators and EA descriptor feature exclusion. Tests
supplement the pinned entire-crate Verus run; they do not replace it.
