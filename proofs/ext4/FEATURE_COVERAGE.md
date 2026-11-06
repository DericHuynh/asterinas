<!-- SPDX-License-Identifier: MPL-2.0 -->

# Full ext4 feature coverage target

The target is full Linux-compatible ext4 feature coverage, including concurrent
read/write, allocation, commit, checkpoint and recovery. The implementation still
admits the bounded, explicitly extended profile in [FORMAT_PROFILE.md](FORMAT_PROFILE.md).
This table expands the target; it does not enable any additional feature.
The [EA-enabled namespace composition](EA_NAMESPACE.md) is included in the
pinned complete verification and compilation run. It remains an immutable
bounded source certificate; full EA filesystem and mount admission remain open.
The separate [concurrent namespace mutation slice](NS_MUTATION.md) is checked
for bounded same-parent NOREPLACE host preparation and exclusive version-checked
publication. It does not enable a mount or durable EA writer.

The inventory is pinned to Linux v7.0 commit
`028ef9c96e96197026887c0f092424679298aae8`, `fs/ext4/ext4.h`, blob
`7617e2d454ea516fee9047366458c0bda568fddf`. There are 40 named numeric feature
bits. A partial result inside the initial combined profile does not prove that
bit independently or its combinations with other features. Unknown bits remain
rejected until their semantics and interaction proofs are defined. Legacy or
unsupported markers need Linux-compatible handling, not invented encodings.

| Class | Bit | Feature | Current status | Required implementation and proof scope |
| --- | --- | --- | --- | --- |
| COMPAT | `0x0001` | `DIR_PREALLOC` | Not implemented | Preallocation representation and compatibility with allocation/reclamation |
| COMPAT | `0x0002` | `IMAGIC_INODES` | Not implemented | Legacy inode interpretation and Linux-compatible acceptance/rejection policy |
| COMPAT | `0x0004` | `HAS_JOURNAL` | Partial: initial profile only | All JBD2 journal versions/features and concurrent transaction lifecycle |
| COMPAT | `0x0008` | `EXT_ATTR` | Partial: source-bound storage, bounded user lifecycle, ACL updates/chmod and creation planning | CREATE/REPLACE/removal/empty/resize, packing, block reuse/COW/release, counters/CRCs, byte authority and journalled first-feature promotion with all-home crash closure checked in XATTR_UPDATES.md. POSIX_ACL.md specifies access/default mode coupling, owner/SGID policies, chmod transformation/storage and immutable parent-bound inheritance plans. Exact checked source is recorded in verification evidence. EA_INODE, quotas, trusted/security mutation, atomic child creation, VFS/idmap/LSM and kernel/CortenMM integration remain open |
| COMPAT | `0x0010` | `RESIZE_INODE` | Not implemented | Reserved GDT inode, online resize and crash-safe geometry changes |
| COMPAT | `0x0020` | `DIR_INDEX` | Partial: complete source-bound immutable admission in bounded profile | Exact source-owned tree, canonical namespace projection, all six unkeyed hashes, inherited collision ranges, Linux candidate-path closure, unique full names and complete source absence checked in HTREE_ADMISSION.md; a bounded same-leaf NOREPLACE rename path with full final HTree validation is checked in NS_MUTATION.md; insert/delete/split/merge/journal operations, other formats and runtime integration remain open |
| COMPAT | `0x0200` | `SPARSE_SUPER2` | Partial: source-selected backup placement, census and lazy bitmap integration | Exact Linux explicit-group precedence, non-sparse/classic alternatives, all admitted group claims/counters and source framing checked in FEATURE_POLICY.md; backup updates during resize remain open |
| COMPAT | `0x0400` | `FAST_COMMIT` | Not implemented | Fast-commit records, full-commit interaction, replay and fallback |
| COMPAT | `0x0800` | `STABLE_INODES` | Partial: admitted fixed-geometry identity policy | Source flags retained and UUID/geometry preserved through admitted primary updates; resize, offline renumbering and encryption-specific constraints remain open (FEATURE_POLICY.md) |
| COMPAT | `0x1000` | `ORPHAN_FILE` | Not implemented | Orphan-file allocation, checksums, insertion/removal and restartable reclamation |
| RO_COMPAT | `0x0001` | `SPARSE_SUPER` | Partial: initial profile only | Backup placement over all supported group layouts |
| RO_COMPAT | `0x0002` | `LARGE_FILE` | Partial: 64-bit regular sizes and reads in bounded profile | Source-bound high/low fields and Linux no-HUGE_FILE limits checked; other inode formats/feature combinations and mutations remain |
| RO_COMPAT | `0x0004` | `BTREE_DIR` | Implemented legacy marker admission in bounded profile | Pinned Linux RO_COMPAT marker accepted; this does not enable DIR_INDEX/HTree formats |
| RO_COMPAT | `0x0008` | `HUGE_FILE` | Partial: sizes/accounting in bounded read-only profile | Source feature and inode flag binding, 32/48-bit normalized counts, exact units/encoding and sparse limit checked; larger volumes, mutation and quota coupling remain |
| RO_COMPAT | `0x0010` | `GDT_CSUM` | Not implemented | Legacy descriptor/bitmap checksums and lazy/uninitialized group states |
| RO_COMPAT | `0x0020` | `DIR_NLINK` | Partial: source-bound sentinel/count and namespace semantics | Unknown directory count=1, exact regular counts, unchanged full topology checks and total overflow/decrement helpers checked; HTree mutation, count-sentinel transitions, create/final-unlink/rmdir and runtime operations remain open (FEATURE_POLICY.md) |
| RO_COMPAT | `0x0040` | `EXTRA_ISIZE` | Partial: initial profile only | Variable inode size, extra fields and checksum coverage |
| RO_COMPAT | `0x0100` | `QUOTA` | Not implemented | Quota inode ownership, usage/reservation and atomic counter transitions |
| RO_COMPAT | `0x0200` | `BIGALLOC` | Not implemented | Cluster bitmap, shared inode clusters, partial-cluster lifecycle and zeroing |
| RO_COMPAT | `0x0400` | `METADATA_CSUM` | Partial: bounded source metadata and lazy inode groups | Checked checksum domains, extended descriptor/bitmap checks and INODE_UNINIT/BLOCK_UNINIT logical bitmap semantics; remaining metadata/layouts and mutation/initialization protocols remain |
| RO_COMPAT | `0x1000` | `READONLY` | Partial: complete fresh-writer exclusion and committed recovery in host profile | Source flag retained; all raw/sealed serial/window factories reject before I/O; committed recovery validates repaired image and retains marker; actual mount/device/VFS refinement remains open (FEATURE_POLICY.md) |
| RO_COMPAT | `0x2000` | `PROJECT` | Not implemented | Project IDs, inheritance, project quota and authorization |
| RO_COMPAT | `0x8000` | `VERITY` | Not implemented | Merkle metadata, immutable content and explicit cryptographic assumptions |
| RO_COMPAT | `0x10000` | `ORPHAN_PRESENT` | Not implemented | Recovery state and orphan-file emptiness/retirement rules |
| INCOMPAT | `0x0001` | `COMPRESSION` | Implemented pinned Linux rejection policy | Named bit-vector proof and structural admission reject this unsupported INCOMPAT marker |
| INCOMPAT | `0x0002` | `FILETYPE` | Partial: initial profile only | All inode/dirent types, including symlinks and special files |
| INCOMPAT | `0x0004` | `RECOVER` | Partial: bounded concurrent-window dirty/activation/retirement, actual scanner/repeated-recovery closure, fresh bootstrap discovery and guarded full prefix/recovery-image admission under explicit device contracts | Full image/recovery acceptance completeness, runtime CortenMM/device refinement and clean unmount |
| INCOMPAT | `0x0008` | `JOURNAL_DEV` | Not implemented | External journal device identity, bounds, exclusion and exclusivity |
| INCOMPAT | `0x0010` | `META_BG` | Not implemented | Distributed descriptor locations and reserved regions across resize |
| INCOMPAT | `0x0040` | `EXTENTS` | Partial: owned read-only trees in bounded profile | 48-bit addresses, depth-0..5 trees, insert/split/merge/truncate and conversion |
| INCOMPAT | `0x0080` | `64BIT` | Partial: wide field codecs and bounded 64-byte descriptors | Exact high/low addresses/counters, complete descriptor/full bitmap checksums, source stride and recovery identity checked; high-address volumes, other widths and mutations remain |
| INCOMPAT | `0x0100` | `MMP` | Not implemented | Multiple-mount protection, leases, failure assumptions and heartbeat ordering |
| INCOMPAT | `0x0200` | `FLEX_BG` | Partial: bounded source-selected metadata placement | Global bitmap/table bounds, logical group counters, retained inode addressing, lazy bitmap composition and global disjoint claims checked; flex allocation, resize and mounted concurrent mutation remain |
| INCOMPAT | `0x0400` | `EA_INODE` | Partial complete bounded reference, payload, global allocation and immutable namespace composition; full filesystem admission still rejects the feature | EA_INODE.md, EA_REFERENCE_CENSUS.md and EA_VALUE_INTEGRITY.md cover modern metadata/refwords, complete source entries, physical counts, logical charges, exact source-node/payload/entry hashes and complete EA tree/sectors. EA_ALLOCATION.md adds fixed metadata and journal ownership, every allocated ordinary inode's complete extent claims, exact parent physical residual, distinct external blocks and exact source bitmap/counter equality. EA_NAMESPACE.md adds exact ordinary nodes, complete source-owned linear/HTree directories, full-key source lookup/absence, typed generations, exact links and rooted directory/regular-file reachability in the checked bounded profile. Recorded evidence determines the exact source and scope. NS_MUTATION.md checks bounded host same-parent NOREPLACE preparation and version-checked publication with exact entry/byte framing and complete EA namespace readmission. CROSS_DIRECTORY_NAMESPACE.md adds bounded existing-linear-block cross-parent moves, regular hard links and nonlast regular unlinks with exact edge transformations, dotdot/parent counts and ancestry exclusion. Actual JBD2 admission, full EA filesystem admission, allocation/orphan/quota/dedup lifecycle, durable mutation and CortenMM/kernel integration remain open. All writer and mount gates remain closed |
| INCOMPAT | `0x1000` | `DIRDATA` | Implemented pinned Linux rejection policy | Named bit-vector proof and structural admission reject this unsupported INCOMPAT marker |
| INCOMPAT | `0x2000` | `CSUM_SEED` | Partial: bounded metadata and journal domain composition | Stored or UUID-derived ext4 seed, independent internal-journal UUID, exact recovery flag preservation and native UUID-change interoperability checked; remaining metadata types, mutation and runtime refinement remain |
| INCOMPAT | `0x4000` | `LARGEDIR` | Partial: source-selected additional HTree depth in bounded immutable profile | Full source/name/namespace admission through two internal index levels, explicit source-feature depth bound and physical no-alias theorem; Linux e2fsck validates a deep fixture and existing timed regular-file writes preserve admission. Large-size geometries, index growth/split/merge, indexed structural or durable directory mutations and runtime remain open (HTREE_ADMISSION.md) |
| INCOMPAT | `0x8000` | `INLINE_DATA` | Not implemented | Inline file/directory storage, xattr coupling and crash-safe conversion |
| INCOMPAT | `0x10000` | `ENCRYPT` | Not implemented | Key/credential boundary, encrypted names/data, nonce lifetime and explicit crypto assumptions |
| INCOMPAT | `0x20000` | `CASEFOLD` | Not implemented | Pinned Unicode normalization, encrypted/casefold lookup and HTree equivalence |

Read-only extent-tree helpers check complete structural trees and lookup
equivalence at depths zero through five over 1–64 KiB blocks. The bounded 4 KiB
whole-image validator now binds inode/feature/source identity, complete metadata
and data ownership, sector counts and structural reads; see
[EXTENT_TREES.md](EXTENT_TREES.md). Other geometries/features, mutations and
concurrent runtime refinement remain open.

The bit inventory is only one part of full compatibility. Additional coverage
includes power-of-two 1 through 64 KiB block geometry where supported by the target architecture,
128-byte and larger inodes, legacy direct/indirect block maps, full extent-tree
checksums, all inode types, journal-free operation, external journals, legacy
JBD/JBD2 checksum/tag formats, 64-bit tags, async commit, all data modes, orphan
lists, fsync/fdatasync/directory fsync, error handling, mount/remount and unmount.
Supported block-size choices must be validated against Asterinas/OSTD and format
limits; filesystem blocks and CortenMM frames are distinct objects.

Each feature needs parser/admission, byte codec, ownership, operation,
concurrency, crash/recovery and interoperability evidence. Feature combinations
need explicit dependency/conflict checks and invariant preservation; checking
bits individually is insufficient. Read-only compatibility and writable
compatibility must be stated separately. Configuration-dependent Linux features
must preserve their documented unavailable/unsupported behavior.

The fixed bootstrap geometry policy in the initial core is not a proof of
online resize, journal relocation or distributed descriptor updates. Those
operations need a versioned bootstrap/recovery design before changing geometry.
Cryptographic primitives, trusted key sources, hardware and scheduler contracts
must be explicit; arithmetic or CRC proofs do not establish authenticity,
confidentiality or scheduler fairness.

[CONCURRENCY.md](CONCURRENCY.md) defines the expanded block, extent and transaction
model and the current proof boundaries.

