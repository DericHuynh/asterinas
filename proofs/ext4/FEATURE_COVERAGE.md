<!-- SPDX-License-Identifier: MPL-2.0 -->

# Full ext4 feature coverage target

The target is full Linux-compatible ext4 feature coverage, including concurrent
read/write, allocation, commit, checkpoint and recovery. The implementation still
admits only the initial profile in [FORMAT_PROFILE.md](FORMAT_PROFILE.md).
This table expands the target; it does not enable any additional feature.

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
| COMPAT | `0x0008` | `EXT_ATTR` | Not implemented | Inline/external xattrs, ACLs, shared-xattr reference counts and authorization |
| COMPAT | `0x0010` | `RESIZE_INODE` | Not implemented | Reserved GDT inode, online resize and crash-safe geometry changes |
| COMPAT | `0x0020` | `DIR_INDEX` | Not implemented | HTree hashes, collision handling, split/merge and lookup equivalence |
| COMPAT | `0x0200` | `SPARSE_SUPER2` | Not implemented | Explicit backup-group selection and resize/backup updates |
| COMPAT | `0x0400` | `FAST_COMMIT` | Not implemented | Fast-commit records, full-commit interaction, replay and fallback |
| COMPAT | `0x0800` | `STABLE_INODES` | Not implemented | Stable inode identity constraints and incompatible maintenance operations |
| COMPAT | `0x1000` | `ORPHAN_FILE` | Not implemented | Orphan-file allocation, checksums, insertion/removal and restartable reclamation |
| RO_COMPAT | `0x0001` | `SPARSE_SUPER` | Partial: initial profile only | Backup placement over all supported group layouts |
| RO_COMPAT | `0x0002` | `LARGE_FILE` | Partial: 64-bit regular sizes and reads in bounded profile | Source-bound high/low fields and Linux no-HUGE_FILE limits checked; other inode formats/feature combinations and mutations remain |
| RO_COMPAT | `0x0004` | `BTREE_DIR` | Not implemented | Legacy/reserved directory marker and exact Linux acceptance semantics |
| RO_COMPAT | `0x0008` | `HUGE_FILE` | Partial: sizes/accounting in bounded read-only profile | Source feature and inode flag binding, 32/48-bit normalized counts, exact units/encoding and sparse limit checked; larger volumes, mutation and quota coupling remain |
| RO_COMPAT | `0x0010` | `GDT_CSUM` | Not implemented | Legacy descriptor/bitmap checksums and lazy/uninitialized group states |
| RO_COMPAT | `0x0020` | `DIR_NLINK` | Not implemented | Directory link overflow conventions and namespace accounting |
| RO_COMPAT | `0x0040` | `EXTRA_ISIZE` | Partial: initial profile only | Variable inode size, extra fields and checksum coverage |
| RO_COMPAT | `0x0100` | `QUOTA` | Not implemented | Quota inode ownership, usage/reservation and atomic counter transitions |
| RO_COMPAT | `0x0200` | `BIGALLOC` | Not implemented | Cluster bitmap, shared inode clusters, partial-cluster lifecycle and zeroing |
| RO_COMPAT | `0x0400` | `METADATA_CSUM` | Partial: initial profile only | All metadata checksum domains and every compatible layout |
| RO_COMPAT | `0x1000` | `READONLY` | Not implemented | Read-only feature semantics and prohibition of persistent mutation |
| RO_COMPAT | `0x2000` | `PROJECT` | Not implemented | Project IDs, inheritance, project quota and authorization |
| RO_COMPAT | `0x8000` | `VERITY` | Not implemented | Merkle metadata, immutable content and explicit cryptographic assumptions |
| RO_COMPAT | `0x10000` | `ORPHAN_PRESENT` | Not implemented | Recovery state and orphan-file emptiness/retirement rules |
| INCOMPAT | `0x0001` | `COMPRESSION` | Not implemented | Legacy unsupported marker; match pinned Linux rejection policy |
| INCOMPAT | `0x0002` | `FILETYPE` | Partial: initial profile only | All inode/dirent types, including symlinks and special files |
| INCOMPAT | `0x0004` | `RECOVER` | Partial: initial profile only | Dirty/clean transitions with concurrent commit/checkpoint/recovery |
| INCOMPAT | `0x0008` | `JOURNAL_DEV` | Not implemented | External journal device identity, bounds, exclusion and exclusivity |
| INCOMPAT | `0x0010` | `META_BG` | Not implemented | Distributed descriptor locations and reserved regions across resize |
| INCOMPAT | `0x0040` | `EXTENTS` | Partial: owned read-only trees in bounded profile | 48-bit addresses, depth-0..5 trees, insert/split/merge/truncate and conversion |
| INCOMPAT | `0x0080` | `64BIT` | Not implemented | 64-bit block counts/addresses and extended descriptors/bitmaps |
| INCOMPAT | `0x0100` | `MMP` | Not implemented | Multiple-mount protection, leases, failure assumptions and heartbeat ordering |
| INCOMPAT | `0x0200` | `FLEX_BG` | Not implemented | Cross-group bitmap/table placement and globally disjoint ownership |
| INCOMPAT | `0x0400` | `EA_INODE` | Not implemented | Value inode lifetime, references, deduplication and quota coupling |
| INCOMPAT | `0x1000` | `DIRDATA` | Not implemented | Non-mainline/legacy marker; match pinned Linux rejection policy |
| INCOMPAT | `0x2000` | `CSUM_SEED` | Partial: bounded metadata and journal domain composition | Stored or UUID-derived ext4 seed, independent internal-journal UUID, exact recovery flag preservation and native UUID-change interoperability checked; remaining metadata types, mutation and runtime refinement remain |
| INCOMPAT | `0x4000` | `LARGEDIR` | Not implemented | Large directories, additional HTree depth and record/size bounds |
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

