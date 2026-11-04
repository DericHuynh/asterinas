<!-- SPDX-License-Identifier: MPL-2.0 -->

# Source-selected ext4 feature semantics

This batch expands actual admission and recovery in the bounded filesystem
profile. It implements backup selection for SPARSE_SUPER2 and non-sparse layouts,
DIR_NLINK count interpretation, READONLY write exclusion, and admission of the
STABLE_INODES and legacy BTREE_DIR markers. It does not complete the full ext4
implementation. FEATURE_COVERAGE.md keeps the remaining feature and operation
requirements explicit; all production/full-feature/mount gates remain false.

## Exact feature policy

`feature_policy.rs` checks COMPAT, RO_COMPAT and INCOMPAT masks separately.
HAS_JOURNAL, LARGE_FILE, EXTRA_ISIZE, METADATA_CSUM, FILETYPE and EXTENTS remain
required. Unknown and unimplemented bits remain rejected. The supported optional
bits compose with HUGE_FILE, CSUM_SEED, bounded 64BIT descriptors, FLEX_BG and
RECOVER. METADATA_CSUM and legacy GDT_CSUM are not silently conflated.
COMPRESSION and DIRDATA match the pinned Linux unsupported-INCOMPAT policy.

Parsed `Superblock` values now retain all three exact source feature masks and
expose the read-only property. Retaining the flags prevents a structural header
consumer from losing the policy information. A parsed header still conveys no
mount, write, VFS permission or device authority.

## Backup placement affects ownership

Linux `ext4_bg_has_super` first reserves group zero. SPARSE_SUPER2 then selects
only the two recorded backup groups, independently of the classic sparse bit.
Without SPARSE_SUPER2, a non-sparse volume has a backup in every group; classic
SPARSE_SUPER selects group one and powers of three, five and seven.
Out-of-range, duplicate or disabled explicit slots cannot produce an out-of-range
physical claim: selection tests only the current admitted group coordinate.

The exact source-derived selection now drives both `allocation::reserved` and
the synthesized BLOCK_UNINIT bitmap. Reserving the correct backups only in the
census would leave lazy groups inconsistent; changing only the bitmaps could
allow a file or journal to alias a backup. Each selected group contributes two
reserved blocks in this profile: one superblock and one descriptor block. The
32-group bound and 32/64-byte descriptors make one descriptor block sufficient.
META_BG, reserved-GDT growth and resize remain rejected.

The generalized reservation and synthesis functions prove success/rejection
against the exact chosen claims, preserve prior occupied blocks and counters,
and explain every real canonical set bit with a reserved claim. Source-bound
allocation builders supply the actual superblock selection. Legacy sparse-only
helpers retain their existing explicit-profile contracts.

Every admitted primary update preserves the backup selection fields and feature
flags, so journal replay cannot change the allocator's interpretation of a
physical group. Filesystem block coordinates remain distinct from CortenMM frames.

## DIR_NLINK preserves topology checks

With DIR_NLINK set, directory `i_links_count == 1` means the stored count is
unknown. It never means one actual directory reference. Namespace admission
accepts that sentinel only for directories with at least two references. Other
directory counts and every regular-file count remain exact, regardless of the
feature bit. Dot/dotdot, unique parents, rootedness, type checks and rejection of
orphaned files remain unchanged and continue through the same full validator.

The total count helpers implement Linux's indexed-directory overflow sentinel at
EXT4_LINK_MAX=65000 and preserve it while decrementing. These are codecs and
checked transitions; they do not implement mkdir, HTree mutation or inode locks.
The full HTree/create/unlink lifecycle remains open.

## READONLY distinguishes new work from recovery

Static allocation/directory/namespace inspection accepts the READONLY marker.
Both raw serial writer and concurrent-window factories reject it before issuing
requests. Their validated-program invariants and named proofs establish that an
owned fresh writer cannot originate on a READONLY source. The sealed filesystem
admission wrappers inherit that exclusion, and private fields prevent replacing
the engine after validation.

Recovery of a committed journal remains available. Linux can recover while
mounting read-only; the READONLY marker is not an instruction to skip the log.
Actual recovery scans the source journal and validates the complete repaired
shadow before returning requests. Recovery bookkeeping and replay preserve the
source policy bits. A successful recovery can therefore restore committed data
without granting authority for a new transaction. Actual mount/device permissions
and CortenMM/OSTD adapters remain separate obligations.

STABLE_INODES is admitted within the fixed-geometry profile. Primary identity
preservation proves that UUID, size and the stable marker cannot change across
admitted updates. Resizing, offline inode renumbering and encryption-specific
stable-identity policies are not introduced. BTREE_DIR is the pinned Linux legacy
RO_COMPAT marker; it does not enable unimplemented DIR_INDEX/HTree formats.

## Design and proof table

| Obligation | Checked implementation | Remaining boundary |
| --- | --- | --- |
| F-ADMIT | Exact feature masks, retained source flags, total Some/None structural admission and rejected unsupported bits | Other ext4 features, full-image acceptance completeness and all feature interactions |
| F-OWN / F-ADMIT | Actual backup selection composes through reservations, initialized bitmaps, canonical lazy bitmaps, counters and global disjoint ownership | META_BG, resize, reserved-GDT growth, wider geometry and high-address volumes |
| F-NAME | Source-selected DIR_NLINK sentinel with exact regular counts and complete existing parent/dot/root proofs | HTree operations, create/unlink and runtime publication |
| J-BOOT / J-RESTART | Recovery retains feature policy; backup coordinates survive primary framing; a committed READONLY journal can be repaired | Device reset/capture, mount integration and full recovery admission completeness |
| C-COMMIT / S-AUTH | All raw/sealed fresh writer factories refuse READONLY; source/images/certificates remain bound | VFS authorization, actual locks/BIOs, CortenMM and device refinement |

The source implementation and Verus proofs are independent. References are pinned
Linux `ext4_bg_has_super`, `ext4_feature_set_ok`, `ext4_inc_count` and
`ext4_dec_count`; exact blobs and reviewed ranges are recorded in sources.json.
Native tests use Linux-created three-group filesystems with all-group, classic,
explicit, disabled-explicit, and 64BIT/FLEX_BG backup configurations; 32 source
feature combinations; unknown-bit rejection; DIR_NLINK corruption; all four raw
and sealed writer paths; and READONLY committed-journal recovery with e2fsck.
Native tests supplement the formal proofs and do not prove hardware durability.
