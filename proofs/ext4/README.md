<!-- SPDX-License-Identifier: MPL-2.0 -->

# Ext4 core and Verus proofs for Asterinas

This package implements and verifies part of an independent, safe Rust
implementation of Linux-compatible ext4. The implemented profile is still a
subset; the expanded target includes [full feature coverage](FEATURE_COVERAGE.md)
and a [concurrent block/extent/transaction protocol](CONCURRENCY.md).
It is not a complete filesystem and is not registered with the kernel VFS.
No mount or filesystem write path is enabled.

The pinned Verus run checks **841 obligations with zero errors**, including
288 named proof functions and 286 named executable functions.
67 host interoperability/regression tests pass on Linux-created metadata.
[Proof status](proof-status.json) and [recorded evidence](verification-evidence.json)
state the exact scope; tests do not discharge formal obligations.

## Implemented and checked

| Component | Checked behavior |
| --- | --- |
| `bytes.rs`, `crc.rs` | Total endian codecs, checked ranges, CRC32C and streaming/zero-field checksum relations. |
| `superblock.rs`, `group.rs`, `inode.rs` | Strict profile checks, geometry/ranges, Linux metadata checksums, typed field decoding, source-selected CSUM_SEED or UUID-derived metadata seeds. [Checksum domains](CSUM_SEED.md) remain separate from the internal journal UUID and JBD2 seed. |
| `group_fields.rs`, `group.rs`, `group_metadata.rs` | Exact 64-bit addresses/superblock counts and 32-bit counters; optional source-selected 64-byte descriptors, complete descriptor and bitmap checksum coverage, bounded high-field rejection and recovery identity. See [group descriptors](GROUP_DESCRIPTORS.md). High-address volumes and other group layouts remain open. |
| `inode_size.rs` | Total Linux high/low size codecs and feature-dependent maximum sizes over seven block sizes; 64-bit regular inode sizes with source-bound optional HUGE_FILE policy in the current 4 KiB profile; exact source metadata and nontruncating logical offsets with EOF/data/hole clipping. See [inode sizes](INODE_SIZES.md). Mutations, other feature combinations and runtime authority remain open. |
| `inode_blocks.rs` | Linux 32/48-bit i_blocks fields and sector/filesystem-block units, exact canonical encoding with aligned huge-unit inputs, checked overflow bounds, and source-bound HUGE_FILE composition with complete data/extent-metadata accounting. See [inode accounting](INODE_BLOCKS.md). |
| `block_range.rs`, `extent_span.rs` | 64-bit block interval bounds, disjointness and exact split partition; Linux 48-bit physical-start codec, reserved terminal logical block and pointwise logical/physical mapping preservation under splitting and merging. Descriptors do not establish allocation, read initialization, concurrency or full-tree admission. |
| `block_lifetime.rs` | Abstract per-block shared read pins, exclusive volume/block/epoch-bound writer leases, initialization/publication and reuse. All finite enabled interleavings preserve the invariant; retired pin IDs stay retired, stale requests/leases are rejected, disjoint writes commute, and nonempty reader/writer examples cover modeled block sizes 1 through 64 KiB. No runtime thread, extent-map, DMA or concurrent journal refinement is claimed. |
| `block_size.rs`, `extent_node.rs` | Shared geometry checks and total local extent-node validation: inline roots, external 1–64 KiB nodes, depth 0–5, 48-bit index children, bounded entries/capacity, ordered nonoverlapping records, legacy/checksummed blocks and the Linux eh_max checksum domain. Strict-key and interval ordering, binary-search partitions, unique covering leaf records and inherited branch bounds are checked. Bounded 4 KiB inode/feature and ownership composition is checked by extent_claims.rs; wider geometry and runtime refinement remain open. |
| `source_block.rs`, `snapshot.rs`, `shadow_model.rs` | Exact bounded byte capture across shadow-page boundaries and owned 64-bit-addressed 1–64 KiB filesystem blocks. Checked multiplication/division binds each block and extent-node buffer to its exact source range and partition bounds, without truncating high page addresses. Bounded 4 KiB inode seed/feature/ownership binding composes through extent_claims.rs. Wider geometry and CortenMM/device origin remain open. |
| `extent_tree.rs`, `extent_tree_model.rs` | Source-bound lookup paths, exact decreasing depths and cycle exclusion; complete recursive structural audits with a separate visit-budget error; audited lookup agrees with every covering leaf record in the entire tree. Written/unwritten/hole results are descriptions. Bounded 4 KiB allocation and inode/feature binding compose with the volume validator. Mutations, other geometries/features and runtime authority remain open. See [extent trees](EXTENT_TREES.md). |
| `extent_claims.rs`, `extent_ownership.rs` | Actual source inode/root/metadata-generation checksum seed, complete depth-0..5 metadata/data claims, distinct inode-owned metadata roles, disjoint census composition and exact sector accounting. Every stored mapping has its exact source claim; complete-tree lookup is unique. Whole-image allocation, namespace/image validation and structural reads use these results in the bounded 4 KiB profile. No mutation or runtime authority is produced. |
| `extent.rs` | Leaf extent codec, initialized/unwritten lengths, logical ordering and disjointness, bounded block resolution. |
| `directory.rs` | Bounded linear dirent parsing, filename validation, directory checksum tails. |
| `jbd2.rs`, `journal_superblock.rs` | Header/tag codecs, UUID binding, checksum primitives, counter bounds and superblock parsing. |
| `descriptor.rs`, `revoke.rs` | Complete canonical v3 descriptor/revoke parsing and encoding, UUIDs, tag terminators, target bounds, checksum tails and capacity limits. |
| `bitmap.rs`, `group_metadata.rs` | Owned initialized block/inode bitmaps, exact free counts, allocated padding, bounded lookup and Linux checksum ranges. INODE_UNINIT groups use a proved canonical empty logical inode bitmap; stale physical bitmap/table contents cannot grant inode access. See [lazy inode groups](LAZY_INODES.md). |
| `block_claims.rs`, `inode_claims.rs` | Bounded disjoint ownership census; failed claims preserve the original; bitmap/role and free-counter equivalence; inode/journal byte binding, exact physical slots, initialized directory extents and `i_blocks` accounting. These are validation components, not a whole-volume certificate or file-access authority. |
| `group_claims.rs` | Sparse-super backup locations match the Linux power rule over the bounded profile; reserve superblock/GDT, bitmaps and inode tables with exact disjoint claims. |
| `snapshot.rs`, `group_metadata.rs`, `group_index.rs` | Exact immutable source ranges bind each group descriptor and bitmap to its declared address; complete ordered group enumeration and equality of aggregate free counters with the primary superblock. No whole-volume inode/namespace authority is produced. |
| `inode_table.rs`, `inode_group.rs`, `allocation_counts.rs`, `allocation.rs` | Complete source-bound allocated-inode traversal, mandatory reserved inode markers, root type, empty unused reserved inodes, inode-table high-water bounds and directory counts; exact composition of metadata/journal/inode claims, all block bitmaps and global free-block accounting. This allocation certificate omits namespace, operation, recovery/mount and device authority. |
| `allocated_inode.rs`, `file_read.rs` | Ordinary inode lookup inherits the whole-image source/ownership certificate; initialized logical mapping is unique and has exact owner/generation/slot identity; block/file-size clipped chunks return source bytes or zeros for holes/unwritten extents. Structural host helpers, not VFS/credential authority. |
| `directory_block.rs` | Complete canonical linear-record coverage including deleted records, unique complete stream, checksum tail and bounded read-only record/name access. Source/target, link and topology checks are composed by the namespace layer. |
| `directory_file.rs`, `directory_source.rs` | Directory bytes and checksum seed come from the actual allocated inode and initialized mapping; executable records equal the unique canonical source stream. Gaps and malformed blocks fail closed. Whole-directory enumeration is composed by directory_index.rs. |
| `name_set.rs` | Owned directory/name keys; exact membership, duplicate rejection and unchanged failed insertion; full byte comparison across CRC bucket collisions. At most 65536 keys, 64/bucket and 255 bytes/name. This is a bounded namespace-admission helper, not a complete namespace certificate. |
| `namespace_model.rs`, `directory_index.rs` | Complete canonical enumeration of every allocated directory/block and live record, including empty preallocation; source/target inode types and target generations, global unique names, exact source entries and complete lookup via proved name-index positions. Bounded to 4096 directory blocks. Link counts and rooted parent topology are composed by namespace.rs. |
| `namespace_counts.rs`, `parent_table.rs`, `tree_model.rs`, `namespace_tree.rs`, `namespace.rs` | Exact source-reference accounting, inode link counts, canonical first-block dot/dotdot placement and targets, unique ordinary directory parents and matching dotdot, root rules, bounded nonrecursive traversal and a theorem that every accepted directory reaches root. Regular file hard links are admitted; disconnected cycles and directory hard links are rejected. This is a static image certificate, not recovery/mount/VFS authority. |
| `patch_set.rs`, `shadow_model.rs`, `snapshot.rs` | Owned exact after-images in a sorted unique target set, binary lookup, 4096-block credit and unchanged rejection. Immutable shadow sources share the original bytes and at most 32 bounded patch layers; later patches take precedence with exact block and byte provenance. The existing allocation/namespace validators read the shadow directly. Recovery admission is composed by recovery_admission.rs. |
| `bootstrap.rs`, `snapshot.rs` | Locate journal inode 8 through the same primary superblock and group-zero descriptor before global bitmap validation; exact reserved-inode byte range and bounded complete journal capture. Discovery alone gives no recovery, mount or write authority. |
| `bootstrap_identity.rs`, `image_validation.rs` | Exact immutable primary bytes, all group bitmap/table addresses and entire journal inode remain fixed; other inodes sharing the block may change. Retained-source static-image inspection runs actual allocation/directory/namespace validation; identity alone does not establish filesystem validity. Recovery I/O admission is composed by recovery_admission.rs. |
| `recovery_patch.rs` | Owned sorted shadow patches contain exactly the replay plan's selected latest unrevoked images, with the same target identities and bytes; unselected targets have no patch. Bootstrap recovery preparation binds the maximal scan certificate to the exact retained source journal, UUID, primary and layout. |
| `recovery_admission.rs` | Before issuing any wrapped request, build the selected-home and retired-tail shadow, validate the complete static filesystem, enforce bootstrap identity and the same journal mapping, then retain that exact certificate through owned dispatch, completion and abort. Inconsistent home metadata may be repaired by committed redo; a valid journal containing an invalid filesystem patch is rejected. This host-core wrapper does not establish actual device state or mount authority. |
| `layout.rs` | Checked mapping of a single initialized journal extent; journal blocks excluded from replay targets. |
| `replay.rs`, `replay_refinement.rs` | Linux same/later revoke suppression and reallocation, latest-image selection, exact chronological redo equivalence, arbitrary partial replay restart. |
| `scan.rs`, `scan_trace.rs`, `scan_stop.rs`, `scan_budget.rs` | Bounded ring scan, contiguous exact record coverage, complete descriptor payloads, committed cut, actual source/commit provenance, checked stopping witnesses, unique canonical maximal prefix and recovered input. Clean snapshots and active snapshots satisfying the declared resource profile are admitted. Every writer crash snapshot satisfies that scan profile. |
| `epoch.rs`, `journal_state.rs`, `super_state.rs` | Conservative fresh IDs independent of checksums; exact superblock state images; immutable geometry/UUID/boot framing; only RECOVER changes during state-image construction; other incompatibility bits and the stored checksum seed remain fixed during replay. |
| `recovery_io.rs`, `recovery_profile.rs`, `recovery_device.rs`, `recovery_closure.rs` | Owned immutable recovery command protocol, partition-confined emitted images, preserved scan certificates, checked sufficient preparation admission, stale/duplicate report rejection, sticky abort, two flushes, finite failure-free completion; terminal-ID recovery without allocating a fresh epoch; byte-valued persistence refinement, unchanged committed input before retirement, and admission preserved through arbitrary finite recovery crashes under an explicit 4 KiB atomicity contract. |
| `recovery_request.rs` | An outstanding request owns its exact recovery machine; completion consumes that object. External callers cannot forge/reuse requests or redirect a completion using a recycled numeric ID. |
| `transaction.rs`, `transaction_refinement.rs` | Owned unique after-images; exact canonical transaction encoding; concrete journal-map witness; returned scans recover every encoded original image. A candidate patch is not filesystem authority. |
| `journal_view.rs` | Physical block-map projection equals scanner bytes; equal journal blocks have equal snapshots; a journal write splices exactly one image; nonjournal writes preserve the snapshot. |
| `write_protocol.rs`, `write_io.rs` | Conservative serial dirty/activation/log/commit/checkpoint/retirement commands, six fences, owned requests, sticky abort, partition confinement and exact local preparation admission. |
| `freshness.rs`, `write_device.rs`, `write_media.rs`, `write_recognition.rs`, `write_admission.rs`, `write_recovery.rs` | All finite ledger interleavings; exact per-event atomic-block byte refinement; finite flush refinement; fresh commit recognition without a checksum identity premise; before/after home-byte guarantees for actual scan plus recovery, safe tail clearing and finite failure-free success under the declared device contract. |
| `write_history.rs` | Induction over actual byte-valued successful writer generations; acknowledged home-image composition; no late ledger persistence; recovery after a final cut includes every acknowledged generation. |
| `frozen.rs` | Owned immutable snapshots, JBD2 escape/restore, snapshot contents independent of the source buffer. |
| `ring.rs` | Bounded credits and injective circular-log position mapping. |
| `gate.rs` | Affine writer capability backed by vstd's exclusive resource algebra; no local trusted token generator. |
| `ownership.rs` | Abstract role separation, zero initialization, stale-generation rejection and no disclosure across block reuse. |
| `journal.rs`, `history.rs`, `persistence.rs`, `system.rs` | Transaction invariants, per-unit completion/persistence interleavings, quiescent reuse, bounded generations, arbitrary finite histories and acknowledged-prefix recovery. |

The top-level model theorem is
`system::crash_at_every_interleaving_preserves_the_acknowledged_prefix`.
Its premise is an execution of the specified device/transaction machine.
Commit and retirement are semantic durable facts in that machine;
**serialized physical writer-history composition is also checked under the stated
device contract; actual driver and runtime gate refinement remain open**.
The proof does not establish durability of a mounted Asterinas filesystem.

The recovery theorem `recovery_device::success_image_equals_linux_redo` proves
that the stable image equals chronological redo plus the retired journal tail.
Its machine permits persistence before completion and after abort, and proves
that a persisted clear tail implies durable home data. It is conditional on a
correct, complete replay plan, a quiescent device and the stated atomicity/flush
contract. The single-transaction writer now has a checked byte/persistence link:
old headers cannot acquire a fresh ID, escaped payloads cannot impersonate
metadata, and a recognized fresh commit implies the complete encoded log is
stable. Before commit the home image is unchanged except recovery marking;
retirement requires durable exact home after-images. A successful flush has a
finite refinement into issued atomic writes, and a failure-free ledger has a
finite successful execution. These results use explicit device assumptions,
not a claim about any actual Asterinas driver.

Active scanning has a checked sufficient resource profile. Every writer crash snapshot
satisfies it, including partial log persistence, without CRC injectivity. Recovery
retirement uses the recognized next sequence, including the terminal value MAX;
new writer epochs still require a fresh nonwrapping ID. Recovery preparation
admits a checked sufficient profile, and every legal writer
crash snapshot satisfies it. The selected replay and a successful modeled recovery
produce complete before/after home bytes outside block zero and the journal.
Block zero separately preserves validated volume identity and the replay policy.
Serialized physical histories compose over actual durable maps, including later
overwrites and a final unacknowledged transaction if its commit persisted.
Every modeled recovery crash snapshot remains admitted for another attempt;
uncleared journals retain the same committed input. Admission survives arbitrary
finite sequences of recovery crashes. These results require the stated atomicity,
flush and quiescent-start contracts. Whole-image allocation validation is checked for the bounded logical-group
profile, and complete static namespace validation now composes source names,
targets, link counts and rooted topology. Filesystem operations, recovery/mount
admission, unmount and actual gate/device refinement remain open.

All public executable entry points validate their inputs without `requires`
clauses that an unverified caller could bypass.
A successful structural parse or allocation certificate is not an authorization
or mount certificate. The allocation builder binds every reserved region,
allocated inode and bitmap to the same borrowed frozen image. Namespace validation
composes that certificate; recovery/mount admission remains separate.
CRC checks do not authenticate a disk or prove freshness.

## Reproduce

Install the Rust toolchain and the digest-pinned Verus release:

~~~sh
rustup toolchain install 1.99.1 --profile minimal
export RUSTUP_TOOLCHAIN=1.99.1
python3 proofs/ext4/tools/install_verus.py /absolute/path/to/new-verus-directory
export VERUS_BIN=/absolute/path/to/new-verus-directory/verus
export VERUS_LIB_DIR=/absolute/path/to/new-verus-directory
python3 proofs/ext4/tools/verify.py
python3 proofs/ext4/tools/check_gate.py
python3 proofs/ext4/tools/check_compat.py
~~~

The compatibility check requires `mke2fs`, `debugfs` and `e2fsck` from e2fsprogs,
and `rustc` from the pinned toolchain.
`RUSTC_BIN`, `MKE2FS_BIN`, `DEBUGFS_BIN` and `E2FSCK_BIN` may select executable paths.
The installer accepts `--archive` for an offline, digest-checked installation.

The runner checks the entire crate with `--no-cheating --no-external-by-default --output-json --compile`.
It rejects local proof escapes, extra flags, omitted modules and source-inventory drift;
requires named proof and executable coverage; invalidates stale artifacts on failure;
and records source, runner, manifest, verifier and emitted-library hashes.
The negative checks include an actual failing Verus assertion in a disposable copy.
Thirteen additional negative Rust compilation checks reject extent-tree and bound-inode certificate/source substitution and recovery/writer request
reuse and forgery, external completion redirection, writer-state replacement and admitted-recovery request/engine substitution.
[CI](../../.github/workflows/verify_ext4.yml) runs the same checks.

The emitted host library exercises proof erasure and Linux byte compatibility.
The journal tests compare checked replay with Linux recovery for seven histories,
including revokes, reallocation, same-transaction revokes, an incomplete tail,
ring wrap and block-zero metadata. They also exercise retired images and five
recovery interruption cuts with `e2fsck`; these examples are not formal proofs.
The complete transaction encoder is tested at 1, 2 and 250 payloads. The serial
writer is checked against Linux recovery at all fifteen command cuts for a
two-payload transaction, with abort injection at each position. Additional cases
exercise 4096/4097 replay credits, reserved revoke targets, and terminal-ID replay
and retirement against Linux recovery. Three completed overlapping writer
generations are followed by all thirteen command cuts of a final writer. Four
repeated recovery crashes include a journaled primary-superblock update. Allocation
checks use Linux bitmaps and census all allocated blocks in the controlled fixture;
checksummed inode aliases, inconsistent sector counts and unwritten directory
extents are rejected. Sparse-super reservations are exercised across all 32 groups;
checksummed global counter mismatches and bitmap source substitution are rejected.
Whole-image checks additionally reject missing root/journal bitmap markers, hidden
reserved-inode storage, inconsistent directory/high-water counts, allocated blocks
without a source claim, claimed blocks marked free, and journal/file aliases.
Read tests cover exact fixture bytes, block/file boundaries, extreme offsets and
requests, holes and unwritten extents backed by nonzero storage. Complete directory
parsing rejects checksummed malformed suffixes and invalid names. Directory reads
bind the inode generation and reject holes; name-index tests accept 64 distinct
colliding keys, reject the next without changing state, and retain owned names
after caller mutation. Whole-directory indexing additionally rejects dangling/journal
targets, type mismatches, duplicate names, malformed empty directory blocks and
directory-credit exhaustion. Namespace tests additionally cover link counts,
dot/parent mismatches, swapped dot/dotdot records, directory hard links, orphaned
files, a locally consistent disconnected cycle, and valid regular-file hard links.
Do not link it into the kernel: its target and toolchain differ from the kernel's.
A kernel source build and its OSTD adapter refinement remain necessary.

## Remaining acceptance gates

[DESIGN.md](DESIGN.md) remains the target design.
[PROOF_OBLIGATIONS.md](PROOF_OBLIGATIONS.md) distinguishes checked abstractions
from the missing implementation/refinement work.
The full design is **not implemented or proved**.
In particular, these are still missing:

- Filesystem operation implementations,
  including allocation, create/unlink/rename, orphan handling, permissions integration and fsync.
- Unmount ordering and actual device atomicity, quiescence and reuse refinement.
  The checked physical history is serialized; a runtime gate must enforce it.
- CortenMM/OSTD frame, sleeping-lock, BIO, DMA and device-persistence adapters,
  with verified callback generations, snapshot loans, quiescence and ingress contracts.
- Read-only/writable mount integration and end-to-end progress proofs.

The framekernel boundary remains unchanged.
Future kernel code must use CortenMM/OSTD ownership, `VmReader`/`VmWriter` and submitted BIOs;
Linux `struct page`, `buffer_head` and folio ownership are not imported.
The host snapshot type does not certify an OSTD frame or DMA loan.

Read [FORMAT_PROFILE.md](FORMAT_PROFILE.md), [TRUST_BOUNDARY.md](TRUST_BOUNDARY.md)
and [sources.json](sources.json) before extending the implementation.
