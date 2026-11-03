<!-- SPDX-License-Identifier: MPL-2.0 -->

# Ext4 core and Verus proofs for Asterinas

This package implements and verifies part of an independent, safe Rust
implementation of a **Linux-compatible ext4 subset**.
It is not a complete filesystem and is not registered with the kernel VFS.
No mount or filesystem write path is enabled.

The pinned Verus run checks **372 obligations with zero errors**, including
183 named proof functions and 106 named executable functions.
Eighteen host interoperability/regression tests pass on Linux-created metadata.
[Proof status](proof-status.json) and [recorded evidence](verification-evidence.json)
state the exact scope; tests do not discharge formal obligations.

## Implemented and checked

| Component | Checked behavior |
| --- | --- |
| `bytes.rs`, `crc.rs` | Total endian codecs, checked ranges, CRC32C and streaming/zero-field checksum relations. |
| `superblock.rs`, `group.rs`, `inode.rs` | Strict profile checks, geometry/ranges, Linux metadata checksums, typed field decoding. |
| `extent.rs` | Leaf extent codec, initialized/unwritten lengths, logical ordering and disjointness, bounded block resolution. |
| `directory.rs` | Bounded linear dirent parsing, filename validation, directory checksum tails. |
| `jbd2.rs`, `journal_superblock.rs` | Header/tag codecs, UUID binding, checksum primitives, counter bounds and superblock parsing. |
| `descriptor.rs`, `revoke.rs` | Complete canonical v3 descriptor/revoke parsing and encoding, UUIDs, tag terminators, target bounds, checksum tails and capacity limits. |
| `layout.rs` | Checked mapping of a single initialized journal extent; journal blocks excluded from replay targets. |
| `replay.rs`, `replay_refinement.rs` | Linux same/later revoke suppression and reallocation, latest-image selection, exact chronological redo equivalence, arbitrary partial replay restart. |
| `scan.rs`, `scan_trace.rs`, `scan_stop.rs`, `scan_budget.rs` | Bounded ring scan, contiguous exact record coverage, complete descriptor payloads, committed cut, actual source/commit provenance, checked stopping witnesses, unique canonical maximal prefix and recovered input. Clean snapshots and active snapshots satisfying the declared resource profile are admitted. Every writer crash snapshot satisfies that scan profile. |
| `epoch.rs`, `journal_state.rs`, `super_state.rs` | Conservative fresh IDs independent of checksums; exact superblock state images; immutable geometry/UUID/boot framing; recovery flag retained during replay. |
| `recovery_io.rs`, `recovery_device.rs` | Owned immutable recovery command protocol, stale/duplicate report rejection, sticky abort, two flushes, finite failure-free completion; terminal-ID recovery without allocating a fresh epoch; byte-valued persistence refinement under an explicit 4 KiB atomicity contract. |
| `recovery_request.rs` | An outstanding request owns its exact recovery machine; completion consumes that object. External callers cannot forge/reuse requests or redirect a completion using a recycled numeric ID. |
| `transaction.rs`, `transaction_refinement.rs` | Owned unique after-images; exact canonical transaction encoding; concrete journal-map witness; returned scans recover every encoded original image. A candidate patch is not filesystem authority. |
| `journal_view.rs` | Physical block-map projection equals scanner bytes; a journal write splices exactly one image; nonjournal writes preserve the snapshot. |
| `write_protocol.rs`, `write_io.rs` | Conservative serial dirty/activation/log/commit/checkpoint/retirement commands, six fences, owned requests, sticky abort, partition confinement and exact local preparation admission. |
| `freshness.rs`, `write_device.rs`, `write_media.rs`, `write_recognition.rs`, `write_admission.rs` | All finite ledger interleavings; exact per-event atomic-block byte refinement; finite flush refinement; fresh commit recognition without a checksum identity premise; before/after home-byte guarantees, safe tail clearing and finite failure-free success under the declared device contract. |
| `frozen.rs` | Owned immutable snapshots, JBD2 escape/restore, snapshot contents independent of the source buffer. |
| `ring.rs` | Bounded credits and injective circular-log position mapping. |
| `gate.rs` | Affine writer capability backed by vstd's exclusive resource algebra; no local trusted token generator. |
| `ownership.rs` | Abstract role separation, zero initialization, stale-generation rejection and no disclosure across block reuse. |
| `journal.rs`, `history.rs`, `persistence.rs`, `system.rs` | Transaction invariants, per-unit completion/persistence interleavings, quiescent reuse, bounded generations, arbitrary finite histories and acknowledged-prefix recovery. |

The top-level model theorem is
`system::crash_at_every_interleaving_preserves_the_acknowledged_prefix`.
Its premise is an execution of the specified device/transaction machine.
Commit and retirement are semantic durable facts in that machine;
**multi-transaction physical-history composition and the actual driver refinement remain open**.
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
admission, multi-transaction physical history, whole-volume validation and the
actual driver refinement remain open.

All public executable entry points validate their inputs without `requires`
clauses that an unverified caller could bypass.
A successful structural parse is not an ownership, authorization or mount certificate.
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
Six additional negative Rust compilation checks reject recovery/writer request
reuse and forgery, external completion redirection and writer-state replacement.
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
and retirement against Linux recovery.
Do not link it into the kernel: its target and toolchain differ from the kernel's.
A kernel source build and its OSTD adapter refinement remain necessary.

## Remaining acceptance gates

[DESIGN.md](DESIGN.md) remains the target design.
[PROOF_OBLIGATIONS.md](PROOF_OBLIGATIONS.md) distinguishes checked abstractions
from the missing implementation/refinement work.
The full design is **not implemented or proved**.
In particular, these are still missing:

- Global ext4 ownership/namespace validation and filesystem operation implementations,
  including allocation, create/unlink/rename, orphan handling, permissions integration and fsync.
- Recovery preparation total admission/progress and multi-transaction physical
  history recognition, boot/unmount ordering and byte-level tearing/reuse proofs.
- CortenMM/OSTD frame, sleeping-lock, BIO, DMA and device-persistence adapters,
  with verified callback generations, snapshot loans, quiescence and ingress contracts.
- Read-only/writable mount integration and end-to-end progress proofs.

The framekernel boundary remains unchanged.
Future kernel code must use CortenMM/OSTD ownership, `VmReader`/`VmWriter` and submitted BIOs;
Linux `struct page`, `buffer_head` and folio ownership are not imported.
The host snapshot type does not certify an OSTD frame or DMA loan.

Read [FORMAT_PROFILE.md](FORMAT_PROFILE.md), [TRUST_BOUNDARY.md](TRUST_BOUNDARY.md)
and [sources.json](sources.json) before extending the implementation.
