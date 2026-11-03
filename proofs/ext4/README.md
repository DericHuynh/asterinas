<!-- SPDX-License-Identifier: MPL-2.0 -->

# Ext4 core and Verus proofs for Asterinas

This package implements and verifies part of an independent, safe Rust
implementation of a **Linux-compatible ext4 subset**.
It is not a complete filesystem and is not registered with the kernel VFS.
No mount or filesystem write path is enabled.

The pinned Verus run checks **128 obligations with zero errors**, including
66 named proof functions and 45 named executable functions.
Eight host interoperability/regression tests pass on Linux-created metadata.
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
| `frozen.rs` | Owned immutable snapshots, JBD2 escape/restore, snapshot contents independent of the source buffer. |
| `ring.rs` | Bounded credits and injective circular-log position mapping. |
| `gate.rs` | Affine writer capability backed by vstd's exclusive resource algebra; no local trusted token generator. |
| `ownership.rs` | Abstract role separation, zero initialization, stale-generation rejection and no disclosure across block reuse. |
| `journal.rs`, `history.rs`, `persistence.rs`, `system.rs` | Transaction invariants, per-unit completion/persistence interleavings, quiescent reuse, bounded generations, arbitrary finite histories and acknowledged-prefix recovery. |

The top-level model theorem is
`system::crash_at_every_interleaving_preserves_the_acknowledged_prefix`.
Its premise is an execution of the specified device/transaction machine.
Commit and retirement are semantic durable facts in that machine;
**their refinement from actual JBD2 bytes and driver events is still unproved**.
The proof does not establish durability of a mounted Asterinas filesystem.

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

The compatibility check requires `mke2fs` and `debugfs` from e2fsprogs,
and `rustc` from the pinned toolchain.
`RUSTC_BIN`, `MKE2FS_BIN` and `DEBUGFS_BIN` may select executable paths.
The installer accepts `--archive` for an offline, digest-checked installation.

The runner checks the entire crate with `--no-cheating --no-external-by-default --output-json --compile`.
It rejects local proof escapes, extra flags, omitted modules and source-inventory drift;
requires named proof and executable coverage; invalidates stale artifacts on failure;
and records source, runner, manifest, verifier and emitted-library hashes.
The negative checks include an actual failing Verus assertion in a disposable copy.
[CI](../../.github/workflows/verify_ext4.yml) runs the same checks.

The emitted host library exercises proof erasure and Linux byte compatibility.
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
- Complete JBD2 transaction/descriptor/revoke scanning, recovery, crash-safe superblock/tail updates,
  and byte-level freshness/tearing/reuse proofs.
- CortenMM/OSTD frame, sleeping-lock, BIO, DMA and device-persistence adapters,
  with verified callback generations, snapshot loans, quiescence and ingress contracts.
- Read-only/writable mount integration and end-to-end progress proofs.

The framekernel boundary remains unchanged.
Future kernel code must use CortenMM/OSTD ownership, `VmReader`/`VmWriter` and submitted BIOs;
Linux `struct page`, `buffer_head` and folio ownership are not imported.
The host snapshot type does not certify an OSTD frame or DMA loan.

Read [FORMAT_PROFILE.md](FORMAT_PROFILE.md), [TRUST_BOUNDARY.md](TRUST_BOUNDARY.md)
and [sources.json](sources.json) before extending the implementation.
