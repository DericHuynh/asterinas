<!-- SPDX-License-Identifier: MPL-2.0 -->

# Directory and mixed namespace exchange

This extends the bounded owned host namespace core with ordinary
`RENAME_EXCHANGE` for regular files, directories and mixed pairs. Both complete
names must exist. The separate [regular replacement/exchange core](FILE_RENAME.md)
and [cross-directory move/link/unlink core](CROSS_DIRECTORY_NAMESPACE.md) retain
their existing operation contracts.

The public entry points are `Checkout::prepare_exchange` and
`Store::publish_exchange`, with a separate consuming `ExchangePrepared` type.
The lower-level constructor is `ns_exchange::prepare_exchange`.

## Checked results

| Check | Current result |
| --- | --- |
| Pinned whole-crate Verus checking and compilation | 2901 obligations, zero errors; 829 named proofs and 712 named executable functions |
| Native interoperability/regressions | 358 passed (296 metadata, 62 journal), including 15 directory/mixed exchange tests |
| Ownership/privacy rejection checks | All 282 current cases rejected; 35 new exchange cases |
| Negative verifier gates | All 6 cases rejected |
| Runner timeout regression | Passed; diagnostic cleanup only, no verifier proof evidence |

[Proof status](proof-status.json) and [recorded evidence](verification-evidence.json)
identify the exact checked source and artifacts. Native/API checks supplement
the proofs; they do not establish kernel or physical durability refinement.

## Verification resource budgets

The verifier has a 2100-second wall timeout; each negative gate has a
2160-second outer timeout. The prior whole-crate archive took approximately
1299.51 seconds, and a 260.85-second filtered core diagnostic motivated the
larger runner budget. These timings guide resource allocation and do not
count as positive proof evidence.

The [CI workflow](../../.github/workflows/verify_ext4.yml) allows 120 minutes
for the complete verification, negative gates, runner timeout regression and
native/API checks. It configures two native harness threads through
`RUST_TEST_THREADS=2` and runs `check_timeout.py`. Pinned tools, strict
whole-crate flags, named coverage and compilation requirements remain
unchanged. These budgets retain the host-only scope and closed activation
gates described below.


## Exact exchange relation

The result swaps both full-key target/generation/type bindings. It updates the
parent binding of each moved directory and preserves every unrelated binding in
both directions. Names are complete byte sequences, including non-UTF-8 bytes;
record ordinals alone are not operation identities.

For distinct parents, the required link-count and dotdot changes are:

| Source operand | Destination operand | Source parent links | Destination parent links | Directory parent bindings |
| --- | --- | --- | --- | --- |
| Regular | Regular | Exact unchanged count | Exact unchanged count | Unchanged |
| Directory | Directory | Exact unchanged count | Exact unchanged count | Both dotdot bindings swap to the opposite parent with its exact generation |
| Directory | Regular | Decrement once | Increment once | Source directory dotdot names the destination parent |
| Regular | Directory | Increment once | Decrement once | Destination directory dotdot names the source parent |

With one shared parent, every link count and directory dotdot binding remains
exact. The shared parent receives two ordinary version increments. Distinct
parents each receive one version increment. Each distinct operand receives the
requested ctime and one ordinary host version increment; operand mtime, link
count, identity, extents, sectors and xattr/EA bytes remain exact.
The host ordinary-version policy is explicit and does not claim equality with
all Linux internal version scheduling.

A same-inode exchange preserves every source byte and has no patches or inode
or directory edits. Regular hardlink aliases are allowed; a directory no-op
requires the same complete key. Mutation-only layout, timestamp representability
and version guards are skipped for that no-op after source admission, READONLY
exclusion and proper-name/type/identity checks. Accepted publication still
consumes one local store revision.

## Components and proof boundaries

| Component | Required contract | Boundary |
| --- | --- | --- |
| `ns_exchange_relation.rs` | Exact typed generation swap, both old/new dotdot witnesses, equal live-entry count and bidirectional preservation of every unrelated full key | No VFS authorization |
| Existing `ns_record_target`, `ns_dir_edit` and `ns_inode_links` | Canonical source pieces, record target/type changes or dotdot retargeting, requested metadata, checksums and local byte frames | Existing supported formats and record capacity |
| `ns_exchange.rs` | Actual source inode positions and directory block maps, every moved-directory edit witness, latest-block coalescing, exact whole-image frame, complete result namespace readmission and rooted topology | Bounded host snapshots |
| `ns_exchange_prepared.rs`, checkout and store | Private owned source/result and operation witness; publication requires exact current source bytes and nonwrapping revision; rejection preserves the store | Host exclusive access without an OSTD scheduler or device refinement |

The plan permits at most four inode edits, four changed directory blocks and
eight physical patches. Two names sharing a directory piece are composed from
the latest staged bytes. Different inode slots in one table block are coalesced
before materialization. Each moved directory's first block is bound to that
directory's actual source mapping and checksum domain.

Complete result admission checks canonical dotdot/named-parent agreement,
link counts and rooted ranks after all edits. Self/descendant cycles reject.
Root operands and overlap between an operand inode and either parent reject
before encoding. A stale topology preparation cannot bypass publication's
revision and entire-source comparison, even when its target blocks differ.

DIR_NLINK stored count `1` remains an unknown count under the source-selected
directory policy. Zero-delta operations preserve it. This bounded mixed
cross-parent operation rejects either affected parent with count `1`, and
performs exact nonwrapping arithmetic for supported counts. Synthetic small
linear marker fixtures test that policy; they are separate from Linux
fsck-clean ordinary exchange fixtures.

## Remaining boundaries

Changed directory pieces use the supported linear layout. No inode or block is
allocated or reclaimed. Last-link replacement, rmdir, whiteout, directory growth
and HTree restructuring need separate implementations and proofs. Kernel VFS
permissions, sticky-bit/idmap/LSM and quota/project policy remain external.

Full-feature, full EA filesystem, writable-mount, kernel/CortenMM/OSTD and
EA-enabled durable-publication gates remain false. Host image ownership does
not establish CortenMM frame loans, mounted cache coherence, lock fairness or
physical JBD2 crash durability. The framekernel does not acquire Linux page,
folio or buffer-head ownership through this component.

## Linux reference

Linux v7.0 commit `028ef9c96e96197026887c0f092424679298aae8`:
[ext4 rename/exchange](https://github.com/torvalds/linux/blob/028ef9c96e96197026887c0f092424679298aae8/fs/ext4/namei.c)
and [directory locking](https://github.com/torvalds/linux/blob/028ef9c96e96197026887c0f092424679298aae8/Documentation/filesystems/directory-locking.rst).
The independent host protocol uses exact-source/revision rejection and complete
result admission. Runtime kernel locking and device persistence require their
own refinement proofs.
