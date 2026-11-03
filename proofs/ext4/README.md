<!-- SPDX-License-Identifier: MPL-2.0 -->

# Ext4 design and Verus models

This package starts the design of an independent, safe Rust implementation of a
**Linux-compatible ext4 subset for Asterinas**. Linux ext4 and JBD2 are format and
behavior references. The selected scope is compatibility with a restricted,
explicitly admitted profile, rather than a new disk format.

**Status: design/model candidates; NOT VERIFIED; no filesystem implementation.**
The executor was unavailable during authoring. None of the Verus proof bodies,
the proof runner, or the proposed device/format refinements has been checked.
A function named "proof" is not evidence that the verifier accepted it.
This package does not register an ext4 driver or enable any disk writes.

The first proposed writable profile uses full data journaling, one transaction
in flight, and a sleeping operation gate held through checkpoint and retirement.
This intentionally limits the initial concurrency and durability protocol. It
does not promise Linux feature completeness or production performance.

## Read in this order

1. [Design and crash model](DESIGN.md).
2. [Compatibility profile and parser boundary](FORMAT_PROFILE.md).
3. [Security, concurrency, and durability obligations](PROOF_OBLIGATIONS.md).
4. [Trust and adapter contracts](TRUST_BOUNDARY.md).
5. [Proof status](proof-status.json) and [pinned toolchain](toolchain.lock.json).
6. [Abstract model entry point](src/model.rs) and [source references](sources.json).

## What is modeled now

- Abstract after-image replay, including replay over a partial checkpoint.
- A single transaction with separately issued and persistent writes, preparation,
  commit submission, durable commit, acknowledgement, partial checkpoint, and
  durable retirement.
- An abort that does not magically cancel already submitted I/O.
- An abstract operation-gate owner and generation, including stale-lease rejection.
- Concrete witnesses for missing preparation and premature checkpointing.

The durable commit/retirement fields are **semantic storage predicates**. They
are not a parser that trusts a magic number or CRC. Proving their relationship
to real JBD2 bytes, torn sectors, sequence numbers, and flush completions is a
required later refinement. The model is not a proof of a filesystem, a driver,
all histories, or all races. The registry makes those gaps explicit.

## Verification gate

The only accepted proof checker for this work is Verus. Tests, crash injection,
Linux mounting, and fsck will be useful implementation validation, but cannot
discharge any formal obligation.

The runner is a draft, too. Once an executor is available, install the exact
release and Rust toolchain in toolchain.lock.json, validate the release archive
digest, and run:

~~~sh
VERUS_BIN=/absolute/path/to/pinned/verus python3 proofs/ext4/tools/verify.py
~~~

It supplies "--no-cheating" and "--output-json", allows no verification filters,
requires a successful entire-crate result, checks named proof coverage, and
records source hashes. It rejects local proof escapes. The pinned Verus/vstd
trusted foundation is still part of the trust boundary.

A successful result for these models would discharge only their scoped abstract
lemmas. It would not turn the compatibility, security, concurrent refinement,
device, or writable-mount gates green. There is no current successful result.

## Proposed milestone order

- M0: check and repair the abstract replay/journal/gate candidates.
- M1: arbitrary finite traces, multiple transactions, physical persistence and
  crashes at every I/O boundary, journal reuse, and repeated recovery.
- M2: checked ext4/JBD2 parsers and encoders, feature admission, CRC computation,
  sequence/wrap policy, and byte-format refinement.
- M3: ownership, initialization, namespace/handle authorization, and filesystem
  operation preservation.
- M4: linear tracked capabilities and OSTD lock/frame/DMA/device refinements.
- M5: prove a read-only Linux-compatible mount and bounded traversal.
- M6: prove and enable the restricted writable profile.
- M7: separately prove higher concurrency, ordered-data mode, mmap, direct I/O,
  allocation optimizations, and additional ext4 features.

No milestone is complete in this change.
