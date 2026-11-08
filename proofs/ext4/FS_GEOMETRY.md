# Checked numeric filesystem geometry

This component describes ext4 blocks from 1 KiB through 64 KiB using u64
filesystem-block counts and partition-byte bounds. It adds checked byte,
sector, primary-superblock and quota-unit placements without narrowing the
existing 4096-byte/u32 protocol.

The source is a numeric description. It grants no source exclusion, allocator
ownership, CortenMM frame/DMA loan, device access, atomicity or durability
authority. The existing framekernel boundary and filesystem admission/mount
gates remain unchanged.

| Boundary | Result |
| --- | --- |
| Construction | Accepted ext4 block size, nonzero count, full filesystem byte range fits the supplied partition |
| Block lookup | Exact byte/512-byte-sector interval or rejection, with no wrapping arithmetic |
| Partition translation | Checked sector origin and end inside the parent device's sector bound |
| DMA buffer arithmetic | Nonempty sector-aligned subrange confined to the supplied byte length |
| Superblock/quota placement | Exact 1024-byte superblock and quota-format unit locations for the selected filesystem geometry |
| 4096-byte compatibility | Exact old byte/sector/primary/quota projections proved |

A partition's sector bound is its complete-sector prefix
floor(partition_bytes / 512). Unaligned trailing bytes do not establish a
whole-byte-partition bound. The 512-byte sector constant is an addressing
unit; it is not an atomic-write premise.

## Recorded checks

| Check | Exact scope | Result |
| --- | --- | --- |
| proof-fs-geometry-03 | Focused module, actual Verus-compiled library | 29 obligations, zero errors |
| fs-geometry-checked-native-01 | Actual focused library, finite numeric cases | 1,225 passed |
| Rust privacy | Five exact invalid callers | Five rejected with their expected error codes |
| Allowed caller | Construction, duplicate, placement and lookup | Compiled and executed successfully |

These are the recorded source and artifact bindings:

| Item | SHA256 |
| --- | --- |
| src/fs_geometry.rs | 65e6ad5666a0ca9039f8381c5b94aac7ebc80e543d0ec445862f555300db64e1 |
| Focused compiled library | 4c6aa770caa99eecd7ddbb6a38622fd8fa3047f04896819ef7c27e35ccb54462 |
| Tested numeric driver | 566f33da3af9373fe3d2c5b7942add7d01f546cc5d27f4518307e311779d168d |
| Tested numeric case file | be08d2d8a6499389a475da6d9f474e29cb635ff62a0195d06fc7d9edfa603e94 |
| Native result | 36c03284b4d739e4efb3ea1c3ef3b89772e5603219f10ed11fae4ee96922f404 |

The native driver, numeric cases, allowed caller and five rejected source
files under [tests/fs_geometry](tests/fs_geometry) are exact copies of the
tested files. Only the negative manifest's task-local absolute source paths
were converted into paths relative to that test directory.
[evidence.json](tests/fs_geometry/evidence.json) records all original hashes
and command/result bindings. The native tests import the actual compiled
geometry API and contain no replacement geometry implementation.

The recorded focused diagnostic omitted --no-cheating; this is disclosed
in the evidence. It selected only fs_geometry and does not certify the
whole crate. The official required flags and verifier pins were not changed.

This branch was restacked onto b1cc48460eedb0126f2fc8e2ddb8c1d897c3f19b
without changing the checked geometry source. Its sole production dependency,
block_size.rs, matches both the focused snapshot and the certified parent.
The current registry is 259 sources, 989 named proofs and 1,262 executable
APIs. The parent's 5,481-obligation certificate covers its original 258-source
snapshot; it does not cover this extension. A new full check is pending.

## Reproduce with an actual artifact

Use the pinned Verus release and Rust toolchain from
[toolchain.lock.json](toolchain.lock.json). Set paths to that installation;
the checker has no task-local path defaults.

From proofs/ext4, create a fresh focused snapshot, compile it with the
official strict flags, and run the copied native assets:

    python3 tools/check_fs_geometry.py \
      --verus /path/to/pinned/verus \
      --rustc /path/to/pinned/1.99.1/bin/rustc \
      --verus-lib-dir /path/to/pinned/verus-libraries \
      --out-dir /tmp/fs-geometry-replay-01

To reuse an existing successful focused diagnostic snapshot:

    python3 tools/check_fs_geometry.py \
      --proof-dir /path/to/proof-fs-geometry \
      --rustc /path/to/pinned/1.99.1/bin/rustc \
      --verus-lib-dir /path/to/pinned/verus-libraries \
      --out-dir /tmp/fs-geometry-replay-02

The snapshot format includes src/, build/libverified_ext4.rlib,
stdout with the JSON verification results, command.json, result.json,
source-sha256.json and baseline-toolchain.lock.json. The checker requires
a successful nonzero 29-obligation focused run, matching geometry/dependency
bytes, unchanged pins/required flags, and an actual compiled library. It
checks the full pinned verifier commit for fresh builds (or exact recorded
provider hashes for the original snapshot), and records and rechecks provider,
snapshot, test, compiler and library hashes
before/after execution. Cases require a 64-bit ELF host target.

The portable wrapper has been prepared and syntax-checked but has not been
executed after packaging. The recorded 1,225/5/1 results above belong to the
original hash-bound driver run. Neither wrapper mode replaces the unchanged
official whole-crate runner or creates a kernel/runtime-refinement claim.
