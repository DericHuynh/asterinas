<!-- SPDX-License-Identifier: MPL-2.0 -->

# Source-block edit coalescing

Several disjoint updates can share one filesystem block, including quota's
1,024-byte units. Constructing a separate full-block replacement for each
update could discard the other changes. BlockEditor retains accepted edits
and their coverage in one candidate derived from an immutable SourceBlock.

A successful edit compares its expected bytes with the original capture,
rejects any previously covered byte, and preserves all earlier covered bytes.
A no-op still reserves its interval. Rejection returns the unchanged owner,
including its hidden coverage. Callers can borrow the candidate's exact bytes
or consume a 4,096-byte/u32-target candidate into the existing AfterImage API;
other geometries and large targets fail without narrowing or losing the owner.
The six public executable APIs are total.

## Checked component scope

The exact 338-line source at SHA256
2d2a09149c9e8f3051d7e6869af6c684ac5e37b902fb51d5cd6bcb397895f676
passed the focused proof-coalesce-04 run: 15 obligations, zero errors and
compilation. Contracts cover original-source binding, exact candidate and
coverage transformations, preservation of previous edits, unchanged failure
owners, and the old-profile projection. The two public proof functions show
commutation of disjoint splices and survival of both edits with unchanged
outside bytes.

The filtered diagnostic records its original flags and full source context;
it is not an official whole-crate certificate. The current branch is based on
b1cc48460eedb0126f2fc8e2ddb8c1d897c3f19b and retains the same module,
direct dependencies, test driver, checker and lock bytes. Five other canonical
proof files changed since that focused snapshot. Whole-crate checking of this
restacked composition is pending.

## Native and API evidence

The actual verifier-compiled library passed coalesce-checked-native-01:

| Unit | Passed |
| --- | ---: |
| Complete-block cases across all seven block sizes | 21 |
| Accepted edits with exact byte checks | 437 |
| Rejected edits with unchanged owner checks | 168 |
| Rust API rejection fixtures | 5 |
| Allowed API compilation control | 1 |

The native driver checks differing edit orders, quota-sized edits, stale
preimages, full/partial overlap, empty/unequal inputs, usize::MAX offsets,
adjacent edits after failure, no-op coverage, and old-profile projection.
API fixtures reject private-field construction, mutable candidate/source
access, cloning the owner and use after a consuming edit. These counts
describe runtime/API checks, not formal obligations or performance results.

[BLOCK_COALESCE_STATUS.json](BLOCK_COALESCE_STATUS.json) retains the complete
native result, proof command/result, artifact and input hashes, original
context binding and earlier attempts. No checks were rerun after restacking.

The tested checker is preserved byte-for-byte and intentionally requires the
original full source/lock hashes. Reproducing proof-coalesce-04 uses the
preserved /root/asterinas-ext4-block-coalesce worktree on
prep/verus-ext4-block-coalesce-checked-04. Running that checker from the new
checkout against the old proof is expected to reject the five different
context hashes. Its guard has not been relaxed.

## Filesystem and framekernel boundary

These are byte transformations against copied RAM provenance. They confer
no allocation, physical mapping, journal, device or write authority. Mapping
quota units to an owned physical home, operation admission, checksum resealing,
complete JBD2 credits, source exclusion, and durable commit/checkpoint remain
separate integration obligations.

Safe CortenMM USegment/VmIo transport, coherent source capture, DMA completion,
flush/reset attestation and mounted VFS publication are not provided here.
No Linux page/folio ownership API or unsafe local implementation is introduced.
Filesystem, full-feature and mount gates remain closed.
