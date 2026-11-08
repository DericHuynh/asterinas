<!-- SPDX-License-Identifier: MPL-2.0 -->

# Checked no_std source package

This branch packages all 258 canonical source files as a safe Rust
`no_std` + `alloc` Cargo library. The tested portable sources, manifest,
lock and source map are copied byte-for-byte from the preserved preparation
worktree. The branch now starts at published
`b1cc48460eedb0126f2fc8e2ddb8c1d897c3f19b`, so its diff contains the
portability edits without repeating the intervening proof-development work.
[Current status](NOSTD_PORTABILITY_STATUS.json) binds those exact inputs
and records the actual Cargo results.

The portable package has **not been formally reverified**. The canonical
source at `5b48f3ec9beb62c5a4220f45e30a779e1b18ce80` passed 5,481
obligations with zero errors and compilation. Its 258 source files,
985 named proofs and 1,249 public executable APIs provide the reference
inventory only. That certificate does not cover the portable source edits.
Canonical native, API and negative-gate results keep their original scope.
The complete canonical evidence is nested under
`canonical_verification_reference` in [verification-evidence.json](verification-evidence.json);
the portable top-level proof result, certificate and library-artifact fields
are null, and the named proof/executable coverage arrays are empty.

## Actual Cargo checks

The existing `/task/ext4-no-std-refresh/checks-01` run passed:

| Check | Result | Elapsed |
| --- | --- | --- |
| Host `cargo check --lib --locked` | passed | 33.140 s |
| `x86_64-unknown-none` `cargo check --lib --locked` | passed | 12.806 s |
| Target `cargo tree -e features --locked` | passed | 0.034 s |

The target feature tree enables `vstd/alloc` and contains neither
`vstd/std` nor `vstd/default`. This statement concerns the `vstd`
features; transitive proc-macro dependencies retain their own features.

The run used nightly `2026-07-21`, one Cargo job, disabled incremental
compilation and dev debug information, offline dependency access, and
`/task/ext4-no-std-refresh/target-nightly` as the external target directory.
Host and target checks used 180-second / 4 GiB address-space limits; the
feature audit used a 30-second / 4 GiB limit. Commands, outputs, result hashes
and the original working directory are recorded in the current status file.

All 261 checked inputs remained unchanged during that run and match this
restacked branch: 258 source files, the package manifest and lock, and the
source map. The root workspace exclusion also matches the tested
preparation bytes. No check was rerun after the exact-byte restack, and
no Verus, native or kernel check was run on this portable source variant.

## Source preservation

[NOSTD_SOURCE_MAP.json](NOSTD_SOURCE_MAP.json) is the immutable historical
transformation record used as a checked input. Its original pending-proof
and not-yet-run Cargo fields describe preparation time; the current
Cargo outcome is recorded separately in
[NOSTD_PORTABILITY_STATUS.json](NOSTD_PORTABILITY_STATUS.json).

The manifest and lock remain byte-identical to tested PR65 commit
`0ff4067f5575954ad7f36beb702c79738abbf6e0`. Official `vstd` is pinned
to `8bf68ee741df833ea5d0fe6a2255126fdea87e47`, with default features
disabled and `alloc` enabled. The root workspace excludes `proofs/ext4`,
while the package keeps its independent workspace. No kernel dependency or
registration is added.

The source edits retain the tested rules: explicit `alloc::vec::Vec`
imports in 109 files; ghost-compatible source-module header imports in 21
files; an unconditional `no_std`/`alloc` crate root; and six spec/proof
references qualified to their original `crate::group::encoded_le`
definition. All 21 rewritten header preimages match the tested PR65 rules.

All 258 source hashes match the source map's canonical/portable pairs.
Every tail beginning at `verus!` is byte-identical to the canonical source
after reversing only the six recorded spec/proof qualifications. Executable
statements, guards, public signatures, proof bodies and module declarations
are preserved. Two aliases of existing public proof lemmas remain in the
tested import repair. There are no module/function exclusions, handwritten
erasure implementations, stubs, assumptions or new local trusted bodies.

The original worktree
`/root/asterinas-ext4-no-std-refresh` is preserved at
`prep/verus-ext4-no-std-refresh-checked-01`; all of its source and evidence
files remain unchanged. Its historical base and the source map are retained
for audit. Mechanical source preservation does not establish a
compiler-erasure theorem or transfer the canonical formal certificate.

## Framekernel boundary

The package remains independent of filesystem registration, credential
policy, allocation capabilities, CortenMM source coherence, DMA, device-write
leases, flush/reset attestation and durable VFS publication. Existing safe
CortenMM `USegment`/`FrameAllocOptions` and `VmReader`/`VmWriter`
adapters remain separate. No Linux page/folio ownership API or unsafe local
implementation is introduced.

The bare-metal target check establishes package type/build portability with
the stated toolchain. It does not establish kernel OSDK linkage, proof-to-
erasure binding, physical I/O refinement, mount admission or full ext4 feature
coverage. Those gates remain closed.
