<!-- SPDX-License-Identifier: MPL-2.0 -->

# Frozen ext4 component composition

All **32 expansion modules** now have successful focused checks, totaling **2,339 obligations across 27 current snapshots**. The locked inventory remains **258 source files, 985 named public proofs and 1,249 public executable functions**. These remain component results; the combined current source separately passed official-strict-02 with 5,481 obligations and zero errors.

The exact source is frozen in `/task/ext4-expansion/checkpoint-input-08`. Its manifest SHA-256 is `4d822a1cb7808131537333f09b42de7f6f61513b878540fc47b0a2f56d0caf07`. All 258 live source files match that manifest, all 32 expansion sources match successful immutable focused snapshots, and the 226 baseline source files remain unchanged from published `a967846`. No proof source, lock, verifier, compatibility runner or gate was changed during the official strict run. The certified source bytes are committed at `5b48f3ec9beb62c5a4220f45e30a779e1b18ce80`.

| Latest checked component | Snapshot | Obligations | Contract or change |
| --- | --- | ---: | --- |
| Cluster lifecycle and SHA/HMAC/HKDF | proof-private-symbols-02 | 212 | Existing contracts rechecked after private method renaming; public APIs and proof names unchanged |
| Fsverity | proof-verity-completeness-03 | 174 | Canonical successful builder content plus numeric layout/build success exactly when the existing admission predicate holds |
| Adiantum | proof-adiantum-11 | 158 | XChaCha12 and Adiantum encrypt/decrypt output refinement to the recorded standard reference models |
| Extra cipher interfaces | proof-extra-modes-05 | 78 | Byte, binding, preparation, dispatch and retirement contracts rechecked with the checked Adiantum source |
| Extent editing/tree plans | proof-extent-edit-17 | 219 | Exact map edits, nonaliasing and tree-plan checksum/reference invariants |

Other checked components, including legacy wide maps, HTree catalogues, fast commit and the remaining feature codecs/protocols, retain their exact ledger entries.

The private-symbol update changes nine SHA and 16 cluster method identifiers. Reversing those identifiers reproduces the previous source bytes exactly. The unchanged strict matcher now finds exactly one result for each of the 44 required public names in those modules; 25 were formerly ambiguous. The public inventory, contracts, executable logic and matcher remain unchanged.

## Dependency boundaries

The current source/dependency map is `/task/ext4-expansion/main-source-integration-02/final-dependency-composition.json`. Extra05 and fsverity-completeness03 were checked with SHA source `3b0e8c89…`; current SHA `7fede7ca…` differs by the byte-exact private renaming above. Older context/cipher and quota caller revisions remain recorded separately.

Fast commit's focused context contains the older complete extent source. Its Mapping enum is byte-identical to current Extent17, and the current full extent implementation is independently checked. These source relations do not substitute for strict dependency composition. No caller context has been silently relabeled as a check of different bytes.

The unchanged official **unfiltered strict** runner passed this frozen source and compiled the core: **5,481 obligations, zero errors**, in 1,720.98 seconds. The report SHA-256 is `19a399e2da952b94fb2d6aaa480ed277691ea13b96800384011ea0496d588077` and the emitted-library SHA-256 is `b5577b84c2e2d66e8b3f0bbbf2c483620dbcdfc4186481293d82add60be6336a`. The historical 3,142-obligation baseline and its complete evidence remain preserved. This closes strict dependency composition for the declared source/model contracts; it does not enable mounting or establish physical durability.

Current-artifact compatibility passes 372 host tests and 376 API rejections. Fresh negative gates: passed; timeout regression: passed.

## Runtime evidence and remaining work

The private-symbol artifact passes the unchanged 616-vector SHA corpus, eight cluster scenarios, 13 existing cluster API rejection cases and one allowed control. Those are repeated boundary checks, not additional unique API cases.

The fsverity-completeness artifact passes 12 independent Merkle cases, 24 exact tree/descriptor files, 420 bounded reads and 12 oversized-read rejections. Its numeric admission driver adds 385 layout cases and 121 bounded builds, using an independent unbounded-integer oracle. Huge layout-only arithmetic does not allocate huge images or confer owned memory.

The previous TC21 all-module artifact passed six native families, 33,740 explicit assertions, separate SHA/legacy/crypto/fsverity metrics, 71 output-byte comparisons and API05. Those results remain historical because TC21 predates the latest source revisions. Current Extent17 runtime evidence is recorded only when its final report is available.

The [SHA](https://github.com/DericHuynh/asterinas/pull/67), [legacy](https://github.com/DericHuynh/asterinas/pull/68), [directory](https://github.com/DericHuynh/asterinas/pull/69) and [fsverity-builder](https://github.com/DericHuynh/asterinas/pull/70) branches retain their component history without PR merges.

Numerical admission and reference-model proofs do not establish owned source/allocation, signatures, cryptographic security, whole-filesystem recovery, namespace/journal composition or physical persistence. HTree merge-sort ordering and full wire/layout proof closure remain open. Mount and writable VFS admission remain gated. The runtime boundary continues to use safe framekernel/CortenMM mechanisms without importing Linux page/folio ownership.

## Current full-proof artifact runtime checks

The exact strict02 library also passes all 24 selected native regression families in strict-composed-native-01. This reruns the recorded crypto, extents, Merkle, journal, quota, cluster, casefold, orphan, legacy and inline drivers through one provider. It includes 1,226,715 casefold comparisons, 219,125 extent assertions, 15 fresh debugfs extent probes, two read-only extent-image fsck checks and one freshly rebuilt quota-image fsck check. Per-family units and oracle provenance are retained in verification-evidence.json; historical C/golden generators are distinguished from fresh oracle executions.

This is selected runtime regression coverage. Four executable expansion modules still lack dedicated native replays (orphan_lifecycle, ea_restart, orphan_chain, resize_plan), and ea_repeated_recovery is proof-only. No filesystem feature-completeness ratio, mount, device authority or physical durability follows from 24 passing families. The current official 372-test compatibility suite, 376 API rejections, six failure gates and timeout regression also pass.
