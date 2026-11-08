<!-- SPDX-License-Identifier: MPL-2.0 -->

# Combining checked ext4 components

This historical checkpoint combined four exact checked source snapshots into the feature branch based on `6161986`. It preserves their separate branch history and test evidence. No pull request is merged by this step.

| Component | Focused snapshot | Obligations | Resulting behavior or contract |
| --- | --- | ---: | --- |
| SHA-256/512 | proof-sha-completion-01 | 117 | Streaming/one-shot success exactly within implementation counter bounds; rejected updates preserve state; fixed digest widths |
| Legacy maps | proof-legacy-wide-02 | 48 | A nonzero filesystem count may exceed 2^32 while pointers stay LE32; pointer/logical/source/budget/alias guards remain |
| HTree plans | proof-directory-order-06 | 101 | Byte-name/key comparators, sort-index permutation, filtering and exact successful rebuild/insert/delete/rename catalogues, deltas and NoChange identity |
| Fsverity | proof-verity-builder-06 | 159 | Every successful build returns exact canonical salted-SHA tree bytes, root-dependent descriptor and measured-header digest |

The current focused ledger is **1,947 obligations across 30 modules**, in 25 current snapshots. The source/API/proof inventory is **258 / 1,249 / 985**. SHA keeps 117 obligations; the increase from 1,862 is four legacy, five HTree and 76 fsverity obligations. Counts include Extra04's 78 obligations conditional on an unverified Adiantum dependency.

The historical fsverity snapshot uses the exact SHA source (`3b0e8c89…`), independently checked in the 117-obligation SHA snapshot. It covers canonical height, digest packing, zero padding, parent levels, top-first serialization and exact getters. Successful build completion iff admission, source-owned allocation, signature authorization, immutable inode publication and disk durability remain open.

This branch subsequently renames 16 private cluster-state and nine private SHA/HMAC-core methods to make public-symbol coverage unambiguous. Reversing the 50 identifier-token edits gives byte-identical originals. Public APIs, specifications and proof contracts stay unchanged; proof-private-symbols-02 rechecks cluster 95 + SHA 117 = 212 obligations. It supersedes the two focused rows without changing the 1,947/30 totals. SHA source identity is now 7fede7ca…, so the older fsverity dependency snapshot remains historical; this alpha-equivalence and focused recheck do not replace a strict all-module dependency proof.

HTree's catalogue contracts preserve complete names, inode numbers, generations and types. Merge-sort ordering, full directory wire/layout correctness, complete source-catalogue ownership, permission/namespace authority and concurrent journaling remain open.

## Source and dependency identities

The full component hashes are recorded in [FEATURE_EXPANSION_STATUS.json](FEATURE_EXPANSION_STATUS.json). The immutable compile input is `/task/ext4-expansion/checkpoint-input-07`, created from the published base archive with all 30 exact checked-source overlays and the updated lock. Its complete older Adiantum and extent engines come from the published base, while active proof drafts remain in the live worktree.

The adjacent `dependency-composition.json` records all 32 composed source identities and the exact new-module identities declared by each focused proof command. Fsverity's SHA binding and fast commit's complete preserved extent Mapping source match their focused contexts exactly. Earlier quota-ledger, context/cipher and extra-mode checks retain recorded dependency variants. Extra04's unverified Adiantum contract remains conditional. Source matching and a later coherent compile do not replace a strict composition proof.

The historical all-module `typecheck-21` compiled the immutable input successfully with `--no-verify`; its 32 component sources match those historical prepared identities. It predates the private cluster/SHA method renaming; no new integrated all-module compile has run on this branch. API05 passes all 36 expansion privacy/ownership negatives and nine allowed controls against that same artifact. Typecheck20/API04 and older integrated crypto runs remain historical. All six existing native families now pass on that same actual TC21 artifact. Their explicit assertion counters total 33,740 (fast commit 3,172 + directory 30,568); separate metrics are SHA 616 vectors, legacy 13 tests, unified crypto 201 vectors and fsverity 12 Merkle cases/24 files/420 reads/12 oversized-read rejections. All 71 freshly emitted FC/directory/fsverity files match the previously checked outputs byte-for-byte. Independent image/CRC/hash oracles were not repeated. The final unfiltered strict proof, full official compatibility rerun and feature/mount admission remain pending.

## Existing exact-artifact runtime evidence

The historical component tests below retain their original actual checked-artifact scope. Private-symbols-native-01 additionally replays the unchanged SHA 616-case and cluster 8-scenario drivers on the new focused 212-obligation artifact, with zero SHA mismatches, all 13 existing cluster API rejections and one allowed control. No local production algorithm is supplied:

| Component artifact | Completed native evidence |
| --- | --- |
| SHA completion01 | 616 independent Python hashlib/hmac/HKDF cases; zero mismatches |
| Legacy wide02 | 13 boundary/source/logical/budget/sparse/alias regressions; the old checked artifact fails the intended 2^32+1 negative control |
| Directory order06 | 30,568 assertions, 110 independent libext2fs hash assertions, and five fresh exact-pool e2fsck/debugfs reconstructions |
| Verity builder06 | 12 independent Merkle cases, 24 exact tree/descriptor files, 420 bounded read probes, 12 oversized-read rejections and corruption controls |

The directory depth-two 50,000-entry stress case was excluded; a 400-entry depth-one reconstruction is covered. The legacy suite did not allocate a multi-terabyte snapshot. The wide regression test/runner changes remain on [PR68](https://github.com/DericHuynh/asterinas/pull/68), and the main compatibility runner was not changed here.

[PR67](https://github.com/DericHuynh/asterinas/pull/67), [PR68](https://github.com/DericHuynh/asterinas/pull/68) and [PR69](https://github.com/DericHuynh/asterinas/pull/69) retain the SHA, legacy and directory component history. [PR70](https://github.com/DericHuynh/asterinas/pull/70) retains the separate fsverity-builder publication history. The separate combined-artifact run reuses those unchanged drivers/goldens and confirms coexistence and selected output identity. Historical independent component oracles retain their original artifact scope. Neither native run establishes cryptographic security, strict dependency proof closure or hardware persistence.

Baseline proof reports, verifier trust settings, feature policy and mount gates remain unchanged. The framekernel boundary still uses safe CortenMM/USegment and VmReader/VmWriter mechanisms; no Linux page/folio ownership is imported. This preparation grants no allocation, credential, device-write or writable VFS authority.
