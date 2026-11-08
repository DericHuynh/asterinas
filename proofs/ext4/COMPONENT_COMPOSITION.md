<!-- SPDX-License-Identifier: MPL-2.0 -->

# Combining checked ext4 components

This branch adds the exact checked Adiantum11 source to the four-component checkpoint based on `a967846`. The separate component histories and test artifacts are preserved. No pull request is merged by this step.

| Component | Focused snapshot | Obligations | Resulting behavior or contract |
| --- | --- | ---: | --- |
| SHA-256/512 | proof-sha-completion-01 | 117 | Streaming/one-shot success exactly within implementation counter bounds; rejected updates preserve state; fixed digest widths |
| Legacy maps | proof-legacy-wide-02 | 48 | A nonzero filesystem count may exceed 2^32 while pointers stay LE32; pointer/logical/source/budget/alias guards remain |
| HTree plans | proof-directory-order-06 | 101 | Byte-name/key comparators, sort-index permutation, filtering and exact successful rebuild/insert/delete/rename catalogues, deltas and NoChange identity |
| Fsverity | proof-verity-builder-06 | 159 | Every successful build returns exact canonical salted-SHA tree bytes, root-dependent descriptor and measured-header digest |
| Adiantum | proof-adiantum-11 | 158 | Exact successful XChaCha12/Adiantum output bytes, canonical field/NH/Poly1305 folds and constructor-bound AES dependency |

The current focused ledger is **2,105 obligations across 31 modules**, in 27 current snapshots. The source/API/proof inventory stays **258 / 1,249 / 985**. The additional 158 obligations are Adiantum11; Extra05 replaces Extra04 at the same 78-obligation count after auditing the selected source and all seven declared crypto dependencies against this branch. These are filtered component checks, not strict composition certification.

The fsverity snapshot uses the exact new SHA source (`3b0e8c89…`), independently checked in the 117-obligation SHA snapshot. It covers canonical height, digest packing, zero padding, parent levels, top-first serialization and exact getters. Successful build completion iff admission, source-owned allocation, signature authorization, immutable inode publication and disk durability remain open.

HTree's catalogue contracts preserve complete names, inode numbers, generations and types. Merge-sort ordering, full directory wire/layout correctness, complete source-catalogue ownership, permission/namespace authority and concurrent journaling remain open.

## Source and dependency identities

The full component hashes are recorded in [FEATURE_EXPANSION_STATUS.json](FEATURE_EXPANSION_STATUS.json). This branch copies only `adiantum.rs` from proof-adiantum-11 (SHA-256 `34e764409e5409928d7fcd2be42d2ccd482aab15a9421dbe27b55456b6dd08fb`). AES matches the 78-obligation snapshot exactly. The historical immutable compile input `checkpoint-input-07` predates this overlay and retains the older Adiantum/extent sources; its source map is preserved rather than relabeled current.

The historical `dependency-composition.json` records the 32 source identities declared for the earlier checkpoint. Extra05 now uses exact matching current AES, SHA, context, base-cipher, HCTR2, SM4 and Adiantum sources. Extra04 and its different unverified Adiantum revision remain historical. Other recorded dependency variants and the unverified retained extent engine remain explicit; source matching and focused module proofs do not replace the final strict composition gate.

The historical `typecheck-21` passed `--no-verify`, API05 and six native families on its own actual all-module artifact. That artifact contains the older Adiantum source, so it is not current compile/runtime evidence for this overlay. Its 33,740 explicit assertion counters and separate SHA/legacy/crypto/fsverity counts remain bound to TC21, with all 71 emitted files matching their earlier independently checked outputs. No new all-module compilation, strict proof or compatibility suite was run for this branch.

## Existing exact-artifact runtime evidence

These completed tests use each component's actual compiled checked artifact. They have been audited, without rerunning or replacing their implementations:

| Component artifact | Completed native evidence |
| --- | --- |
| SHA completion01 | 616 independent Python hashlib/hmac/HKDF cases; zero mismatches |
| Legacy wide02 | 13 boundary/source/logical/budget/sparse/alias regressions; the old checked artifact fails the intended 2^32+1 negative control |
| Directory order06 | 30,568 assertions, 110 independent libext2fs hash assertions, and five fresh exact-pool e2fsck/debugfs reconstructions |
| Verity builder06 | 12 independent Merkle cases, 24 exact tree/descriptor files, 420 bounded read probes, 12 oversized-read rejections and corruption controls |
| Adiantum11 | 26 pinned Linux golden commands, 51 independent Python/OpenSSL golden commands and 11 bounds/counter controls using the actual focused-checked provider |

The directory depth-two 50,000-entry stress case was excluded; a 400-entry depth-one reconstruction is covered. The legacy suite did not allocate a multi-terabyte snapshot. The wide regression test/runner changes remain on [PR68](https://github.com/DericHuynh/asterinas/pull/68), and the main compatibility runner was not changed here.

[PR67](https://github.com/DericHuynh/asterinas/pull/67), [PR68](https://github.com/DericHuynh/asterinas/pull/68) and [PR69](https://github.com/DericHuynh/asterinas/pull/69) retain the SHA, legacy and directory component history. [PR70](https://github.com/DericHuynh/asterinas/pull/70) retains the separate fsverity-builder publication history. The historical combined-artifact run reuses those unchanged drivers/goldens and confirms coexistence for its older source identities. It does not include this Adiantum source. Historical independent component oracles retain their original artifact scope. Native runs establish neither cryptographic security, strict dependency proof closure nor hardware persistence. Adiantum's general inverse, constant-time and physical-erasure properties remain open; the reference correction and successful-output scope are recorded in [ADIANTUM_REFINEMENT.md](ADIANTUM_REFINEMENT.md).

Baseline proof reports, verifier trust settings, feature policy and mount gates remain unchanged. The framekernel boundary still uses safe CortenMM/USegment and VmReader/VmWriter mechanisms; no Linux page/folio ownership is imported. This preparation grants no allocation, credential, device-write or writable VFS authority.
