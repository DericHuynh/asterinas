<!-- SPDX-License-Identifier: MPL-2.0 -->

# Adiantum byte refinement

This branch replaces the older implementation draft with the exact checked
`proof-adiantum-11` source. All 158 selected Adiantum obligations passed with
zero errors and compilation. Its AES dependency is byte-identical to the
78-obligation `proof-aes-08` snapshot. The check is filtered; no unfiltered
whole-crate certificate is added.

| Ledger | Focused obligations | Checked new modules |
| --- | ---: | ---: |
| Previous checkpoint | 1,947 | 30 |
| Adiantum11 addition | 158 | 1 |
| This branch | 2,105 | 31 |

The source/API/named-proof registry stays 258 / 1,249 / 985. Extra05 replaces
Extra04 at the same 78-obligation count: the selected extra-mode source and all
seven declared crypto dependencies match this branch exactly. This source
audit does not establish strict whole-filesystem dependency composition.

## Checked behavior

Successful `xchacha12_bytes` results equal the pure byte reference, including
HChaCha-derived subkeys, counter words, full blocks and partial final blocks.
Successful encryption/decryption results equal the Adiantum reference with
an AES-256 key bound to the actual XChaCha-derived schedule. Private contracts
cover little-endian codecs, canonical arithmetic modulo 2^130-5, conditional
reduction, fixed-step multiplication, NH chunk padding and passes, Poly1305
block folds, and final output composition.

The proof exposed a reference-model issue: encoding an arbitrary natural
required an explicit range reduction before narrowing it to u128.
`encoded128` now reduces modulo 2^128 before its bounded cast. This states the
protocol's low 128-bit encoding directly. No cipher algorithm change is claimed.

The public implementation limits remain a 32-byte key, a 32-byte tweak, at most
16 MiB per operation, an Adiantum minimum length of 16 bytes, and the recorded
XChaCha counter-fit rejection. These are successful-result refinement
contracts; general completion iff admission and a general encryption/decryption
inverse theorem are not claimed.

## Exact artifact checks

`adiantum-checked-native-11` imports the actual compiled Adiantum11/AES library;
its driver contains no replacement cipher. It replays 26 pinned Linux golden
commands and 51 independent Python integer/OpenSSL golden commands without
mismatches. Eleven additional controls cover invalid key/length inputs,
empty XChaCha input, the last valid counter block, counter exhaustion, and
oversized-input rejection. Native checks complement the proof; they are not
formal cryptographic-security evidence.

| Identity | SHA-256 |
| --- | --- |
| Adiantum source, 1,658 lines | `34e764409e5409928d7fcd2be42d2ccd482aab15a9421dbe27b55456b6dd08fb` |
| AES dependency | `035f6c518e3567cd5b83626800eefb0da4b058d3cfbeee1f9592d41a2afcdfb7` |
| Actual proof11 provider | `4a9d8f1ef834ec60f1f0da41234e77a72efffd5d8fba161f24023084c6b6c4c6` |

Exact commands, source contexts, provider/driver/golden manifests and results
are recorded in `FEATURE_EXPANSION_STATUS.json` and the retained
`/task/ext4-expansion/adiantum-checked-native-11` evidence directory.
The Linux reference pin remains
`028ef9c96e96197026887c0f092424679298aae8`.

## Boundaries

Cryptographic indistinguishability/authentication, constant-time compilation,
physical key erasure, mounted key provisioning and nonce authority remain
outside this result. Adiantum is not an authenticated cipher. No writable VFS,
journal durability or source-allocation authority follows from these byte
contracts.

The historical TC21/API05/six-family native artifacts retain the older
Adiantum source. They remain valid evidence for their own recorded inputs and
are marked noncurrent for this branch. No new all-module compilation, native
composition or strict whole-crate run was performed here.

The framekernel trust boundary and safe CortenMM/USegment ownership rules are
unchanged. No Linux page/folio ownership or new unsafe kernel code is added.
Baseline proof reports, verifier trust settings, source pins and feature/mount
gates are unchanged.
