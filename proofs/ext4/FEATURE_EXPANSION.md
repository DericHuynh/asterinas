# Ext4 feature expansion: implementation and proof ledger

This branch adds executable feature components before completing their proofs and filesystem integration, as requested. The last whole-crate verified baseline is commit `9083e1d36cb433927df6c0b636c8377a4c350c22`: 3,142 obligations, 915 named proofs, 775 public executable APIs, 372 native tests and 340 API rejection cases. That evidence applies to the baseline bytes. It does not certify new files.

All 32 new host modules are now declared in the actual model entrypoint and pinned source/API/proof inventory: 258 source files, 979 named proofs and 1,249 public executable APIs. This records what must be checked; a new strict whole-crate result is still pending. Diagnostic snapshots explicitly declare their selected modules, preserve their exact bytes, and retain every failure. Compile-only diagnostics use `--no-verify` and are never proof evidence. Focused proof checks use module filters and still require a later unfiltered strict check before publication as verified code.

The existing full-feature and mount gates remain closed. A completed codec, numeric protocol or test image does not authorize a mounted operation.

| Design domain | Executable work added | Current proof boundary | Remaining filesystem work |
| --- | --- | --- | --- |
| Legacy block maps | Direct/single/double/triple decomposition, source-block lookup, sparse reads and bounded whole-tree collection | Exact path, lookup/read bytes, emitted address ranges and data/metadata nonalias/claim-membership passed a focused check; full reachable-tree/path coverage remains open | Allocation, truncate/revoke transactions and whole-source ownership admission |
| Inode formats | Variable-inode CRC, type/device codecs, fast-symlink storage and separate live plain-target validation | Focused check passed for exact checksum/masked bytes, sealing frames and plain-target bounds | Unified live-inode admission, long/encrypted symlinks and special-file VFS operations |
| Inline data | system.data decoding, reads, fixed-capacity regular writes/truncation and directory decoding | Focused check passed for exact source/read/write bytes, cached non-overlap and preservation of every other attribute header/local value | Directory edits, re-layout, growth, block conversion and journal composition |
| GDT_CSUM | Linux CRC16 descriptor calculation, sealing and lazy flags | Focused check passed for exact CRC and checksum-field-only mutation | Whole-filesystem legacy admission and group initialization transactions |
| META_BG / resize | Descriptor copies, sparse backups, reserved GDT pointers and grow/publication protocol | Descriptor geometry, complete ordered backups/reserved pointers and exact grow edit/publication protocol passed focused checks | Actual bitmap/table/GDT/superblock after-images, owned allocation and interrupted-grow recovery |
| BIGALLOC | Cluster reserve/map/unmap/init/pin/retire bookkeeping | Consuming-owner state, uniqueness, initialization/failure/reset, bitmap and modeled quiescence contracts passed a focused check (95) | Real data I/O authority, partial-cluster reconciliation, extent/quota integration and recovery |
| Extents | Mapping edits, initialized/unwritten conversion and depth 0–5 tree rebuilding | Mapping/nonalias/canonical-layout contracts under construction | Owned allocator, zeroing, bitmap/quota/revoke changes and durable publication |
| DIR_INDEX / LARGEDIR | Linear/HTree rebuild, insert/delete/same-directory rename, six legacy hashes, collision continuation and depth 0–2 | Executable implementation tested; full refinement proof pending | Target inode checks, cross-directory structural transactions, encrypted/casefold directories and allocation |
| Orphans | Legacy chain, orphan-file CRC/slots/global duplicate admission and reclamation lifecycle | Lifecycle and legacy-chain checks passed; the chain check covers catalogue walks, acyclicity and exact insert/remove link words (45); orphan-file proofs remain under construction | Actual orphan allocation/growth/fallback, inode/bitmap/quota/revoke transactions and recovery discovery |
| MMP | Exact 1,024-byte record plus claim/read/write/flush/re-read/heartbeat/clean-stop protocol | Exact codec, modeled protocol history, pending-command binding, abort retention and fault absorption passed a focused check (105) | Real freshness/clock/visibility bounds and mount exclusion capability |
| Journal formats | JBD2 v1/v2/v3 checksums, 32/64-bit tags, UUID/escape/revoke formats | Feature negotiation, superblock/commit formats (40) and tag/descriptor/revoke/escape codec contracts (63) passed focused checks | Integrated versioned writer/scanner/recovery, async commits, external journals and all data modes |
| Fast commit | TLV builder, valid-tail prefix scanner, replay intents and inode merge rules | Exact CRC segments, record provenance and committed-prefix preservation under construction | Source-owned replay executor, real area allocator and full/fast-commit scheduling/exclusion |
| Repeated EA recovery | Retained target and fresh bootstrap/scan/admission with exact repaired-byte comparison | Focused check passed for retained target, exact repaired-byte comparison and guarded restart histories | Universal repaired-image acceptance and runtime reset lease |
| Quota / project | vfsv0/vfsv1 radix images, records, consuming U/G/P reservation/transfer/free ledger and project inheritance checks | Project fields/inheritance (11), exact ledger lifecycle/framing (68) and quota wire decoding/rebuild contracts (89) passed focused checks | Whole free-list/source ownership, authoritative clock/credentials and atomic quota+inode/allocator transactions |
| Casefold | Pinned Unicode 12.1 NFDICF, Hangul, ignored-character barriers and strict/opaque UTF-8 rules | Pinned-table shape/order/scalar/expansion (150) and UTF-8/search/normalized-key refinement to the Rust reference model (65) passed focused checks | Formal Linux Unicode equivalence and casefold/encryption lookup/hash/duplicate/mutation integration |
| Fscrypt | Policy/context/KDF/IV handling, AES, SM4, XTS, CBC-CS3, CBC-ESSIV, Adiantum-XChaCha12-AES and AES-256-HCTR2; unified currently accepted cipher-pair dispatch | AES schedule/block refinement, bidirectional reference round-trip and retirement framing (78), SM4 refinement (28), and policy/context/KDF/IV reference contracts (57) and base XTS/CBC-CS3 key-binding, data/name and mode byte contracts (73) passed focused checks; remaining mode composition proofs are open | Remaining primitive/mode composition, key provisioning, nonce authority, no-key names, encrypted symlinks and VFS transactions |
| Fsverity | SHA-256/512 Merkle construction, descriptors, layout and verified-read algorithm | Streaming SHA-256/512, HMAC/HKDF reference and finalization contracts passed a focused check (115); salted-tree/path composition remains under construction | PKCS#7 verification/policy, source-owned tree allocation, enable transaction and immutable runtime binding |
| Framekernel runtime | Safe CortenMM USegment/FrameAllocOptions and VmReader/VmWriter adapter; private BIO buffers, no_std source package and scoped RAM Snapshot bridge | Existing three adapter kernel tests passed. The separate package/bridge passed source and feature checks; its scoped RAM test passed 1/0 with 146 filtered. Formal transport refinement remains open | Proof-to-erasure binding, coherent source capture/device-wide alias exclusion, hardware atomicity/drain/reset contracts and mounted VFS |

The DIR_PREALLOC and IMAGIC_INODES compatibility markers still need an explicit pinned-Linux policy review. JOURNAL_DEV requires an external-device ownership and recovery implementation. COMPRESSION and DIRDATA remain intentional Linux-compatible rejections. Existing READONLY and STABLE_INODES restrictions remain applicable.

Focused diagnostics currently cover **24 unique new modules and 1,327 obligations**, with zero reported errors and compilation, across the 20 current entries below. Superseded snapshots are excluded from this total.

| Module or bundle | Obligations | Snapshot |
| --- | ---: | --- |
| GDT_CSUM, inode payload, orphan lifecycle, EA restart/repeated recovery | 84 | proof-core-slices-01 |
| Descriptor geometry | 49 | proof-meta-04 |
| Unicode table shape | 150 | proof-unicode-04 |
| Resize planning/publication | 41 | proof-resize-06 |
| Inline bytes and other-attribute framing | 27 | proof-inline-09 |
| JBD2 feature/checksum formats | 40 | proof-jbd2-features-04 |
| Project-ID fields/inheritance | 11 | proof-project-01 |
| SM4 schedule/block refinement | 28 | proof-sm4-02 |
| Legacy map/read and collection claims | 44 | proof-legacy-06 |
| Legacy orphan chain | 45 | proof-orphan-chain-01 |
| Cluster owner/initialization lifecycle | 95 | proof-cluster-07 |
| Casefold reference pipeline | 65 | proof-casefold-02 |
| AES reference/round-trip/retirement | 78 | proof-aes-08 |
| Quota reservation ledger | 68 | proof-quota-ledger-05 |
| SHA-256/512, HMAC and HKDF | 115 | proof-sha2-08 |
| Fscrypt policy/context/KDF/IV | 57 | proof-fscrypt-context-05 |
| JBD2 tag/descriptor/revoke/escape codecs | 63 | proof-jbd2-tags-11 |
| Quota wire decoding/rebuild | 89 | proof-quota-wire-05 |
| MMP codec and reported protocol history | 105 | proof-mmp-08 |
| Base fscrypt XTS/CBC-CS3 and binding byte contracts | 73 | proof-fscrypt-cipher-05 |

Each result uses an immutable snapshot and a module filter. The recorded focused commands are filtered diagnostics, not the final unfiltered strict --no-cheating gate or a proof of filesystem composition. Exact commands, flags and source hashes are recorded in [FEATURE_EXPANSION_STATUS.json](FEATURE_EXPANSION_STATUS.json). Earlier failed and superseded snapshots remain historical evidence.

Pinned references for the expansion are listed in [FEATURE_EXPANSION_SOURCES.json](FEATURE_EXPANSION_SOURCES.json). Draft defects and their discovery methods are recorded in [FEATURE_EXPANSION_FINDINGS.md](FEATURE_EXPANSION_FINDINGS.md).

## Validation so far

The implementation diagnostics are independent of formal discharge:

- The first 28 modules compiled together in typecheck-05 before proof annotations. Typecheck-17 compiles the coherent all-32-module checkpoint, including all current focused-checked components. Four unproved files use immutable drafts that reached body checking; ongoing repairs remain separate. This compile-only result does not certify later live changes or replace the pending strict proof.
- HTree outputs were installed into real ext4 images across several block/checksum/filetype profiles, including an indexed depth-one directory; e2fsck and debugfs accepted the completed fixtures.
- Casefold-checked-native-02 imports the proof-casefold-02 artifact directly and matches the pinned Linux normalization corpus in 1,226,715 comparisons with zero mismatches. This is checked-artifact interoperability evidence, not a formal C-equivalence theorem.
- SHA/HMAC/Merkle results passed 78 independent Python-oracle cases; AES/XTS/CTS passed 59 OpenSSL/NIST cases. These tests establish no cryptographic proof or constant-time guarantee.
- Checked-sha2-native-01 imports the focused-checked 115-obligation SHA/HMAC/HKDF artifact and matches 616 Python hashlib/hmac vectors with zero mismatches, covering streaming/padding boundaries, long keys, HKDF maximum/partial outputs and rejected inputs. No replacement hash implementation is supplied by the harness.
- Journal/extent diagnostics passed 2,859 assertions; e2fsprogs replayed generated escaped journal payloads in 28 independent recovery cases across checksum/version-width profiles, revokes and corrupted controls.
- Legacy maps, inline data, inode checksums, symlink classification and descriptor CRCs were compared with Linux/libext2fs/debugfs and real images. An inconsistent inline-directory i_size was caught and corrected.
- Sparse backup enumeration matched an independent oracle up to 4,294,967,000 groups in under 4 ms per native test process. The previous draft scanned every group.
- Six plain fast-symlink regressions cover empty/interior-NUL/unterminated targets, incompatible flags and invalid geometry.
- The integrated 32-module artifact passed 474 crypto/context/verity commands with every primitive imported from that artifact; none of the native programs supplied replacement algorithms. These are runtime checks, not proofs.
- Cipher-checked-native-01 imports the focused-checked AES/SHA/context/cipher artifact and replays all 59 pinned OpenSSL/NIST-validated commands successfully, including mode tails, V1/V2 dispatch, binding and retirement controls. These are runtime inverse checks, not a full mode-inverse or cryptographic security theorem.
- Mmp-checked-native-01 imports the focused-checked MMP artifact and passes three codec/protocol tests, including ordered claim/stop, stale or competing observations, backward clocks, and an aborted descriptor followed by late success. Reports remain modeled software inputs; no physical lease or persistence authority is established.
- The focused-checked AES/SM4 artifacts pass the published AES-128/AES-256 and SM4 known-answer vectors, inverse checks and retired-key rejection. The first vector harness incorrectly expected AES-192 support; the API correctly rejects that unsupported key length. That failed expectation and its corrected run are retained separately.
- Cluster-init-native-07 imports the focused-checked proof-cluster-07 artifact and passes eight native scenarios, including six completion permutations, plus the existing 13 cluster API rejection cases. The scenarios exercise the modeled standalone ledger; they do not attest real concurrent I/O, reset quiescence or durability.
- Quota-wire-checked-native-01 imports the focused-checked 89-obligation quota wire artifact and passes two wire tests plus three user/group/project file rebuilds. All three match the earlier fixtures byte-for-byte and pass e2fsck; whole free-list/source ownership and filesystem transaction composition remain pending.
- The original 17 expansion API rejection cases plus three allowed-use controls passed against typecheck-13; four cipher cases also passed against focused-checked artifacts. Quota-boundaries-native-01 adds 12 quota privacy/ownership rejection cases and three allowed controls against proof-quota-ledger-05. Seven fast-commit Builder/Scan ownership and privacy cases plus three controls also pass. Expansion-boundaries-native-03 reruns all 36 new negative API cases and nine allowed controls against the same typecheck-17 artifact, giving 376 expected cases with the baseline 340; the full official compatibility suite has not been rerun. Repeated cluster cases are not counted again.
- Three CortenMM adapter tests ran in the kernel under QEMU. Four host regressions check the test-only x86 QEMU exit classifier. Zero selected guest tests remain allowed by the existing harness and are not counted as execution evidence.
- The no_std+alloc source package is published separately in [PR65](https://github.com/DericHuynh/asterinas/pull/65), commit 0ff4067, with host/target Cargo checks and a compile-only Verus frontend check. The separate CortenMM bridge, [PR66](https://github.com/DericHuynh/asterinas/pull/66) at eef3f69, passed its kernel-nightly source check, alloc-present/std-absent audit and exact scoped RAM guest test: 1 passed, 0 failed, 146 filtered, with unchanged sources/fixtures and branch-local generated dependencies. The ANSI-normalized classification is snapshot-ktest-02-classification-01. No filesystem registration or physical-source admission is enabled; these branches retain older snapshots and do not certify the strengthened live feature branch.

Proof preparation also exposed missing whole-file orphan duplicate rejection, duplicate logical-cluster reservations and acceptance of a late success after failed initialization. The implementations now reject these cases or require explicit reset. The cluster invariants have now passed their focused 95-obligation check; the final strict proof and cross-layer composition remain pending.

The scratch evidence ledger is `/task/ext4-expansion/session-status.json`. Source snapshots, commands, output, solver logs and failed attempts are retained beneath that directory. Dense test images were made sparse only after checking identical SHA256 contents. Old completed solver logs were archived with per-file hash verification.

## Completion criteria

Each row needs exact source/format refinement, total public APIs, ownership and concurrency invariants, crash and restart closure where relevant, Linux image interoperability, negative API tests and a strict whole-crate proof against the locked source inventory. Mounted support additionally requires composition across allocator, namespace, quota, orphan, crypto and device layers.

Numeric identifiers and modeled completion events do not confer device, inode, frame, allocation or credential authority. BIO completion and 512-byte sector metadata do not establish 4 KiB failure atomicity or power-loss durability. Those premises must be supplied by the runtime boundary before writable admission.
