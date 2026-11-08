# Ext4 feature expansion: implementation and proof ledger

This branch adds executable feature components before completing their proofs and filesystem integration, as requested. The last whole-crate verified baseline is commit `9083e1d36cb433927df6c0b636c8377a4c350c22`: 3,142 obligations, 915 named proofs, 775 public executable APIs, 372 native tests and 340 API rejection cases. That evidence applies to the baseline bytes. It does not certify new files.

All 32 new host modules are now declared in the actual model entrypoint and pinned source/API/proof inventory: 258 source files, 969 named proofs and 1,249 public executable APIs. This records what must be checked; a new strict whole-crate result is still pending. Diagnostic snapshots explicitly declare their selected modules, preserve their exact bytes, and retain every failure. Compile-only diagnostics use `--no-verify` and are never proof evidence. Focused proof checks use module filters and still require a later unfiltered strict check before publication as verified code.

The existing full-feature and mount gates remain closed. A completed codec, numeric protocol or test image does not authorize a mounted operation.

| Design domain | Executable work added | Current proof boundary | Remaining filesystem work |
| --- | --- | --- | --- |
| Legacy block maps | Direct/single/double/triple decomposition, source-block lookup, sparse reads and bounded whole-tree collection | Exact path and source-trace contracts under construction | Allocation, truncate/revoke transactions and whole-source ownership admission |
| Inode formats | Variable-inode CRC, type/device codecs, fast-symlink storage and separate live plain-target validation | Focused check passed for exact checksum/masked bytes, sealing frames and plain-target bounds | Unified live-inode admission, long/encrypted symlinks and special-file VFS operations |
| Inline data | system.data decoding, reads, fixed-capacity regular writes/truncation and directory decoding | Focused check passed for exact source/read/write bytes, cached non-overlap and preservation of every other attribute header/local value | Directory edits, re-layout, growth, block conversion and journal composition |
| GDT_CSUM | Linux CRC16 descriptor calculation, sealing and lazy flags | Focused check passed for exact CRC and checksum-field-only mutation | Whole-filesystem legacy admission and group initialization transactions |
| META_BG / resize | Descriptor copies, sparse backups, reserved GDT pointers and grow/publication protocol | Descriptor geometry, complete ordered backups/reserved pointers and exact grow edit/publication protocol passed focused checks | Actual bitmap/table/GDT/superblock after-images, owned allocation and interrupted-grow recovery |
| BIGALLOC | Cluster reserve/map/unmap/init/pin/retire bookkeeping | Uniqueness, initialization, failure/reset and quiescence contracts under construction | Real data I/O authority, partial-cluster reconciliation, extent/quota integration and recovery |
| Extents | Mapping edits, initialized/unwritten conversion and depth 0–5 tree rebuilding | Mapping/nonalias/canonical-layout contracts under construction | Owned allocator, zeroing, bitmap/quota/revoke changes and durable publication |
| DIR_INDEX / LARGEDIR | Linear/HTree rebuild, insert/delete/same-directory rename, six legacy hashes, collision continuation and depth 0–2 | Executable implementation tested; full refinement proof pending | Target inode checks, cross-directory structural transactions, encrypted/casefold directories and allocation |
| Orphans | Legacy chain, orphan-file CRC/slots/global duplicate admission and reclamation lifecycle | Lifecycle focused check passed; chain/file byte and uniqueness proofs under check | Actual orphan allocation/growth/fallback, inode/bitmap/quota/revoke transactions and recovery discovery |
| MMP | Exact 1,024-byte record plus claim/read/write/flush/re-read/heartbeat/clean-stop protocol | Codec and protocol proof work pending | Real freshness/clock/visibility bounds and mount exclusion capability |
| Journal formats | JBD2 v1/v2/v3 checksums, 32/64-bit tags, UUID/escape/revoke formats | Byte and parser contracts under construction | Integrated versioned writer/scanner/recovery, async commits, external journals and all data modes |
| Fast commit | TLV builder, valid-tail prefix scanner, replay intents and inode merge rules | Exact CRC segments, record provenance and committed-prefix preservation under construction | Source-owned replay executor, real area allocator and full/fast-commit scheduling/exclusion |
| Repeated EA recovery | Retained target and fresh bootstrap/scan/admission with exact repaired-byte comparison | Focused check passed for retained target, exact repaired-byte comparison and guarded restart histories | Universal repaired-image acceptance and runtime reset lease |
| Quota / project | vfsv0/vfsv1 radix images, records, U/G/P reservation/transfer/free ledger and project inheritance checks | Atomic ledger, wire, grace and project-field contracts under construction | Source quota ownership, authoritative clock/credentials and atomic quota+inode/allocator transactions |
| Casefold | Pinned Unicode 12.1 NFDICF, Hangul, ignored-character barriers and strict/opaque UTF-8 rules | Full pinned-table shape/order/scalar/max-expansion proof passed; UTF-8/normalization/search pipeline proof pending | Full table-shape proof and casefold/encryption lookup/hash/duplicate/mutation integration |
| Fscrypt | Policy/context/KDF/IV handling, AES, SM4, XTS, CBC-CS3, CBC-ESSIV, Adiantum-XChaCha12-AES and AES-256-HCTR2; unified currently accepted cipher-pair dispatch | Schedule, block, stream, binding and retirement proofs under construction | Primitive proofs, key provisioning, nonce authority, no-key names, encrypted symlinks and VFS transactions |
| Fsverity | SHA-256/512 Merkle construction, descriptors, layout and verified-read algorithm | SHA and salted-path composition proofs under construction | PKCS#7 verification/policy, source-owned tree allocation, enable transaction and immutable runtime binding |
| Framekernel runtime | Safe CortenMM USegment/FrameAllocOptions and VmReader/VmWriter adapter; private BIO bounce buffers and fallible DMA setup | Compiler and kernel runtime tests passed; formal transport refinement pending | no_std proof-core packaging, device-wide alias exclusion, hardware atomicity/drain/reset contracts and mounted VFS |

The DIR_PREALLOC and IMAGIC_INODES compatibility markers still need an explicit pinned-Linux policy review. JOURNAL_DEV requires an external-device ownership and recovery implementation. COMPRESSION and DIRDATA remain intentional Linux-compatible rejections. Existing READONLY and STABLE_INODES restrictions remain applicable.

The first focused bundle checked `group_legacy`, `inode_payload`, `orphan_lifecycle`, `ea_restart` and `ea_repeated_recovery`: 84 obligations, zero errors and compilation, against immutable source. This is a module-filtered diagnostic result, not a strict whole-crate certificate for the expansion. Its source hashes and commands are retained in `/task/ext4-expansion/proof-core-slices-01`. A subsequent focused `meta_bg` check passed 49 obligations with zero errors and compilation; With the inline-data check (22 obligations) and complete pinned Unicode table-shape check (150), Using the latest 27-obligation inline check and 41-obligation resize-plan check, 351 focused obligations across nine new modules are checked. Earlier focused snapshots are retained as historical evidence.

Pinned references for the expansion are listed in [FEATURE_EXPANSION_SOURCES.json](FEATURE_EXPANSION_SOURCES.json). Draft defects and their discovery methods are recorded in [FEATURE_EXPANSION_FINDINGS.md](FEATURE_EXPANSION_FINDINGS.md).

## Validation so far

The implementation diagnostics are independent of formal discharge:

- The first 28 modules compiled together in typecheck-05 before proof annotations. All 32 final annotated modules compile together in typecheck-12. Both are compile-only diagnostics.
- HTree outputs were installed into real ext4 images across several block/checksum/filetype profiles, including an indexed depth-one directory; e2fsck and debugfs accepted the completed fixtures.
- Unicode processing matched the pinned Linux normalization implementation in 1,226,715 comparisons. Quota-file images rebuilt by the new codec passed e2fsck.
- SHA/HMAC/Merkle results passed 78 independent Python-oracle cases; AES/XTS/CTS passed 59 OpenSSL/NIST cases. These tests establish no cryptographic proof or constant-time guarantee.
- Journal/extent diagnostics passed 2,859 assertions; e2fsprogs replayed generated escaped journal payloads in 28 independent recovery cases across checksum/version-width profiles, revokes and corrupted controls.
- Legacy maps, inline data, inode checksums, symlink classification and descriptor CRCs were compared with Linux/libext2fs/debugfs and real images. An inconsistent inline-directory i_size was caught and corrected.
- Sparse backup enumeration matched an independent oracle up to 4,294,967,000 groups in under 4 ms per native test process. The previous draft scanned every group.
- Six plain fast-symlink regressions cover empty/interior-NUL/unterminated targets, incompatible flags and invalid geometry.
- The integrated 32-module artifact passed 474 crypto/context/verity commands with every primitive imported from that artifact; none of the native programs supplied replacement algorithms. These are runtime checks, not proofs.
- Three CortenMM adapter tests ran in the kernel under QEMU. Four host regressions check the test-only x86 QEMU exit classifier. Zero selected guest tests remain allowed by the existing harness and are not counted as execution evidence.

Proof preparation also exposed missing whole-file orphan duplicate rejection, duplicate logical-cluster reservations and acceptance of a late success after failed initialization. The implementations now reject these cases or require explicit reset. Their new invariants still need the final strict proof run.

The scratch evidence ledger is `/task/ext4-expansion/session-status.json`. Source snapshots, commands, output, solver logs and failed attempts are retained beneath that directory. Dense test images were made sparse only after checking identical SHA256 contents. Old completed solver logs were archived with per-file hash verification.

## Completion criteria

Each row needs exact source/format refinement, total public APIs, ownership and concurrency invariants, crash and restart closure where relevant, Linux image interoperability, negative API tests and a strict whole-crate proof against the locked source inventory. Mounted support additionally requires composition across allocator, namespace, quota, orphan, crypto and device layers.

Numeric identifiers and modeled completion events do not confer device, inode, frame, allocation or credential authority. BIO completion and 512-byte sector metadata do not establish 4 KiB failure atomicity or power-loss durability. Those premises must be supplied by the runtime boundary before writable admission.
