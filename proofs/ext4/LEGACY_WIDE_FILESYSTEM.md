<!-- SPDX-License-Identifier: MPL-2.0 -->

# Legacy inode pointers on a wide filesystem

Legacy inode pointers remain 32-bit little-endian values even when the filesystem's block count exceeds 2^32. The structural parser previously rejected the entire geometry above that boundary. It now retains the full nonzero u64 block count and checks each nonzero LE32 pointer against that count.

Only the executable geometry rejection in `legacy_map::parse` changes. Block-size validation, zero-count rejection, inode representation checks, per-pointer range checks, the u32 logical-block domain, traversal budgets, overflow checks, source admission, sparse reads and collection alias rejection retain their behavior. In particular, a low pointer does not permit reading from an incomplete snapshot: lookup and collection still require every declared filesystem block to fit the supplied `Snapshot`.

This is an independent safe Rust structural reader. It neither imports Linux page/folio/buffer_head ownership nor changes the CortenMM/framekernel adapter or grants device-write authority.

## Linux format reference

The references are pinned to Linux commit `028ef9c96e96197026887c0f092424679298aae8`:

- [ext4.h:117–120](https://github.com/torvalds/linux/blob/028ef9c96e96197026887c0f092424679298aae8/fs/ext4/ext4.h#L117): the filesystem block type is 64-bit and the logical block type is u32; lines 786–787 bound nonextent physical pointers to 0xffffffff.
- [ext4.h:3373–3381](https://github.com/torvalds/linux/blob/028ef9c96e96197026887c0f092424679298aae8/fs/ext4/ext4.h#L3373): filesystem count decoding has a separate 64BIT feature rule. Structural parser acceptance here does not replace that superblock admission rule.
- [indirect.c:74–113](https://github.com/torvalds/linux/blob/028ef9c96e96197026887c0f092424679298aae8/fs/ext4/indirect.c#L74): legacy logical path decomposition; lines 148–184 read LE32 pointers.
- [super.c:4871–4872](https://github.com/torvalds/linux/blob/028ef9c96e96197026887c0f092424679298aae8/fs/ext4/super.c#L4871): `s_blockfile_groups` restricts the legacy allocation region independently of the complete filesystem group count.

These are format references, not a Linux-equivalence proof or an established Linux defect.

## Checked contracts

The immutable `proof-legacy-wide-02` snapshot compiled with **48 obligations and zero errors**, filtered to `legacy_map`. The exact 909-line source SHA-256 is:

```text
d5fc15d4af1f9ddb86f09c12664e6b9cc19377e59b03220c3807a14210ae1d80
```

The existing exact path, source-bound lookup, pointwise read-byte, emitted-address range, data/metadata nonalias and claim-membership contracts remain checked. Three additional public lemmas record that widening a filesystem bound preserves a valid legacy root, legacy pointer byte spans are independent of filesystem width, and changing only the count preserves pointer interpretation.

A new source-fit specification and lookup/collection error postconditions make the existing complete-snapshot preflight explicit. Collection preserves Budget precedence for oversized budgets. Zero-length and EOF reads still return empty output without performing lookup.

This replaces the current 44-obligation `proof-legacy-06` record; that record remains in the superseded ledger. It is a focused diagnostic rather than the pending strict unfiltered whole-crate gate.

## Native regressions

`legacy-wide-native-02` links [tests/legacy_wide_fs.rs](tests/legacy_wide_fs.rs) directly against the actual compiled wide02 rlib. All **13 tests passed**, with zero failures, ignored tests or filters. They cover:

| Boundary | Native assertion |
| --- | --- |
| Filesystem count | Seven supported block sizes and counts 2^32−1, 2^32, 2^32+1, 2^48 and u64::MAX are retained by structural parsing |
| Pointer width/range | Adjacent inode words decode as separate LE32 pointers; 0xffffffff is rejected at an equal filesystem end and accepted below a larger end |
| Source admission | Missing huge snapshots and a snapshot one byte short of its declared geometry return Source even when the referenced low block exists |
| Logical addressing | Path requests above u32 and collected triple-indirect entries above u32 are rejected |
| Other boundaries | Budget precedence, malformed geometry, unsupported flags/types, sparse zeros, EOF clipping, beyond-EOF allocations and physical aliases |

The same wide-count test, compiled against the previous actual checked legacy06 rlib, fails at 2^32+1 blocks. This intentional negative control demonstrates that the regression detects the removed rejection.

The small complete images exercise real `Snapshot` lookup/read/collection APIs. No multi-terabyte snapshot was allocated, so successful I/O on a complete wide filesystem is not a native-test claim. In particular, u64::MAX tests establish structural parser behavior, not admissibility of a Linux filesystem with that geometry.

Run the focused tests without replacing the official build or inventing a strict proof report:

```sh
python3 tools/check_legacy_wide_fs.py \
  --proof-attempt /task/ext4-expansion/proof-legacy-wide-02 \
  --baseline-proof-attempt /task/ext4-expansion/proof-legacy-06 \
  --output /task/ext4-expansion/legacy-wide-native-FRESH \
  --rustc /task/verus/rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/bin/rustc \
  --libraries /task/verus/installed
```

The runner validates the pinned compiler, successful focused command, immutable source manifest, source/artifact hashes and exact test inventory. Artifact hashes identify the observed local build and protect its integrity during the native run; the existing proof metadata does not provide an independent proof-completion artifact attestation. It saves commands, logs and a report in a fresh directory. The ordinary compatibility runner also includes the standalone test suite; its full combined run is still pending.

The checked library SHA-256 is `851eeb39c72a6217d43dc1175e4839ad6a8483b75f94b22a1e6f373c76bb7e94`. Exact proof command, native source/runner hashes and report identity are recorded in [FEATURE_EXPANSION_STATUS.json](FEATURE_EXPANSION_STATUS.json).

The full reachable-tree/logical-coverage certificate, whole-source ownership, allocation/truncate/revoke transactions, filesystem integration and strict whole-crate verification remain open. No mount or writable VFS path is enabled.
