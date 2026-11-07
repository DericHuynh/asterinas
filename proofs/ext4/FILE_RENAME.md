<!-- SPDX-License-Identifier: MPL-2.0 -->

# Regular-file replacement and exchange

This component extends the bounded host namespace core with replacement of an
existing regular-file destination and exchange of two existing regular-file
bindings. It uses a complete admitted source image and the same exact-source,
nonwrapping revision publication protocol as the
[cross-directory operations](CROSS_DIRECTORY_NAMESPACE.md).

The public APIs are `Checkout::prepare_rename_replace`,
`Checkout::prepare_rename_exchange` and `Store::publish_file_rename`.
Both full keys must already exist and name regular inodes.
Absent destinations use `prepare_rename_noreplace` within one parent and
`prepare_move_noreplace` across parents.

## Checked results

| Check | Current result |
| --- | --- |
| Pinned whole-crate Verus checking and compilation | 2797 obligations, zero errors; 810 named proofs and 703 named executable functions |
| Native interoperability/regressions | 343 passed (281 metadata, 62 journal), including 15 regular-file rename tests |
| Ownership/privacy rejection checks | All 247 current cases rejected |
| Negative verifier gates | All 6 cases rejected |
| Runner timeout regression | Passed; diagnostic cleanup only, no verifier proof evidence |

[Proof status](proof-status.json) and [recorded evidence](verification-evidence.json)
identify the exact checked source and artifacts. Native/API checks supplement
the proofs; they do not establish kernel or physical durability refinement.

## Operation contracts

| Operation | Required source | Exact namespace result | Metadata changes |
| --- | --- | --- | --- |
| Distinct-inode regular-file replacement | Both full keys resolve to regular inodes; distinct destination inode retains another link | Old key disappears; destination key names the original source inode with its exact generation/type; every unrelated binding remains exact | Victim links decrement once and remain positive; source links stay exact; both inodes receive requested ctime; changed parents receive ctime/mtime |
| Distinct-inode regular-file exchange | Both full keys resolve to regular inodes | The two complete target/generation/type bindings swap; names and all other bindings remain exact | Both inode link counts stay exact; both receive requested ctime; changed parents receive ctime/mtime |
| Same-inode replacement or exchange | The two resolved keys name the same regular inode, including the same full key | Every source binding remains exact | Entire result equals source, empty patch set, no inode timestamp/version change |

Changed parent versions advance once for each edited directory entry: twice for
a shared parent and once each for distinct parents. Ordinary target inode
versions advance once under the host codec's conservative policy. This is an
explicit host version policy; Linux's exact internal inode-version scheduling is
not inferred from namespace equivalence.

## Component boundaries

| Component | Required checked property | Boundary |
| --- | --- | --- |
| Directory target codec | Canonical selected record; exact new inode/type; names, lengths, offsets, all unrelated bytes and checksum domain preserved | Existing supported directory pieces; no growth, allocation or index restructuring |
| Namespace relation | Both source identities, exact full-key transformation and bidirectional preservation of every unrelated binding | No credentials or VFS policy |
| Source-bound constructor | Actual inode positions, generations, directory block maps, staged same-block edits, full byte frame and complete result readmission | Bounded owned host images |
| Prepared value | Private, consuming ownership of exact source/result, revision, certificate and checked operation | No independent filesystem authority |
| Publication | Current full bytes and revision must match; rejection preserves store; accepted installation advances revision exactly once | Host exclusive access, without OSTD lock or device refinement |

Same-block changes must use the latest staged block. This applies both to two
dirents in one directory piece and to different inode slots sharing an
inode-table block. No saved physical offset alone authorizes an operation.

After complete source admission, READONLY exclusion and checks of names and regular-file keys,
the same-inode no-op skips mutation-only directory-layout, timestamp
representability and inode-version checks. The supplied time remains request
metadata; no on-disk timestamp or version changes.

A successful same-inode no-op still consumes its prepared value. If accepted by
the host store it advances the scheduling revision once, while every on-disk
byte remains unchanged. Stale, full-source-mismatched or exhausted no-op
candidates reject under the same publication guards. The revision is local to one retained Store history.

## Remaining boundaries

The actual READONLY feature remains a rejection condition. Changed directories
use the supported linear layout. Last-link replacement, directories and mixed
exchanges, whiteout, allocation, orphan/live-handle lifetime, reclamation and
directory growth need separate implementations and proofs. Kernel VFS
permissions, sticky-bit/idmap/LSM rules, quota and project-inheritance policy are
not supplied by this host operation.

All full-feature, full EA filesystem, writable-mount, kernel/CortenMM and
EA-enabled durable-publication gates remain false. Whole-image host ownership
does not establish CortenMM frame loans, cache coherence, OSTD lock refinement,
JBD2 acknowledgement or physical crash durability. Linux page, folio and
buffer-head ownership is not introduced into the framekernel.

## Linux reference

The reference remains Linux v7.0 commit
`028ef9c96e96197026887c0f092424679298aae8`.
[fs/namei.c](https://github.com/torvalds/linux/blob/028ef9c96e96197026887c0f092424679298aae8/fs/namei.c)
returns success when source and destination resolve to the same inode.
[fs/ext4/namei.c](https://github.com/torvalds/linux/blob/028ef9c96e96197026887c0f092424679298aae8/fs/ext4/namei.c)
binds current source/destination dirents, replaces their target words, updates
ctime and parent metadata, and adds a displaced victim to orphan handling only
when its last link disappears. Exchange checks both identities and updates both
entries. The bounded replacement path requires the victim to remain linked.
These comparisons identify behavior to model; they establish no Linux defect.
