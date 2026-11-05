<!-- SPDX-License-Identifier: MPL-2.0 -->

# Concurrent namespace preparation and publication

The host namespace mutation core prepares owned updates in parallel and publishes
one complete, checked image under exclusive access to the store.
Its first concrete operation is `prepare_rename_noreplace`: rename one regular
file or directory within the same parent, using the existing canonical record's
space without allocation.
The operation retains the actual EA-enabled source and completely validates the
result through [EA namespace admission](EA_NAMESPACE.md).

The implementation and proof contracts are included in the pinned entire-crate
verification and compilation run. Native evidence adds 23 mutation regressions
and 16 ownership/privacy misuse rejections. Tests supplement the proofs; they
do not discharge formal obligations. Recorded evidence identifies the exact
checked source, artifacts and scope.

This is host-image mutation with a checked publication protocol. It does not
authorize a VFS operation, mutate a mounted filesystem or acknowledge durable
JBD2 commit. Runtime credentials, OSTD locks, CortenMM frame access and actual
EA-enabled journal/bootstrap/recovery composition remain separate boundaries.

| Design component | Implementation and contract | Remaining boundary |
| --- | --- | --- |
| `ns_rename_block.rs` | Replaces exactly one live canonical record's full name within its existing span; preserves record locations, targets, types, record lengths and every other name; checks the exact leaf checksum and byte frame | Record insertion/deletion, capacity growth, HTree splitting and moving names between leaves |
| `ns_inode_touch.rs` | Updates parent ctime/mtime and target ctime with exact requested representable values, increments each ordinary version without wrap, reseals inode CRCs and preserves identity, links, extents, sector and xattr bytes | Trusted runtime clock, inode lifecycle and broader inode formats |
| `ns_rename.rs` | Resolves exact source full key and generation, requires destination absence, coalesces actual directory/inode-table after-images, checks exact complete before/after name transformation and byte framing, then validates the entire EA-enabled result | Cross-parent moves, replacement, link/unlink/create/rmdir, allocation/orphan machinery and credential mediation |
| `ns_mutation_model.rs` | Defines current and prepared image certificates, total capture/publication transitions, exact-source and revision matching, counter exhaustion and arbitrary finite history preservation | Actual scheduler fairness, physical locks, I/O and operation families outside this subset |
| `ns_checkout.rs`, `ns_prepared.rs`, `ns_mutation.rs` | Owns a certified image, clones immutable checkouts, prepares outside store publication and installs the consumed prepared result only after exact revision/source comparisons; success replaces the complete image/certificate and advances one epoch, while rejection preserves current state | Efficient shared frame-backed snapshots, OSTD guard refinement, mounted caches and durable publication |

## Concrete rename semantics

The source key is the full `(parent inode, old name bytes)` pair, resolved from a
complete admitted namespace. The target number, generation, type and canonical
record location come from that exact source.
Dot and dotdot are not mutable operands. Names obey the parser's length, NUL and
slash restrictions and need not be UTF-8.

The destination must be absent. This API implements the `NOREPLACE` case:
an existing destination rejects even when it is the same key or another hard
link to the same inode. Ordinary replacing `rename` has different no-op and
victim semantics and is outside this API.
The new name must fit the selected record's existing payload capacity.
Capacity or unsupported-layout failure yields no prepared mutation and changes
no store state.

The record retains its inode, type, start, record length and canonical position.
Only its name length and payload, and the containing leaf checksum word, may
change. Spare payload is cleared. All other canonical records and names remain
exact. The complete before/after namespace sequences have the same length and
order: exactly the selected entry has the requested new full name, while every
entry retains its target, generation, type and location.
Final namespace validity alone would not establish this requested transformation;
the candidate checks the separate exact operation relation.

Same-parent directory rename leaves dotdot, parent graph and all link counts
unchanged. Regular-file hard links retain their exact reference counts as well.
Parent inode ctime/mtime and version are updated, and the target inode ctime and
version are updated. The target's own mtime remains exact.
The inode codec rejects ordinary version exhaustion and unrepresentable times.
It does not authenticate the supplied clock value or prove clock monotonicity.

The directory record and inode data come from actual source physical mappings.
When parent and target share a 4 KiB inode-table block, their 256-byte changes
are coalesced into one staged block using the latest staged bytes.
Mode, owners, links, generations, sizes, extents, i_blocks, EA pointers, inline
xattrs and unrelated neighboring inode slots remain exact.
The whole-image frame also preserves EA values/refwords, shared external xattrs,
bitmaps, counters, journal storage, fixed metadata and extra partition bytes.
Directory names do not create additional EA xattr-parent references.

The actual READONLY feature rejects mutation preparation. Source feature flags
are retained; the constructor does not clear EA_INODE or DIR_INDEX to obtain a
different-profile certificate.

## Indexed directories

The leaf codec retains the source-selected linear/indexed interpretation and
inode-derived checksum seed. HTree root dots and routing blocks are not normal
writable name records.
For an indexed leaf, a new name is accepted only if the complete final HTree
still validates with the actual source hash seed, signedness, inherited ranges,
collision continuation and LARGEDIR depth.
A name requiring routing changes or another leaf rejects in this bounded path.
No HTree split, rebalance, root promotion or directory growth is claimed.

## Concurrent protocol and histories

`Store` owns the current image, its EA namespace certificate, a `u64` revision
and a caller-selected publication limit. `open` validates and copies its source.
`checkout` returns an independent owned image and the captured revision.
Workers can keep these immutable reads and prepare private after-images while
other workers publish.
Dropping or failing a checkout/preparation writes no current store state and
holds no mutable store reservation.

`publish` consumes its prepared object under one exclusive `&mut Store` borrow.
It checks, in order:

1. The prepared revision equals the current revision.
2. The complete prepared before-image equals the complete current image.
3. The configured limit and `u64` exhaustion permit one more publication.

Success moves the exact prepared result and checked namespace certificate into
the store and increments the revision once. There is no fallible encoding,
validation or allocation after these checks in the publication path.
Failure consumes the candidate and leaves current bytes, certificate, revision
and limit unchanged. Clients retry by obtaining a fresh checkout and preparing
the operation again.

The model's generic prepared view carries admitted before/after image
certificates. The concrete private `Prepared` type additionally retains the
exact checked rename relation. Executable success refines the same enabled
publication transition; the history proof covers every finite sequence of
captures, accepted publications and rejected publication attempts.
Every state remains certified, source length and limit remain fixed, and the
revision equals its initial value plus the accepted publication count.
Accepted publications have distinct ordered revisions and define the modeled
linearization order. Old owned checkout reads remain certified and unchanged.

After one candidate publishes, another prepared at that revision is stale even
if its full name or logical inode appears disjoint. Distinct inodes can share a
physical inode-table block; installing an old whole-block image could otherwise
erase newer metadata while leaving a structurally valid filesystem.
Global revision rejection also closes stale negative-lookup and ancestry
dependencies without inventing a minimal read set.
There is no stale disjoint merge or automatic rebase.
If old bytes reappear within one store history, a strictly newer revision still
rejects the old preparation. Counters reject before wrap.

The revision is scoped to one host store history, not a globally unique mount
incarnation or credential. A checked candidate from an equivalent image and
revision is semantically interchangeable with a local candidate.
The API deliberately grants no cross-store identity, remount isolation or
authenticated filesystem authority from a number or ghost-only token.
Opening a new Store, replacing a Store value or swapping Store values selects
another host history; the previous history's epoch guarantee does not carry over.
Such resets are not modeled or authorized kernel lifecycle transitions, and this
core supplies no persistent or globally fresh mount epoch.

## Representation and runtime limits

The owned host representation admits at most 256 MiB per complete image, within
the inherited EA allocation/namespace limits. Each checkout and prepared result
may own another image-sized vector. This bounds logical image lengths, not exact
aggregate heap use or allocation success.
Copying a checkout and comparing a successful publication can scan the whole
image. This is a proof-core representation, not a production kernel hot-path
performance claim.

Native tests may coordinate the verified store through `std::sync::Mutex` and
prepare in actual threads. The mutex supplies host scheduling/exclusive access;
those tests do not prove an OSTD lock implementation or scheduler progress.
The core's `&mut` boundary and owned copies prevent callers from observing a
partially replaced store through its safe API. This is not physical sector
atomicity or crash durability.

An eventual kernel adapter must refine sleeping guard ownership, source
capture/freshness, dentry/inode cache coherence, cancellation and CortenMM frame
alias/loan rules. A cloned OSTD frame does not itself establish immutable bytes.
No Linux page, folio or buffer-head ownership is imported.

## Open operation and durability boundaries

Hard link and nonlast unlink need new exact insertion/removal codecs and link
counter transitions. Last-link unlink, rmdir and replacing a sole-linked victim
also need orphan/live-handle lifetime and reclamation/accounting closure.
Create/mkdir require allocation, initialization, generation freshness, bitmap
and group counters, security/ACL inheritance and lifecycle proofs.
Cross-parent directory moves require dotdot and parent-count updates and stable
ancestry; exchange/whiteout and replacing rename add distinct transformations.
Those are not implemented by this same-parent NOREPLACE path.

Publication means an admitted new host namespace version is visible.
It does not mean the directory or file has been fsynced, that the exact patches
are committed/checkpointed, or that a crash can recover that namespace.
Existing ordinary-profile writer/window admission must not be substituted for
the actual EA-enabled JBD2 state/bootstrap/recovery composition.
The full EA filesystem, full feature, writable mount and kernel/CortenMM gates
remain false. Permission, sticky-bit, idmap and LSM mediation remain outside this
non-authority host operation.

## Linux reference

The reference remains Linux v7.0 commit
`028ef9c96e96197026887c0f092424679298aae8`.
`Documentation/filesystems/directory-locking.rst` describes per-directory and
cross-directory rename locking and its ancestry/deadlock argument.
`fs/ext4/namei.c` rechecks source dirent identity, re-finds potentially stale
records after HTree changes, and separates overwritten/last-link orphan handling.
Those checks motivate exact current-source binding and the explicit operation
limits above. Their lock proof is not inherited by a different host protocol.
No Linux defect is claimed.
