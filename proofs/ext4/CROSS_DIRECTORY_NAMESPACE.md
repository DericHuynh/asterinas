<!-- SPDX-License-Identifier: MPL-2.0 -->

# Cross-directory moves, regular hard links and nonlast unlink

The bounded host namespace edit path extends the same-parent
[NOREPLACE rename core](NS_MUTATION.md) with three operations: a move to an
absent full destination key, a hard link to an existing regular inode, and
removal of a regular-file name whose inode remains linked.
It prepares private after-images from one complete admitted EA-enabled source
and publishes one complete result through the existing exact-source/revision
store protocol.

This document describes the component contracts and their boundaries.
[Recorded proof status](proof-status.json) and
[verification evidence](verification-evidence.json) identify the checked source
and native regressions. Native tests supplement the universal transition
contracts; they do not establish formal verification or kernel runtime correctness.

The full EA filesystem, full-feature, writable mount, kernel/CortenMM and
EA-enabled durable namespace-publication gates remain **false**.
The host API does not authenticate credentials, enforce sticky-bit/idmap/LSM
policy, change a mounted filesystem, or acknowledge a durable JBD2 commit.

## Bounded operation relation

An operand is a complete byte name in an admitted directory, resolved to the
source inode number, generation, type and canonical record. Names are not
assumed to be UTF-8. Empty names, slash, NUL, dot and dotdot operands reject.
A saved byte offset or old inode number alone is not an operation identity.

| Operation | Exact name transformation | Inode and topology changes | Bounded rejection cases |
| --- | --- | --- | --- |
| `prepare_move_noreplace` | Remove the exact old full key and add the destination key with the same target number, generation and type; every unrelated name binding remains exact | Touch both changed parents' ctime/mtime and ordinary version and the target's ctime/version. A directory move also replaces its canonical dotdot parent, decrements the old parent's exact link count and increments the new parent's exact count | Existing destination, insufficient supported record capacity, unsupported directory layout or index edit, root/dot operands, invalid resulting topology, and either directory parent carrying the DIR_NLINK marker `1` |
| `prepare_link` | Keep the exact source full key and add one previously absent destination key to the same regular inode; every other binding remains exact | Increment that ordinary regular inode's link count by one; touch its ctime/version and the changed destination parent's ctime/mtime/version | Directory source, existing destination, link ceiling `65000`, insufficient supported capacity, unsupported layout |
| `prepare_unlink` | Remove one exact regular-file full key and keep every other binding exact | Decrement that same inode's count by one, retaining at least one link; touch its ctime/version and the changed parent's ctime/mtime/version | Directory source, dot/root operands, and removal of a last link |

These three APIs retain their original contracts. The move API implements
the absent-destination case; these APIs do not provide replacement, exchange,
whiteout or the successful same-inode replacement no-op of ordinary Linux
`rename`. The existing same-parent API retains its separate contract.
No fresh inode or block is allocated and no inode or block is released.

The separate [regular-file replacement and exchange path](FILE_RENAME.md)
adds `prepare_rename_replace` and `prepare_rename_exchange`, published through
`publish_file_rename`. Both full keys must exist and name regular inodes;
a distinct replacement victim must remain linked. Same-inode operations
preserve every source byte. The component table below continues to describe
the original cross-directory move, link and unlink implementation.

Directory link count `1` is interpreted as an unknown count only by the
source-selected DIR_NLINK admission rule for directories. The bounded directory
move rejects parents with this marker. It performs ordinary exact parent-count
arithmetic and does not promote an exact count to the marker. The regular-file
link ceiling and last-link guard remain exact even when DIR_NLINK is enabled.

The exact requested transformation is checked separately from complete final
namespace validity. A second valid filesystem with unrelated names changed
would not satisfy this operation relation. Physical record indices may change
when a free record is split or a removed record becomes unused; semantic
comparison retains the complete parent/name/target/generation/type bindings.
A directory move explicitly includes the moved directory's dotdot binding.

## Component and proof boundaries

| Component | Checked contract | Remaining boundary |
| --- | --- | --- |
| Existing `ea_namespace`, `ea_directory_index` and allocation/source layers | Bind ordinary inode identities, full source names, canonical records, directory physical blocks, extent storage, EA references and complete rooted topology to the exact retained source | Source origin, authenticated access, mounted cache ownership and writable lifecycle |
| `ns_dir_edit.rs`: `InsertChange`, `RemoveChange` | Reuse an unused span or split aligned slack in one existing 4 KiB piece; removal clears only the selected inode word. Preserve all unrelated live bindings, canonical parsing and exact source checksum domain | Allocation, directory growth, HTree split/rebalance/root promotion and arbitrary compaction |
| `ns_dir_edit.rs`: `DotDotChange` | Replace only canonical record 1 in a linear moved directory's first block and required checksum bytes; preserve all other bytes and bindings | Indexed dotdot encoding and arbitrary parent changes without the complete operation/topology check |
| `ns_inode_links.rs` | Permit only signed `-1`, `0`, `+1`; old/result counts remain in `1..=65000`; write the exact 16-bit link count, exact requested ctime/optional mtime, one nonwrapping ordinary version increment and inode checksum | Last-link/orphan handling, marker promotion, trusted time and other inode formats |
| `ns_namespace_relation.rs`, `ns_namespace_edit.rs` | Resolve complete current source keys, bind edits to actual source inode slots and directory block mappings, coalesce shared physical blocks, check exact complete entry transformation and byte frames, then readmit the complete EA-enabled result | Credentials, replacement/exchange, allocation/reclamation, efficient incremental admission and stale-plan rebasing |
| `ns_edit_prepared.rs`, `ns_checkout.rs` | Retain exact owned source/result images, source revision, admitted result and the private operation witness; preparation remains private until publication | A prepared value is not filesystem authority; host image copies do not refine CortenMM frame ownership |
| `ns_mutation.rs`, `ns_mutation_model.rs` | Consume the prepared value; require exact current revision and entire source bytes; reject exhaustion; replace the complete current image/certificate atomically at the host API boundary; refine the shared finite-history publication transition | Actual OSTD sleeping lock/scheduler refinement, fairness, mount incarnation and device durability |

The concrete prepared type retains the same operation witness that the
candidate constructor checked. The publication theorem relates successful
installation to that result and certificate. The shared history invariant
preserves admission through every finite modeled capture/publication/rejection
schedule; each accepted publication advances the revision once.

## Physical maps, coalescing and frames

Selected directory bytes come from the admitted directory's actual logical to
physical mapping. Selected inode bytes come from the actual source inode
position, number and generation. Full source parsing is repeated during
preparation; stale locations from another image are not accepted as current
canonical records.

Different logical inode numbers can share one physical inode-table block.
Staging must splice each 256-byte inode update into the latest staged copy of
that block. Full-block after-images are keyed by physical block and coalesced;
installing an older copy for the next inode would lose an earlier update.
The final candidate checks the exact edited inode slices and all unrelated
neighboring bytes.

For every changed inode, mode, owner, group, generation, size, extents,
sector accounting, EA pointers, inline xattrs and other unrelated fields remain
exact. The whole-image frame preserves unrelated directory records, all other
inode slots, ordinary data, shared external xattrs, EA value/refword storage,
bitmaps, group/primary counters, inode 8, journal storage and extra partition
bytes. A new hard link adds a namespace reference to an existing ordinary inode;
it does not add an xattr-parent reference or change an EA value inode's refword.

The actual READONLY source feature rejects preparation. Source-selected
checksum seed, HUGE_FILE, DIR_NLINK, EA_INODE and DIR_INDEX interpretation remain
bound to the same source. Feature flags are not cleared to get a different
admission profile.

This candidate path rejects editing any indexed directory: each changed parent
and the moved directory whose dotdot would change must use the linear format.
An indexed source directory used only to resolve an unchanged hardlink source
can remain admitted.
The standalone insertion/removal codecs can check ordinary indexed leaf pieces;
that local capability is not exposed as a writable HTree operation here.
The complete result still retains and validates all unmodified source-selected
HTrees, including source seed/signedness, inherited ranges, collision
continuations and supported depth. Enabling indexed edits later requires an
explicit routing-preserving operation relation or a checked index update.

## Publication, conflicts and lifetime

Workers can capture independent owned checkouts and prepare outside the store's
exclusive publication access. Publication accepts only a candidate whose
revision and complete before-image equal the current store. Failure consumes
the candidate and preserves current bytes, certificate, revision and limit.
There is no stale disjoint merge.

The full revision check closes three dependencies that block disjointness alone
misses: a destination's old absence, canonical source identity after reuse, and
directory ancestry after another move. If two old candidates separately move
siblings underneath one another, the first publication makes the other stale;
the second cannot install its old topology even when its target blocks differ.
If old bytes later reappear, the strictly newer nonwrapping revision still
rejects the old candidate within that store history.

Host `&mut Store` ownership gives one complete publication point through this
safe API. Native tests may provide exclusive access with a host mutex.
Neither fact is a proof of OSTD locks, physical sector atomicity, crash
consistency or globally fresh identity across Store replacement/remount.
The existing host image and resource budgets remain in force; whole-image
copies and comparisons are not a production kernel performance claim.

Last-link unlink, rmdir and sole-linked replacement need orphan/live-handle
lifetime and complete storage/EA reclamation. Create/mkdir and growth need
allocation, initialization, fresh generation, bitmap/group accounting,
ACL/security inheritance and lifecycle closure. A durable namespace operation
must compose its exact patch set with the actual EA-enabled JBD2
bootstrap/admission/recovery path. Ordinary-profile writer/window certificates
do not establish that composition.

## Linux comparison

The reference is Linux v7.0 commit
`028ef9c96e96197026887c0f092424679298aae8`:
[directory-locking.rst](https://github.com/torvalds/linux/blob/028ef9c96e96197026887c0f092424679298aae8/Documentation/filesystems/directory-locking.rst)
and
[fs/ext4/namei.c](https://github.com/torvalds/linux/blob/028ef9c96e96197026887c0f092424679298aae8/fs/ext4/namei.c),
blob `c4b5e252af0efbfcbaf83688a32d445327a74a02`. The reviewed unlink/link
and rename ranges are lines 3060–3360, 3410–3700 and 3700–4080.
Linux rechecks the source dirent inode and re-finds potentially stale records;
a saved pointer can reference unused space after HTree changes. A directory
move changes dotdot and parent counts. Final unlink and overwritten final-link
victims enter orphan/lifetime handling.

Linux's cross-directory locking proof uses the filesystem rename lock,
stable common ancestry and its documented parent/child lock order. The
independent host protocol instead rejects every stale source revision under
one exclusive publication boundary. Its correctness rests on that explicit
protocol and whole result admission, not an inherited inode-number lock-order
argument. No Linux defect is claimed.
