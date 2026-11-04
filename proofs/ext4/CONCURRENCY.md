<!-- SPDX-License-Identifier: MPL-2.0 -->

# Concurrent ext4 protocol and block/extent model

This is the expanded implementation target. Existing serialized journal proofs
remain scoped to their stated machine and device contract. They do not prove
concurrent JBD2 operation or any newly listed on-disk feature.

## State and identities

Physical addresses carry a volume/mount identity and a 64-bit block number.
Extents carry a 32-bit logical start, positive Linux-encoded length, 48-bit
physical start and initialized/unwritten state. The terminal logical block is
reserved according to Linux ext4_valid_extent. Block size is part of volume
geometry; a filesystem block is not a Linux page or a CortenMM frame.

The model separates a block's physical address, allocation generation, inode
owner/generation, logical mapping, cache version and journal transaction ID.
Reusing any one identifier must not resurrect another capability. Mount epochs
and bounded counter exhaustion are explicit; no proof assumes machine counters
never wrap. Reserved, journal, extent-tree, bitmap, inode-table, xattr, quota and
file-data ownership are distinct roles. Bigalloc additionally tracks clusters,
per-inode partial-cluster occupancy and the rule for releasing a whole cluster.

An extent map is an ordered, nonoverlapping logical interval relation with a
consistent physical ownership map. Hole, unwritten, private initialized and
published initialized states have different read rules. Splitting/merging must
preserve the mapping pointwise. Insert, punch, truncate, collapse, insert-range
and unwritten conversion must update both interval and physical ownership state.
The tree representation must refine this relation for all admitted depths.

## Threads, transactions and publication

Many threads may hold compatible read leases or private disjoint mutations.
Conflicting inode/extent updates require a proved exclusive lease and a checked
mapping epoch. A read or DMA loan pins the allocation generation until it is
returned; freeing or reassigning that block requires those loans to be drained.
An old read result cannot authorize access to a newer owner after reuse.

The journal model must represent running transactions/handles, one committing
transaction, and a queue of committed checkpoint transactions. Joining a
transaction reserves credits; the final handle closes its running state before
freezing. A later running transaction may modify a block while an older immutable
version is committing/checkpointing. Those versions have distinct owned bytes.
The protocol cannot mutate or recycle an older version with outstanding I/O.

Commit order, checkpoint order, cache publication and acknowledgement order are
separate. Conflicting updates must serialize; disjoint updates must commute at
the specified abstraction boundary. A later home version cannot be overwritten
by an older completion or delayed persistence. Checking a generation only when
issuing a BIO is insufficient: per-block persistence dependencies and quiescence
must exclude that late write. Flush completion is tied to a finite set of issued
writes under an explicit device contract, never inferred from write completion.

Allocation becomes readable only after the required zeroing/data initialization.
Unwritten conversion must preserve zeros outside the written range, including
partial blocks, and the selected data mode must order durable data/metadata
correctly. Truncate/free/reuse adds revoke obligations for older journal versions.
Abort prevents new success/publication but does not cancel outstanding I/O.

Large reads/writes use explicit chunk/prefix semantics; whole-syscall atomicity is
not inferred from transaction atomicity. File, data and directory fsync have
separate dependency closures. Lost replies, deferred errors, unlink with live
handles, orphan recovery and repeated recovery crashes remain in the model.

## Lock and CortenMM boundary

The planned lock ranks are mount lifecycle, ordered namespace/inode identities,
inode extent/range state, allocation-group state, then short journal/cache state
sections. Exact ranks and handle lifetimes require a concrete adapter proof.
Blocking I/O, credit waits and completion waits cannot hold a spinlock or a lock
needed by their callback. Ordered acquisition and a decreasing wait graph must
establish absence of cycles; scheduler fairness is a separate progress premise.

Upper-half implementation stays safe Rust. CortenMM/OSTD frames and
VmReader/VmWriter/BIO DMA loans remain the memory and I/O ownership boundary.
No Linux page/folio/buffer_head ownership is imported. Host immutable slices
and owned vectors are a proof-core representation, not that adapter proof.

## Obligations

| ID | Required result | Current status |
| --- | --- | --- |
| C-BLOCK | Unique allocation ownership; generation-aware pinning; reuse waits for all read/DMA/I/O loans. | Existing ownership model proves abstract zeroing/owner uniqueness; concurrent pins and runtime refinement open. |
| C-EXTENT | Interval/tree equivalence and pointwise mapping preservation under split/merge, insertion, conversion and removal. | Initial inline-leaf parsing/lookup plus 64-bit block intervals, 48-bit extent-start codecs and pointwise split preservation checked. Tree refinement and other transitions open. |
| C-LOCK | Compatible readers, exclusive writers, stale epoch rejection and deadlock-free lock order. | Existing global affine writer gate checked; per-block/inode concurrency open. |
| C-RUN | Concurrent handles reserve credits and close/freeze a transaction exactly once. | Open. |
| C-COMMIT | Running/committing overlap uses distinct immutable versions; durable commits respect transaction dependencies. | Serialized writer checked; concurrent refinement open. |
| C-CHECKPOINT | Multiple checkpoint transactions cannot overwrite newer versions or reuse blocks/log slots with pending effects. | Serialized reuse checked; overlapping checkpoint proof open. |
| C-REVOKE | Free/reuse and unwritten conversion generate correct revokes and preserve initialization under interleavings. | Recovery filtering checked; concurrent production/operation proof open. |
| C-RECOVER | Every concurrent crash cut has a canonical recoverable committed prefix and validates a complete filesystem. | Serialized/repeated recovery and sealed host-image admission checked; concurrent closure open. |
| C-PUBLISH | Readers, handles and fsync observe only their allowed version and durability closure. | Structural reads checked; concurrent VFS/handle publication open. |
| C-RESIZE | Versioned bootstrap admits old/new geometry and journal targets across resize without partition escape. | Fixed-profile identity policy checked; dynamic geometry open. |
| C-FEATURES | All supported feature combinations preserve the block/extent/concurrency invariants. | Initial fixed profile only; full feature matrix open. |

Every new transition needs an enabled condition, executable refinement,
invariant-preservation proof and a nonempty reachable example. Arbitrary finite
interleavings must be covered by induction over the same transition relation.
Tests supplement those proofs; they do not replace a missing transition or
assumption about actual locks, devices or CortenMM ownership.
