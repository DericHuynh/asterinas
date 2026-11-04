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

The checked block_lifetime.rs specification now models per-block shared readers
and exclusive writers, explicit volume/allocation epochs, fresh writer serials,
private/unwritten/published states and zeroing before initialized publication.
All enabled finite interleavings preserve its invariant. Returned read-pin IDs
stay retired; stale allocation epochs, wrong volumes and stale writer leases
are rejected. Disjoint writes commute, with nonempty concurrent reader/writer
examples for every modeled power-of-two 1 through 64 KiB block size.

Those are file-block/cache-state transitions, not physical write atomicity.
This model does not prove scheduler progress, counter lowering/exhaustion,
mapping-epoch capture, DMA or outstanding physical-I/O quiescence. Scalar model
keys do not establish unforgeable runtime guards; tracked-token and actual
OSTD-lock refinement remain required. Extent lookup must also capture/check an
inode mapping epoch: an allocation epoch alone is not a complete lookup proof.

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

The reviewed concrete boundaries are:

| Asterinas/OSTD API | Required refinement |
| --- | --- |
| [Frame and Segment](../../ostd/src/mm/frame/mod.rs) | Reference counts preserve physical-memory lifetime. Untyped-frame readers/writers do not enforce Rust's alias/mutability rule, so a cloned frame is not an immutable snapshot. Track byte access, cache version and outstanding aliases separately. |
| [UniqueFrame](../../ostd/src/mm/frame/unique.rs) | Unique metadata access must remain consistent with frame ownership and any later sharing; it does not turn a disk block number into a memory capability. |
| [DmaStream](../../ostd/src/mm/dma/dma_stream.rs) | Preserve direction, initialization, mapping lifetime, cache coherence and sync_to_device/sync_from_device obligations. Keep frozen bytes unavailable to CPU mutation while the device owns a loan. |
| [Bio](../../kernel/core/comps/block/src/bio.rs) | Submission consumes segments and the FnOnce callback. Bind request identity and buffers to the modeled generation; completion still does not prove durable persistence or cancellation of pending device effects. |
| [RwMutex](../../ostd/src/sync/rwmutex.rs) | Refine shared/exclusive model leases to sleeping guards and wait queues; prove callback dependencies and lock ranks separately from memory safety. |

## Obligations

| ID | Required result | Current status |
| --- | --- | --- |
| C-BLOCK | Unique allocation ownership; generation-aware pinning; reuse waits for all read/DMA/I/O loans. | Abstract per-block shared read pins, exclusive writer leases, volume/allocation epochs, retired pin IDs and zeroing/publication preserve all finite interleavings in block_lifetime.rs. DMA, physical-I/O quiescence, extent binding and runtime refinement remain open. |
| C-EXTENT | Interval/tree equivalence and pointwise mapping preservation under split/merge, insertion, conversion and removal. | Initial inline-leaf parsing/lookup, 64-bit block intervals, 48-bit extent-start codecs and pointwise split/merge preservation checked. Local full-depth extent-node parsing, child bounds/order and eh_max checksums are checked. Owned source-block capture and node parsing bind exact source ranges and partition bounds. Source-bound paths, complete structural tree audits and audited lookup equivalence with all covering leaf records are checked; see [EXTENT_TREES.md](EXTENT_TREES.md). Bounded 4 KiB inode/feature/source binding, complete tree metadata/data ownership, exact sector accounting and structural reads now compose through the whole-image certificate. Other geometries/features, mutations and runtime refinement remain open. |
| C-LOCK | Compatible readers, exclusive writers, stale epoch rejection and deadlock-free lock order. | Global affine gate and abstract per-block reader/writer exclusion, stale allocation epoch/lease rejection and disjoint-write commutation checked. Inode mapping epochs, runtime guard refinement and deadlock freedom open. |
| C-RUN | Concurrent handles reserve credits and close/freeze a transaction exactly once. | Bounded candidate batches reserve sorted disjoint targets, lend actual mutable Rust handles and consume freeze only after every slot closes. Exact slot transitions preserve invariants for all finite interleavings; disjoint events commute and retired slots cannot reopen. Sealed frozen snapshots compose with the canonical JBD2 encoder. See [EDIT_HANDLES.md](EDIT_HANDLES.md). Shared journal-space accounting, filesystem operation closure and kernel lock/loan refinement remain open. |
| C-COMMIT | Running/committing overlap uses distinct immutable versions; durable commits respect transaction dependencies. | Serialized writer checked. Sealed [candidate writer admission](WRITER_ADMISSION.md) validates the complete starting filesystem and actual dirty/log/home/retirement result, binding one source, frozen layout, bootstrap identity and certificate through owned requests. Operation authority, complete physical-ledger/filesystem refinement and concurrent overlap remain open. |
| C-CHECKPOINT | Multiple checkpoint transactions cannot overwrite newer versions or reuse blocks/log slots with pending effects. | Serialized reuse checked; overlapping checkpoint proof open. |
| C-REVOKE | Free/reuse and unwritten conversion generate correct revokes and preserve initialization under interleavings. | Recovery filtering checked; concurrent production/operation proof open. |
| C-RECOVER | Every concurrent crash cut has a canonical recoverable committed prefix and validates a complete filesystem. | Serialized/repeated recovery and sealed host-image admission checked; concurrent closure open. |
| C-PUBLISH | Readers, handles and fsync observe only their allowed version and durability closure. | Structural reads checked; concurrent VFS/handle publication open. |
| C-RESIZE | Versioned bootstrap admits old/new geometry and journal targets across resize without partition escape. | Fixed-profile identity policy checked; dynamic geometry open. |
| C-FEATURES | All supported feature combinations preserve the block/extent/concurrency invariants. | Bounded static profile includes optional HUGE_FILE, CSUM_SEED bounded 64BIT descriptors and FLEX_BG placement, source-derived accounting/checksum domains and independent journal identity; full feature and concurrent mutation composition remain open. |

Every new transition needs an enabled condition, executable refinement,
invariant-preservation proof and a nonempty reachable example. Arbitrary finite
interleavings must be covered by induction over the same transition relation.
Tests supplement those proofs; they do not replace a missing transition or
assumption about actual locks, devices or CortenMM ownership.
