<!-- SPDX-License-Identifier: MPL-2.0 -->

# Concurrent ext4 protocol and block/extent model

This is the expanded implementation target. Existing serialized journal proofs
remain scoped to their stated machine and device contract. They do not prove
concurrent JBD2 operation or any newly listed on-disk feature.

The checked [host namespace mutation core](NS_MUTATION.md) prepares owned
EA-enabled same-parent NOREPLACE renames in parallel and uses exact source and
revision comparison for exclusive publication. Its finite history contracts
preserve complete namespace admission. Runtime locks, broader namespace
operations and actual EA journal durability remain open.

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
The bounded executable journal_queue.rs now reserves shared log space before
lending actual edit parts, compacts unused credits at sealing and preserves
older frozen versions during newer edits. Its exact reservation/edit transitions
preserve invariants over all finite interleavings; see
[JOURNAL_RESERVATIONS.md](JOURNAL_RESERVATIONS.md). Ordered physical
commit/checkpoint and sealed-space reclamation remain open.
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
| C-EXTENT | Interval/tree equivalence and pointwise mapping preservation under split/merge, insertion, conversion and removal. | Initial inline-leaf parsing/lookup, 64-bit block intervals, 48-bit extent-start codecs and pointwise split/merge preservation checked. Local full-depth extent-node parsing, child bounds/order and eh_max checksums are checked. Owned source-block capture and node parsing bind exact source ranges and partition bounds. Source-bound paths, complete structural tree audits and audited lookup equivalence with all covering leaf records are checked; see [EXTENT_TREES.md](EXTENT_TREES.md). Bounded 4 KiB inode/feature/source binding, complete tree metadata/data ownership, exact sector accounting and structural reads now compose through the whole-image certificate. Admitted timed-content writes additionally preserve the complete tree, exact claims and mappings through all final-image overlays (EXTENT_WRITE_FRAMING.md). Result-inode and exact logical read-byte composition through independently validated admitted timed-write results is checked (WRITE_READ_RESULTS.md). General validator completeness, other geometries/features, allocation/conversion and runtime refinement remain open. |
| C-LOCK | Compatible readers, exclusive writers, stale epoch rejection and deadlock-free lock order. | Global affine gate and abstract per-block reader/writer exclusion, stale allocation epoch/lease rejection and disjoint-write commutation checked. Inode mapping epochs, runtime guard refinement and deadlock freedom open. |
| C-RUN | Concurrent handles reserve credits and close/freeze a transaction exactly once. | Bounded candidate batches reserve sorted disjoint targets, lend actual mutable Rust handles and consume freeze only after every slot closes. Exact slot transitions preserve invariants for all finite interleavings; disjoint events commute and retired slots cannot reopen. Sealed frozen snapshots compose with the canonical JBD2 encoder. See [EDIT_HANDLES.md](EDIT_HANDLES.md). Bounded shared append-only window accounting, exact unused-credit compaction and immutable older/newer version overlap now compose in [JOURNAL_RESERVATIONS.md](JOURNAL_RESERVATIONS.md). Running extension/restart, checkpoint reclamation, filesystem operation closure and kernel lock/loan refinement remain open. |
| C-COMMIT | Running/committing overlap uses distinct immutable versions; durable commits respect transaction dependencies. | Serialized admitted writer remains checked. The additional [durable closed-window core](DURABLE_JOURNAL_WINDOWS.md) retains exact sealed encodings, validates contiguous log spans and fresh consecutive sequences, and proves exact durable descriptor/payload/commit bytes for the reported prefix under the explicit device contract. Newer commits may advance while older checkpoints remain incomplete; dispatch owns one pending request. Actual scanner/recovery prefix closure for every bounded window cut and arbitrary finite recovery retries now composes in [CONCURRENT_RECOVERY_CLOSURE.md](CONCURRENT_RECOVERY_CLOSURE.md), including exact primary bytes with persisted recovery marking. Initial/every-prefix full static admission and fresh crash-source discovery now compose in WINDOW_FILESYSTEM_ADMISSION.md. Full validator/recovery acceptance completeness, multiple pending BIOs, runtime locks and CortenMM/driver refinement remain open. |
| C-CHECKPOINT | Checkpoints respect committed versions and conflicting home writes; tail advances only past durable homes. | The [closed-window core](DURABLE_JOURNAL_WINDOWS.md) checks commit-before-home, FIFO home-generation fences, coalesced checkpoint-prefix headers, tail-generation fences, exact latest successful home bytes and a clean final tail. Every finite modeled lane/persistence/error/abort interleaving preserves ordering; success has no late modeled writes. Actual suffix redo now repairs every partial checkpoint at every window cut; repeated recovery preserves the exact complete-prefix target (CONCURRENT_RECOVERY_CLOSURE.md). Initial/every-prefix admission and fresh bootstrap now compose in WINDOW_FILESYSTEM_ADMISSION.md. Circular-log/credit reuse, full admission completeness, physical source/reset quiescence and runtime refinement remain open. |
| C-REVOKE | Free/reuse and unwritten conversion generate correct revokes and preserve initialization under interleavings. | Recovery filtering checked; concurrent production/operation proof open. |
| C-RECOVER | Every concurrent crash cut has a canonical recoverable committed prefix and validates a complete filesystem. | Serialized/repeated recovery and sealed host-image admission checked. Successful admitted writer and recovery durable maps now equal their complete validated filesystem images, with unchanged extra partition bytes and finite failure-free model witnesses; see WRITER_IMAGE.md and RECOVERY_IMAGE.md. Every admitted recovery-model cut is now the complete valid image or repairable to it with the same exact admitted plan, with unchanged-tail canonical journal preservation (RECOVERY_CRASH_IMAGES.md). Fresh bootstrap discovery for all admitted recovery-model cuts and unchanged-tail canonical scan-source equality now compose (RECOVERY_BOOTSTRAP.md). Every bounded concurrent-window cut now admits actual scanning/recovery using the retained mapping; suffix redo yields exact complete-prefix bytes including primary recovery marking, and arbitrary finite recovery attempts preserve admission and the exact target (CONCURRENT_RECOVERY_CLOSURE.md). Fresh bootstrap reconstruction for all window cuts, complete initial/every-prefix validation and guarded full repaired-image admission now compose in WINDOW_FILESYSTEM_ADMISSION.md. Full validator/recovery acceptance completeness, operation crash closure, circular reuse and actual CortenMM/device refinement remain open. |
| C-PUBLISH | Readers, handles and fsync observe only their allowed version and durability closure. | Actual data/zero chunks refine logical bytes; admitted timed writes have exact prefix and unchanged-byte reads through any validated result source and successful modeled durable media (WRITE_READ_RESULTS.md). Concurrent VFS/handle publication, CortenMM source capture and full operation/admission completeness remain open. |
| C-NS-MUTATE | Concurrent preparation and atomic exact namespace mutation publication. | Checked bounded host: actual same-parent NOREPLACE name/metadata changes, whole-result EA admission, immutable owned reads, exact source/revision guards, stale rejection, nonwrapping epochs and finite history contracts (NS_MUTATION.md). All other namespace operations, dependency-aware rebasing, VFS authorization, actual OSTD locks/CortenMM and EA journal crash closure remain open. |
| C-RESIZE | Versioned bootstrap admits old/new geometry and journal targets across resize without partition escape. | Fixed-profile identity policy checked; dynamic geometry open. |
| C-FEATURES | All supported feature combinations preserve the block/extent/concurrency invariants. | Bounded static profile includes optional HUGE_FILE, CSUM_SEED bounded 64BIT descriptors and FLEX_BG placement, source-derived accounting/checksum domains and independent journal identity; full feature and concurrent mutation composition remain open. |

Every new transition needs an enabled condition, executable refinement,
invariant-preservation proof and a nonempty reachable example. Arbitrary finite
interleavings must be covered by induction over the same transition relation.
Tests supplement those proofs; they do not replace a missing transition or
assumption about actual locks, devices or CortenMM ownership.
