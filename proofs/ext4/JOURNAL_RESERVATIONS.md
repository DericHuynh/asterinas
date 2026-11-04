<!-- SPDX-License-Identifier: MPL-2.0 -->

# Concurrent journal reservations and frozen versions

`journal_queue.rs` implements shared log-space accounting around the existing
borrowed edit handles. One queue has a running candidate and an ordered prefix
of sealed immutable versions. A newer candidate may edit the same home targets
while workers read older sealed bytes. The queue reserves log slots before
lending edit handles, and older sealed bytes and reservations remain unchanged.

This is an append-only candidate window for one queue instance. It does not
establish that the corresponding region of an actual device is free, activate
the journal, publish filesystem state or report durable commitment.

## Reservation and ownership contract

| Operation | Checked behavior |
| --- | --- |
| Reserve | Validate sorted allowed targets, one through 250 payload credits, shared capacity, the 64-version bound and counter availability before constructing the running batch. Rejection preserves the queue view. |
| Borrow work | Lend two disjoint actual mutable Parts for the running batch and an immutable slice of older versions. Their final values compose into the same parent batch; frozen bytes, accounting and mapping remain fixed. |
| Seal a nonempty batch | Require every slot closed and valid. Move its exact owned selection into a sealed version and charge selected payloads plus one descriptor and one commit block. |
| Seal an empty batch | Release the entire running reservation and append no transaction. Its reservation serial remains consumed. |
| Unused credits | Compact only the youngest unsealed reservation. The next version begins immediately after the actual preceding records, so unused credits do not create a gap that would stop JBD2 scanning. |
| Cancel | Release only the running reservation after all Rust loans have ended. Sealed credits and bytes remain pinned, and the serial counter never decreases. |
| Read a sealed version | Expose immutable snapshots, targets and checked physical log-slot coordinates. No writable aliases or numeric completion/redirection API are provided. |

Capacity is `journal blocks - 2`: logical block zero is the journal header and
one final slot remains unused. Spans begin at logical block one and do not wrap
within this window. Each nonempty sealed span contains exactly its payload
count plus two records. Every pair of sealed spans is proved disjoint, including
its mapping through the retained internal-journal extent.

The 64-bit reservation serial is distinct from a Linux JBD2 transaction ID.
Cancellation and empty batches may consume serials; they must not introduce
gaps in JBD2 transaction sequencing. At terminal serial exhaustion, new
reservations fail instead of wrapping. Future append/commit code must assign
the canonical JBD2 sequence under its validated journal epoch.

## Proofs and executable boundary

`journal_queue_trace.rs` proves invariant preservation for every enabled
reserve/edit/seal/cancel transition and every cut of arbitrary finite traces.
The same transitions appear in the executable queue's normal-return contracts
and in the existing edit-handle contracts. The proofs establish shared-capacity
bounds, contiguous spans, serial freshness, non-overlap and exact preservation
of every older sealed record and byte. A nonempty witness contains older frozen
and newer private versions of the same target with different bytes.

The mutable Queue follows Running's explicit `wf` and normal-return
preservation pattern. Its constructor establishes `wf`; public methods have
checked entry arithmetic and no public preconditions. Sealed versions retain
type invariants. The pinned vector/borrow models do not establish the required
no-unwind contracts for a global invariant over mutable queue storage, so no
such contract or local library specification is introduced. Kernel unwind,
allocation-failure and scheduler refinement remain separate work.

The host tests run two newer edit workers alongside a reader of older frozen
bytes, including identical home targets. Other cases cover unchanged rejection,
cancelled serials, dropped/aborted handles, exact shared-capacity and version
limits, physical slot uniqueness, unused-credit compaction and empty batches.
Two compacted versions encode into consecutive canonical JBD2 records; the
checked scanner and independent e2fsprogs recovery select the newer version.
Negative Rust compilation checks reject credit forgery, forged/replaced frozen
records, cancellation through a live work borrow and mutation of frozen bytes.
These native checks supplement the formal theorems.

## Linux reference and remaining integration

The pinned Linux v7.0 `fs/jbd2/transaction.c` accounts outstanding credits before
dirtying buffers, and `commit.c` waits for live updates before switching the
running transaction. Its frozen-buffer handling preserves older versions.
`checkpoint.c` waits for conflicting work and drops checkpoint locks around
commit waits. These rules guide the separation of accounting, private mutable
bytes and frozen versions; exact blobs and reviewed definitions are recorded
in sources.json.

| Concurrency obligation | Accomplished | Remaining |
| --- | --- | --- |
| C-RUN | Bounded shared window accounting, actual disjoint borrowed handles, exact close/seal, unused-credit release and arbitrary finite reservation/edit interleavings | Running transaction extension/restart, wait queues, mount ownership and full operation closure |
| C-COMMIT | Older/newer candidate versions remain isolated; the separate [closed-window core](DURABLE_JOURNAL_WINDOWS.md) now owns encodings, sequences and durable commit requests with byte-level persistence proofs | Actual concurrent crash-scan/recovery composition, full filesystem admission and runtime refinement |
| C-CHECKPOINT | Sealed reservations remain pinned; the separate closed-window core now checks FIFO home checkpoints, conflicting-version fences and fenced tail-prefix retirement | Circular log/credit reclamation, fresh-source restart and hardware quiescence |
| C-LOCK | Rust loans prevent cancellation or sealing while work parts remain live | Actual OSTD guard ranks, waits, callbacks, reset/unmount and deadlock/progress refinement |

There is no sealed-credit reclamation API. This conservatively prevents reuse
before physical quiescence and reusable-log admission are established. Closed-window checkpoint/tail proofs are now separate in DURABLE_JOURNAL_WINDOWS.md. Native tests of
completed records do not establish concurrent crash recovery or filesystem
durability. The actual adapter must retain CortenMM/OSTD frame, mapping and DMA
loans; owned host snapshots do not prove that boundary. No Linux page, folio or
buffer_head ownership is introduced. Kernel mount/write gates remain closed.
