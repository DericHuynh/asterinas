<!-- SPDX-License-Identifier: MPL-2.0 -->

# Durable commit and checkpoint for a reserved journal window

`journal_window.rs` consumes the contents of an immutable prefix of sealed
journal reservations into owned canonical encodings. The caller may then
schedule commit, checkpoint and tail requests independently. Newer log commits
may advance while an older checkpoint remains incomplete. Home generations
remain FIFO and every generation ends with a home flush. This prevents delayed
older home writes from overwriting a newer committed version of the same block.

This is a bounded host core for the existing format profile. A single pending
request owns the engine and its immutable borrowed command. It is suitable for
an eventual driver dispatcher, but does not implement simultaneous pending BIOs,
kernel worker scheduling, or filesystem operations. The frozen queue may
continue preparing newer candidates independently; this engine owns a copied,
closed window and does not append to it or reclaim its reservations.

## Executable ordering

| Lane | Requests | Checked dependency and result |
| --- | --- | --- |
| Bootstrap | Dirty primary, flush, activate journal, flush | No log/home/tail lane is enabled until durable recovery marking and activation are reported. |
| Commit | Descriptor, payload images, log flush, commit record, commit flush | Contiguous reserved spans and fresh consecutive JBD2 sequences; the reported committed prefix advances only after the commit flush. |
| Checkpoint | Original after-images, home flush | Only committed versions are eligible; the next home generation starts after the previous home flush. |
| Tail | Prefix header, tail flush | Snapshot an already checkpointed prefix, preserve that goal while other lanes advance, and retire only after the exact header's flush. Multiple checkpointed versions may be retired together. |
| Error/abort | Preserve issued effects, stop new dispatch | Failure never advances commit/checkpoint/retirement frontiers. Abort retains a pending request, and cannot cancel device effects. |

The initial journal must be clean and match the supplied UUID and internal
single-extent geometry. Encodings retain exact frozen after-images and validated
primary/journal sources. Preparation rejects gaps or reordered reservation
serials, wrong geometry, unsupported codecs, the cumulative 4,096-payload recovery budget, other resource limits and insufficient
nonwrapping JBD2 sequence space. Reservation serials remain separate from disk
sequence numbers. All public executable APIs validate inputs without public
preconditions. Private state and consuming Pending objects prevent request
forgery, stale completion reuse and completion redirection; borrowed bytes
prevent finishing a request while its command loan is live.

## Proof boundary

`journal_program.rs` specifies the exact transitions used by the executable
engine. `journal_window_device.rs` adds issued and stable write sets. Write
completion does not imply persistence. Flush success drains earlier issued
writes; independent persistence may occur before completion or after failure
and abort. `journal_window_media.rs` interprets these operations as exact
partition-confined 4096-byte block writes. Repeated-address writes are separated
by a completed fence, and stable bytes follow actual issue order.

| Design obligation | Accomplished in this component | Remaining |
| --- | --- | --- |
| C-COMMIT / J-ACK | Ordered multi-version commit requests, exact durable descriptor/payload/commit bytes for the reported prefix under the device contract, immutable owned request buffers | Bounded actual-scanner/recovery prefix closure now composes in [concurrent recovery closure](CONCURRENT_RECOVERY_CLOSURE.md); operation/mount admission and driver reports remain open |
| C-CHECKPOINT | FIFO home generations, commit-before-home, full home-prefix persistence before tail issue, coalesced prefix headers, fenced tail generations, exact latest final home bytes and final clean tail | Circular log reuse, sealed-credit reclamation, restart/append admission and hardware quiescence |
| J-BOOT | Recovery marking and activation fences, retained geometry/UUID, fresh contiguous IDs and exact active/retired header images | Actual-device source provenance, clean unmount, external journals and other unsupported format features |
| S-RACE | Every finite modeled lane/persistence/completion/abort interleaving preserves the ledger and repeated-address ordering; abort retains effects | Kernel locks, worker fairness, overlapping pending BIOs, DMA loans, reset and unmount integration |
| D-ORDER / D-ATOMIC | Exact atomic-block persistence refinement and finite flush refinement under an explicit device contract; final success has no late modeled persistence | Proving the actual OSTD/device implementation satisfies that contract |
| Progress | A finite failure-free scheduler witness and bounded work for a new window | Device responsiveness, memory allocation and runtime scheduling fairness |

The model controls one protected window and excludes competing protocol instances or external writes. The device contract requires a quiescent initial device matching the retained
snapshot, atomic 4 KiB writes, and a flush that persists every previously issued
write before reporting success. This contract does not follow merely from a
Linux-compatible disk format. A driver, cache or medium with weaker guarantees
must supply a different protocol and proof. There is no local trusted proof
escape, checksum-injectivity premise or external-body wrapper.

The native cache harness deliberately completes writes before persisting them,
drains independent pending writes in reverse order, overlaps a newer commit
with an older checkpoint, delays tail fences while checkpoint work advances,
and permits late persistence after abort at every command cut. The checked
scanner and independent Linux/e2fsprogs recovery are compared on those cuts.
These examples supplement the formal results. Formal actual-scanner and repeated-recovery closure now composes for every bounded window crash snapshot in [concurrent recovery closure](CONCURRENT_RECOVERY_CLOSURE.md).

## Linux reference and framekernel integration

The ordering follows the pinned Linux v7.0 JBD2 durability rules:
`fs/jbd2/commit.c` waits for log I/O before issuing a non-async commit record and
establishes cache ordering before tail updates; `fs/jbd2/checkpoint.c` explicitly
flushes recently checkpointed home blocks before dropping their transactions
from the journal. Exact reviewed blobs are recorded in sources.json. The
implementation is new safe Rust, with a conservative explicit-flush protocol.

Kernel integration must use CortenMM/OSTD frame ownership, reader/writer loans,
BIO completion generations and DMA quiescence. Host snapshots do not certify
these resources. Linux page, folio and buffer_head ownership is not imported.
Full-feature, kernel-concurrency, mount and writable-filesystem gates remain
closed. This component does not authorize a mounted writable ext4 filesystem.

The bounded [EA namespace durable transaction](EA_DURABLE_NAMESPACE.md) adds a
separate EA-aware single-transaction writer, raw crash-cut journal discovery and
checked repaired-shadow recovery. Its explicit atomic-block, flush,
exclusive-source and restart-quiescence premises require CortenMM/OSTD and
actual-device refinement. Full EA filesystem, concurrent EA windows, mounted
operation and hardware durability gates remain open.
