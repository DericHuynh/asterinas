<!-- SPDX-License-Identifier: MPL-2.0 -->

# Crash and repeated-recovery closure of a concurrent journal window

The reserved-window engine now connects to the actual checked JBD2 scanner and
recovery protocol at every modeled commit/checkpoint/tail/persistence/error/abort
cut. A fresh scan returns exactly the physically durable, unretired suffix.
Replaying that suffix over partial checkpoint writes produces the same complete
transaction prefix as chronological redo from the retained initial image.
The prefix includes every reported commit and may include one additional commit
whose image persisted before its success callback.

This closes the bounded host protocol's scanner, replay and repeated-recovery
link using the retained validated journal mapping. It does not authorize filesystem operations or a writable kernel mount.
The engine still dispatches one pending request at a time; completed writes may
remain volatile while commit, checkpoint and tail lanes interleave. Runtime
worker locks, simultaneous pending BIOs, source capture and CortenMM/OSTD frame,
DMA and device refinement remain separate.

## Exact claim and contracts

Let `c` be the reported commit prefix, plus the current unreported transaction
if its commit image is stable. Let `r` be the prefix in the latest physically
persisted tail header, or zero before activation. The proofs establish
`reported commits <= c <= window length` and `r <= c`. An active scanner returns
exactly transactions `[r, c)`. A final clear tail implies all window homes are
already stable; an initial clean header implies no transaction has committed.

For every existing nonjournal block, successful recovery equals chronological
redo of transactions `[0, c)` from the initial block map, with the persisted
needs-recovery marking applied to block zero first. The marking is bookkeeping,
not an extra filesystem transaction. Block zero is included in the exact byte
claim; its metadata updates must also satisfy the checked replay policy, which
preserves volume identity and keeps RECOVER set. Clean unmount is separate.

Repeated recovery preserves this same byte-valued target. An uncleared journal
retains its exact canonical committed input, and another replay overrides any
partial home writes. A changed recovery tail implies complete stable homes and
a clean journal, so a subsequent empty replay retains that result. Induction
covers arbitrary finite recovery-attempt sequences, including attempts stopped
before completion, after failure and after abort.

The additional sealed [window filesystem admission](WINDOW_FILESYSTEM_ADMISSION.md)
wrapper checks the initial image and every complete home prefix before I/O,
preserves bootstrap identity and proves fresh discovery at every window cut.
Cold recovery validates its actual repaired shadow before returning requests.
Full-image/recovery acceptance completeness, operation permissions and runtime
refinement remain open; the raw window factory alone does not grant admission.

The device contract requires exclusive control of this protected journal
window, a quiescent initial device matching the retained source, atomic 4 KiB
writes, and successful flushes that drain earlier issued writes. Every new
recovery attempt starts from a quiescent crash/reset snapshot. Abort alone does
not establish quiescence: submitted effects may still persist. Actual hardware,
reset and DMA implementations are not inferred from a sector size or disk format.

## Admission correction

The old window factory could reserve more payloads than the actual scanner's
4,096-entry resource profile. Such a candidate could commit a journal that its
own checked recovery API would reject. Preparation now checks cumulative payload
credits before encoding each new version and rejects a window above 4,096.
The 64-version and 250-payload-per-transaction limits remain; a single descriptor
and commit consume additional log space but no replay entries.

This budget is proved sufficient for every recognized prefix and its next
record, including an incomplete descriptor whose payloads happen to pass CRC
checks. No checksum identity assumption is used. The native boundary regression
uses a Linux-created 128 MiB filesystem with a 32 MiB journal: 4,096 payloads in
17 transactions prepare, scan and recover through Linux; 4,097 are rejected
before I/O.

## Proof and design table

| Obligation | Checked artifact | Remaining boundary |
| --- | --- | --- |
| J-BOOT | `window_snapshot.rs`: every actual journal header is initial or an ordered prefix image; mapping, UUID, sequence, primary identity and active recovery policy survive every cut | Actual source provenance, reset and unmount |
| J-ACK / C-COMMIT | `window_provenance.rs`, `window_scan.rs`, `window_recognition.rs`: stable commits form a contiguous prefix; fresh metadata comes from exact issued images; maximal actual scans return exactly the unretired durable suffix | Operation/fsync authority and actual worker/driver refinement |
| C-CHECKPOINT / J-CUT | `window_redo.rs`, `window_recovery.rs`: chronological suffix redo covers every partial FIFO checkpoint and gives exact complete-prefix bytes for all nonjournal blocks, including block zero's persisted recovery mark | Circular reuse, sealed-credit reclamation and full filesystem operation preservation |
| J-RESTART | `window_recovery_profile.rs`: every finite window cut admits actual scanning and recovery; arbitrary finite recovery attempts preserve admission | Hardware quiescence and full filesystem/recovery acceptance completeness |
| J-TRACE | `window_repeated_recovery.rs`: every finite recovery crash history preserves the same exact target, and a final successful recovery reaches it | Unbounded progress, device responsiveness and scheduler fairness |
| S-RACE / D-ORDER | Actual media projection and every enabled finite lane/completion/persistence/failure/abort interleaving compose into scanner/recovery closure | OSTD locks, callbacks, simultaneous pending BIOs, CortenMM frame/DMA loans and device contracts |

`window_stream.rs` bounds every well-formed record prefix and its next record.
`window_records.rs` constructs exact canonical multi-transaction certificates
and chronological logs from retained after-images. The scanner's own
certificate, maximality and preparation contracts are used; a correct abstract
replay log is not supplied as a premise in place of actual parsing. Existing
recovery persistence and restart proofs supply the recovery-attempt refinement.
All modules remain in entire-crate verification and compilation with no local
trusted proof escapes or filtered verification.

The Linux reference is pinned v7.0 `fs/jbd2/recovery.c`: scanning starts at
`s_sequence`/`s_start`, publishes complete committed transactions, and bounds
later passes by the discovered end transaction. Exact reviewed ranges and blob
are recorded in sources.json. The Rust implementation and proofs are independent;
Linux page, folio and buffer_head ownership are not imported.

Native tests additionally cover differently sized transactions, repeated block
zero updates, an older persisted prefix tail, overwritten data, repeated recovery
crashes, and exact final primary/data bytes. They supplement the formal claims.
Kernel, full-feature, concurrent-filesystem and writable-mount gates remain false.
