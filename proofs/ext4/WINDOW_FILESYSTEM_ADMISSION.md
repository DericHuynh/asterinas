<!-- SPDX-License-Identifier: MPL-2.0 -->

# Fresh bootstrap and filesystem admission for a concurrent window

`window_admission::prepare` seals a reserved multi-transaction window to its
immutable source and complete static filesystem certificates. It discovers the
journal from the source, checks the complete initial filesystem, and checks the
dirty-marked image and every complete home prefix before returning an I/O owner.
A later transaction cannot excuse an invalid earlier prefix: a crash can retain
that earlier durable commit without the later repair.

This is full allocation/directory/namespace validation within FORMAT_PROFILE.md.
It does not expand that bounded on-disk profile, establish operation permission,
or enable a kernel mount. In particular, sound success certificates and
completeness of the validator's acceptance domain are distinct obligations.

## Construction and ownership

The factory derives primary geometry, group-zero descriptor, journal inode 8,
journal extent, journal UUID and exact journal bytes from the same `Snapshot`.
The checked initial journal mapping must equal the mapping used by the window
encoder. Each prefix passes `bootstrap_identity::check` and the actual
`image_validation::inspect` pipeline; its journal mapping must remain identical.
Thus every admitted prefix preserves the immutable primary fields, every group
bitmap/table address and all 256 bytes of inode 8. Other inodes in the same
physical block remain editable.

The source borrow, owned encoded window and ghost certificates travel together
through dispatch, completion and abort. All public executable methods are total
and have no caller-supplied proof preconditions. Private fields and consuming
requests prevent substituting a raw engine or source, redirecting completion,
reusing requests, or changing command bytes through a shared loan.

`PatchSet::upsert` owns the latest image at each target. Its proof relates each
replacement/insertion to exactly one whole-block shadow update and preserves all
other bytes. Cumulative prefix validation overlays one dirty patch and one
cumulative home patch on the original source. It consumes two additional shadow
layers for any admitted window length, including 64 transactions, rather than
one layer per transaction. The existing 4,096 cumulative payload-entry bound
remains; the dirty singleton has a separate layer and does not consume home
patch credits. Input snapshots need two free layers. Allocation failure and
unwinding are outside the ordinary-return host-library claim.

## Fresh crash-source discovery

`window_bootstrap.rs` starts from the exact initial filesystem block map and
flattens the byte-valued persistence model into a fresh source. Each nonjournal
block is either its original source block, the dirty primary, or an exact home
image from a transaction. A home image equals that block in its corresponding
complete validated prefix. The primary and group-zero descriptor may come from
different prefixes; the proof does not force them to share an endpoint.

The allocation census proves that the inode-8 table block cannot alias the
primary, descriptor block or any journal block. Every possible table-block
version preserves exactly the journal-inode slice. The independent primary,
descriptor and inode facts establish the source-derived bootstrap predicate and
unchanged locator geometry at every cut of every finite enabled persistence
trace, including error and abort cuts. The existing complete `bootstrap::locate`
contract therefore establishes actual Some/None discovery for these sources.

The fresh bootstrap's canonical scan input is proved equal to the exact actual
window journal, including its current header, UUID and checksum seed. Existing
actual-scanner admission, maximal committed-suffix recognition and redo closure
therefore apply to freshly discovered inputs. No CRC injectivity or retained
caller-provided journal coordinate substitutes for this proof.

## Full recovered-image admission

Cold restart uses `recovery_admission::prepare` on the fresh, quiescent source.
It discovers bootstrap first, runs the actual maximal scan, forms the exact
selected-home plus retired-tail shadow and validates the complete repaired
filesystem before returning any wrapped recovery request. A partially
checkpointed home filesystem may fail static validation before replay; that
failure must not preempt discovery and repair.

The composition theorem binds every successful cold-recovery certificate to the
actual window scan and exact final shadow. `successful_admitted_cold_recovery_has_the_exact_complete_filesystem_image`
composes admitted-recovery image refinement: successful durable media equal the
complete validated image and have no late modeled persistence.
Every subsequent modeled crash during such an admitted recovery also preserves
fresh bootstrap discovery with the original window geometry.

There is deliberately no theorem claiming that `image_validation::inspect` or
`recovery_admission::prepare` always returns `Some` for every logically valid
complete-prefix repair. Whole allocation/namespace validation completeness and
certificate framing across changed journal-body bytes remain open. Cold recovery
reruns the full validators on its actual repaired shadow and fails closed.
Native all-cut tests exercise successful admission; they do not prove this
remaining acceptance/completeness theorem. The existing arbitrary finite retry
byte-target closure remains checked independently in CONCURRENT_RECOVERY_CLOSURE.md.

## Design and proof table

| Design obligation | Checked artifact | Remaining boundary |
| --- | --- | --- |
| J-LOCATE / J-BOOT | Exact source-bound initial and every-prefix identity; independent valid primary/GDT mixtures and fixed inode 8 establish fresh bootstrap at every finite window cut | Dynamic resize, source capture/reset and device refinement |
| C-COMMIT / C-CHECKPOINT | Every complete transaction prefix passes actual allocation, directory and namespace validation before the first request; exact cumulative patches use two layers | Operation authority, circular reuse and simultaneous pending BIOs |
| F-ADMIT | Full static success certificates for the initial image and every prefix; cold recovery validates its actual complete repaired shadow | Some/None completeness of full-image and recovery factories; full ext4 feature set |
| C-RECOVER / J-RESTART | Fresh discovered scan equals actual window journal; successful cold admission binds the exact complete result; further admitted-recovery cuts keep fresh discovery | Unconditional full-filesystem cold/repeated admission completeness |
| S-RACE | Source/engine/certificates retained through consuming requests; negative Rust checks reject forgery, substitution, reuse, mutation and live-loan consumption | Actual OSTD worker locks, callbacks and CortenMM frame/DMA ownership |
| D-ORDER / D-ATOMIC / D-QUIESCE | Existing byte-valued atomic-block and flush model supplies the crash projection | Exclusive protected window, matching quiescent initial capture, atomic 4 KiB persistence, flush draining prior writes, quiescent reset on every restart |

## Linux references and native regressions

The pinned Linux `fs/ext4/super.c` reference discovers and checks the internal
journal inode in `ext4_get_journal_inode`, then loads the journal in
`ext4_load_journal`; `fs/jbd2/recovery.c::jbd2_journal_recover` scans, collects
revokes, replays, syncs and flushes. The Rust source and proofs are independent;
no Linux page, folio or buffer_head ownership is imported. CortenMM/OSTD frame and
BIO/DMA adapters remain required by the framekernel architecture.

Native tests cover every request cut of an interleaved two-version window,
independently changed primary/GDT/inode-table blocks, an independent internal
journal UUID, Linux final recovery, a
partially checkpointed hard-link update repaired before admission, rejection of
an invalid initial image and an invalid intermediate prefix later repaired,
protected inode-8 edits with valid CRCs, all 64 prefixes at source shadow depth
30, patch replacement at capacity, and sticky abort/error behavior. These tests
supplement the entire-crate Verus proofs. Production, full-feature,
concurrent-filesystem and mount/write gates remain false.

The bounded [EA namespace durable transaction](EA_DURABLE_NAMESPACE.md) adds a
separate EA-aware single-transaction writer, raw crash-cut journal discovery and
checked repaired-shadow recovery. Its explicit atomic-block, flush,
exclusive-source and restart-quiescence premises require CortenMM/OSTD and
actual-device refinement. Full EA filesystem, concurrent EA windows, mounted
operation and hardware durability gates remain open.
