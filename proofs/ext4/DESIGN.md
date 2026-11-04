<!-- SPDX-License-Identifier: MPL-2.0 -->

# Design: a Linux-compatible ext4 subset proved with Verus

Status: target design, partially implemented and checked.
The current evidence is in README.md and proof-status.json.
This document does not certify the unfinished filesystem or kernel integration.

## Decisions and scope

The user selected a Linux-compatible ext4 subset. Propose an initial 4 KiB
filesystem-block profile with an internal JBD2 journal, extents, bounded
transactions, full data journaling ("data=journal"), and one transaction in
flight. There is no new journal or filesystem byte format.

Every feature and inode representation must be explicitly admitted. The
profile is intentionally narrower than a default mke2fs filesystem.
An unsupported feature is rejected before writes; Linux's willingness to
ignore some COMPAT bits is not a proof that this implementation may do so.
[FORMAT_PROFILE.md](FORMAT_PROFILE.md) separates planned features from support.

All new kernel implementation code must stay in safe Rust above OSTD.
CortenMM frame ownership and OSTD VmReader/VmWriter, locking, and DMA APIs
remain the memory boundary. Linux struct page, buffer_head, and folio ownership
are not interchangeable with those APIs.

## Architecture and refinement direction

~~~mermaid
flowchart TD
    S["Filesystem operation specification"]
    C["Verified namespace, extent, allocation, and access-control core"]
    J["Verified transaction and recovery protocol"]
    F["Verified ext4/JBD2 byte codecs and admission"]
    A["OSTD frame, lock, BIO, and persistence adapters"]
    D["Device contract: completion, flush, atomic units, failure"]
    S --> C
    C --> J
    J --> F
    F --> A
    A --> D
~~~

The arrows are required refinement obligations, not existing verified calls.
The checked core and proof code live independently in proofs/ext4 and are not
members of the kernel workspace. A later component should remain outside aster-core where
the repository's component/layer rules allow it. Public VFS interfaces and
lock order must be audited before selecting the concrete integration location.

The core owns filesystem state and private transaction after-images.
The VFS adapter supplies validated handle/credential/mount-policy capabilities.
The journal owns immutable log images and log reservations.
The I/O adapter owns submitted BIOs and records generation-bound completions.

## Observable filesystem contract

The abstract filesystem contains inode generations and types; file lengths and
logical bytes; directory links and link counts; extent trees; free/reserved/owned
blocks; open handles and orphans; and authorization/mount policy.

A transaction transforms one valid abstract filesystem state into another.
The operation proof must establish authorization and preservation of that
validity. The journal proof only makes an already justified transformation
crash consistent; it cannot make an unauthorized or corrupt patch legitimate.

Initial bounded mutating operations are synchronous. The durable point is the
successful commit fence; the proposed first implementation keeps the operation
gate through checkpoint and durable retirement before publishing success.
This is stronger than the minimum durability of a normal Linux write.
A large write may return a durably committed byte prefix; the specification
must not silently promise whole-syscall atomicity for arbitrary write lengths.
Operations whose metadata closure cannot fit reserved credits are not started.

File fsync covers the file data and metadata needed to retrieve it. Directory
fsync covers namespace changes. Fdatasync may initially provide the stronger
fsync guarantee. File fsync is not used as a substitute for proving directory
durability. A failed or interrupted call can still have committed: an error
after submission is not evidence of rollback.

Open-file capabilities follow POSIX semantics. Chmod affects future permission
checks; it does not automatically revoke an existing valid writable descriptor.
Path-based operations check policy at the specified namespace linearization
point. Inode generations and open references prevent descriptor reuse attacks.

## Storage and crash model

Model separately:

- issued writes and their immutable snapshots;
- completed requests, which may only be in volatile device cache;
- durable atomic storage units;
- pending device writes that may persist in an allowed order;
- successful persistence fences; and
- a crash that drops volatile caches and CPU state.

A crash can occur between any two atomic persistence events, inside a
multi-sector filesystem-block write, between flush submission and completion,
while a caller waits, during checkpoint, during tail update, or during recovery.
A completed ordinary Write BIO is not automatically durable.

The failure-atomic unit is a device-contract parameter. Asterinas's 512-byte
SECTOR_SIZE is an addressing unit, not evidence of power-loss atomicity.
A writable mount must establish the concrete device's atomicity and flush
contracts, or use a proved protocol for a weaker device. Otherwise it is refused.

The initial profile uses one device for filesystem and journal. Multi-device
flush ordering, async commit, and a volatile cache that lies about flush success
are outside that profile. Device errors may leave writes partially durable or
still in flight. Abort prevents new application acknowledgements and mutations;
it does not cancel issued writes or make their DMA buffers safe to free.

Stable-media corruption after a successful durable fence and a malicious drive
are different fault models from crash persistence. CRC is neither an
authentication code nor a collision-free oracle. Full guarantees against
malicious storage would require a separately designed authenticated root and
freshness/rollback protection.

## Journal protocol

~~~mermaid
stateDiagram-v2
    [*] --> Stage
    Stage --> Prepare : reserve complete closure and freeze after-images
    Prepare --> Prepared : payload/descriptors/revokes stable after flush
    Prepared --> CommitIssued : submit commit record
    CommitIssued --> Durable : commit persistence fence succeeds
    Durable --> Checkpoint : write committed after-images to home addresses
    Checkpoint --> HomeStable : all home writes durable after flush
    HomeStable --> Retired : durable tail/sequence update
    Retired --> [*] : quiesce old generation, release reservations
~~~

An internal durable acknowledgement can be justified only at Durable or later.
The conservative initial public operation returns at Retired. Future earlier
publication or background checkpointing needs an additional refinement proof.

1. Reserve transaction credits, log space, data/metadata blocks, and private
   memory before modifying public state.
2. Materialize the entire transaction closure into private immutable after-images:
   file data, extent nodes, inode-table blocks, bitmaps, group/superblock fields,
   directory blocks, and applicable orphan/revoke information.
3. Submit journal descriptors and payloads. Freeze images until all corresponding
   DMA loans are returned. Flush and wait for the persistence contract.
4. Only then issue the commit record. A successful ordinary completion is still
   insufficient; establish its persistence with the device contract.
5. Checkpoint only committed after-images. Partial checkpoint writes are safe
   because complete redo remains available.
6. Flush home writes before making a durable tail/sequence update that permits
   recovery to ignore the transaction.
7. Reuse no journal slot, freed filesystem block, frame, or transaction generation
   until the appropriate retirement and I/O-quiescence proofs permit it.

The core must never mutate a frozen journal image via a cache alias.
A writable mmap can bypass an inode/page-cache mutex, so initial writable mmap
and direct I/O are not admitted. A later mmap design must prove write protection,
TLB shootdown, dirty-generation tracking, and snapshot ownership. Existing
Asterinas page-cache behavior is not assumed to imply those properties.

If publication ever precedes checkpoint completion, readers must resolve
committed journal/cache after-images rather than stale home blocks. The initial
gate avoids that externally observable window. The future read-overlay rule
must be proved before asynchronous publication is allowed.

## Recovery contract

For a legal operation history H and every admitted crash image d, recovery
must produce a state corresponding to a legal durable prefix of H that includes
every acknowledged durable transaction. It may include a committed transaction
whose reply was lost. It may not expose a transaction's partial after-images.

A recovery attempt may itself crash. It retains the necessary journal records
until replayed home writes are durable and retirement is durable. Reapplying
the same after-images must be idempotent. Tail advancement is not permitted
merely because replay writes were submitted.

The checked journal.rs models one transaction and partial checkpointing.
history.rs, persistence.rs and system.rs compose arbitrary finite histories,
per-unit completion/persistence events, quiescent reuse and bounded u32 IDs.
The "committed" and "retired" bits still mean semantic durable facts;
they are not a concrete record recognizer.
Single-transaction physical record recognition, tail ordering, revoke replay
and fresh epoch selection are now checked under the explicit device contract.
The active scanner and recovery preparation admit every legal writer crash
snapshot under their resource profile. Serialized physical writer generations
compose over actual durable maps, and arbitrary finite recovery crashes preserve
admission; an uncleared journal retains its committed input. Actual runtime
serialization, driver refinement and unmount remain open. Ring position injectivity and counter arithmetic helpers
do not discharge those obligations. The model stops before counter wrap and
reserves room for a representable next-tail sequence.

Recovery of a foreign dirty Linux journal is admitted only after the relevant
transaction/revoke/feature profile has been proved. A clean-volume subset is
not permission to guess that an unknown dirty journal was produced by us.
The implementation must classify the bytes and reject unsupported recovery.

## Security and concurrency model

- Decode all geometry, record lengths, extents, and counters with checked
  machine arithmetic before producing typed identifiers or allocating memory.
- Every actual BIO address must be proved within the selected device/partition.
- Reserved journal and immutable format regions cannot become file data.
- Allocation tokens provide exclusive block roles and ownership; no live block
  is simultaneously free, journal, metadata, or another inode's data.
- Every newly readable byte is initialized, zero/hole semantics are explicit,
  and reading beyond i_size cannot disclose old frame or disk contents.
- Path permits, open-handle capabilities, inode generations, and transaction
  leases have distinct meanings. None is represented by an unchecked integer
  supplied by a user.
- Initial operations serialize through a sleeping gate. Async completion and
  abort still interleave with callers and are modeled independently.
- No I/O wait occurs while a spinlock is held. A proposed lock hierarchy is not
  accepted until checked against real VFS/dentry/inode/page-cache call paths.
- Runtime capability constructors, lock acquire/release, callback generations,
  unmount, and device-reset paths must refine the ownership model in Verus.
- Deadlock freedom and eventual completion require separate arguments.
  Progress additionally needs scheduler/device fairness and available credits.

## Linux reference points

| Reference | Design consequence |
| --- | --- |
| Linux ext4 journal documentation | Distinguish ordered metadata journaling from full data journaling; honor JBD2 byte order and records. |
| fs/jbd2/commit.c, journal_submit_commit_record | Model persistence fences; Linux uses PREFLUSH/FUA on the normal barrier path. |
| fs/jbd2/recovery.c, jbd2_journal_recover | Scan, revoke, replay, then make replayed writes persistent. |
| fs/jbd2/checkpoint.c | Checkpoint completion and log-tail reuse are distinct phases. |
| fs/ext4/fsync.c | Bind fsync to the relevant transaction and propagate writeback/flush errors. |
| ext4 extent format | Prove bounds, depth, initialized/unwritten semantics, and ownership. |
| Asterinas BlockDevice/BIO | Completion, queue reordering, flush support, frame loans, and error contracts need explicit adapter proofs. |

Pinned commits and file blob hashes are recorded in sources.json.
