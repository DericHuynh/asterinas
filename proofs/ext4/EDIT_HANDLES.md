<!-- SPDX-License-Identifier: MPL-2.0 -->

# Borrowed concurrent edit batches

`edit_handles.rs` implements reserved, disjoint candidate edit slots in safe
Rust. `edit_schedule.rs` proves arbitrary finite interleavings of the same slot
transition relation. This completes a bounded part of C-RUN. It does not create
a filesystem operation, reserve space in a shared journal, or authorize I/O.

## Ownership and credit contract

`reserve` validates one through 250 strictly increasing targets against the
sealed journal layout. Each target owns one credit and one slot. The target
plan remains immutable. A running batch can lend two disjoint parts; a part can
lend further parts or one mutable handle. Checked `final` reference relations
connect all returned slots back to their parent batch, including exact values
outside an edited slot. No scalar owner ID or assumed fresh integer stands in
for the actual Rust borrow.

The `Open`, `Stage`, `Close` and `Abort` transition definitions occur in the
executable methods' checked contracts. The schedule proofs use these exact
definitions. Enabled steps preserve sorted targets, slot count and image
identity. Events at different positions commute. Closed and aborted slots stay
retired throughout every admitted finite execution. Image buffers always have
4,096 bytes and retain the target of their reservation.

| State | Permitted operation | Result |
| --- | --- | --- |
| Unused | Borrow handle | Open; fixed target and credit |
| Open | Stage 4 KiB | Replace private owned snapshot |
| Open | Stage another length | Reject; preserve slot |
| Open | Consume close | Closed; retain last snapshot or no image |
| Open | Consume abort | Aborted; discard snapshot |
| Closed or Aborted | Reopen | Reject |

Dropping a handle while open leaves that slot open. A worker that unwinds before
closing cannot silently approve its edits. Aborted slots are sticky. Workers
must explicitly close unused credits as well as credits carrying images.

`freeze` consumes the batch after all borrows end. It checks that every slot is
closed and that every image matches its target. Rejection returns the unchanged
batch. Success moves the selected images into a sealed `FrozenBatch` in target
order, preserving exact bytes and the reserved layout. It omits credits closed
without an image. An empty frozen batch is permitted, but cannot encode a JBD2
transaction. A nonempty batch still passes all canonical encoder checks,
including sequence, UUID and primary-superblock replay policy. Owned frozen
bytes can enter the existing serialized writer; batching alone grants no
filesystem or device authority.

## Verification and concrete checks

The full pinned Verus invocation checks every body and compiles the public API.
It introduces no local trusted specification, assumption or external body. The
slice split helpers use the pinned standard-library models for `split_at_mut`
and full range indexing to establish fixed final lengths and disjoint parent
composition. The immutable plan and keys have type invariants. Mutable storage
has explicit shape checks and normal-return preservation contracts; no unwind
guarantee is assumed for a library operation whose pinned model lacks one.

Native tests run four scoped Rust workers on nested disjoint partitions, verify
overwritten snapshots and input-buffer mutation, reject failed/dropped/aborted
handles, exercise the exact 250-credit boundary, and encode two workers' images
for independent e2fsprogs JBD2 recovery. Negative Rust compilation checks reject
forgery, target redirection, reuse after close, aliased handles, freezing a live
borrow and forged frozen batches. These are host API checks; thread scheduling
and the native test harness are not formally verified.

## Linux reference and remaining refinement

Linux v7.0 `fs/jbd2/transaction.c` reserves credits before allowing a handle to
join a running transaction and accounts for live updates before commit can
freeze it. This implementation uses typed borrowed slots and explicit close
instead of copying Linux `buffer_head` ownership or update counters. It does
not yet implement Linux's complete shared journal-space accounting, overlapping
running/committing/checkpoint queues, transaction extension/restart, revokes,
or filesystem operation closure. Those need additional executable transitions
and proofs before C-RUN/C-COMMIT/C-CHECKPOINT can be discharged.

The actual upper-half adapter must use CortenMM/OSTD frame, lock and DMA loan
ownership. An owned host vector models immutable bytes; cloning an OSTD frame
would not establish that immutability. Mount activation, VFS authorization,
deadlock freedom, device persistence and concurrent filesystem durability
remain open. The production activation gates stay closed.
