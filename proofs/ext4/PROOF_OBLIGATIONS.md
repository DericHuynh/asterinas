<!-- SPDX-License-Identifier: MPL-2.0 -->

# Proof obligations and acceptance gates

**Every row is open.** "Candidate" means a statement/body was drafted, not that
Verus accepted it. Tests and successful Linux/fsck runs do not close these rows.

## Intended top-level theorems

These are intended theorem forms, not implemented top-level proofs:

- **Refinement:** every concrete admitted operation and callback step simulates
  the specified filesystem/journal/device transitions.
- **Authorization:** each linearized path operation has the required current
  namespace permission; handle operations have a valid, nonforgeable open
  capability and matching inode generation.
- **Isolation:** a legal operation cannot access another device/partition,
  another owner's allocated blocks without authority, the journal as file data,
  or uninitialized bytes.
- **Crash consistency:** for every admitted execution and crash cut, including
  allowed pending-write persistence during that cut, recovery corresponds to a
  legal prefix of the linearized committed transaction history that includes
  all durable acknowledgements. Aborted-before-commit attempts are not
  transactions in that history; a commit whose reply was lost may be included.
- **Recovery closure:** every partial recovery step preserves enough stable
  information for another recovery to reach the same legal state.
- **Concurrency safety:** all allowed interleavings preserve the ownership,
  initialization, lock, lease, and journal invariants.
- **Progress:** under explicit scheduler/device fairness, resource availability,
  no new crashes, and no relevant I/O failure, the supported operations and
  recovery terminate. Safety alone does not prove this theorem.

A legal prefix expresses later overwrites correctly: it does not require the
original value of every acknowledged write to remain visible forever.

## Journal and device

| ID | Obligation | Present artifact / missing work |
| --- | --- | --- |
| J-ALG | Complete redo is idempotent and overrides any compatible partial checkpoint. | Candidate redo.rs algebra. |
| J-INIT | The abstract initial invariant is satisfiable for a nonempty transaction. | Candidate initialization and explicit commit/retire witness. |
| J-STEP | Every allowed single-transaction transition preserves the invariant. | Candidate journal.rs step lemmas and next-step case split. |
| J-ACK | An acknowledged abstract transaction recovers its after-state. | Candidate; only the M0 single-transaction abstraction. |
| J-CUT | Recovery returns before or after, never a partial transaction. | Candidate; same M0 scope. |
| J-TRACE | Induct over arbitrary finite histories and transaction composition. | Missing. |
| J-REUSE | Safe ring reuse, bounded credits, tail fencing, no stale records/I/O, and finite TID/wrap behavior. | Missing. |
| J-REVOKE | No replay of old metadata into a later freed/reused data block; correct revoke cancellation and sequence rules. | Missing. |
| J-BOOT | Crash-safe ext4 needs-recovery and JBD2 superblock/head/tail/sequence transitions. | Missing. |
| J-RESTART | Physical recovery can crash at any sector/write/fence boundary and resume safely. | Algebra candidate only; physical transition/refinement missing. |
| J-ERROR | Abort/error/timeout is not cancellation or proof of rollback; no false success after abort. | M0 allows late persistence; executable and quiescence proofs missing. |
| D-ORDER | Completion/flush/FUA/dependency contracts for each admitted driver and partition wrapper. | Missing. |
| D-ATOMIC | Addressing, failure-atomic unit, tearing, volatile cache, and crash projection match the hardware model. | Missing. |
| D-DMA | Frozen snapshot, coherence, generation-bound completion, and lifetime/loan return. | Missing. |
| D-QUIESCE | No old-generation DMA or I/O can affect reused memory/log/home space. | Missing. |

The M0 commit and retirement predicates must be refined to byte-level recognition.
A checksum-equality assumption cannot substitute for that proof.

## Format and filesystem state

| ID | Obligation | Present artifact / missing work |
| --- | --- | --- |
| F-ADMIT | Sound and complete admission for the exact supported feature/profile rules; fail closed elsewhere. | Profile proposal only. |
| F-PARSE | Total bounded parsers with checked arithmetic and range/resource safety for arbitrary media. | Missing. |
| F-CODEC | Encode/decode relation, endian conversions, checksums, seeds, escaping, UUIDs, tag/record lengths, and canonical Linux-compatible bytes. | Missing. |
| F-MAP | Extent-tree bounds/order/depth, initialization/unwritten semantics, and logical-to-physical refinement. | Missing. |
| F-OWN | Global no-alias ownership, reserved/journal/metadata/data separation, and allocation/free-counter consistency. | Missing. |
| F-READ | Authorized reads return exactly initialized bytes/zeros within i_size and never stale reused contents. | Missing. |
| F-OPS | Each supported create/read/write/attribute operation preserves valid filesystem state and refines its observable result. | Missing. |
| F-NAME | Directory entry validity, link counts, rename atomicity, topology, and lookup consistency. | Missing; do not enable unproved namespace operations. |
| F-ORPHAN | Open-unlinked lifetime, orphan persistence, restartable truncate/reclamation, and last-close behavior. | Missing. |
| F-CREDITS | Complete transaction closure is bounded and reserved before public mutation; ENOSPC/ENOMEM unwind is safe. | Missing. |
| F-SYNC | Write-prefix, fsync/fdatasync/directory-fsync, lost replies, error propagation, and writeback-error semantics. | Missing. |

For F-OPS, prove: valid_fs(before) and the operation's actual authority/inputs
imply a valid after-state plus the specified result and patch relation.
Do not merely assume valid_fs(after) at a wrapper boundary.

Unbounded unlink/truncate work needs proved orphan/deferred-reclamation
transactions. Large writes need an explicit short-write/prefix contract.
Neither is silently treated as a single bounded atomic operation.

## Security and concurrent integration

| ID | Obligation | Present artifact / missing work |
| --- | --- | --- |
| S-ENTRY | Unverified callers cannot forge capabilities or bypass verified preconditions. | Missing. |
| S-AUTH | Path permissions, open-handle rights, credential/mount mappings, policy checks, and inode generations have correct POSIX meanings. | Missing. |
| S-LEASE | A current writer is unique; releasing/reacquiring does not resurrect an old lease. | Abstract predicate candidates in lease.rs. |
| S-TOKEN | Token constructors and Verus tracked ownership refine real OSTD lock guards and caller identities. | Missing; S-LEASE alone does not establish this. |
| S-CACHE | Private/frozen/initialized/cache-visible/user-mapped/DMA states cannot be confused; no stale page after truncate/reuse. | Missing. |
| S-RACE | All operation/callback/abort/unmount/reset interleavings preserve invariants. | M0 I/O interleavings only; integration proof missing. |
| S-LOCK | Consistent hierarchy and no blocking under spinlocks, callback dependency cycles, or gate reentry. | Missing. |
| S-RECOVERY | No callers are admitted until the recovered image and mount state are validated. | Missing. |
| S-RESOURCE | Malformed lengths, deep/cyclic metadata, sparse ranges, queue saturation, and reservation exhaustion are bounded or rejected. | Missing. |
| L-PROGRESS | Deadlock freedom, eventual I/O/credit/gate progress, and recovery termination under stated fairness. | Missing. |

## Milestone acceptance

- M0 is accepted only after the pinned full-crate Verus run checks every named
  candidate, including negative witnesses and the nonempty positive witness,
  with no local proof escapes and recorded source/version hashes.
- M1-M4 require new models and executable refinement proofs, not just more
  examples that instantiate M0.
- Read-only admission requires its parser, ownership/authorization, bounds,
  cache, and recovery gates. "Read only" does not make hostile parsing safe.
- Writable admission requires every applicable journal/device/format/operation/
  security gate for the declared feature profile, plus Linux byte compatibility.
- Each later feature identifies the invariants it changes and re-proves all
  dependent obligations. Ordered mode, transaction overlap, mmap, direct I/O,
  fast commit, log optimization, and block reuse are separate changes.

No production feature may use this document's desired theorem as an axiom.
