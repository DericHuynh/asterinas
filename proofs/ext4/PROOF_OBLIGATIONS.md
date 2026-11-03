<!-- SPDX-License-Identifier: MPL-2.0 -->

# Proof obligations and acceptance gates

**No end-to-end filesystem claim is closed.**
The table records checked abstract obligations, partial executable results and
missing refinements separately. Tests and Linux/fsck runs do not close formal rows.
See verification-evidence.json for the pinned entire-crate result.

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
| J-ALG | Complete redo is idempotent and overrides any compatible partial checkpoint. | Checked abstractly: redo.rs domain preservation, idempotence and partial-checkpoint completion. |
| J-INIT | The abstract initial invariant is satisfiable for a nonempty transaction. | Checked: initialization plus explicit nonempty commit/retirement/public-success witnesses. |
| J-STEP | Every allowed single-transaction transition preserves the invariant. | Checked abstractly: journal.rs step preservation and persistence.rs event refinement. |
| J-ACK | An acknowledged abstract transaction recovers its after-state. | Checked abstractly: acknowledged transactions survive; public success additionally requires quiescent retirement. |
| J-CUT | Recovery returns before or after, never a partial transaction. | Checked abstractly: before/after recovery and composed acknowledged-prefix theorem in system.rs. |
| J-TRACE | Induct over arbitrary finite histories and transaction composition. | Checked for arbitrary finite model histories and per-unit I/O interleavings, composed in system.rs. Raw device/disk refinement remains open. |
| J-REUSE | Safe ring reuse, bounded credits, tail fencing, no stale records/I/O, and finite TID/wrap behavior. | Partial: injective ring positions, bounded credits, finite counters, and no late model events after quiescent retirement. Physical window/slot/tail refinement missing. |
| J-REVOKE | No replay of old metadata into a later freed/reused data block; correct revoke cancellation and sequence rules. | Partial: executable same/later revoke filtering, latest image selection, reallocation ordering and exact chronological-redo equivalence checked. Allocation/writer/revoke production and complete scan refinement remain open. |
| J-BOOT | Crash-safe ext4 needs-recovery and JBD2 superblock/head/tail/sequence transitions. | Partial: exact state-image codecs and geometry/UUID/boot-byte framing, conservative fresh epochs, block-zero replay retains RECOVER; recovery tail protocol checked under an explicit device contract. Activation/unmount and writer composition remain open. |
| J-RESTART | Physical recovery can crash at any sector/write/fence boundary and resume safely. | Partial: exact replay restart after arbitrary partial home changes; byte-valued recovery persistence/completion/abort interleavings and safe clear-tail cuts checked under an explicit 4 KiB atomicity/flush/quiescent-start contract. Scanner completeness, device refinement and end-to-end closure remain open. |
| J-ERROR | Abort/error/timeout is not cancellation or proof of rollback; no false success after abort. | Partial: abort preserves pending effects and forbids new acknowledgements in the checked model. Runtime error/quiescence refinement missing. |
| D-ORDER | Completion/flush/FUA/dependency contracts for each admitted driver and partition wrapper. | Missing. |
| D-ATOMIC | Addressing, failure-atomic unit, tearing, volatile cache, and crash projection match the hardware model. | Missing. |
| D-DMA | Frozen snapshot, coherence, generation-bound completion, and lifetime/loan return. | Missing. |
| D-QUIESCE | No old-generation DMA or I/O can affect reused memory/log/home space. | Missing. |

The M0 commit and retirement predicates must be refined to byte-level recognition.
A checksum-equality assumption cannot substitute for that proof.

## Format and filesystem state

| ID | Obligation | Present artifact / missing work |
| --- | --- | --- |
| F-ADMIT | Sound and complete admission for the exact supported feature/profile rules; fail closed elsewhere. | Partial: checked exact structural feature/profile predicates with success/rejection equivalence. Whole-volume and mount admission missing. |
| F-PARSE | Total bounded parsers with checked arithmetic and range/resource safety for arbitrary media. | Partial: total bounded metadata and canonical descriptor/revoke parsers; ring scanning, committed source provenance and record-before-commit ordering checked. Full-prefix scanner completeness and whole-volume validation missing. |
| F-CODEC | Encode/decode relation, endian conversions, checksums, seeds, escaping, UUIDs, tag/record lengths, and canonical Linux-compatible bytes. | Partial: checked endian/extent/header/tag and complete canonical v3 descriptor/revoke/commit codecs, CRC streaming, metadata checksum inputs, UUIDs and owned escaping. Transaction writer and complete disk-history refinement missing. |
| F-MAP | Extent-tree bounds/order/depth, initialization/unwritten semantics, and logical-to-physical refinement. | Partial: checked inline leaf roots, logical disjointness and initialized/unwritten mapping. Nonzero tree depth rejected; global ownership/refinement missing. |
| F-OWN | Global no-alias ownership, reserved/journal/metadata/data separation, and allocation/free-counter consistency. | Partial: abstract role map, allocation/release/write preservation and owner uniqueness checked in ownership.rs. Actual disk ownership/bitmap validator missing. |
| F-READ | Authorized reads return exactly initialized bytes/zeros within i_size and never stale reused contents. | Partial: abstract zero initialization, stale-generation rejection and no disclosure after block reuse checked. Executable authorized file-read refinement missing. |
| F-OPS | Each supported create/read/write/attribute operation preserves valid filesystem state and refines its observable result. | Missing. |
| F-NAME | Directory entry validity, link counts, rename atomicity, topology, and lookup consistency. | Missing; do not enable unproved namespace operations. |
| F-ORPHAN | Open-unlinked lifetime, orphan persistence, restartable truncate/reclamation, and last-close behavior. | Missing. |
| F-CREDITS | Complete transaction closure is bounded and reserved before public mutation; ENOSPC/ENOMEM unwind is safe. | Partial: checked bounded payload/log arithmetic. Filesystem transaction closure and fallible resource reservation missing. |
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
| S-ENTRY | Unverified callers cannot forge capabilities or bypass verified preconditions. | Partial: executable parsers/helpers are total and have no public requires clauses. Capability/VFS/kernel ingress refinement missing. |
| S-AUTH | Path permissions, open-handle rights, credential/mount mappings, policy checks, and inode generations have correct POSIX meanings. | Partial: executable Linux DAC subset and owner/override properties checked. Credential/idmap binding, ACL/LSM policy, namespace and handle integration missing. |
| S-LEASE | A current writer is unique; releasing/reacquiring does not resurrect an old lease. | Checked at the abstract lease and affine resource-token scopes; actual OSTD guard refinement remains open. |
| S-TOKEN | Token constructors and Verus tracked ownership refine real OSTD lock guards and caller identities. | Partial: gate.rs affine capability uniqueness and claim/release/reacquire checked using vstd resource algebra. OSTD lock and identity bridge missing. |
| S-CACHE | Private/frozen/initialized/cache-visible/user-mapped/DMA states cannot be confused; no stale page after truncate/reuse. | Partial: owned initialized snapshot, no mutable exposure, independent capture and escape/restore checked. CortenMM frame/user mapping/cache/DMA refinement missing. |
| S-RACE | All operation/callback/abort/unmount/reset interleavings preserve invariants. | Partial: all modeled finite operation/I/O/abort interleavings checked. Runtime callback/unmount/reset/lock integration missing. |
| S-LOCK | Consistent hierarchy and no blocking under spinlocks, callback dependency cycles, or gate reentry. | Missing. |
| S-RECOVERY | No callers are admitted until the recovered image and mount state are validated. | Missing. |
| S-RESOURCE | Malformed lengths, deep/cyclic metadata, sparse ranges, queue saturation, and reservation exhaustion are bounded or rejected. | Partial: checked bounded parser/name/extent/snapshot loops and credit arithmetic. Whole-volume traversal, reservation failure and queue-progress refinement missing. |
| L-PROGRESS | Deadlock freedom, eventual I/O/credit/gate progress, and recovery termination under stated fairness. | Partial: recovery command rank and finite failure-free successful completion checked. Scheduler/device fairness, scanning completeness, resource availability and kernel lock/progress proofs remain open. |

## Milestone acceptance

- M0 is checked by the pinned full-crate Verus run, including negative witnesses
  and nonempty positive witnesses, with no local proof escapes and recorded hashes.
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

## Current milestone status

M0 is checked. M1 has checked logical history, per-unit persistence-contract,
quiescence and bounded-generation composition; the raw-media refinement is open.
M2 has the exact structural subset in FORMAT_PROFILE.md, not whole-volume admission.
M3 has checked role/initialization models and a DAC core, not filesystem operations.
M4 has an affine gate and immutable host snapshot, not OSTD adapters.
M5-M7 are not implemented.

The checked composed theorem may not be used as a substitute for J-REVOKE,
J-BOOT, D-ORDER/D-ATOMIC/D-DMA/D-QUIESCE, F-OPS/F-NAME/F-ORPHAN,
S-LOCK/S-RECOVERY, or the remaining executable refinements.
The full design and proof remain unfinished.
