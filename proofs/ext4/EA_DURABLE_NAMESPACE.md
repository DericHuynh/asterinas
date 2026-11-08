<!-- SPDX-License-Identifier: MPL-2.0 -->

# Durable EA namespace transactions

This component connects bounded, checked namespace edits to one serialized
Linux-compatible JBD2 transaction. It is an owned host core. Kernel VFS,
CortenMM/OSTD source capture, lock/BIO/DMA ownership and actual device refinement
remain open; the implementation does not enable a mounted writable filesystem.

## Admission and retained operation

The factory consumes one of the four existing prepared operation families:
same-directory rename, link/nonlast unlink/directory move, regular-file
rename/exchange, or general ordinary regular/directory exchange. It retains
the typed operation witness and the exact sorted patch set. It compares the
entire supplied immutable source against the prepared source before creating
a request. The retained proposal epoch records provenance; it is not checked against a live
Store or device epoch. A quiescent, exclusive device capture must match that
source before execution.

Preparation rejects empty/noop edits, more than eight changed home blocks,
targets zero or one, journal targets, changed locator identity, unsupported
features, read-only images, and a nonempty or mismatched initial journal.
The ordinary-profile writer and recovery APIs keep their original admission
guards. Existing volatile namespace preparation still rejects RECOVER images.

The EA-aware path inspects actual bytes with EA_INODE and RECOVER present.
It never clears a feature bit or substitutes a clean primary to obtain an
allocation or namespace certificate. Before I/O, the factory checks the
dirty-marked before image, the complete dirty-marked after-home image and the
exact completed log/home/tail shadow. It retains those certificates.
Partial checkpoints need not themselves be valid namespaces: cold recovery
discovers and scans the journal before inspecting allocation or directories.

## Durability contract

| Stage | Required ordering | Result under the device model |
| --- | --- | --- |
| Recovery marker | Write actual EA primary with RECOVER and exact checksum, then flush | Later journal requests start after recovery marking. |
| Activation | Write active journal header, then flush | A fresh scanner can locate the transaction. |
| Log | Descriptor and escaped payloads, log flush, commit record, commit flush | Acknowledgment begins only after successful commit-flush reporting. |
| Checkpoint | Exact original home images, then home flush | Every home is durable before tail retirement can start. |
| Retirement | Exact retired header, then tail flush | Success has exact final home/tail bytes and no enabled late modeled persistence. |
| Failure or abort | Stop new dispatch; retain issued writes and pending ownership | A completion error does not cancel writes or establish quiescence. |

The explicit premise is an exclusive protected transaction window, an initially
quiescent device matching the captured source, atomic 4096-byte persistence, and
flush success only after all previously issued writes are durable. Independent
persistence can precede completion and can follow failure or abort. Every fresh
restart requires device quiescence. These premises need a CortenMM/OSTD and
actual-device implementation proof; Linux disk compatibility does not provide it.

## Recovery and proof scope

Fresh EA bootstrap uses the actual primary, group-zero locator fields and the
entire reserved inode-8 slice. It does not need allocation bitmaps to be
consistent during a partial checkpoint. Other inode slots may change in the
same physical inode-table block; the exact journal-inode slice remains fixed.

Cold recovery scans actual journal bytes and rejects every parsed committed
target-zero write (including revoked or superseded writes). It builds the exact latest unrevoked selected homes and
retired tail, then checks the resulting actual EA namespace and retained
locator identity. Only that checked repaired shadow can receive the sealed
recovery wrapper. Successful wrapper execution refines that exact image.

The sufficient raw recovery profile separately requires the actual EA header,
scan-budget admission, an active journal's durable recovery marker, and absence
of primary targets in every committed recognized stream. The writer-cut
profile proof covers finite writer traces, including errors, abort and late
persistence. The raw constructor's failure contract then rules out rejection
for those inputs. This does not prove that the full namespace validator accepts
every repaired shadow.

[EA admission completeness](EA_ADMISSION_COMPLETENESS.md) supplies exact
header/group/index and allocated-slot read contracts and complete-index
count/parent/topology acceptance.
It also corrects empty non-journal reserved-slot admission without weakening
the journal-inode parser or granting live-inode authority.
Complete census/allocation/directory and top-level namespace-validator
acceptance are still needed before this becomes universal repaired-shadow
admission.

Universal fresh EA bootstrap, raw-constructor and admission closure across
arbitrary repeated recovery crashes remains open. The recovery image theorems
cover an already admitted recovery engine, its successful exact final image and
a finite successful execution witness. Native repeated-recovery examples are
additional evidence.

| Design obligation | Implementation and proof target | Open boundary |
| --- | --- | --- |
| J-ACK / C-COMMIT | Exact durable descriptor/payload/commit bytes after the reported commit flush; typed operation retained | Physical completion authority and caller-visible fsync integration |
| C-CHECKPOINT / D-ORDER | Commit before homes, home flush before tail, exact final bytes | Multiple EA transactions, circular reuse and concurrent checkpoint lanes |
| J-BOOT | Actual EA header/checksum, fixed raw locator at every modeled writer cut | Device capture and kernel volume identity |
| J-RECOVERY | Actual scanner, raw construction under the writer-cut sufficient profile, complete before-or-after homes and acknowledgment implies after under the model | Unconditional full EA validator success/completeness and universal repeated EA restart/admission closure |
| S-RACE | Affine owned requests, immutable borrowed command bytes, late persistence after abort retained | Kernel locking, callback generations, DMA quiescence and competing writers |
| D-ATOMIC | Atomic-block and flush refinement in the specified model | Actual hardware and OSTD adapter refinement |
| Namespace | Exact checked prepared patches and full before/after shadow admission | Allocation/create/final unlink/replacing directory rename, mounted permission/fsync semantics |

Native examples exercise Linux journal-only recovery before comparing exact
home bytes and running a separate read-only filesystem check. They supplement
formal verification and do not prove universal filesystem admission completeness.

## Linux reference

The pinned Linux v7.0 reference is recorded in sources.json. JBD2 commit.c waits
for payload/control I/O and, for non-async commits with barriers, uses
REQ_PREFLUSH | REQ_FUA on the commit record. This implementation uses separate
log and commit flushes. checkpoint.c flushes checkpointed homes before updating
the tail. recovery.c scans, processes revokes, replays, synchronizes and flushes;
escaped payload checksums cover the stored bytes before restoring JBD2_MAGIC.
No Linux defect is asserted.

The implementation is new safe Rust above the framekernel boundary. Future
kernel integration must use CortenMM/OSTD frame ownership and reader/writer/BIO
loans. Linux page, folio and buffer_head ownership is not imported.

## Validation

The pinned unfiltered Verus run checks **3122 obligations with zero
errors** and compiles the host library. Its complete manifest includes
226 sources, 900 named proofs and 774
public executable functions. Both complete native suites pass:
302 metadata plus 62 journal tests. All
330 API rejection cases, six verifier rejection gates and the separate
timeout regression pass.

Six new native tests cover the four prepared families across four source
profiles, selected writer request cuts with failure/abort/late persistence,
repeated cold recovery examples, exact Linux journal-only replay, primary-target
rejection and the legacy clean-only namespace boundary. Native examples
supplement the proofs; the open boundaries above remain open.

The first full attempt found a solver resource limit in the existing reserved
window shape induction. Three private helper proofs replace its broad context;
the public contract, decreases and per-function limit remain unchanged. The
fresh full run supplies the positive evidence. Failed and focused diagnostic
attempts are retained separately and do not count as full proof evidence.
