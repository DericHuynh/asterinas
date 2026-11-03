<!-- SPDX-License-Identifier: MPL-2.0 -->

# Trust boundary and required adapters

Status: explicit foundation and contracts; concrete kernel adapters remain unproved.

## Trusted foundation

The final claim will be conditional on a reviewed foundation: the pinned Verus
and vstd semantics/axioms, SMT soundness, Rust compiler/code generation and
erasure, vstd resource-algebra ghost ownership, the machine model, and explicit
hardware/device assumptions. The verified runner itself, installer and test
harness are ordinary trusted build/validation tools, not Verus-proved code.

OSTD/CortenMM, VFS authorization, block drivers, and DMA routines are not
automatically proved by proving this package. Either import an existing checked
proof matching the exact API/version, prove the adapter/implementation, or list
the remaining trust explicitly. Do not hide an entire filesystem in a trusted
wrapper.

The core may not use assume/admit, external bodies, unverified helper calls,
selective verifier filters, or unchecked aliases to bypass a failed proof.
The local checker enforces a narrow gate, but is not a proof that the verifier
itself or vstd is sound.

## Persistence-device contract

A future PersistDevice adapter must establish:

| Contract | Required meaning |
| --- | --- |
| Addressing | Every submitted atomic-unit range lies in the chosen partition; checked conversions preserve it. |
| WriteSnapshot | The submitted bytes equal the specified immutable after-image while DMA may read them. |
| Completion | Distinguish queue acceptance, I/O completion, and persistence; document every status. |
| FlushFence | On successful completion, all required earlier writes in the same persistence domain are durable. |
| Atomicity | State the power-loss failure-atomic unit; 512-byte addressing is not sufficient evidence. |
| Errors | An error does not imply no effect or cancellation; no new success acknowledgement after abort. |
| Quiescence | Old-generation I/O cannot later modify a reused log/home region or a freed/reused frame. |
| Ordering | Queue merging/reordering preserves the fence contract and dependency graph. |
| Reset/recovery | Bind device reset, cache loss, pending writes, and mount generation to the crash model. |

Asterinas exposes BioType::Flush and NotSupported, but BlockDeviceMeta presently
has no formal power-loss atomicity or persistence-domain capability. Existing
BIO ownership is useful; IoBatch completion alone does not discharge FlushFence.

Use write + successful explicit flush for the conservative profile. Adding FUA,
combined PREFLUSH/FUA, or eliminating fences requires an equivalence proof.
Unsupported flush, uncertain completion, timeout, or a device contract that
cannot be established must not result in a successful durable acknowledgement.

## Frame and DMA contract

Use OSTD frame handles, typed/untyped memory separation, VmReader/VmWriter, and
the existing ownership transfer into SubmittedBio. Never manufacture a Linux
page reference or a mutable Rust slice to untyped frame memory.

A cloneable BioSegment is not by itself a unique immutable snapshot.
The bridge must maintain tracked ownership/loan state: private initialized
after-image -> frozen device-readable loan -> completion/quiescence -> reuse.
No kernel or user alias may mutate the frozen bytes. DMA cache coherence and
completion callbacks are part of the proof boundary.

User buffers can change while copied; the operation input is the owned bytes
actually captured, not an assumed atomic snapshot of an arbitrarily mutable
user buffer. Once captured for the journal they remain immutable.

## Locks and capabilities

Model the operation gate with Verus tracked permissions and then prove that an
actual OSTD lock acquisition yields exactly the matching live capability.
A pure integer actor/generation predicate alone is not an unforgeable capability.
lease.rs models that predicate. gate.rs adds an affine capability backed by
vstd's exclusive resource algebra and proves uniqueness and stale-generation
rejection. It still does not establish an actual OSTD mutex acquisition.

Audit entry paths from VFS/dentry/inode locks before fixing the global hierarchy.
Include error paths, callbacks, eviction, unmount, reset, cancellation, and
crash/recovery. Do not hold a spinlock across I/O or wait for a callback while
holding a lock the callback needs.

Capability creation/destruction and FFI or unverified callers need verified
entry precondition enforcement. A successful proof of a function's body does
not establish that unverified callers meet its requires clauses.

## Security claim limits

For a well-formed initial filesystem and the stated crash model, prove that
authorized operations preserve ownership, namespace, initialization, and the
durable history. For arbitrary supplied media, separately prove parser/resource
safety, partition confinement, and rejection/validation before mount.

A malicious disk can forge ownership and CRCs. This design does not authenticate
historical file contents, defeat rollback by a hostile drive, prove physical
secure erasure, or eliminate hardware timing side channels. Mount nosuid/nodev
and any namespace/credential mapping must have a real VFS contract; they are
not consequences of the ext4 format.

## Current executable boundary

The core is compiled by the pinned verifier into a host Rust library and exercised
by a separate unverified interoperability harness.
There are no local assumptions, admitted lemmas, trusted function bodies,
trusted generated token APIs, or calls to a handwritten unverified core helper.
All public executable functions perform their own checks and have no `requires` clauses.
Private fields and Verus checked type invariants preserve replay-plan and
recovery-state validity across public method calls; no trusted invariant wrapper
is used. Completion reports are untrusted adapter inputs at this host boundary:
the protocol checks ordering and request IDs but cannot establish that a caller
really dispatched a BIO or that a reported flush was physically effective.

`recovery_device.rs` states a 4096-byte failure-atomic persistence model explicitly.
It allows a cached write to persist before its completion and after abort,
requires home flush before retirement, and proves each allowed event preserves
the recovery invariant. Its success image equals the byte-valued Linux redo
result plus the retired tail. This theorem does not establish device atomicity,
the absence of old-generation requests, repeated recovery admission/closure or global replay authorization. A device with only 512-byte addressing has not met this contract.

Every returned scan includes a source-bound contiguous record certificate,
all descriptor payloads, the last committed cut and a stopping witness.
The maximal canonical record prefix and committed input are proved unique.
The scan has checked total acceptance for the sufficient resource profile in
`scan_budget.rs`. Every writer crash snapshot meets that profile, even when
only part of the log has persisted. Recovery preparation also has a checked sufficient profile, and every legal
writer crash snapshot satisfies it. Actual scan selection plus modeled successful
recovery has complete before/after nonjournal home bytes outside block zero.
Block zero has a separate preserved-identity and replay-policy proof. These
results do not establish global replay authorization or repeated recovery admission. Retirement stores the scan
next-sequence value without allocating a new epoch, so terminal-ID recovery
remains possible; future writer admission still refuses wraparound.

Every emitted recovery image is checked to fit its partition, and the scan
certificate is preserved across completion and abort. The public I/O boundary transfers the entire recovery machine into a private,
non-Clone `Pending` request. Completion consumes this request and returns its
own machine, including after abort. Rust privacy and ownership reject forged
requests, duplicate completion and retargeting through the internal numeric-ID
method. This does not supply the kernel gate, actual callback binding, request
drain, DMA lifetime, or a trustworthy device completion report.

The writer uses the same ownership boundary and validates every emitted write's
4 KiB image and partition range. Its six fences order dirty marking, journal
activation, prepared log, commit, checkpoint and retirement. The command state
machine and its single-transaction byte/persistence simulation are checked under
the stated device contract. Each persistence event inserts exactly its issued
image at its physical address; successful flush has a finite issued-write
refinement. Fresh commit recognition derives from epoch/provenance and prepared
log durability, without CRC injectivity. Multi-transaction physical history and
the actual device adapter remain open.
The device contract applies to each submitted partition-relative 4 KiB span,
including physical alignment. The partition wrapper must establish that relation.

`FrozenBlock` owns initialized Rust bytes and exposes no mutable borrow or Clone.
This proves the host snapshot relationship; it does not prove an OSTD frame loan.
Kernel integration must capture bytes through `VmReader`/`VmWriter` and CortenMM
ownership, account for fallible memory reservation, and relate frozen frames and
DMA callbacks to these checked models.
The existing cloneable BIO segment is not treated as an exclusive snapshot.

The current block-device metadata does not advertise power-loss atomicity,
persistence domains or a formal flush/DMA contract.
A verified adapter cannot infer them from a sector size or a completed BIO.
The driver/OSTD contracts and their implementation refinements must be supplied
before a writable mount can be enabled.

The Rust standard library/allocator and their pinned vstd specifications are part
of the host-core foundation. The snapshot's allocating loops have checked bounds;
this does not prove successful allocation under arbitrary memory pressure.
The kernel adapter must provide fallible reservation and OSTD memory semantics.
The DAC core takes the filesystem UID and already mapped owner/group/capability
facts; it does not implement credential authentication, idmapped mounts or LSMs.
