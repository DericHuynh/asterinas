<!-- SPDX-License-Identifier: MPL-2.0 -->

# Trust boundary and required adapters

Status: contracts to discharge, not verified adapters.

## Trusted foundation

The final claim will be conditional on a reviewed foundation: the pinned Verus
and vstd semantics/axioms, SMT soundness, Rust compiler/code generation and
erasure, the machine model, and explicit hardware/device assumptions.

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
The current lease.rs only models that predicate.

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
