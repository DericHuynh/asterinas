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
the absence of old-generation requests, global replay authorization or actual device behavior. A device with only 512-byte addressing has not met this contract.

Every returned scan includes a source-bound contiguous record certificate,
all descriptor payloads, the last committed cut and a stopping witness.
The maximal canonical record prefix and committed input are proved unique.
The scan has checked total acceptance for the sufficient resource profile in
`scan_budget.rs`. Every writer crash snapshot meets that profile, even when
only part of the log has persisted. Recovery preparation also has a checked sufficient profile, and every legal
writer crash snapshot satisfies it. Actual scan selection plus modeled successful
recovery has complete before/after nonjournal home bytes outside block zero.
Block zero has a separate preserved-identity and replay-policy proof. These
results do not establish global replay authorization. Repeated recovery admission
is checked after every modeled crash cut and arbitrary finite sequences of
attempts; an uncleared journal has the same committed input. Retirement stores the scan
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
log durability, without CRC injectivity. Serialized physical writer generations
compose over their actual durable maps; the final recovery includes every
acknowledged generation. The runtime gate, filesystem operation authority and
actual device adapter remain open. A crash discards volatile cache and a new
attempt requires quiescent-start device semantics; abort does not imply them.
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

The initialized bitmap and block-claim census components validate allocation
bits, free counters, padding and checksum inputs. Accepted inode claims bind
physical slots to their actual extent bytes, inode generation and sector count;
journal inode 8 is reserved separately. Claim rejection preserves the original
census, and successful additions preserve previously occupied slots. These
components do not enumerate an entire volume or authenticate caller ownership.
The census is bounded to 1,048,576 blocks; successful allocation still uses the
stated host allocator foundation. Kernel memory must use fallible CortenMM/OSTD
reservation before accepting a volume or transaction.

The borrowed `snapshot.rs` source prevents host Rust mutation while its bytes are
borrowed. `group_metadata.rs` reads each descriptor and initialized bitmap at its declared
address, or derives the appropriate canonical bitmap under checked UNINIT flags, and `group_index.rs` retains that same source while checking every group
and summing free counters. Ghost byte provenance does not use CRC injectivity.
Sparse-super/GDT reservations match the Linux power rule within the 32-group
resource profile. The allocation builder now also enumerates every allocated inode and proves
complete bitmap/counter agreement. Static namespace validation now composes the source certificate. The borrowed host image is not an OSTD frame/DMA loan,
a device snapshot, or permission to validate unrecovered partial checkpoints.

`allocation.rs` produces a whole-image allocation certificate for the bounded
logical-group subset. It checks all reserved regions and allocated inode
claims against the same immutable source, including inode-bitmap markers, unused
reserved inode storage, directory counts and declared unused inode-table tails.
Every logical block-bitmap bit matches exactly the disjoint source-derived census;
BLOCK_UNINIT selects proved reserved-metadata/padding bits, and initialized groups
retain their physical bitmap relation. The aggregate free total equals the
primary superblock. This does not certify namespace/link
consistency, VFS access, journal cleanliness, recovery or mount admission. Global
allocation validation belongs after recovery or over a validated shadow image;
bootstrap journal discovery and operation preservation of its static inode/table
mapping remain separate obligations. No actual frame or device authority is
created by the host certificate.

`allocated_inode.rs` derives ordinary inode metadata/physical claims from the
whole-image certificate. `file_read.rs` proves unique initialized mappings and
exact file-size/block-clipped host slices or zero spans for holes/unwritten
extents. These helpers do not accept or create credentials, open rights or VFS
capabilities; kernel ingress must add those proofs. `directory_block.rs` checks
complete canonical record coverage, including deleted records, and proves the
complete stream unique. The directory-file layer now binds its checksum seed/source to the actual
allocated directory; the namespace layer now composes target/link/topology checks.

`directory_source.rs` defines canonical directory source bytes and records with
guarded logical choices. Executable initialized mappings and complete record
chains witness existence; their checked uniqueness proves the returned records
equal that source function. No unproved selection or checksum-identity premise
is introduced. `name_set.rs` uses the checked CRC only to select a bounded
bucket, then compares complete directory/name keys. It owns copied name bytes
and preserves its original state on rejection. Collision/total caps are explicit
resource limits; the helper does not certify that its inode numbers are live or
that a namespace is complete, authorized, rooted or link-count consistent.

`directory_index.rs` composes the canonical source functions into complete
enumeration of every allocated directory and every block up to its block-aligned
i_size, including empty preallocation. All live records contribute exact owned
entries, whose source directory and target type/generation are checked. Name-set
ordinals are proved to identify their insertion position; lookup returns exactly
the corresponding source entry and absence excludes every canonical name match.
The index is bounded to 4096 directory blocks and 65536 names. The namespace
layer adds dot/parent relations, link counts and rooted topology; operation and
recovery/mount admission remain separate. These host structures remain outside VFS/credential/device authority.

`namespace.rs` composes exact source entry accounting with checked inode link
counts, Linux canonical dot/dotdot placement/targets, unique ordinary directory
parents and matching dotdot, and a bounded parent-graph walk. Integer depth ranks
prove every accepted directory reaches root. The executable uses color/depth
arrays and bounded cursor walks; path sequences are ghost proof certificates,
not a runtime stack. Regular-file hard links are permitted, while directory
hard links, orphaned live files and disconnected cycles are rejected. This
certifies one immutable selected image. Recovery/boot selection, actual mount
admission, operation preservation, credentials/handles and CortenMM/OSTD/device
refinement are still required; the namespace object does not confer those rights.

## User-xattr transaction boundary

The xattr lifecycle is a bounded host operation. Only `user.*` mutation consumes
the current ACL write grant; generic owned-store/packing helpers grant no I/O or
privileged namespace authority. Sticky-directory owner checks conservatively
exclude the unmodelled CAP_FOWNER exception. The complete proposed attribute set,
allocation/reference census and final namespace are validated before dispatch.
Byte authority excludes neighboring inodes, unrelated metadata and shared value
bytes. EXT_ATTR is the sole newly variable compatible feature under bootstrap/
recovery identity, and this builder only enables it. Other format features retain
their existing policy.

All-home crash closure is conditional on the existing protected-source, 4-KiB
atomic-write, draining-flush and quiescent restart contract. It establishes no
physical device behavior, concurrent inode/xattr/cache lock, allocator epoch or
CortenMM frame/DMA ownership. Kernel/full-feature/mount gates remain closed.

## ACL mutation authority

ACL mutation consumes a separate, source/kind-bound private authorization object.
Ordinary ACL/DAC write grants cannot substitute for it. Actual mutations require
the owner or the supplied scoped FOWNER decision; FSETID only controls SGID
retention. Default removal on a regular file may succeed without owner authority
and produces no mutation. The operation binds access ACL content, resulting mode
and allocation metadata to the same transaction and commit decision.

Filesystem IDs, group membership and FOWNER/FSETID scope remain authenticated VFS
inputs. LSM decisions, ID translation, runtime ACL-cache coherence, locks and
CortenMM/OSTD/device refinement remain open. The common storage constructor is
crate-private and grants no standalone public filesystem write authority.

The separate `acl_chmod` factory also consumes exact-source owner/scoped FOWNER
authority. It accepts requested permission/special bits through `07777`, preserves
file type, and clears requested SGID without owning-group membership or scoped
FSETID. FSETID supplies no ownership authority. Its full-mode byte codec is
separate from the existing ACL-set codec, whose contract still forbids adding
set-ID bits and preserves setuid/sticky. The shared storage builder records which
mode policy applies. A public raw codec result grants no filesystem mutation
right; only the operation-specific candidate reaches sealed writer admission.

Chmod's unchanged-logical-value storage path records retention separately from
rebuilt canonical output. Retention is unavailable to the existing user-xattr
and ACL-set factories. Its proof boundary preserves the source attribute bytes
and pointer, restricts the transaction to one inode-table home image and excludes
every external attribute block from writes. Valid source hints such as a zero
external `h_hash` remain byte-exact rather than being rewritten or rejected by a
canonical-encoder condition. Complete result allocation, namespace and logical
value checks remain mandatory. This is not permission to skip validation of
newly generated attribute storage.

`acl_inherit::Plan` binds an immutable parent directory and its source default
ACL to proposed child mode/access/default bytes. Private construction protects
that correspondence; the object authenticates no caller, selects no child inode
and exposes no I/O method. Its broader Linux file-type planning does not widen
whole-image inode admission. A plan computed from a READONLY parent remains a
read-only result. Allocator authority, an exclusive unpublished child, link-count
and directory publication, parent/child locking, runtime cache coherence and
atomic journal closure must be supplied by a future child-creation operation.
The byte-level inheritance contracts cannot stand in for those boundaries.

Inheritance subject-access monotonicity evaluates the transformed ACL and source
default ACL with the same numeric owner, owning-group, subject and group-set
inputs. It does not prove any child-to-parent ownership relation or compare the
child against the parent's access ACL. Reverse version-2 ACL reporting similarly
preserves supplied numeric named IDs and reports INVALID_ID for special entries;
mount/user-namespace translation and authenticated userspace ID reporting remain
VFS obligations.

## Isolated EA_INODE core

`ea_source::Header` retains actual source features and geometry, requires the
superblock clean-state marker and RECOVER clear, and proves initialized allocated
inode-table provenance. These markers do not establish whole-filesystem or
journal admission. It is a separate type; the implementation does not strip
EA_INODE to manufacture an ordinary `GroupIndex` or widen full admission.

The private `ea_reference` and `ea_value` objects bind a complete parent xattr key,
descriptor, allocated live value inode, initialized mappings and returned bytes
to that same source. Dense mappings, distinct physical value blocks and complete
CRC/entry-hash checks do not prove global metadata/data separation, absence of
extra extents beyond EOF, full sector accounting, quota limits or authenticated
VFS access. The modern reader excludes Linux's legacy Lustre classification;
it does not implement that alternative lifetime protocol. Immutable host results
grant no device requests, filesystem mutation or CortenMM/OSTD ownership.

`ea_inode::Status::Unlinked` means only zero local references/links under the
codec's zero-dtime profile. It does not prove orphan membership or reclamation.
Reference-word edits return byte images with no caller authority, I/O or
durability certificate. `ea_refs` physical and per-parent ledgers validate only
caller-supplied structural records; they are not complete authenticated source
censuses and cannot alone justify stored refcounts or quota changes.
Full EA_INODE admission, lifetime, quota, concurrency and journal/device
refinement remain required. Kernel/full-feature/writable-mount gates remain false.

## Source-bound EA reference census

`ea_census` composes the actual-feature complete group index, logical lazy bitmap
semantics and every-inode classification with complete parent EA projections.
A successful result requires the supplied scan budget to cover all declared
inodes; no partial prefix becomes a positive certificate. All allocated EA values
must be live, every physical descriptor must target an allocated exact-size value,
and stored EA counts equal the complete physical graph indegrees. Every logical
parent binding separately excludes the bounded legacy Lustre classification.
Each logical binding checks its exact source-selected entry name and target's
stored value-hash word against the entry hash, accepting the unsigned or
historical signed-name variant. The stored word is not assumed to equal a CRC
of unread payload bytes; full value-content and physical-sector audits remain
separate.
Every ordinary external parent pointer contributes to its block's `h_refcount`,
including pointers to blocks containing only local values.

The group index checks pairwise inode-table block-range separation before
construction and binds source-node membership to those ranges. Distinct inode
numbers consequently retain disjoint source byte slots. The census rejects all
external xattr pointers into any inode-table block, preserving the inline versus
external physical-entry distinction even with FLEX_BG placement. This does not
establish separation from GDT/bitmap/journal roles or data extents; global physical
ownership remains a separate admission boundary.

This is the source-bound layer missing from bare `ea_refs`/graph helpers;
arbitrary caller-supplied ledgers do not gain its certificate. The graph/census
still authenticates no physical device, caller or VFS handle. The header requires
RECOVER clear and unsupported orphan-work markers absent; allocated zero-ref EA values are
rejected, and reserved body tables must parse and be absent. Those constraints
do not supply a journal, namespace or orphan-lifetime proof.

The parent `i_blocks` split includes every logical EA charge and one external
block charge even when sharing or disabled quotas affect no physical allocation.
Its `own` residual is arithmetic, not ownership. Complete physical separation,
value content/CRC validation for every target, sector/EOF closure, quota database
persistence, authenticated lifecycle edits and CortenMM/OSTD lock/cache/device
refinement remain open. Full filesystem admission and mount/writer gates remain
closed. See [EA reference census](EA_REFERENCE_CENSUS.md). The separate value
integrity composition below supplies bounded payload/EA-sector closure; this
reference census alone still establishes metadata relations only.


## Source-bound EA value integrity

The private integrity result retains one original-source reference census and
one complete payload/storage result for every census EA inode. Explicit physical
record coverage and unique value inode identities prevent a partial or unrelated
value list from standing in for complete inspection. Same source header and inode
number determine one exact node; payload metadata and logical bindings therefore
refer to the same retained inode bytes, without a CRC identity premise.

Complete source tree claims include all external extent nodes and every data
extent. A shared physical ledger rejects within/across-value aliases and retains
exact initialized map roles. Dense data-extent coverage and full source-byte CRCs
are checked separately from structural tree validity. Extra data allocations past
the rounded EOF reject the profile. Complete EA sectors include metadata blocks;
parent logical charges remain a separate quantity. Accepted empty metadata leaves
are still counted; no minimal/canonical extent-tree representation is inferred.

Every claimed EA block must be set in the actual group's logical allocation
bitmap and excluded from source-selected superblock/GDT backups, all bitmap and
inode-table blocks and every external-xattr block. These checks do not enumerate
ordinary-file/directory or journal data owners, or prove all allocated bits have
a unique global owner. Full EA filesystem admission and every mount/write gate
remain closed.

The aggregate byte budget bounds declared/retained payload lengths. Host Vec
capacity, transient buffers and allocation success are not consequences of that
bound. Final partial-block bytes beyond the value length are not returned or
hashed; future publication/reuse requires an initialization and tail-zeroing
protocol. Immutable host inspection grants no VFS credentials, allocation,
refcount/quota/orphan edit, lock, BIO, DMA or device authority. Runtime refinement
must use Asterinas's CortenMM/OSTD framekernel interfaces. See
[EA value integrity](EA_VALUE_INTEGRITY.md).

## EA-enabled whole-volume physical ownership

The separate EA allocation certificate retains the complete original-source EA
integrity result and extends an exact owned duplicate of its claim ledger.
Every declared source inode slot has an explicit class. The ordinary catalogue
is exactly the projection of that source scan; caller-supplied or partial lists
cannot justify used-directory counters or global ownership. Empty reserved slots
contribute no hidden storage, and supported allocated EA slots resolve to retained
checked values. Source feature masks are retained throughout.

The final exact claim sequence includes all EA allocations, source-selected fixed
metadata, inode 8's supported journal extent, every ordinary file/directory extent
tree and one claim per distinct external xattr block. Later appends preserve every
prior occupied slot. Repeated external pointers skip only addresses already in
the preceding source pointer catalogue; an arbitrary existing role-7 slot does
not authorize sharing. Complete ordinary parent residual sectors equal actual
owned extent blocks; logical EA charges are never counted as duplicate physical
allocation.

Both directions of every logical block bitmap are compared against final occupied
roles, with exact group directory counts and global free counts. Thus claimed-free
and allocated-but-unowned storage reject this bounded result. This does not prove
directory record contents, links, rootedness or HTree correctness, nor the mapped
journal's JBD2 header/UUID/state, emptiness or actual recovery admission. An image
with invalid namespace or journal bytes can still satisfy allocation ownership.

Host-owned candidate duplication and immutable observations grant no allocation,
credential, mutation, lock, BIO or persistence authority. Full filesystem EA
admission, every kernel/full-feature/writable-mount gate and durable EA lifecycle
remain closed. Future runtime execution must refine CortenMM/OSTD framekernel
ownership and device contracts. See [EA allocation](EA_ALLOCATION.md).
