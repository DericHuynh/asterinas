<!-- SPDX-License-Identifier: MPL-2.0 -->

# Journalled user-xattr lifecycle

`xattr_lifecycle::set_user` and `remove_user` consume a source-bound ACL/DAC
write grant and build a complete candidate transaction for the admitted Linux
ext4 profile. They implement creation, replacement, removal, empty values,
resizing, inline/external movement, exclusive block reuse, shared-block
copy-on-write, reference release and allocation accounting. An unchanged set
returns `Ok(None)` after validating flags; it does not start a transaction.
Errors leave the immutable source untouched and expose no I/O command.

The executable operation fixes the namespace to `user.*`, requires a nonempty
suffix, admits regular files and directories, and restricts sticky-directory
writes to the owner. The current credential model has no CAP_FOWNER input, so
its privileged sticky-directory exception is conservatively unavailable.
A grant for another inode, source or access request cannot be substituted.
The generic owned store and table packer preserve complete keys and local
values with nonzero namespace indices. Unsupported entries or exhausted bounds
reject construction; these helpers confer no privileged-namespace authority.

| Design obligation | Implemented and checked | Remaining boundary |
| --- | --- | --- |
| S-AUTH / S-ENTRY | Consumed exact-source request-2 ACL grant, user namespace, regular/directory/sticky checks, READONLY exclusion, complete parse agreement | Authenticated VFS caller/groups/idmaps, CAP_FOWNER exception, LSM and trusted/security namespace policy; ACL set/chmod use separate authorities in POSIX_ACL.md |
| F-CODEC | Complete-key CREATE/REPLACE/remove semantics, empty values, zero-padded repacking, unsigned Linux entry/block hashes, sorted external tables, physical-address CRC, inode pointer and ctime/version/checksum reseal | EA_INODE, wider admitted inode/block formats and feature combinations |
| F-OPS | Returned image decodes to exactly the intended set; every other complete key/value is retained; full combined allocation and final namespace checks precede dispatch | Completeness of successful packing/admission and broader POSIX operations |
| F-OWN | Census-selected free blocks, exclusive reuse, shared COW/decrement, single-block bitmap/counter accounting, neighboring-inode and shared-value byte authority checks | Runtime allocator/cache locks, quotas, frame epochs and DMA exclusion |
| F-CREDITS | Up to six coalesced, sorted, complete after-images are reserved, staged, closed and frozen together | Fallible memory reservation and concurrent multi-operation closure |
| J-ACK | Every home image, including primary counters/feature promotion, is exact on successful durable completion; journal retirement follows durable homes | Physical BIO, flush and device refinement |
| J-CUT / J-RESTART | Every modeled writer cut and successful certified recovery uses one persisted-commit decision for the complete patch set; before commit the primary retains old counters/features with only recovery marking permitted | Full recovery admission completeness and actual quiescent restart/capture |
| S-RACE / S-LOCK | Private affine grants/candidates and immutable snapshot borrows prevent source replacement, prepared-image mutation and reuse after begin | Kernel inode/xattr/allocation locks and concurrent operation freshness |

`xattr_store.rs` owns independent namespace/name/value bytes. Failed CREATE,
REPLACE, key/size/flag checks and removal return the unchanged store. As in
Linux ext4, CREATE|REPLACE reports existing-key or missing-key failure after
lookup. A zero-length value is an existing attribute, distinct from absence.
All equality decisions compare complete bytes; hashes and CRCs establish no
identity or authentication assumption.

`xattr_pack.rs` uses bounded subset-sum placement for the 88-byte inline and
4060-byte external payloads. External keys follow Linux's namespace, name-length
and unsigned-name order. New block hashes stop permanently at a zero *entry*
hash; a zero intermediate accumulator alone does not stop hashing. Values are
zero-padded to four-byte boundaries. The builder decodes its complete output
and compares both directions against the intended owned store before returning
an image. `xattr_canonical.rs` additionally checks all generated name/value padding,
every entry hash and the complete block hash. This is a proved checked-output construction; a full Some/None
admission-completeness theorem for the packer is not claimed.

Rebuilding also safely separates aliased values from a read-only input table:
all values are copied before editing, and every unrelated complete key is
checked in the decoded result. Capacity exhaustion rejects the operation before
I/O. The earlier `xattr_update`/`xattr_replace` isolated same-length fast path
remains available independently and continues rejecting aliases.

`xattr_inode_edit.rs` preserves non-xattr sector accounting through the Linux
HUGE_FILE codec. It updates ctime, the ordinary observable disk version and both
inode checksum halves while framing identity, mode, owners, extents, mtime and
all unrelated bytes. Observable versions remain below `2^63`; exhaustion and
invalid timestamps reject construction without writes.

`xattr_block_update.rs` reuses exclusive blocks, allocates only census-free
blocks, and decrements shared references without editing their entries/values.
For chmod with unchanged logical values, the common builder also offers a
retained-storage path: the source pointer/inline bytes remain fixed, exactly one
inode-table home image is prepared, and external blocks are excluded from the
write set. A shared external block needs no copy or reference change. This path
preserves valid Linux source hash hints, including `h_hash == 0`, through exact
source-byte framing. Complete allocation, namespace and value checks still apply;
generated canonical padding/hashes are required only on the rebuild path.
The user-xattr and ACL-set factories cannot select retention and continue to
require canonical rebuilt outputs.
Dropping an exclusive block frees its bit and updates group and primary free
counts. Lazy groups start from their checked canonical logical bitmap, clear
BLOCK_UNINIT and materialize the updated bitmap. Both descriptor widths retain
the correct bitmap checksum halves and group checksum.

`xattr_footprint.rs` checks byte authority against the exact source inode and
allocation census. The combined candidate is then reparsed for complete
allocation, reference counts, pointer/sector consistency, checksums and exact
attribute contents. The sealed writer additionally validates the complete
initial and final allocation/namespace images plus bootstrap identity before
returning an I/O-capable object.

Creating the first attribute journals the EXT_ATTR bit with the inode and any
allocation changes. General primary/recovery identity permits variation only
in that compatible bit; unrelated compatible features remain fixed. The xattr
builder only enables it, never clears it. Incompatible format bits, UUID,
geometry and journal identity remain fixed under the existing recovery policy.

`xattr_durable.rs` composes the actual scanner, selected redo, byte-valued writer
and recovery models for all home images together. A persisted commit can recover
the new state even without a returned success. The primary's precommit recovery
marker does not publish new allocation counters or EXT_ATTR. These proofs retain
the explicit exclusive protected source window, matching quiescent initial
snapshot, atomic 4-KiB writes, draining flush and quiescent restart contracts.
An abort by itself does not establish quiescence.

Native tests exercise Linux-created ACL/inline/external/shared images, flag
precedence, missing versus empty values, exact two-area capacity, hashes,
resizing/reuse/freeing/COW, peer preservation, first-feature promotion, failures,
and recovered writer cuts. Linux e2fsck independently replays committed journals
and validates resulting allocation and xattrs. Negative Rust compilation checks
reject forged stores/packed images/candidates, redirection, mutation and grant
or candidate reuse. Tests supplement the formal checks.

This remains a bounded host implementation. EA_INODE value lifetimes, quota
coupling, trusted/security namespace changes, atomic child creation with inherited
ACLs, deduplication into an existing block,
a mounted syscall and kernel concurrency are unfinished. A functioning full ext4
filesystem is not claimed. Kernel/full-feature/mount gates remain false.
Future kernel execution must use the CortenMM/OSTD ownership, sleeping-lock and
BIO/DMA interfaces of Asterinas's framekernel architecture. Linux page, folio and
buffer-head ownership is not imported. Pinned references are in `sources.json`.

The separate [EA_INODE core](EA_INODE.md) now provides isolated metadata,
source-bound value inspection and structural reference/quota contracts. It does
not extend this lifecycle's ordinary filesystem admission, value allocation,
orphan handling or journalled update support.
The [source EA reference census](EA_REFERENCE_CENSUS.md) separately binds complete
parent descriptors, physical counts, logical billing and external sharing to the
actual metadata; global ownership and this lifecycle's EA mutation admission
remain unfinished.


Access/default ACL updates are implemented separately in [POSIX_ACL.md](POSIX_ACL.md).
They use owner/scoped FOWNER authority and couple permissions/SGID to storage.
ACL chmod additionally transforms the access ACL and requested special permission
bits through a distinct source-bound authority. The existing ACL-set codec keeps
its restriction against adding set-ID bits. Inheritance currently produces only
an immutable parent-bound plan; it does not allocate or publish a child inode.
`xattr_transaction.rs` now provides the crate-private common storage builder;
`xattr_commit.rs` provides common all-home commit/recovery closure.
The public user-namespace policy and exact-mode preservation remain unchanged.
