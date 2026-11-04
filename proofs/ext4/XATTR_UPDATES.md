<!-- SPDX-License-Identifier: MPL-2.0 -->

# Journalled inode-body user-attribute replacement

`xattr_update::prepare` consumes an actual source-bound ACL/DAC write grant and
constructs one inode-table after-image for an existing `user.*` value. The
current operation accepts regular files, a nonempty byte-name suffix, a
nonempty replacement of exactly the existing length, and an isolated local
inode-body value. It rejects READONLY sources, no-op replacements, nonzero
inline entry hashes, unsupported storage, invalid timestamps and exhausted
ordinary-inode version counters. `None` reports that no candidate was prepared;
it is not a POSIX errno interface.

This implements a bounded host transaction operation. It does not implement
attribute creation/removal, value resizing, external-block mutation, shared
block copy-on-write, EA_INODE, quotas, ACL/security-namespace mutation, a mounted
setxattr syscall or CortenMM/OSTD execution.

| Design obligation | Implemented and checked | Remaining boundary |
| --- | --- | --- |
| S-AUTH / S-ENTRY | Consumed source-bound request-2 grant; regular-file and fixed user-namespace checks; the ACL certificate and new complete body parse agree on every record | VFS caller authentication, idmaps, LSM and mount/open-handle policy |
| F-CODEC | Same-size local replacement, zero padding, unchanged entry/name metadata, ctime-only update, exact ordinary-inode version increment and inode checksum reseal | Other storage/size changes and format geometries |
| F-OPS | Recovered or completed inode contains the exact requested value; every other inline attribute, mtime, identity, extents, external pointer and unrelated inode byte is retained | Complete operation/admission acceptance without final validation and broader POSIX semantics |
| F-OWN | One source-selected kind-3 inode-table home; all data, directory, extent and external-xattr blocks retain their exact source bytes; neighboring inodes in the same table block are framed | Allocation, external-block mutation/COW and runtime ownership |
| F-CREDITS | One owned after-image is staged, closed and frozen under the existing bounded reservation API before complete writer admission | Fallible memory/resource reservation and multi-operation closure |
| J-ACK | Successful physical-model completion equals the completely validated final filesystem image and exact replacement inode | Actual hardware, BIO and flush refinement |
| J-CUT / J-RESTART | Every modeled writer cut followed by a returned certified scan and successful recovery yields the complete old inode or complete updated inode, selected by persisted commit, including value/time/version/checksum together | Full recovery admission completeness, other device atomicity and runtime restart/capture |
| S-RACE / S-LOCK | Immutable source borrows and private affine grants/candidates prevent source replacement, mutation of prepared images and reuse after begin | Actual xattr/inode locks, concurrent operation freshness, callbacks and CortenMM/OSTD guards |

The input table is complete and terminated. A separate induction proves that
two valid complete parses of the same bytes have identical entries and end
offsets. The operation uses that result to bind its selected record to the same
inode-body table used for ACL authorization.

Read-only xattr tables can contain overlapping local values. That does not
grant independent mutable ownership. The mutation check compares the selected
padded value span against every other local nonempty value, across all
namespaces. It rejects aliases before preparing an image. The framing theorem
therefore preserves other values, including access ACLs and security attributes,
without assuming hashes or checksums are injective.

Linux's ordinary VFS version counter reserves one internal bit for its queried
marker. The disk fields are decoded as low/high words, but this operation only
increments observable versions below `2^63 - 1`; reaching the limit prevents
another update. It rejects larger raw values as well. This bounded policy avoids
wrap/reuse and does not apply EA-inode reference-count semantics to ordinary
files. The inode-body entry hash stays zero, as in Linux's non-EA inline update
path. Replacement padding is cleared.

The generated table-block image splices the exact 256-byte sealed inode into
the retained snapshot. The existing writer factory checks the complete initial
and dirty/log/home/retirement result images plus bootstrap identity before
returning an I/O-capable host object. The new durability and crash theorems
compose with the actual scanner, selected replay, and byte-valued writer and
recovery models. A persisted commit may recover the new value even if no public
success was returned. Their existing exclusive-source, quiescent restart,
atomic-4-KiB-write and flush contracts remain explicit; these are not hardware
or mounted-filesystem proofs.

Native tests use Linux-created compact ACLs, inline user values and external
attributes. A named ACL user performs the operation despite no OTHER write
permission. Tests check exact new value, unchanged ACL/external blocks/data,
mtime framing, ctime/version, zero padding, version carry and exhaustion,
READONLY, wrong grant, missing key, no-op and size rejection. A valid immutable
image with an inline user value aliased onto the access ACL is rejected for
mutation. Both precommit and committed-precheckpoint snapshots are recovered
through the actual host recovery engine; Linux e2fsck also recovers the committed
journal and validates the resulting value. Rust negative cases cover forged or
redirected candidates, reused grants/candidates and mutable image access.

Pinned references in `sources.json` cover Linux `xattr_permission`,
`ext4_xattr_set_entry`, `ext4_xattr_ibody_set`, ctime/version dirtying,
`ext4_inode_peek_iversion`, inode version serialization, and the VFS queried-bit
representation. No Linux page, folio or buffer-head ownership is imported.
Kernel/full-feature/mount gates remain false.
