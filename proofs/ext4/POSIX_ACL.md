<!-- SPDX-License-Identifier: MPL-2.0 -->

# Source-bound POSIX ACL decisions and updates

The host profile decodes Linux ext4 compact version-1 ACL values, evaluates
permission requests and connects successful source-bound decisions to the
initialized-file content/time writer and the user-xattr lifecycle in
[XATTR_UPDATES.md](XATTR_UPDATES.md). Access/default ACL mutation now couples
attribute storage and inode mode in one checked transaction. This remains a host implementation;
VFS authentication, idmap translation, LSM decisions and CortenMM/OSTD runtime
locking, capture and device refinement are not supplied by an ACL object.

References: Linux v7.0 `028ef9c96e96197026887c0f092424679298aae8`,
`fs/ext4/acl.c`, `fs/ext4/acl.h` and `fs/posix_acl.c`. The compact disk version is
1; the VFS xattr version is 2. Special entries occupy four disk bytes; named
user/group entries occupy eight. Mixing the encodings is rejected.

| Component | Implemented and checked | Remaining work |
| --- | --- | --- |
| `acl.rs` | Exact entry bytes/offsets, lengths, permission bits and IDs; canonical tag-state order; mandatory mask with named entries; complete termination; Linux owner/named-user/group/other evaluation and mode equivalence | chmod/inheritance, wider feature combinations and broader acceptance completeness |
| `acl_xattr.rs` | Version-2 xattr to compact version-1 conversion, exact complete entry/permission/named-ID correspondence, short-entry ID omission, empty/header-only removal, mask-inclusive extended status and permission-mode projection | VFS ID translation, reverse userspace reporting and full acceptance completeness |
| `acl_update.rs` | Source-bound owner/scoped FOWNER authority, kind binding, access/default set/remove, mode-only folding, SGID policy, exact changed/unchanged keys and one-commit crash closure | Authenticated caller/capability/idmap/LSM decisions, inheritance/chmod and runtime serialization |
| `inode_mode.rs`, `xattr_transaction.rs`, `xattr_commit.rs` | Permission/SGID checksum resealing with unrelated-byte framing; crate-private shared storage/COW/accounting builder and common all-home durable/crash closure for user and ACL factories | Fallible resources, full operation/admission completeness and CortenMM/device refinement |
| `acl_access.rs` | Actual allocated inode/source attribute binding; mapped group membership consistency; exact ACL value and inode-mode agreement; malformed values rejected before capability checks; Linux DAC override/read-search conditions | VFS authenticated caller/capability/idmap/LSM refinement |
| `content_write.rs` | Consumed source-bound authorization object; mode-only constructor rejects access ACLs; ACL-aware constructor feeds existing clipped content and timed metadata/journal admission | POSIX open/write, allocation, other operations and runtime serialization |
| `write_frame.rs` | Timed-content writes preserve every external kind-7 xattr block, inline bytes 160..256 and the 48-bit external pointer | Other operation-specific framing and runtime/device refinement |

The evaluator follows Linux's `posix_acl_permission`: owner entries take
precedence; a matching named user is masked and does not fall through; each
matching group must independently satisfy the complete request before masking.
Partial grants from different groups are not combined. A matching but denied
group class prevents fallback to OTHER. Named proofs cover those precedence and
denial properties as well as executable/specification correspondence.

An authorization records the exact source inode, full access-ACL value, request,
credential inputs and mapped group set. Public callers cannot construct or
redirect its private fields. The content constructor consumes it and stores its
proof witness with the candidate. It checks regular-file, set-ID, size and
initialized block conditions before producing an image. The existing complete
writer admission and durable-image/recovery models apply to that candidate;
this does not assert a mounted filesystem or a runtime lock protocol.

Native tests use debugfs/libext2fs to convert VFS version-2 ACLs to actual compact
Linux disk bytes, e2fsck-check the fixture, and exercise source-bound decisions,
ACL-authorized content/time preparation, mask/mode inconsistency, malformed
values, capability conditions, complete-request group behavior, compact entry
boundaries and Rust privacy/ownership rejection cases. Pinned whole-crate Verus
verification remains the proof evidence.

## Access and default ACL mutation

`acl_update::authorize` checks an exact allocated inode, supplied filesystem IDs,
groups and scoped FOWNER/FSETID inputs. It binds the private authorization object
to Access or Default; `prepare` consumes that object and version-2 ACL bytes.
The current write permission or a named-user write ACL does not authorize changing
ACLs. The owner or scoped FOWNER decision is required for every returned mutation.
FSETID alone grants no ACL mutation authority.
The VFS must authenticate these inputs and establish the mount/user-namespace
scope of capabilities and ID/group mappings; a public host input struct supplies
none of that runtime authority.

| Request | Checked result |
| --- | --- |
| Nonempty access ACL | Mode permissions follow USER_OBJ, MASK or GROUP_OBJ, and OTHER. Named entries and MASK make the ACL extended and retained. SGID is cleared unless the caller belongs to the owning group or has the scoped FSETID decision. |
| Mode-only access ACL | The access attribute is removed and the requested permissions are represented in i_mode. An existing MASK keeps an ACL extended even without named entries. |
| Access ACL removal | Attribute removed if present; existing mode and SGID preserved. Removing an absent key succeeds without a transaction. |
| Nonempty default ACL | Accepted on a directory and retained, including a three-entry ACL. Existing mode and SGID are preserved. Regular files reject a nonempty default ACL. |
| Default ACL removal | Removes a directory's attribute without changing mode. On a regular file it succeeds without mutation, including for a nonowner, as in Linux's set_posix_acl. The bound Default authorization cannot be redirected to Access. |
| Empty input or version-2 header without entries | Interpreted as removal, not a stored empty ACL value. This differs from ordinary zero-length user attributes. |
| Unchanged normalized ACL and mode | Returns success without preparing a transaction. READONLY sources are rejected before this path. |

The converter accepts numeric named IDs already translated to the filesystem
mapping. Special-entry ID words are ignored, matching Linux, and omitted from
the compact disk form. Named INVALID_ID values, unsupported versions, malformed
lengths, invalid tags/permissions/order and missing required masks are rejected.
The complete-parse uniqueness proof in `acl.rs` binds a fresh parse to the
converted bytes without a hash or checksum identity assumption.

The common storage builder is crate-private and returns no public I/O object.
User-namespace and ACL factories independently establish their own policy before
using it. Both retain exact unrelated attributes, canonical padding/hashes,
shared-block COW/release, normalized sectors, complete allocation validation and
sealed initial/final namespace admission. Pure mode-only changes with no xattrs
do not unnecessarily enable EXT_ATTR. Type, owner IDs, setuid/sticky bits,
extents and unrelated inode bytes remain fixed; SGID can be cleared, never added.

The ACL candidate places mode, ACL bytes, pointer, ctime, version, checksums and
any allocation changes in the same bounded home-image set. The common commit
proof and ACL-specific wrapper use one persisted-commit decision for all homes,
including primary counters/features. Successful certified recovery after any
modeled writer cut therefore cannot publish mixed ACL/mode home images.
These are conditional byte-model theorems under the existing exclusive protected
source window, matching quiescent snapshot, atomic 4-KiB writes, draining flush
and quiescent restart contract. Abort alone establishes no quiescence.

Native regressions cover Linux compact conversion, owner-without-write updates,
named-writer denial, scoped FOWNER/FSETID separation, every SGID policy case,
mask-only retention, mode-only folding, default-directory semantics, idempotent
removal, COW peer preservation and release, checksum-seed/descriptor/HUGE_FILE
combinations, and each exercised writer crash cut with Linux e2fsck replay.
Negative Rust compilation additionally checks authority/candidate forgery,
kind/source redirection, mutation/reuse, wrong grant types, and access to the
private storage constructor.

EA_INODE, quotas, trusted/security namespace mutation, ACL inheritance/chmod,
reverse userspace reporting, full admission completeness and actual CortenMM/
OSTD inode/cache/allocator/device integration remain open. Kernel/full-feature/
writable-mount gates remain false. No Linux page, folio or buffer-head ownership
is introduced.
