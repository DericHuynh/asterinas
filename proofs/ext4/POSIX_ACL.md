<!-- SPDX-License-Identifier: MPL-2.0 -->

# Source-bound POSIX ACL decisions

The host profile decodes Linux ext4 compact version-1 ACL values, evaluates
permission requests and connects successful source-bound decisions to the
initialized-file content/time writer and the isolated inode-body user-value
replacement in [XATTR_UPDATES.md](XATTR_UPDATES.md). This remains a host implementation;
VFS authentication, idmap translation, LSM decisions and CortenMM/OSTD runtime
locking, capture and device refinement are not supplied by an ACL object.

References: Linux v7.0 `028ef9c96e96197026887c0f092424679298aae8`,
`fs/ext4/acl.c`, `fs/ext4/acl.h` and `fs/posix_acl.c`. The compact disk version is
1; the VFS xattr version is 2. Special entries occupy four disk bytes; named
user/group entries occupy eight. Mixing the encodings is rejected.

| Component | Implemented and checked | Remaining work |
| --- | --- | --- |
| `acl.rs` | Exact entry bytes/offsets, lengths, permission bits and IDs; canonical tag-state order; mandatory mask with named entries; complete termination; Linux owner/named-user/group/other evaluation and mode equivalence | Empty-ACL representation, chmod/inheritance/ACL mutations and broader acceptance completeness |
| `acl_access.rs` | Actual allocated inode/source attribute binding; mapped group membership consistency; exact ACL value and inode-mode agreement; malformed values rejected before capability checks; Linux DAC override/read-search conditions | VFS authenticated caller/capability/idmap/LSM refinement |
| `content_write.rs` | Consumed source-bound authorization object; mode-only constructor rejects access ACLs; ACL-aware constructor feeds existing clipped content and timed metadata/journal admission | POSIX open/write, allocation, other operations and runtime serialization |
| `write_frame.rs` | Timed-content writes preserve every external kind-7 xattr block, inline bytes 160..256 and the 48-bit external pointer | Full ACL-mutation crash closure and runtime/device refinement |

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
