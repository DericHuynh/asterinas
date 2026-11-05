<!-- SPDX-License-Identifier: MPL-2.0 -->

# Source-bound EA value storage integrity

The EA value integrity layer composes the complete
[reference metadata census](EA_REFERENCE_CENSUS.md) with full extent-claim
collection and payload validation for every retained modern live EA inode.
The new executable contracts and obligations belong to the pinned whole-crate
manifest; recorded evidence determines their exact checked source and scope.
This document does not enable full filesystem admission or a kernel mount.

| Design component | Present implementation and contracts | Remaining boundary |
| --- | --- | --- |
| `extent_claims::collect_checked` | Reusable source-bound complete extent traversal, exact metadata/data claim projection, checked ownership-ledger append and total allocated-block count | Caller-supplied owner labels become authenticated source inode identity only in a higher layer; no filesystem operation authority |
| `ea_storage.rs` | Actual allocated live EA inode, complete source extent audit, exact complete claims, initialized dense logical coverage through the rounded value size, no additional data extent allocations past EOF, payload CRC and exact source bytes, complete EA inode sector accounting | Data-block bitmap/fixed-role checks are composed by ea_block_policy; ordinary/journal extent separation, VFS permissions, allocator/lifetime and device refinement remain separate |
| `ea_block_policy.rs` | Every EA data and external extent-node block is set in the exact logical allocation bitmap, excluded from fixed source-selected metadata and excluded from every source external-xattr block | Other files' and journal's data extents, complete bitmap ownership equality and namespace/journal admission |
| `ea_integrity.rs` | Complete bounded source reference census retained alongside one checked value result per census EA inode; shared physical ledger rejects aliases within and across all admitted EA value trees | Full filesystem allocation/namespace/journal composition, allocation/refcount/orphan/quota/dedup lifecycle, concurrency and durable mutation |

## Same-source complete value validation

The read-only API is `ea_integrity::inspect(source, inode_budget, node_budget,
byte_budget)`. Its private result exposes the retained `reference_census`, immutable
`ledger`, indexed `value` access and `value_count`, `total_bytes` and
`allocated_blocks` observations. These getters preserve the original-source
certificate and grant no mutable access to stored payloads or claims.

The source census already scans every declared inode and binds all physical EA
records, logical parent entries, stored EA refwords and external-block parent
counts to one original snapshot. The integrity constructor retains that census
and validates the entire census value list. It cannot return a positive result
for a silently truncated prefix when a node or aggregate byte budget is exhausted.
Explicit coverage checks connect every physical graph record to a stored value,
and the returned value inode numbers are unique. Exact node/Info identity proofs
then connect physical targets and each logical source entry to that same verified
payload and its CRC/name-hash relation.

Each stored value is bound to an allocated modern live EA inode obtained from the
same checked index. Its identity, metadata seed, generation, value length and
stored payload hash come from the exact retained source inode bytes. The extent
checksum domain includes that source inode number and generation. CRC equality is
never used in place of source identity or complete byte equality.

The complete audited tree is projected into all external extent-tree metadata
claims and every leaf data extent in source traversal order. Inline inode-root
bytes do not consume an additional physical block. All reachable external metadata nodes are counted, including any structurally
accepted empty leaves; minimal/canonical tree shape is not inferred. The physical
ledger validates
each claim before changing owned host state and preserves all prior occupied
slots. It rejects repeated metadata addresses, metadata/data overlap, repeated
physical data blocks, and overlap between different EA value inodes.

Dense initialized leaf coverage starts at logical block zero and ends exactly at
`ceil(value_length / 4096)`. Holes, unwritten extents and initialized or unwritten
data allocations after that rounded endpoint reject the profile. Returned bytes are
clipped to the exact value length and are related pointwise to the source block
map. The full returned payload CRC must equal the stored EA inode hash. Entry
name/hash relations and modern-versus-Lustre classification remain checked by
the retained logical binding census.

The final partial data block is counted as a full allocation, while only the
value bytes participate in the payload hash and returned slice. The immutable
reader does not infer zero-filled unused tails or grant authority to disclose or
reuse those bytes. Future allocation/write lifecycle code must establish its own
initialization and tail-zeroing obligations.

## Physical accounting and role separation

For the 4 KiB, non-BIGALLOC, non-HUGE_FILE EA inode profile, the exact relation is

```text
EA inode i_blocks (512-byte sectors)
    = 8 * (complete data extent blocks + external extent-tree metadata blocks)
```

EA inode metadata forbids nested inline/external xattrs, so there is no additional
EA inode external-xattr block charge. This physical count is separate from each
ordinary parent's logical EA value charge. Sharing one value across multiple
keys or parents does not multiply its physical storage ownership.

The standalone `ea_storage::inspect` primitive validates a source EA inode and
appends complete tree claims to a caller-owned ledger; it does not itself supply
allocation-bit or fixed-metadata provenance. The aggregate composes the separate
block policy before publishing a positive integrity result.

Every claim block must be allocated in its source group's checked logical block
bitmap. Lazy BLOCK_UNINIT semantics use the checked canonical logical bitmap,
not stale physical bits. Every EA claim is also excluded from all fixed metadata:
source-selected primary/backup superblock and descriptor blocks, every block and
inode bitmap, and every complete inode-table range. All source parent pointers to
external xattr blocks are excluded even when the block contains only local values.
The supported geometry uses one descriptor block and rejects RESIZE_INODE and
reserved-GDT expansion; this is not a general online-resize layout proof.

These exclusions do not prove global physical ownership. In particular, this
layer does not yet enumerate ordinary-file/directory or journal data extents, so
it cannot rule out an EA extent alias with those data owners. It also does not
prove that every allocated bitmap bit has exactly one global owner. Full
filesystem admission must compose those remaining roles before enabling EA_INODE.

## Linux reference and accepted profile

The reference is Linux v7.0 commit
`028ef9c96e96197026887c0f092424679298aae8`. Linux's
`ext4_xattr_inode_write` in `fs/ext4/xattr.c` allocates mappings through the rounded
value size, writes the payload and zeros the final partial block tail. Its read
path checks the declared size, full payload CRC and signed/unsigned entry hash.
`ext4_ext_replay_set_iblocks` in `fs/ext4/extents.c` counts both data blocks and
external extent-tree blocks before converting the sum to 512-byte sectors.

The dense/no-additional-extents constraints define this conservative immutable
admission profile. They do not assert that every image Linux can read has exactly
that shape. The constructor rejects unsupported shapes rather than discarding
extra allocated extents from accounting. Linux allocator preallocation policies
and future updates require separate compatibility and lifecycle proofs.

| Resource and trust boundary | Contract |
| --- | --- |
| Source inode scan | The caller's inode budget must cover every declared source inode. |
| Per-value extent audit | An explicit bounded node budget covers the complete tree, including each repeated-address visit before ownership rejection. |
| Aggregate payload bytes | The total byte budget covers the declared and retained lengths of all returned EA values before each payload is copied; exhaustion yields no positive partial certificate. Allocator capacity, temporary buffers and host allocation success are separate. |
| Physical resources | One ownership ledger covers all admitted EA values; physical claim lengths remain bounded by the declared volume. |
| Runtime and authority | Host-owned immutable bytes are neither mounted read handles nor credential, allocator, lock, journal, DMA or device authority. |

The separate [EA allocation compositor](EA_ALLOCATION.md) now combines this EA
value closure with ordinary and journal extent ownership, complete physical
bitmap equality and exact source-bound ordinary inode residual accounting.
Directory/namespace and actual JBD2 identity/state/recovery admission remain
separate integration obligations.
Allocation, block/value COW, deduplication, refcount and logical quota changes,
orphan/reclamation, concurrent cache/lock protocols and all resulting durable
home images remain unfinished. Runtime execution must refine Asterinas's
CortenMM/OSTD framekernel ownership and I/O interfaces; Linux page/folio/buffer-head
ownership is not imported. Full-feature, kernel and writable-mount gates stay false.
