<!-- SPDX-License-Identifier: MPL-2.0 -->

# Source-bound whole-volume allocation with EA_INODE

The EA allocation compositor extends the checked
[EA value integrity layer](EA_VALUE_INTEGRITY.md) with every supported ordinary
inode's complete extent allocations, the internal journal mapping, fixed volume
metadata and distinct external xattr blocks. A positive result relates the
combined physical ownership ledger to every source group allocation bitmap in
both directions. It retains all EA reference, payload and source-name/hash
relations established by the earlier layers.

The executable contracts and named obligations belong to the pinned whole-crate
manifest; recorded evidence determines the exact checked source and scope. This
is an immutable allocation certificate. It does not establish directory record
or namespace validity, actual JBD2 journal state/admission, filesystem operation
authority, a writable mount or CortenMM/OSTD/device execution.

| Design component | Present implementation and contracts | Remaining boundary |
| --- | --- | --- |
| `block_claims::Census::duplicate` | Owned duplication of the exact immutable role and claim catalogue; the retained EA integrity result and extended candidate refer to equal initial ownership | Host allocation/capacity behavior and future runtime representation refinement |
| `ea_reservations.rs` | Source-selected fixed group metadata reservation and one physical claim per distinct source external-xattr block, including blocks with only local values | Mutation, allocation and shared-block COW/lifetime |
| `ea_journal.rs` | Actual allocated source inode 8, supported single initialized extent, exact physical sector count, no nested attributes and one disjoint journal claim | JBD2 superblock identity/UUID/state, committed log admission, recovery and writer integration |
| `ea_ordinary.rs` | Source-bound ordinary parent metadata/attributes, complete regular-file/directory extent claims, exact normalized parent-sector split and physical interpretation of the ordinary allocation residual | Directory contents and namespace, data read/operation authority, extent mutation and runtime cache/locks |
| `ea_allocation_counts.rs` | Every logical source block bitmap equals the final ledger's occupied slots, complete source-directory counts and exact primary free-block count | Allocation transitions and persistent counter updates |
| `ea_allocation.rs` | Complete declared inode-slot classification, source-bound ordinary catalogue, retained EA integrity and one global disjoint physical ownership ledger | Namespace/JBD2 admission, durable filesystem mutations, concurrency and framekernel runtime refinement |

## Complete source composition

The public entry is `ea_allocation::inspect(source, inode_budget, node_budget,
byte_budget)`. It retains the successful `ea_integrity` result and extends an
exact owned duplicate of its EA block ledger. It does not remove the source
EA_INODE feature bit or manufacture an ordinary-profile `GroupIndex`.

The constructor scans every declared inode slot, with the caller's inode budget
covering the entire declared count. Unallocated ordinary slots contribute no
storage. Supported empty reserved slots must contain no hidden allocations or
attributes. Allocated modern EA slots resolve to the exact retained checked EA
value. Journal inode 8 is handled by the journal mapper. Every allocated
ordinary inode 2 or numbered at least 11 contributes one actual source-bound
regular-file or directory result. Root inode 2 must be a directory.

The explicit slot catalogue connects these roles to the complete source scan.
The ordinary sequence is exactly the ordinary projection of that catalogue;
source directory counts cannot be justified by a caller-supplied incomplete or
duplicate list. EA values in the supported reserved 3/4 slots remain EA values,
not ordinary parents or empty reserved inodes.

All claims enter one checked ledger. Its final claim sequence is exactly the
retained EA claims plus the source-derived reservations and complete ordinary
claims in the constructor's declared order. Claims are never silently dropped
when an alias, unsupported shape or resource failure occurs. No positive
certificate follows a partially successful scan or ledger extension.

## Physical roles and sharing

| Role | Physical ownership |
| --- | --- |
| 1 | Primary and source-selected backup superblock/descriptor regions |
| 2 | The internal journal's supported physical extent |
| 3 | Every group block bitmap, inode bitmap and complete inode table |
| 4 | Regular-file data and EA value data, retaining distinct source inode identity |
| 5 | Initialized directory data |
| 6 | Inode-owned external extent-tree metadata |
| 7 | One physical external-xattr block, shared only through checked parent pointers |

The ledger rejects overlaps between EA data or extent metadata and ordinary
file/directory storage, journal storage, fixed metadata or external xattr blocks.
It also rejects ordinary-to-ordinary aliases, repeated external extent nodes and
cross-role aliases between source group reservations. The earlier per-value
integrity checks remain necessary: global physical ownership alone would not
check a value's declared payload, CRC or source entry hash.

External xattr parent pointers are enumerated separately from contained EA
entries. The compositor records each distinct external block once, even when
multiple parents share it or it contains no EA entries. A repeated pointer is
skipped only because the same address occurred in the preceding source pointer
catalogue. A pre-existing ledger slot of role 7 does not by itself authorize
sharing or permit the compositor to claim an unrelated occupied block.

The retained reference census checks each external header's parent count and
each EA inode's distinct physical-entry indegree. Logical parent billing is
separate from both of those counts.

## Exact accounting

Each ordinary inode has the source-bound sector relation

```text
normalized parent sectors
    = 8 * complete ordinary data/extent-metadata allocation
    + (external xattr pointer present ? 8 : 0)
    + sum over logical EA entries(ceil(value_size / 4096) * 8)
```

The arithmetic `own` residual from the earlier billing layer is now equal to
actual complete ordinary extent claims. Logical EA charges must not be added as
physical claims; the EA inode's value storage is already claimed once. External
blocks shared by several parents are physically claimed once, while each parent
retains its own pointer charge. EA inode physical sectors continue to include
both its data and external extent-tree metadata.

Regular files retain supported holes, unwritten/preallocated extents and
allocations after their current logical EOF; those are physically accounted.
The stricter EA value profile requires dense initialized data ending at the
rounded value length. Ordinary directory claims require initialized data, but
this does not validate directory records, HTree routing, links or rootedness.
Every reachable supported extent metadata node is counted; tree minimality and
zero-filled unused payload tails are not inferred.

Every group's checked logical allocation bitmap must equal the final nonfree
ledger roles for the complete group range. This rejects claimed-free storage
and allocated-but-unowned blocks after all declared roles are composed. Lazy
bitmap groups use their source-selected logical semantics, not stale physical
bitmap bits. Group free counts already match those checked bitmap images, and
the complete sum equals the primary superblock free count.

The used-directory count in each group equals the complete source ordinary
catalogue's allocated directories in that group. Modern EA values and inode 8
are regular inodes and do not increment that count. The admitted 64-byte
descriptor profile requires the corresponding high counter halves to be zero.

## Bounds, Linux references and remaining work

The fixed source profile remains 4 KiB blocks, 256-byte inodes, at most 32 groups
and at most 1,048,576 filesystem blocks/inodes. Unsupported inode types, legacy
block maps, fragmented journals and unimplemented on-disk feature combinations
reject admission. There is no Linux-wide acceptance-completeness claim.

The public `node_budget` remains the EA per-value audit budget of 1 through
4,096; ordinary extent audits derive a separate budget of volume blocks plus
one for the inline root. The retained EA payload limit remains 16 MiB per value
and at most 64 MiB of aggregate declared payload bytes. These bounds do not prove
exact heap capacity, temporary-buffer size or host allocation success.

References remain Linux v7.0 `028ef9c96e96197026887c0f092424679298aae8`.
`fs/ext4/xattr.c` creates EA inodes as regular files and distinguishes logical
parent charges from physical shared storage. `fs/ext4/ialloc.c` updates the
group used-directory counter only for directory mode. `fs/ext4/extents.c`
accounts data and external extent-tree blocks in physical sector accounting.
The implementation is independent safe Rust and does not import Linux
page/folio/buffer-head ownership into Asterinas.

This certificate can exist even when directory bytes are invalid or the mapped
journal has invalid/nonempty JBD2 content. Full EA filesystem admission must
compose directory/namespace validation and actual journal identity/state and
recovery contracts before authorizing operations. Allocation, refcount/COW,
quota persistence, orphan/reclamation, concurrent cache/lock protocols, durable
home images and restartable operations remain unfinished. Kernel, full-feature
and writable-mount gates remain false. Runtime execution must refine Asterinas's
CortenMM/OSTD frame, ownership, synchronization and device interfaces.
