<!-- SPDX-License-Identifier: MPL-2.0 -->

# Source-bound EA reference and billing census

The census implementation extends the isolated [EA_INODE core](EA_INODE.md) with
complete bounded source metadata enumeration and physical/logical reference
closure. A successful result binds every classified inode and projected EA
descriptor to the original snapshot. It relates every allocated live EA inode's
stored count to the distinct physical entry graph, while preserving logical
multiplicity for parent billing. The new executable contracts and obligations
are in the pinned manifest; recorded evidence determines exact checked scope.

This remains immutable metadata inspection. It is not full filesystem admission,
global block ownership, namespace/journal validation, content validation of every
EA value, a quota database, orphan lifetime, or a journalled update protocol.
Ordinary full-filesystem admission still rejects EA_INODE, and all kernel,
full-feature and writable-mount gates remain false.

| Design component | Present implementation and contracts | Remaining boundary |
| --- | --- | --- |
| `ea_index.rs` | Complete ordered actual-feature group index; same-source descriptors and block/inode bitmaps, canonical logical lazy bitmaps, checksums/high halves/padding/free counts, primary free-counter sums, pairwise inode-table block-range separation and disjoint source inode slots | Other metadata/data role separation, global physical ownership, namespace/journal admission and lazy-group allocation |
| `ea_parent.rs` | Exact allocated ordinary-parent metadata, complete inline/external EA descriptor projection, full-key uniqueness, source entry locations, nonself targets, per-parent logical projection and actual external header count | Value content and global block ownership, caller authority and mutation/lifetime coupling |
| `ea_ref_projection.rs` | Owned graph with exact supplied-parent input projection, physical location deduplication and per-parent logical multiplicity; conflicting descriptors and resource exhaustion reject construction | The bare graph's inputs are caller data; source completeness is established by `ea_census`, not graph construction alone |
| `ea_billing.rs` | Exact normalized parent-sector split into logical EA charges, one external-block charge and an aligned arithmetic residual; every logical entry is charged even when values/blocks are shared | The residual is not physical ownership; extent audit, quota limits/database persistence and mutation remain separate |
| `ea_census.rs` | Complete declared inode scan/classification, graph inputs exactly projected from source parents, allocated live exact-size physical targets, stored EA counts equal physical indegree, exact source-name/target-stored-hash relation and non-Lustre checks for every logical parent, external `h_refcount` equal every ordinary parent pointer, and every external xattr block excluded from all inode-table blocks | Other metadata/data role separation, global ownership, namespace/journal/value-content admission, orphan/allocation/quota lifetime and CortenMM/VFS/device refinement |

References are Linux v7.0 `028ef9c96e96197026887c0f092424679298aae8`, particularly
`fs/ext4/xattr.c`, `fs/ext4/inode.c`, `fs/ext4/orphan.c`,
`include/linux/quotaops.h` and `fs/quota/dquot.c`, pinned in `sources.json`.

## Complete source enumeration

`ea_index` retains the original EA_INODE-enabled header and reads every group in
order. Initialized bitmap bytes come from their exact source locations.
INODE_UNINIT groups use canonical all-free logical inode bitmaps, so stale
physical table bytes cannot supply allocated inodes. BLOCK_UNINIT groups use
source-geometry/backup-selected canonical reserved-metadata and padding bits.
Physical checksum fields are ignored only for the corresponding checked lazy
case. Initialized extended descriptors use both checksum halves. The complete
group free-block and free-inode sums must match the primary superblock.
Before constructing the index, every pair of inode-table block ranges must be
disjoint. This applies to source-selected FLEX_BG placement as well as local
group placement. Node/table-membership and byte-range contracts connect each
retained source inode to its checked table and separate different inode slots.
These bitmap/count and table-range relations are not a global physical ownership
census.

`ea_census::inspect(source, inode_budget)` requires the budget to cover the
header's entire declared inode count before scanning. It visits every slot;
it cannot return a positive certificate for a silently truncated inode prefix.
The bounded profile supports at most 32 groups and 1,048,576 declared inodes.
Successful classification distinguishes unallocated ordinary slots, supported
reserved slots, live ordinary parents and allocated modern live EA values.
Root inode 2 must be a directory. Reserved inode handling is separate from
ordinary-parent projection; the journal inode is required to have no attributes.
The constructor also structurally parses each Reserved body's geometry and
requires it to contain no attributes; the class contract retains body absence.
Nonjournal reserved slots additionally satisfy the empty reserved
inode predicate, while inode 8 has checked ordinary regular metadata and no
external pointer. Uninterpreted padding when extra size is zero is not treated
as an attribute table; no blanket zero-padding condition is inferred.
EA values may occupy ordinary inode numbers or the supported reserved 3/4 slots.
No allocated zero-reference EA inode is admitted as an orphan.

The header requires the superblock clean-state marker, RECOVER clear and
`s_last_orphan == 0`; ORPHAN_FILE and ORPHAN_PRESENT remain unsupported by the
feature policy. These exclusions do not prove that a journal is empty or that
a namespace/mount is valid. The local `ea_inode::Unlinked` codec state remains
available independently and supplies no orphan membership proof.

## Physical graph, logical bindings and external sharing

Each ordinary parent's body and external tables are parsed completely from the
same source. Every EA entry is projected by physical location: inode number and
entry offset for body entries, external block address and entry offset otherwise.
Shared external entries therefore occur once in the physical graph. Each parent
sharing an entry retains its own logical record, and distinct entry offsets remain
distinct even when they reference the same value inode.

The graph stores its parent inputs and exact physical/logical projections.
`ea_census` binds those inputs to all source parents with EA entries; the graph
helper alone accepts caller-supplied records. Deduplication uses the complete
physical location and requires matching value-inode and value-size fields. Hash or CRC
equality supplies no source identity assumption.

The census also rejects every external xattr block that lies in any group's
inode-table range. Disjoint source inode slots prevent distinct inline parents
from sharing the same inode bytes. The external exclusion prevents an external
entry location from being an alternate name for any inode slot under FLEX_BG.
It is a specific role-separation boundary: GDT, bitmap, journal, other metadata
and data-extent aliases still require the future global ownership audit.

Every physical graph target must be allocated in its group's checked logical
inode bitmap from the same source. It must have live modern EA metadata and the
exact descriptor value length. Conversely,
every allocated live EA inode's positive stored reference word must equal its
physical graph indegree. An allocated EA inode with no incoming descriptor is
rejected. This is reference metadata closure; it does not audit every value's
data extents or compare every payload CRC with its stored value hash.

Every logical binding also checks the entry hash against the exact selected
source entry name combined with the target inode's stored value-hash word.
Either Linux's unsigned-name convention or its historical signed-name convention
must match. The selector returns the actual source name for the selected physical
entry; a supplied hash or another entry's name cannot substitute. This establishes
an entry/metadata-hash relation, not a payload CRC check. The census still does
not read every value's contents or audit its complete physical sector accounting.

The modern-versus-Lustre check is applied to every logical parent binding,
including every parent of a shared external block. It is not checked only once
per deduplicated physical entry. The bounded raw-mtime comparison conservatively
excludes the legacy classification; unusual extended-time epochs may reject
additional images. Linux-wide fallback acceptance completeness is not claimed.

External parent pointers are enumerated separately from EA entries. Their header
`h_refcount` must equal the complete number of ordinary parent pointers, including
blocks containing only local values and therefore no EA graph records. This
count does not multiply EA inode physical indegrees.

## Billing is distinct from ownership

Linux charges parent `i_blocks` for logical EA values even when quota features
are disabled. In this 4 KiB, non-BIGALLOC profile, each parent has the split

```text
normalized parent sectors = own residual sectors
                          + (external pointer present ? 8 : 0)
                          + sum over logical EA entries(ceil(value_size / 4096) * 8)
```

Every logical EA entry contributes, including two different keys referencing
the same value and entries in a shared external block. Each parent also pays
for its external block pointer. Linux separately accounts for the EA inode's own
value/extent storage; this census does not audit that physical sector count.
Parent bills must not be added as physical allocation
claims. `ea_billing` checks nonnegative subtraction, alignment and overflow.
Within the census, the logical entries are bound to the actual parent tables.
The resulting `own` field remains an arithmetic residual until a global extent
and allocation audit binds it to real physical claims.

| Resource/profile boundary | Contract |
| --- | --- |
| Inode scan | Caller budget covers every declared inode; insufficient budget rejects before a positive census. |
| Tracked references | At most 4,096 physical records, logical records and EA-bearing graph parents; no dropped entries on exhaustion. |
| Values and external pointers | At most 4,096 allocated EA values and ordinary external-parent pointer records, including local-only external blocks. |
| Per-parent entries | At most 260 projected EA records across body and external storage. |
| Operation authority | No caller credential, VFS permission, count-edit, allocator, journal or device authority follows from the result. |

Native regression scenarios include reserved slots carrying hidden inline EA
entries, two-group FLEX_BG placement with lazy bitmap semantics, overlapping
inode-table ranges and external-xattr/inode-table aliases. Exact executions and
pass counts are supplied by recorded evidence, not by this scenario list.

The separate [EA value integrity layer](EA_VALUE_INTEGRITY.md) now composes this
reference closure with complete bounded EA tree claims, payload CRCs, exact EA
physical sectors, joint EA value disjointness and source allocation/fixed-metadata/
external-xattr exclusions. The reference census alone retains its metadata-only
scope. Full admission still requires ordinary/journal data-owner separation,
exact global bitmap ownership, namespace/journal validation and exact ordinary
inode sector accounting without bypassing feature checks. Authenticated allocation, refcount/COW/deduplication, quota persistence,
orphan/reclamation, concurrent lock/cache protocols and durable crash recovery
remain unfinished. Runtime execution must use Asterinas's CortenMM/OSTD
framekernel memory, ownership, locking and device interfaces.
