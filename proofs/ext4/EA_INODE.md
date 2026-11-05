<!-- SPDX-License-Identifier: MPL-2.0 -->

# Isolated EA_INODE read and reference core

The EA_INODE core implements modern Linux value-inode metadata, exact-source
descriptor/value inspection, hashing and structural reference accounting.
The [source reference census](EA_REFERENCE_CENSUS.md) additionally binds complete
parent projections, physical counts, logical billing and external sharing to
all declared inode slots in the same snapshot. The separate
[EA value integrity layer](EA_VALUE_INTEGRITY.md) composes that census with all-value
payload CRCs, complete extent/data claims, exact physical sectors, joint EA claim
disjointness and checked allocation/fixed-metadata/external-xattr exclusions.
Its executable contracts and named obligations are included in the pinned
whole-crate manifest; recorded evidence determines the exact checked source.
This is not full EA_INODE filesystem admission or a journalled update path.
The ordinary whole-image allocation, namespace, writer and mount profile still
rejects EA_INODE, and every kernel/full-feature/writable-mount gate remains false.

References are pinned to Linux v7.0
`028ef9c96e96197026887c0f092424679298aae8`, principally `fs/ext4/xattr.c`,
`fs/ext4/xattr.h`, `fs/ext4/inode.c` and `fs/ext4/ext4.h` in `sources.json`.
The implementation uses safe owned or borrowed bytes; it does not import Linux
page, folio or buffer-head ownership into Asterinas's framekernel architecture.

| Design component | Present implementation and contracts | Remaining boundary |
| --- | --- | --- |
| `ea_inode.rs` | Modern 256-byte regular EA inode with EA/EXTENTS flags, nonempty value up to 16 MiB, checksum, value CRC in raw atime word, 64-bit reference count in raw ctime/high and low i_version words, live/unlinked local states and framed reference-word edits | Allocation, complete sector accounting, authenticated refcount changes, orphan membership, quota changes and durable filesystem transactions |
| `ea_source.rs` | Isolated original-snapshot header with actual EA_INODE feature retained, clean-state marker and RECOVER clear; bounded 4 KiB/256-byte geometry, source-selected descriptor width/seed/features; initialized allocated inode-bit, descriptor/bitmap checksums, unused-table bound and exact group/slot/table bytes | Full volume/journal and global ownership admission, lazy-group allocation and runtime capture; complete EA reference metadata enumeration is composed separately in EA_REFERENCE_CENSUS.md |
| `ea_reference.rs` | Ordinary parent metadata and allocated table provenance, same-source inline/external parsing, physical external checksum, complete namespace/name selection, cross-location key uniqueness and bounded nonself value-inode descriptor | Caller/namespace authority, physical block ownership and descriptor-to-lifetime coupling; complete parent projections and source count closure are composed separately |
| `ea_hash.rs` | Value CRC over all bytes, EA entry name plus one CRC word, modern unsigned and historical signed-name variants, exact-byte equality available separately | Cryptographic authentication is not provided; deduplication/allocation remains separate and must compare full bytes |
| `ea_value.rs` | Same-source allocated live value inode, exact descriptor size, complete extent-tree audit with budget up to 4,096 nodes, dense initialized mappings through the value length, unique physical value blocks, exact pointwise source bytes and both value/entry hash checks; excludes Linux's legacy Lustre classification | The isolated reader alone does not supply global metadata/data disjointness, extra-EOF allocation exclusion or complete sectors. EA_VALUE_INTEGRITY.md composes complete value/data-extent/sector checks and bounded all-value content validation; ordinary/journal ownership, quota persistence, authorization and kernel/device refinement remain open |
| `ea_refs.rs` | Up to 4,096 caller-supplied physical entry records, unique structural locations and consistent value sizes; add/remove/external-block clone count relations; separate per-parent logical references and cluster-rounded EA quota additions | Bare ledger construction does not establish source completeness; EA_REFERENCE_CENSUS.md supplies source metadata/refcount closure separately. Quota limits/database persistence, allocation/orphan transitions and journal closure remain open |

## Source and value boundaries

`ea_source::parse` reads the actual snapshot and rejects unsupported geometry or
feature combinations. It requires the superblock clean-state marker and a clear
RECOVER bit; those markers alone do not establish whole-filesystem or journal
admission. The source EA_INODE flag is retained. No stripped-feature shadow
superblock or ordinary `GroupIndex` is manufactured to bypass ordinary admission.
An allocated-node result retains exact descriptor, initialized inode bitmap and
inode-table ranges from that same snapshot. INODE_UNINIT and an unused inode-table
slot cannot supply a node from stale bytes.

`ea_reference::inspect` additionally requires an ordinary regular/directory parent
metadata image. It parses both attribute locations with EA descriptors enabled,
rejects duplicate complete keys, and returns a private descriptor selected by
namespace and full name. Hash equality is not a key-identity assumption. The
descriptor has a nonzero value length and an in-range value inode different from
the parent; selecting it does not itself establish allocation of the value inode.

`ea_value::inspect` obtains that value inode through the same header, checks its
live modern EA metadata and descriptor length, and audits its complete extent
tree. Each logical value block must resolve to an initialized mapping; holes,
unwritten mappings and repeated physical value blocks are rejected. Returned
bytes are clipped to the declared value length and are related pointwise to the
exact retained source. Values are bounded to 16 MiB, or at most 4,096 value blocks;
the separate extent audit budget is also bounded to 4,096 nodes.

The reader verifies the full value CRC using the source metadata seed and the
entry hash using either Linux name-byte convention. It explicitly rejects the
legacy Lustre classification based on entry/inode hash mismatch, parent number
and generation. CRC/hash checks establish integrity relations, not authenticity
or collision-free identity. `Value::same_bytes` compares complete returned bytes;
it does not implement deduplication, allocation or reference transfer.

These checks do not establish that value data or extent metadata are globally
disjoint from other filesystem ownership. They do not exclude additional extents
beyond the value's EOF, prove complete `i_blocks` accounting, enforce quota limits,
decode encryption, authenticate VFS access or refine CortenMM/OSTD source capture.
The reader exposes immutable host bytes, not an authorized mounted read handle.
The separate integrity layer closes the all-value payload, complete EA tree claim,
extra data-extent EOF and EA physical-sector boundaries for its stricter profile.
It still does not establish ordinary/journal data ownership or full admission.

## Local reference edits and physical versus logical accounting

EA inode reference words are not ordinary ctime or observable VFS i_version.
`ea_inode` uses the raw low i_version word and raw ctime high word, preserving the
value CRC, size, identity, extent root and unrelated bytes during resealing.
The high-word encoder writes the canonical ctime epoch needed to decode that
unsigned word; extended-time epochs do not become reference-count bits.

`Status::Live` requires a positive count and one inode link. `Status::Unlinked`
only describes zero references, zero links and the profile's zero dtime. It does
not certify membership in an orphan list/file or completion of reclamation.
`set_refcount` returns a checked byte image; it grants no authority to change a
real count and emits no I/O. In particular, a zero transition requires a separate
admitted orphan/lifetime protocol before it can enter a filesystem transaction.
No durability or concurrent-reference-update theorem is claimed for this codec.

Physical EA references count distinct xattr entry records: an inode-body entry
counts once, and an entry in a distinct external block counts once. The external
block's parent-sharing `h_refcount` is not a multiplier. Copying an external block
adds each copied EA entry once; detaching one of several parents without copying
or deleting the block does not remove its physical entries.

Quota additions are logical and per parent. Two parents sharing one external EA
entry each incur its EA-inode addition and cluster-rounded value-byte charge,
even though the physical entry contributes one reference. `quota_usage` computes
those additions from validated caller-supplied logical records; it excludes the
parent's own inode charge and performs no quota-limit or persistence operation.

Both ledgers validate their supplied record sets and reject duplicate locations,
conflicting value sizes and resource/overflow failures. The records remain caller
data: a structurally valid ledger does not prove that every disk entry was found,
that a claimed location came from this source, or that any EA inode's stored count
equals a complete on-disk census. The separate source census now establishes
those bounded reference metadata links and exact parent billing inputs.
Authenticated allocation/refcount/quota/orphan edits still require their own
ownership, lifetime and transaction protocols; a census is immutable inspection.

| Next integration obligation | Required implementation/proof |
| --- | --- |
| Full admission | Compose the source reference and EA value integrity results with ordinary/journal extent ownership, exact global bitmap equality, namespace/journal admission and exact ordinary-parent residual accounting, without bypassing feature checks. |
| Lifecycle and quotas | Couple physical references, per-parent charges, allocation, block COW, value deduplication and zero-reference orphan/reclamation transitions with complete failure unwind. |
| Durability and races | Include every resulting home image in one admitted transaction, prove crash/recovery closure and serialize competing inode/xattr/cache/allocator operations. |
| Framekernel runtime | Refine authenticated VFS/idmap/LSM inputs, CortenMM/OSTD frame/cache/DMA ownership, sleeping-lock order and actual BIO/flush/quiescence behavior. |
