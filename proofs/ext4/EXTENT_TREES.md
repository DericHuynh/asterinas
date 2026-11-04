<!-- SPDX-License-Identifier: MPL-2.0 -->

# Extent-tree validation and lookup

This extends the proof core beyond the initial inline-leaf profile. It does not
expand kernel mount admission or the whole-image allocation validator. An extent
descriptor, a checked path and a structurally checked tree convey no permission
to read or modify a device, CortenMM frame or another inode's data.

## Linux reference and representation

The reference is Linux v7.0 commit
`028ef9c96e96197026887c0f092424679298aae8`,
[`fs/ext4/extents.c`](https://github.com/torvalds/linux/blob/028ef9c96e96197026887c0f092424679298aae8/fs/ext4/extents.c),
blob `8cce1479be6d1e8d4f57428a0a0ed1088744e72e`, and
[`fs/ext4/ext4_extents.h`](https://github.com/torvalds/linux/blob/028ef9c96e96197026887c0f092424679298aae8/fs/ext4/ext4_extents.h),
blob `ebaf7cc42430fa2c36c08dedfc6767f651431442`.
The implementation is independent Rust; Linux's page, folio and buffer_head
ownership is not imported.

The inline root occupies the inode's 60-byte i_block field. External nodes use
the filesystem block size, from 1 through 64 KiB. Headers, records, 48-bit child
addresses, encoded extent lengths and the eh_max checksum domain follow the
Linux layouts. The checksum seed and legacy/checksummed mode remain explicit
inputs until bound to a checked inode and volume feature set.

Linux's ext4_ext_binsearch_idx, ext4_ext_binsearch and ext4_find_extent guide
selection and descent. Binary search finds the position after every key less
than or equal to the query. Index traversal selects its predecessor, or the
first child when the query precedes the first key. It still validates that
child before reporting a hole. A node at depth d must lead to a child at d-1;
the maximum root depth is five.

## Certificates and obligations

| Component | Established relation | Remaining boundary |
| --- | --- | --- |
| Node parser and search | Total parsing, strict keys, nonoverlapping local intervals, exact binary-search partition and unique covering leaf record | The caller must supply the correct checksum mode and inode seed |
| Branch check | Expected depth, nonempty internal nodes, matching first key for nonempty children and inherited exclusive logical upper bounds | Structural validity does not establish physical ownership |
| lookup / CheckedPath | Exact root/source bytes, every selected child from the same immutable source, depth decreases, no repeated external block along a successful path, written/unwritten/hole distinction | Unvisited branches are not validated by this API |
| audit / CheckedTree | Every reachable child satisfies the structural predicate; exact visit counts and sufficient-budget completion are proved | Data/metadata allocation claims, physical alias rejection and sector accounting must still compose with whole-volume admission |
| Complete mapping model | Enumerates all children and covering leaf records independently of binary search; an audited path agrees with that relation, including absence of a mapping; CheckedTree.find returns such a path for every valid query | No file-access, concurrency or mutation authority is produced |

Each descendant inherits an interval bounded by its index key and the next
sibling key, or the enclosing upper bound. Checking the final local record's
end suffices because the checked ordering theorem bounds every earlier record.
These inherited bounds exclude logical mappings that cross sibling boundaries.
The reserved terminal logical block is not a valid lookup query.

An empty leaf is allowed, including an empty root. An internal node without
children is rejected. Parent first-key equality is required only for a nonempty
child, matching Linux's empty-entry check. Physical sharing is not inferred from
this exception: repeated empty nodes and overlapping physical data still need
the allocation census to reject invalid ownership.

The audit uses a finite conjunction in on-disk child order and proves its
complete coverage. Its recursive depth is at most six nodes including the root.
The visit budget is a caller-supplied resource bound, with a distinct Budget
error; it is not an on-disk format limit. The count includes repeated address
visits and is proved exact. A valid tree with a sufficient budget succeeds;
Corrupt implies the structural predicate fails, and Budget implies the exact
visit count exceeds the supplied bound. Temporary owned block buffers use at
most one root-to-leaf stack. A filesystem block remains distinct from the 4 KiB
shadow page and from a CortenMM frame.

## Integration still required

Bind the root offset, feature mode, checksum seed, inode number/generation and
filesystem geometry to the checked volume/inode. Compose every tree-metadata
and data extent with global allocation roles, initialized bitmap semantics and
i_blocks accounting. A structural Written result describes the encoded extent
state; it grants no access to the backing bytes.

Before a lookup can authorize concurrent I/O, atomically bind the inode mapping
epoch, logical offset, physical allocation epoch and owner under the actual
OSTD guard. Pin the allocation/cache version through any DMA loan and pending
I/O. Frame lifetime alone does not freeze bytes. Insert, split, conversion,
truncate, allocation, journalling and recovery must preserve the complete tree
and ownership relations; the read-only audit does not prove these transitions.

Host interoperability covers a Linux-created external extent tree and the
actual UUID/inode/generation checksum seed. Synthetic tests cover all seven
block sizes, depths zero through five, full-capacity binary searches, sibling
boundaries, unvisited corruption, cycles and budget exhaustion. Tests supplement
the Verus proof; they do not establish Linux-driver or CortenMM refinement.
