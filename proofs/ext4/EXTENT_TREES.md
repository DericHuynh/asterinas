<!-- SPDX-License-Identifier: MPL-2.0 -->

# Extent-tree validation and lookup

The bounded initialized-group validator now admits ordinary inode trees at
depths zero through five with 4 KiB filesystem blocks. Journal inode 8 retains
its separately checked single-extent layout. Standalone node/tree helpers also
cover 1–64 KiB blocks. Kernel mount/write paths remain disabled. A descriptor or
structural tree certificate conveys no device, CortenMM or credential authority.

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
inputs to standalone helpers. extent_claims.bind derives them from the actual
allocated inode and checked volume feature profile.

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
| audit / CheckedTree | Every reachable child satisfies the structural predicate; exact visit counts and sufficient-budget completion are proved | Standalone structural validity remains separate from allocation and inode identity |
| Complete mapping model | Enumerates all children and covering leaf records independently of binary search; an audited path agrees with that relation, including absence of a mapping; CheckedTree.find returns such a path for every valid query | No file-access, concurrency or mutation authority is produced |
| extent_claims / extent_ownership | Bind the source inode/root/seed; enumerate every metadata and data claim; each stored mapping contributes its exact ownership claim; include external tree nodes in i_blocks | Current whole-volume geometry and physical census limits remain bounded |
| Whole-image allocation / file_read | Compose all tree claims with reservations, journal, bitmaps and counters; reject physical aliases; reads inherit exact initialized owner/generation/logical identity and return source bytes or zeros | POSIX authorization, mutation, concurrent cache/DMA and device refinement remain open |

Each descendant inherits an interval bounded by its index key and the next
sibling key, or the enclosing upper bound. Checking the final local record's
end suffices because the checked ordering theorem bounds every earlier record.
These inherited bounds exclude logical mappings that cross sibling boundaries.
The reserved terminal logical block is not a valid lookup query.

An empty leaf is allowed, including an empty root. An internal node without
children is rejected. Parent first-key equality is required only for a nonempty
child, matching Linux's empty-entry check. Physical sharing is not inferred from
this exception: the composed allocation census rejects repeated empty nodes and
overlapping physical data, including aliases across inodes or reserved/journal space.

The audit uses a finite conjunction in on-disk child order and proves its
complete coverage. Its recursive depth is at most six nodes including the root.
The visit budget is a caller-supplied resource bound, with a distinct Budget
error; it is not an on-disk format limit. The count includes repeated address
visits and is proved exact. A valid tree with a sufficient budget succeeds;
Corrupt implies the structural predicate fails, and Budget implies the exact
visit count exceeds the supplied bound. Temporary owned block buffers use at
most one root-to-leaf stack. A filesystem block remains distinct from the 4 KiB
shadow page and from a CortenMM frame.

## Allocation and read integration

The new bound inode certificate retains the actual initialized-group source,
allocated inode number, generation, inode checksum and derived extent-block seed.
The root byte offset comes from the source group/slot calculation. Tree metadata
has a distinct census role (kind 6), with its inode/generation and one-block
length. Candidate construction claims every external node and data extent in
disk order, preserves earlier occupied slots and checks exact 512-byte sector
accounting: eight sectors per data or external metadata block in this profile.

Whole-image admission reserves volume metadata and the journal first, then
collects every allocated ordinary inode's complete claims. Existing bitmap and
counter proofs compose unchanged. The unique covering-extent theorem and the
mapping-to-claim theorem connect structural reads to those exact physical slots.
lookup_allocated restores the complete-tree certificate from the sealed volume
and traverses only the requested path; it does not audit the entire tree again.

These are immutable host-image allocation/read proofs. Standalone Written
descriptions confer no backing-byte authority. Other geometries/features,
mutations and runtime integration still require their own composition proofs.

Before a lookup can authorize concurrent I/O, atomically bind the inode mapping
epoch, logical offset, physical allocation epoch and owner under the actual
OSTD guard. Pin the allocation/cache version through any DMA loan and pending
I/O. Frame lifetime alone does not freeze bytes. Insert, split, conversion,
truncate, allocation, journalling and recovery must preserve the complete tree
and ownership relations; the read-only audit does not prove these transitions.

Host interoperability covers a Linux-created external extent tree and the
actual source-selected metadata/inode/generation checksum seed, including
CSUM_SEED volumes whose filesystem and internal journal UUIDs differ. Synthetic tests cover all seven
block sizes, depths zero through five, full-capacity binary searches, sibling
boundaries, unvisited corruption, cycles and budget exhaustion. Additional tests
compose owned depth-two-through-five trees, initialized reads and unwritten zeros
with complete namespace/image validation, and reject stale seeds, wrong sector
counts, shared empty nodes and metadata/data/journal/cross-inode aliases. Tests supplement
the Verus proof; they do not establish Linux-driver or CortenMM refinement.
