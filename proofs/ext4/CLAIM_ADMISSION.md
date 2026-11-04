<!-- SPDX-License-Identifier: MPL-2.0 -->

# Complete metadata and journal claim admission

The allocation census records filesystem block roles. `claim_admission`
defines when a sequence can be appended: every claim has a valid bounded
interval and role, every claimed interval is initially free, and the new
claims are pairwise disjoint. This does not describe ownership of a memory
frame or grant access to CortenMM storage.

Two checked results connect that condition to actual census construction:

| Result | Meaning |
| --- | --- |
| Valid ledger extension implies appendability | A successful final ledger cannot conceal an invalid, overlapping or initially occupied added claim. This follows from exact interval/role lookup and ledger disjointness. |
| One exact claim preserves remaining appendability | The executable pointwise update cannot consume any later disjoint claim. Availability survives each iteration. |

`group_claims::reserve` and `reserve_with_features` now prove success exactly
when the descriptor, geometry and complete reserved-claim sequence satisfy
their declared admission predicate. The sequence includes the sparse-super
superblock/GDT pair where applicable and the actual source descriptor's block
bitmap, inode bitmap and inode-table interval. FLEX_BG placement retains its
global physical addresses. The loop proves remaining availability, prior
occupied-role preservation and the exact accumulated claim sequence.

`inode_claims::reserve_journal` likewise proves success exactly when the
source journal inode/layout, sector accounting, volume geometry and initially
free journal interval satisfy its declared predicate. Failure means that
predicate is false. Journal role 2 remains disjoint from metadata, files,
directories and inode-owned extent-tree metadata.

These strengthen executable contracts without changing parsing or reservation
decisions. The pinned Linux bitmap/group/journal-inode references in
sources.json continue to define the admitted byte interpretation. The
independent safe Rust census establishes global disjointness separately from
Linux's local descriptor checks.

| Design obligation | Accomplished | Remaining |
| --- | --- | --- |
| F-ADMIT | Complete group-metadata and internal-journal reservation predicates, with executable success/rejection equivalence | Complete all-inode allocation, namespace and recovery admission |
| F-OWN | Exact sequence availability; pointwise role updates preserve remaining disjoint reservations | Allocation/free/extent mutation preservation and complete filesystem operations |
| S-ENTRY | Existing private census ownership and total public entry points retain their boundaries | Actual CortenMM/OSTD guards, cache, device and VFS integration |

The existing bounded format profile still applies. These are static candidate
construction proofs, not a concurrent allocator or a mounted filesystem.
Kernel mount/write activation remains disabled.
