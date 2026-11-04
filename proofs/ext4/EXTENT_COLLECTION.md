<!-- SPDX-License-Identifier: MPL-2.0 -->

# Complete source-bound extent collection

`extent_claims::collection_admissible` specifies the complete incoming
candidate: a valid census of the same volume geometry, an accepted live
source inode/tree, initially free pairwise-disjoint source-derived claims and
exact feature-selected inode sector accounting. Both data extents and every
inode-owned external tree node are included.

The executable collector now proves both directions:

| Result | Checked relation |
| --- | --- |
| Some | The incoming candidate satisfies the admission predicate; the returned ledger appends exactly all source-derived claims, preserves earlier occupied roles and matches inode accounting. |
| None | The incoming candidate does not satisfy that predicate. |

The recursive node collector proves the corresponding exact appendability
contract under its checked structural inputs. Leaf claims have exact ordered
prefixes and entry positions. Child-subtree claims have exact ordered prefixes
and complete next-subtree slices. A valid ledger extension of a completed
prefix preserves availability of the remaining suffix; taking the next child
prefix therefore preserves that entire child's appendability. This closes the
failure branches after earlier children have been consumed internally.

No partial candidate is published when collection fails. This is construction
of a private host census, not rollback of issued device writes.

## Tighter bound and removed checks

The collector previously rejected an accumulated count above 536,870,911 in
both its leaf and child loops. The new checked bound is tighter: each completed
partial claim sequence fits the physical volume's block count. It follows
from the actual valid ledger and the disjoint finite-block enumeration proof,
including every extent metadata block.

The two coarse runtime checks are removed. Loop invariants and the recursive
result now prove `count <= volume blocks` at every corresponding point. Under
the current census cap of 1,048,576 blocks, the old checks could never reject a
constructed valid prefix. Integer additions and inode sector multiplication
remain checked. Parsing, alias rejection and accounting checks retain their
behavior.

| Design obligation | Accomplished | Remaining |
| --- | --- | --- |
| F-ADMIT | Complete source inode/extent claim-collection admission and recursive success/rejection equivalence | All-inode/group census construction, namespace and recovery admission completeness |
| F-OWN | Exact complete ordered claims, initial availability, prior-role preservation and remaining-subtree availability | Allocation/free/conversion operations and complete filesystem preservation |
| S-RESOURCE | Actual partial and complete claim counts bounded by the physical volume; two redundant aggregate checks removed | Fallible memory reservation and actual runtime/device progress |

The Linux extent layout, seed, depth and interval rules remain those recorded
in EXTENT_TREES.md and sources.json. Filesystem blocks and physical role
ownership remain separate from CortenMM/OSTD frames, mappings, locks and DMA.
Full ext4 features, concurrent journals, actual kernel integration and device
durability refinement remain open. Kernel mount/write gates remain disabled.
