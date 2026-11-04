<!-- SPDX-License-Identifier: MPL-2.0 -->

# Complete inode binding and physical audit budgets

`extent_claims::bind` now proves success/rejection equivalence with
`binding_admissible`: the inode is live in the retained source, its
feature-selected metadata/checksum and root type are accepted, its complete
source-derived tree is structurally valid, and the supplied budget covers the
exact audit visit count. This includes every branch at admitted depths zero
through five. Repeated addresses consume repeated visits; global allocation
validation still rejects physical aliases.

The new resource proofs connect three quantities:

| Quantity | Checked bound |
| --- | --- |
| Complete tree visits | At most the inode's collected claim lengths plus one for the inline root; every external-node visit contributes a metadata-block claim |
| Complete valid ledger claim lengths | At most the physical volume's block count; valid pairwise-disjoint intervals enumerate distinct blocks inside the finite volume |
| One live inode's claim lengths | At most the complete ledger's claim lengths, through the exact inode/group/all-group concatenations |

`allocation_budget::every_live_inode_fits_the_volume_sized_audit_budget`
combines these results: every live ordinary inode in a valid AllocationView
satisfies the exact binding predicate with budget `blocks + 1`. The argument
uses the actual global no-alias ledger, including external extent metadata.
Tree depth alone would not establish this physical work bound.

The executable `extent_claims::audit_allocated` uses that theorem. It takes a
sealed AllocatedInode, derives its retained source, inode identity and volume
budget, and returns a complete BoundInode without an optional failure result
or an unchecked precondition at its public entry. Its internal bind/unwrap is
proved successful. This removes a guessed audit budget for already validated
inodes; it does not grant VFS or device authority.

The finite block enumeration and set-cardinality argument are ghost proofs;
they add no runtime block-list allocation. Runtime audit behavior and the
format profile are otherwise unchanged. Memory-allocation failure, actual
source capture and driver progress remain outside the host-core proof.

Linux's pinned extent headers, depth rules, checksum domains and source
interpretation remain those recorded in EXTENT_TREES.md and sources.json.
No Linux page/folio ownership is introduced. Filesystem block roles remain
separate from CortenMM/OSTD frame, mapping, lock and DMA ownership.

| Design obligation | Accomplished | Remaining |
| --- | --- | --- |
| F-ADMIT | Complete live-inode/tree binding predicate and guaranteed allocated-inode audit | Complete census construction, namespace and recovery admission |
| F-MAP | Same-source inode/root/generation/checksum and complete tree audit composition | Extent mutation, allocation/free/conversion and full ext4 layouts/features |
| F-OWN | Exact global-to-inode claim sum and physical volume work bound | Filesystem operation preservation and actual concurrent ownership refinement |
| S-RESOURCE | A volume-sized visit budget suffices for every validated inode | Fallible memory reservation and runtime scheduler/device progress |

These results apply to the existing bounded host profile. Full ext4 feature
coverage, concurrent journals and actual CortenMM/OSTD/device integration remain
open. Kernel mount/write gates remain disabled.
