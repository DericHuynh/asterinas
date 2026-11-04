<!-- SPDX-License-Identifier: MPL-2.0 -->

# Validated serialized writer admission

`writer_admission.rs` accepts a sealed frozen edit batch and one retained,
immutable source snapshot. Before returning any dispatchable wrapper it checks
the complete static filesystem before and after the proposed transaction, the
actual journal layout, and the bootstrap identity policy. This is host-core
candidate admission. VFS authorization, current physical-media identity,
CortenMM locks/loans and mounted filesystem durability require further proofs.

## Exact candidate result

The checked result applies these layers to the retained source, in order:

1. The writer's dirty primary-superblock image at block zero.
2. Its actual descriptor, escaped payload and commit images at their exact
   physical journal addresses.
3. Its original home after-images in frozen target order.
4. Its retired journal superblock.

The retained source is the same one used to discover the journal inode, read the
primary superblock, derive the internal journal UUID, capture all journal bytes
and validate the starting allocation and namespace. The frozen reservation's
layout must match that source. Journal bytes, including its UUID, are not taken
from a different filesystem or supplied independently by the caller.

Temporary owned patch sets and borrowed shadow layers construct the exact
candidate result without copying the complete filesystem. The immutable writer
retains the actual images. A ghost certificate records the successful complete
allocation/namespace checks and exact result relation after the temporary shadow
layers are dropped. The certificate is not an unchecked boolean supplied by the
caller. `PatchSet::from_images` checks ordered unique targets and its credit
limit while consuming owned images; rejection returns the original images.

| Boundary | Checked guarantee | Remaining work |
| --- | --- | --- |
| Input source | Complete static allocation and namespace certificate, source-bound bootstrap and journal | Physical device/mount epoch and exclusion |
| Frozen edits | Exact sealed images and reserved layout | Operation-specific authority and observable result |
| Proposed result | Complete static validation of actual dirty/log/home/tail layers | Proof of every supported filesystem operation and admission completeness |
| Bootstrap | Fixed primary identity, group metadata addresses and entire journal inode | Resize, relocation and versioned bootstrap |
| Dispatch/completion | Consuming wrappers retain the same source, images and certificate; no forged or reused completion | Concrete OSTD BIO/DMA and device refinement |
| Abort/failure | Sticky failure prevents new dispatch; outstanding completion stays owned and consumable | Physical quiescence and concurrent commit/checkpoint |

## Scope of the proof

The complete pinned Verus run checks construction and preservation of the
certificate, including all public executable bodies. The existing serialized
writer's local admission, command ordering, byte/persistence ledger and crash
proofs remain under their declared atomicity, flush and quiescent-start
contract. Retaining this new static result certificate does not itself prove
that a real device executes the commands, or discharge the remaining full-image
refinement between that ledger and filesystem operations. No device report is
treated as an authority to mutate an unrelated filesystem.

Native tests materialize the candidate result from the writer's actual getters,
run the six-fence command pipeline, compare the entire resulting image including
all journal records, validate it again and check e2fsprogs acceptance. They also
exercise fully checksummed namespace/journal-identity violations, invalid starts,
wrong reservation layouts, failure and abort with late completion. Negative Rust
compilation checks cover forged wrappers, replaced engines, extraction, reused
dispatch and reused/replaced pending completions. Tests supplement the formal
scope and do not establish a physical driver contract.

All mount and write activation gates remain closed. The implementation uses
safe Rust and host-owned bytes. The eventual framekernel adapter must preserve
these identities and immutable versions using CortenMM/OSTD ownership; Linux
page, folio and buffer-head ownership is not part of the implementation.
