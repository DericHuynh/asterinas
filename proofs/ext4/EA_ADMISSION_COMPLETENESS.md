<!-- SPDX-License-Identifier: MPL-2.0 -->

# EA admission acceptance completeness

This change strengthens acceptance completeness for explicit stages of the
existing bounded EA_INODE profile.
A successful constructor still establishes the original validity relation.
A rejected constructor additionally excludes its declarative admission profile:
an input satisfying that profile cannot be rejected.
Header, group/index and graph runtime decisions are unchanged.
The reserved-inode leaf check also fixes a false rejection in EA census
construction, while retaining its existing declarative safety conditions.

This is a prerequisite for complete EA filesystem admission after recovery.
It does not prove that the complete filesystem validator accepts every valid
repaired image.
The [durable namespace core](EA_DURABLE_NAMESPACE.md) still validates each actual
repaired shadow before granting recovery I/O authority.

## Source projections and exact parser contracts

The header profile checks the actual primary superblock bytes, partition length,
geometry, feature policy and checksum.
The canonical header projection decodes only those bytes.
A valid header is proved equal to that projection, and an admissible source has a
valid projected header.
Actual EA_INODE and RECOVER bits are retained.
The legacy clean namespace inspector and volatile mutation constructors retain
their separate RECOVER-clear guard.

Allocated inode-slot reads use the exact source-selected descriptor, initialized
inode bitmap, inode-table address, slot and 256-byte slice.
The read profile includes bitmap allocation, table high-water bounds and the
existing checksum checks.
Allocation alone does not bypass an uninitialized or unused inode-table slot.

Each canonical group projection retains actual descriptor addresses, counters
and checksum domains.
Initialized bitmaps retain their physical source bytes.
INODE_UNINIT and BLOCK_UNINIT select the existing logical empty/reserved bitmap
semantics, so stale physical bytes do not become allocation authority.
The canonical index is the complete ordered sequence of these groups, with
source-primary free-counter sums and pairwise disjoint inode tables.
The index loop retains the exact corresponding projected prefix.
Uniqueness proofs show that every original valid group or index is this same
projection; canonical admission does not add a narrower hidden format policy.

| Constructor | Declarative admission profile | Result contract |
| --- | --- | --- |
| `ea_source::parse` | `source_admissible` over actual source bytes | Some retains the unique valid `header_projection`; None excludes the source profile |
| `Header::get` | `ea_source::node_admissible` for the requested exact slot | Some retains the unique `node_projection`; None excludes that slot profile |
| `ea_index::read_group` | `group_admissible` for the source-selected group | Some retains the exact `source_group`; None excludes its validity |
| `ea_index::parse` | `ea_index::admissible` for the complete `source_index` | Some retains the complete canonical index; None excludes that index profile |
| `Index::node` | Actual logical inode allocation and `ea_source::node_admissible` | Some retains the exact source inode-slot view; None excludes their conjunction |

The profiles depend on source bytes and declarative validity.
They do not call the executable validators or assume successful execution.

## Complete namespace counts and rooted topology

The namespace bridge theorem proves that every existing valid full namespace
certificate satisfies these complete lower and upper stage profiles.
This supplies facts for later recovery composition without strengthening the
unproved raw namespace acceptance contract.

These upper-stage contracts start with a sealed, complete EA directory index.
They do not establish that the earlier directory-index constructor can accept
every valid raw filesystem.

The count profile consists of the existing capacity bounds and canonical dot
record rules over the complete entry sequence.
Malformed dot placement, target or type excludes count admission.
The parent profile adds the existing Linux link-count rule, root-directory
requirement, one dot and dotdot per directory and the unique matching named
parent.
Its parent array is the unique `parent_projection` of the entry fold.

A locally valid parent graph may contain a disconnected cycle.
`bounded_rooted` separately requires the existing graph shape and an independent
rank sequence: root inode 2 has rank zero; every other active directory has a
positive rank at most MAX_DEPTH, exactly one more than its parent; inactive
slots have rank zero.
This predicate mentions neither traversal colors nor an execution result or
Tree certificate.

The graph constructor is complete for that bounded rank profile.
Ghost path-distance facts and uniqueness of resolved depths exclude each
runtime rejection when a witness exists.
The existing nonrecursive traversal still allocates only color/depth arrays;
ghost witness and path sequences add no runtime stack.
The public `build_parent_table` consumes an already sealed parent table and
returns no mutable parent authority.

| Constructor | Declarative admission profile | Result contract |
| --- | --- | --- |
| `ea_namespace_counts::collect` | Capacity and complete `dots_valid` | Some retains the complete counts and admission; None excludes the profile |
| `ea_namespace_parent::build` | Complete count profile, root and all `node_ok` link/parent rules | Some retains the unique source-derived parent array; None excludes the profile |
| `ea_namespace_topology::build_parent_table` | `bounded_rooted` over the sealed parent array | Some retains the same parent array and bounded ranks; None excludes any such rank witness |
| `ea_namespace_topology::build` | Parent admission and `bounded_rooted(parent_projection(index))` | Some retains that exact topology; None excludes the composed upper-stage profile |

## Design obligations and remaining composition

| Design obligation | Accomplished by these contracts | Remaining boundary |
| --- | --- | --- |
| F-PARSE / F-CODEC | Exact canonical EA header, group/index and allocated inode-slot read acceptance; reserved-slot leaf checks match the existing safety predicate | Other ext4 feature combinations and geometries |
| F-ADMIT | No false rejection for the explicit source/index and complete-index count/parent/topology profiles; non-journal reserved-slot rejection reconciled with its declarative rule | Complete EA census, payload integrity, global allocation, node/directory capture and directory-index constructor acceptance; full `ea_namespace::inspect_journal` acceptance |
| F-NAME | Exact complete-index link/parent profile and bounded rooted-graph admission | Complete raw-directory admission, mounted namespace operations, credentials and cache coherence |
| J-BOOT / J-RECOVERY | Supplies lower and upper validator-completeness prerequisites to the existing actual-EA recovery path | Universal repaired-shadow admission and repeated EA recovery-crash fresh bootstrap/raw-constructor/admission closure |
| S-ENTRY / S-RESOURCE | Total public executable APIs, sealed source certificates and existing bounded execution | Fallible allocation, source capture/exclusion and live runtime identity refinement |
| S-RACE / D-ATOMIC | Preserves the existing owned immutable host boundary and durable device-model premises | CortenMM/OSTD frame, lock, BIO/DMA and actual device/flush refinement |

## Reserved-inode admission correction

The previous EA census parsed xattr-body geometry before classifying a
non-journal reserved slot.
This rejected a Linux-clean image whose empty reserved slot carried irrelevant
`i_extra_isize` bytes, even though that slot satisfied the existing
`empty_reserved(raw) && !body_present(raw)` admission rule.
The checker now tests that exact rule directly for non-journal reserved slots.
It does not impose live-inode xattr-body geometry on an unused reserved slot.
For example, an otherwise-empty 256-byte reserved slot with `raw[128] = 1`
and no body header is admitted by this leaf check.

The unchanged empty-slot predicate requires zero mode, links, size, block count,
inode flags, external-xattr address and extent/block-map bytes.
The exact body-absence condition is also retained.
These bytes cannot grant live inode, xattr, extent or namespace authority.
Active EA values in supported reserved slots 3 and 4 are classified and checked
before the empty-reserved path; malformed active values cannot fall back to
empty-slot admission.
Unsupported quota, resize and orphan feature policies remain rejected.

Journal inode 8 retains the stricter metadata parser, regular-file type,
`i_extra_isize = 32`, zero external-xattr address and original body parsing.
Its absent-body check still covers the word at offset 160.
The correction does not weaken journal identity or journal-inode validation.

The reserved-slot leaf now has matching declarative and executable admission.
Complete census, payload-integrity, allocation, directory and namespace
constructor acceptance remain open.
The Linux-clean example identifies a false rejection in this implementation;
it does not establish a Linux defect.

Full ext4 features, multiple concurrent EA transactions and mounted writable
filesystem authority remain open.
The implementation stays in safe Rust above Asterinas's framekernel boundary.
Linux page, folio and buffer_head ownership is not imported.

## Reference and evidence

The reference remains Linux v7.0 commit
`028ef9c96e96197026887c0f092424679298aae8`, pinned in sources.json.
The existing descriptor/bitmap rules follow the recorded ext4 balloc, ialloc,
bitmap and superblock sources.
Namespace link-count and source-inode distinctions retain the references in
[EA_NAMESPACE.md](EA_NAMESPACE.md).
The reserved-slot correction also follows the distinction in e2fsprogs 1.47.0
`e2fsck/pass1.c`: unused reserved slots are skipped rather than interpreted as
ordinary live inodes.
That reference does not authorize skipping the independent empty-slot or
journal checks required by this implementation.
No Linux defect is asserted.

[Recorded evidence](verification-evidence.json) and
[proof status](proof-status.json) identify the exact whole-crate verification,
compiled artifact and native regression scope.
Native examples supplement the contracts; they do not discharge formal
obligations or establish full filesystem acceptance completeness.

## Validation of this change

The pinned unfiltered whole-crate run uses `--no-cheating`,
`--no-external-by-default` and `--compile`.
All 233 core source, manifest, runner and test inputs, plus the reference manifest, remain identical through final
verification and regression checks.

| Check | Result |
| --- | --- |
| Whole-crate formal obligations | 3142, zero errors |
| Named proof / public executable coverage | 915 / 775 across 226 sources |
| Native tests | 372, including eight new admission-stage and reserved-inode tests |
| Rust ownership and privacy rejection cases | 340, including ten new sealed-graph boundary cases |
| Verifier rejection gates / timeout cleanup regression | Six rejected / passed |

The official runners and CI remain unchanged apart from the additive literal
API cases in the compatibility runner.
Every historical false boundary and historical claim in the recorded evidence
is retained.
