<!-- SPDX-License-Identifier: MPL-2.0 -->

# Source-bound namespace with EA_INODE

The EA namespace compositor extends [whole-volume allocation](EA_ALLOCATION.md)
with complete directory contents, typed names, exact link references and a rooted
directory graph.
It retains the actual EA-enabled allocation certificate and its source bytes;
it does not clear the EA_INODE feature or construct an ordinary-profile volume.
The owning wrapper retains `allocation`, `index` and `tree`; its
`NamespaceView` binds `index.volume == allocation` and `tree.index == index`
and requires all three certificates to be valid.
A successful namespace result describes an immutable, bounded source image.
The recorded whole-crate verification evidence determines which implementation
and named obligations have been checked.
The namespace implementation and proof contracts are included in the pinned
entire-crate verification and compilation run. Native evidence adds 23
namespace regressions and 16 ownership/privacy misuse rejections; tests do
not discharge formal obligations.

This layer does not authorize mounting or filesystem operations.
The mapped internal journal still requires actual JBD2 identity, state and
recovery admission.
Runtime credentials, concurrent namespace mutation, durable namespace updates
and CortenMM/OSTD/device refinement remain separate obligations.

| Design component | Implementation and contract | Remaining boundary |
| --- | --- | --- |
| `ea_namespace_nodes.rs` | Inode-number-indexed table containing exactly every supported ordinary source inode, with exact mode, links and generation; no EA, journal or empty reserved slot becomes an active namespace node | Credential authority, cache freshness and runtime inode lifecycle |
| `ea_directory.rs` | Every logical block through directory EOF is an exact borrowed initialized source mapping, globally owned by that directory; complete canonical pieces and source-bound HTree validation | Concurrent directory updates, crash protocols and broader directory-layout support |
| `ea_directory_index.rs` | Every ordinary directory and every nonzero canonical source record is enumerated; target type and generation agree with exact ordinary source metadata; full byte-string keys are unique | VFS lookup, symlink traversal, mount crossings, casefold and encryption semantics |
| `ea_namespace_counts.rs` | Complete entry fold counts references, canonical dot records, non-dot incoming directory edges and their parents | Mutable link-count updates and atomic cross-directory rename |
| `ea_namespace_parent.rs` | Source link counts obey exact regular counts or the Linux DIR_NLINK directory rule; every directory has canonical dots and one matching named parent, with the root exception | A locally valid graph alone does not establish rootedness |
| `ea_namespace_topology.rs` | Bounded nonrecursive graph validation assigns checked depths, rejects cycles and proves every source directory reaches inode 2 | Runtime lock ordering, concurrent ancestry changes and recovery of partial namespace mutations |
| `ea_namespace.rs` | Owns and binds the allocation, complete directory index and rooted topology to the same source image | Actual JBD2 state/recovery admission and full EA filesystem admission |

## Exact ordinary inode membership

The node table is indexed by source inode number and covers every declared slot.
An active table slot matches one exact ordinary entry retained by
`ea_allocation`: its inode number, mode, positive source link count and generation
come from that ordinary inode's source bytes.
Conversely, every retained ordinary inode has its active table slot.
A caller cannot obtain a smaller accepted namespace by omitting an allocated
ordinary inode or supplying a duplicate catalogue entry.

The allocation layer classifies supported modern EA inodes separately, including
EA values in supported reserved slots 3 and 4.
Journal inode 8 is also separate.
Ordinary metadata accepts only supported regular-file and directory modes and
rejects the EA inode flag.
Those source classifications are preserved through namespace construction.
A directory record that targets an EA value, the journal, an unallocated slot or
an empty reserved slot therefore fails typed-target validation, even if its
`file_type` claims an ordinary regular file.

Generation numbers are exact source metadata, not a caller-supplied identity.
A successful lookup retains both the source inode number and that generation.
These immutable facts do not establish runtime freshness after inode reuse.

## Complete physical directory capture

Each directory must have positive block-aligned `i_size` within the supported
bounds.
For every logical block from zero through `i_size / 4096 - 1`, the constructor
reaudits the ordinary inode's complete extent tree, finds an initialized mapping
and checks its entry in the final global ownership ledger.
The role must be initialized directory data owned by the exact source inode and
generation at that logical block.
The retained parser input is exactly that physical source block's byte slice.

Distinct logical directory blocks have distinct physical sources.
The whole-volume ledger also excludes aliases with other directories, regular
files, EA values, extent metadata, fixed metadata, external xattr blocks and the
journal.
Neither an arbitrary caller-provided block list nor an independently valid
directory block can establish this ownership relation.

This namespace profile requires every directory data extent to end within its
declared block-aligned `i_size`.
Together with one checked mapping for every logical block, this captures the
complete admitted directory data allocation.
It conservatively rejects extra initialized directory data beyond EOF instead
of leaving those allocated bytes outside the namespace catalogue.
This is a supported-profile restriction, not a claim that every Linux directory
has that shape.
Regular-file holes, unwritten extents and allocations beyond EOF remain governed
by the allocation layer and are not changed by this directory policy.

Every captured block has the source-selected parser interpretation.
Linear blocks retain complete canonical directory records, including inode-zero
unused records; unused records do not become namespace entries.
For indexed directories, the root, internal index blocks and leaf blocks retain
their distinct parsed roles.
The source inode's actual indexed flag is preserved.
HTree validation uses all captured raw blocks, the actual superblock hash seed,
source signed/unsigned hash selection, actual LARGEDIR capability and the
inode-number/generation-derived metadata checksum seed.
Existing HTree topology, hash-range and collision-continuation proofs are reused.
An indexed source directory cannot silently become a linear catalogue.

## Complete names and source projection

The directory catalogue has exactly one slot for each ordinary source inode.
A slot contains a checked directory if and only if that source ordinary inode
is a directory.
The retained directory list is exactly the nonempty catalogue projection.
The entry list is the complete projection of nonzero canonical records from
those directories, in ordinary-inode, logical-block and record order.
Index blocks have no live name records; inode-zero records are skipped without
ending the scan.

Each entry identifies its source directory, logical block and canonical record,
full name bytes, target inode number, target generation and file type.
Every source directory and every target must be an active ordinary node.
The supported directory-entry types are regular file 1 and directory 2, and each
must agree with the target's actual source mode.
Names are byte strings with the parser's length, NUL and slash restrictions;
UTF-8 is not assumed.

The name set compares the full `(directory inode, name bytes)` key.
Hash equality does not establish name equality.
A positive lookup names an actual retained source entry with the exact target
type and generation.
A negative lookup excludes that full key from the complete source-record
projection.
This conclusion requires both the constructor's exact catalogue completeness and
the block/directory projection relations; uniqueness of a supplied name set
alone would not establish source absence.
The indexed HTree order and flat logical-block enumeration need not be equal;
both are bound to the same complete source blocks and canonical records.

## Link references, parents and rootedness

The reference fold counts every live source entry whose target is an inode,
including `.` and `..`.
A regular file's stored positive source link count equals its exact reference
count.
The DIR_NLINK feature does not weaken that rule.
For directories only, source `i_links_count == 1` with DIR_NLINK means an unknown
count and still requires at least two actual references.
All other supported directory counts are exact.

Canonical `.` targets its own directory with directory type and occupies record
zero of logical block zero.
Canonical `..` has directory type and occupies record one of that block.
Each directory has exactly one of each.
For linear directories these are canonical record positions; the proof does not
infer a fixed byte offset for the second record.
Each nonroot directory has exactly one non-dot incoming directory edge, and its
source `..` target equals that edge's source directory.
Root inode 2 has `..` equal to itself and no named incoming directory edge.
Regular hard links may have several containing directories.

These local rules still permit a disconnected directory cycle.
The topology validator separately follows the complete parent graph using colors
and checked ranks, rejecting unresolved cycles and excessive depth.
The root has depth zero; every other active directory has positive depth exactly
one above its parent.
A recursive proof over that decreasing depth establishes that every admitted
directory reaches inode 2.

Regular-file reachability also needs a separate composition step.
Its positive exact reference count implies that an actual entry targeting it
exists in the complete source entry list.
Typed entries and canonical dot rules make that witness a non-dot regular-file
entry in an admitted directory.
The containing directory reaches the root by the topology theorem.
Thus every admitted ordinary regular file has at least one rooted source path;
this does not impose a unique parent on regular hard links.
Inactive namespace slots have no directory references.

## Bounds and remaining authority

The inherited source profile uses 4 KiB blocks and 256-byte inodes, at most 32
groups and at most 1,048,576 filesystem blocks/inodes.
The namespace admits at most 4,096 directory blocks in aggregate, at most 65,536
full keys and a parent depth at most 65,536.
Existing name-set collision bucket bounds also apply.
Capacity exhaustion or unsupported metadata returns no certificate; a partial
scan cannot become a successful namespace.
These logical bounds do not prove allocation success or exact runtime heap use.

This remains a conservative Linux-compatible subset.
Unsupported on-disk feature combinations and inode types reject admission.
Full ext4 feature coverage, Linux-wide acceptance completeness and preservation
under arbitrary Linux writers are not established.
The implementation is independent safe Rust and imports no Linux
page/folio/buffer-head ownership model.
Its eventual kernel adapter must preserve Asterinas's framekernel boundary and
refine CortenMM/OSTD frame ownership, synchronization and device ordering.

No namespace operation, rename, allocation/reclamation, xattr update or durable
transaction is authorized by the immutable certificate.
Checksums provide the source integrity relations specified by the parsers; they
do not authenticate a hostile storage device or solve concurrent byte changes.
Actual source capture/freshness, CortenMM integration, dentry/inode cache coherence,
credential checks and locking need runtime refinement.
The internal journal mapping does not establish JBD2 contents, sequence, replay,
commit/checkpoint state or crash closure for this namespace.
Full EA filesystem admission, kernel integration, full-feature and writable-mount
gates remain false until those layers are composed and verified.

## Linux reference semantics

The reference remains Linux v7.0 commit
`028ef9c96e96197026887c0f092424679298aae8`.
`fs/ext4/inode.c` `check_igot_inode` distinguishes ordinary inode lookup from
`EXT4_IGET_EA_INODE`, and `__ext4_iget` checks reserved/special inode access.
The namespace's ordinary/EA separation follows that distinction.
`fs/ext4/namei.c` `ext4_inc_count` and `ext4_dec_count` describe the directory
link-count sentinel; regular-file reference checks remain exact.
Directory record, HTree and hash semantics continue to use the pinned
`fs/ext4/dir.c`, `namei.c`, `hash.c` and supporting format definitions.
The admission restrictions above deliberately state where the supported source
profile is narrower than Linux.
