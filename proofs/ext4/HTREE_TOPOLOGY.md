<!-- SPDX-License-Identifier: MPL-2.0 -->

# Complete logical HTree topology

`htree_topology.rs` checks a complete 4 KiB metadata-checksummed HTree's supplied
logical block array. It supports the root and zero through two internal levels,
validates every referenced leaf's complete directory record chain and checksum,
and rejects reuse, cycles and unreferenced supplied logical blocks.

This certifies logical reachability and record structure. Physical extent/BIO
identity, hash-range/name lookup equivalence, inode target allocation, namespace
consistency and VFS authority still require composition with the filesystem.
DIR_INDEX admission therefore remains closed. This host object does not replace
CortenMM/OSTD snapshot, ownership, locking or device refinement.

| Component | Implemented contract | Remaining work |
| --- | --- | --- |
| Source array | Exact immutable bytes for every supplied 4 KiB logical block, bounded at 65,536 blocks | Retained filesystem extent/source and CortenMM physical mapping authority |
| Root/internal traversal | Exact source-selected edges, complete child-prefix recursion and ordinary/LARGEDIR depth limits | Hash bounds and full-key routing/lookup equivalence |
| Leaves | Canonical complete directory record chains, inode-number bounds and inode-seeded CRCs | Target inode type/allocation and namespace topology |
| Logical role census | One disjoint claim per reached index or leaf; all supplied logical blocks claimed | Physical allocation census and mutation/reclamation |
| Published graph | Private checked root/census/source witness; total role queries; named reachability and no-reuse proofs | Full DIR_INDEX admission, create/unlink/split/merge and journalled operation closure |

The recursive claim projection starts at the exact supplied root and appends all
of each source index's children in order. Construction goes through the same
checked finite disjoint ledger used elsewhere, in a separate logical namespace.
The graph never exports that ledger as physical-filesystem authority. A private
spare slot supports the ledger's minimum capacity for a two-block directory; it
is outside the reported logical block count and cannot be queried as a directory
block. A complete
final role scan excludes orphan blocks; a ledger claim collision excludes reuse
by two tree paths, including repeated index/leaf roles. Checksums are not used
as byte identity or as an injectivity assumption.

Native tests include a Linux e2fsck-D index, all supplied directory blocks, nested
three-level trees, ordinary/LARGEDIR limits, orphan blocks, repeated children,
cycles and unchecked/corrupt leaves. Equal bytes in distinct logical slots are
permitted; physical block alias exclusion belongs to the source/extent adapter.
All claims remain scoped by the exact pinned whole-crate verification evidence.
