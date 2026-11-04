<!-- SPDX-License-Identifier: MPL-2.0 -->

# Extent-tree preservation by admitted content writes

`extent_frame.rs` proves source framing for complete structural extent trees.
The two contexts must have identical geometry, root address and checksum domain,
with equal source lengths. The inline root and every external metadata claim
must retain their exact bytes. Under those premises, the entire checked tree,
its complete metadata/data claim sequence and every stored mapping are
preserved. This covers written extents, unwritten extents, holes and branches
that a particular lookup does not visit. Equality is byte-based; no checksum
collision or identity assumption is used.

The recursive proof follows the same complete child/claim enumeration used by
the source-bound extent validator. Every external child's own metadata claim
occurs in its subtree; restriction of the parent's frame supplies both its
unchanged source block and all descendant frames. The standalone framing result
requires physical metadata addresses to fit the current 32-bit claim type
(`blocks <= 2^32`). The actual composed volume profile remains at most 1,048,576
4 KiB filesystem blocks; wider standalone extent codecs do not relax that limit.

`write_frame.rs` discharges those premises for the actual complete final image
of `content_write::Candidate::begin_timed`. It includes all dirty-superblock,
encoded-journal, data/inode-home and retirement-tail overlays, rather than only
the two candidate home patches. The result uses the exact source and layout
retained by the admitted writer.

| Obligation | Checked result | Remaining boundary |
| --- | --- | --- |
| Physical separation | The ledger maps every reserved claim to its exact role; the primary/GDT, internal journal and each inode-table position have their distinct roles | Runtime CortenMM/OSTD ownership and mapping epochs |
| Candidate source | The initialized content target has file-data role; the selected inode table block has metadata role and cannot alias it | Authenticated VFS credentials and operation exclusion |
| Protocol frame | Blocks outside the primary, journal and home targets retain their exact source bytes through all overlays | Actual driver/device/source-capture refinement |
| External nodes | Every extent-metadata role remains byte-for-byte unchanged, including other inodes and off-path nodes | Concurrent mutation and overlapping transaction queues |
| Inline root | The final inode equals the exact timestamp/checksum reseal and its complete extent root remains unchanged | Allocation, extent insertion/removal, conversion and inode-format expansion |
| Complete tree | Rebased source context has the same valid tree, exact claims and all stored mappings | Fresh-source inode/index projection and complete file-read operation composition |

The candidate constructors now expose their journal-layout equality. Borrowing
edit parts explicitly preserves the running batch's layout and credit count,
so this relation composes through real mutable borrows, close, release and freeze.
These are proved frame contracts on the existing implementation.

Successful physical execution already equals the complete admitted image by
[WRITER_IMAGE.md](WRITER_IMAGE.md), under its declared atomic-block/flush and
quiescent-source contract. This result does not establish live-reader
publication, lock or DMA exclusion, actual hardware atomicity, general
writer-crash admission closure, or full ext4 support. No kernel path is enabled.

The host interoperability check writes content and timestamps through a
Linux-created external tree, reparses the complete allocation/namespace image,
reads the entire file including holes, and compares every external tree block
and the inline root byte-for-byte. Tests supplement the complete Verus proof.
