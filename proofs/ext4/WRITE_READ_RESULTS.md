<!-- SPDX-License-Identifier: MPL-2.0 -->

# Exact file reads after admitted timed writes

The result theorem is pointwise over every byte below the original inode size.
For an admitted initialized overwrite with input prefix `data` and offset `off`,
reads from a valid result allocation image return `data[q - off]` when
`off <= q < off + data.len()`, and the original logical file byte everywhere
else. The file size, inode number/generation, mode, owners, link count and all
extent mappings remain unchanged. The timestamp/checksum update retains its
existing exact byte specification.

`file_read::byte_at` defines the logical byte from the unique initialized
mapping, or zero for a hole/unwritten mapping. The actual executable `chunk`
contract now proves every returned data byte and every zero chunk agrees with
that model. Its existing block/EOF clipping and End result are preserved. The
write theorem composes with these executable read contracts; it is not based on
an unchecked read oracle.

`write_result.rs` accepts any independently validated allocation certificate
whose retained source equals the actual admitted final writer bytes. It does
not assume that certificate has the old inode coordinates or mappings:

1. Frame the primary recovery-state image and the complete descriptor block.
2. Decode equal geometry, feature-selected descriptor width/checksum seed and
   exact group descriptor addresses from both retained sources.
3. Recompute the inode's group/slot/table coordinate in the new image.
4. Preserve its logical inode allocation bitmap. Initialized bitmaps use exact
   physical source bytes; INODE_UNINIT groups use their canonical logical bytes.
   The bitmap cannot overlap the selected inode table, data, primary or journal.
5. Project the exact resealed inode from the result source, preserving every
   field used by reads, its checksum domain, root coordinate and depth.
6. Transfer complete-tree mappings, then prove the requested bytes, untouched
   bytes in the same block, untouched initialized blocks and zero reads.

FLEX_BG physical placement, optional 64-byte descriptors, HUGE_FILE accounting
and CSUM_SEED remain selected by the actual source. A matching CRC never serves
as a source, inode or block identity proof. Filesystem blocks remain distinct
from CortenMM frames and Linux memory objects.

| Obligation | Checked result | Remaining scope |
| --- | --- | --- |
| Inode projection | Actual result allocation bit, group/slot/table coordinate, read fields, generation, extent context and depth | General static-validator completeness and source-capture refinement |
| Logical mappings | Original and independently validated result inode have exactly the same initialized mappings | Allocation, conversion, insert/split/truncate and other inode formats |
| Read implementation | Actual data/zero chunks equal the pointwise logical byte model, with existing EOF/block clipping | VFS handles/credentials and CortenMM read/DMA adapter |
| Write result | Exact input prefix; every other file byte unchanged, including holes/unwritten extents | Full POSIX writes, extending files, user-memory faults and other metadata policies |
| Durability | The actual successful writer media yields the exact logical file-byte result; no later model persistence is enabled | Concrete atomicity/flush/driver contract, crashes and concurrent publication |

The complete after-image is still actually inspected by writer admission. This
result proves observable file bytes through that admitted result; it does not
prove full operation/admission completeness or enable a kernel write path.
Authenticated credentials/clock, live-reader exclusion, mapping epochs,
concurrent commit/checkpoint, writer-crash admission closure and actual
CortenMM/OSTD/BIO refinement remain open. Full ext4 on-disk feature coverage
remains the expanded target in FEATURE_COVERAGE.md.

The existing host checks cover whole-file reads, initialized/hole/unwritten
semantics, clipping, native external trees and timestamp/checksum interoperability.
They supplement the pinned entire-crate Verus proof and emitted-code compilation.
