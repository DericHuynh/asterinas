<!-- SPDX-License-Identifier: MPL-2.0 -->

# Linux compatibility profile

Status: the following **structural parsers and canonical encoders are implemented
and Verus-checked**.
There is no admitted mount profile or production disk writer yet. The expanded
full-feature target is tracked in [FEATURE_COVERAGE.md](FEATURE_COVERAGE.md);
this document describes only the currently admitted structural subset.
The accepted byte structures do not certify the whole volume.

## Implemented structural subset

| Structure | Accepted representation |
| --- | --- |
| ext4 superblock | 1024 bytes, Linux creator OS, revision 1, 4 KiB blocks/clusters, 256-byte inodes, first data block 0, first ordinary inode 11, internal journal inode 8. |
| Geometry | Bounded block count with zero high fields, 32768 blocks/group, positive inodes/group <=32768 and divisible by 16, checked group/count/partition relationships. |
| Feature COMPAT | Exactly HAS_JOURNAL (`0x0004`). |
| Feature INCOMPAT | FILETYPE + EXTENTS (`0x0042`), optionally RECOVER (`0x4`), 64BIT (`0x80`) and CSUM_SEED (`0x2000`); all eight combinations admitted. Raw parsing surfaces RECOVER; recovery preparation requires it when the journal has a nonzero start. |
| Feature RO_COMPAT | SPARSE_SUPER + LARGE_FILE + EXTRA_ISIZE + METADATA_CSUM (`0x0443`), optionally HUGE_FILE (`0x044b`). |
| Group descriptor | 32 bytes without 64BIT, 64 bytes with it; bitmaps and inode table inside the group and locally disjoint, initialized or canonical logical block/inode bitmaps (`bg_flags` 0 through 7), bounded counters with zero high address/counter fields, and CRC32C over the complete descriptor with 16-bit checksum storage. |
| Inode | 256 bytes, extra_isize 32, live regular file/directory, EXTENTS flag, optionally HUGE_FILE when the filesystem feature is present, no ACL/xattr block, 64-bit regular-file i_size up to Linux's 2 TiB-minus-4 KiB bound without HUGE_FILE or 16 TiB-minus-4 KiB with it, low-only directory size with zero high field, Linux UID/GID high halves and inode CRC32C. |
| Ordinary inode extent tree | Inline root with up to four entries, external 4 KiB nodes at depth 0–5, exact parent/depth/key bounds and checksums; complete same-source metadata/data ownership census. Physical addresses must fit the bounded volume, despite the 48-bit codec. Written length up to 32768; unwritten length up to 32767; zero length rejected. |
| Directory | Linear 4 KiB records with FILETYPE and metadata checksum tail; live entries limited to regular files/directories; no NUL or slash in a name. |
| JBD2 superblock | Version 2, 4 KiB journal blocks, first log position 1, >=1024 journal blocks, one user, the internal journal's own UUID, no stored error/dynamic copy/fast-commit blocks. |
| Journal features | No feature bits for a clean mke2fs journal, or CSUM_V3 with optional REVOKE. A dirty journal without v3 is rejected. Unknown bits, 64-bit tags and async commit rejected. |
| JBD2 records | Canonical v3 descriptors with 1..250 16-byte tags, first-tag UUID and later SAME_UUID, one terminator and checksum tail; 32-bit revoke blocks with 0..1019 records; checked full commit images and escaped payload CRCs. |
| Allocation bitmap | Initialized or synthesized 4 KiB block/inode bitmaps, LSB bit numbering, allocated padding, exact free counts; block checksum covers 4096 bytes, inode checksum covers `inodes_per_group / 8`, with low 16-bit checks in 32-byte descriptors and complete 32-bit low/high checks in 64-byte descriptors. INODE_UNINIT groups use canonical all-free inode bits; BLOCK_UNINIT groups use canonical reserved-metadata/padding bits. The respective unused physical checksum is ignored only under its checked flag. |
| Ownership census | Candidate census for 3..1,048,576 filesystem blocks (up to 4 GiB of 4 KiB blocks), disjoint physical claims, exact bitmap agreement and free counts. This resource bound applies to the new census component; no mount profile is enabled. |
| Inode allocation binding | Root inode 2 and ordinary inodes >=11 use complete source-bound trees, inode generation and exact 512-byte `i_blocks` accounting for both data and external extent metadata, normalizing the source 32/48-bit sector or HUGE_FILE block units; without the filesystem feature the high field stays zero. Directory extents must be initialized. Journal inode 8 is reserved separately from file data. |
| Group source index | One immutable borrowed source; all groups in order, exact descriptor and initialized bitmap byte provenance, or descriptor-bound canonical empty inode bitmaps for INODE_UNINIT, aggregate free counters equal the superblock. Bounded to 32 groups; sparse-super backups reserve one superblock and one GDT block. Not a whole-volume certificate. |
| Whole-image allocation | Complete same-source logical inode-bitmap traversal; reserved inode bitmap markers 1..10 required, root inode 2 a directory, unused reserved inodes have no live mode/links/storage, no allocated inode in the declared unused table suffix, exact directory counts; metadata/journal/inode claims exactly match every valid block bitmap bit and global free counts. Namespace and recovery/mount admission remain separate. |
| Structural host reads | Ordinary allocated inode lookup from the whole-image certificate; initialized logical mapping and source/owner/generation identity; chunks clipped to block boundaries and i_size, holes/unwritten extents return zeros. Not a VFS authorization API. |
| Complete directory blocks | Exact contiguous record chain from offset 0 through 4084, including deleted records; unique complete stream, checksum tail, bounded name access, at most 510 records/block. Source/target and topology checks are composed by the namespace certificate. |
| Source-bound directory reads | Directory blocks must be initialized, fit a positive block-aligned i_size, pass the source-selected ext4 metadata/inode/generation checksum and have complete canonical records. The actual mapped source bytes and canonical record stream are proved equal. Whole-directory/namespace enumeration is separate. |
| Name index | Full (directory inode, byte-name) equality; 1..255 byte names, no NUL or slash, owned snapshots, 4096 CRC buckets, at most 64 keys/bucket and 65536 total. Limit exhaustion rejects admission; CRC equality is never name equality. These are helper resource bounds, not an enabled mount profile. |
| Directory index | Complete canonical live-entry enumeration for all allocated directories, positive block-aligned sizes, initialized blocks, source and target inode types/generations, globally unique (directory,name) keys and exact complete lookup. At most 4096 directory blocks and the name-index limits above. Dot/parent rules, link counts and rooted topology are checked separately by the namespace certificate. |
| Namespace certificate | Exact live-inode reference counts equal i_links_count; one dot at block 0/record 0 targets self, one dotdot at block 0/record 1 targets the live parent; root parent is self with no ordinary incoming directory link, every other directory has one ordinary incoming link matching dotdot. Finite depth ranks prove every directory reaches root. Regular file hard links allowed; directory hard links, orphaned live files and disconnected cycles rejected. Bounded nonrecursive graph traversal, depth at most 65536; no mount/VFS/recovery authority. |
| Lazy block groups | BLOCK_UNINIT derives reserved superblock/GDT/bitmap/table bits and padding from the actual descriptor/geometry, with exact free-count validation. Every allocated real bit has a reserved metadata claim. See [lazy block groups](LAZY_BLOCKS.md). Allocation/initialization transactions remain open. |
| Lazy inode groups | INODE_UNINIT is forbidden in group zero and requires all inodes free, zero directories and fully unused table suffix elsewhere. Stale physical bitmap/table contents cannot grant inode or directory-target access. See [lazy inode groups](LAZY_INODES.md). First-allocation and concurrent/background initialization transitions remain open. |
| Bootstrap journal discovery | Same-source primary superblock, group-zero descriptor and exact reserved inode 8; bounded journal capture before global allocation validation. Static layout preservation and recovered-shadow admission remain separate. |
| Wide group-field codecs | Exact full 64-bit low/high addresses and superblock counts, 32-bit low/high counters and bitmap checksums; total offset checks and encoding without truncation. See [group descriptors](GROUP_DESCRIPTORS.md). Whole-image admission remains bounded. |
| Standalone wide interval helpers | Overflow-safe 64-bit block intervals and 48-bit extent-start codec with exact split mapping. These descriptors alone do not establish whole-volume or mutation authority. |
| Standalone extent-node helpers | Local inline-root and external-node parsing for 1–64 KiB blocks and depth 0–5, ordered leaf/index records, 48-bit child addresses and legacy/metadata-csum tails covering eh_max. Local validation does not establish source/seed binding, graph correctness or global physical ownership. |
| Standalone source-block helpers | Owned immutable 1–64 KiB filesystem-block bytes at checked 64-bit addresses; exact source provenance across 4 KiB shadow pages and bounded byte capture. Extent-node helpers additionally bound the declared filesystem size to that snapshot. These are host buffer/source checks, not inode/feature authority, a CortenMM adapter or full mount admission. |
| Recovery bounds | One initialized journal extent of 1024..32768 blocks; at most 4096 staged payload/revoke entries, with whole-record preflight; no transaction-ID wrap; a fully occupied ring without a proved stopping boundary is rejected. |

Superblock reserved-GDT blocks and high block-count fields must be zero.
The descriptor size is 64 with 64BIT, or zero/32 without it; minimum/desired inode extra sizes are 32.
Unknown feature masks are rejected even when Linux could ignore them.
Indexed directories, legacy indirect block maps, inline data,
larger 64-bit geometry, FLEX_BG, META_BG, BIGALLOC, encryption, verity,
external/async/fast journals and ORPHAN_FILE are outside the implemented subset.
The target design may expand these restrictions only with corresponding proofs.

A controlled interoperable fixture is generated by:

~~~sh
mke2fs -F -t ext4 -b 4096 -I 256 \
  -O none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum \
  -E lazy_itable_init=0,lazy_journal_init=0 image 16384
~~~

`tools/check_compat.py` creates its own temporary image and adds a regular file
with debugfs; no existing device is formatted.
The local validation used e2fsprogs 1.47.0.
This command creates test input, not a volume safe to mount with this package.

## Checksums and generations

ext4 fields are little endian; JBD2 fields are big endian.
CRC32C follows Linux's raw accumulator convention, without an implicit complement.
The superblock checksum uses seed `~0` through offset 1020.
The ext4 metadata seed is the stored superblock field at offset 624 when
CSUM_SEED is enabled, or CRC32C(`~0`, filesystem UUID) otherwise.
Group checksums include that seed and LE group number with the checksum field zero.
Inode checksums include that seed, LE inode number and generation,
with both checksum halves zero.
Directory checksums use the inode seed and exclude the 12-byte tail.
JBD2 independently derives its seed from the journal superblock UUID, which may
differ from the filesystem UUID. See [checksum domains](CSUM_SEED.md).
JBD2 tag checksums cover the BE sequence and the **escaped** payload.
JBD2 superblock and commit checksums zero their respective checksum fields.

These relations and the executable CRC implementation are checked.
They are integrity checks, not authentication or a collision-free record oracle.
Binding caller-supplied seeds/identifiers to a validated mounted object remains
an integration obligation.

The composed model uses bounded u32 transaction IDs, stops before wrap,
and reserves MAX for a representable terminal next-tail value.
The counter helper is not authority to start a transaction.
The executable fresh-epoch selector exceeds the supplied minimum and every
header-shaped old transaction ID, irrespective of checksums, and refuses the
terminal range. The checked replay window is shorter than 32768 transactions,
so its numeric ordering agrees with Linux's signed modular ordering.
Returned scans have checked contiguous record coverage, stopping witnesses and
a unique maximal canonical prefix. The sufficient active-scan resource profile
is checked, and all writer crash snapshots satisfy it. Recovery preparation has a checked sufficient profile, satisfied by every legal
writer crash snapshot. Repeated recovery admission and serialized physical
writer histories are checked under the device contract. Actual remount, unmount
and runtime reuse enforcement remain open.
Recovery retirement uses the scan next sequence, including MAX; it does not
allocate a new epoch. Writer admission still refuses exhausted generations.

Recovery allows filesystem block zero as a target, but excludes the journal.
Its block-zero after-image must retain RECOVER, pass the ext4 checksum/profile
checks, and preserve filesystem UUID, geometry, journal identity, stored metadata
seed, all incompatibility bits other than RECOVER, and boot/reserved bytes.
Mutable counters, timestamps, mount bookkeeping and the label may change.
This local policy is not global inode/bitmap/ownership validation.

## Unfinished mount and write obligations

- Bind the checked allocation/namespace certificates to recovery/mount admission and actual VFS/OSTD state.
- Prove allocation/free counter and no-alias preservation for every mutating operation.
- Prove operation preservation of topology, link counts and directory lookup/rename, plus orphan/reclamation rules.
- Verified read/write/allocation operation preservation and transaction closure.
- Unmount ordering and actual runtime/device enforcement of serialized log reuse.
- Preservation of bootstrap group addresses and journal inode 8, and recovery validation in a shadow view before publication.
- OSTD frame/DMA/device and VFS/credential refinements.

A replay target must not escape the partition or overwrite the journal.
A locally bounded extent must not be accepted as proof that it belongs to the inode.
A zero journal start field alone must not establish a clean mounted filesystem.
No raw parser result is used to bypass these gates.

The candidate transaction encoder accepts 1..250 unique, nonjournal home targets
and emits one descriptor, escaped payloads and a commit. Its writer requires a
clean journal, selects a fresh nonwrapping epoch and stages dirty/activation/
log/commit/checkpoint/retirement commands. These host commands do not authorize
filesystem operations or enable a production disk writer.
