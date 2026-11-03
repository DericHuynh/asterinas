<!-- SPDX-License-Identifier: MPL-2.0 -->

# Linux compatibility profile

Status: planned, not implemented or verified. There is currently no supported
mount profile. This manifest is not a claim that a default mke2fs image works.

## Initial candidate

- ext4 byte format, 4 KiB filesystem blocks, 256-byte inodes, one device.
- An internal JBD2 journal with an immutable, validated mapping.
- Extent-backed regular files and linear directories; checked sparse and
  unwritten-extent reads.
- Full data journaling, synchronous bounded operations, serialized mutation.
- A deliberately restricted filesystem-size/address range until 64-bit group
  descriptors and journal tags are proved.
- No writable admission before the parser, operation, recovery, and adapter gates.

The exact mkfs feature allowlist is to be locked by the codec/admission proof.
There is no untested formatting command in this proposal.

## Feature policy

| Feature/representation | Initial decision |
| --- | --- |
| HAS_JOURNAL, FILETYPE, EXTENTS | Required candidate features; prove parser and writer. |
| RECOVER | A state condition to validate and handle; never blindly ignore it. |
| METADATA_CSUM | Planned checksum correctness and validation, not authentication. |
| SPARSE_SUPER, LARGE_FILE, EXTRA_ISIZE | Admit only after corresponding geometry/inode obligations pass. |
| 64BIT / high extent addresses | Reject outside the proved address profile until expanded. |
| FLEX_BG, META_BG, BIGALLOC | Not initially admitted. |
| DIR_INDEX / indexed-directory inode flag | Not initially admitted; do not parse an htree as a normal dirent block. |
| INLINE_DATA, encryption, verity | Not initially admitted. |
| External journal, async commit, fast commit | Not initially admitted. |
| ORPHAN_FILE and other new orphan formats | Not initially admitted; prove a specific orphan representation first. |
| Unknown COMPAT/RO_COMPAT/INCOMPAT bits | Reject in the first strict profile, including otherwise "ignorable" bits. |
| Legacy indirect mappings or special inode encodings | Reject unless explicitly covered by the profile. |

Filesystem feature masks alone are insufficient: also check inode flags, inode
types, extent encodings, journal features/tags, checksum variants, UUID binding,
and mount-state fields. A Linux-compatible subset must emit canonical ext4/JBD2
bytes with no private replacement journal format.

## Parser obligations

1. Device and partition sizes, checked byte/sector/block conversions, nonzero
   geometry, supported block and inode sizes, and descriptor-table bounds.
2. Every length and offset before indexing or allocating, including directory
   rec_len/name_len, tags, revoke records, inode extras, and extent entries.
3. Extent ordering/non-overlap, bounded depth, child validity, physical ranges,
   initialized versus unwritten lengths, holes, and i_size limits.
4. Reserved-region construction and role disjointness, including all admitted
   backup superblocks/descriptors, bitmaps, inode tables, and journal extents.
5. Byte-order conversion: ext4 fields are little endian; JBD2 is big endian.
6. CRC algorithms, correct seeds/covered bytes, UUID and sequence association,
   tag escaping, and preserve/encode rules for every admitted field.
7. Bounded traversal and resource budgets; malicious media must not cause an
   unchecked loop, recursion, allocation, out-of-partition access, or publication
   of uninitialized memory.
8. Global ownership/namespace validation or a proved alternative certificate.
   Local extent bounds alone do not rule out cross-inode block aliasing.

Validate recovery input in a shadow/overlay view before publishing the mounted
filesystem. Dirty home metadata is not necessarily a valid complete state.
A replay target from an on-disk tag must not be allowed to overwrite the journal
or escape the partition. Do not write arbitrary unvalidated replay records
before proving the allowed-target policy and recovered-state validity.

## Journal-specific obligations

Prove descriptors, flags, escaped payloads, checksums, commit records, revokes,
and journal superblock updates against Linux's admitted representation.
Prove the scan/revoke/replay relationship; revokes are not merely "last write
wins" records. Prove no earlier metadata replay can overwrite a later reused
data block.

Neither a matching CRC nor a magic/TID pair authenticates a record.
Generation, active-window, write-before-commit, and retirement properties must
establish that an accepted record belongs to the correct live transaction.
Counter wrap, stale records, delayed I/O, and circular-log reuse are mandatory
cases. The initial implementation must refuse an unproved wrap or feature
rather than extend a nat theorem to u32 by assumption.

The ext4 needs-recovery flag and journal head/tail/sequence updates require
their own crash protocol. Do not infer a clean mount from a single zero field.
A clean Linux volume may be admitted earlier than a foreign dirty journal;
unsupported recovery is rejected, never silently skipped.

## Compatibility validation after proofs

Use controlled Linux/e2fsprogs images for every admitted feature profile.
Round-trip through both implementations, run fsck, inject crashes, and compare
operation/error behavior. These checks validate the implementation/model
connection; they do not replace Verus proofs.
