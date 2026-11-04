<!-- SPDX-License-Identifier: MPL-2.0 -->

# 64-bit fields and group descriptors

The checked core admits ext4's 64BIT feature with 64-byte group descriptors in
its bounded 4 KiB profile. Exact wide field codecs are also available. Full
64-bit-volume allocation, other descriptor sizes, FLEX_BG, META_BG, block-bitmap initialization and allocation transitions remain
unfinished. [Lazy inode groups](LAZY_INODES.md) have a checked static interpretation.

| Component | Checked representation and boundary |
| --- | --- |
| High/low address codecs | `group_fields.rs` joins/splits 32-bit halves without truncation through `u64::MAX`. Non-wide encoding rejects values above `u32::MAX`; total readers validate offsets without wrapping. |
| High/low counter codecs | Exact 16-bit halves through `u32::MAX`; non-wide encoding rejects values above 65535. Descriptor decode binds all three metadata addresses, allocation/directory/unused counters and both bitmap checksums to their actual fields. |
| Superblock counters | The standalone codec returns complete low/high block, reserved-block and free-block values. The whole-image profile separately requires zero high count fields and enforces its resource cap; it never admits a truncated larger volume. |
| Descriptor width | The source 64BIT flag selects 64 bytes; other admitted images use 32. Superblock admission requires `s_desc_size=64` when 64BIT is present and 0 or 32 otherwise. |
| Descriptor checksum | Seed with the selected ext4 metadata seed and little-endian group number, then CRC every descriptor byte with the two-byte checksum field replaced by zeros. The low 16 bits are stored, for both widths. |
| Bitmap checksum | A 32-byte descriptor checks the low 16 bits. A 64-byte descriptor checks all 32 bits from the actual low/high fields for initialized bitmaps. INODE_UNINIT groups synthesize the logical inode bitmap and ignore its unused physical checksum. Block coverage is 4096 bytes; inode coverage is `inodes_per_group/8`. The standalone Bitmap retains its 16-bit relation, and same-source GroupMetadata additionally proves the full checksum. |
| Bounded group admission | Metadata addresses stay within the declared non-flex group, and counters fit group/inode bounds. All admitted high address/count fields are zero in this profile. A checked theorem connects the bounded values to complete wide decoding; the full-width codec remains distinct from this admission policy. |
| Source index | Descriptor `g` occupies the exact source range `4096 + g*width .. 4096 + (g+1)*width`. Width and checksum seed come from the same primary superblock. |
| Bootstrap identity | Recovery preserves the descriptor width feature, every group's low address fields, and all three high address fields for 64-byte descriptors. Journal inode 8 and its complete mapping stay fixed. |
| Composition | Complete allocation, initialized bitmaps, inode-owned extent metadata, structural reads, static namespace/image inspection and checked recovery admission compose with optional HUGE_FILE and CSUM_SEED. |

The current whole-image cap remains 1,048,576 blocks and 32 groups. Either
width fits its descriptors into one 4 KiB GDT block, so the existing sparse-super
reservation is unchanged. Wider standalone values do not establish allocation
or I/O authority. Filesystem blocks remain distinct from CortenMM frames; no
Linux page/folio/buffer_head ownership is introduced. Actual CortenMM/OSTD,
concurrent mutation and driver refinement remain open, and no mount is enabled.

Pinned Linux references in [sources.json](sources.json) cover the
`ext4_group_desc` layout and high/low accessors, `ext4_group_desc_csum`, and
full-versus-truncated bitmap checksum selection. The Rust implementation is
independent.

Host tests use native mke2fs/debugfs/tune2fs/e2fsck. They cover all combinations
of optional HUGE_FILE/CSUM_SEED with 64BIT, complete source-bound trees through
depth five, and a two-group image containing a live second-group inode to
exercise stride, initialized bitmap and high-water accounting. Negative cases
include correct checksums with unrepresentable high addresses/counters,
corrupted extended CRC coverage, bitmap high-checksum changes with a valid
descriptor checksum, wrong descriptor widths and recovery changes to
second-group high addresses. These tests complement the Verus proofs; they do
not establish full-volume, Linux-driver or device durability refinement.
