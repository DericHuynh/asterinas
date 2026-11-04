<!-- SPDX-License-Identifier: MPL-2.0 -->

# Inode sizes and sparse-file bounds

Ordinary regular-file metadata, allocated inode views and structural reads use
64-bit sizes. The initialized-group profile still requires 4 KiB blocks and
does not admit HUGE_FILE or LARGEDIR. Sparse files may exceed the physical image
size; ownership and allocation account for their actual stored extents.

The reference is Linux v7.0 commit
`028ef9c96e96197026887c0f092424679298aae8`:

- ext4_isize / ext4_isize_set in fs/ext4/ext4.h, blob
  `7617e2d454ea516fee9047366458c0bda568fddf`.
- ext4_max_size in fs/ext4/super.c, blob
  `a34efb44e73d70d034aa2ed1b4011a6851235f22`.

For regular files, i_size_lo at offset 4 and i_size_high at offset 108 form one
64-bit value. Without LARGEDIR, Linux reads only the low size for other inode
types. The current directory admission policy additionally rejects a nonzero
high field. Journal inode 8 keeps its separate narrow single-extent parser;
enlarging ordinary file sizes cannot reinterpret its bootstrap mapping.

| Rule | Checked result | Remaining scope |
| --- | --- | --- |
| Field codec | Total high/low decoding and encoding with exact values; seven block sizes; explicit HUGE_FILE/LARGEDIR policy inputs | Standalone policy inputs grant no volume or inode authority |
| Maximum size | Linux's extent bound and, without HUGE_FILE, the 32-bit sector-count bound | Enabling HUGE_FILE or other geometries requires actual feature/accounting composition |
| Bound metadata | Size, UID, GID, mode, generation and links refer to the exact checked source inode | VFS credentials and runtime mutation are separate |
| Structural read | Offsets below i_size fit the logical-block type without truncation; data retain physical owner/generation/logical identity; holes/unwritten extents give zeros; reads stop at EOF | CortenMM, concurrent cache/DMA and device refinement remain open |

For block size B, the extent limit is `(2^32 - 1) * B`. Without HUGE_FILE,
Linux also limits the file to `floor((2^32 - 1)/(B/512)) * B`. For the supported
power-of-two sizes this is `2^41 - B`. Thus the current 4 KiB profile's maximum
is **2,199,023,251,456 bytes (2 TiB minus 4 KiB)**, including sparse files.
The HUGE_FILE helper policy models the larger extent limit; its presence does
not enable that feature in whole-volume admission.

The logical file offset never becomes a physical source address. A sparse read
resolves the extent relation, then uses its checked physical block and the
within-block offset. Candidate allocation traverses metadata/data extents, not
every hole or every byte of i_size. Directory enumeration retains its existing
bounded block budget before converting a count to u32.

Host cases cover 4 GiB boundaries, the exact Linux maximum, high logical
extents backed by a small image, EOF/maximum-offset clipping and malformed
high fields. A Linux debugfs-created sparse inode is checked by the reader,
whole-image validator and e2fsck. These tests supplement the Verus proofs and
do not establish a mounted-filesystem or write-operation theorem.
