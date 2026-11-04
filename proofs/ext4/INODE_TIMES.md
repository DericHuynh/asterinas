<!-- SPDX-License-Identifier: MPL-2.0 -->

# Linux ext4 inode timestamp codecs

`inode_time.rs` implements Linux's signed 32-bit base seconds, two epoch bits
and 30 nanosecond bits. Canonical extended encoding admits seconds from
`-2147483648` through `15032385535` and nanoseconds below one billion. Verus
checks both value roundtripping and uniqueness of the complete encoded words.
These bounds cover Linux's 1901 through 2446 range, including every epoch boundary.

Raw decoding preserves the actual nanosecond bits, including values greater
than or equal to one billion. Canonical encoding rejects such invalid values.
Legacy encoding follows Linux's signed-seconds clamping rule, discards
nanoseconds and adds no epoch bits. A negative base with epoch zero remains
negative. The codec does not silently reinterpret old malformed epoch-three
timestamps as historical dates; the pinned Linux decoder also reads the actual
epoch bits. Filesystem maintenance policy is separate.

`inode_time_fields.rs` binds those words to the actual field offsets and declared
`i_extra_isize`. Buffer capacity alone cannot authorize reading extended fields.

| Field | Base offset | Extra-word offset | Minimum declared extra size for extra word |
| --- | --- | --- | --- |
| atime | 8 | 140 | 16 |
| ctime | 12 | 132 | 8 |
| mtime | 16 | 136 | 12 |
| crtime | 144 | 148 | 24 |

Creation time's base word additionally requires a declared extra size of 20.
Atime, ctime and mtime have legacy base words in a 128-byte inode. The local
helpers accept a 128-byte buffer or a sufficiently sized extra header whose
declared fields fit the supplied buffer. Unsupported/truncated shapes reject
without indexing outside the buffer.

The checked setter validates every fallible input before changing bytes. Success
has an exact byte-splice specification and a read-after-write theorem. Failure
preserves every input byte. Unrelated inode bytes remain unchanged. The helpers
do not update the inode checksum; an operation must reseal it after assembling
all metadata changes. A timestamp value also does not authenticate a clock or
grant VFS mutation authority.

Native checks exercise all epoch boundaries, nanosecond extremes, legacy
clamping, raw invalid nanoseconds, every declared field-presence boundary,
unchanged failed updates and preservation of unrelated bytes. Debugfs reads
the emitted post-2038 base/extra words for all four fields. After explicit inode
checksum resealing, complete image validation and e2fsck accept the image and
preserve those inode bytes.

The reference is Linux v7.0 `fs/ext4/ext4.h`'s timestamp table,
`ext4_encode_extra_time`, `ext4_decode_extra_time`, `EXT4_FITS_IN_INODE` and
`EXT4_INODE_SET_XTIME_VAL`, pinned in `sources.json`. Wider inode helpers do not
expand whole-image admission beyond the existing 256-byte, extra-size-32
profile. Timestamp/metadata write closure, VFS operations and CortenMM/OSTD
runtime integration remain separate obligations.
