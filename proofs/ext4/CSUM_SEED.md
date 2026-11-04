<!-- SPDX-License-Identifier: MPL-2.0 -->

# ext4 and JBD2 checksum domains

The bounded profile admits INCOMPAT_CSUM_SEED (`0x2000`) in combination with
its existing feature set, including optional HUGE_FILE and bounded 64BIT descriptors. This is partial ext4
format coverage; the filesystem, runtime and mount obligations remain open.

| Domain | Source and checked relation |
| --- | --- |
| Primary superblock | CRC32C starts at `~0`, through byte 1020, independently of CSUM_SEED. |
| ext4 metadata | With CSUM_SEED, read `s_checksum_seed` at superblock offset 624. Otherwise derive CRC32C(`~0`, filesystem UUID). |
| Group metadata | The same-source group index and every group record retain exactly the selected ext4 metadata seed. Descriptor and bitmap checks use it. |
| Inode, directory and extent metadata | The selected seed composes with the actual inode number and generation; source-bound inode/tree and complete allocation/namespace validation retain that relation. Journal inode 8 also uses this ext4 metadata domain. |
| JBD2 records | Derive the seed from the internal journal superblock's own UUID, at journal offset 48. Descriptor UUID checks and payload/record checksums use that journal identity. |
| Filesystem identity | The filesystem UUID stays fixed across the modeled writer and recovery histories. It need not equal the internal journal UUID. |
| Recovery feature policy | Dirty/clean image construction changes only RECOVER (`0x4`) and recomputes the superblock checksum. Replay and bootstrap identity checks preserve every other incompatibility bit, including CSUM_SEED, and the stored seed bytes. |

`superblock::metadata_checksum_seed` is total: a non-1024-byte input returns
None; every 1024-byte input returns the exact feature-selected seed. Admission
still separately checks the complete superblock profile and checksum. This
helper alone conveys no filesystem authority. The theorem
`super_state::recovery_preserves_the_metadata_checksum_domain` proves that both
recovery image construction and accepted replay retain that exact seed.

`bootstrap::locate` derives the ext4 metadata seed to validate the group-zero
descriptor and journal inode. It then reads the UUID from the journal reached
through that checked inode, deriving the independent JBD2 seed. Its exact scan
source binds journal bytes, UUID, seed, layout and primary image to one retained
snapshot. `uuid()` exposes the filesystem UUID; `journal_uuid()` exposes the
internal journal UUID. The lower-level writer/recovery factories check their
UUID argument against the journal and preserve the primary volume identity
independently. Those factories are candidate command builders, not mount or
mutation authorization.

The pinned Linux references are `ext4_init_metadata_csum` in `fs/ext4/super.c`
and the JBD2 journal load checksum-seed setup in `fs/jbd2/journal.c`; exact
commits and blobs are recorded in [sources.json](sources.json). The Rust code
is independently implemented. No Linux page, folio or buffer_head ownership
model is introduced. CortenMM/OSTD guards, memory and device refinement remain
separate unfinished obligations.

Host tests use native `mke2fs`, `debugfs`, `tune2fs` and `e2fsck`, with and
without HUGE_FILE. Changing the filesystem UUID with CSUM_SEED leaves both the
stored metadata seed and internal journal UUID unchanged. Native disable/enable
transitions followed by another UUID change produce three distinct checksum
identities. The tests validate complete allocation/namespace images, owned
extent trees through depth five, journal inode discovery, writer admission and
committed recovery using the actual JBD2 domain. `e2fsck` independently replays
the emitted journal. Negative cases cover a wrong stored seed, use of the
filesystem UUID as journal identity, feature-bit switching under otherwise
valid checksums, and malformed input lengths. Tests supplement the Verus
checks; they do not prove Linux execution or device durability.
