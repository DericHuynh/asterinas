<!-- SPDX-License-Identifier: MPL-2.0 -->

# HTree block codecs and routing

The standalone host codec reads Linux HTree roots and internal index nodes over
1–64 KiB blocks. It does not enable DIR_INDEX in full filesystem admission.
Complete source/tree/hash/name admission is composed separately in
[HTree admission](HTREE_ADMISSION.md). Mutation and kernel runtime integration
remain open.

The format and routing reference is Linux v7.0 commit
`028ef9c96e96197026887c0f092424679298aae8`, `fs/ext4/namei.c`: dx_root,
dx_node, dx_countlimit, dx_entry, get_dx_countlimit, ext4_dx_csum, dx_probe and
ext4_htree_next_block. This is an independent safe Rust implementation using
immutable borrowed bytes; no Linux page/folio/buffer-head ownership is imported.
CortenMM/OSTD source capture, mapping, locking and device refinement remain open.

| Component | Implemented and checked | Remaining work |
| --- | --- | --- |
| Root header | Exact dot/dotdot forms and inode bounds, information offset/size, recognized hash IDs, reserved bytes, ordinary/LARGEDIR depth limits | Source inode/parent/feature coupling in complete directory admission |
| Internal header | Fake unused dirent and full-block record length, including Linux 64 KiB encodings | Full tree role/depth and reuse/cycle exclusion |
| Table | Exact geometry-selected capacity, positive bounded count, sorted raw hash boundaries, masked 28-bit positive logical children in the directory range | Whole tree edges, total leaf census and initialized owned physical mappings |
| Checksum | Linux used-prefix plus tail-reserved/zero-checksum domain, optional metadata checksum profile | Source-derived inode/generation seed authority in full admission |
| Initial routing | Total binary search returns the unique greatest raw boundary not exceeding the hash | Hash computation and full-key leaf lookup equivalence |
| Collision continuation | Exact next-boundary base-hash test, separate from initial search; odd continuation boundary lies above its even base hash | Multi-level next traversal, collision-chain completeness and leaf hash ranges |

The first entry's hash word is overlaid with count/limit and has effective hash
zero. Child block words reserve four upper coalesce bits; the returned logical
block masks them as Linux does. Neither a child integer nor a parsed index is
filesystem, allocation, credential or I/O authority.

An HTree checksum covers bytes through the used entries, followed by the tail's
reserved word and a zero checksum word. Unused table slots are excluded. Native
regressions check this domain, counts, sortedness, collisions, masked pointers,
invalid headers, depth limits and both checksum profiles at all seven block
sizes. A Linux-created directory is indexed with e2fsck -D; its root, inode-seeded
checksum, logical edges and leaf checksums are checked against the codec. The complete source adapter now additionally checks all names, hash ranges and
whole-image namespace admission; see HTREE_ADMISSION.md.
