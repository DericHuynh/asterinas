<!-- SPDX-License-Identifier: MPL-2.0 -->

# Content and inode-time transaction closure

`inode_touch.rs` updates ctime and mtime and reseals the actual inode checksum
for the current 256-byte, extra-size-32 metadata-checksummed profile. Its total
entry point first validates the inode number, source-selected checksum seed,
feature-dependent metadata rules and timestamp representability. Rejection
preserves every input byte. Success has an exact byte specification and proves
that metadata remains valid for the same inode identity and feature policy.

Only bytes 12–19 (ctime/mtime seconds), 132–139 (their extra words), 124–125 and
130–131 (checksum halves) may change. Mode/UID/GID, size, generation, extents,
sector accounting, other timestamps and every unrelated field remain exact.
Checksum validity follows equality of the actual zeroed-checksum byte sequence,
with the unchanged inode/generation domain. No CRC collision or authentication
assumption is used.

`content_write::Candidate::begin_timed` composes this update with its source-bound
initialized content candidate:

1. Obtain the actual retained inode bytes, metadata seed and feature policy.
2. Update and reseal the inode; locate its exact group/slot table position.
3. Copy that physical source block and replace just the selected inode's bytes.
4. Reserve the distinct data/table targets in sorted order, stage both through
   real borrowed handles, consume close/release and freeze the two exact images.
5. Enter same-source complete before/after filesystem and bootstrap validation.

The resulting writer's originals equal exactly those two specified images.
Other inodes sharing the table block retain their complete bytes. This matters
when ordinary inode 12 shares a block with reserved journal inode 8. FLEX_BG
addresses come from the actual inode group and descriptor; logical group
membership is not inferred from physical table placement.

| Obligation | Result | Remaining scope |
| --- | --- | --- |
| Timestamp fields | Exact ctime/mtime values and unrelated-field frame | Runtime clock identity/policy |
| Inode checksum | Actual source domain, recomputed checksum, metadata validity | Other inode formats/features |
| Table placement | Actual source group/slot and precise 256-byte splice | Concurrent mapping/mount epoch |
| Candidate closure | Exact two-image frozen transaction and complete result admission | Allocation, size extension, unwritten conversion and other operation closures |
| Durability | Existing serialized writer applies under its declared device model | Full filesystem/physical-ledger closure, overlapping commit/checkpoint and concrete driver |
| Security boundary | Existing regular-file, initialized ownership, DAC-input and set-ID rejection rules | Authenticated VFS handles/credentials, mount policy, CortenMM locks and DMA |

This is a verified transaction candidate with content and time metadata, not a
complete POSIX write implementation. Inode-version policy, privilege removal for
set-ID files, global operation exclusion, user-memory faults, fsync/open-file
semantics and full filesystem crash/recovery refinement remain open. The clock
and credential inputs must be bound by the eventual kernel adapter.

Native checks exercise exact resealing and unchanged rejection, one transaction
containing content plus its inode table, preservation of adjacent journal inode
8, complete static validation and Linux e2fsck acceptance. The eight admitted
64BIT/HUGE_FILE/CSUM_SEED combinations additionally exercise live inode 4097 in
a relocated FLEX_BG table. Full pinned Verus verification checks all bodies and
contracts. No kernel mount/write path is enabled.
