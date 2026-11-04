<!-- SPDX-License-Identifier: MPL-2.0 -->

# Source-bound initialized content replacement

`content_write.rs` constructs a private candidate for a regular file's existing,
initialized extent mapping. It binds the actual allocated inode, source,
generation, logical block, physical allocation owner and exact captured input
prefix. It is a content-update primitive used to build later filesystem
operations. It does not implement POSIX write/open or authenticate credentials.

## Checked contract

The requested prefix ends at the first filesystem-block boundary, EOF or end of
input. Empty input, EOF and overflowing/out-of-range offsets return no candidate.
Holes and unwritten mappings are rejected. The primitive preserves every byte
outside that prefix in the selected block and produces only one data after-image.
Every replacement byte stays in that same logical block. Candidates for distinct
physical blocks commute when applied to their shared immutable source.
The complete source allocation certificate supplies initialized ownership of the
actual inode/generation/logical block; a caller cannot redirect the patch to a
directory, bitmap, journal, extent node or another inode.

The DAC check uses the actual inode mode/owner and supplied credential inputs.
The kernel must bind those inputs to current authenticated filesystem credentials,
mapped groups and capabilities. This module does not turn caller-supplied numbers
into authority. Directories and files with either set-ID bit are rejected; there
is no implicit permission to retain privileged bits after changing executable
content. Full operation policy must implement the Linux privilege-removal rules.

| Boundary | Current result | Remaining obligation |
| --- | --- | --- |
| Inode and mapping | Actual source-bound allocated regular inode and initialized owned extent | Runtime extent lock, mapping epoch and CortenMM loan |
| Input bytes | Owned exact clipped snapshot, independent of later input mutation | User-memory copying/fault/prefix contract |
| Patch bytes | Exact replacement inside the requested span; all surrounding bytes preserved | Allocation, unwritten conversion, size extension and tree mutation |
| Permission inputs | Source mode/owner DAC predicate; directories/set-ID files rejected | Authenticated credentials, VFS handles, mount policy and privilege removal |
| Writer construction | Consumes candidate into reserved handle/close/freeze and same-source complete writer admission | Global operation gate, commit/checkpoint overlap and physical media binding |
| POSIX write | Not implemented | Remaining inode-version/metadata policies, errors, open/fsync semantics and observable results |

`Candidate::begin` consumes the candidate and constructs a real one-slot edit
handle, stages the owned image, consumes close, freezes the batch, and enters
`writer_admission::prepare` with the same source and journal layout. Its checked
result retains complete before/after validation and exactly that original image.
No I/O occurs during planning or failed admission.

Linux v7.0 `fs/ext4/inode.c`, especially `ext4_journalled_write_end`, separates
copied bytes, block initialization, inode-size changes, metadata dirtying and
journal completion. This primitive covers existing initialized content only;
the timed path includes ctime/mtime and checksum closure, while other inode changes need broader operation closure. The algorithm
uses owned Rust bytes and the framekernel design's future CortenMM/OSTD adapter;
Linux folio/page/buffer-head ownership is not imported.

Native checks cover unaligned and full-block requests, boundary/EOF clipping,
unchanged surrounding bytes, changed caller input, directory/DAC/set-ID rejection,
holes/unwritten extents and same-source writer execution with e2fsprogs. These
checks supplement the pinned complete Verus proof run. No mount or VFS mutation
path is activated.

`Candidate::begin_timed` now adds exact source-bound ctime/mtime and inode-checksum
updates to the same journal batch as the content image. See
[WRITE_METADATA.md](WRITE_METADATA.md) for its checked table placement, adjacent
inode preservation and two-image transaction contract. Full POSIX/VFS and
runtime operation semantics remain open.
