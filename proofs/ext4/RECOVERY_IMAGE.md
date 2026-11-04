<!-- SPDX-License-Identifier: MPL-2.0 -->

# Complete admitted recovery image refinement

`recovery_image.rs` connects the sealed recovery-admission certificate to the
existing physical recovery model. Successful modeled recovery produces the
entire validated filesystem byte image, including the selected home images,
retired journal superblock, unchanged journal records and all extra partition
bytes. Its completed cache is empty, so no old modeled persistence event remains
enabled.

The starting source need only satisfy the admitted bootstrap/recovery rules.
It does not have to pass complete initial allocation or namespace validation:
partially checkpointed home metadata may be inconsistent. Recovery admission
instead validates the exact selected-home plus retired-tail result before
returning dispatchable owned requests. This supports repair from committed redo
without treating inconsistent home metadata as filesystem authority.

## Proof chain

| Step | Checked result |
| --- | --- |
| Source to physical map | `disk_image.rs` constructs exactly the filesystem address domain and exact source bytes. Disk addresses remain separate from CortenMM memory capabilities. |
| Initial recovery model | The actual replay plan's targets exist in that map, exclude the journal and satisfy the existing device invariant. |
| Selected homes | The retained sorted shadow patches and Linux latest/unrevoked selected redo have identical target identities and bytes. |
| Retired tail | The same exact tail image is inserted at the actual journal superblock address. |
| Completed durable map | Flattening the stable map equals the certificate's complete final source, retaining allocation/namespace validity. |
| Extra partition bytes | Bytes beyond the filesystem remain exact; no block-number cast truncates a trailing-byte index. |
| Finite witness | A constructive failure-free issue/completion trace reaches the validated image, including empty replay plans. |

The finite witness is for the admitted recovery image set in the specified
device model. It is not a guarantee that a physical device succeeds or a reset
operation for an aborted live engine. Actual attempts must preserve the existing
owned request/state protocol and obtain an appropriate fresh source and physical
quiescence before restart.

## Remaining boundaries

The proof uses the declared 4 KiB atomic-write, flush and quiescent-source
contract. The existing recovery invariant already covers arbitrary finite
completion, persistence and abort interleavings; the complete-image result
applies when such a modeled execution reaches success. Source capture, physical
device identity/exclusion, CortenMM frame/DMA loans, actual command dispatch and
driver behavior still need concrete refinement.

This result does not establish that every writer crash snapshot passes complete
filesystem recovery admission. General filesystem certificate closure across
writer/recovery crashes, concurrent commit/checkpoint, other atomic unit sizes,
full ext4 feature coverage and mount/VFS publication remain open. Earlier
serialized crash/restart results keep their documented model and byte scope.

The pinned entire-crate Verus invocation checks every new body without local
assumptions, external bodies or filtered verification. Existing native tests
cover valid replay, repaired home metadata, invalid replay rejection, abort with
late completion, terminal sequence recovery, repeated recovery crashes and Linux
interoperability. They supplement the formal model and do not discharge its
hardware/runtime premises. Mount/write activation gates stay closed.

Complete image repairability at every admitted recovery-model cut and exact
journal preservation for unchanged tails are now checked in
[RECOVERY_CRASH_IMAGES.md](RECOVERY_CRASH_IMAGES.md). Fresh-source admission
reconstruction and runtime restart boundaries remain open.
