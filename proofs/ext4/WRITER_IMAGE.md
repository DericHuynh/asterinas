<!-- SPDX-License-Identifier: MPL-2.0 -->

# Serialized durable writer and validated image equality

`writer_image.rs` connects the complete source retained by writer admission to
the existing serialized atomic-block device model. Its success theorem compares
the entire resulting byte image with the already validated final filesystem
image, including block zero, journal records, home images, the retired tail and
any partition bytes beyond the filesystem.

The source-map and byte-projection helpers now live in `disk_image.rs` and are
shared with the complete admitted recovery refinement in
[RECOVERY_IMAGE.md](RECOVERY_IMAGE.md).

## Checked relation

The initial physical map has exactly the filesystem block addresses. Its finite
domain is constructed from a sequence of unsigned block numbers; no assumed
finite-set constructor or local trusted specification is introduced. Each map
cell has the exact corresponding 4,096 source bytes. Its journal projection
equals the journal bytes captured by the same bootstrap source. These facts
establish the existing physical writer context from the admission certificate.

The complete validated output has the writer's dirty/log/home/tail layering.
The proofs identify its exact block values and relate them to the successful
device ledger:

| Block class | Durable result |
| --- | --- |
| Journal superblock | Retired tail image |
| Original home target | Exact frozen original image |
| Descriptor/payload/commit record | Exact emitted record, including escaped payload bytes |
| Block zero without a home update | Dirty primary image |
| Every other filesystem block | Exact initial source bytes |
| Partition bytes after the filesystem | Exact initial source bytes |

`successful_durable_writer_is_the_complete_validated_filesystem_image` proves
that flattening the successful durable map equals the certificate's entire final
source and retains its complete namespace/allocation validity. The modeled writer
has no enabled late persistence event after success. The separate constructive
theorem `every_admitted_writer_has_a_finite_validated_completion` supplies a
finite successful model execution from the actual initial writer state; this is
a failure-free witness, not a promise that a physical device cannot fail.

## Device and runtime boundary

The result uses the existing declared contract: atomic 4 KiB writes, flush
completion with its specified persistence effect and a quiescent initial device
whose bytes equal the retained source. The finite ledger and command refinement
proofs establish the model's ordering; a driver does not obtain this contract
merely by reporting ordinary write completion.

This theorem covers successful serialized writers. Earlier journal proofs retain
their documented crash-cut scope; complete filesystem certificate closure over
arbitrary writer/recovery crashes, overlapping commit/checkpoint and other atomic
unit sizes require further proofs. Source capture, physical media identity and
exclusion, runtime publication and actual device execution remain adapter
obligations. CortenMM/OSTD frame and DMA ownership must preserve the modeled
snapshots and command identities. Filesystem blocks here are disk addresses, not
Linux pages or CortenMM frame capabilities.

The proof is checked by the pinned entire-crate Verus invocation without local
assumptions or external bodies. Existing native tests independently compare the
complete six-fence output with the admitted image and exercise content plus
resealed inode-time transactions, including relocated FLEX_BG tables. Tests do
not discharge the driver contract or the remaining crash/concurrency obligations.
Production mount/write gates remain closed.
