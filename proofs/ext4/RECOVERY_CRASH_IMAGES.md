<!-- SPDX-License-Identifier: MPL-2.0 -->

# Complete filesystem repairability at admitted recovery cuts

`recovery_crash_image.rs` extends complete-image success refinement to every
state satisfying the existing physical recovery invariant. These states include
pending I/O, abort, failures and partial persistence. The theorem retains the
same exact admitted replay plan and final filesystem certificate.
`every_finite_admitted_recovery_execution_has_complete_or_repairable_crash_cuts`
composes initial admission, event preservation and both byte-image cases for all
cuts of every enabled finite event trace.

| Stable journal superblock at the cut | Checked complete-image result |
| --- | --- |
| Equal to its initial bytes | Reapply the admitted latest/unrevoked selection and retired tail; the resulting entire image equals the same validated final filesystem. Every journal byte still equals the original canonical input. |
| Different from its initial bytes | The recovery invariant identifies the persisted retirement tail. Its home fence already made all selected homes durable, so the stable image itself equals the complete validated final filesystem. |

The second branch deliberately requires an actual change from the initial
superblock. It does not infer retirement merely because old and desired bytes
happen to be equal. The first branch handles unchanged markers without assuming
they are fresh. Exact map equality and byte projection preserve the complete
namespace/allocation certificate and every extra partition byte.

The proof obtains the deterministic complete redo map's byte certificate from
the already constructed finite successful model execution. It then composes
the existing interrupted-replay and safe-retirement theorems with that exact
certificate. No local witness, checksum injectivity, external body or unproved
restart assumption is introduced.

An unchanged tail also preserves the entire mapped journal input, including all
non-superblock records and the superblock itself. This binds repairability to
the canonical log originally admitted, rather than an arbitrary replacement
plan or a numeric transaction ID alone.

These are physical-model cut results under the declared 4 KiB atomicity, flush
and initial-source contract. A valid stable image does not cancel an outstanding
request or authorize immediate log reuse: an old pending tail write could affect
a later generation. Existing quiescence, owned-completion and retirement rules
must still be respected by a runtime adapter.

The theorem does not prove that a fresh process reconstructs a complete new
bootstrap/filesystem admission from every crash source. That requires additional
source/identity/admission closure and resource-completeness proofs. It also does
not establish writer-crash filesystem closure, concurrent commit/checkpoint,
actual CortenMM/BIO/driver behavior or complete ext4 feature support. Kernel
mount/write gates remain closed.
