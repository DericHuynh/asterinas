<!-- SPDX-License-Identifier: MPL-2.0 -->

# Fresh journal discovery after interrupted recovery

`recovery_bootstrap.rs` proves bootstrap admission for the byte image of every
state satisfying the admitted recovery-device invariant. Induction over the
actual enabled event relation supplies that invariant for every cut of every
finite recovery trace, including pending requests, errors, abort and partial
persistence. `bootstrap::locate` needs only the fresh immutable source at runtime;
it does not need the previous engine or replay plan to discover the journal.

The proof is conditional on the existing 4 KiB failure-atomic write, flush and
quiescent initial-source model. A runtime reset/capture adapter must still bind
its actual bytes and outstanding effects to that model.

| Obligation | Checked result | Remaining boundary |
| --- | --- | --- |
| Whole-block projection | Every complete present disk block and mapped journal snapshot equal the flattened source bytes | Actual driver/source capture |
| Replay cut bytes | Each non-journal cut block is its exact old block or the validated complete redo block | Torn writes outside the declared atomicity contract |
| Bootstrap identity | Primary geometry, descriptor width, FLEX_BG selection and metadata checksum domain stay fixed; group-zero table address stays fixed | Dynamic resize/journal relocation |
| Fresh locator | Complete old/new primary and GDT mixtures, with the exact journal inode, remain admitted; locator completeness guarantees successful discovery | General filesystem/recovery admission completeness |
| Shared inode-table block | Static ownership separates the table from the journal header; the exact inode-8 slice survives even when another inode in that block is replayed | Runtime mapping epochs, locks and DMA |
| Canonical scan input | An unchanged retirement tail preserves the entire exact journal and hence the same fresh canonical scan source, including UUID/seed/sequence/layout | Fresh scan/recovery preparation and full admission composition |

The final validated allocation image supplies a valid bootstrap with the same
locator geometry. At a cut, primary and GDT blocks may independently be old or
new. Their checksums are inherited from those complete blocks. Exact immutable
identity fixes geometry/features and inode-table addresses; no CRC collision or
identity assumption is used.

The selected inode table cannot alias the journal header: the complete result
census gives it metadata role 3 and the internal journal role 2. Its persisted
block is old or new, and bootstrap identity keeps inode 8's full 256 bytes equal
in both. Other inodes in that block may change. The cut source therefore keeps
the journal inode even when its containing block is replayed.

`bootstrap_frame.rs` checks these source/format facts independently of the device
machine. `disk_image.rs` connects complete physical blocks and mapped journals
to source ranges. `recovery_bootstrap.rs` composes those facts with the admitted
plan and physical invariant, then with all finite enabled event traces.

The native repeated-recovery case now logs a primary update, a checksummed GDT
flag update, a repair for an initially inconsistent home bitmap, a timestamp and
checksum update to inode 12 sharing inode 8's table block, and file data. It
rediscovers and prepares recovery from each tested crash source, checks exact
journal preservation before retirement, and checks Linux recovery and final
metadata bytes. This test supplements the universal proof.

This closes fresh bootstrap discovery for admitted recovery-model cuts. It does
not prove construction of a complete filesystem/recovery admission after every
crash, writer-crash bootstrap closure, runtime I/O cancellation/quiescence,
concurrent commit/checkpoint, CortenMM/OSTD/BIO refinement or full ext4 feature
coverage. A valid cut image or successful locator does not authorize log reuse
with outstanding requests. Kernel mount/write gates remain closed.
