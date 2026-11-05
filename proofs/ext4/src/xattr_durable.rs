// SPDX-License-Identifier: MPL-2.0

//! Conditional durability/crash closure for the entire xattr patch set.
//! The primary's precommit recovery marker is framed separately from its
//! journalled allocation counters and EXT_ATTR feature promotion.

use vstd::prelude::*;
use crate::{disk_image, layout::JournalLayout, patch_set, replay_refinement::{self, Disk},
    transaction::{self, TransactionView}, transaction_refinement, write_device::{self, Machine},
    write_io::Images, write_media, write_recognition, write_recovery, writer_admission::{self, AdmissionView}, xattr_lifecycle::{self, UpdateView}};

verus! {

pub open spec fn admitted(v: UpdateView, a: AdmissionView, images: Images) -> bool {
    xattr_lifecycle::valid(v) && writer_admission::valid(a, images) && a.boot.source == v.grant.node.volume.index.source
        && images.tx.original == v.patches && images.tx.layout == v.grant.node.volume.journal
}
pub proof fn completed_xattr_transactions_have_every_exact_durable_home_and_a_retired_log(v: UpdateView, a: AdmissionView, images: Images, machine: Machine)
    requires admitted(v, a, images), write_device::inv(machine, images.tx.payloads.len()), machine.io.phase is Done, !machine.io.pending, !machine.io.faulted,
    ensures write_media::disk(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images)[images.journal_block] == images.tail,
        forall|i: int| 0 <= i < v.patches.len() ==> #[trigger]
            write_media::disk(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images)[v.patches[i].block] == v.patches[i].image,
{ crate::xattr_commit::completed_xattr_transactions_have_every_exact_durable_home_and_a_retired_log(v.patches, a, images, machine); }

pub proof fn every_recovered_nonprimary_xattr_home_uses_the_same_commit_decision(v: UpdateView, a: AdmissionView,
    images: Images, machine: Machine, layout: &JournalLayout, scan: &crate::scan::Scan, recovery: crate::recovery_device::Machine, tail: Seq<u8>, i: int)
    requires admitted(v, a, images), write_device::inv(machine, images.tx.payloads.len()), layout.wf(), layout.view() == images.tx.layout,
        write_recovery::returned(scan, write_recovery::source(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images, layout)),
        crate::recovery_device::inv(recovery, write_media::disk(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images), scan.plan(), images.journal_block, tail),
        recovery.io.phase == 4, !recovery.io.faulted, !recovery.io.pending, 0 <= i < v.patches.len(), v.patches[i].block != 0,
    ensures recovery.stable[v.patches[i].block] == if machine.stable.contains(6 + images.tx.payloads.len()) { v.patches[i].image }
        else { disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks)[v.patches[i].block] },
{ crate::xattr_commit::every_recovered_nonprimary_xattr_home_uses_the_same_commit_decision(v.patches, a, images, machine, layout, scan, recovery, tail, i); }

proof fn primary_facts(a: AdmissionView, images: Images)
    requires writer_admission::valid(a, images),
    ensures write_recognition::context(disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images),
        crate::write_io::valid_images(images), write_media::targets_exist(disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images), transaction::wf(images.tx), images.journal_block > 1,
        disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks).dom().contains(0),
        disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks)[0] == a.boot.source.subrange(0, 4096),
        crate::super_state::preserves(disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks)[0], images.dirty),
{
    hide(crate::crc::fold);
    crate::writer_image::an_admitted_source_supplies_the_physical_writer_context(a, images);
    reveal(writer_admission::valid); reveal(crate::write_io::valid_images);
}
proof fn plan_indices(plan: &crate::replay::ReplayPlan)
    requires plan.refines(),
    ensures replay_refinement::indices_valid(plan.log(), plan.selection()),
{
    assert forall|p: int| 0 <= p < plan.selection().len() implies #[trigger] plan.selection()[p] < plan.log().len() by {
        assert(crate::replay::latest(plan.log(), plan.revocations(), plan.selection()[p] as int));
    }
}
proof fn activation_precedes_a_stable_commit(machine: Machine, count: nat)
    requires write_device::inv(machine, count), machine.stable.contains(6 + count),
    ensures machine.stable.contains(2),
{
    assert(machine.issued.contains(6 + count));
    assert(6 + count <= crate::write_protocol::completed_count(machine.io, count));
    assert(write_device::is_write(2, count) && write_device::fence_after(2, count) < crate::write_protocol::completed_count(machine.io, count));
}

#[verifier::rlimit(40)]
pub proof fn every_recovered_primary_xattr_home_has_old_counters_or_the_exact_committed_image(v: UpdateView, a: AdmissionView,
    images: Images, machine: Machine, layout: &JournalLayout, scan: &crate::scan::Scan, recovery: crate::recovery_device::Machine, tail: Seq<u8>, i: int)
    requires admitted(v, a, images), write_device::inv(machine, images.tx.payloads.len()), layout.wf(), layout.view() == images.tx.layout,
        write_recovery::returned(scan, write_recovery::source(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images, layout)),
        crate::recovery_device::inv(recovery, write_media::disk(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images), scan.plan(), images.journal_block, tail),
        recovery.io.phase == 4, !recovery.io.faulted, !recovery.io.pending, 0 <= i < v.patches.len(), v.patches[i].block == 0,
    ensures if machine.stable.contains(6 + images.tx.payloads.len()) { recovery.stable[0] == v.patches[i].image }
        else { crate::super_state::preserves(a.boot.source.subrange(0, 4096), recovery.stable[0]) },
{ crate::xattr_commit::every_recovered_primary_xattr_home_has_old_counters_or_the_exact_committed_image(v.patches, a, images, machine, layout, scan, recovery, tail, i); }

pub proof fn every_writer_cut_recovers_all_xattr_metadata_together(v: UpdateView, a: AdmissionView,
    images: Images, machine: Machine, layout: &JournalLayout, scan: &crate::scan::Scan, recovery: crate::recovery_device::Machine, tail: Seq<u8>)
    requires admitted(v, a, images), write_device::inv(machine, images.tx.payloads.len()), layout.wf(), layout.view() == images.tx.layout,
        write_recovery::returned(scan, write_recovery::source(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images, layout)),
        crate::recovery_device::inv(recovery, write_media::disk(machine, disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks), images), scan.plan(), images.journal_block, tail),
        recovery.io.phase == 4, !recovery.io.faulted, !recovery.io.pending,
    ensures forall|i: int| 0 <= i < v.patches.len() ==> (if machine.stable.contains(6 + images.tx.payloads.len()) {
            #[trigger] recovery.stable[v.patches[i].block] == v.patches[i].image
        } else if v.patches[i].block == 0 { crate::super_state::preserves(a.boot.source.subrange(0, 4096), recovery.stable[0]) }
        else { recovery.stable[v.patches[i].block] == disk_image::initial_disk(a.boot.source, images.tx.layout.fs_blocks)[v.patches[i].block] }),
{ crate::xattr_commit::every_writer_cut_recovers_all_xattr_metadata_together(v.patches, a, images, machine, layout, scan, recovery, tail); }

}
