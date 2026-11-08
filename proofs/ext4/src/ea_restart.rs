// SPDX-License-Identifier: MPL-2.0

//! Guarded cold restart of an admitted EA recovery target.
//! The anchor retains the original immutable source and only redo/tail images.
//! Each new capture runs raw bootstrap, scanning and full repaired namespace
//! validation, then compares the entire repaired target in bounded chunks.
//! This is target-invariance safety, not proof of universal admission or an
//! actual source/device quiescence lease.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, ea_bootstrap, ea_namespace,
    ea_recovery_admission::{self, AdmissionView, CheckedRecovery},
    patch_set::{self, PatchSet}, recovery_io::Recovery,
    snapshot::{Snapshot, MAX_SHADOW_LAYERS}, transaction::{self, AfterImage, ImageView}};

verus! {

pub const COMPARISON_CHUNK: usize = 65536;

#[derive(Debug, PartialEq, Eq)]
pub enum RestartError {
    SnapshotUnavailable,
    RejectedImage,
    DifferentTarget,
}

/// Clone only retained redo images, with no mutable alias to either copy.
fn copy_patches(source: &PatchSet) -> (r: PatchSet)
    ensures source.wf(), r.wf(), r.view() == source.view(),
{
    let length = source.len();
    let mut images = Vec::<AfterImage>::new();
    let mut index = 0usize;
    assert(transaction::images(images@) =~= source.view().take(0));
    while index < length
        invariant source.wf(), length == source.view().len(), length <= patch_set::MAX_PATCHES,
            index <= length,
            transaction::images(images@) == source.view().take(index as int),
        decreases length - index,
    {
        let image = source.at(index).unwrap();
        let captured = AfterImage::capture(image.block(), image.as_slice()).unwrap();
        let ghost before = transaction::images(images@);
        let ghost next = captured.view();
        assert(next == source.view()[index as int]);
        images.push(captured);
        assert(transaction::images(images@) =~= before.push(next));
        assert(transaction::images(images@) =~= source.view().take(index as int + 1));
        index += 1;
    }
    assert(transaction::images(images@) =~= source.view());
    assert(patch_set::valid(transaction::images(images@)));
    match PatchSet::from_images(images) {
        Ok(patches) => patches,
        Err(_) => {
            proof { assert(false); }
            PatchSet::new()
        },
    }
}

fn retirement_patch(engine: &Recovery) -> (r: PatchSet)
    ensures r.wf(), r.view() == seq![ImageView {
        block: engine.journal_block(), image: engine.tail(),
    }],
{
    let (block, image) = engine.retirement_image();
    let empty = PatchSet::new();
    match empty.insert(block, image) {
        Ok(patches) => {
            assert(patches.view() =~= seq![ImageView { block, image: image@ }]);
            patches
        },
        Err(_) => {
            proof { assert(false); }
            PatchSet::new()
        },
    }
}

/// Compare all partition bytes, including bytes beyond the filesystem range.
/// Temporary allocation is at most two comparison chunks.
fn equal_snapshots(left: &Snapshot<'_>, right: &Snapshot<'_>) -> (r: bool)
    ensures r == (left.view() == right.view()),
{
    let length = left.partition_bytes();
    if length != right.partition_bytes() { return false; }
    let mut offset = 0u64;
    while offset < length
        invariant offset <= length, length as nat == left.view().len(),
            left.view().len() == right.view().len(),
            left.view().take(offset as int) == right.view().take(offset as int),
        decreases length - offset,
    {
        let remaining = length - offset;
        let amount = if remaining > COMPARISON_CHUNK as u64 {
            COMPARISON_CHUNK
        } else { remaining as usize };
        assert(0 < amount <= COMPARISON_CHUNK);
        assert(offset as nat + amount <= length);
        let a = match left.capture_bytes(offset, amount) {
            Some(bytes) => bytes, None => { return false; },
        };
        let b = match right.capture_bytes(offset, amount) {
            Some(bytes) => bytes, None => { return false; },
        };
        if !bytes::equal(a.as_slice(), b.as_slice()) {
            assert(left.view() != right.view());
            return false;
        }
        let next = offset + amount as u64;
        assert(left.view().take(next as int) =~= right.view().take(next as int)) by {
            assert forall|i: int| 0 <= i < next implies
                (#[trigger] left.view().take(next as int)[i]) == right.view().take(next as int)[i] by {
                if i < offset {
                    assert(left.view().take(offset as int)[i] == right.view().take(offset as int)[i]);
                } else {
                    assert(a@[i - offset as int] == b@[i - offset as int]);
                }
            }
        }
        offset = next;
    }
    assert(offset == length);
    assert(offset as int == left.view().len());
    assert forall|i: int| 0 <= i < left.view().len() implies
        (#[trigger] left.view()[i]) == right.view()[i] by {
        assert(left.view().take(offset as int)[i] == right.view().take(offset as int)[i]);
    }
    assert(left.view() =~= right.view());
    true
}

proof fn checked_target_facts(ready: &CheckedRecovery<'_, '_>)
    requires ready.wf(),
    ensures ea_bootstrap::valid(ready.view().before),
        ea_namespace::valid(ready.view().after),
        ready.source_view() == ready.view().before.source,
        ready.home_images() == ready.view().homes,
        ready.owner().journal_block() == ready.view().before.layout.start,
        ea_recovery_admission::final_source(ready.source_view(), ready.home_images(), ready.owner())
            == ea_recovery_admission::recovered_source(ready.view()),
        ready.view().inode_budget == ready.view().after.allocation.integrity.inode_budget,
        ready.view().node_budget == ready.view().after.allocation.integrity.node_budget,
        ready.view().byte_budget == ready.view().after.allocation.integrity.byte_budget,
{
    reveal(ea_recovery_admission::valid);
}

/// Immutable exact target retained across independently captured restarts.
/// It is a host admission object, not device, DMA or mounted filesystem authority.
pub struct Anchor<'s, 'a> {
    source: &'s Snapshot<'a>,
    homes: PatchSet,
    retirement: PatchSet,
    inode_budget: u32,
    node_budget: u64,
    byte_budget: u64,
    certificate: Ghost<Seq<AdmissionView>>,
}

impl<'s, 'a> Anchor<'s, 'a> {
    pub closed spec fn initial(&self) -> AdmissionView { self.certificate@[0] }
    pub closed spec fn certificate_count(&self) -> nat { self.certificate@.len() }
    pub closed spec fn target(&self) -> Seq<u8> {
        patch_set::apply(patch_set::apply(self.source.view(), self.homes.view()), self.retirement.view())
    }
    pub closed spec fn wf(&self) -> bool {
        &&& self.certificate_count() == 1
        &&& ea_bootstrap::valid(self.initial().before)
        &&& ea_namespace::valid(self.initial().after)
        &&& self.source.view() == self.initial().before.source
        &&& self.homes.view() == self.initial().homes
        &&& self.retirement.view().len() == 1
        &&& self.retirement.view()[0].block == self.initial().before.layout.start
        &&& self.target() == ea_recovery_admission::recovered_source(self.initial())
        &&& self.inode_budget == self.initial().inode_budget
        &&& self.node_budget == self.initial().node_budget
        &&& self.byte_budget == self.initial().byte_budget
        &&& self.source.depth() <= MAX_SHADOW_LAYERS - 2
    }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn initial_source(&self) -> (r: &'s Snapshot<'a>)
        ensures self.wf(), r.view() == self.initial().before.source,
    {
        proof { use_type_invariant(self); }
        self.source
    }

    pub fn budgets(&self) -> (r: (u32, u64, u64))
        ensures self.wf(),
            r == (self.initial().inode_budget, self.initial().node_budget, self.initial().byte_budget),
    {
        proof { use_type_invariant(self); }
        (self.inode_budget, self.node_budget, self.byte_budget)
    }

    /// A new attempt is exposed only after fresh raw discovery and full
    /// namespace admission agree with the initial exact target.
    pub fn restart<'t, 'b>(&self, source: &'t Snapshot<'b>)
        -> (r: Result<CheckedRecovery<'t, 'b>, RestartError>)
        ensures self.wf(), match r {
            Ok(ready) => ready.wf() && ready.view().before.source == source.view()
                && ea_namespace::valid(ready.view().after)
                && ea_recovery_admission::recovered_source(ready.view()) == self.target()
                && ready.view().inode_budget == self.initial().inode_budget
                && ready.view().node_budget == self.initial().node_budget
                && ready.view().byte_budget == self.initial().byte_budget
                && ready.owner().state().request == 0 && ready.owner().state().cursor == 0
                && !ready.owner().state().pending && !ready.owner().state().faulted,
            Err(_) => true,
        },
    {
        proof { use_type_invariant(self); }
        if source.shadow_depth() > MAX_SHADOW_LAYERS - 2 {
            return Err(RestartError::SnapshotUnavailable);
        }
        let ready = match ea_recovery_admission::prepare(
            source, self.inode_budget, self.node_budget, self.byte_budget) {
            Some(ready) => ready,
            None => { return Err(RestartError::RejectedImage); },
        };
        proof { checked_target_facts(&ready); }
        let ghost candidate_target = ea_recovery_admission::recovered_source(ready.view());
        let ghost original_target = self.target();
        let same = {
            let expected_homes = match self.source.overlay(&self.homes) {
                Some(snapshot) => snapshot,
                None => { return Err(RestartError::SnapshotUnavailable); },
            };
            let expected = match expected_homes.overlay(&self.retirement) {
                Some(snapshot) => snapshot,
                None => { return Err(RestartError::SnapshotUnavailable); },
            };
            assert(expected.view() == original_target);
            let candidate_homes = match source.overlay(ready.home_patches()) {
                Some(snapshot) => snapshot,
                None => { return Err(RestartError::SnapshotUnavailable); },
            };
            let tail = retirement_patch(ready.engine_ref());
            let candidate = match candidate_homes.overlay(&tail) {
                Some(snapshot) => snapshot,
                None => { return Err(RestartError::SnapshotUnavailable); },
            };
            assert(candidate.view() == candidate_target);
            let equal = equal_snapshots(&expected, &candidate);
            assert(equal == (candidate_target == original_target));
            equal
        };
        if !same { return Err(RestartError::DifferentTarget); }
        Ok(ready)
    }
}

pub fn prepare<'s, 'a>(source: &'s Snapshot<'a>, inode_budget: u32, node_budget: u64, byte_budget: u64)
    -> (r: Result<(Anchor<'s, 'a>, CheckedRecovery<'s, 'a>), RestartError>)
    ensures match r {
        Ok((anchor, ready)) => anchor.wf() && ready.wf()
            && anchor.initial() == ready.view()
            && anchor.initial().before.source == source.view()
            && anchor.initial().inode_budget == inode_budget
            && anchor.initial().node_budget == node_budget
            && anchor.initial().byte_budget == byte_budget
            && anchor.target() == ea_recovery_admission::recovered_source(ready.view()),
        Err(_) => true,
    },
{
    if source.shadow_depth() > MAX_SHADOW_LAYERS - 2 {
        return Err(RestartError::SnapshotUnavailable);
    }
    let ready = match ea_recovery_admission::prepare(source, inode_budget, node_budget, byte_budget) {
        Some(ready) => ready,
        None => { return Err(RestartError::RejectedImage); },
    };
    proof { checked_target_facts(&ready); }
    let homes = copy_patches(ready.home_patches());
    let retirement = retirement_patch(ready.engine_ref());
    let ghost checked = ready.view();
    let ghost certificates = seq![checked];
    assert(retirement.view().len() == 1);
    assert(retirement.view()[0].block == checked.before.layout.start);
    assert(patch_set::apply(patch_set::apply(source.view(), homes.view()), retirement.view())
        == ea_recovery_admission::recovered_source(checked));
    let anchor = Anchor {
        source, homes, retirement, inode_budget, node_budget, byte_budget,
        certificate: Ghost(certificates),
    };
    assert(anchor.wf());
    Ok((anchor, ready))
}

/// A finite list of accepted attempts is collected from successful restart
/// results. Rejection is permitted and supplies no recovery request authority.
pub open spec fn accepted_attempts(target: Seq<u8>, attempts: Seq<AdmissionView>) -> bool {
    forall|i: int| 0 <= i < attempts.len() ==>
        ea_namespace::valid((#[trigger] attempts[i]).after)
            && ea_recovery_admission::recovered_source(attempts[i]) == target
}

pub proof fn every_finite_accepted_restart_has_the_same_validated_target(
    target: Seq<u8>, attempts: Seq<AdmissionView>, first: int, second: int)
    requires accepted_attempts(target, attempts),
        0 <= first < attempts.len(), 0 <= second < attempts.len(),
    ensures ea_namespace::valid(attempts[first].after),
        ea_namespace::valid(attempts[second].after),
        ea_recovery_admission::recovered_source(attempts[first])
            == ea_recovery_admission::recovered_source(attempts[second]),
{
}

}
