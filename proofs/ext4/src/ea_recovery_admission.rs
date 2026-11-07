// SPDX-License-Identifier: MPL-2.0

//! EA recovery requests sealed to the actual repaired shadow namespace.
//! Journal discovery and scanning use the raw source before any allocation or
//! namespace inspection. Only the selected redo images and retired tail are
//! overlaid for full EA validation. Device and mounted refinement remain open.

use vstd::prelude::*;
use crate::{ea_bootstrap::{self, BootstrapView}, bootstrap_identity,
    ea_namespace::{self, NamespaceView}, patch_set::{self, PatchSet}, recovery_io::{self, Command, Recovery},
    recovery_patch, recovery_request::{self, Completion}, snapshot::Snapshot, transaction::ImageView};

verus! {

pub struct AdmissionView {
    pub before: BootstrapView, pub homes: Seq<ImageView>, pub after: NamespaceView,
    pub inode_budget: u32, pub node_budget: u64, pub byte_budget: u64,
}

pub open spec fn recovered_source(v: AdmissionView) -> Seq<u8> {
    v.after.allocation.integrity.references.index.header.source
}

pub open spec fn final_source(before: Seq<u8>, homes: Seq<ImageView>, engine: &Recovery) -> Seq<u8> {
    patch_set::apply(patch_set::apply(before, homes),
        seq![ImageView { block: engine.journal_block(), image: engine.tail() }])
}

#[verifier::opaque]
pub open spec fn valid(v: AdmissionView, engine: &Recovery) -> bool {
    &&& ea_bootstrap::valid(v.before) && engine.plan().refines()
    &&& engine.plan().layout().view() == v.before.layout
    &&& engine.primary() == v.before.source.subrange(0, 4096)
    &&& engine.partition_bytes() as nat == v.before.source.len()
    &&& engine.scan_result().certificate(ea_bootstrap::scan_source(v.before))
    &&& engine.scan_result().maximal(ea_bootstrap::scan_source(v.before))
    &&& crate::write_recovery::returned(engine.scan_result(), ea_bootstrap::scan_source(v.before))
    &&& engine.journal_block() == v.before.layout.start && engine.tail().len() == 4096
    &&& patch_set::valid(v.homes) && recovery_patch::matches_prefix(engine.plan(), v.homes, engine.plan().selection().len())
    &&& ea_namespace::valid(v.after) && v.after.allocation.journal.layout == v.before.layout
    &&& v.after.allocation.integrity.inode_budget == v.inode_budget
    &&& v.after.allocation.integrity.node_budget == v.node_budget
    &&& v.after.allocation.integrity.byte_budget == v.byte_budget
    &&& (forall|i: int| 0 <= i < engine.plan().log().len() ==> (#[trigger] engine.plan().log()[i]).block != 0)
    &&& recovered_source(v) == final_source(v.before.source, v.homes, engine)
    &&& bootstrap_identity::preserved(v.before, recovered_source(v))
}

proof fn same_images_keep_admission(v: AdmissionView, before: &Recovery, after: &Recovery)
    requires valid(v, before), recovery_request::same_images(after, before),
    ensures valid(v, after),
{
    reveal(valid);
}

pub struct CheckedRecovery<'s, 'a> {
    source: &'s Snapshot<'a>, engine: Recovery, homes: PatchSet, certificate: Ghost<Seq<AdmissionView>>,
}

pub struct Pending<'s, 'a> {
    source: &'s Snapshot<'a>, pending: recovery_request::Pending, homes: PatchSet, certificate: Ghost<Seq<AdmissionView>>,
}

impl<'s, 'a> CheckedRecovery<'s, 'a> {
    pub closed spec fn view(&self) -> AdmissionView { self.certificate@[0] }
    pub closed spec fn certificate_count(&self) -> nat { self.certificate@.len() }
    pub closed spec fn owner(&self) -> &Recovery { &self.engine }
    pub closed spec fn source_view(&self) -> Seq<u8> { self.source.view() }
    pub closed spec fn home_images(&self) -> Seq<ImageView> { self.homes.view() }
    pub open spec fn wf(&self) -> bool {
        self.certificate_count() == 1 && valid(self.view(), self.owner()) && self.view().before.source == self.source_view() && self.view().homes == self.home_images()
    }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn source_snapshot(&self) -> (r: &'s Snapshot<'a>)
        ensures self.wf(), r.view() == self.view().before.source,
    {
        proof { use_type_invariant(self); }
        self.source
    }

    pub fn home_patches(&self) -> (r: &PatchSet) ensures self.wf(), r.view() == self.view().homes {
        proof { use_type_invariant(self); }
        &self.homes
    }

    pub fn engine_ref(&self) -> (r: &Recovery) ensures self.wf(), r == self.owner() {
        proof { use_type_invariant(self); }
        &self.engine
    }

    pub fn finished(&self) -> (r: bool)
        ensures self.wf(), r == (!self.owner().state().faulted && self.owner().state().phase == 4 && !self.owner().state().pending),
    {
        proof { use_type_invariant(self); }
        self.engine.finished()
    }

    pub fn failed(&self) -> (r: bool) ensures self.wf(), r == self.owner().state().faulted {
        proof { use_type_invariant(self); }
        self.engine.failed()
    }

    pub fn abort(self) -> (r: Self)
        ensures r.wf(), r.view() == self.view(), r.owner().state() == (recovery_io::State { faulted: true, ..self.owner().state() }),
    {
        proof { use_type_invariant(&self); }
        let CheckedRecovery { source, mut engine, homes, certificate } = self;
        let ghost before = engine;
        engine.abort();
        proof { same_images_keep_admission(certificate@[0], &before, &engine); }
        CheckedRecovery { source, engine, homes, certificate }
    }

    pub fn dispatch(self) -> (r: Result<Pending<'s, 'a>, Self>)
        ensures match r {
            Ok(p) => p.wf() && p.view() == self.view()
                && !self.owner().state().pending && !self.owner().state().faulted && self.owner().state().phase < 4
                && p.owner().state() == recovery_io::started(self.owner().state()),
            Err(done) => done.wf() && done.view() == self.view() && done.owner().state() == self.owner().state()
                && (self.owner().state().pending || self.owner().state().faulted || self.owner().state().phase == 4),
        },
    {
        proof { use_type_invariant(&self); }
        let CheckedRecovery { source, engine, homes, certificate } = self;
        let ghost before = engine;
        match recovery_request::dispatch(engine) {
            Ok(pending) => {
                proof { same_images_keep_admission(certificate@[0], &before, pending.owner()); }
                Ok(Pending { source, pending, homes, certificate })
            },
            Err(engine) => {
                proof { same_images_keep_admission(certificate@[0], &before, &engine); }
                Err(CheckedRecovery { source, engine, homes, certificate })
            },
        }
    }
}

impl<'s, 'a> Pending<'s, 'a> {
    pub closed spec fn view(&self) -> AdmissionView { self.certificate@[0] }
    pub closed spec fn certificate_count(&self) -> nat { self.certificate@.len() }
    pub closed spec fn owner(&self) -> &Recovery { self.pending.owner() }
    pub closed spec fn source_view(&self) -> Seq<u8> { self.source.view() }
    pub closed spec fn home_images(&self) -> Seq<ImageView> { self.homes.view() }
    pub open spec fn wf(&self) -> bool {
        self.certificate_count() == 1 && valid(self.view(), self.owner()) && self.view().before.source == self.source_view() && self.view().homes == self.home_images()
    }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn pending_command(&self) -> (r: Command<'_>)
        ensures self.wf(), r.view() == self.owner().expected(),
            match r.view() {
                recovery_io::CommandView::Write { block, image } => image.len() == 4096
                    && block < self.owner().plan().layout().view().fs_blocks
                    && block as nat * 4096 + 4096 <= self.owner().partition_bytes(),
                recovery_io::CommandView::Flush => true,
            },
    {
        proof { use_type_invariant(self); }
        self.pending.pending_command()
    }

    pub fn abort_pending(self) -> (r: Self)
        ensures r.wf(), r.view() == self.view(), r.owner().state() == (recovery_io::State { faulted: true, ..self.owner().state() }),
    {
        proof { use_type_invariant(&self); }
        let Pending { source, pending, homes, certificate } = self;
        let ghost before = *pending.owner();
        let pending = pending.abort_pending();
        proof { same_images_keep_admission(certificate@[0], &before, pending.owner()); }
        Pending { source, pending, homes, certificate }
    }

    pub fn finish_pending(self, outcome: Completion) -> (r: CheckedRecovery<'s, 'a>)
        ensures r.wf(), r.view() == self.view(),
            r.owner().state() == recovery_io::completed(self.owner().state(), self.owner().plan().selection().len(), outcome is Succeeded),
    {
        proof { use_type_invariant(&self); }
        let Pending { source, pending, homes, certificate } = self;
        let ghost before = *pending.owner();
        let engine = pending.finish_pending(outcome);
        proof { same_images_keep_admission(certificate@[0], &before, &engine); }
        CheckedRecovery { source, engine, homes, certificate }
    }
}

pub fn prepare<'s, 'a>(source: &'s Snapshot<'a>, inode_budget: u32, node_budget: u64, byte_budget: u64) -> (r: Option<CheckedRecovery<'s, 'a>>)
    ensures match r {
        Some(ready) => ready.wf() && ready.view().before.source == source.view()
            && ready.view().inode_budget == inode_budget && ready.view().node_budget == node_budget
            && ready.view().byte_budget == byte_budget
            && ready.owner().state().cursor == 0 && ready.owner().state().request == 0
            && !ready.owner().state().pending && !ready.owner().state().faulted,
        None => true,
    },
{
    let boot = match ea_bootstrap::locate(source) { Some(boot) => boot, None => { return None; } };
    let engine = match boot.prepare_recovery() { Some(engine) => engine, None => { return None; } };
    let homes = recovery_patch::collect(engine.replay_plan());
    let home_source = match source.overlay(&homes) { Some(source) => source, None => { return None; } };
    let (journal, tail) = engine.retirement_image();
    let empty = PatchSet::new();
    let ghost empty_images = empty.view();
    let tail_patch = match empty.insert(journal, tail) { Ok(patch) => patch, Err(_) => { return None; } };
    assert(tail_patch.view() =~= seq![ImageView { block: journal, image: tail@ }]);
    let final_source = match home_source.overlay(&tail_patch) { Some(source) => source, None => { return None; } };
    if !ea_bootstrap::check_identity(&boot, &final_source) { return None; }
    let checked = match ea_namespace::inspect_journal(&final_source, inode_budget, node_budget, byte_budget) { Some(checked) => checked, None => { return None; } };
    let final_layout = checked.allocation().journal();
    let original_layout = boot.layout();
    if final_layout.physical_start() != original_layout.physical_start()
        || final_layout.blocks() != original_layout.blocks()
        || final_layout.filesystem_blocks() != original_layout.filesystem_blocks() { return None; }
    let ghost certificate = AdmissionView { before: boot.view(), homes: homes.view(), after: checked.view(), inode_budget, node_budget, byte_budget };
    assert(valid(certificate, &engine)) by { reveal(valid); }
    let ghost certificates = seq![certificate];
    Some(CheckedRecovery { source, engine, homes, certificate: Ghost(certificates) })
}

}
