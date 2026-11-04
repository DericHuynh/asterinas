// SPDX-License-Identifier: MPL-2.0

//! Source-bound, sealed multi-transaction filesystem admission. Every complete
//! home prefix is validated before the first request, including prefixes later
//! repaired by another transaction. Device and CortenMM authority is separate.

use vstd::prelude::*;
use crate::{bootstrap::{self, Bootstrap, BootstrapView}, bootstrap_identity,
    image_validation::{self, CheckedImage}, journal_program::{self, Lane},
    journal_queue::{self, FrozenVersion}, journal_window::{self, Engine, Operation, WindowView},
    namespace::{self, NamespaceView}, patch_set::PatchSet,
    recovery_io::Command, recovery_request::Completion, snapshot::Snapshot,
    transaction::ImageView, window_prefix};

verus! {

pub struct AdmissionView { pub boot: BootstrapView, pub initial: NamespaceView, pub prefixes: Seq<NamespaceView> }

pub open spec fn certified(boot: BootstrapView, certificate: NamespaceView, source: Seq<u8>) -> bool {
    namespace::valid(certificate) && certificate.index.volume.index.source == source
        && certificate.index.volume.journal == boot.layout && bootstrap_identity::preserved(boot, source)
}

#[verifier::opaque]
pub open spec fn valid(a: AdmissionView, v: WindowView) -> bool {
    &&& bootstrap::valid(a.boot) && journal_window::valid(v)
    &&& namespace::valid(a.initial) && a.initial.index.volume.index.source == a.boot.source
    &&& a.initial.index.volume.journal == a.boot.layout
    &&& v.layout == a.boot.layout && v.initial_primary == a.boot.source.subrange(0, 4096)
    &&& v.initial_journal == bootstrap::journal_bytes(a.boot) && v.uuid == bootstrap::journal_identity(a.boot)
    &&& v.partition_bytes as nat == a.boot.source.len()
    &&& a.prefixes.len() == v.txs.len() + 1
    &&& (forall|k: int| 0 <= k < a.prefixes.len() ==> #[trigger] certified(a.boot, a.prefixes[k], window_prefix::prefix(a.boot.source, v, k as nat)))
}

pub struct CheckedWindow<'s, 'a> { source: &'s Snapshot<'a>, engine: Engine, certificate: Ghost<AdmissionView> }
pub struct Pending<'s, 'a> { source: &'s Snapshot<'a>, pending: journal_window::Pending, certificate: Ghost<AdmissionView> }

impl<'s, 'a> CheckedWindow<'s, 'a> {
    pub closed spec fn view(&self) -> AdmissionView { self.certificate@ }
    pub closed spec fn owner(&self) -> &Engine { &self.engine }
    pub closed spec fn source_view(&self) -> Seq<u8> { self.source.view() }
    pub open spec fn wf(&self) -> bool { valid(self.view(), self.owner().program()) && self.view().boot.source == self.source_view() }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn source_snapshot(&self) -> (r: &'s Snapshot<'a>) ensures self.wf(), r.view() == self.view().boot.source {
        proof { use_type_invariant(self); }
        self.source
    }

    pub fn engine_ref(&self) -> (r: &Engine) ensures self.wf(), r == self.owner() {
        proof { use_type_invariant(self); }
        &self.engine
    }

    pub fn progress(&self) -> (r: (usize, usize, usize, bool))
        ensures self.wf(), r == (self.owner().state().commit, self.owner().state().checkpoint, self.owner().state().retired, self.owner().state().faulted),
    { proof { use_type_invariant(self); } self.engine.progress() }

    pub fn finished(&self) -> (r: bool) ensures self.wf(), r == journal_program::finished(self.owner().state(), journal_window::counts(self.owner().program())) {
        proof { use_type_invariant(self); }
        self.engine.finished()
    }

    pub fn can_dispatch(&self, lane: Lane) -> (r: bool)
        ensures self.wf(), r == journal_program::enabled(self.owner().state(), lane, journal_window::counts(self.owner().program())),
    { proof { use_type_invariant(self); } self.engine.can_dispatch(lane) }

    pub fn abort(self) -> (r: Self) ensures r.wf(), r.view() == self.view(), r.owner().program() == self.owner().program(),
        r.owner().state() == (journal_program::State { faulted: true, ..self.owner().state() }),
    {
        proof { use_type_invariant(&self); }
        let CheckedWindow { source, engine, certificate } = self;
        CheckedWindow { source, engine: engine.abort(), certificate }
    }

    pub fn dispatch(self, lane: Lane) -> (r: Result<Pending<'s, 'a>, Self>)
        ensures match r {
            Ok(pending) => pending.wf() && pending.view() == self.view() && pending.owner().program() == self.owner().program()
                && journal_program::enabled(self.owner().state(), lane, journal_window::counts(self.owner().program()))
                && pending.owner().state() == journal_program::started(self.owner().state(), lane),
            Err(unchanged) => unchanged.wf() && unchanged.view() == self.view() && unchanged.owner().program() == self.owner().program()
                && unchanged.owner().state() == self.owner().state()
                && !journal_program::enabled(self.owner().state(), lane, journal_window::counts(self.owner().program())),
        },
    {
        proof { use_type_invariant(&self); }
        let CheckedWindow { source, engine, certificate } = self;
        match journal_window::dispatch(engine, lane) {
            Ok(pending) => Ok(Pending { source, pending, certificate }),
            Err(engine) => Err(CheckedWindow { source, engine, certificate }),
        }
    }
}

impl<'s, 'a> Pending<'s, 'a> {
    pub closed spec fn view(&self) -> AdmissionView { self.certificate@ }
    pub closed spec fn owner(&self) -> &Engine { self.pending.owner() }
    pub closed spec fn source_view(&self) -> Seq<u8> { self.source.view() }
    pub open spec fn wf(&self) -> bool { valid(self.view(), self.owner().program()) && self.view().boot.source == self.source_view() }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn operation(&self) -> (r: Operation)
        ensures self.wf(), r == journal_window::pending_operation(self.owner().state(), journal_window::counts(self.owner().program())),
            journal_window::operation_valid(r, self.owner().program()),
    { proof { use_type_invariant(self); } self.pending.operation() }

    pub fn request_number(&self) -> (r: u64) ensures self.wf(), r == self.owner().state().request, r > 0 {
        proof { use_type_invariant(self); }
        self.pending.request_number()
    }

    pub fn pending_command(&self) -> (r: Command<'_>) ensures self.wf(),
        r.view() == journal_window::expected(self.owner().program(), journal_window::pending_operation(self.owner().state(), journal_window::counts(self.owner().program()))),
        journal_window::command_bounded(self.owner().program(), r.view()),
    { proof { use_type_invariant(self); } self.pending.pending_command() }

    pub fn abort_pending(self) -> (r: Self) ensures r.wf(), r.view() == self.view(), r.owner().program() == self.owner().program(),
        r.owner().state() == (journal_program::State { faulted: true, ..self.owner().state() }),
    {
        proof { use_type_invariant(&self); }
        let Pending { source, pending, certificate } = self;
        Pending { source, pending: pending.abort_pending(), certificate }
    }

    pub fn finish_pending(self, outcome: Completion) -> (r: CheckedWindow<'s, 'a>)
        ensures r.wf(), r.view() == self.view(), r.owner().program() == self.owner().program(),
            r.owner().state() == journal_program::completed(self.owner().state(), journal_window::counts(self.owner().program()), outcome is Succeeded),
    {
        proof { use_type_invariant(&self); }
        let Pending { source, pending, certificate } = self;
        CheckedWindow { source, engine: pending.finish_pending(outcome), certificate }
    }
}

fn inspect_prefix<'a>(source: Snapshot<'a>, boot: &Bootstrap<'_, '_>) -> (r: Option<CheckedImage<'a>>)
    ensures match r { Some(checked) => checked.wf() && certified(boot.view(), checked.view(), source.view()), None => true },
{
    if !bootstrap_identity::check(boot, &source) { return None; }
    let checked = match image_validation::inspect(source) { Some(checked) => checked, None => { return None; } };
    let layout = boot.layout();
    let actual = checked.journal();
    if actual.physical_start() != layout.physical_start() || actual.blocks() != layout.blocks()
        || actual.filesystem_blocks() != layout.filesystem_blocks() { return None; }
    Some(checked)
}

pub fn prepare<'s, 'a>(source: &'s Snapshot<'a>, versions: &[FrozenVersion]) -> (r: Option<CheckedWindow<'s, 'a>>)
    ensures match r { Some(ready) => ready.wf() && ready.view().boot.source == source.view()
        && ready.owner().state() == journal_program::initial()
        && Seq::new(ready.owner().program().txs.len(), |i: int| ready.owner().program().txs[i].source) == journal_queue::frozen_views(versions@), None => true },
{
    let boot = match bootstrap::locate(source) { Some(boot) => boot, None => { return None; } };
    let initial = match image_validation::inspect(source.duplicate()) { Some(checked) => checked, None => { return None; } };
    let layout = boot.layout();
    let actual = initial.journal();
    if actual.physical_start() != layout.physical_start() || actual.blocks() != layout.blocks()
        || actual.filesystem_blocks() != layout.filesystem_blocks() { return None; }
    let journal = boot.capture_journal();
    let engine = match journal_window::prepare(versions, &journal, boot.journal_uuid(), layout.duplicate(), boot.primary(), source.partition_bytes()) {
        Some(engine) => engine, None => { return None; },
    };
    let ghost v = engine.program();
    let empty = PatchSet::new();
    let dirty = match empty.insert(0, engine.dirty_marker()) { Ok(patches) => patches, Err(_) => { return None; } };
    assert(dirty.view() =~= seq![ImageView { block: 0, image: v.dirty }]);
    let marked = match source.overlay(&dirty) { Some(marked) => marked, None => { return None; } };
    let first = match inspect_prefix(marked.duplicate(), &boot) { Some(checked) => checked, None => { return None; } };
    let ghost prefixes = seq![first.view()];
    let mut homes = PatchSet::new();
    assert(crate::patch_set::apply(marked.view(), homes.view()) =~= marked.view());
    let mut index = 0usize;
    proof {
        journal_window::a_window_retains_its_geometry_and_bounded_counts(v);
        assert(Seq::new(v.txs.len(), |i: int| v.txs[i].source).len() == v.txs.len());
        assert(journal_queue::frozen_views(versions@).len() == versions.len());
    }
    while index < versions.len()
        invariant index <= versions.len() == v.txs.len() <= 64, engine.wf(), engine.program() == v,
            boot.wf(), initial.wf(), initial.view().index.volume.index.source == boot.view().source,
            initial.view().index.volume.journal == boot.view().layout,
            boot.view().source == source.view(), boot.view().source.len() >= 8192, v.layout == boot.view().layout,
            v.initial_primary == boot.view().source.subrange(0, 4096), v.initial_journal == bootstrap::journal_bytes(boot.view()),
            v.uuid == bootstrap::journal_identity(boot.view()), v.partition_bytes as nat == boot.view().source.len(),
            Seq::new(v.txs.len(), |i: int| v.txs[i].source) == journal_queue::frozen_views(versions@),
            marked.view() == window_prefix::marked(boot.view().source, v), homes.wf(),
            crate::patch_set::apply(marked.view(), homes.view()) == window_prefix::prefix(boot.view().source, v, index as nat),
            prefixes.len() == index + 1,
            (forall|k: int| 0 <= k < prefixes.len() ==> #[trigger] certified(boot.view(), prefixes[k], window_prefix::prefix(boot.view().source, v, k as nat))),
        decreases versions.len() - index,
    {
        proof {
            journal_window::window_entry(v, index as int); reveal(journal_window::positioned_valid);
            assert(v.txs[index as int].source == journal_queue::frozen_views(versions@)[index as int]);
            assert(v.txs[index as int].tx.original == versions@[index as int].view().images);
        }
        homes = match window_prefix::append_version(homes, &versions[index], Ghost(marked.view())) { Some(homes) => homes, None => { return None; } };
        assert(window_prefix::prefix(boot.view().source, v, index as nat + 1)
            == window_prefix::overlay(window_prefix::prefix(boot.view().source, v, index as nat), v.txs[index as int].tx.original));
        assert(crate::patch_set::apply(marked.view(), homes.view()) == window_prefix::prefix(boot.view().source, v, index as nat + 1));
        let candidate = match marked.overlay(&homes) { Some(candidate) => candidate, None => { return None; } };
        let checked = match inspect_prefix(candidate, &boot) { Some(checked) => checked, None => { return None; } };
        let ghost previous = prefixes;
        proof {
            prefixes = prefixes.push(checked.view());
            assert forall|k: int| 0 <= k < prefixes.len() implies #[trigger] certified(boot.view(), prefixes[k], window_prefix::prefix(boot.view().source, v, k as nat)) by {
                if k < previous.len() { assert(certified(boot.view(), previous[k], window_prefix::prefix(boot.view().source, v, k as nat))); }
            }
        }
        index += 1;
    }
    let ghost certificate = AdmissionView { boot: boot.view(), initial: initial.view(), prefixes };
    assert(valid(certificate, v)) by { reveal(valid); }
    Some(CheckedWindow { source, engine, certificate: Ghost(certificate) })
}

}
