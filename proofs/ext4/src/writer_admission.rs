// SPDX-License-Identifier: MPL-2.0

//! Serialized candidate writer sealed to complete before/after filesystem
//! certificates and one immutable source. No physical device, VFS credentials
//! or CortenMM ownership is established by these host-core certificates.

use vstd::prelude::*;
use crate::{bootstrap::{self, BootstrapView}, bootstrap_identity, edit_handles::FrozenBatch,
    image_validation, namespace::{self, NamespaceView}, patch_set::{self, PatchSet},
    recovery_io::{Command, CommandView}, recovery_request::Completion, snapshot::Snapshot,
    transaction::{self, AfterImage, ImageView}, write_io::{self, Images, Writer}, write_protocol::{self, Phase}};

verus! {

pub struct AdmissionView { pub boot: BootstrapView, pub before: NamespaceView, pub after: NamespaceView }

pub open spec fn final_source(source: Seq<u8>, images: Images) -> Seq<u8> {
    patch_set::apply(patch_set::apply(patch_set::apply(patch_set::apply(source,
        seq![ImageView { block: 0, image: images.dirty }]), write_io::log_images(images)), images.tx.original),
        seq![ImageView { block: images.journal_block, image: images.tail }])
}

#[verifier::opaque]
pub open spec fn valid(v: AdmissionView, images: Images) -> bool {
    &&& bootstrap::valid(v.boot) && write_io::valid_images(images)
    &&& namespace::valid(v.before) && namespace::valid(v.after)
    &&& v.before.index.volume.index.source == v.boot.source
    &&& v.before.index.volume.journal == v.boot.layout && v.after.index.volume.journal == v.boot.layout
    &&& images.initial_primary == v.boot.source.subrange(0, 4096)
    &&& images.initial_journal == bootstrap::journal_bytes(v.boot)
    &&& images.tx.uuid == bootstrap::journal_identity(v.boot) && images.tx.layout == v.boot.layout
    &&& images.partition_bytes as nat == v.boot.source.len()
    &&& patch_set::valid(images.tx.original) && patch_set::valid(write_io::log_images(images))
    &&& v.after.index.volume.index.source == final_source(v.boot.source, images)
    &&& bootstrap_identity::preserved(v.boot, v.after.index.volume.index.source)
}

pub struct CheckedWriter<'s, 'a> { source: &'s Snapshot<'a>, writer: Writer, certificate: Ghost<AdmissionView> }
pub struct Pending<'s, 'a> { source: &'s Snapshot<'a>, pending: write_io::Pending, certificate: Ghost<AdmissionView> }

impl<'s, 'a> CheckedWriter<'s, 'a> {
    pub closed spec fn view(&self) -> AdmissionView { self.certificate@ }
    pub closed spec fn owner(&self) -> &Writer { &self.writer }
    pub closed spec fn source_view(&self) -> Seq<u8> { self.source.view() }
    pub open spec fn wf(&self) -> bool { valid(self.view(), self.owner().images()) && self.view().boot.source == self.source_view() }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn source_snapshot(&self) -> (r: &'s Snapshot<'a>)
        ensures self.wf(), r.view() == self.view().boot.source,
    {
        proof { use_type_invariant(self); }
        self.source
    }

    pub fn engine_ref(&self) -> (r: &Writer) ensures self.wf(), r == self.owner() {
        proof { use_type_invariant(self); }
        &self.writer
    }

    pub fn finished(&self) -> (r: bool)
        ensures self.wf(), r == (self.owner().state().phase is Done && !self.owner().state().pending && !self.owner().state().faulted),
    {
        proof { use_type_invariant(self); }
        self.writer.finished()
    }

    pub fn failed(&self) -> (r: bool) ensures self.wf(), r == self.owner().state().faulted {
        proof { use_type_invariant(self); }
        self.writer.failed()
    }

    pub fn abort(self) -> (r: Self)
        ensures r.wf(), r.view() == self.view(), r.owner().images() == self.owner().images(),
            r.owner().state() == (write_protocol::State { faulted: true, ..self.owner().state() }),
    {
        proof { use_type_invariant(&self); }
        let CheckedWriter { source, writer, certificate } = self;
        let writer = write_io::abort(writer);
        CheckedWriter { source, writer, certificate }
    }

    pub fn dispatch(self) -> (r: Result<Pending<'s, 'a>, Self>)
        ensures match r {
            Ok(pending) => pending.wf() && pending.view() == self.view() && pending.owner().images() == self.owner().images()
                && !self.owner().state().pending && !self.owner().state().faulted && !(self.owner().state().phase is Done)
                && pending.owner().state() == write_protocol::started(self.owner().state()),
            Err(done) => done.wf() && done.view() == self.view() && done.owner().images() == self.owner().images()
                && done.owner().state() == self.owner().state()
                && (self.owner().state().pending || self.owner().state().faulted || self.owner().state().phase is Done),
        },
    {
        proof { use_type_invariant(&self); }
        let CheckedWriter { source, writer, certificate } = self;
        match write_io::dispatch(writer) {
            Ok(pending) => Ok(Pending { source, pending, certificate }),
            Err(writer) => Err(CheckedWriter { source, writer, certificate }),
        }
    }
}

impl<'s, 'a> Pending<'s, 'a> {
    pub closed spec fn view(&self) -> AdmissionView { self.certificate@ }
    pub closed spec fn owner(&self) -> &Writer { self.pending.owner() }
    pub closed spec fn source_view(&self) -> Seq<u8> { self.source.view() }
    pub open spec fn wf(&self) -> bool { valid(self.view(), self.owner().images()) && self.view().boot.source == self.source_view() }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn pending_command(&self) -> (r: Command<'_>)
        ensures self.wf(), r.view() == write_io::expected(self.owner().images(), self.owner().state()),
            match r.view() {
                CommandView::Write { block, image } => image.len() == 4096 && block < self.owner().images().tx.layout.fs_blocks
                    && block as nat * 4096 + 4096 <= self.owner().images().partition_bytes,
                CommandView::Flush => true,
            },
    {
        proof { use_type_invariant(self); }
        self.pending.pending_command()
    }

    pub fn abort_pending(self) -> (r: Self)
        ensures r.wf(), r.view() == self.view(), r.owner().images() == self.owner().images(),
            r.owner().state() == (write_protocol::State { faulted: true, ..self.owner().state() }),
    {
        proof { use_type_invariant(&self); }
        let Pending { source, pending, certificate } = self;
        let pending = pending.abort_pending();
        Pending { source, pending, certificate }
    }

    pub fn finish_pending(self, outcome: Completion) -> (r: CheckedWriter<'s, 'a>)
        ensures r.wf(), r.view() == self.view(), r.owner().images() == self.owner().images(),
            r.owner().state() == write_protocol::completed(self.owner().state(), self.owner().images().tx.payloads.len(), outcome is Succeeded),
    {
        proof { use_type_invariant(&self); }
        let Pending { source, pending, certificate } = self;
        let writer = pending.finish_pending(outcome);
        CheckedWriter { source, writer, certificate }
    }
}

fn collect_images(writer: &Writer, logs: bool) -> (r: Option<PatchSet>)
    ensures match r { Some(homes) => homes.wf()
        && homes.view() == (if logs { write_io::log_images(writer.images()) } else { writer.images().tx.original }), None => true },
{
    let count = if logs { writer.log_record_count() } else { writer.original_count() };
    let ghost expected = if logs { write_io::log_images(writer.images()) } else { writer.images().tx.original };
    let mut images = Vec::new();
    let mut index = 0usize;
    while index < count
        invariant images.len() == index <= count == expected.len(),
            expected == (if logs { write_io::log_images(writer.images()) } else { writer.images().tx.original }),
            transaction::images(images@) == expected.take(index as int),
        decreases count - index,
    {
        let (block, bytes) = if logs { writer.log_record(index).unwrap() } else { writer.original_image(index).unwrap() };
        let image = AfterImage::capture(block, bytes).unwrap();
        images.push(image);
        assert(transaction::images(images@) =~= expected.take(index as int + 1));
        index += 1;
    }
    assert(transaction::images(images@) == expected);
    match PatchSet::from_images(images) { Ok(homes) => Some(homes), Err(_) => None }
}

pub fn prepare<'s, 'a>(source: &'s Snapshot<'a>, frozen: FrozenBatch) -> (r: Option<CheckedWriter<'s, 'a>>)
    ensures match r {
        Some(ready) => ready.wf() && ready.view().boot.source == source.view()
            && ready.owner().images().tx.original == frozen.frozen_view()
            && ready.owner().images().tx.layout == frozen.frozen_layout()
            && ready.owner().state() == write_protocol::initial(),
        None => true,
    },
{
    let boot = match bootstrap::locate(source) { Some(boot) => boot, None => { return None; } };
    let before = match image_validation::inspect(source.duplicate()) { Some(checked) => checked, None => { return None; } };
    let layout = boot.layout();
    let prior_layout = before.journal();
    let reserved = frozen.reserved_layout();
    if prior_layout.physical_start() != layout.physical_start() || prior_layout.blocks() != layout.blocks()
        || prior_layout.filesystem_blocks() != layout.filesystem_blocks()
        || reserved.physical_start() != layout.physical_start() || reserved.blocks() != layout.blocks()
        || reserved.filesystem_blocks() != layout.filesystem_blocks() { return None; }
    let journal = boot.capture_journal();
    let bytes = source.partition_bytes();
    let writer = match write_io::prepare(&journal, boot.journal_uuid(), layout.duplicate(), boot.primary(), bytes, frozen.into_images()) {
        Some(writer) => writer, None => { return None; }
    };
    let homes = match collect_images(&writer, false) { Some(homes) => homes, None => { return None; } };
    let logs = match collect_images(&writer, true) { Some(logs) => logs, None => { return None; } };
    let empty = PatchSet::new();
    let marker = writer.dirty_marker();
    let dirty = match empty.insert(0, marker) { Ok(dirty) => dirty, Err(_) => { return None; } };
    assert(dirty.view() =~= seq![ImageView { block: 0, image: marker@ }]);
    let marked = match source.overlay(&dirty) { Some(source) => source, None => { return None; } };
    let logged = match marked.overlay(&logs) { Some(source) => source, None => { return None; } };
    let home_source = match logged.overlay(&homes) { Some(source) => source, None => { return None; } };
    let (block, tail) = writer.retirement_image();
    let empty = PatchSet::new();
    let retired = match empty.insert(block, tail) { Ok(retired) => retired, Err(_) => { return None; } };
    assert(retired.view() =~= seq![ImageView { block, image: tail@ }]);
    let final_source = match home_source.overlay(&retired) { Some(source) => source, None => { return None; } };
    if !bootstrap_identity::check(&boot, &final_source) { return None; }
    let after = match image_validation::inspect(final_source) { Some(checked) => checked, None => { return None; } };
    let final_layout = after.journal();
    if final_layout.physical_start() != layout.physical_start() || final_layout.blocks() != layout.blocks()
        || final_layout.filesystem_blocks() != layout.filesystem_blocks() { return None; }
    let ghost certificate = AdmissionView { boot: boot.view(), before: before.view(), after: after.view() };
    assert(valid(certificate, writer.images())) by { reveal(valid); }
    Some(CheckedWriter { source, writer, certificate: Ghost(certificate) })
}

}
