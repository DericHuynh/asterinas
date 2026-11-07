// SPDX-License-Identifier: MPL-2.0

//! Exact prepared EA namespace operations sealed to a serial journal writer.
//! Actual dirty before/after homes and the final logged image are fully checked
//! before dispatch. Proposal epochs are provenance, not Store or device leases.

use vstd::prelude::*;
use crate::{bootstrap::BootstrapView, bootstrap_identity, bytes, ea_bootstrap,
    ea_namespace::{self, NamespaceView}, ea_write_io::{self, Writer},
    ns_journal_prepared::{self, Prepared, Operation}, ns_mutation_model::PreparedView,
    patch_set::{self, PatchSet}, recovery_io::{Command, CommandView},
    recovery_request::Completion, snapshot::Snapshot, transaction::{self, AfterImage, ImageView},
    write_io::{self, Images}, write_protocol::{self, Phase}};

verus! {

pub struct AdmissionView {
    pub boot: BootstrapView, pub prepared_records: Seq<PreparedView>, pub operation_records: Seq<Operation>,
    pub prefixes: Seq<NamespaceView>, pub after_records: Seq<NamespaceView>,
}

impl AdmissionView {
    pub closed spec fn prepared(&self) -> PreparedView { self.prepared_records[0] }
    pub closed spec fn operation(&self) -> Operation { self.operation_records[0] }
    pub closed spec fn after(&self) -> NamespaceView { self.after_records[0] }
}

pub open spec fn source_of(v: NamespaceView) -> Seq<u8> {
    v.allocation.integrity.references.index.header.source
}

pub open spec fn marked(source: Seq<u8>, images: Images) -> Seq<u8> {
    patch_set::apply(source, seq![ImageView { block: 0, image: images.dirty }])
}

pub open spec fn home_source(source: Seq<u8>, images: Images) -> Seq<u8> {
    patch_set::apply(marked(source, images), images.tx.original)
}

pub open spec fn final_source(source: Seq<u8>, images: Images) -> Seq<u8> {
    crate::writer_admission::final_source(source, images)
}

pub open spec fn certified(boot: BootstrapView, namespace: NamespaceView, source: Seq<u8>) -> bool {
    ea_namespace::valid(namespace) && source_of(namespace) == source
        && namespace.allocation.journal.layout == boot.layout
        && bootstrap_identity::preserved(boot, source)
}

#[verifier::opaque]
pub open spec fn valid(v: AdmissionView, images: Images) -> bool {
    &&& v.prepared_records.len() == 1 && v.operation_records.len() == 1 && v.after_records.len() == 1
    &&& ea_bootstrap::valid(v.boot) && ea_write_io::valid_images(images)
    &&& ns_journal_prepared::valid_operation(v.operation(), v.prepared())
    &&& v.prepared().before == v.boot.source
    &&& images.tx.original == ns_journal_prepared::patches(v.operation())
    &&& 0 < images.tx.original.len() <= 8
    &&& images.initial_primary == v.boot.source.subrange(0, 4096)
    &&& images.initial_journal == ea_bootstrap::journal_bytes(v.boot)
    &&& images.tx.uuid == ea_bootstrap::journal_identity(v.boot) && images.tx.layout == v.boot.layout
    &&& images.partition_bytes as nat == v.boot.source.len()
    &&& bootstrap_identity::preserved(v.boot, v.prepared().after)
    &&& v.prefixes.len() == 2
    &&& certified(v.boot, v.prefixes[0], marked(v.boot.source, images))
    &&& certified(v.boot, v.prefixes[1], home_source(v.boot.source, images))
    &&& certified(v.boot, v.after(), final_source(v.boot.source, images))
    &&& patch_set::valid(images.tx.original) && patch_set::valid(write_io::log_images(images))
}

pub(crate) proof fn transport_facts(v: AdmissionView, images: Images)
    requires valid(v, images),
    ensures ea_bootstrap::valid(v.boot), ea_write_io::valid_images(images), write_io::transport_images(images),
        images.tx.layout == v.boot.layout, images.journal_block == v.boot.layout.start,
        images.initial_primary == v.boot.source.subrange(0, 4096),
        images.initial_journal == ea_bootstrap::journal_bytes(v.boot),
        images.tx.uuid == ea_bootstrap::journal_identity(v.boot),
        images.partition_bytes as nat == v.boot.source.len(), 0 < images.tx.original.len() <= 8,
{
    reveal(valid);
    reveal(ea_write_io::valid_images);
    reveal(write_io::transport_images);
}

pub(crate) proof fn dirty_prefix_facts(v: AdmissionView, images: Images)
    requires valid(v, images),
    ensures v.prefixes.len() == 2,
        certified(v.boot, v.prefixes[0], marked(v.boot.source, images)),
{ reveal(valid); }

pub(crate) proof fn admission_facts(v: AdmissionView, images: Images)
    requires valid(v, images),
    ensures ea_bootstrap::valid(v.boot), ea_write_io::valid_images(images), write_io::transport_images(images),
        images.tx.layout == v.boot.layout, images.journal_block == v.boot.layout.start,
        images.initial_primary == v.boot.source.subrange(0, 4096),
        images.initial_journal == ea_bootstrap::journal_bytes(v.boot),
        images.tx.uuid == ea_bootstrap::journal_identity(v.boot),
        images.partition_bytes as nat == v.boot.source.len(),
        v.prefixes.len() == 2, 0 < images.tx.original.len() <= 8,
        patch_set::valid(images.tx.original), patch_set::valid(write_io::log_images(images)),
        certified(v.boot, v.prefixes[0], marked(v.boot.source, images)),
        certified(v.boot, v.prefixes[1], home_source(v.boot.source, images)),
        certified(v.boot, v.after(), final_source(v.boot.source, images)),
{
    reveal(valid);
    reveal(ea_write_io::valid_images);
    reveal(write_io::transport_images);
}

pub(crate) proof fn prepared_patch_facts(v: AdmissionView, images: Images)
    requires valid(v, images),
    ensures ea_bootstrap::valid(v.boot), patch_set::valid(images.tx.original),
        v.prepared().before == v.boot.source,
        v.prepared().after == patch_set::apply(v.boot.source, images.tx.original),
        bootstrap_identity::preserved(v.boot, v.prepared().after),
{
    reveal(valid);
    ns_journal_prepared::operation_facts(v.operation(), v.prepared());
}

pub proof fn an_admitted_writer_retains_the_exact_typed_namespace_operation(v: AdmissionView, images: Images)
    requires valid(v, images),
    ensures ns_journal_prepared::valid_operation(v.operation(), v.prepared()),
        crate::ns_mutation_model::prepared_valid(v.prepared()),
        v.prepared().before == v.boot.source,
        images.tx.original == ns_journal_prepared::patches(v.operation()),
        v.prepared().after == patch_set::apply(v.boot.source, images.tx.original),
{
    reveal(valid);
    ns_journal_prepared::operation_facts(v.operation(), v.prepared());
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error { SourceMismatch, NoChanges, Invalid }

pub struct CheckedWriter<'s, 'a> { source: &'s Snapshot<'a>, writer: Writer, certificate: Ghost<Seq<AdmissionView>> }
pub struct Pending<'s, 'a> { source: &'s Snapshot<'a>, pending: ea_write_io::Pending, certificate: Ghost<Seq<AdmissionView>> }

impl<'s, 'a> CheckedWriter<'s, 'a> {
    pub closed spec fn view(&self) -> AdmissionView { self.certificate@[0] }
    pub closed spec fn certificate_count(&self) -> nat { self.certificate@.len() }
    pub closed spec fn owner(&self) -> &Writer { &self.writer }
    pub closed spec fn source_view(&self) -> Seq<u8> { self.source.view() }
    pub open spec fn wf(&self) -> bool { self.certificate_count() == 1 && valid(self.view(), self.owner().images()) && self.view().boot.source == self.source_view() }

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

    pub fn acknowledged(&self) -> (r: bool)
        ensures self.wf(), r == (write_protocol::completed_count(self.owner().state(), self.owner().images().tx.payloads.len())
            > 7 + self.owner().images().tx.payloads.len()),
    {
        proof { use_type_invariant(self); }
        self.writer.acknowledged()
    }

    pub fn abort(self) -> (r: Self)
        ensures r.wf(), r.view() == self.view(), r.owner().images() == self.owner().images(),
            r.owner().state() == (write_protocol::State { faulted: true, ..self.owner().state() }),
    {
        proof { use_type_invariant(&self); }
        let CheckedWriter { source, writer, certificate } = self;
        let writer = ea_write_io::abort(writer);
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
        match ea_write_io::dispatch(writer) {
            Ok(pending) => Ok(Pending { source, pending, certificate }),
            Err(writer) => Err(CheckedWriter { source, writer, certificate }),
        }
    }
}

impl<'s, 'a> Pending<'s, 'a> {
    pub closed spec fn view(&self) -> AdmissionView { self.certificate@[0] }
    pub closed spec fn certificate_count(&self) -> nat { self.certificate@.len() }
    pub closed spec fn owner(&self) -> &Writer { self.pending.owner() }
    pub closed spec fn source_view(&self) -> Seq<u8> { self.source.view() }
    pub open spec fn wf(&self) -> bool { self.certificate_count() == 1 && valid(self.view(), self.owner().images()) && self.view().boot.source == self.source_view() }

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

fn source_matches(source: &Snapshot<'_>, expected: &[u8]) -> (r: bool)
    ensures r == (source.view() == expected@),
{
    if source.partition_bytes() != expected.len() as u64 { return false; }
    let mut offset = 0usize;
    while offset < expected.len()
        invariant offset <= expected.len(), source.view().len() == expected.len(),
            source.view().take(offset as int) == expected@.take(offset as int),
        decreases expected.len() - offset,
    {
        let remaining = expected.len() - offset;
        let amount = if remaining > 65536 { 65536usize } else { remaining };
        let raw = source.capture_bytes(offset as u64, amount).unwrap();
        if !bytes::equal(&raw, &expected[offset..offset + amount]) { return false; }
        assert(raw@ == source.view().subrange(offset as int, offset as int + amount));
        assert(raw@ == expected@.subrange(offset as int, offset as int + amount));
        assert(source.view().take(offset as int + amount) =~= expected@.take(offset as int + amount)) by {
            assert forall|i: int| 0 <= i < offset as int + amount implies
                #[trigger] source.view().take(offset as int + amount)[i]
                    == expected@.take(offset as int + amount)[i] by {
                if i < offset {
                    assert(source.view().take(offset as int)[i] == expected@.take(offset as int)[i]);
                } else {
                    assert(raw@[i - offset as int] == source.view()[i]);
                    assert(raw@[i - offset as int] == expected@[i]);
                }
            }
        }
        offset += amount;
    }
    assert(source.view().take(offset as int) =~= source.view());
    assert(expected@.take(offset as int) =~= expected@);
    assert(source.view() =~= expected@);
    true
}

fn collect(patches: &PatchSet) -> (r: Vec<AfterImage>)
    ensures transaction::images(r@) == patches.view(),
{
    let count = patches.len();
    let mut images = Vec::new();
    let mut index = 0usize;
    while index < count
        invariant images.len() == index <= count == patches.view().len(),
            transaction::images(images@) == patches.view().take(index as int),
        decreases count - index,
    {
        let patch = patches.at(index).unwrap();
        let image = AfterImage::capture(patch.block(), patch.as_slice()).unwrap();
        let ghost previous = transaction::images(images@);
        images.push(image);
        assert(transaction::images(images@) =~= previous.push(image.view()));
        index += 1;
    }
    assert(patches.view().take(index as int) =~= patches.view());
    images
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
        let ghost previous = transaction::images(images@);
        images.push(image);
        assert(transaction::images(images@) =~= previous.push(image.view()));
        index += 1;
    }
    assert(expected.take(count as int) =~= expected);
    match PatchSet::from_images(images) { Ok(patches) => Some(patches), Err(_) => None }
}

fn inspect(source: &Snapshot<'_>, boot: &ea_bootstrap::Bootstrap<'_, '_>,
    inode_budget: u32, node_budget: u64, byte_budget: u64) -> (r: Option<Ghost<Seq<NamespaceView>>>)
    ensures match r { Some(c) => c@.len() == 1 && certified(boot.view(), c@[0], source.view()), None => true },
{
    if !ea_bootstrap::check_identity(boot, source) { return None; }
    let namespace = match ea_namespace::inspect_journal(source, inode_budget, node_budget, byte_budget) {
        Some(namespace) => namespace, None => { return None; }
    };
    let mapping = namespace.allocation().journal();
    let original = boot.layout();
    if mapping.physical_start() != original.physical_start() || mapping.blocks() != original.blocks()
        || mapping.filesystem_blocks() != original.filesystem_blocks() { return None; }
    let ghost certificate = seq![namespace.view()];
    Some(Ghost(certificate))
}

fn certify_sources(source: &Snapshot<'_>, writer: &Writer, boot: &ea_bootstrap::Bootstrap<'_, '_>,
    inode_budget: u32, node_budget: u64, byte_budget: u64) -> (r: Option<Ghost<Seq<NamespaceView>>>)
    ensures match r { Some(c) => c@.len() == 3
        && certified(boot.view(), c@[0], marked(source.view(), writer.images()))
        && certified(boot.view(), c@[1], home_source(source.view(), writer.images()))
        && certified(boot.view(), c@[2], final_source(source.view(), writer.images()))
        && patch_set::valid(writer.images().tx.original)
        && patch_set::valid(write_io::log_images(writer.images())), None => true },
{
    let ghost images = writer.images();
    let homes = match collect_images(writer, false) { Some(homes) => homes, None => { return None; } };
    let logs = match collect_images(writer, true) { Some(logs) => logs, None => { return None; } };
    let empty = PatchSet::new();
    let dirty = match empty.insert(0, writer.dirty_marker()) { Ok(dirty) => dirty, Err(_) => { return None; } };
    assert(dirty.view() =~= seq![ImageView { block: 0, image: images.dirty }]);
    let marked = match source.overlay(&dirty) { Some(marked) => marked, None => { return None; } };
    let before = match inspect(&marked, boot, inode_budget, node_budget, byte_budget) {
        Some(checked) => checked, None => { return None; }
    };
    let home_source = match marked.overlay(&homes) { Some(home_source) => home_source, None => { return None; } };
    let after_homes = match inspect(&home_source, boot, inode_budget, node_budget, byte_budget) {
        Some(checked) => checked, None => { return None; }
    };
    let logged = match marked.overlay(&logs) { Some(logged) => logged, None => { return None; } };
    let checkpointed = match logged.overlay(&homes) { Some(checkpointed) => checkpointed, None => { return None; } };
    let (journal, raw_tail) = writer.retirement_image();
    let empty = PatchSet::new();
    let tail = match empty.insert(journal, raw_tail) { Ok(tail) => tail, Err(_) => { return None; } };
    assert(tail.view() =~= seq![ImageView { block: journal, image: raw_tail@ }]);
    let final_source = match checkpointed.overlay(&tail) { Some(final_source) => final_source, None => { return None; } };
    let after = match inspect(&final_source, boot, inode_budget, node_budget, byte_budget) {
        Some(checked) => checked, None => { return None; }
    };
    let ghost certificates = seq![before@[0], after_homes@[0], after@[0]];
    Some(Ghost(certificates))
}

proof fn assemble_certificate(v: AdmissionView, images: Images)
    requires v.prepared_records.len() == 1, v.operation_records.len() == 1, v.after_records.len() == 1,
        ea_bootstrap::valid(v.boot), ea_write_io::valid_images(images),
        ns_journal_prepared::valid_operation(v.operation(), v.prepared()), v.prepared().before == v.boot.source,
        images.tx.original == ns_journal_prepared::patches(v.operation()), 0 < images.tx.original.len() <= 8,
        images.initial_primary == v.boot.source.subrange(0, 4096),
        images.initial_journal == ea_bootstrap::journal_bytes(v.boot),
        images.tx.uuid == ea_bootstrap::journal_identity(v.boot), images.tx.layout == v.boot.layout,
        images.partition_bytes as nat == v.boot.source.len(),
        bootstrap_identity::preserved(v.boot, v.prepared().after), v.prefixes.len() == 2,
        certified(v.boot, v.prefixes[0], marked(v.boot.source, images)),
        certified(v.boot, v.prefixes[1], home_source(v.boot.source, images)),
        certified(v.boot, v.after(), final_source(v.boot.source, images)),
        patch_set::valid(images.tx.original), patch_set::valid(write_io::log_images(images)),
    ensures valid(v, images),
{ reveal(valid); }

pub fn prepare<'s, 'a>(source: &'s Snapshot<'a>, prepared: Prepared,
    inode_budget: u32, node_budget: u64, byte_budget: u64) -> (r: Result<CheckedWriter<'s, 'a>, Error>)
    ensures match r { Ok(ready) => ready.wf() && ready.view().boot.source == source.view()
        && ready.view().prepared() == prepared.view() && ready.view().operation() == prepared.operation()
        && ready.owner().state() == write_protocol::initial(), Err(_) => true },
{
    if !source_matches(source, prepared.before_bytes()) { return Err(Error::SourceMismatch); }
    if bytes::equal(prepared.before_bytes(), prepared.bytes()) { return Err(Error::NoChanges); }
    let patches = prepared.patches();
    if patches.len() == 0 { return Err(Error::NoChanges); }
    if patches.len() > 8 { return Err(Error::Invalid); }
    let boot = match ea_bootstrap::locate(source) { Some(boot) => boot, None => { return Err(Error::Invalid); } };
    let operation_source = Snapshot::from_bytes(prepared.bytes());
    if !ea_bootstrap::check_identity(&boot, &operation_source) { return Err(Error::Invalid); }
    let input = collect(patches);
    let writer = match ea_write_io::prepare(source, boot.journal_uuid(), boot.layout().duplicate(), input) {
        Some(writer) => writer, None => { return Err(Error::Invalid); }
    };
    let ghost images = writer.images();
    let checked = match certify_sources(source, &writer, &boot, inode_budget, node_budget, byte_budget) {
        Some(checked) => checked, None => { return Err(Error::Invalid); }
    };
    let ghost proposals = seq![prepared.view()];
    let ghost operations = seq![prepared.operation()];
    let ghost results = seq![checked@[2]];
    let ghost certificate = AdmissionView { boot: boot.view(), prepared_records: proposals, operation_records: operations,
        prefixes: checked@.take(2), after_records: results };
    proof { assemble_certificate(certificate, images); }
    let ghost certificates = seq![certificate];
    Ok(CheckedWriter { source, writer, certificate: Ghost(certificates) })
}

}
