// SPDX-License-Identifier: MPL-2.0

//! One owned EA namespace transaction using the existing serial JBD2 protocol.
//! The transport accepts actual EA feature bytes; filesystem admission and
//! physical completion authority remain in their separate sealed adapters.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, ea_source, epoch, frozen::FrozenBlock, journal_state, journal_superblock,
    layout::JournalLayout, recovery_io::{Command, CommandView}, recovery_request::Completion,
    snapshot::Snapshot, super_state, transaction::{self, AfterImage, Encoded},
    write_io::{self, *}, write_protocol::{self, Phase, State}};

verus! {

#[verifier::opaque]
pub open spec fn valid_images(v: Images) -> bool {
    &&& write_io::transport_images(v)
    &&& ea_source::header_accepted(v.initial_primary.subrange(1024, 2048), v.partition_bytes)
    &&& ea_source::header_accepted(v.dirty.subrange(1024, 2048), v.partition_bytes)
    &&& !crate::feature_policy::readonly(v.initial_primary.subrange(1024, 2048))
    &&& (forall|i: int| 0 <= i < v.tx.original.len() ==> (#[trigger] v.tx.original[i]).block >= 2)
}

pub struct Writer {
    tx: Encoded, dirty: FrozenBlock, activation: FrozenBlock, tail: FrozenBlock,
    initial_journal: Ghost<Seq<u8>>, initial_primary: Ghost<Seq<u8>>, journal_block: u32, partition_bytes: u64,
    state: State,
}

impl Writer {
    pub closed spec fn images(&self) -> Images {
        Images { tx: self.tx.view(), dirty: self.dirty.view(), activation: self.activation.view(), tail: self.tail.view(),
            initial_journal: self.initial_journal@, initial_primary: self.initial_primary@,
            journal_block: self.journal_block, partition_bytes: self.partition_bytes }
    }
    pub closed spec fn state(&self) -> State { self.state }

    pub open spec fn wf(&self) -> bool { valid_images(self.images()) && write_protocol::wf(self.state(), self.images().tx.payloads.len()) }

    #[verifier::type_invariant]
    spec fn valid(self) -> bool { self.wf() }

    pub fn finished(&self) -> (r: bool)
        ensures r == (self.state().phase is Done && !self.state().pending && !self.state().faulted),
    {
        match self.state.phase { Phase::Done => !self.state.pending && !self.state.faulted, _ => false }
    }
    pub fn failed(&self) -> (r: bool) ensures r == self.state().faulted { self.state.faulted }

    /// This frontier records a successful commit-flush report. Physical
    /// durability follows only when the device adapter satisfies its contract.
    pub fn acknowledged(&self) -> (r: bool)
        ensures r == (write_protocol::completed_count(self.state(), self.images().tx.payloads.len())
            > 7 + self.images().tx.payloads.len()),
    {
        proof { use_type_invariant(self); }
        match self.state.phase {
            Phase::Homes | Phase::HomeFence | Phase::Retire | Phase::RetirementFence | Phase::Done => true,
            _ => false,
        }
    }


    pub fn original_count(&self) -> (r: usize)
        ensures valid_images(self.images()), r == self.images().tx.original.len(), r <= 250,
    {
        proof { use_type_invariant(self); reveal(valid_images); reveal(write_io::transport_images); }
        self.tx.payload_count()
    }

    pub fn original_image(&self, index: usize) -> (r: Option<(u32, &[u8])>)
        ensures valid_images(self.images()), match r {
            Some((block, image)) => index < self.images().tx.original.len()
                && self.images().tx.original[index as int] == (transaction::ImageView { block, image: image@ }) && image.len() == 4096,
            None => index >= self.images().tx.original.len(),
        },
    {
        proof { use_type_invariant(self); image_shapes(self.images()); }
        self.tx.original_at(index)
    }

    pub fn dirty_marker(&self) -> (r: &[u8])
        ensures valid_images(self.images()), r@ == self.images().dirty, r.len() == 4096,
    {
        proof { use_type_invariant(self); reveal(valid_images); reveal(write_io::transport_images); }
        self.dirty.as_slice()
    }

    pub fn retirement_image(&self) -> (r: (u32, &[u8]))
        ensures valid_images(self.images()), r.0 == self.images().journal_block, r.1@ == self.images().tail, r.1.len() == 4096,
    {
        proof { use_type_invariant(self); reveal(valid_images); reveal(write_io::transport_images); }
        (self.journal_block, self.tail.as_slice())
    }

    pub fn log_record_count(&self) -> (r: usize)
        ensures valid_images(self.images()), r == log_images(self.images()).len(), 3 <= r <= 252,
    {
        proof { use_type_invariant(self); reveal(valid_images); reveal(write_io::transport_images); }
        self.tx.payload_count() + 2
    }

    pub fn log_record(&self, index: usize) -> (r: Option<(u32, &[u8])>)
        ensures valid_images(self.images()), match r {
            Some((block, image)) => index < log_images(self.images()).len()
                && log_images(self.images())[index as int] == (transaction::ImageView { block, image: image@ }) && image.len() == 4096,
            None => index >= log_images(self.images()).len(),
        },
    {
        proof { use_type_invariant(self); image_shapes(self.images()); command_context(self.images()); }
        let count = self.tx.payload_count();
        if index >= count + 2 { return None; }
        let block = self.journal_block + 1 + index as u32;
        if index == 0 { Some((block, self.tx.descriptor_bytes())) }
        else if index == count + 1 { Some((block, self.tx.commit_bytes())) }
        else { Some((block, self.tx.payload_at(index - 1).unwrap())) }
    }
}

pub fn abort(mut writer: Writer) -> (r: Writer)
    ensures r.images() == writer.images(), r.state() == (State { faulted: true, ..writer.state() }),
{
    proof { use_type_invariant(&writer); }
    writer.state = State { faulted: true, ..writer.state };
    writer
}

pub struct Pending { writer: Writer }

impl Pending {
    pub closed spec fn owner(&self) -> &Writer { &self.writer }

    #[verifier::type_invariant]
    spec fn valid(self) -> bool { self.owner().state().pending }

    #[verifier::rlimit(40)]
    pub fn pending_command(&self) -> (r: Command<'_>)
        ensures r.view() == expected(self.owner().images(), self.owner().state()),
            match r.view() {
                CommandView::Write { block, image } => image.len() == 4096 && block < self.owner().images().tx.layout.fs_blocks
                    && block as nat * 4096 + 4096 <= self.owner().images().partition_bytes,
                CommandView::Flush => true,
            },
    {
        proof { use_type_invariant(self); use_type_invariant(&self.writer); command_context(self.writer.images()); }
        let writer = &self.writer;
        let count = writer.tx.payload_count();
        proof { expected_command_is_confined(writer.images(), writer.state()); }
        match writer.state.phase {
            Phase::MarkDirty => Command::Write { block: 0, image: writer.dirty.as_slice() },
            Phase::Activate => Command::Write { block: writer.journal_block, image: writer.activation.as_slice() },
            Phase::Descriptor => Command::Write { block: writer.journal_block + 1, image: writer.tx.descriptor_bytes() },
            Phase::Payloads => Command::Write { block: writer.journal_block + 2 + writer.state.cursor as u32,
                image: writer.tx.payload_at(writer.state.cursor).unwrap() },
            Phase::Commit => Command::Write { block: writer.journal_block + 2 + count as u32, image: writer.tx.commit_bytes() },
            Phase::Homes => {
                let (block, image) = writer.tx.original_at(writer.state.cursor).unwrap();
                Command::Write { block, image }
            },
            Phase::Retire => Command::Write { block: writer.journal_block, image: writer.tail.as_slice() },
            _ => Command::Flush,
        }
    }

    pub fn abort_pending(self) -> (r: Self)
        ensures r.owner().images() == self.owner().images(),
            r.owner().state() == (State { faulted: true, ..self.owner().state() }),
    {
        proof { use_type_invariant(&self); use_type_invariant(&self.writer); }
        let Pending { mut writer } = self;
        writer.state = State { faulted: true, ..writer.state };
        Pending { writer }
    }

    pub fn finish_pending(self, outcome: Completion) -> (r: Writer)
        ensures r.images() == self.owner().images(),
            r.state() == write_protocol::completed(self.owner().state(), self.owner().images().tx.payloads.len(), outcome is Succeeded),
    {
        proof { use_type_invariant(&self); use_type_invariant(&self.writer); }
        let Pending { mut writer } = self;
        let succeeded = match outcome { Completion::Succeeded => true, Completion::Failed => false };
        let count = writer.tx.payload_count();
        writer.state = write_protocol::finish(writer.state, count, succeeded);
        writer
    }
}

pub fn dispatch(mut writer: Writer) -> (r: Result<Pending, Writer>)
    ensures match r {
        Ok(p) => p.owner().images() == writer.images() && !writer.state().pending && !writer.state().faulted
            && !(writer.state().phase is Done) && p.owner().state() == write_protocol::started(writer.state()),
        Err(w) => w.images() == writer.images() && w.state() == writer.state()
            && (writer.state().pending || writer.state().faulted || writer.state().phase is Done),
    },
{
    proof { use_type_invariant(&writer); }
    let done = match writer.state.phase { Phase::Done => true, _ => false };
    if writer.state.pending || writer.state.faulted || done { return Err(writer); }
    let count = writer.tx.payload_count();
    writer.state = write_protocol::start(writer.state, count);
    Ok(Pending { writer })
}

proof fn transport(v: Images)
    requires valid_images(v),
    ensures write_io::transport_images(v),
{ reveal(valid_images); }

proof fn image_shapes(v: Images)
    requires valid_images(v),
    ensures v.tx.descriptor.len() == 4096, v.tx.commit.len() == 4096,
        forall|i: int| 0 <= i < v.tx.original.len() ==> (#[trigger] v.tx.original[i]).image.len() == 4096,
        forall|i: int| 0 <= i < v.tx.payloads.len() ==> (#[trigger] v.tx.payloads[i]).len() == 4096,
{
    transport(v);
    write_io::transport_image_shapes(v);
}

proof fn command_context(v: Images)
    requires valid_images(v),
    ensures 0 < v.tx.payloads.len() <= 250, v.tx.original.len() == v.tx.payloads.len(),
        v.journal_block as nat + v.tx.payloads.len() + 3 <= v.tx.layout.fs_blocks,
        v.tx.layout.fs_blocks as nat * 4096 <= v.partition_bytes,
{
    transport(v);
    write_io::transport_command_context(v);
}

pub proof fn expected_command_is_confined(v: Images, state: State)
    requires valid_images(v), write_protocol::wf(state, v.tx.payloads.len()),
    ensures match expected(v, state) {
        CommandView::Write { block, image } => image.len() == 4096 && block < v.tx.layout.fs_blocks
            && block as nat * 4096 + 4096 <= v.partition_bytes,
        CommandView::Flush => true,
    },
{
    transport(v);
    write_io::expected_transport_command_is_confined(v, state);
}

pub fn prepare(source: &Snapshot<'_>, uuid: &[u8], layout: JournalLayout, input: Vec<AfterImage>) -> (r: Option<Writer>)
    ensures match r {
        Some(w) => w.wf() && valid_images(w.images()) && w.state() == write_protocol::initial()
            && w.images().tx.layout == layout.view() && w.images().tx.uuid == uuid@
            && w.images().partition_bytes as nat == source.view().len()
            && w.images().journal_block == layout.view().start
            && w.images().initial_primary == source.view().subrange(0, 4096)
            && w.images().initial_journal == source.view().subrange(layout.view().start as int * 4096,
                (layout.view().start as int + layout.view().journal_blocks) * 4096)
            && w.images().tx.original == transaction::images(input@),
        None => true,
    },
{
    hide(crate::crc::fold);
    hide(ea_source::header_accepted);
    hide(journal_superblock::accepted);
    let partition_bytes = source.partition_bytes();
    if !layout.valid() { return None; }
    let header = match ea_source::parse(source) { Some(header) => header, None => { return None; } };
    let (blocks, _, _, _) = header.parameters();
    proof { reveal(ea_source::header_valid); }
    if blocks != layout.filesystem_blocks() { return None; }
    let primary = source.block(0).unwrap().as_slice();
    if crate::feature_policy::is_readonly(&primary[1024..2048]).unwrap() { return None; }
    if input.len() == 0 || input.len() > 250 { return None; }
    let mut index = 0usize;
    while index < input.len()
        invariant index <= input.len(),
            forall|i: int| 0 <= i < index ==> (#[trigger] input@[i].view()).block >= 2,
        decreases input.len() - index,
    {
        if input[index].block() < 2 { return None; }
        index += 1;
    }
    let journal = match source.capture(layout.physical_start(), layout.blocks()) { Some(journal) => journal, None => { return None; } };
    let info = match journal_superblock::parse(&journal[..1024], uuid, layout.blocks()) { Some(info) => info, None => { return None; } };
    if info.start != 0 { return None; }
    let sequence = match epoch::fresh_sequence(&journal, info.sequence) { Some(sequence) => sequence, None => { return None; } };
    let dirty = match crate::ea_super_state::recovery_image(primary, partition_bytes, true) {
        Some(dirty) => dirty, None => { return None; }
    };
    let tx = match transaction::encode(input, uuid, sequence, &layout, dirty.as_slice(), partition_bytes) {
        Some(tx) => tx, None => { return None; }
    };
    proof {
        reveal(ea_source::header_valid);
        reveal(ea_source::header_accepted);
        assert(journal@.subrange(0, 4096).subrange(0, 1024) =~= journal@.subrange(0, 1024));
        assert(bytes::be32(journal@.subrange(0, 4096), 28) == 0);
        assert(journal_state::input_ok(journal@.subrange(0, 4096), uuid@, layout.view().journal_blocks, sequence, 1));
    }
    let activation = journal_state::encode(&journal[..4096], uuid, layout.blocks(), sequence, 1).unwrap();
    assert(journal_state::input_ok(activation.view(), uuid@, layout.view().journal_blocks, (sequence + 1) as u32, 0));
    let tail = journal_state::encode(activation.as_slice(), uuid, layout.blocks(), sequence + 1, 0).unwrap();
    let journal_block = layout.physical_start();
    proof { write_protocol::initialization(tx.view().payloads.len()); }
    let ghost assembled = Images { tx: tx.view(), dirty: dirty.view(), activation: activation.view(), tail: tail.view(),
        initial_journal: journal@, initial_primary: primary@, journal_block, partition_bytes: partition_bytes };
    assert(valid_images(assembled)) by { reveal(valid_images); reveal(write_io::transport_images); }
    let result = Writer { tx, dirty, activation, tail, initial_journal: Ghost(journal@), initial_primary: Ghost(primary@),
        journal_block, partition_bytes: partition_bytes, state: State { phase: Phase::MarkDirty, cursor: 0, request: 0, pending: false, faulted: false } };
    assert(result.images() == assembled);
    Some(result)
}

}
