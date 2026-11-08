// SPDX-License-Identifier: MPL-2.0

//! Owned full-data-journal command pipeline. Candidate construction validates
//! local geometry and bytes; it does not replace global filesystem authority.
//! A successful device report needs a concrete adapter contract before use.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, epoch, frozen::FrozenBlock, journal_state, journal_superblock, layout::JournalLayout,
    recovery_io::{Command, CommandView}, recovery_request::Completion, super_state, superblock,
    transaction::{self, AfterImage, Encoded, TransactionView}, write_protocol::{self, Phase, State}};

verus! {

pub struct Images {
    pub tx: TransactionView, pub dirty: Seq<u8>, pub activation: Seq<u8>, pub tail: Seq<u8>,
    pub initial_journal: Seq<u8>, pub initial_primary: Seq<u8>, pub journal_block: u32, pub partition_bytes: u64,
}

pub open spec fn log_images(v: Images) -> Seq<transaction::ImageView> {
    Seq::new(v.tx.payloads.len() + 2, |i: int| transaction::ImageView {
        block: (v.journal_block as int + 1 + i) as u32,
        image: if i == 0 { v.tx.descriptor } else if i == v.tx.payloads.len() as int + 1 { v.tx.commit } else { v.tx.payloads[i - 1] },
    })
}

/// Exact serial JBD2 transport, independent of filesystem source admission.
/// Callers separately validate the actual primary and after-image sources.
/// This predicate supplies no operation, mount, EA or device authority.
#[verifier::opaque]
pub open spec fn transport_images(v: Images) -> bool {
    &&& transaction::wf(v.tx) && v.journal_block == v.tx.layout.start
    &&& v.tx.layout.fs_blocks as nat * 4096 <= v.partition_bytes
    &&& v.initial_journal.len() == v.tx.layout.journal_blocks as nat * 4096
    &&& bytes::le32(v.initial_primary, 1028) == v.tx.layout.fs_blocks
    &&& journal_superblock::accepted(v.initial_journal.subrange(0, 1024), v.tx.uuid, v.tx.layout.journal_blocks)
    &&& bytes::be32(v.initial_journal, 28) == 0
    &&& epoch::newer(v.initial_journal, bytes::be32(v.initial_journal, 24) as u32, v.tx.sequence)
    &&& super_state::preserves(v.initial_primary, v.dirty)
    &&& v.dirty == super_state::recovery_bytes(v.initial_primary, true)
    &&& super_state::is_dirty(v.dirty)
    &&& v.tx.primary == v.dirty && v.tx.partition_bytes == v.partition_bytes
    &&& journal_state::preserves(v.initial_journal.subrange(0, 4096), v.activation)
    &&& journal_superblock::accepted(v.activation.subrange(0, 1024), v.tx.uuid, v.tx.layout.journal_blocks)
    &&& bytes::be32(v.activation, 24) == v.tx.sequence && bytes::be32(v.activation, 28) == 1
    &&& bytes::be32(v.activation, 40) == 17
    &&& journal_state::preserves(v.activation, v.tail)
    &&& journal_superblock::accepted(v.tail.subrange(0, 1024), v.tx.uuid, v.tx.layout.journal_blocks)
    &&& bytes::be32(v.tail, 24) == v.tx.sequence as nat + 1 && bytes::be32(v.tail, 28) == 0
}

pub proof fn valid_images_implies_transport_images(v: Images)
    requires valid_images(v),
    ensures transport_images(v),
{
    reveal(valid_images);
    reveal(transport_images);
}

#[verifier::opaque]
pub open spec fn valid_images(v: Images) -> bool {
    &&& transaction::wf(v.tx) && v.journal_block == v.tx.layout.start
    &&& v.tx.layout.fs_blocks as nat * 4096 <= v.partition_bytes
    &&& v.initial_journal.len() == v.tx.layout.journal_blocks as nat * 4096
    &&& superblock::accepted(v.initial_primary.subrange(1024, 2048), v.partition_bytes)
    &&& !crate::feature_policy::readonly(v.initial_primary.subrange(1024, 2048))
    &&& bytes::le32(v.initial_primary, 1028) == v.tx.layout.fs_blocks
    &&& journal_superblock::accepted(v.initial_journal.subrange(0, 1024), v.tx.uuid, v.tx.layout.journal_blocks)
    &&& bytes::be32(v.initial_journal, 28) == 0
    &&& epoch::newer(v.initial_journal, bytes::be32(v.initial_journal, 24) as u32, v.tx.sequence)
    &&& super_state::preserves(v.initial_primary, v.dirty)
    &&& v.dirty == super_state::recovery_bytes(v.initial_primary, true)
    &&& superblock::accepted(v.dirty.subrange(1024, 2048), v.partition_bytes) && super_state::is_dirty(v.dirty)
    &&& v.tx.primary == v.dirty && v.tx.partition_bytes == v.partition_bytes
    &&& journal_state::preserves(v.initial_journal.subrange(0, 4096), v.activation)
    &&& journal_superblock::accepted(v.activation.subrange(0, 1024), v.tx.uuid, v.tx.layout.journal_blocks)
    &&& bytes::be32(v.activation, 24) == v.tx.sequence && bytes::be32(v.activation, 28) == 1
    &&& bytes::be32(v.activation, 40) == 17
    &&& journal_state::preserves(v.activation, v.tail)
    &&& journal_superblock::accepted(v.tail.subrange(0, 1024), v.tx.uuid, v.tx.layout.journal_blocks)
    &&& bytes::be32(v.tail, 24) == v.tx.sequence as nat + 1 && bytes::be32(v.tail, 28) == 0
}

pub open spec fn expected(v: Images, state: State) -> CommandView {
    match state.phase {
        Phase::MarkDirty => CommandView::Write { block: 0, image: v.dirty },
        Phase::Activate => CommandView::Write { block: v.journal_block, image: v.activation },
        Phase::Descriptor => CommandView::Write { block: (v.journal_block + 1) as u32, image: v.tx.descriptor },
        Phase::Payloads => CommandView::Write { block: (v.journal_block as int + 2 + state.cursor) as u32,
            image: v.tx.payloads[state.cursor as int] },
        Phase::Commit => CommandView::Write { block: (v.journal_block as int + 2 + v.tx.payloads.len()) as u32, image: v.tx.commit },
        Phase::Homes => CommandView::Write { block: v.tx.original[state.cursor as int].block,
            image: v.tx.original[state.cursor as int].image },
        Phase::Retire => CommandView::Write { block: v.journal_block, image: v.tail },
        _ => CommandView::Flush,
    }
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

    #[verifier::type_invariant]
    spec fn valid(self) -> bool {
        valid_images(self.images()) && write_protocol::wf(self.state(), self.images().tx.payloads.len())
    }

    pub fn finished(&self) -> (r: bool)
        ensures r == (self.state().phase is Done && !self.state().pending && !self.state().faulted),
    {
        match self.state.phase { Phase::Done => !self.state.pending && !self.state.faulted, _ => false }
    }
    pub fn failed(&self) -> (r: bool) ensures r == self.state().faulted { self.state.faulted }

    pub fn original_count(&self) -> (r: usize)
        ensures valid_images(self.images()), r == self.images().tx.original.len(), r <= 250,
    {
        proof { use_type_invariant(self); reveal(valid_images); }
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
        proof { use_type_invariant(self); reveal(valid_images); }
        self.dirty.as_slice()
    }

    pub fn retirement_image(&self) -> (r: (u32, &[u8]))
        ensures valid_images(self.images()), r.0 == self.images().journal_block, r.1@ == self.images().tail, r.1.len() == 4096,
    {
        proof { use_type_invariant(self); reveal(valid_images); }
        (self.journal_block, self.tail.as_slice())
    }

    pub fn log_record_count(&self) -> (r: usize)
        ensures valid_images(self.images()), r == log_images(self.images()).len(), 3 <= r <= 252,
    {
        proof { use_type_invariant(self); reveal(valid_images); }
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

#[verifier::rlimit(30)]
pub proof fn expected_command_is_confined(v: Images, state: State)
    requires valid_images(v), write_protocol::wf(state, v.tx.payloads.len()),
    ensures match expected(v, state) {
        CommandView::Write { block, image } => image.len() == 4096 && block < v.tx.layout.fs_blocks
            && block as nat * 4096 + 4096 <= v.partition_bytes,
        CommandView::Flush => true,
    },
{
    valid_images_implies_transport_images(v);
    expected_transport_command_is_confined(v, state)
}

#[verifier::rlimit(30)]
pub proof fn expected_transport_command_is_confined(v: Images, state: State)
    requires transport_images(v), write_protocol::wf(state, v.tx.payloads.len()),
    ensures match expected(v, state) {
        CommandView::Write { block, image } => image.len() == 4096 && block < v.tx.layout.fs_blocks
            && block as nat * 4096 + 4096 <= v.partition_bytes,
        CommandView::Flush => true,
    },
{
    transport_command_context(v);
    transport_image_shapes(v);
    transport_state_image_shapes(v);
    if state.phase is Homes { transport_home_bounds(v, state.cursor as int); }
}

proof fn state_image_shapes(v: Images)
    requires valid_images(v),
    ensures v.dirty.len() == 4096, v.activation.len() == 4096, v.tail.len() == 4096,
{
    valid_images_implies_transport_images(v);
    transport_state_image_shapes(v)
}

pub proof fn transport_state_image_shapes(v: Images)
    requires transport_images(v),
    ensures v.dirty.len() == 4096, v.activation.len() == 4096, v.tail.len() == 4096,
{ reveal(transport_images); }

proof fn home_bounds(v: Images, i: int)
    requires valid_images(v), 0 <= i < v.tx.original.len(),
    ensures v.tx.original[i].block < v.tx.layout.fs_blocks,
{
    valid_images_implies_transport_images(v);
    transport_home_bounds(v, i)
}

pub proof fn transport_home_bounds(v: Images, i: int)
    requires transport_images(v), 0 <= i < v.tx.original.len(),
    ensures v.tx.original[i].block < v.tx.layout.fs_blocks,
{
    hide(crate::crc::fold);
    reveal(transport_images);
    assert(crate::replay::payload_for_layout(v.tx.tags[i], v.tx.payloads[i], v.tx.sequence, v.tx.seed, v.tx.layout));
}


spec fn replay_candidate_allowed(v: Images, i: int) -> bool {
    v.tx.original[i].block < v.tx.layout.fs_blocks && v.tx.original[i].image.len() == 4096
}

proof fn command_context(v: Images)
    requires valid_images(v),
    ensures 0 < v.tx.payloads.len() <= 250, v.tx.original.len() == v.tx.payloads.len(),
        v.journal_block as nat + v.tx.payloads.len() + 3 <= v.tx.layout.fs_blocks,
        v.tx.layout.fs_blocks as nat * 4096 <= v.partition_bytes,
{
    valid_images_implies_transport_images(v);
    transport_command_context(v)
}

pub proof fn transport_command_context(v: Images)
    requires transport_images(v),
    ensures 0 < v.tx.payloads.len() <= 250, v.tx.original.len() == v.tx.payloads.len(),
        v.journal_block as nat + v.tx.payloads.len() + 3 <= v.tx.layout.fs_blocks,
        v.tx.layout.fs_blocks as nat * 4096 <= v.partition_bytes,
{
    reveal(transport_images);
}

proof fn image_shapes(v: Images)
    requires valid_images(v),
    ensures v.tx.descriptor.len() == 4096, v.tx.commit.len() == 4096,
        forall|i: int| 0 <= i < v.tx.original.len() ==> (#[trigger] v.tx.original[i]).image.len() == 4096,
        forall|i: int| 0 <= i < v.tx.payloads.len() ==> (#[trigger] v.tx.payloads[i]).len() == 4096,
{
    valid_images_implies_transport_images(v);
    transport_image_shapes(v)
}

pub proof fn transport_image_shapes(v: Images)
    requires transport_images(v),
    ensures v.tx.descriptor.len() == 4096, v.tx.commit.len() == 4096,
        forall|i: int| 0 <= i < v.tx.original.len() ==> (#[trigger] v.tx.original[i]).image.len() == 4096,
        forall|i: int| 0 <= i < v.tx.payloads.len() ==> (#[trigger] v.tx.payloads[i]).len() == 4096,
{
    hide(crate::crc::fold);
    reveal(transport_images);
    assert forall|i: int| 0 <= i < v.tx.payloads.len() implies (#[trigger] v.tx.payloads[i]).len() == 4096 by {
        assert(crate::replay::payload_for_layout(v.tx.tags[i], v.tx.payloads[i], v.tx.sequence, v.tx.seed, v.tx.layout));
    }
    assert forall|i: int| 0 <= i < v.tx.original.len() implies (#[trigger] v.tx.original[i]).image.len() == 4096 by {
        assert(crate::replay::payload_for_layout(v.tx.tags[i], v.tx.payloads[i], v.tx.sequence, v.tx.seed, v.tx.layout));
        assert(crate::replay::restored(v.tx.payloads[i], v.tx.tags[i].flags % 2 == 1) == v.tx.original[i].image);
        assert(crate::replay::restored(v.tx.payloads[i], v.tx.tags[i].flags % 2 == 1).len() == v.tx.payloads[i].len());
    }
}

pub open spec fn can_prepare(journal: Seq<u8>, uuid: Seq<u8>, layout: &JournalLayout, primary: Seq<u8>,
    partition_bytes: u64, input: Seq<transaction::ImageView>) -> bool {
    &&& layout.wf() && primary.len() == 4096
    &&& journal.len() == layout.view().journal_blocks as nat * 4096
    &&& superblock::accepted(primary.subrange(1024, 2048), partition_bytes)
    &&& !crate::feature_policy::readonly(primary.subrange(1024, 2048))
    &&& layout.view().fs_blocks as nat == bytes::le32(primary, 1028)
    &&& journal_superblock::accepted(journal.subrange(0, 1024), uuid, layout.view().journal_blocks)
    &&& bytes::be32(journal, 28) == 0
    &&& epoch::admissible(journal, bytes::be32(journal, 24) as u32)
    &&& transaction::input_ok(input, uuid, 1, layout, super_state::recovery_bytes(primary, true), partition_bytes)
}

#[verifier::rlimit(40)]
pub fn prepare(journal: &[u8], uuid: &[u8], layout: JournalLayout, primary: &[u8], partition_bytes: u64,
    input: Vec<AfterImage>) -> (r: Option<Writer>)
    ensures match r {
        Some(w) => valid_images(w.images()) && w.state() == write_protocol::initial()
            && w.images().tx.layout == layout.view() && w.images().tx.uuid == uuid@
            && w.images().partition_bytes == partition_bytes && w.images().journal_block == layout.view().start
            && w.images().initial_journal == journal@ && w.images().initial_primary == primary@
            && w.images().tx.original == transaction::images(input@)
            && can_prepare(journal@, uuid@, &layout, primary@, partition_bytes, transaction::images(input@)),
        None => !can_prepare(journal@, uuid@, &layout, primary@, partition_bytes, transaction::images(input@)),
    },
{
    hide(crate::crc::fold);
    hide(superblock::accepted);
    hide(journal_superblock::accepted);
    if !layout.valid() || primary.len() != 4096 || journal.len() as u64 != layout.blocks() as u64 * 4096 { return None; }
    if crate::feature_policy::is_readonly(&primary[1024..2048]).unwrap() { return None; }
    let boot = match superblock::parse(&primary[1024..2048], partition_bytes) { Some(s) => s, None => { return None; } };
    if boot.blocks() != layout.filesystem_blocks() { return None; }
    assert(layout.view().fs_blocks as nat * 4096 <= partition_bytes) by { reveal(superblock::accepted); }
    let info = match journal_superblock::parse(&journal[..1024], uuid, layout.blocks()) { Some(s) => s, None => { return None; } };
    if info.start != 0 { return None; }
    let sequence = match epoch::fresh_sequence(journal, info.sequence) { Some(s) => s, None => { return None; } };
    let dirty = super_state::recovery_image(primary, partition_bytes, true).unwrap();
    let tx = match transaction::encode(input, uuid, sequence, &layout, dirty.as_slice(), partition_bytes) {
        Some(tx) => tx, None => { return None; }
    };
    proof {
        assert(journal@.subrange(0, 4096).subrange(0, 1024) =~= journal@.subrange(0, 1024));
        assert(bytes::be32(journal@.subrange(0, 4096), 28) == 0);
        assert(journal_state::input_ok(journal@.subrange(0, 4096), uuid@, layout.view().journal_blocks, sequence, 1));
    }
    let activation = journal_state::encode(&journal[..4096], uuid, layout.blocks(), sequence, 1).unwrap();
    assert(journal_state::input_ok(activation.view(), uuid@, layout.view().journal_blocks, (sequence + 1) as u32, 0));
    let tail = journal_state::encode(activation.as_slice(), uuid, layout.blocks(), sequence + 1, 0).unwrap();
    let journal_block = (layout.offset(0, partition_bytes).unwrap() / 4096) as u32;
    proof { write_protocol::initialization(tx.view().payloads.len()); }
    let ghost assembled = Images { tx: tx.view(), dirty: dirty.view(), activation: activation.view(), tail: tail.view(),
        initial_journal: journal@, initial_primary: primary@, journal_block, partition_bytes };
    assert(valid_images(assembled)) by { reveal(valid_images); }
    let result = Writer { tx, dirty, activation, tail, initial_journal: Ghost(journal@), initial_primary: Ghost(primary@),
        journal_block, partition_bytes, state: State { phase: Phase::MarkDirty, cursor: 0, request: 0, pending: false, faulted: false } };
    assert(result.images() == assembled);
    Some(result)
}

}
