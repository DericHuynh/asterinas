// SPDX-License-Identifier: MPL-2.0

//! Owned multi-transaction commit/checkpoint program for one reserved window.
//! Successful callback reports need the device model's atomic-write/flush
//! contract. This core does not grant mount, operation or driver authority.

use vstd::prelude::*;
use crate::{bytes, crc, epoch, frozen::FrozenBlock, journal_program::{self, Lane, State},
    journal_queue::{self, FrozenVersion, FrozenView}, journal_state, journal_superblock,
    layout::{JournalLayout, LayoutView}, recovery_io::{Command, CommandView}, recovery_request::Completion,
    super_state, superblock, transaction::{self, AfterImage, Encoded, TransactionView}};

verus! {

pub struct PositionedView { pub tx: TransactionView, pub source: FrozenView }

#[verifier::opaque]
pub open spec fn positioned_valid(v: PositionedView) -> bool {
    &&& transaction::wf(v.tx) && v.tx.original == v.source.images && v.tx.layout == v.source.layout
    &&& v.source.serial > 0 && v.source.first > 0 && v.source.blocks as nat == v.tx.original.len() + 2
    &&& v.source.first as nat + v.source.blocks < v.tx.layout.journal_blocks
}

struct Positioned { tx: Encoded, first: u32, source: Ghost<FrozenView> }

impl Positioned {
    spec fn view(&self) -> PositionedView { PositionedView { tx: self.tx.view(), source: self.source@ } }
    spec fn wf(&self) -> bool { positioned_valid(self.view()) && self.first == self.source@.first }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
}

spec fn positioned_views(txs: Seq<Positioned>) -> Seq<PositionedView> { Seq::new(txs.len(), |i: int| txs[i].view()) }

pub struct WindowView {
    pub txs: Seq<PositionedView>, pub tails: Seq<Seq<u8>>, pub dirty: Seq<u8>, pub layout: LayoutView,
    pub first: u32, pub uuid: Seq<u8>, pub partition_bytes: u64, pub initial_journal: Seq<u8>, pub initial_primary: Seq<u8>,
}

pub open spec fn counts(v: WindowView) -> Seq<nat> { Seq::new(v.txs.len(), |i: int| v.txs[i].tx.original.len()) }

#[verifier::opaque]
pub open spec fn entries(txs: Seq<PositionedView>) -> nat
    decreases txs.len(),
{
    if txs.len() == 0 { 0 } else { entries(txs.drop_last()) + txs.last().tx.original.len() }
}

pub(crate) proof fn entries_push(txs: Seq<PositionedView>, tx: PositionedView)
    ensures entries(txs.push(tx)) == entries(txs) + tx.tx.original.len(),
{
    assert(txs.push(tx).drop_last() =~= txs);
    reveal(entries);
}

pub open spec fn tail_offset(txs: Seq<PositionedView>, prefix: int) -> u32 {
    if prefix == txs.len() { 0u32 } else { txs[prefix].source.first }
}

pub open spec fn tail_start(v: WindowView, prefix: int) -> u32 {
    tail_offset(v.txs, prefix)
}

pub open spec fn header_image(raw: Seq<u8>, original: Seq<u8>, uuid: Seq<u8>, blocks: u32, sequence: u32, start: u32) -> bool {
    &&& raw.len() == 4096 && journal_state::preserves(original.subrange(0, 4096), raw)
    &&& journal_superblock::accepted(raw.subrange(0, 1024), uuid, blocks)
    &&& bytes::be32(raw, 24) == sequence && bytes::be32(raw, 28) == start && bytes::be32(raw, 40) == 17
}

#[verifier::opaque]
pub open spec fn valid(v: WindowView) -> bool {
    &&& v.layout.start > 1 && 1024 <= v.layout.journal_blocks <= 32768
    &&& v.layout.start as nat + v.layout.journal_blocks <= v.layout.fs_blocks
    &&& v.layout.fs_blocks as nat * 4096 <= v.partition_bytes
    &&& 0 < v.txs.len() <= 64 && journal_program::counts_valid(counts(v))
    &&& !crate::feature_policy::readonly(v.initial_primary.subrange(1024, 2048))
    &&& v.initial_primary.len() == 4096 && superblock::accepted(v.initial_primary.subrange(1024, 2048), v.partition_bytes)
    &&& bytes::le32(v.initial_primary, 1028) == v.layout.fs_blocks
    &&& v.initial_journal.len() == v.layout.journal_blocks as nat * 4096
    &&& journal_superblock::accepted(v.initial_journal.subrange(0, 1024), v.uuid, v.layout.journal_blocks)
    &&& bytes::be32(v.initial_journal, 28) == 0
    &&& epoch::newer(v.initial_journal, bytes::be32(v.initial_journal, 24) as u32, v.first)
    &&& 0 < v.first && v.first as nat + v.txs.len() <= 4294967295
    &&& v.dirty.len() == 4096 && v.dirty == super_state::recovery_bytes(v.initial_primary, true)
    &&& super_state::preserves(v.initial_primary, v.dirty) && super_state::is_dirty(v.dirty)
    &&& superblock::accepted(v.dirty.subrange(1024, 2048), v.partition_bytes)
    &&& transaction_window(v.txs, v.layout, v.uuid, v.dirty, v.partition_bytes, v.first)
    &&& v.tails.len() == v.txs.len() + 1
    &&& (forall|k: int| 0 <= k <= v.txs.len() ==> #[trigger] header_image(v.tails[k], v.initial_journal, v.uuid,
        v.layout.journal_blocks, (v.first as nat + k) as u32, tail_start(v, k)))
}

pub open spec fn transaction_window(txs: Seq<PositionedView>, layout: LayoutView, uuid: Seq<u8>, dirty: Seq<u8>, partition_bytes: u64, first: u32) -> bool {
    &&& 0 < txs.len() <= 64 && first > 0 && first as nat + txs.len() <= 4294967295
    &&& entries(txs) <= 4096
    &&& (forall|i: int| 0 <= i < txs.len() ==> #[trigger] positioned_valid(txs[i])
        && txs[i].tx.layout == layout && txs[i].tx.uuid == uuid && txs[i].tx.primary == dirty
        && txs[i].tx.partition_bytes == partition_bytes && txs[i].tx.sequence as nat == first as nat + i
        && txs[i].source.first as nat == if i == 0 { 1nat }
            else { txs[i - 1].source.first as nat + txs[i - 1].source.blocks as nat })
    &&& (forall|i: int, j: int| 0 <= i < j < txs.len() ==> (#[trigger] txs[i]).source.serial < (#[trigger] txs[j]).source.serial)
}

struct Plan {
    txs: Vec<Positioned>, tails: Vec<FrozenBlock>, dirty: FrozenBlock, layout: JournalLayout,
    first: u32, uuid: Ghost<Seq<u8>>, partition_bytes: u64, initial_journal: Ghost<Seq<u8>>, initial_primary: Ghost<Seq<u8>>,
}

impl Plan {
    spec fn view(&self) -> WindowView {
        WindowView { txs: positioned_views(self.txs@), tails: Seq::new(self.tails.len() as nat, |i: int| self.tails@[i].view()),
            dirty: self.dirty.view(), layout: self.layout.view(), first: self.first, uuid: self.uuid@,
            partition_bytes: self.partition_bytes, initial_journal: self.initial_journal@, initial_primary: self.initial_primary@ }
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { valid(self.view()) && self.layout.wf() }
}

pub proof fn a_window_retains_its_geometry_and_bounded_counts(v: WindowView)
    requires valid(v),
    ensures journal_program::counts_valid(counts(v)), 0 < v.txs.len() <= 64,
        v.layout.start > 1, 1024 <= v.layout.journal_blocks <= 32768,
        v.layout.start as nat + v.layout.journal_blocks <= v.layout.fs_blocks,
        v.layout.fs_blocks as nat * 4096 <= v.partition_bytes, v.tails.len() == v.txs.len() + 1,
        entries(v.txs) <= 4096,
{
    hide(crc::fold);
    reveal(valid);
}

#[derive(Clone, Copy)]
pub enum Operation {
    Dirty, DirtyFence, Activate, ActivationFence,
    Descriptor(usize), Payload(usize, usize), LogFence(usize), Commit(usize), CommitFence(usize),
    Home(usize, usize), HomeFence(usize), Tail(usize), TailFence(usize),
}

pub open spec fn is_write(op: Operation) -> bool {
    match op { Operation::Dirty | Operation::Activate | Operation::Descriptor(_) | Operation::Payload(_, _)
        | Operation::Commit(_) | Operation::Home(_, _) | Operation::Tail(_) => true, _ => false }
}

pub open spec fn operation_valid(op: Operation, v: WindowView) -> bool {
    match op {
        Operation::Descriptor(t) | Operation::LogFence(t) | Operation::Commit(t) | Operation::CommitFence(t)
            | Operation::HomeFence(t) => t < v.txs.len(),
        Operation::Payload(t, k) | Operation::Home(t, k) => t < v.txs.len() && k < counts(v)[t as int],
        Operation::Tail(k) | Operation::TailFence(k) => 0 < k <= v.txs.len(),
        _ => true,
    }
}

pub open spec fn pending_operation(s: State, shape: Seq<nat>) -> Operation {
    match s.lane {
        Lane::Bootstrap => if s.bootstrap == 0 { Operation::Dirty } else if s.bootstrap == 1 { Operation::DirtyFence }
            else if s.bootstrap == 2 { Operation::Activate } else { Operation::ActivationFence },
        Lane::Commit => if s.commit_cursor == 0 { Operation::Descriptor(s.commit) }
            else if s.commit_cursor <= shape[s.commit as int] { Operation::Payload(s.commit, (s.commit_cursor - 1) as usize) }
            else if s.commit_cursor == shape[s.commit as int] + 1 { Operation::LogFence(s.commit) }
            else if s.commit_cursor == shape[s.commit as int] + 2 { Operation::Commit(s.commit) }
            else { Operation::CommitFence(s.commit) },
        Lane::Checkpoint => if s.home_cursor < shape[s.checkpoint as int] { Operation::Home(s.checkpoint, s.home_cursor) }
            else { Operation::HomeFence(s.checkpoint) },
        Lane::Tail => if s.tail_phase == 0 { Operation::Tail(s.tail_goal) } else { Operation::TailFence(s.tail_goal) },
    }
}

pub open spec fn expected(v: WindowView, op: Operation) -> CommandView {
    match op {
        Operation::Dirty => CommandView::Write { block: 0, image: v.dirty },
        Operation::Activate => CommandView::Write { block: v.layout.start, image: v.tails[0] },
        Operation::Descriptor(t) => CommandView::Write { block: (v.layout.start as nat + v.txs[t as int].source.first) as u32, image: v.txs[t as int].tx.descriptor },
        Operation::Payload(t, k) => CommandView::Write { block: (v.layout.start as nat + v.txs[t as int].source.first as nat + 1 + k) as u32,
            image: v.txs[t as int].tx.payloads[k as int] },
        Operation::Commit(t) => CommandView::Write { block: (v.layout.start as nat + v.txs[t as int].source.first as nat + 1 + counts(v)[t as int]) as u32,
            image: v.txs[t as int].tx.commit },
        Operation::Home(t, k) => CommandView::Write { block: v.txs[t as int].tx.original[k as int].block,
            image: v.txs[t as int].tx.original[k as int].image },
        Operation::Tail(k) => CommandView::Write { block: v.layout.start, image: v.tails[k as int] },
        _ => CommandView::Flush,
    }
}

pub proof fn a_pending_window_operation_is_in_range(v: WindowView, state: State)
    requires valid(v), journal_program::wf(state, counts(v)), state.pending,
    ensures operation_valid(pending_operation(state, counts(v)), v),
{
    match state.lane { Lane::Bootstrap => {}, Lane::Commit => {}, Lane::Checkpoint => {}, Lane::Tail => {} }
}

pub open spec fn command_bounded(v: WindowView, command: CommandView) -> bool {
    match command { CommandView::Write { block, image } => image.len() == 4096 && block < v.layout.fs_blocks
        && block as nat * 4096 + 4096 <= v.partition_bytes, CommandView::Flush => true }
}

pub proof fn every_window_command_is_partition_bounded(v: WindowView, op: Operation)
    requires valid(v), operation_valid(op, v),
    ensures command_bounded(v, expected(v, op)),
{
    hide(crc::fold);
    hide(superblock::accepted);
    hide(journal_superblock::accepted);
    hide(transaction::wf);
    a_window_retains_its_geometry_and_bounded_counts(v);
    match op {
        Operation::Descriptor(t) | Operation::Payload(t, _) | Operation::Commit(t) | Operation::Home(t, _) => {
            window_entry(v, t as int);
            reveal(positioned_valid);
            transaction_bounds(v.txs[t as int].tx);
            match op {
                Operation::Payload(_, k) | Operation::Home(_, k) => { payload_bounds(v.txs[t as int].tx, k as int); },
                _ => {},
            }
        },
        Operation::Activate => { window_header(v, 0); },
        Operation::Tail(k) => { window_header(v, k as int); },
        Operation::Dirty => { reveal(valid); },
        _ => {},
    }
}

proof fn transaction_bounds(tx: TransactionView)
    requires transaction::wf(tx),
    ensures tx.descriptor.len() == 4096, tx.commit.len() == 4096, 0 < tx.original.len() <= 250,
        tx.original.len() == tx.payloads.len(),
{
    hide(crc::fold);
    hide(crate::descriptor::candidate);
    hide(crate::descriptor::represents);
    hide(super_state::replay_ok);
}

proof fn payload_bounds(tx: TransactionView, k: int)
    requires transaction::wf(tx), 0 <= k < tx.original.len(),
    ensures tx.payloads[k].len() == 4096, tx.original[k].image.len() == 4096,
        tx.original[k].block < tx.layout.fs_blocks,
        !(tx.layout.start <= tx.original[k].block < tx.layout.start as nat + tx.layout.journal_blocks),
{
    hide(crc::fold);
    hide(crate::descriptor::candidate);
    hide(crate::descriptor::represents);
    hide(super_state::replay_ok);
    assert(crate::replay::payload_for_layout(tx.tags[k], tx.payloads[k], tx.sequence, tx.seed, tx.layout));
}

pub(crate) proof fn window_entry(v: WindowView, index: int)
    requires valid(v), 0 <= index < v.txs.len(),
    ensures positioned_valid(v.txs[index]), v.txs[index].tx.layout == v.layout,
        v.txs[index].tx.uuid == v.uuid, v.txs[index].tx.primary == v.dirty,
        v.txs[index].tx.partition_bytes == v.partition_bytes,
        v.txs[index].tx.sequence as nat == v.first as nat + index,
        v.txs[index].source.first as nat == if index == 0 { 1nat }
            else { v.txs[index - 1].source.first as nat + v.txs[index - 1].source.blocks as nat },
{ reveal(valid); assert(positioned_valid(v.txs[index])); }

pub(crate) proof fn window_header(v: WindowView, prefix: int)
    requires valid(v), 0 <= prefix <= v.txs.len(),
    ensures header_image(v.tails[prefix], v.initial_journal, v.uuid, v.layout.journal_blocks,
        (v.first as nat + prefix) as u32, tail_start(v, prefix)),
{ reveal(valid); }

fn copy_and_encode(version: &FrozenVersion, uuid: &[u8], sequence: u32, layout: &JournalLayout, primary: &[u8], partition_bytes: u64) -> (r: Option<Positioned>)
    ensures match r {
        Some(positioned) => positioned.wf() && positioned.view().source == version.view()
            && positioned.view().tx.uuid == uuid@ && positioned.view().tx.sequence == sequence
            && positioned.view().tx.layout == layout.view() && positioned.view().tx.primary == primary@
            && positioned.view().tx.partition_bytes == partition_bytes,
        None => true,
    },
{
    hide(crc::fold);
    let mapping = version.journal_layout();
    if mapping.physical_start() != layout.physical_start() || mapping.blocks() != layout.blocks()
        || mapping.filesystem_blocks() != layout.filesystem_blocks() { return None; }
    let (serial, first, blocks) = version.reservation();
    let count = version.image_count();
    let mut input: Vec<AfterImage> = Vec::new();
    let mut index = 0usize;
    while index < count
        invariant index <= count <= 250, input.len() == index, count == version.view().images.len(),
            transaction::images(input@) == version.view().images.take(index as int),
        decreases count - index,
    {
        let (target, raw) = version.image_at(index).unwrap();
        let image = match AfterImage::capture(target, raw) { Some(image) => image, None => { return None; } };
        let ghost previous = transaction::images(input@);
        input.push(image);
        assert(transaction::images(input@) =~= previous.push(image.view()));
        index += 1;
    }
    assert(transaction::images(input@) == version.view().images);
    let tx = match transaction::encode(input, uuid, sequence, layout, primary, partition_bytes) { Some(tx) => tx, None => { return None; } };
    proof { reveal(positioned_valid); }
    let positioned = Positioned { tx, first, source: Ghost(version.view()) };
    assert(positioned.wf()) by { reveal(positioned_valid); }
    Some(positioned)
}

pub struct Engine { plan: Plan, state: State }
pub struct Pending { engine: Engine, id: u64 }

impl Engine {
    pub closed spec fn program(&self) -> WindowView { self.plan.view() }
    pub closed spec fn state(&self) -> State { self.state }
    pub open spec fn wf(&self) -> bool { valid(self.program()) && journal_program::wf(self.state(), counts(self.program())) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn first_sequence(&self) -> (r: u32) ensures r == self.program().first { self.plan.first }

    pub fn dirty_marker(&self) -> (r: &[u8]) ensures r@ == self.program().dirty, r.len() == 4096 {
        proof { use_type_invariant(self); reveal(valid); }
        self.plan.dirty.as_slice()
    }

    pub fn transaction_count(&self) -> (r: usize) ensures self.wf(), r == self.program().txs.len(), 0 < r <= 64 {
        proof { use_type_invariant(self); a_window_retains_its_geometry_and_bounded_counts(self.program()); }
        self.plan.txs.len()
    }

    pub fn progress(&self) -> (r: (usize, usize, usize, bool))
        ensures self.wf(), r == (self.state().commit, self.state().checkpoint, self.state().retired, self.state().faulted),
            r.2 <= r.1 <= r.0 <= self.program().txs.len(),
    { proof { use_type_invariant(self); } (self.state.commit, self.state.checkpoint, self.state.retired, self.state.faulted) }

    pub fn finished(&self) -> (r: bool) ensures r == journal_program::finished(self.state(), counts(self.program())) {
        self.state.bootstrap == 4 && self.state.commit == self.plan.txs.len() && self.state.checkpoint == self.plan.txs.len()
            && self.state.retired == self.plan.txs.len() && self.state.tail_phase == 0 && !self.state.pending && !self.state.faulted
    }

    pub fn can_dispatch(&self, lane: Lane) -> (r: bool)
        ensures self.wf(), r == journal_program::enabled(self.state(), lane, counts(self.program())),
    {
        proof { use_type_invariant(self); }
        if self.state.pending || self.state.faulted || self.state.request == 18446744073709551615 { return false; }
        match lane {
            Lane::Bootstrap => self.state.bootstrap < 4,
            Lane::Commit => self.state.bootstrap == 4 && self.state.commit < self.plan.txs.len(),
            Lane::Checkpoint => self.state.bootstrap == 4 && self.state.checkpoint < self.state.commit,
            Lane::Tail => self.state.bootstrap == 4 && (self.state.tail_phase == 1 || self.state.checkpoint > self.state.retired),
        }
    }

    pub fn abort(self) -> (r: Self)
        ensures r.wf(), r.program() == self.program(), r.state() == (State { faulted: true, ..self.state() }),
    {
        proof { use_type_invariant(&self); journal_program::aborting_keeps_the_request_and_all_committed_frontiers(self.state(), counts(self.program())); }
        let Engine { plan, state } = self;
        Engine { plan, state: State { faulted: true, ..state } }
    }
}

fn count_at(plan: &Plan, index: usize) -> (r: usize)
    ensures r as nat == if index < counts(plan.view()).len() { counts(plan.view())[index as int] } else { 0nat }, r <= 250,
{
    proof { use_type_invariant(plan); }
    if index >= plan.txs.len() { return 0; }
    let positioned = &plan.txs[index];
    proof { use_type_invariant(positioned); reveal(positioned_valid); }
    positioned.tx.payload_count()
}

fn operation_value(s: State, commit_count: usize, home_count: usize, Ghost(shape): Ghost<Seq<nat>>) -> (r: Operation)
    requires journal_program::wf(s, shape), s.pending,
        commit_count as nat == if s.commit < shape.len() { shape[s.commit as int] } else { 0nat },
        home_count as nat == if s.checkpoint < shape.len() { shape[s.checkpoint as int] } else { 0nat },
    ensures r == pending_operation(s, shape),
{
    match s.lane {
        Lane::Bootstrap => if s.bootstrap == 0 { Operation::Dirty } else if s.bootstrap == 1 { Operation::DirtyFence }
            else if s.bootstrap == 2 { Operation::Activate } else { Operation::ActivationFence },
        Lane::Commit => if s.commit_cursor == 0 { Operation::Descriptor(s.commit) }
            else if s.commit_cursor <= commit_count { Operation::Payload(s.commit, s.commit_cursor - 1) }
            else if s.commit_cursor == commit_count + 1 { Operation::LogFence(s.commit) }
            else if s.commit_cursor == commit_count + 2 { Operation::Commit(s.commit) }
            else { Operation::CommitFence(s.commit) },
        Lane::Checkpoint => if s.home_cursor < home_count { Operation::Home(s.checkpoint, s.home_cursor) }
            else { Operation::HomeFence(s.checkpoint) },
        Lane::Tail => if s.tail_phase == 0 { Operation::Tail(s.tail_goal) } else { Operation::TailFence(s.tail_goal) },
    }
}

pub fn dispatch(engine: Engine, lane: Lane) -> (r: Result<Pending, Engine>)
    ensures match r {
        Ok(pending) => pending.owner().program() == engine.program()
            && journal_program::enabled(engine.state(), lane, counts(engine.program()))
            && pending.owner().state() == journal_program::started(engine.state(), lane),
        Err(unchanged) => unchanged.program() == engine.program() && unchanged.state() == engine.state()
            && !journal_program::enabled(engine.state(), lane, counts(engine.program())),
    },
{
    proof { use_type_invariant(&engine); }
    if !engine.can_dispatch(lane) { return Err(engine); }
    let ghost shape = counts(engine.program());
    let Engine { plan, state } = engine;
    let started = journal_program::begin_request(state, lane, Ghost(shape));
    Ok(Pending { engine: Engine { plan, state: started }, id: started.request })
}

impl Pending {
    pub closed spec fn owner(&self) -> &Engine { &self.engine }
    pub closed spec fn id(&self) -> u64 { self.id }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.engine.wf() && self.engine.state.pending && self.id == self.engine.state.request }

    pub fn operation(&self) -> (r: Operation)
        ensures r == pending_operation(self.owner().state(), counts(self.owner().program())), operation_valid(r, self.owner().program()),
    {
        proof { use_type_invariant(self); a_pending_window_operation_is_in_range(self.engine.program(), self.engine.state()); }
        operation_value(self.engine.state, count_at(&self.engine.plan, self.engine.state.commit),
            count_at(&self.engine.plan, self.engine.state.checkpoint), Ghost(counts(self.engine.program())))
    }

    pub fn request_number(&self) -> (r: u64) ensures r == self.id(), r == self.owner().state().request, r > 0 {
        proof { use_type_invariant(self); }
        self.id
    }

    pub fn pending_command(&self) -> (r: Command<'_>)
        ensures r.view() == expected(self.owner().program(), pending_operation(self.owner().state(), counts(self.owner().program()))),
            command_bounded(self.owner().program(), r.view()),
    {
        proof { use_type_invariant(self); }
        let op = self.operation();
        proof {
            a_window_retains_its_geometry_and_bounded_counts(self.engine.program());
            every_window_command_is_partition_bounded(self.engine.program(), op);
        }
        let plan = &self.engine.plan;
        match op {
            Operation::Dirty => Command::Write { block: 0, image: plan.dirty.as_slice() },
            Operation::Activate => Command::Write { block: plan.layout.physical_start(), image: plan.tails[0].as_slice() },
            Operation::Descriptor(t) => {
                let p = &plan.txs[t];
                proof { window_entry(plan.view(), t as int); use_type_invariant(p); reveal(positioned_valid); }
                Command::Write { block: plan.layout.physical_start() + p.first, image: p.tx.descriptor_bytes() }
            },
            Operation::Payload(t, k) => {
                let p = &plan.txs[t];
                proof { window_entry(plan.view(), t as int); use_type_invariant(p); reveal(positioned_valid); }
                Command::Write { block: plan.layout.physical_start() + p.first + 1 + k as u32, image: p.tx.payload_at(k).unwrap() }
            },
            Operation::Commit(t) => {
                let p = &plan.txs[t];
                proof { window_entry(plan.view(), t as int); use_type_invariant(p); reveal(positioned_valid); }
                Command::Write { block: plan.layout.physical_start() + p.first + 1 + p.tx.payload_count() as u32, image: p.tx.commit_bytes() }
            },
            Operation::Home(t, k) => { let (block, image) = plan.txs[t].tx.original_at(k).unwrap(); Command::Write { block, image } },
            Operation::Tail(k) => Command::Write { block: plan.layout.physical_start(), image: plan.tails[k].as_slice() },
            _ => Command::Flush,
        }
    }

    pub fn abort_pending(self) -> (r: Self)
        ensures r.owner().program() == self.owner().program(), r.id() == self.id(),
            r.owner().state() == (State { faulted: true, ..self.owner().state() }),
    {
        proof { use_type_invariant(&self); }
        let Pending { engine, id } = self;
        Pending { engine: engine.abort(), id }
    }

    pub fn finish_pending(self, outcome: Completion) -> (r: Engine)
        ensures r.wf(), r.program() == self.owner().program(),
            r.state() == journal_program::completed(self.owner().state(), counts(self.owner().program()), outcome is Succeeded),
    {
        proof { use_type_invariant(&self); }
        let commit_count = count_at(&self.engine.plan, self.engine.state.commit);
        let home_count = count_at(&self.engine.plan, self.engine.state.checkpoint);
        let ghost shape = counts(self.engine.program());
        let Pending { engine: Engine { plan, state }, id: _ } = self;
        let success = match outcome { Completion::Succeeded => true, Completion::Failed => false };
        let completed = journal_program::finish_request(state, commit_count, home_count, success, Ghost(shape));
        Engine { plan, state: completed }
    }
}

fn encode_versions(versions: &[FrozenVersion], uuid: &[u8], first: u32, layout: &JournalLayout, primary: &[u8], partition_bytes: u64) -> (r: Option<Vec<Positioned>>)
    requires 0 < versions.len() <= 64, first > 0, first as nat + versions.len() <= 4294967295,
    ensures match r { Some(txs) => transaction_window(positioned_views(txs@), layout.view(), uuid@, primary@, partition_bytes, first)
        && Seq::new(txs.len() as nat, |i: int| positioned_views(txs@)[i].source) == journal_queue::frozen_views(versions@), None => true },
{
    hide(crc::fold);
    let mut txs: Vec<Positioned> = Vec::new();
    let mut index = 0usize;
    let mut cursor = 1u32;
    let mut previous_serial = 0u64;
    let mut credits = 0usize;
    assert(entries(positioned_views(txs@)) == 0) by { reveal(entries); }
    while index < versions.len()
        invariant index <= versions.len() <= 64, versions.len() > 0, txs.len() == index,
            credits <= 4096, credits as nat == entries(positioned_views(txs@)),
            first > 0, first as nat + versions.len() <= 4294967295,
            cursor as nat == if index == 0 { 1nat } else { positioned_views(txs@)[index as int - 1].source.first as nat
                + positioned_views(txs@)[index as int - 1].source.blocks as nat },
            previous_serial == if index == 0 { 0u64 } else { positioned_views(txs@)[index as int - 1].source.serial },
            (forall|i: int| 0 <= i < index ==> #[trigger] positioned_valid(positioned_views(txs@)[i])
                && positioned_views(txs@)[i].source == versions@[i].view()
                && positioned_views(txs@)[i].tx.layout == layout.view() && positioned_views(txs@)[i].tx.uuid == uuid@
                && positioned_views(txs@)[i].tx.primary == primary@ && positioned_views(txs@)[i].tx.partition_bytes == partition_bytes
                && positioned_views(txs@)[i].tx.sequence as nat == first as nat + i
                && positioned_views(txs@)[i].source.first as nat == if i == 0 { 1nat } else {
                    positioned_views(txs@)[i - 1].source.first as nat + positioned_views(txs@)[i - 1].source.blocks as nat }),
            (forall|i: int, j: int| 0 <= i < j < index ==> (#[trigger] positioned_views(txs@)[i]).source.serial
                < (#[trigger] positioned_views(txs@)[j]).source.serial),
        decreases versions.len() - index,
    {
        let version = &versions[index];
        let (serial, logical, blocks) = version.reservation();
        if logical != cursor || serial <= previous_serial { return None; }
        let count = version.image_count();
        if count > 4096 - credits { return None; }
        let positioned = match copy_and_encode(version, uuid, first + index as u32, &layout, primary, partition_bytes) {
            Some(positioned) => positioned, None => { return None; },
        };
        let ghost previous = positioned_views(txs@);
        let ghost last = positioned.view();
        assert(last.tx.original.len() == count) by { reveal(positioned_valid); }
        txs.push(positioned);
        assert(positioned_views(txs@) =~= previous.push(last));
        proof { entries_push(previous, last); }
        proof {
            assert forall|i: int| 0 <= i < index + 1 implies #[trigger] positioned_valid(positioned_views(txs@)[i])
                && positioned_views(txs@)[i].source == versions@[i].view()
                && positioned_views(txs@)[i].tx.layout == layout.view() && positioned_views(txs@)[i].tx.uuid == uuid@
                && positioned_views(txs@)[i].tx.primary == primary@ && positioned_views(txs@)[i].tx.partition_bytes == partition_bytes
                && positioned_views(txs@)[i].tx.sequence as nat == first as nat + i
                && positioned_views(txs@)[i].source.first as nat == if i == 0 { 1nat } else {
                    positioned_views(txs@)[i - 1].source.first as nat + positioned_views(txs@)[i - 1].source.blocks as nat } by {
                if i < index {
                    assert(positioned_valid(previous[i]));
                    assert(previous[i].source == versions@[i].view());
                    assert(previous[i].tx.layout == layout.view() && previous[i].tx.uuid == uuid@);
                    assert(previous[i].tx.primary == primary@ && previous[i].tx.partition_bytes == partition_bytes);
                    assert(previous[i].tx.sequence as nat == first as nat + i);
                    assert(previous[i].source.first as nat == if i == 0 { 1nat } else { previous[i - 1].source.first as nat + previous[i - 1].source.blocks as nat });
                } else {
                    assert(last.source == versions@[i].view());
                    assert(last.source.first == logical);
                    assert(last.source.first as nat == if i == 0 { 1nat } else { previous[i - 1].source.first as nat + previous[i - 1].source.blocks as nat });
                }
            }
            assert forall|i: int| 0 <= i < index implies (#[trigger] previous[i]).source.serial < serial by {
                if i < index as int - 1 { assert(previous[i].source.serial < previous[index as int - 1].source.serial); }
            }
            assert(logical as nat + blocks < layout.view().journal_blocks) by { reveal(positioned_valid); }
        }
        cursor = logical + blocks;
        previous_serial = serial;
        credits += count;
        index += 1;
    }
    assert forall|i: int| 0 <= i < versions.len() implies positioned_views(txs@)[i].source == (#[trigger] versions@[i]).view() by {
        assert(positioned_valid(positioned_views(txs@)[i]));
    }
    assert(Seq::new(txs.len() as nat, |i: int| positioned_views(txs@)[i].source) =~= journal_queue::frozen_views(versions@));
    Some(txs)
}

fn encode_tails(txs: &[Positioned], journal: &[u8], uuid: &[u8], layout: &JournalLayout, first: u32) -> (r: Option<Vec<FrozenBlock>>)
    requires journal.len() >= 4096,
        transaction_window(positioned_views(txs@), layout.view(), uuid@, positioned_views(txs@)[0].tx.primary,
            positioned_views(txs@)[0].tx.partition_bytes, first),
    ensures match r { Some(tails) => tails.len() == txs.len() + 1
        && (forall|k: int| 0 <= k <= txs.len() ==> #[trigger] header_image(tails@[k].view(), journal@, uuid@, layout.view().journal_blocks,
            (first as nat + k) as u32, tail_offset(positioned_views(txs@), k))), None => true },
{
    hide(crc::fold);
    hide(journal_superblock::accepted);
    let ghost completed_txs = positioned_views(txs@);
    let mut tails: Vec<FrozenBlock> = Vec::new();
    let mut prefix = 0usize;
    while prefix <= txs.len()
        invariant prefix <= txs.len() + 1, tails.len() == prefix, 0 < txs.len() <= 64,
            positioned_views(txs@) == completed_txs, journal.len() >= 4096,
            transaction_window(completed_txs, layout.view(), uuid@, completed_txs[0].tx.primary, completed_txs[0].tx.partition_bytes, first), first > 0, first as nat + txs.len() <= 4294967295,
            (forall|k: int| 0 <= k < prefix ==> #[trigger] header_image(tails@[k].view(), journal@, uuid@, layout.view().journal_blocks,
                (first as nat + k) as u32, tail_offset(completed_txs, k))),
        decreases txs.len() + 1 - prefix,
    {
        let start = if prefix == txs.len() { 0u32 } else {
            let positioned = &txs[prefix];
            proof { use_type_invariant(positioned); }
            positioned.first
        };
        let image = match journal_state::encode(&journal[..4096], uuid, layout.blocks(), first + prefix as u32, start) {
            Some(image) => image, None => { return None; },
        };
        assert(header_image(image.view(), journal@, uuid@, layout.view().journal_blocks, (first as nat + prefix) as u32,
            if prefix == txs.len() { 0u32 } else { completed_txs[prefix as int].source.first }));
        tails.push(image);
        prefix += 1;
    }
    Some(tails)
}

pub fn prepare(versions: &[FrozenVersion], journal: &[u8], uuid: &[u8], layout: JournalLayout, primary: &[u8], partition_bytes: u64) -> (r: Option<Engine>)
    ensures match r {
        Some(engine) => engine.wf() && engine.state() == journal_program::initial()
            && engine.program().initial_journal == journal@ && engine.program().initial_primary == primary@
            && engine.program().uuid == uuid@ && engine.program().layout == layout.view()
            && engine.program().partition_bytes == partition_bytes
            && Seq::new(engine.program().txs.len(), |i: int| engine.program().txs[i].source) == journal_queue::frozen_views(versions@),
        None => true,
    },
{
    hide(crc::fold);
    hide(superblock::accepted);
    hide(journal_superblock::accepted);
    if versions.len() == 0 || versions.len() > 64 || !layout.valid() || primary.len() != 4096
        || journal.len() as u64 != layout.blocks() as u64 * 4096 { return None; }
    if crate::feature_policy::is_readonly(&primary[1024..2048]).unwrap() { return None; }
    let boot = match superblock::parse(&primary[1024..2048], partition_bytes) { Some(boot) => boot, None => { return None; } };
    if boot.blocks() != layout.filesystem_blocks() { return None; }
    assert(layout.view().fs_blocks as nat * 4096 <= partition_bytes) by { reveal(superblock::accepted); }
    let info = match journal_superblock::parse(&journal[..1024], uuid, layout.blocks()) { Some(info) => info, None => { return None; } };
    if info.start != 0 { return None; }
    let first = match epoch::fresh_sequence(journal, info.sequence) { Some(first) => first, None => { return None; } };
    if first as u64 + versions.len() as u64 > 4294967295 { return None; }
    let dirty = super_state::recovery_image(primary, partition_bytes, true).unwrap();
    let txs = match encode_versions(versions, uuid, first, &layout, dirty.as_slice(), partition_bytes) {
        Some(txs) => txs, None => { return None; },
    };
    assert(positioned_valid(positioned_views(txs@)[0]));
    let tails = match encode_tails(&txs, journal, uuid, &layout, first) {
        Some(tails) => tails, None => { return None; },
    };
    let ghost completed_txs = positioned_views(txs@);
    let ghost assembled = WindowView { txs: completed_txs, tails: Seq::new(tails.len() as nat, |i: int| tails@[i].view()), dirty: dirty.view(),
        layout: layout.view(), first, uuid: uuid@, partition_bytes, initial_journal: journal@, initial_primary: primary@ };
    assert(valid(assembled)) by {
        reveal(valid);
        assert forall|i: int| 0 <= i < assembled.txs.len() implies 1 <= #[trigger] counts(assembled)[i] <= 250 by {
            assert(positioned_valid(assembled.txs[i]));
            reveal(positioned_valid);
        }
    }
    let plan = Plan { txs, tails, dirty, layout, first, uuid: Ghost(uuid@), partition_bytes, initial_journal: Ghost(journal@), initial_primary: Ghost(primary@) };
    assert(plan.view() == assembled);
    proof {
        a_window_retains_its_geometry_and_bounded_counts(assembled);
        journal_program::initial_window_state_is_valid(counts(assembled));
    }
    let state = State { bootstrap: 0, commit: 0, commit_cursor: 0, checkpoint: 0, home_cursor: 0,
        retired: 0, tail_goal: 0, tail_phase: 0, pending: false, lane: Lane::Bootstrap, request: 0, faulted: false };
    Some(Engine { plan, state })
}

}
