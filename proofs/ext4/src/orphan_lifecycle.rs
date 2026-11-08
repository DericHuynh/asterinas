// SPDX-License-Identifier: MPL-2.0

//! Owned orphan reclamation workflow. Journal commands are completed only by
//! the later source-bound durable-journal adapter; ordinary write completion
//! is insufficient. Numeric identities and status queries are not inode,
//! allocation, frame or device capabilities.

use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Reason { Unlink, Truncate }
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Error { Identity, Geometry, Links, Handles, Pins, Overflow, Phase }
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Stage {
    AddReady, OrphanDurable, ReclaimCommitted, ReclaimCheckpointed,
    NeedRemove, RemovalCommitted, RemovalCheckpointed, Retired,
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Command {
    JournalAdd { inode: u32, generation: u32, target_blocks: u64, unlink: bool },
    JournalReclaim { inode: u32, generation: u32, blocks: u64 },
    CheckpointData,
    QuiesceData,
    JournalRemove { inode: u32, generation: u32 },
    CheckpointRemoval,
    QuiesceRemoval,
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Completion { Durable, Failed }

/// Numeric protocol state only: completion events must later be refined to
/// the durable journal/device and runtime quiescence adapters.
#[verifier::ext_equal]
pub struct View {
    pub volume: u64, pub inode: u32, pub generation: u32, pub reason: Reason,
    pub links_after: u16, pub handles: u64, pub io_pins: u64,
    pub target_blocks: u64, pub remaining: u64, pub reclaimed: u64,
    pub stage: Stage, pub faulted: bool, pub next_request: u64,
}
pub open spec fn after_orphan(v: View) -> bool {
    v.stage == Stage::ReclaimCommitted || v.stage == Stage::ReclaimCheckpointed
        || v.stage == Stage::NeedRemove || v.stage == Stage::RemovalCommitted
        || v.stage == Stage::RemovalCheckpointed || v.stage == Stage::Retired
}
pub open spec fn valid(v: View) -> bool {
    &&& v.volume > 0 && v.inode > 0 && v.next_request > 0
    &&& v.remaining as nat + v.reclaimed as nat <= u64::MAX
    &&& v.reason == Reason::Unlink ==> v.links_after == 0 && v.target_blocks == 0
    &&& v.reason == Reason::Truncate ==> v.links_after > 0
    &&& v.stage == Stage::AddReady ==> v.reclaimed == 0
    &&& v.reason == Reason::Unlink && after_orphan(v) ==> v.handles == 0 && v.io_pins == 0
    &&& v.stage == Stage::NeedRemove || v.stage == Stage::RemovalCommitted
        || v.stage == Stage::RemovalCheckpointed || v.stage == Stage::Retired ==> v.remaining == 0
}
pub open spec fn enabled(v: View, command: Command) -> bool {
    &&& !v.faulted
    &&& match command {
        Command::JournalAdd { inode, generation, target_blocks, unlink } =>
            v.stage == Stage::AddReady && inode == v.inode && generation == v.generation
                && target_blocks == v.target_blocks && unlink == (v.reason == Reason::Unlink),
        Command::JournalReclaim { inode, generation, blocks } =>
            v.stage == Stage::OrphanDurable && inode == v.inode && generation == v.generation
                && 0 < blocks <= v.remaining && v.io_pins == 0
                && (v.reason == Reason::Unlink ==> v.handles == 0),
        Command::CheckpointData => v.stage == Stage::ReclaimCommitted,
        Command::QuiesceData => v.stage == Stage::ReclaimCheckpointed,
        Command::JournalRemove { inode, generation } =>
            (v.stage == Stage::OrphanDurable || v.stage == Stage::NeedRemove)
                && inode == v.inode && generation == v.generation && v.remaining == 0
                && v.io_pins == 0 && (v.reason == Reason::Unlink ==> v.handles == 0),
        Command::CheckpointRemoval => v.stage == Stage::RemovalCommitted,
        Command::QuiesceRemoval => v.stage == Stage::RemovalCheckpointed,
    }
}
pub open spec fn completed(v: View, command: Command, completion: Completion) -> View {
    if matches!(completion, Completion::Failed) || v.faulted { View { faulted: true, ..v } }
    else { match command {
        Command::JournalAdd { .. } => View { stage: Stage::OrphanDurable, ..v },
        Command::JournalReclaim { blocks, .. } =>
            if blocks == 0 || blocks > v.remaining || blocks as nat + v.reclaimed as nat > u64::MAX {
                View { faulted: true, ..v }
            } else { View { remaining: (v.remaining - blocks) as u64, reclaimed: (v.reclaimed + blocks) as u64,
                stage: Stage::ReclaimCommitted, ..v } },
        Command::CheckpointData => View { stage: Stage::ReclaimCheckpointed, ..v },
        Command::QuiesceData => View { stage: if v.remaining == 0 { Stage::NeedRemove } else { Stage::OrphanDurable }, ..v },
        Command::JournalRemove { .. } => View { stage: Stage::RemovalCommitted, ..v },
        Command::CheckpointRemoval => View { stage: Stage::RemovalCheckpointed, ..v },
        Command::QuiesceRemoval => View { stage: Stage::Retired, ..v },
    } }
}
#[verifier::ext_equal]
pub struct RequestView { pub owner: View, pub command: Command, pub request: u64 }
pub open spec fn request_valid(v: RequestView) -> bool {
    valid(v.owner) && enabled(v.owner, v.command)
        && v.request > 0 && v.request as nat + 1 == v.owner.next_request
}
pub open spec fn reusable(v: View) -> bool {
    !v.faulted && v.stage == Stage::Retired && v.reason == Reason::Unlink
        && v.handles == 0 && v.io_pins == 0 && v.remaining == 0
}

pub struct Lifecycle {
    volume: u64, inode: u32, generation: u32, reason: Reason,
    links_after: u16, handles: u64, io_pins: u64,
    target_blocks: u64, remaining: u64, reclaimed: u64,
    stage: Stage, faulted: bool, next_request: u64,
}
pub struct Pending { owner: Lifecycle, command: Command, request: u64 }
pub struct Issued { owner: Lifecycle, command: Command, request: u64 }

impl Lifecycle {
    pub closed spec fn view(&self) -> View {
        View { volume: self.volume, inode: self.inode, generation: self.generation, reason: self.reason,
            links_after: self.links_after, handles: self.handles, io_pins: self.io_pins,
            target_blocks: self.target_blocks, remaining: self.remaining, reclaimed: self.reclaimed,
            stage: self.stage, faulted: self.faulted, next_request: self.next_request }
    }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn identity(&self) -> (r: (u64, u32, u32)) ensures r == (self.view().volume, self.view().inode, self.view().generation) { (self.volume, self.inode, self.generation) }
    pub fn stage(&self) -> (r: Stage) ensures r == self.view().stage { self.stage }
    pub fn reason(&self) -> (r: Reason) ensures r == self.view().reason { self.reason }
    pub fn references(&self) -> (r: (u16, u64, u64)) ensures r == (self.view().links_after, self.view().handles, self.view().io_pins) { (self.links_after, self.handles, self.io_pins) }
    pub fn progress(&self) -> (r: (u64, u64, u64)) ensures r == (self.view().target_blocks, self.view().remaining, self.view().reclaimed) { (self.target_blocks, self.remaining, self.reclaimed) }
    pub fn faulted(&self) -> (r: bool) ensures r == self.view().faulted { self.faulted }
    pub fn reusable_inode(&self) -> (r: bool) ensures r == reusable(self.view()) {
        !self.faulted && matches!(self.stage, Stage::Retired) && matches!(self.reason, Reason::Unlink)
            && self.handles == 0 && self.io_pins == 0 && self.remaining == 0
    }
    pub fn finished_truncate(&self) -> (r: bool) ensures r == (!self.view().faulted && self.view().stage == Stage::Retired && self.view().reason == Reason::Truncate) {
        !self.faulted && matches!(self.stage, Stage::Retired) && matches!(self.reason, Reason::Truncate)
    }
    /// Existing descriptors may be duplicated after unlink; a zero-handle
    /// unlinked inode cannot be newly opened through this workflow.
    pub fn retain_handle(&mut self) -> (r: bool)
        ensures final(self).wf(), if r {
            final(self).view() == (View { handles: (old(self).view().handles + 1) as u64, ..old(self).view() })
        } else { final(self).view() == old(self).view() },
    {
        proof { use_type_invariant(&*self); }
        if self.faulted || matches!(self.stage, Stage::Retired) || self.handles == 0 || self.handles == u64::MAX {
            return false;
        }
        self.handles += 1; true
    }
    pub fn open_linked(&mut self) -> (r: bool)
        ensures final(self).wf(), if r {
            final(self).view() == (View { handles: (old(self).view().handles + 1) as u64, ..old(self).view() })
        } else { final(self).view() == old(self).view() },
    {
        proof { use_type_invariant(&*self); }
        if self.faulted || matches!(self.stage, Stage::Retired) || self.links_after == 0 || self.handles == u64::MAX {
            return false;
        }
        self.handles += 1; true
    }
    pub fn close_handle(&mut self) -> (r: bool)
        ensures final(self).wf(), if r {
            final(self).view() == (View { handles: (old(self).view().handles - 1) as u64, ..old(self).view() })
        } else { final(self).view() == old(self).view() },
    {
        proof { use_type_invariant(&*self); }
        if self.handles == 0 { return false; }
        self.handles -= 1; true
    }
    pub fn pin_io(&mut self) -> (r: bool)
        ensures final(self).wf(), if r {
            final(self).view() == (View { io_pins: (old(self).view().io_pins + 1) as u64, ..old(self).view() })
        } else { final(self).view() == old(self).view() },
    {
        proof { use_type_invariant(&*self); }
        if self.faulted || matches!(self.stage, Stage::Retired) || self.handles == 0 || self.io_pins == u64::MAX {
            return false;
        }
        self.io_pins += 1; true
    }
    pub fn unpin_io(&mut self) -> (r: bool)
        ensures final(self).wf(), if r {
            final(self).view() == (View { io_pins: (old(self).view().io_pins - 1) as u64, ..old(self).view() })
        } else { final(self).view() == old(self).view() },
    {
        proof { use_type_invariant(&*self); }
        if self.io_pins == 0 { return false; }
        self.io_pins -= 1; true
    }
    pub fn abort(&mut self)
        ensures final(self).wf(), final(self).view() == (View { faulted: true, ..old(self).view() }),
    { proof { use_type_invariant(&*self); } self.faulted = true; }

    /// Reserve an immutable command. Reclamation waits for all prior I/O;
    /// final unlink also waits for the last open descriptor.
    pub fn dispatch(mut self, max_blocks: u64) -> (r: Result<Pending, Self>)
        ensures self.wf(), match r {
            Ok(pending) => pending.wf()
                && pending.view().owner == (View { next_request: (self.view().next_request + 1) as u64, ..self.view() })
                && pending.view().request == self.view().next_request
                && (match pending.view().command { Command::JournalReclaim { blocks, .. } => blocks <= max_blocks, _ => true }),
            Err(owner) => owner.wf() && owner.view() == self.view(),
        },
    {
        proof { use_type_invariant(&self); }
        if self.faulted || self.next_request == u64::MAX { return Err(self); }
        let command = match self.stage {
            Stage::AddReady => Command::JournalAdd { inode: self.inode, generation: self.generation,
                target_blocks: self.target_blocks, unlink: matches!(self.reason, Reason::Unlink) },
            Stage::OrphanDurable => {
                if self.io_pins != 0 || (matches!(self.reason, Reason::Unlink) && self.handles != 0) {
                    return Err(self);
                }
                if self.remaining == 0 {
                    Command::JournalRemove { inode: self.inode, generation: self.generation }
                } else {
                    if max_blocks == 0 { return Err(self); }
                    let blocks = if max_blocks < self.remaining { max_blocks } else { self.remaining };
                    Command::JournalReclaim { inode: self.inode, generation: self.generation, blocks }
                }
            },
            Stage::ReclaimCommitted => Command::CheckpointData,
            Stage::ReclaimCheckpointed => Command::QuiesceData,
            Stage::NeedRemove => {
                if self.io_pins != 0 || (matches!(self.reason, Reason::Unlink) && self.handles != 0) {
                    return Err(self);
                }
                Command::JournalRemove { inode: self.inode, generation: self.generation }
            },
            Stage::RemovalCommitted => Command::CheckpointRemoval,
            Stage::RemovalCheckpointed => Command::QuiesceRemoval,
            Stage::Retired => { return Err(self); },
        };
        let request = self.next_request;
        self.next_request += 1;
        Ok(Pending { owner: self, command, request })
    }
}

impl Pending {
    pub closed spec fn view(&self) -> RequestView {
        RequestView { owner: self.owner.view(), command: self.command, request: self.request }
    }
    pub open spec fn wf(&self) -> bool { request_valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn pending_command(&self) -> (r: Command) ensures r == self.view().command { self.command }
    pub fn pending_request(&self) -> (r: u64) ensures r == self.view().request { self.request }
    pub fn pending_identity(&self) -> (r: (u64, u32, u32)) ensures r == (self.view().owner.volume, self.view().owner.inode, self.view().owner.generation) { self.owner.identity() }
    pub fn cancel_before_issue(self) -> (r: Lifecycle) ensures r.wf(), r.view() == self.view().owner { proof { use_type_invariant(&self); } self.owner }
    pub fn issue(self) -> (r: Issued) ensures r.wf(), r.view() == self.view() { proof { use_type_invariant(&self); }
        Issued { owner: self.owner, command: self.command, request: self.request }
    }
}
impl Issued {
    pub closed spec fn view(&self) -> RequestView {
        RequestView { owner: self.owner.view(), command: self.command, request: self.request }
    }
    pub open spec fn wf(&self) -> bool {
        valid(self.view().owner)
            && enabled(View { faulted: false, ..self.view().owner }, self.view().command)
            && self.view().request > 0 && self.view().request as nat + 1 == self.view().owner.next_request
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn issued_command(&self) -> (r: Command) ensures r == self.view().command { self.command }
    pub fn issued_request(&self) -> (r: u64) ensures r == self.view().request { self.request }
    pub fn issued_identity(&self) -> (r: (u64, u32, u32)) ensures r == (self.view().owner.volume, self.view().owner.inode, self.view().owner.generation) { self.owner.identity() }
    /// Abort retains the issued request; issued effects may persist later.
    pub fn abort_pending(mut self) -> (r: Self)
        ensures r.wf(), r.view() == (RequestView { owner: View { faulted: true, ..self.view().owner }, ..self.view() }),
    { proof { use_type_invariant(&self); } self.owner.faulted = true; self }
    pub fn finish(self, completion: Completion) -> (r: Lifecycle)
        ensures r.wf(), r.view() == completed(self.view().owner, self.view().command, completion),
            r.view().remaining as nat + r.view().reclaimed as nat
                == self.view().owner.remaining as nat + self.view().owner.reclaimed as nat,
    {
        proof { use_type_invariant(&self); }
        let Issued { mut owner, command, request: _ } = self;
        if matches!(completion, Completion::Failed) || owner.faulted {
            owner.faulted = true; return owner;
        }
        match command {
            Command::JournalAdd { .. } => { owner.stage = Stage::OrphanDurable; },
            Command::JournalReclaim { blocks, .. } => {
                if blocks == 0 || blocks > owner.remaining || blocks > u64::MAX - owner.reclaimed {
                    owner.faulted = true; return owner;
                }
                owner.remaining -= blocks; owner.reclaimed += blocks;
                owner.stage = Stage::ReclaimCommitted;
            },
            Command::CheckpointData => { owner.stage = Stage::ReclaimCheckpointed; },
            Command::QuiesceData => {
                owner.stage = if owner.remaining == 0 { Stage::NeedRemove } else { Stage::OrphanDurable };
            },
            Command::JournalRemove { .. } => { owner.stage = Stage::RemovalCommitted; },
            Command::CheckpointRemoval => { owner.stage = Stage::RemovalCheckpointed; },
            Command::QuiesceRemoval => { owner.stage = Stage::Retired; },
        }
        owner
    }
}

/// The add transaction must atomically include last-unlink or the truncate's
/// logical-size change. Its candidate is private until JournalAdd is durable.
pub fn prepare(volume: u64, inode: u32, generation: u32, reason: Reason,
    links_before: u16, handles: u64, io_pins: u64, current_blocks: u64,
    target_blocks: u64) -> (r: Result<Lifecycle, Error>)
    ensures match r {
        Ok(owner) => owner.wf() && owner.view().volume == volume && owner.view().inode == inode
            && owner.view().generation == generation && owner.view().reason == reason
            && owner.view().handles == handles && owner.view().io_pins == io_pins
            && owner.view().target_blocks == target_blocks
            && owner.view().remaining as nat == current_blocks as nat - target_blocks as nat
            && owner.view().reclaimed == 0 && owner.view().stage == Stage::AddReady && !owner.view().faulted,
        Err(_) => true,
    },
{
    if volume == 0 || inode == 0 { return Err(Error::Identity); }
    if target_blocks > current_blocks { return Err(Error::Geometry); }
    if matches!(reason, Reason::Unlink) && (links_before != 1 || target_blocks != 0) {
        return Err(Error::Links);
    }
    if matches!(reason, Reason::Truncate) && links_before == 0 { return Err(Error::Links); }
    Ok(Lifecycle { volume, inode, generation, reason,
        links_after: if matches!(reason, Reason::Unlink) { 0 } else { links_before },
        handles, io_pins, target_blocks, remaining: current_blocks - target_blocks,
        reclaimed: 0, stage: Stage::AddReady, faulted: false, next_request: 1 })
}

/// A cold recovery source must establish the retained orphan record and
/// target size before calling this factory. Recovery starts after reset
/// quiescence, with no open descriptors or old DMA loans.
pub fn resume_from_recovered_inode(volume: u64, inode: u32, generation: u32,
    links: u16, current_blocks: u64, target_blocks: u64) -> (r: Result<Lifecycle, Error>)
    ensures match r {
        Ok(owner) => owner.wf() && owner.view().volume == volume && owner.view().inode == inode
            && owner.view().generation == generation && owner.view().links_after == links
            && owner.view().handles == 0 && owner.view().io_pins == 0
            && owner.view().target_blocks == target_blocks
            && owner.view().remaining as nat == current_blocks as nat - target_blocks as nat
            && owner.view().reclaimed == 0 && owner.view().stage == Stage::OrphanDurable && !owner.view().faulted,
        Err(_) => true,
    },
{
    if volume == 0 || inode == 0 { return Err(Error::Identity); }
    if target_blocks > current_blocks || (links == 0 && target_blocks != 0) {
        return Err(Error::Geometry);
    }
    Ok(Lifecycle { volume, inode, generation,
        reason: if links == 0 { Reason::Unlink } else { Reason::Truncate },
        links_after: links, handles: 0, io_pins: 0, target_blocks,
        remaining: current_blocks - target_blocks, reclaimed: 0,
        stage: Stage::OrphanDurable, faulted: false, next_request: 1 })
}


pub proof fn reclamation_requires_a_durable_orphan_and_no_prior_io(v: View, command: Command)
    requires valid(v), enabled(v, command), command is JournalReclaim,
    ensures v.stage == Stage::OrphanDurable && v.io_pins == 0
        && (v.reason == Reason::Unlink ==> v.handles == 0),
{ }
pub proof fn inode_reuse_requires_the_final_removal_quiescence(v: View, command: Command, completion: Completion)
    requires valid(v), enabled(v, command), reusable(completed(v, command, completion)),
    ensures command == Command::QuiesceRemoval && matches!(completion, Completion::Durable)
        && v.stage == Stage::RemovalCheckpointed && v.remaining == 0 && v.handles == 0 && v.io_pins == 0,
{ }
pub proof fn failed_or_aborted_requests_never_authorize_reuse(v: View, command: Command)
    ensures !reusable(completed(v, command, Completion::Failed)),
{ }
pub proof fn reclamation_preserves_the_total_work(v: View, command: Command, completion: Completion)
    requires valid(v), enabled(v, command),
    ensures completed(v, command, completion).remaining as nat + completed(v, command, completion).reclaimed as nat
        == v.remaining as nat + v.reclaimed as nat,
{ }

}
