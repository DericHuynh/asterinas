// SPDX-License-Identifier: MPL-2.0

//! An outstanding request owns its exact recovery machine. Completion consumes
//! this object, so a callback cannot name another machine by a recycled integer
//! ID. Device reports still need the concrete adapter's flush/DMA contract.

use vstd::prelude::*;
use crate::recovery_io::{self, Command, Recovery};

verus! {

pub enum Completion { Succeeded, Failed }
pub struct Pending { engine: Recovery, id: u64 }

pub open spec fn same_images(a: &Recovery, b: &Recovery) -> bool {
    &&& a.plan() == b.plan() && a.tail() == b.tail() && a.journal_block() == b.journal_block()
    &&& a.scan_result() == b.scan_result()
    &&& a.primary() == b.primary() && a.partition_bytes() == b.partition_bytes()
}

impl Pending {
    pub closed spec fn owner(&self) -> &Recovery { &self.engine }
    pub closed spec fn id(&self) -> u64 { self.id }

    #[verifier::type_invariant]
    spec fn valid(self) -> bool { self.owner().state().pending && self.id() == self.owner().state().request }

    pub fn pending_command(&self) -> (r: Command<'_>)
        ensures r.view() == self.owner().expected(),
            match r.view() {
                recovery_io::CommandView::Write { block, image } => image.len() == 4096
                    && block < self.owner().plan().layout().view().fs_blocks
                    && block as nat * 4096 + 4096 <= self.owner().partition_bytes(),
                recovery_io::CommandView::Flush => true,
            },
    {
        proof { use_type_invariant(self); }
        self.engine.command().unwrap()
    }

    pub fn abort_pending(self) -> (r: Self)
        ensures same_images(r.owner(), self.owner()),
            r.owner().state() == (recovery_io::State { faulted: true, ..self.owner().state() }), r.id() == self.id(),
    {
        proof { use_type_invariant(&self); }
        let Pending { mut engine, id } = self;
        engine.abort();
        Pending { engine, id }
    }

    pub fn finish_pending(self, outcome: Completion) -> (r: Recovery)
        ensures same_images(&r, self.owner()),
            r.state() == recovery_io::completed(self.owner().state(), self.owner().plan().selection().len(), outcome is Succeeded),
    {
        proof { use_type_invariant(&self); }
        let Pending { mut engine, id } = self;
        let succeeded = match outcome { Completion::Succeeded => true, Completion::Failed => false };
        let accepted = engine.complete(id, succeeded);
        assert(accepted);
        engine
    }
}

pub fn dispatch(mut engine: Recovery) -> (r: Result<Pending, Recovery>)
    ensures match r {
        Ok(p) => same_images(p.owner(), &engine) && !engine.state().pending && !engine.state().faulted && engine.state().phase < 4
            && p.owner().state() == recovery_io::started(engine.state()),
        Err(s) => same_images(&s, &engine) && s.state() == engine.state()
            && (engine.state().pending || engine.state().faulted || engine.state().phase == 4),
    },
{
    match engine.begin() {
        Some(id) => Ok(Pending { engine, id }),
        None => Err(engine),
    }
}

pub proof fn a_pending_request_is_bound_to_its_owned_machine(tracked p: &Pending)
    ensures p.owner().state().pending, p.id() == p.owner().state().request,
{
    use_type_invariant(p);
}

}
