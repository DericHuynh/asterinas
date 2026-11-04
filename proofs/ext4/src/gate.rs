// SPDX-License-Identifier: MPL-2.0

//! An affine writer capability, backed by vstd's exclusive resource algebra.
//! Unlike lease.rs's predicates, this token cannot be duplicated by verified
//! clients. Refinement to a sleeping OSTD lock is still a separate obligation.

use vstd::prelude::*;
use vstd::resource::{Loc, exclusive::ExclusiveRA, pcm::Resource, algebra::ResourceAlgebra};

verus! {

pub struct Lease { pub owner: Option<nat>, pub generation: nat }
type Algebra = Option<ExclusiveRA<Lease>>;

pub tracked struct WriterToken { resource: Resource<Algebra> }

impl WriterToken {
    pub closed spec fn id(&self) -> Loc { self.resource.loc() }
    pub closed spec fn wf(&self) -> bool {
        self.resource.value() is Some && self.resource.value()->Some_0 is Exclusive
    }
    pub closed spec fn state(&self) -> Lease {
        self.resource.value()->Some_0->Exclusive_0
    }

    pub proof fn new() -> (tracked r: Self)
        ensures r.wf(), r.state().owner == None, r.state().generation == 0,
    {
        let tracked resource = Resource::alloc(Some(ExclusiveRA::Exclusive(
            Lease { owner: None, generation: 0 })));
        WriterToken { resource }
    }

    proof fn replace(tracked self, state: Lease) -> (tracked r: Self)
        requires self.wf(),
        ensures r.wf(), r.id() == self.id(), r.state() == state,
    {
        let value = Some(ExclusiveRA::Exclusive(state));
        assert forall|frame: Algebra|
            #[trigger] Algebra::op(self.resource.value(), frame).valid()
            implies #[trigger] Algebra::op(value, frame).valid() by {
            if frame is Some { assert(false); }
        }
        let tracked resource = self.resource.update(value);
        WriterToken { resource }
    }

    pub proof fn claim(tracked self, actor: nat) -> (tracked r: Self)
        requires self.wf(), self.state().owner == None,
        ensures r.wf(), r.id() == self.id(), r.state().owner == Some(actor),
            r.state().generation == self.state().generation + 1,
    {
        self.replace(Lease { owner: Some(actor), generation: self.state().generation + 1 })
    }

    pub proof fn release(tracked self) -> (tracked r: Self)
        requires self.wf(), self.state().owner is Some,
        ensures r.wf(), r.id() == self.id(), r.state().owner == None,
            r.state().generation == self.state().generation,
    {
        self.replace(Lease { owner: None, generation: self.state().generation })
    }
}

pub proof fn capabilities_for_one_gate_cannot_be_duplicated(
    tracked a: &mut WriterToken, tracked b: &WriterToken,
)
    requires old(a).wf(), b.wf(),
    ensures final(a).id() != b.id(), *final(a) == *old(a),
{
    if a.id() == b.id() { a.resource.validate_2(&b.resource); }
}

pub proof fn nonvacuous_claim_release_reacquire(actor: nat) {
    let tracked free = WriterToken::new();
    let ghost id = free.id();
    let tracked held = free.claim(actor);
    let ghost old_generation = held.state().generation;
    let tracked free = held.release();
    let tracked held = free.claim(actor);
    assert(held.id() == id);
    assert(held.state().owner == Some(actor));
    assert(held.state().generation == old_generation + 1);
    assert(held.state().generation != old_generation);
}

}
