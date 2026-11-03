// SPDX-License-Identifier: MPL-2.0

//! Abstract transaction-gate ownership and stale-lease rejection.
//! This does not implement, or yet refine to, an OSTD mutex.

use vstd::prelude::*;

verus! {

pub struct Gate {
    pub owner: Option<nat>,
    pub generation: nat,
}

pub open spec fn permitted(g: Gate, actor: nat, generation: nat) -> bool {
    g.owner == Some(actor) && g.generation == generation
}

pub open spec fn claim(g: Gate, actor: nat) -> Gate {
    Gate { owner: Some(actor), generation: g.generation + 1 }
}

pub open spec fn release(g: Gate) -> Gate {
    Gate { owner: None, generation: g.generation }
}

pub proof fn two_current_writers_are_the_same_actor(
    g: Gate, a: nat, b: nat, ga: nat, gb: nat,
)
    requires permitted(g, a, ga), permitted(g, b, gb),
    ensures a == b, ga == gb,
{
}

pub proof fn claim_advances_generation(g: Gate, actor: nat)
    requires g.owner == None,
    ensures claim(g, actor).generation > g.generation,
        permitted(claim(g, actor), actor, g.generation + 1),
{
}

pub proof fn releasing_revokes_current_lease(g: Gate, actor: nat, generation: nat)
    ensures !permitted(release(g), actor, generation),
{
}

pub proof fn stale_lease_cannot_return_after_reacquisition(g: Gate, actor: nat)
    requires g.owner == None,
    ensures !permitted(
        claim(release(claim(g, actor)), actor),
        actor, claim(g, actor).generation,
    ),
{
}

}
