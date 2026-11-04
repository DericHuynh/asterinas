// SPDX-License-Identifier: MPL-2.0

//! Exact admission conditions for appending disjoint physical claims.
//! These are filesystem block roles, independent of CortenMM frame ownership.

use vstd::prelude::*;
use crate::block_claims::{self, CensusView, Claim, Slot};

verus! {

pub open spec fn available(roles: Seq<Slot>, claim: Claim) -> bool {
    block_claims::valid_claim(claim, roles.len())
        && forall|b: int| block_claims::covers(claim, b) ==> (#[trigger] roles[b]).kind == 0
}

pub open spec fn appendable(roles: Seq<Slot>, claims: Seq<Claim>) -> bool {
    &&& forall|i: int| 0 <= i < claims.len() ==> #[trigger] available(roles, claims[i])
    &&& forall|i: int, j: int| 0 <= i < j < claims.len() ==> #[trigger] block_claims::disjoint(claims[i], claims[j])
}

pub proof fn an_appendable_sequence_has_appendable_prefixes(roles: Seq<Slot>, claims: Seq<Claim>, count: nat)
    requires appendable(roles, claims), count <= claims.len(),
    ensures appendable(roles, claims.take(count as int)),
{
    assert forall|i: int| 0 <= i < claims.take(count as int).len() implies #[trigger] available(roles, claims.take(count as int)[i]) by {
        assert(claims.take(count as int)[i] == claims[i]);
        assert(available(roles, claims[i]));
    }
    assert forall|i: int, j: int| 0 <= i < j < claims.take(count as int).len() implies
        #[trigger] block_claims::disjoint(claims.take(count as int)[i], claims.take(count as int)[j]) by {
        assert(claims.take(count as int)[i] == claims[i] && claims.take(count as int)[j] == claims[j]);
        assert(block_claims::disjoint(claims[i], claims[j]));
    }
}

proof fn claims_disjoint_from_a_range_have_a_free_lookup(claims: Seq<Claim>, next: Claim, block: int)
    requires block_claims::covers(next, block),
        forall|i: int| 0 <= i < claims.len() ==> #[trigger] block_claims::disjoint(claims[i], next),
    ensures block_claims::lookup(claims, block) == block_claims::free_slot(),
    decreases claims.len(),
{
    reveal(block_claims::lookup);
    if claims.len() > 0 {
        assert(block_claims::disjoint(claims[claims.len() as int - 1], next));
        assert(!block_claims::covers(claims.last(), block));
        assert forall|i: int| 0 <= i < claims.drop_last().len() implies
            #[trigger] block_claims::disjoint(claims.drop_last()[i], next) by {
            assert(claims.drop_last()[i] == claims[i]);
        }
        claims_disjoint_from_a_range_have_a_free_lookup(claims.drop_last(), next, block);
    }
}

/// A valid final ledger proves that the added claims were valid, pairwise
/// disjoint and entirely free in the original ledger. This is necessity,
/// independent of the particular sequence of runtime claim calls.
pub proof fn every_valid_ledger_extension_was_appendable(before: CensusView, after: CensusView, added: Seq<Claim>)
    requires block_claims::ledger(before.roles, before.claims), block_claims::ledger(after.roles, after.claims),
        after.roles.len() == before.roles.len(), after.claims == before.claims + added,
    ensures appendable(before.roles, added),
{
    reveal(block_claims::ledger);
    assert forall|i: int| 0 <= i < added.len() implies #[trigger] available(before.roles, added[i]) by {
        let position = before.claims.len() as int + i;
        assert(after.claims[position] == added[i]);
        assert(block_claims::valid_claim(added[i], before.roles.len()));
        assert forall|j: int| 0 <= j < before.claims.len() implies
            #[trigger] block_claims::disjoint(before.claims[j], added[i]) by {
            assert(after.claims[j] == before.claims[j]);
            assert(block_claims::disjoint(after.claims[j], after.claims[position]));
        }
        assert forall|b: int| block_claims::covers(added[i], b) implies (#[trigger] before.roles[b]).kind == 0 by {
            claims_disjoint_from_a_range_have_a_free_lookup(before.claims, added[i], b);
            assert(before.roles[b] == block_claims::lookup(before.claims, b));
        }
    }
    assert forall|i: int, j: int| 0 <= i < j < added.len() implies
        #[trigger] block_claims::disjoint(added[i], added[j]) by {
        let first = before.claims.len() as int + i;
        let second = before.claims.len() as int + j;
        assert(after.claims[first] == added[i] && after.claims[second] == added[j]);
        assert(block_claims::disjoint(after.claims[first], after.claims[second]));
    }
}

/// Exact pointwise claim execution cannot consume any later disjoint claim.
pub proof fn appending_one_claim_keeps_the_remaining_claims_appendable(before: Seq<Slot>, after: Seq<Slot>, claims: Seq<Claim>)
    requires appendable(before, claims), claims.len() > 0, after.len() == before.len(),
        forall|b: int| 0 <= b < before.len() ==> (#[trigger] after[b])
            == if block_claims::covers(claims[0], b) { block_claims::at(claims[0], b) } else { before[b] },
    ensures appendable(after, claims.skip(1)),
{
    assert forall|i: int| 0 <= i < claims.skip(1).len() implies #[trigger] available(after, claims.skip(1)[i]) by {
        assert(claims.skip(1)[i] == claims[i + 1]);
        assert(available(before, claims[i + 1]));
        assert(block_claims::disjoint(claims[0], claims[i + 1]));
        assert forall|b: int| block_claims::covers(claims.skip(1)[i], b) implies (#[trigger] after[b]).kind == 0 by {
            assert(0 <= b < before.len());
            assert(!block_claims::covers(claims[0], b));
            assert(before[b].kind == 0);
        }
    }
    assert forall|i: int, j: int| 0 <= i < j < claims.skip(1).len() implies
        #[trigger] block_claims::disjoint(claims.skip(1)[i], claims.skip(1)[j]) by {
        assert(claims.skip(1)[i] == claims[i + 1] && claims.skip(1)[j] == claims[j + 1]);
        assert(block_claims::disjoint(claims[i + 1], claims[j + 1]));
    }
}

proof fn a_noncovering_suffix_keeps_the_previous_lookup(previous: Seq<Claim>, added: Seq<Claim>, block: int)
    requires forall|i: int| 0 <= i < added.len() ==> !#[trigger] block_claims::covers(added[i], block),
    ensures block_claims::lookup(previous + added, block) == block_claims::lookup(previous, block),
    decreases added.len(),
{
    if added.len() > 0 {
        assert((previous + added).last() == added[added.len() as int - 1]);
        assert(!block_claims::covers(added[added.len() as int - 1], block));
        assert((previous + added).drop_last() =~= previous + added.drop_last());
        assert forall|i: int| 0 <= i < added.drop_last().len() implies !#[trigger] block_claims::covers(added.drop_last()[i], block) by {
            assert(added.drop_last()[i] == added[i]);
        }
        a_noncovering_suffix_keeps_the_previous_lookup(previous, added.drop_last(), block);
        reveal(block_claims::lookup);
    } else { assert(previous + added =~= previous); }
}

/// A completed recursive subtree may append several claims at once. Its
/// exact ledger prefix still cannot consume any remaining disjoint claim.
pub proof fn a_valid_prefix_extension_keeps_the_remaining_claims_appendable(before: CensusView, after: CensusView, claims: Seq<Claim>, count: nat)
    requires block_claims::ledger(before.roles, before.claims), block_claims::ledger(after.roles, after.claims),
        after.roles.len() == before.roles.len(), count <= claims.len(), appendable(before.roles, claims),
        after.claims == before.claims + claims.take(count as int),
    ensures appendable(after.roles, claims.skip(count as int)),
{
    reveal(block_claims::ledger);
    let added = claims.take(count as int);
    let remaining = claims.skip(count as int);
    assert forall|i: int| 0 <= i < remaining.len() implies #[trigger] available(after.roles, remaining[i]) by {
        assert(remaining[i] == claims[count as int + i]);
        assert(available(before.roles, claims[count as int + i]));
        assert forall|block: int| block_claims::covers(remaining[i], block) implies (#[trigger] after.roles[block]).kind == 0 by {
            assert(before.roles[block].kind == 0);
            assert forall|j: int| 0 <= j < added.len() implies !#[trigger] block_claims::covers(added[j], block) by {
                assert(added[j] == claims[j]);
                assert(block_claims::disjoint(claims[j], claims[count as int + i]));
            }
            a_noncovering_suffix_keeps_the_previous_lookup(before.claims, added, block);
            assert(before.roles[block] == block_claims::lookup(before.claims, block));
            assert(after.roles[block] == block_claims::lookup(before.claims + added, block));
        }
    }
    assert forall|i: int, j: int| 0 <= i < j < remaining.len() implies #[trigger] block_claims::disjoint(remaining[i], remaining[j]) by {
        assert(remaining[i] == claims[count as int + i] && remaining[j] == claims[count as int + j]);
        assert(block_claims::disjoint(claims[count as int + i], claims[count as int + j]));
    }
}

}
