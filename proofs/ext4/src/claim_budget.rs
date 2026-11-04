// SPDX-License-Identifier: MPL-2.0

//! Physical resource bounds from valid disjoint filesystem block claims.

use vstd::prelude::*;
use crate::{block_claims::{self, Claim, Slot}, extent_claims, inode_claims};

verus! {

pub open spec fn interval(claim: Claim) -> Seq<int> {
    Seq::new(claim.length as nat, |i: int| claim.start as int + i)
}

#[verifier::opaque]
pub open spec fn enumeration(claims: Seq<Claim>) -> Seq<int>
    decreases claims.len(),
{
    if claims.len() == 0 { Seq::empty() }
    else { enumeration(claims.drop_last()) + interval(claims.last()) }
}

proof fn disjoint_valid_claims_enumerate_distinct_bounded_blocks(claims: Seq<Claim>, blocks: nat)
    requires forall|i: int| 0 <= i < claims.len() ==> #[trigger] block_claims::valid_claim(claims[i], blocks),
        forall|i: int, j: int| 0 <= i < j < claims.len() ==> #[trigger] block_claims::disjoint(claims[i], claims[j]),
    ensures enumeration(claims).len() == inode_claims::allocated(claims), enumeration(claims).no_duplicates(),
        forall|i: int| 0 <= i < enumeration(claims).len() ==> 0 <= (#[trigger] enumeration(claims)[i]) < blocks
            && exists|j: int| 0 <= j < claims.len() && #[trigger] block_claims::covers(claims[j], enumeration(claims)[i]),
    decreases claims.len(),
{
    reveal(enumeration);
    reveal(inode_claims::allocated);
    if claims.len() == 0 {
        assert(enumeration(claims) =~= Seq::<int>::empty());
    } else {
        let previous = claims.drop_last();
        let last = claims.last();
        assert(block_claims::valid_claim(last, blocks));
        assert forall|i: int| 0 <= i < previous.len() implies #[trigger] block_claims::valid_claim(previous[i], blocks) by {
            assert(previous[i] == claims[i]);
        }
        assert forall|i: int, j: int| 0 <= i < j < previous.len() implies #[trigger] block_claims::disjoint(previous[i], previous[j]) by {
            assert(previous[i] == claims[i] && previous[j] == claims[j]);
        }
        disjoint_valid_claims_enumerate_distinct_bounded_blocks(previous, blocks);
        let prefix = enumeration(previous);
        let suffix = interval(last);
        assert(suffix.no_duplicates());
        assert forall|i: int, j: int| 0 <= i < prefix.len() && 0 <= j < suffix.len() implies prefix[i] != suffix[j] by {
            let owner = choose|k: int| 0 <= k < previous.len() && block_claims::covers(previous[k], prefix[i]);
            assert(previous[owner] == claims[owner]);
            assert(last == claims[claims.len() as int - 1]);
            assert(block_claims::disjoint(previous[owner], last));
            assert(block_claims::covers(last, suffix[j]));
        }
        vstd::seq_lib::lemma_no_dup_in_concat(prefix, suffix);
        assert forall|i: int| 0 <= i < enumeration(claims).len() implies 0 <= (#[trigger] enumeration(claims)[i]) < blocks
            && exists|j: int| 0 <= j < claims.len() && #[trigger] block_claims::covers(claims[j], enumeration(claims)[i]) by {
            if i < prefix.len() {
                assert(enumeration(claims)[i] == prefix[i]);
                let owner = choose|k: int| 0 <= k < previous.len() && block_claims::covers(previous[k], prefix[i]);
                assert(previous[owner] == claims[owner]);
                assert(block_claims::covers(claims[owner], enumeration(claims)[i]));
            } else {
                assert(enumeration(claims)[i] == suffix[i - prefix.len() as int]);
                assert(block_claims::covers(claims[claims.len() as int - 1], enumeration(claims)[i]));
            }
        }
    }
}

/// Valid physical intervals are disjoint subsets of a finite volume. Their
/// total lengths, including metadata and data, therefore fit that volume.
pub proof fn every_disjoint_claim_ledger_fits_the_physical_volume(roles: Seq<Slot>, claims: Seq<Claim>)
    requires block_claims::ledger(roles, claims),
    ensures inode_claims::allocated(claims) <= roles.len(),
{
    reveal(block_claims::ledger);
    disjoint_valid_claims_enumerate_distinct_bounded_blocks(claims, roles.len());
    let actual = enumeration(claims);
    let volume = Seq::new(roles.len(), |i: int| i);
    assert(volume.no_duplicates());
    actual.unique_seq_to_set();
    volume.unique_seq_to_set();
    actual.to_set_ensures();
    volume.to_set_ensures();
    assert(actual.to_set().subset_of(volume.to_set())) by {
        assert forall|block: int| actual.to_set().contains(block) implies volume.to_set().contains(block) by {
            let i = choose|i: int| 0 <= i < actual.len() && actual[i] == block;
            assert(0 <= block < roles.len());
            assert(volume[block] == block);
            assert(volume.to_set().contains(volume[block]));
        }
    }
    vstd::set_lib::lemma_len_subset(actual.to_set(), volume.to_set());
}

pub proof fn an_appended_claim_sequence_fits_the_final_ledger(roles: Seq<Slot>, previous: Seq<Claim>, added: Seq<Claim>)
    requires block_claims::ledger(roles, previous + added),
    ensures inode_claims::allocated(added) <= roles.len(),
{
    every_disjoint_claim_ledger_fits_the_physical_volume(roles, previous + added);
    extent_claims::allocated_concatenation(previous, added);
}

}
