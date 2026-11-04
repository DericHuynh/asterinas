// SPDX-License-Identifier: MPL-2.0

//! A bounded ownership census for volume validation. Claims are candidate
//! metadata, not file handles or allocation authority. Every range is checked
//! before changing the census; physical aliases are rejected within and across
//! inodes, journal space and reserved metadata.

use vstd::prelude::*;
use crate::bitmap;

verus! {

pub const MAX_BLOCKS: u32 = 1048576;

// 0: free, 1: reserved, 2: journal, 3: volume metadata, 4: file data,
// 5: directory data, 6: inode-owned extent-tree metadata.
#[derive(Clone, Copy)]
pub struct Slot { pub kind: u8, pub inode: u32, pub generation: u32, pub logical: u32, pub initialized: bool }
#[derive(Clone, Copy)]
pub struct Claim {
    pub start: u32, pub length: u32, pub kind: u8, pub inode: u32,
    pub generation: u32, pub logical: u32, pub initialized: bool,
}

pub open spec fn free_slot() -> Slot { Slot { kind: 0, inode: 0, generation: 0, logical: 0, initialized: false } }

pub open spec fn valid_claim(c: Claim, blocks: nat) -> bool {
    &&& c.length > 0 && c.start as nat + c.length <= blocks
    &&& 1 <= c.kind <= 6
    &&& (if c.kind == 4 || c.kind == 5 {
        c.inode > 0 && c.logical as nat + c.length <= 4294967296 && (c.kind == 5 ==> c.initialized)
    } else if c.kind == 6 {
        c.inode > 0 && c.length == 1 && c.logical == 0 && !c.initialized
    } else { c.inode == 0 && c.generation == 0 && c.logical == 0 && !c.initialized })
}

pub open spec fn covers(c: Claim, block: int) -> bool { c.start <= block < c.start as int + c.length }

pub open spec fn at(c: Claim, block: int) -> Slot {
    Slot { kind: c.kind, inode: c.inode, generation: c.generation,
        logical: if c.kind == 4 || c.kind == 5 { (c.logical as int + block - c.start) as u32 } else { 0 }, initialized: c.initialized }
}

#[verifier::opaque]
pub open spec fn lookup(claims: Seq<Claim>, block: int) -> Slot
    decreases claims.len(),
{
    if claims.len() == 0 { free_slot() }
    else if covers(claims.last(), block) { at(claims.last(), block) }
    else { lookup(claims.drop_last(), block) }
}

pub open spec fn disjoint(a: Claim, b: Claim) -> bool {
    a.start as nat + a.length <= b.start || b.start as nat + b.length <= a.start
}

#[verifier::opaque]
pub open spec fn preserves_occupied(before: Seq<Slot>, after: Seq<Slot>) -> bool {
    before.len() == after.len() && (forall|b: int| 0 <= b < before.len() && (#[trigger] before[b]).kind != 0 ==> after[b] == before[b])
}

pub proof fn occupied_slot_preservation_is_transitive(a: Seq<Slot>, b: Seq<Slot>, c: Seq<Slot>)
    requires preserves_occupied(a, b), preserves_occupied(b, c),
    ensures preserves_occupied(a, c),
{
    reveal(preserves_occupied);
    assert forall|i: int| 0 <= i < a.len() && (#[trigger] a[i]).kind != 0 implies c[i] == a[i] by {
        assert(b[i] == a[i] && b[i].kind != 0);
    }
}

#[verifier::opaque]
pub open spec fn ledger(roles: Seq<Slot>, claims: Seq<Claim>) -> bool {
    &&& 2 < roles.len() <= MAX_BLOCKS
    &&& (forall|i: int| 0 <= i < claims.len() ==> #[trigger] valid_claim(claims[i], roles.len()))
    &&& (forall|i: int, j: int| 0 <= i < j < claims.len() ==> #[trigger] disjoint(claims[i], claims[j]))
    &&& (forall|b: int| 0 <= b < roles.len() ==> #[trigger] roles[b] == lookup(claims, b))
}

proof fn a_covering_claim_marks_an_occupied_slot(claims: Seq<Claim>, blocks: nat, block: int, index: int)
    requires forall|i: int| 0 <= i < claims.len() ==> #[trigger] valid_claim(claims[i], blocks),
        0 <= index < claims.len(), covers(claims[index], block),
    ensures lookup(claims, block).kind != 0,
    decreases claims.len(),
{
    reveal(lookup);
    if !covers(claims.last(), block) {
        assert(index < claims.len() - 1);
        assert forall|i: int| 0 <= i < claims.drop_last().len() implies #[trigger] valid_claim(claims.drop_last()[i], blocks) by {
            assert(claims.drop_last()[i] == claims[i]);
        }
        a_covering_claim_marks_an_occupied_slot(claims.drop_last(), blocks, block, index);
    } else { assert(valid_claim(claims[claims.len() as int - 1], blocks)); }
}

proof fn one_covering_claim_determines_lookup(claims: Seq<Claim>, block: int, index: int)
    requires 0 <= index < claims.len(), covers(claims[index], block),
        forall|i: int, j: int| 0 <= i < j < claims.len() ==> #[trigger] disjoint(claims[i], claims[j]),
    ensures lookup(claims, block) == at(claims[index], block),
    decreases claims.len(),
{
    reveal(lookup);
    if covers(claims.last(), block) {
        if index < claims.len() - 1 { assert(disjoint(claims[index], claims[claims.len() as int - 1])); }
    } else {
        assert(index < claims.len() - 1);
        assert forall|i: int, j: int| 0 <= i < j < claims.drop_last().len()
            implies #[trigger] disjoint(claims.drop_last()[i], claims.drop_last()[j]) by {
            assert(claims.drop_last()[i] == claims[i] && claims.drop_last()[j] == claims[j]);
        }
        one_covering_claim_determines_lookup(claims.drop_last(), block, index);
    }
}

proof fn an_entirely_free_range_is_disjoint(roles: Seq<Slot>, claims: Seq<Claim>, c: Claim)
    requires ledger(roles, claims), valid_claim(c, roles.len()),
        forall|b: int| covers(c, b) ==> (#[trigger] roles[b]).kind == 0,
    ensures forall|i: int| 0 <= i < claims.len() ==> #[trigger] disjoint(claims[i], c),
{
    reveal(ledger);
    assert forall|i: int| 0 <= i < claims.len() implies #[trigger] disjoint(claims[i], c) by {
        assert(valid_claim(claims[i], roles.len()));
        if !disjoint(claims[i], c) {
            let block = if claims[i].start > c.start { claims[i].start as int } else { c.start as int };
            assert(covers(claims[i], block) && covers(c, block));
            a_covering_claim_marks_an_occupied_slot(claims, roles.len(), block, i);
            assert(roles[block].kind == 0 && roles[block] == lookup(claims, block));
        }
    }
}

#[verifier::opaque]
pub open spec fn bitmap_matches(roles: Seq<Slot>, first: u32, bitmap: bitmap::BitmapView) -> bool {
    &&& bitmap::accepted(bitmap.raw, bitmap.valid, bitmap.meaningful, bitmap.free, bitmap.checksum, bitmap.seed)
    &&& first as nat + bitmap.valid <= roles.len()
    &&& (forall|i: int| 0 <= i < bitmap.valid ==>
        #[trigger] bitmap::set(bitmap.raw, i) == (roles[first as int + i].kind != 0))
}

#[verifier::opaque]
pub open spec fn free_roles(roles: Seq<Slot>, first: u32, count: nat) -> nat
    decreases count,
{
    if count == 0 { 0nat }
    else { free_roles(roles, first, (count - 1) as nat)
        + if roles[first as int + count as int - 1].kind == 0 { 1nat } else { 0nat } }
}

proof fn matching_prefixes_have_equal_free_counts(roles: Seq<Slot>, first: u32, raw: Seq<u8>, count: nat)
    requires first as nat + count <= roles.len(),
        forall|i: int| 0 <= i < count ==> #[trigger] bitmap::set(raw, i) == (roles[first as int + i].kind != 0),
    ensures free_roles(roles, first, count) == bitmap::free_bits(raw, count),
    decreases count,
{
    reveal(free_roles);
    reveal(bitmap::free_bits);
    if count > 0 {
        matching_prefixes_have_equal_free_counts(roles, first, raw, (count - 1) as nat);
        assert(bitmap::set(raw, count as int - 1) == (roles[first as int + count as int - 1].kind != 0));
    }
}

fn check_claim(c: &Claim, blocks: usize) -> (r: bool)
    ensures r == valid_claim(*c, blocks as nat),
{
    c.length > 0 && c.start as u64 + c.length as u64 <= blocks as u64 && c.kind >= 1 && c.kind <= 6
        && if c.kind == 4 || c.kind == 5 {
            c.inode > 0 && c.logical as u64 + c.length as u64 <= 4294967296 && (c.kind != 5 || c.initialized)
        } else if c.kind == 6 {
            c.inode > 0 && c.length == 1 && c.logical == 0 && !c.initialized
        } else { c.inode == 0 && c.generation == 0 && c.logical == 0 && !c.initialized }
}

fn slot_at(c: &Claim, block: u32) -> (r: Slot)
    requires valid_claim(*c, MAX_BLOCKS as nat), covers(*c, block as int),
    ensures r == at(*c, block as int),
{
    let logical = if c.kind == 4 || c.kind == 5 { (c.logical as u64 + (block - c.start) as u64) as u32 } else { 0 };
    Slot { kind: c.kind, inode: c.inode, generation: c.generation, logical, initialized: c.initialized }
}

pub struct CensusView { pub roles: Seq<Slot>, pub claims: Seq<Claim> }
pub struct Census { roles: Vec<Slot>, claims: Ghost<Seq<Claim>> }

impl Census {
    pub closed spec fn view(&self) -> CensusView { CensusView { roles: self.roles@, claims: self.claims@ } }
    pub open spec fn wf(&self) -> bool { ledger(self.view().roles, self.view().claims) }

    #[verifier::type_invariant]
    spec fn valid(self) -> bool { self.wf() }

    pub fn new(blocks: u32) -> (r: Option<Self>)
        ensures match r {
            Some(c) => 2 < blocks <= MAX_BLOCKS && c.wf() && c.view().roles.len() == blocks
                && c.view().claims.len() == 0 && (forall|i: int| 0 <= i < blocks ==> #[trigger] c.view().roles[i] == free_slot()),
            None => blocks <= 2 || blocks > MAX_BLOCKS,
        },
    {
        if blocks <= 2 || blocks > MAX_BLOCKS { return None; }
        let mut roles = Vec::new();
        let mut index = 0u32;
        assert(lookup(Seq::empty(), 0) == free_slot()) by { reveal(lookup); }
        while index < blocks
            invariant roles.len() == index, index <= blocks <= MAX_BLOCKS, blocks > 2,
                forall|b: int| 0 <= b < index ==> #[trigger] roles@[b] == free_slot(),
            decreases blocks - index,
        {
            roles.push(Slot { kind: 0, inode: 0, generation: 0, logical: 0, initialized: false });
            index += 1;
        }
        assert(ledger(roles@, Seq::empty())) by {
            reveal(ledger);
            assert forall|b: int| 0 <= b < roles.len() implies #[trigger] roles@[b] == lookup(Seq::empty(), b) by {
                reveal(lookup);
            }
        }
        Some(Census { roles, claims: Ghost(Seq::empty()) })
    }

    pub fn role_of(&self, block: u32) -> (r: Option<Slot>)
        ensures self.wf(), match r {
            Some(role) => block < self.view().roles.len() && role == self.view().roles[block as int],
            None => block >= self.view().roles.len(),
        },
    {
        proof { use_type_invariant(self); }
        if block as usize >= self.roles.len() { None } else { Some(self.roles[block as usize]) }
    }

    pub fn block_count(&self) -> (r: u32)
        ensures self.wf(), r as nat == self.view().roles.len(), 2 < r <= MAX_BLOCKS,
    {
        proof { use_type_invariant(self); reveal(ledger); }
        self.roles.len() as u32
    }

    pub fn matches_bitmap(&self, first: u32, bitmap: &bitmap::Bitmap) -> (r: bool)
        ensures self.wf(), r == bitmap_matches(self.view().roles, first, bitmap.view()),
    {
        proof { use_type_invariant(self); }
        let count = bitmap.entry_count();
        if first as u64 + count as u64 > self.roles.len() as u64 {
            proof { reveal(bitmap_matches); } return false;
        }
        assert(self.roles.len() <= MAX_BLOCKS) by { reveal(ledger); }
        let mut index = 0u32;
        while index < count
            invariant self.wf(), index <= count, count == bitmap.view().valid,
                first as nat + count <= self.roles.len(), self.roles.len() <= MAX_BLOCKS,
                forall|i: int| 0 <= i < index ==> #[trigger] bitmap::set(bitmap.view().raw, i)
                    == (self.view().roles[first as int + i].kind != 0),
            decreases count - index,
        {
            let allocated = bitmap.is_set(index).unwrap();
            if allocated != (self.roles[(first + index) as usize].kind != 0) {
                proof {
                    reveal(bitmap_matches);
                    if bitmap_matches(self.view().roles, first, bitmap.view()) {
                        assert(bitmap::set(bitmap.view().raw, index as int)
                            == (self.view().roles[first as int + index as int].kind != 0));
                    }
                }
                return false;
            }
            index += 1;
        }
        proof { reveal(bitmap_matches); }
        true
    }

    pub fn claim(self, c: Claim) -> (r: Result<Self, Self>)
        ensures match r {
            Ok(next) => next.wf() && valid_claim(c, self.view().roles.len())
                && preserves_occupied(self.view().roles, next.view().roles)
                && next.view().roles.len() == self.view().roles.len() && next.view().claims == self.view().claims.push(c)
                && (forall|b: int| 0 <= b < self.view().roles.len() ==> #[trigger] next.view().roles[b]
                    == if covers(c, b) { at(c, b) } else { self.view().roles[b] }),
            Err(original) => original.view() == self.view() && (!valid_claim(c, self.view().roles.len())
                || exists|b: int| covers(c, b) && (#[trigger] self.view().roles[b]).kind != 0),
        },
    {
        proof { use_type_invariant(&self); }
        assert(self.view().roles.len() <= MAX_BLOCKS) by { reveal(ledger); }
        if !check_claim(&c, self.roles.len()) { return Err(self); }
        let end = c.start + c.length;
        let mut block = c.start;
        while block < end
            invariant self.wf(), valid_claim(c, self.view().roles.len()),
                c.start <= block <= end, end as nat == c.start as nat + c.length,
                self.view().roles.len() <= MAX_BLOCKS,
                forall|b: int| c.start <= b < block ==> (#[trigger] self.view().roles[b]).kind == 0,
            decreases end - block,
        {
            if self.roles[block as usize].kind != 0 {
                assert(exists|b: int| covers(c, b) && (#[trigger] self.view().roles[b]).kind != 0);
                return Err(self);
            }
            block += 1;
        }
        let ghost previous = self.view();
        proof { an_entirely_free_range_is_disjoint(previous.roles, previous.claims, c); }
        let Census { mut roles, claims } = self;
        let ghost next_claims = claims@.push(c);
        block = c.start;
        while block < end
            invariant c.start <= block <= end, end as nat == c.start as nat + c.length,
                roles.len() == previous.roles.len(), ledger(previous.roles, previous.claims),
                valid_claim(c, roles.len() as nat), roles.len() <= MAX_BLOCKS,
                forall|b: int| covers(c, b) ==> (#[trigger] previous.roles[b]).kind == 0,
                forall|b: int| 0 <= b < roles.len() ==> (#[trigger] roles@[b])
                    == if c.start <= b < block { at(c, b) } else { previous.roles[b] },
            decreases end - block,
        {
            roles[block as usize] = slot_at(&c, block);
            block += 1;
        }
        assert(ledger(roles@, next_claims)) by {
            reveal(ledger);
            assert forall|b: int| 0 <= b < roles.len() implies #[trigger] roles@[b] == lookup(next_claims, b) by {
                reveal(lookup);
                assert(next_claims.drop_last() =~= previous.claims);
            }
        }
        assert(preserves_occupied(previous.roles, roles@)) by {
            reveal(preserves_occupied);
            assert forall|b: int| 0 <= b < roles.len() && (#[trigger] previous.roles[b]).kind != 0
                implies roles@[b] == previous.roles[b] by {
                assert(!covers(c, b));
            }
        }
        Ok(Census { roles, claims: Ghost(next_claims) })
    }
}

pub proof fn two_recorded_claims_cannot_own_the_same_physical_block(census: &Census, a: nat, b: nat, block: int)
    requires census.wf(), a < census.view().claims.len(), b < census.view().claims.len(),
        covers(census.view().claims[a as int], block), covers(census.view().claims[b as int], block),
    ensures a == b,
{
    reveal(ledger);
    if a < b { assert(disjoint(census.view().claims[a as int], census.view().claims[b as int])); }
    if b < a { assert(disjoint(census.view().claims[b as int], census.view().claims[a as int])); }
}

pub proof fn a_matching_bitmap_has_the_exact_census_free_count(roles: Seq<Slot>, first: u32, bitmap: bitmap::BitmapView)
    requires bitmap_matches(roles, first, bitmap),
    ensures free_roles(roles, first, bitmap.valid as nat) == bitmap.free as nat,
{
    reveal(bitmap_matches);
    matching_prefixes_have_equal_free_counts(roles, first, bitmap.raw, bitmap.valid as nat);
}

pub proof fn every_recorded_claim_is_allocated_in_a_matching_bitmap(census: &Census, first: u32,
    bitmap: bitmap::BitmapView, index: nat, block: int)
    requires census.wf(), bitmap_matches(census.view().roles, first, bitmap), index < census.view().claims.len(),
        covers(census.view().claims[index as int], block), first <= block < first as int + bitmap.valid,
    ensures bitmap::set(bitmap.raw, block - first as int),
{
    reveal(ledger);
    reveal(bitmap_matches);
    a_covering_claim_marks_an_occupied_slot(census.view().claims, census.view().roles.len(), block, index as int);
    assert(census.view().roles[block] == lookup(census.view().claims, block));
    assert(bitmap::set(bitmap.raw, block - first as int) == (census.view().roles[block].kind != 0));
}

pub proof fn a_recorded_claim_determines_its_exact_physical_slot(census: &Census, index: nat, block: int)
    requires census.wf(), index < census.view().claims.len(), covers(census.view().claims[index as int], block),
    ensures 0 <= block < census.view().roles.len(), census.view().roles[block] == at(census.view().claims[index as int], block),
{
    reveal(ledger);
    assert(valid_claim(census.view().claims[index as int], census.view().roles.len()));
    one_covering_claim_determines_lookup(census.view().claims, block, index as int);
}

pub proof fn a_ledger_claim_determines_its_exact_physical_slot(roles: Seq<Slot>, claims: Seq<Claim>, claim: Claim, block: int)
    requires ledger(roles, claims), claims.contains(claim), covers(claim, block),
    ensures 0 <= block < roles.len(), roles[block] == at(claim, block),
{
    reveal(ledger);
    let index = choose|i: int| 0 <= i < claims.len() && claims[i] == claim;
    assert(valid_claim(claims[index], roles.len()));
    one_covering_claim_determines_lookup(claims, block, index);
}

#[verifier::opaque]
pub open spec fn mapped_claims(roles: Seq<Slot>, claims: Seq<Claim>) -> bool {
    &&& forall|i: int| 0 <= i < claims.len() ==> #[trigger] valid_claim(claims[i], roles.len())
    &&& forall|i: int, b: int| 0 <= i < claims.len() && #[trigger] covers(claims[i], b) ==>
        0 <= b < roles.len() && roles[b] == at(claims[i], b)
}

pub proof fn occupied_preservation_keeps_mapped_claims(before: Seq<Slot>, after: Seq<Slot>, claims: Seq<Claim>)
    requires mapped_claims(before, claims), preserves_occupied(before, after),
    ensures mapped_claims(after, claims),
{
    reveal(mapped_claims);
    reveal(preserves_occupied);
    assert forall|i: int, b: int| 0 <= i < claims.len() && #[trigger] covers(claims[i], b) implies
        0 <= b < after.len() && after[b] == at(claims[i], b) by {
        assert(valid_claim(claims[i], before.len()));
        assert(before[b] == at(claims[i], b) && before[b].kind != 0);
    }
}

pub proof fn every_appended_claim_has_its_exact_physical_slots(census: &Census, prefix: Seq<Claim>, added: Seq<Claim>)
    requires census.wf(), census.view().claims == prefix + added,
    ensures mapped_claims(census.view().roles, added),
{
    reveal(mapped_claims);
    assert forall|i: int| 0 <= i < added.len() implies #[trigger] valid_claim(added[i], census.view().roles.len()) by {
        reveal(ledger);
        assert(census.view().claims[prefix.len() as int + i] == added[i]);
    }
    assert forall|i: int, b: int| 0 <= i < added.len() && #[trigger] covers(added[i], b) implies
        0 <= b < census.view().roles.len() && census.view().roles[b] == at(added[i], b) by {
        let index = prefix.len() as int + i;
        assert(census.view().claims[index] == added[i]);
        a_recorded_claim_determines_its_exact_physical_slot(census, index as nat, b);
    }
}

}
