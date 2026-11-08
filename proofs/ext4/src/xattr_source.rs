// SPDX-License-Identifier: MPL-2.0

//! Complete immutable xattr source and reference census. Each shared external
//! block is claimed once, its stored reference count equals all source inode
//! references, and no data, journal or extent-tree block can alias that claim.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{allocated_inode, block_claims::{self, Census, Claim, Slot}, bytes, group_index::{self, GroupIndex, IndexView},
    inode_table, xattr, xattr_table};

verus! {

pub open spec fn active(v: IndexView, n: u32) -> bool { n == 8 || allocated_inode::live(v, n) }
pub open spec fn enabled(v: IndexView) -> bool { bytes::le32(v.source, 1116) as u32 & 8 != 0 }
pub open spec fn pointer(v: IndexView, n: u32) -> nat {
    xattr::inode_address(inode_table::raw(v, n))
}
pub open spec fn block_bytes(v: IndexView, block: nat) -> Seq<u8> { v.source.subrange(block as int * 4096, (block as int + 1) * 4096) }

#[verifier::opaque]
pub open spec fn body_checked(v: IndexView, n: u32) -> bool {
    exists|body: xattr::BodyView| #[trigger] xattr::valid_body(body) && body.raw == inode_table::raw(v, n) && !body.ea && body.inodes == v.inodes
        && (xattr::body_present(body.raw) ==> enabled(v))
}

#[verifier::opaque]
pub open spec fn block_checked(v: IndexView, block: nat) -> bool {
    &&& 0 < block < v.blocks && enabled(v)
    &&& xattr::header(block_bytes(v, block), block as u64, v.seed, true)
    &&& exists|table: xattr_table::TableView| #[trigger] xattr_table::valid(table) && table.raw == block_bytes(v, block)
        && table.first == 32 && table.base == 0 && !table.ea && table.inodes == v.inodes && table.sorted
}

pub open spec fn references(v: IndexView, block: nat, count: nat) -> nat
    decreases count,
{
    if count == 0 { 0nat } else { references(v, block, (count - 1) as nat)
        + if active(v, count as u32) && pointer(v, count as u32) == block && block > 0 { 1nat } else { 0nat } }
}

pub open spec fn claim(block: u32) -> Claim {
    Claim { start: block, length: 1, kind: 7, inode: 0, generation: 0, logical: 0, initialized: false }
}

#[verifier::opaque]
pub open spec fn claims(v: IndexView, count: nat) -> Seq<Claim>
    decreases count,
{
    if count == 0 { Seq::empty() } else {
        let block = pointer(v, count as u32);
        let before = claims(v, (count - 1) as nat);
        if active(v, count as u32) && block > 0 && references(v, block, (count - 1) as nat) == 0 {
            before.push(claim(block as u32))
        } else { before }
    }
}

#[verifier::opaque]
pub open spec fn body_prefix(v: IndexView, count: nat) -> bool {
    forall|n: u32| 0 < n <= count && active(v, n) ==> #[trigger] body_checked(v, n)
        && (pointer(v, n) > 0 ==> pointer(v, n) < v.blocks) && keys_checked(v, n)
}

#[verifier::opaque]
pub open spec fn keys_checked(v: IndexView, n: u32) -> bool {
    exists|attributes: crate::xattr_inode::AttributesView| #[trigger] crate::xattr_inode::valid(attributes)
        && attributes.index == v && attributes.number == n
}

#[verifier::opaque]
pub open spec fn checked(v: IndexView, roles: Seq<Slot>) -> bool {
    &&& body_prefix(v, v.inodes as nat)
    &&& (forall|block: u32| 0 < block < v.blocks && references(v, block as nat, v.inodes as nat) > 0 ==>
        #[trigger] block_checked(v, block as nat) && roles[block as int].kind == 7
            && bytes::le32(block_bytes(v, block as nat), 4) == references(v, block as nat, v.inodes as nat))
}

proof fn extend_body_prefix(v: IndexView, n: u32)
    requires n > 0, body_prefix(v, (n - 1) as nat),
        active(v, n) ==> body_checked(v, n) && (pointer(v, n) > 0 ==> pointer(v, n) < v.blocks) && keys_checked(v, n),
    ensures body_prefix(v, n as nat),
{
    reveal(body_prefix);
    assert forall|i: u32| 0 < i <= n as nat && active(v, i) implies #[trigger] body_checked(v, i)
        && (pointer(v, i) > 0 ==> pointer(v, i) < v.blocks) && keys_checked(v, i) by {
        if i < n { assert(body_checked(v, i)); }
    }
}

pub fn inspect_body<'a>(index: &GroupIndex<'a>, n: u32) -> (r: Option<xattr::Body<'a>>)
    ensures index.wf(), match r { Some(body) => body.wf() && body.view().raw == inode_table::raw(index.view(), n)
        && !body.view().ea && body.view().inodes == index.view().inodes && body_checked(index.view(), n), None => true },
{
    let (_, inodes, _, _) = index.parameters();
    proof { reveal(group_index::valid); }
    let raw = match inode_table::read(index, n) { Some(raw) => raw, None => { return None; } };
    let body = match xattr::parse_body(raw, false, inodes) { Some(body) => body, None => { return None; } };
    let primary = index.source().block(0).unwrap();
    let marked = bytes::read_le32(primary.as_slice(), 1116).unwrap() & 8 != 0;
    assert(marked == enabled(index.view()));
    if body.present() && !marked { return None; }
    proof {
        assert(exists|b: xattr::BodyView| #[trigger] xattr::valid_body(b) && b.raw == raw@ && !b.ea && b.inodes == inodes
            && (xattr::body_present(b.raw) ==> enabled(index.view()))) by {
            assert(xattr::valid_body(body.view()));
        }
        reveal(body_checked);
    }
    Some(body)
}

pub fn inspect_block<'a>(index: &GroupIndex<'a>, block: u64) -> (r: Option<xattr::Block<'a>>)
    ensures index.wf(), match r { Some(value) => value.wf() && value.address() == block
        && value.view().raw == block_bytes(index.view(), block as nat) && !value.view().ea && value.view().inodes == index.view().inodes
        && block_checked(index.view(), block as nat), None => true },
{
    let (blocks, inodes, _, seed) = index.parameters();
    proof { reveal(group_index::valid); }
    if block == 0 || block >= blocks as u64 { return None; }
    let primary = index.source().block(0).unwrap();
    if bytes::read_le32(primary.as_slice(), 1116).unwrap() & 8 == 0 { return None; }
    let raw = index.source().block(block as u32).unwrap();
    let value = match xattr::parse_block(raw.as_slice(), block, seed, true, false, inodes) { Some(value) => value, None => { return None; } };
    assert(block_checked(index.view(), block as nat)) by { reveal(block_checked); assert(xattr_table::valid(value.view())); }
    Some(value)
}

pub proof fn every_referenced_external_block_has_one_canonical_claim(v: IndexView, block: u32, count: nat)
    requires references(v, block as nat, count) > 0, block > 0, count <= v.inodes,
    ensures claims(v, count).contains(claim(block)),
    decreases count,
{
    reveal(claims);
    if references(v, block as nat, (count - 1) as nat) > 0 {
        every_referenced_external_block_has_one_canonical_claim(v, block, (count - 1) as nat);
        let before = claims(v, (count - 1) as nat);
        let new_block = pointer(v, count as u32);
        if active(v, count as u32) && new_block > 0 && references(v, new_block, (count - 1) as nat) == 0 {
            vstd::seq_lib::lemma_seq_contains_after_push(before, claim(new_block as u32), claim(block));
        }
    } else {
        assert(active(v, count as u32) && pointer(v, count as u32) == block);
        assert(claims(v, count).last() == claim(block));
        vstd::seq_lib::lemma_seq_contains_after_push(claims(v, (count - 1) as nat), claim(block), claim(block));
    }
}

fn source_active(index: &GroupIndex<'_>, n: u32) -> (r: bool)
    ensures index.wf(), r == active(index.view(), n),
{
    let (_, inodes, ipg, _) = index.parameters();
    if n == 8 { return true; }
    if n == 0 || n > inodes || n != 2 && n < 11 { return false; }
    proof {
        reveal(group_index::valid);
        vstd::arithmetic::mul::lemma_mul_is_commutative(ipg as int, index.view().groups.len() as int);
        vstd::arithmetic::div_mod::lemma_multiply_divide_lt(n as int - 1, ipg as int, index.view().groups.len() as int);
    }
    let group = index.get((n - 1) / ipg).unwrap();
    let (_, bitmap) = group.bitmaps();
    proof { reveal(group_index::records_match); reveal(crate::group_metadata::valid); }
    bitmap.is_set((n - 1) % ipg).unwrap()
}

fn zeros(blocks: u32) -> (r: Vec<u32>)
    requires blocks <= block_claims::MAX_BLOCKS,
    ensures r.len() == blocks, forall|b: int| 0 <= b < blocks ==> #[trigger] r@[b] == 0,
{
    let mut counts = Vec::new();
    let mut b = 0u32;
    while b < blocks
        invariant counts.len() == b <= blocks <= block_claims::MAX_BLOCKS,
            forall|i: int| 0 <= i < b ==> #[trigger] counts@[i] == 0,
        decreases blocks - b,
    { counts.push(0u32); b += 1; }
    counts
}

pub fn audit(census: Census, index: &GroupIndex<'_>) -> (r: Option<Census>)
    ensures index.wf(), match r { Some(next) => next.wf() && next.view().roles.len() == index.view().blocks
        && next.view().claims == census.view().claims + claims(index.view(), index.view().inodes as nat)
        && block_claims::preserves_occupied(census.view().roles, next.view().roles)
        && checked(index.view(), next.view().roles), None => true },
{
    let (blocks, inodes, _, _) = index.parameters();
    if census.block_count() != blocks || inodes > block_claims::MAX_BLOCKS { return None; }
    let mut counts = zeros(blocks);
    let ghost initial = census.view();
    let mut current = census;
    let mut n = 1u32;
    assert(body_prefix(index.view(), 0)) by { reveal(body_prefix); }
    assert(claims(index.view(), 0) == Seq::<Claim>::empty()) by { reveal(claims); }
    assert(block_claims::preserves_occupied(initial.roles, current.view().roles)) by { reveal(block_claims::preserves_occupied); }
    while n <= inodes
        invariant index.wf(), index.view().blocks == blocks <= block_claims::MAX_BLOCKS, index.view().inodes == inodes <= block_claims::MAX_BLOCKS,
            1 <= n <= inodes + 1, counts.len() == blocks,
            current.wf(), current.view().roles.len() == blocks,
            current.view().claims == initial.claims + claims(index.view(), (n - 1) as nat),
            body_prefix(index.view(), (n - 1) as nat), block_claims::preserves_occupied(initial.roles, current.view().roles),
            (forall|b: u32| b < blocks ==> #[trigger] counts@[b as int] as nat == references(index.view(), b as nat, (n - 1) as nat) && counts@[b as int] <= xattr::MAX_REFS),
            (forall|b: u32| b < blocks && counts@[b as int] > 0 ==> #[trigger] block_checked(index.view(), b as nat)),
        decreases inodes - n + 1,
    {
        let ghost old_counts = counts@;
        let ghost before = current.view();
        let mut target = 0u32;
        let is_active = if n == 8 { true } else { source_active(index, n) };
        if is_active {
            let attributes = match crate::xattr_inode::inspect(index, n) { Some(attributes) => attributes, None => { return None; } };
            assert(keys_checked(index.view(), n)) by { reveal(keys_checked); assert(crate::xattr_inode::valid(attributes.view())); }
            let raw = inode_table::read(index, n).unwrap();
            let pointer = bytes::read_le32(raw, 104).unwrap() as u64 + bytes::read_le16(raw, 118).unwrap() as u64 * 4294967296;
            if pointer != 0 {
                if pointer >= blocks as u64 { return None; }
                target = pointer as u32;
                if counts[target as usize] == xattr::MAX_REFS { return None; }
                if counts[target as usize] == 0 {
                    let _block = match inspect_block(index, pointer) { Some(block) => block, None => { return None; } };
                    let owned = Claim { start: target, length: 1, kind: 7, inode: 0, generation: 0, logical: 0, initialized: false };
                    current = match current.claim(owned) { Ok(next) => next, Err(_) => { return None; } };
                }
                counts.set(target as usize, counts[target as usize] + 1);
            }
        }
        proof {
            assert(block_claims::preserves_occupied(before.roles, current.view().roles)) by { reveal(block_claims::preserves_occupied); }
            block_claims::occupied_slot_preservation_is_transitive(initial.roles, before.roles, current.view().roles);
            reveal(claims);
            assert forall|b: u32| b < blocks implies #[trigger] counts@[b as int] as nat == references(index.view(), b as nat, n as nat) && counts@[b as int] <= xattr::MAX_REFS by {
                if b != target || target == 0 { assert(counts@[b as int] == old_counts[b as int]); }
            }
            assert forall|b: u32| b < blocks && counts@[b as int] > 0 implies #[trigger] block_checked(index.view(), b as nat) by {
                if b != target || target == 0 { assert(old_counts[b as int] > 0); }
            }
            extend_body_prefix(index.view(), n);
        }
        n += 1;
    }
    let mut block = 0u32;
    while block < blocks
        invariant index.wf(), counts.len() == blocks == index.view().blocks,
            current.wf(), current.view().roles.len() == blocks,
            current.view().claims == initial.claims + claims(index.view(), index.view().inodes as nat),
            body_prefix(index.view(), index.view().inodes as nat), block <= blocks,
            block_claims::preserves_occupied(initial.roles, current.view().roles),
            (forall|b: u32| b < blocks ==> #[trigger] counts@[b as int] as nat == references(index.view(), b as nat, index.view().inodes as nat)),
            (forall|b: u32| b < blocks && counts@[b as int] > 0 ==> #[trigger] block_checked(index.view(), b as nat)),
            (forall|b: u32| b < block && counts@[b as int] > 0 ==> #[trigger] bytes::le32(block_bytes(index.view(), b as nat), 4) == counts@[b as int]),
        decreases blocks - block,
    {
        if counts[block as usize] > 0 {
            proof { reveal(group_index::valid); }
            let raw = index.source().block(block).unwrap();
            assert(raw.bytes() == block_bytes(index.view(), block as nat));
            if bytes::read_le32(raw.as_slice(), 4).unwrap() != counts[block as usize] { return None; }
        }
        proof {
            assert forall|b: u32| b < block + 1 && counts@[b as int] > 0 implies #[trigger] bytes::le32(block_bytes(index.view(), b as nat), 4) == counts@[b as int] by {
                if b < block { assert(bytes::le32(block_bytes(index.view(), b as nat), 4) == counts@[b as int]); }
            }
        }
        block += 1;
    }
    proof {
        block_claims::every_appended_claim_has_its_exact_physical_slots(&current, initial.claims, claims(index.view(), index.view().inodes as nat));
        assert forall|b: u32| 0 < b < blocks && references(index.view(), b as nat, index.view().inodes as nat) > 0 implies
            #[trigger] block_checked(index.view(), b as nat) && current.view().roles[b as int].kind == 7
                && bytes::le32(block_bytes(index.view(), b as nat), 4) == references(index.view(), b as nat, index.view().inodes as nat) by {
            every_referenced_external_block_has_one_canonical_claim(index.view(), b, index.view().inodes as nat);
            let owned = claims(index.view(), index.view().inodes as nat);
            let k = choose|k: int| 0 <= k < owned.len() && owned[k] == claim(b);
            reveal(block_claims::mapped_claims);
            assert(block_claims::covers(owned[k], b as int));
            assert(current.view().roles[b as int] == block_claims::at(claim(b), b as int));
        }
        assert(checked(index.view(), current.view().roles)) by { reveal(checked); }
    }
    Some(current)
}

}
