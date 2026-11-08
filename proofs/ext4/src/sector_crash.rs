// SPDX-License-Identifier: MPL-2.0

//! Candidate single-request crash model with mathematical 512-byte pieces.
//!
//! These owned RAM values confer no device, source, allocation, DMA, completion,
//! fence or reset authority. Physical interpretation of an indivisible piece
//! requires an additional audited atomic-512 environment contract; 512-byte
//! accounting alone supplies no such premise. Finer tears remain outside this
//! deliberately bounded candidate model.
//!
//! One immutable issued image remains present after software completion. There
//! is no request reuse/reset or physical receipt factory here. Fresh physical
//! request identities and reset quiescence require a later owner refinement.
//! The old atomic-4096 media model is unchanged; its single-write embedding
//! below explicitly requires the stronger whole-image cut premise.

use vstd::{assert_maps_equal, prelude::*};
use crate::block_size;

verus! {

pub const PIECE_BYTES: usize = 512;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RequestId {
    pub namespace: u64,
    pub epoch: u64,
    pub serial: u64,
    pub target: u64,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error { Identity, AlreadyCompleted, Piece }

pub fn same_request(a: RequestId, b: RequestId) -> (r: bool)
    ensures r == (a == b),
{
    a.namespace == b.namespace && a.epoch == b.epoch
        && a.serial == b.serial && a.target == b.target
}

pub open spec fn piece_mask(bytes: nat, piece: int) -> Seq<bool> {
    Seq::new(bytes / 512, |i: int| i == piece)
}
pub open spec fn cut(base: Seq<u8>, issued: Seq<u8>, retained: Seq<bool>) -> Seq<u8> {
    Seq::new(base.len(), |i: int| if retained[i / 512] { issued[i] } else { base[i] })
}
pub open spec fn all_mask(bytes: nat, value: bool) -> Seq<bool> {
    Seq::new(bytes / 512, |i: int| value)
}
pub open spec fn whole_image_cut(retained: Seq<bool>) -> bool {
    (forall|i: int| #![trigger retained[i]] 0 <= i < retained.len() ==> retained[i])
        || (forall|i: int| #![trigger retained[i]] 0 <= i < retained.len() ==> !retained[i])
}

pub struct StateView {
    pub base: Seq<u8>,
    pub issued: Seq<u8>,
    pub stable: Seq<u8>,
    pub stable_pieces: Seq<bool>,
    pub identity: RequestId,
    pub completed: bool,
}
pub open spec fn valid_state(v: StateView) -> bool {
    &&& block_size::accepted(v.base.len())
    &&& v.issued.len() == v.base.len()
    &&& v.stable_pieces.len() == v.base.len() / 512
    &&& v.stable == cut(v.base, v.issued, v.stable_pieces)
}
pub open spec fn initial(base: Seq<u8>, issued: Seq<u8>, identity: RequestId) -> StateView {
    StateView { base, issued, stable: base, stable_pieces: all_mask(base.len(), false),
        identity, completed: false }
}
pub open spec fn completion(v: StateView) -> StateView {
    StateView { base: v.base, issued: v.issued, stable: v.stable,
        stable_pieces: v.stable_pieces, identity: v.identity, completed: true }
}
pub open spec fn installed(v: StateView, piece: int) -> StateView {
    let mask = v.stable_pieces.update(piece, true);
    StateView { base: v.base, issued: v.issued, stable: cut(v.base, v.issued, mask),
        stable_pieces: mask, identity: v.identity, completed: v.completed }
}
pub open spec fn admits_cut(v: StateView, retained: Seq<bool>) -> bool {
    retained.len() == v.stable_pieces.len()
        && forall|i: int| 0 <= i < retained.len() && #[trigger] v.stable_pieces[i] ==> retained[i]
}
pub open spec fn completion_event(before: StateView, report: RequestId, after: StateView) -> bool {
    before.identity == report && !before.completed && after == completion(before)
}
pub open spec fn stable_piece_event(before: StateView, report: RequestId,
    piece: nat, after: StateView) -> bool
{
    before.identity == report && piece < before.stable_pieces.len()
        && after == installed(before, piece as int)
}

// This is an explicit relation assumed of two model states, not a receipt or
// an executable operation. It describes the drain guarantee for THIS request,
// within its exact namespace/epoch, at a supplied serial cutoff. It makes no
// statement about other outstanding requests or physical implementations.
pub open spec fn abstract_fence_contract(before: StateView, report: RequestId,
    cutoff: u64, after: StateView) -> bool
{
    &&& report == before.identity && report.serial <= cutoff
    &&& after.base == before.base && after.issued == before.issued
    &&& after.identity == before.identity && after.completed == before.completed
    &&& after.stable_pieces == all_mask(before.base.len(), true)
    &&& after.stable == cut(before.base, before.issued, after.stable_pieces)
}

proof fn geometry_pieces(length: nat)
    requires block_size::accepted(length),
    ensures 2 <= length / 512 <= 128, length % 512 == 0,
        length / 512 * 512 == length, 1024 <= length <= 65536,
{
}
proof fn byte_piece_bounds(length: nat, index: int)
    requires block_size::accepted(length), 0 <= index < length,
    ensures 0 <= index / 512 < length / 512,
{
    geometry_pieces(length);
}
proof fn byte_in_piece(index: int, piece: int)
    requires index >= 0, piece >= 0,
    ensures (index / 512 == piece) <==> (piece * 512 <= index < piece * 512 + 512),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(index, 512);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(index, 512);
}
proof fn initial_is_valid(base: Seq<u8>, issued: Seq<u8>, identity: RequestId)
    requires block_size::accepted(base.len()), issued.len() == base.len(),
    ensures valid_state(initial(base, issued, identity)),
{
    geometry_pieces(base.len());
    assert(cut(base, issued, all_mask(base.len(), false)) =~= base);
}
proof fn installed_is_valid(v: StateView, piece: int)
    requires valid_state(v), 0 <= piece < v.stable_pieces.len(),
    ensures valid_state(installed(v, piece)),
{
}
pub proof fn stable_piece_preserves_every_outside_byte(before: StateView, report: RequestId,
    piece: nat, after: StateView, index: int)
    requires valid_state(before), stable_piece_event(before, report, piece, after),
        0 <= index < before.base.len(),
        index < piece * 512 || index >= piece * 512 + 512,
    ensures valid_state(after), after.stable[index] == before.stable[index],
{
    installed_is_valid(before, piece as int);
    byte_piece_bounds(before.base.len(), index);
    byte_in_piece(index, piece as int);
}
pub proof fn stable_piece_uses_only_the_exact_issued_bytes(before: StateView, report: RequestId,
    piece: nat, after: StateView, index: int)
    requires valid_state(before), stable_piece_event(before, report, piece, after),
        piece * 512 <= index < piece * 512 + 512,
    ensures 0 <= index < before.issued.len(), after.stable[index] == before.issued[index],
        after.identity == before.identity && after.issued == before.issued,
{
    geometry_pieces(before.base.len());
    byte_in_piece(index, piece as int);
}
pub proof fn stale_or_redirected_reports_enable_neither_transition(before: StateView,
    report: RequestId, after: StateView, piece: nat)
    requires report != before.identity,
    ensures !completion_event(before, report, after),
        !stable_piece_event(before, report, piece, after),
{
}
pub proof fn software_completion_changes_no_stable_byte(before: StateView,
    report: RequestId, after: StateView)
    requires valid_state(before), completion_event(before, report, after),
    ensures valid_state(after), after.stable == before.stable,
        after.stable_pieces == before.stable_pieces,
        after.issued == before.issued && after.identity == before.identity,
{
}
pub proof fn an_already_completed_report_cannot_be_consumed_twice(before: StateView,
    report: RequestId, after: StateView)
    requires before.completed,
    ensures !completion_event(before, report, after),
{
}
pub proof fn an_admitted_cut_retains_every_known_stable_byte(v: StateView,
    retained: Seq<bool>, index: int)
    requires valid_state(v), admits_cut(v, retained), 0 <= index < v.base.len(),
        v.stable_pieces[index / 512],
    ensures cut(v.base, v.issued, retained)[index] == v.stable[index],
        cut(v.base, v.issued, retained)[index] == v.issued[index],
{
    byte_piece_bounds(v.base.len(), index);
    assert(retained[index / 512]);
}

pub proof fn completed_write_can_still_have_no_new_stable_piece(base: Seq<u8>,
    issued: Seq<u8>, identity: RequestId)
    requires block_size::accepted(base.len()), issued.len() == base.len(), issued != base,
    ensures valid_state(completion(initial(base, issued, identity))),
        completion(initial(base, issued, identity)).completed,
        completion(initial(base, issued, identity)).stable == base,
        completion(initial(base, issued, identity)).stable != issued,
        completion_event(initial(base, issued, identity), identity,
            completion(initial(base, issued, identity))),
{
    initial_is_valid(base, issued, identity);
}
pub proof fn every_initial_piece_subset_is_an_admitted_candidate_cut(base: Seq<u8>,
    issued: Seq<u8>, identity: RequestId, retained: Seq<bool>)
    requires block_size::accepted(base.len()), issued.len() == base.len(),
        retained.len() == base.len() / 512,
    ensures valid_state(initial(base, issued, identity)),
        admits_cut(initial(base, issued, identity), retained),
{
    initial_is_valid(base, issued, identity);
}
pub proof fn matching_conditional_fence_has_exact_issued_stable_bytes(before: StateView,
    report: RequestId, cutoff: u64, after: StateView)
    requires valid_state(before), abstract_fence_contract(before, report, cutoff, after),
    ensures valid_state(after), after.stable == before.issued,
        after.identity == report && after.identity.serial <= cutoff,
        after.completed == before.completed,
{
    assert(after.stable =~= before.issued) by {
        assert forall|i: int| 0 <= i < before.issued.len() implies
            #[trigger] after.stable[i] == before.issued[i] by {
            byte_piece_bounds(before.base.len(), i);
        }
    }
}

pub proof fn two_changed_distinct_sectors_admit_a_mixed_cut(base: Seq<u8>, issued: Seq<u8>,
    left: int, right: int)
    requires block_size::accepted(base.len()), issued.len() == base.len(),
        0 <= left < base.len(), 0 <= right < base.len(), left / 512 != right / 512,
        base[left] != issued[left], base[right] != issued[right],
    ensures cut(base, issued, piece_mask(base.len(), left / 512)) != base,
        cut(base, issued, piece_mask(base.len(), left / 512)) != issued,
        cut(base, issued, piece_mask(base.len(), left / 512))[left] == issued[left],
        cut(base, issued, piece_mask(base.len(), left / 512))[right] == base[right],
{
    byte_piece_bounds(base.len(), left);
    byte_piece_bounds(base.len(), right);
    assert(piece_mask(base.len(), left / 512)[left / 512]);
    assert(!piece_mask(base.len(), left / 512)[right / 512]);
}

// The offsets illustrate separate locations used by the existing super_state
// edits. BOTH byte differences are explicit premises. This theorem does not
// calculate a CRC, prove CRC noncollision, claim every torn checksum invalid,
// or diagnose Linux or a mounted filesystem.
pub proof fn separate_1120_and_2044_locations_have_a_mixed_byte_cut(base: Seq<u8>, issued: Seq<u8>)
    requires base.len() == 4096, issued.len() == 4096,
        base[1120] != issued[1120], base[2044] != issued[2044],
    ensures cut(base, issued, piece_mask(4096, 2)) != base,
        cut(base, issued, piece_mask(4096, 2)) != issued,
        cut(base, issued, piece_mask(4096, 2))[1120] == issued[1120],
        cut(base, issued, piece_mask(4096, 2))[2044] == base[2044],
{
    two_changed_distinct_sectors_admit_a_mixed_cut(base, issued, 1120, 2044);
}

pub proof fn whole_image_premise_restricts_4096_cut_to_the_old_choice(base: Seq<u8>,
    issued: Seq<u8>, retained: Seq<bool>)
    requires base.len() == 4096, issued.len() == 4096, retained.len() == 8,
        whole_image_cut(retained),
    ensures cut(base, issued, retained) == if retained[0] { issued } else { base },
{
    assert forall|i: int| 0 <= i < base.len() implies
        #[trigger] cut(base, issued, retained)[i] == if retained[0] { issued[i] } else { base[i] } by {
        byte_piece_bounds(base.len(), i);
    }
    assert(cut(base, issued, retained) =~= if retained[0] { issued } else { base });
}

// Exact single-write embedding into the UNCHANGED old write_media::apply.
// This requires whole_image_cut as an additional premise. It is not an
// embedding of arbitrary 512-piece cuts or the entire writer/recovery protocol.
pub proof fn whole_image_4096_cut_embeds_one_existing_atomic_media_event(
    disk: crate::replay_refinement::Disk, images: crate::write_io::Images,
    earlier: Set<nat>, event: nat, retained: Seq<bool>)
    requires crate::write_device::is_write(event, images.tx.payloads.len()),
        !earlier.contains(event), retained.len() == 8, whole_image_cut(retained),
        crate::write_media::apply(disk, images, earlier, event).dom().contains(
            crate::write_media::address(images, event)),
        crate::write_media::apply(disk, images, earlier, event)[
            crate::write_media::address(images, event)].len() == 4096,
        crate::write_media::image(images, event).len() == 4096,
    ensures {
        let before = crate::write_media::apply(disk, images, earlier, event);
        let target = crate::write_media::address(images, event);
        let image = cut(before[target], crate::write_media::image(images, event), retained);
        before.insert(target, image) == crate::write_media::apply(disk, images,
            if retained[0] { earlier.insert(event) } else { earlier }, event + 1)
    },
{
    let before = crate::write_media::apply(disk, images, earlier, event);
    let target = crate::write_media::address(images, event);
    whole_image_premise_restricts_4096_cut_to_the_old_choice(before[target],
        crate::write_media::image(images, event), retained);
    if retained[0] {
        crate::write_media::adding_a_later_token_cannot_change_an_earlier_prefix(
            disk, images, earlier, event, event);
    } else {
        assert_maps_equal!(before.insert(target, before[target]), before, key => {});
    }
}

fn copy_bytes(raw: &[u8]) -> (r: Vec<u8>)
    ensures r@ == raw@,
{
    let mut out = Vec::<u8>::new(); let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len(), out@ == raw@.take(i as int),
        decreases raw.len() - i,
    { out.push(raw[i]); i += 1; }
    out
}

pub struct SectorCrash {
    base: Vec<u8>,
    issued: Vec<u8>,
    stable: Vec<u8>,
    stable_pieces: Vec<bool>,
    identity: RequestId,
    completed: bool,
}
impl SectorCrash {
    pub closed spec fn view(&self) -> StateView {
        StateView { base: self.base@, issued: self.issued@, stable: self.stable@,
            stable_pieces: self.stable_pieces@, identity: self.identity, completed: self.completed }
    }
    pub open spec fn wf(&self) -> bool { valid_state(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn candidate(base: &[u8], issued: &[u8], identity: RequestId) -> (r: Option<Self>)
        ensures match r {
            Some(owner) => owner.wf() && owner.view() == initial(base@, issued@, identity),
            None => !block_size::accepted(base.len() as nat) || issued.len() != base.len(),
        },
    {
        if !block_size::valid(base.len()) || issued.len() != base.len() { return None; }
        proof { geometry_pieces(base.len() as nat); }
        let mut mask = Vec::new(); let mut i = 0usize;
        while i < base.len() / PIECE_BYTES
            invariant i <= base.len() / PIECE_BYTES, mask.len() == i,
                mask@ == Seq::<bool>::new(i as nat, |j: int| false),
            decreases base.len() / PIECE_BYTES - i,
        { mask.push(false); i += 1; }
        proof { initial_is_valid(base@, issued@, identity); }
        Some(Self { base: copy_bytes(base), issued: copy_bytes(issued), stable: copy_bytes(base),
            stable_pieces: mask, identity, completed: false })
    }

    /// Records only a matching software report. Issued bytes and stable pieces
    /// remain owned and unchanged. Duplicate or mismatching reports reject.
    pub fn record_completion(self, report: RequestId) -> (r: Result<Self, (Self, Error)>)
        ensures self.wf(),
            r.is_ok() <==> (report == self.view().identity && !self.view().completed),
            match r {
                Ok(next) => next.wf() && completion_event(self.view(), report, next.view()),
                Err((owner, error)) => owner.wf() && owner.view() == self.view()
                    && match error {
                        Error::Identity => report != self.view().identity,
                        Error::AlreadyCompleted => report == self.view().identity && self.view().completed,
                        Error::Piece => false,
                    },
            },
    {
        proof { use_type_invariant(&self); }
        if !same_request(self.identity, report) { return Err((self, Error::Identity)); }
        if self.completed { return Err((self, Error::AlreadyCompleted)); }
        let Self { base, issued, stable, stable_pieces, identity, completed: _ } = self;
        Ok(Self { base, issued, stable, stable_pieces, identity, completed: true })
    }

    /// A mathematical environment event, not physical persistence evidence.
    /// The caller supplies an index but cannot substitute any byte payload.
    /// Repeating a stable piece is idempotent. Software completion does not
    /// disable this event; the immutable issued image is still retained.
    pub fn record_stable_piece(self, report: RequestId, piece: usize) -> (r: Result<Self, (Self, Error)>)
        ensures self.wf(),
            r.is_ok() <==> (report == self.view().identity && piece < self.view().stable_pieces.len()),
            match r {
                Ok(next) => next.wf() && stable_piece_event(self.view(), report, piece as nat, next.view()),
                Err((owner, error)) => owner.wf() && owner.view() == self.view()
                    && match error {
                        Error::Identity => report != self.view().identity,
                        Error::Piece => report == self.view().identity && piece >= self.view().stable_pieces.len(),
                        Error::AlreadyCompleted => false,
                    },
            },
    {
        proof { use_type_invariant(&self); geometry_pieces(self.view().base.len()); }
        if !same_request(self.identity, report) { return Err((self, Error::Identity)); }
        if piece >= self.stable_pieces.len() { return Err((self, Error::Piece)); }
        let ghost before = self.view();
        let Self { base, issued, mut stable, mut stable_pieces, identity, completed } = self;
        let start = piece * PIECE_BYTES; let end = start + PIECE_BYTES;
        let mut i = start;
        while i < end
            invariant start == piece * 512, end == start + 512, start <= i <= end <= stable.len(),
                base@ == before.base, issued@ == before.issued,
                identity == before.identity, completed == before.completed,
                stable.len() == before.base.len(), stable_pieces@ == before.stable_pieces,
                valid_state(before), piece < before.stable_pieces.len(),
                forall|j: int| 0 <= j < stable.len() ==> #[trigger] stable@[j]
                    == if start <= j < i { issued@[j] } else { before.stable[j] },
            decreases end - i,
        { stable[i] = issued[i]; i += 1; }
        stable_pieces.set(piece, true);
        proof {
            assert(stable@ =~= cut(before.base, before.issued, before.stable_pieces.update(piece as int, true))) by {
                assert forall|j: int| 0 <= j < stable.len() implies #[trigger] stable@[j]
                    == cut(before.base, before.issued, before.stable_pieces.update(piece as int, true))[j] by {
                    byte_piece_bounds(before.base.len(), j); byte_in_piece(j, piece as int);
                }
            }
            installed_is_valid(before, piece as int);
        }
        Ok(Self { base, issued, stable, stable_pieces, identity, completed })
    }

    /// Captures one modeled crash image. Already stable pieces cannot be lost;
    /// any other issued pieces may independently survive in this candidate cut.
    pub fn candidate_cut(&self, retained: &[bool]) -> (r: Option<Vec<u8>>)
        ensures self.wf(), match r {
            Some(raw) => admits_cut(self.view(), retained@)
                && raw@ == cut(self.view().base, self.view().issued, retained@),
            None => !admits_cut(self.view(), retained@),
        },
    {
        proof { use_type_invariant(self); geometry_pieces(self.view().base.len()); }
        if retained.len() != self.stable_pieces.len() { return None; }
        let mut i = 0usize;
        while i < retained.len()
            invariant self.wf(), i <= retained.len(), retained.len() == self.stable_pieces.len(),
                forall|j: int| 0 <= j < i && #[trigger] self.stable_pieces@[j] ==> retained@[j],
            decreases retained.len() - i,
        {
            if self.stable_pieces[i] && !retained[i] { return None; }
            i += 1;
        }
        let mut out = Vec::new(); i = 0;
        while i < self.base.len()
            invariant i <= self.base.len(), out.len() == i,
                retained.len() == self.stable_pieces.len(), self.wf(),
                admits_cut(self.view(), retained@),
                out@ == cut(self.base@, self.issued@, retained@).take(i as int),
            decreases self.base.len() - i,
        {
            proof { byte_piece_bounds(self.base.len() as nat, i as int); }
            out.push(if retained[i / PIECE_BYTES] { self.issued[i] } else { self.base[i] });
            i += 1;
        }
        Some(out)
    }

    pub fn stable_bytes(&self) -> (r: &[u8])
        ensures self.wf(), r@ == self.view().stable,
    { proof { use_type_invariant(self); } &self.stable }
    pub fn issued_bytes(&self) -> (r: &[u8])
        ensures self.wf(), r@ == self.view().issued,
    { proof { use_type_invariant(self); } &self.issued }
    pub fn stable_piece_flags(&self) -> (r: &[bool])
        ensures self.wf(), r@ == self.view().stable_pieces,
    { proof { use_type_invariant(self); } &self.stable_pieces }
    pub fn request_identity(&self) -> (r: RequestId)
        ensures self.wf(), r == self.view().identity,
    { proof { use_type_invariant(self); } self.identity }
    pub fn software_completed(&self) -> (r: bool)
        ensures self.wf(), r == self.view().completed,
    { proof { use_type_invariant(self); } self.completed }
}

}
