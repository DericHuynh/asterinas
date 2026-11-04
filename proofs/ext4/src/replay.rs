// SPDX-License-Identifier: MPL-2.0

//! Owned replay candidates and Linux revoke filtering. A plan is a bounded,
//! journal-excluding patch, not authority to publish a mounted filesystem.
//! The recovered shadow image must pass global filesystem validation first.

use vstd::prelude::*;
use crate::{bytes, crc, frozen::FrozenBlock, jbd2, layout::{JournalLayout, LayoutView}};

verus! {

pub struct Revocation { pub block: u32, pub sequence: u32 }
pub struct RecoveredWrite { block: u32, sequence: u32, image: FrozenBlock }
#[verifier::ext_equal]
pub struct WriteView { pub block: u32, pub sequence: u32, pub image: Seq<u8> }

pub open spec fn restored(raw: Seq<u8>, escaped: bool) -> Seq<u8> {
    if escaped { seq![0xc0u8, 0x3bu8, 0x39u8, 0x98u8] + raw.subrange(4, 4096) }
    else { raw }
}

pub open spec fn payload_ok(tag: jbd2::Tag, raw: Seq<u8>, sequence: u32, seed: u32, layout: &JournalLayout) -> bool {
    payload_for_layout(tag, raw, sequence, seed, layout.view())
}

pub open spec fn payload_for_layout(tag: jbd2::Tag, raw: Seq<u8>, sequence: u32, seed: u32, layout: LayoutView) -> bool {
    &&& raw.len() == 4096 && 0 < sequence < 4294967295
    &&& layout.start > 1 && 1024 <= layout.journal_blocks <= 32768
    &&& layout.start as int + layout.journal_blocks <= layout.fs_blocks
    &&& tag.block < layout.fs_blocks && !(layout.start <= tag.block < layout.start as int + layout.journal_blocks)
    &&& jbd2::flags_ok(tag.flags as nat)
    &&& (if tag.flags % 2 == 1 { bytes::be32(raw, 0) == 0 }
        else { bytes::be32(raw, 0) != 0xc03b3998 })
    &&& tag.checksum == crc::fold(crc::fold(seed, bytes::encoded_be(sequence)), raw)
}

impl RecoveredWrite {
    pub closed spec fn view(&self) -> WriteView {
        WriteView { block: self.block, sequence: self.sequence, image: self.image.view() }
    }
    pub fn block(&self) -> (r: u32) ensures r == self.view().block { self.block }
    pub fn sequence(&self) -> (r: u32) ensures r == self.view().sequence { self.sequence }
    pub fn image(&self) -> (r: &[u8]) ensures r@ == self.view().image { self.image.as_slice() }
}

pub fn decode_payload(tag: &jbd2::Tag, raw: &[u8], sequence: u32, seed: u32, layout: &JournalLayout)
    -> (r: Option<RecoveredWrite>)
    ensures match r {
        Some(w) => payload_ok(*tag, raw@, sequence, seed, layout) && w.view().block == tag.block
            && w.view().sequence == sequence && w.view().image == restored(raw@, tag.flags % 2 == 1),
        None => !payload_ok(*tag, raw@, sequence, seed, layout),
    },
{
    if raw.len() != 4096 || sequence == 0 || sequence == 4294967295 || !layout.allows_target(tag.block)
        || (tag.flags != 0 && tag.flags != 1 && tag.flags != 2 && tag.flags != 3
            && tag.flags != 8 && tag.flags != 9 && tag.flags != 10 && tag.flags != 11) { return None; }
    let escaped = tag.flags % 2 == 1;
    let prefix = bytes::read_be32(raw, 0).unwrap();
    if (escaped && prefix != 0) || (!escaped && prefix == jbd2::MAGIC) { return None; }
    if jbd2::payload_checksum(seed, sequence, raw).unwrap() != tag.checksum { return None; }
    let captured = FrozenBlock::capture(raw).unwrap();
    let image = captured.restore(escaped).unwrap();
    Some(RecoveredWrite { block: tag.block, sequence, image })
}

pub open spec fn images(writes: Seq<RecoveredWrite>) -> Seq<WriteView> {
    Seq::new(writes.len(), |i: int| writes[i].view())
}

pub open spec fn blocked(block: u32, sequence: u32, revocations: Seq<Revocation>) -> bool {
    exists|i: int| 0 <= i < revocations.len() && (#[trigger] revocations[i]).block == block
        && revocations[i].sequence >= sequence
}

pub fn unrevoked(block: u32, sequence: u32, revocations: &[Revocation]) -> (r: bool)
    ensures r == !blocked(block, sequence, revocations@),
{
    let mut i = 0usize;
    while i < revocations.len()
        invariant i <= revocations.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] revocations@[j]).block != block
                || revocations@[j].sequence < sequence,
        decreases revocations.len() - i,
    {
        if revocations[i].block == block && revocations[i].sequence >= sequence {
            proof { assert(blocked(block, sequence, revocations@)); }
            return false;
        }
        proof {
            assert forall|j: int| 0 <= j < i + 1 implies (#[trigger] revocations@[j]).block != block
                || revocations@[j].sequence < sequence by {
                if j < i { assert(revocations@[j].block != block || revocations@[j].sequence < sequence); }
            }
        }
        i += 1;
    }
    proof {
        if blocked(block, sequence, revocations@) {
            let j = choose|j: int| 0 <= j < revocations.len() && revocations@[j].block == block
                && revocations@[j].sequence >= sequence;
            assert(revocations@[j].block != block || revocations@[j].sequence < sequence);
        }
    }
    true
}

pub open spec fn input_ok(log: Seq<WriteView>, revocations: Seq<Revocation>, layout: &JournalLayout, first: u32, last: u32) -> bool {
    &&& layout.wf() && 0 < first <= last < 4294967295 && last as int - first <= 32768
    &&& log.len() + revocations.len() <= 4096
    &&& (forall|i: int| 0 <= i < log.len() ==> layout.allowed((#[trigger] log[i]).block)
        && first <= log[i].sequence <= last && log[i].image.len() == 4096)
    &&& (forall|i: int| 0 < i < log.len() ==> (#[trigger] log[i]).sequence >= log[i - 1].sequence)
    &&& (forall|i: int| 0 <= i < revocations.len() ==> layout.allowed((#[trigger] revocations[i]).block)
        && first <= revocations[i].sequence <= last)
}

fn valid_input(writes: &[RecoveredWrite], revocations: &[Revocation], layout: &JournalLayout, first: u32, last: u32) -> (r: bool)
    ensures r == input_ok(images(writes@), revocations@, layout, first, last),
{
    if !layout.valid() || first == 0 || first > last || last == 4294967295 || last - first > 32768
        || writes.len() > 4096 || revocations.len() > 4096 || writes.len() > 4096 - revocations.len() { return false; }
    let mut i = 0usize;
    while i < writes.len()
        invariant i <= writes.len(),
            forall|j: int| 0 <= j < i ==> layout.allowed((#[trigger] writes@[j].view()).block)
                && first <= writes@[j].view().sequence <= last && writes@[j].view().image.len() == 4096,
            forall|j: int| 0 < j < i ==> (#[trigger] writes@[j].view()).sequence >= writes@[j - 1].view().sequence,
        decreases writes.len() - i,
    {
        let w = &writes[i];
        if !layout.allows_target(w.block) || w.sequence < first || w.sequence > last || w.image.as_slice().len() != 4096
            || (i > 0 && w.sequence < writes[i - 1].sequence) {
            proof {
                if input_ok(images(writes@), revocations@, layout, first, last) {
                    assert(layout.allowed(images(writes@)[i as int].block));
                    assert(first <= images(writes@)[i as int].sequence <= last);
                    assert(images(writes@)[i as int].image.len() == 4096);
                    if i > 0 { assert(images(writes@)[i as int].sequence >= images(writes@)[i as int - 1].sequence); }
                }
            }
            return false;
        }
        proof {
            assert forall|j: int| 0 <= j < i + 1 implies layout.allowed((#[trigger] writes@[j].view()).block)
                && first <= writes@[j].view().sequence <= last && writes@[j].view().image.len() == 4096 by {
                if j < i { assert(layout.allowed(writes@[j].view().block)); }
            }
            assert forall|j: int| 0 < j < i + 1 implies
                (#[trigger] writes@[j].view()).sequence >= writes@[j - 1].view().sequence by {
                if j < i { assert(writes@[j].view().sequence >= writes@[j - 1].view().sequence); }
            }
        }
        i += 1;
    }
    let mut k = 0usize;
    while k < revocations.len()
        invariant k <= revocations.len(),
            forall|j: int| 0 <= j < k ==> layout.allowed((#[trigger] revocations@[j]).block)
                && first <= revocations@[j].sequence <= last,
        decreases revocations.len() - k,
    {
        let r = &revocations[k];
        if !layout.allows_target(r.block) || r.sequence < first || r.sequence > last {
            proof {
                if input_ok(images(writes@), revocations@, layout, first, last) {
                    assert(layout.allowed(revocations@[k as int].block)
                        && first <= revocations@[k as int].sequence <= last);
                }
            }
            return false;
        }
        proof {
            assert forall|j: int| 0 <= j < k + 1 implies layout.allowed((#[trigger] revocations@[j]).block)
                && first <= revocations@[j].sequence <= last by {
                if j < k { assert(layout.allowed(revocations@[j].block) && first <= revocations@[j].sequence <= last); }
            }
        }
        k += 1;
    }
    true
}

pub open spec fn latest(log: Seq<WriteView>, revocations: Seq<Revocation>, index: int) -> bool {
    &&& 0 <= index < log.len()
    &&& !blocked(log[index].block, log[index].sequence, revocations)
    &&& (forall|j: int| index < j < log.len() ==> (#[trigger] log[j]).block != log[index].block
        || blocked(log[j].block, log[j].sequence, revocations))
}

pub open spec fn covered(log: Seq<WriteView>, revocations: Seq<Revocation>, selected: Seq<usize>, start: nat) -> bool {
    forall|j: int| start <= j < log.len() && !blocked((#[trigger] log[j]).block, log[j].sequence, revocations)
        ==> exists|p: int| 0 <= p < selected.len() && j <= selected[p] < log.len()
            && log[selected[p] as int].block == log[j].block
}

pub open spec fn unique_targets(log: Seq<WriteView>, selected: Seq<usize>) -> bool {
    forall|p: int, q: int| 0 <= p < q < selected.len() ==>
        (#[trigger] log[selected[p] as int]).block != (#[trigger] log[selected[q] as int]).block
}

fn contains_target(writes: &[RecoveredWrite], selected: &[usize], block: u32) -> (r: bool)
    ensures r == (exists|p: int| 0 <= p < selected.len() && selected@[p] < writes.len()
        && (#[trigger] writes@[selected@[p] as int].view()).block == block),
{
    let mut i = 0usize;
    while i < selected.len()
        invariant i <= selected.len(),
            forall|j: int| 0 <= j < i && selected@[j] < writes.len()
                ==> (#[trigger] writes@[selected@[j] as int].view()).block != block,
        decreases selected.len() - i,
    {
        let index = selected[i];
        if index < writes.len() && writes[index].block == block {
            proof {
                assert(writes@[selected@[i as int] as int].view().block == block);
                assert(exists|p: int| 0 <= p < selected.len() && selected@[p] < writes.len()
                    && writes@[selected@[p] as int].view().block == block);
            }
            return true;
        }
        proof {
            assert forall|j: int| 0 <= j < i + 1 && selected@[j] < writes.len() implies
                (#[trigger] writes@[selected@[j] as int].view()).block != block by {
                if j < i { assert(writes@[selected@[j] as int].view().block != block); }
            }
        }
        i += 1;
    }
    false
}

pub struct ReplayPlan {
    layout: JournalLayout,
    writes: Vec<RecoveredWrite>,
    revocations: Vec<Revocation>,
    selected: Vec<usize>,
}

proof fn coverage_step(log: Seq<WriteView>, revocations: Seq<Revocation>, old: Seq<usize>, next: Seq<usize>, index: nat)
    requires index < log.len(), covered(log, revocations, old, index + 1),
        next == old || next == old.push(index as usize),
        !blocked(log[index as int].block, log[index as int].sequence, revocations) ==>
            exists|p: int| 0 <= p < next.len() && index <= next[p] < log.len()
                && log[next[p] as int].block == log[index as int].block,
    ensures covered(log, revocations, next, index),
{
    assert forall|j: int| index <= j < log.len() && !blocked((#[trigger] log[j]).block, log[j].sequence, revocations)
        implies exists|p: int| 0 <= p < next.len() && j <= next[p] < log.len()
            && log[next[p] as int].block == log[j].block by {
        if j > index {
            assert(exists|p: int| 0 <= p < old.len() && j <= old[p] < log.len()
                && log[old[p] as int].block == log[j].block);
            let p = choose|p: int| 0 <= p < old.len() && j <= old[p] < log.len()
                && log[old[p] as int].block == log[j].block;
            assert(next[p] == old[p]);
        }
    }
}

impl ReplayPlan {
    #[verifier::type_invariant]
    spec fn valid_plan(self) -> bool { self.refines() }
    pub closed spec fn log(&self) -> Seq<WriteView> { images(self.writes@) }
    pub closed spec fn revocations(&self) -> Seq<Revocation> { self.revocations@ }
    pub closed spec fn selection(&self) -> Seq<usize> { self.selected@ }
    pub closed spec fn layout(&self) -> &JournalLayout { &self.layout }
    pub open spec fn refines(&self) -> bool {
        &&& self.layout().wf()
        &&& self.selection().len() <= self.log().len()
        &&& self.log().len() + self.revocations().len() <= 4096
        &&& (forall|i: int| 0 <= i < self.log().len() ==>
            self.layout().allowed((#[trigger] self.log()[i]).block) && self.log()[i].image.len() == 4096)
        &&& (forall|p: int| 0 <= p < self.selection().len()
            ==> #[trigger] latest(self.log(), self.revocations(), self.selection()[p] as int))
        &&& unique_targets(self.log(), self.selection())
        &&& (forall|j: int| #[trigger] latest(self.log(), self.revocations(), j) ==>
            exists|p: int| 0 <= p < self.selection().len() && self.selection()[p] == j)
    }

    pub fn len(&self) -> (r: usize) ensures self.refines(), r == self.selection().len() {
        proof { use_type_invariant(self); }
        self.selected.len()
    }

    pub fn get(&self, index: usize) -> (r: Option<&RecoveredWrite>)
        ensures match r {
            Some(w) => index < self.selection().len() && self.selection()[index as int] < self.log().len()
                && w.view() == self.log()[self.selection()[index as int] as int],
            None => index >= self.selection().len() || self.selection()[index as int] >= self.log().len(),
        },
    {
        if index >= self.selected.len() { return None; }
        let i = self.selected[index];
        if i >= self.writes.len() { return None; }
        Some(&self.writes[i])
    }
}

pub fn build(layout: JournalLayout, writes: Vec<RecoveredWrite>, revocations: Vec<Revocation>, first: u32, last: u32)
    -> (r: Option<ReplayPlan>)
    ensures match r {
        Some(p) => input_ok(images(writes@), revocations@, &layout, first, last) && p.refines()
            && p.log() == images(writes@) && p.revocations() == revocations@
            && p.layout().view() == layout.view() && p.selection().len() <= writes.len(),
        None => !input_ok(images(writes@), revocations@, &layout, first, last),
    },
{
    if !valid_input(writes.as_slice(), revocations.as_slice(), &layout, first, last) { return None; }
    let ghost log = images(writes@);
    let mut selected: Vec<usize> = Vec::new();
    let mut remaining = writes.len();
    while remaining > 0
        invariant remaining <= writes.len(), log == images(writes@),
            selected.len() <= writes.len() - remaining,
            unique_targets(log, selected@), covered(log, revocations@, selected@, remaining as nat),
            forall|p: int| 0 <= p < selected.len() ==> remaining <= (#[trigger] selected@[p]) < writes.len()
                && latest(log, revocations@, selected@[p] as int),
        decreases remaining,
    {
        let index = remaining - 1;
        let w = &writes[index];
        let keep = unrevoked(w.block, w.sequence, revocations.as_slice());
        let present = if keep { contains_target(writes.as_slice(), selected.as_slice(), w.block) } else { false };
        let ghost old_selection = selected@;
        if keep && !present {
            proof {
                assert(latest(log, revocations@, index as int)) by {
                    assert forall|j: int| index < j < log.len() implies (#[trigger] log[j]).block != log[index as int].block
                        || blocked(log[j].block, log[j].sequence, revocations@) by {
                        if log[j].block == log[index as int].block && !blocked(log[j].block, log[j].sequence, revocations@) {
                            assert(exists|p: int| 0 <= p < selected.len() && j <= selected@[p] < log.len()
                                && log[selected@[p] as int].block == log[j].block);
                        }
                    }
                }
            }
            selected.push(index);
        }
        proof {
            if keep {
                if present {
                    let p = choose|p: int| 0 <= p < old_selection.len() && old_selection[p] < writes.len()
                        && writes@[old_selection[p] as int].view().block == w.view().block;
                    assert(selected@[p] == old_selection[p]);
                    assert(index <= selected@[p] < log.len());
                    assert(log[selected@[p] as int].block == log[index as int].block);
                } else {
                    assert(selected@[selected.len() as int - 1] == index);
                }
                assert(exists|p: int| 0 <= p < selected.len() && index <= selected@[p] < log.len()
                    && log[selected@[p] as int].block == log[index as int].block);
            }
            coverage_step(log, revocations@, old_selection, selected@, index as nat);
        }
        remaining = index;
    }
    proof {
        assert forall|j: int| #[trigger] latest(log, revocations@, j) implies
            exists|p: int| 0 <= p < selected.len() && selected@[p] == j by {
            assert(exists|p: int| 0 <= p < selected.len() && j <= selected@[p] < log.len()
                && log[selected@[p] as int].block == log[j].block);
            let p = choose|p: int| 0 <= p < selected.len() && j <= selected@[p] < log.len()
                && log[selected@[p] as int].block == log[j].block;
            assert(!blocked(log[selected@[p] as int].block, log[selected@[p] as int].sequence, revocations@));
            if selected@[p] != j {
                assert(log[selected@[p] as int].block != log[j].block
                    || blocked(log[selected@[p] as int].block, log[selected@[p] as int].sequence, revocations@));
            }
        }
    }
    Some(ReplayPlan { layout, writes, revocations, selected })
}

pub proof fn same_or_later_revoke_suppresses_a_write(block: u32, sequence: u32, revocations: Seq<Revocation>, i: int)
    requires 0 <= i < revocations.len(), revocations[i].block == block, revocations[i].sequence >= sequence,
    ensures blocked(block, sequence, revocations),
{
}

pub proof fn reallocation_after_every_revoke_survives(block: u32, sequence: u32, revocations: Seq<Revocation>)
    requires forall|i: int| 0 <= i < revocations.len() && (#[trigger] revocations[i]).block == block
        ==> revocations[i].sequence < sequence,
    ensures !blocked(block, sequence, revocations),
{
    if blocked(block, sequence, revocations) {
        let i = choose|i: int| 0 <= i < revocations.len() && revocations[i].block == block && revocations[i].sequence >= sequence;
    }
}

pub open spec fn serial_gt(a: u32, b: u32) -> bool {
    let difference = (a as int - b as int) % 4294967296;
    0 < difference < 2147483648
}

pub fn linux_sequence_after(a: u32, b: u32) -> (r: bool)
    ensures r == serial_gt(a, b),
{
    let difference = a.wrapping_sub(b);
    difference != 0 && difference < 2147483648
}

pub proof fn bounded_window_matches_linux_serial_order(first: u32, last: u32, a: u32, b: u32)
    requires first <= a <= last, first <= b <= last, last as int - first < 2147483648,
    ensures serial_gt(a, b) == (a > b),
{
    if a >= b {
        assert((a as int - b as int) % 4294967296 == a as int - b as int);
    } else {
        assert((a as int - b as int) % 4294967296 == a as int - b as int + 4294967296);
    }
}

}
