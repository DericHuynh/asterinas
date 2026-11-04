// SPDX-License-Identifier: MPL-2.0

//! Physical byte interpretation of the writer's per-write persistence ledger.
//! Whole-image persistence is an explicit 4 KiB device-contract premise. The
//! proof must show that each event changes exactly the issued physical block.

use vstd::{assert_maps_equal, prelude::*};
use crate::{recovery_io::CommandView, replay, replay_refinement::Disk, transaction, write_device::{self, Machine}, write_io};

verus! {

pub open spec fn command(v: write_io::Images, k: nat) -> CommandView {
    write_io::expected(v, write_device::at(k, v.tx.payloads.len()))
}

pub open spec fn address(v: write_io::Images, k: nat) -> u32 {
    match command(v, k) { CommandView::Write { block, image } => block, CommandView::Flush => 0 }
}

pub open spec fn image(v: write_io::Images, k: nat) -> Seq<u8> {
    match command(v, k) { CommandView::Write { block, image } => image, CommandView::Flush => Seq::empty() }
}

pub open spec fn targets_exist(before: Disk, v: write_io::Images) -> bool {
    forall|k: nat| write_device::is_write(k, v.tx.payloads.len()) ==> #[trigger] before.dom().contains(address(v, k))
}

pub open spec fn apply(before: Disk, v: write_io::Images, stable: Set<nat>, limit: nat) -> Disk
    decreases limit,
{
    if limit == 0 { before }
    else {
        let k = (limit - 1) as nat;
        let previous = apply(before, v, stable, k);
        if write_device::is_write(k, v.tx.payloads.len()) && stable.contains(k) { previous.insert(address(v, k), image(v, k)) }
        else { previous }
    }
}

pub open spec fn disk(m: Machine, before: Disk, v: write_io::Images) -> Disk {
    apply(before, v, m.stable, write_device::total(v.tx.payloads.len()))
}

pub(crate) proof fn program_context(v: write_io::Images)
    requires write_io::valid_images(v),
    ensures transaction::wf(v.tx), v.journal_block == v.tx.layout.start,
{
    reveal(write_io::valid_images);
}

proof fn home_target(v: write_io::Images, index: int)
    requires transaction::wf(v.tx), 0 <= index < v.tx.original.len(),
    ensures v.tx.original[index].block < v.tx.layout.fs_blocks,
        !(v.tx.layout.start <= v.tx.original[index].block < v.tx.layout.start as int + v.tx.layout.journal_blocks),
{
    assert(replay::payload_for_layout(v.tx.tags[index], v.tx.payloads[index], v.tx.sequence, v.tx.seed, v.tx.layout));
}

#[verifier::rlimit(30)]
pub proof fn repeated_addresses_are_separated_by_a_completed_fence(v: write_io::Images, earlier: nat, later: nat)
    requires write_io::valid_images(v), write_device::is_write(earlier, v.tx.payloads.len()),
        write_device::is_write(later, v.tx.payloads.len()), earlier < later, address(v, earlier) == address(v, later),
    ensures write_device::fence_after(earlier, v.tx.payloads.len()) < later,
{
    hide(crate::crc::fold);
    program_context(v);
    let count = v.tx.payloads.len();
    if 8 + count <= earlier < 8 + 2 * count {
        let i = (earlier - (8 + count)) as int;
        home_target(v, i);
        if 8 + count <= later < 8 + 2 * count {
            let j = (later - (8 + count)) as int;
            home_target(v, j);
            assert(v.tx.original[i].block != v.tx.original[j].block);
        }
    }
    if 8 + count <= later < 8 + 2 * count { home_target(v, (later - (8 + count)) as int); }
}

pub proof fn apply_preserves_domain(before: Disk, v: write_io::Images, stable: Set<nat>, limit: nat)
    requires targets_exist(before, v),
    ensures apply(before, v, stable, limit).dom() == before.dom(),
    decreases limit,
{
    if limit > 0 {
        apply_preserves_domain(before, v, stable, (limit - 1) as nat);
        if write_device::is_write((limit - 1) as nat, v.tx.payloads.len()) {
            assert(before.dom().contains(address(v, (limit - 1) as nat)));
        }
    }
}

pub proof fn apply_keeps_every_existing_block(before: Disk, v: write_io::Images, stable: Set<nat>, limit: nat)
    ensures before.dom().subset_of(apply(before, v, stable, limit).dom()),
    decreases limit,
{
    if limit > 0 { apply_keeps_every_existing_block(before, v, stable, (limit - 1) as nat); }
}

pub proof fn adding_a_later_token_cannot_change_an_earlier_prefix(before: Disk, v: write_io::Images,
    stable: Set<nat>, k: nat, limit: nat)
    requires limit <= k,
    ensures apply(before, v, stable.insert(k), limit) == apply(before, v, stable, limit),
    decreases limit,
{
    if limit > 0 { adding_a_later_token_cannot_change_an_earlier_prefix(before, v, stable, k, (limit - 1) as nat); }
}

pub proof fn persisting_one_token_changes_exactly_its_block(before: Disk, v: write_io::Images,
    stable: Set<nat>, k: nat, limit: nat)
    requires k < limit, write_device::is_write(k, v.tx.payloads.len()), !stable.contains(k),
        forall|j: nat| k < j < limit && write_device::is_write(j, v.tx.payloads.len()) && stable.contains(j)
            ==> #[trigger] address(v, j) != address(v, k),
    ensures apply(before, v, stable.insert(k), limit) == apply(before, v, stable, limit).insert(address(v, k), image(v, k)),
    decreases limit,
{
    let last = (limit - 1) as nat;
    if k == last {
        adding_a_later_token_cannot_change_an_earlier_prefix(before, v, stable, k, last);
    } else {
        persisting_one_token_changes_exactly_its_block(before, v, stable, k, last);
        if write_device::is_write(last, v.tx.payloads.len()) && stable.contains(last) {
            assert(address(v, last) != address(v, k));
            let prefix = apply(before, v, stable, last);
            assert_maps_equal!(prefix.insert(address(v, k), image(v, k)).insert(address(v, last), image(v, last)),
                prefix.insert(address(v, last), image(v, last)).insert(address(v, k), image(v, k)), block => { });
        }
    }
}

pub proof fn a_ledger_persistence_event_refines_one_atomic_block_write(m: Machine, before: Disk,
    v: write_io::Images, k: nat)
    requires write_io::valid_images(v), write_device::inv(m, v.tx.payloads.len()),
        write_device::enabled(m, write_device::Event::Persist(k)), targets_exist(before, v),
    ensures disk(write_device::next(m, write_device::Event::Persist(k), v.tx.payloads.len()), before, v)
        == disk(m, before, v).insert(address(v, k), image(v, k)),
        disk(m, before, v).dom() == before.dom(),
{
    program_context(v);
    let count = v.tx.payloads.len();
    assert(k < write_device::total(count));
    assert forall|j: nat| k < j < write_device::total(count) && write_device::is_write(j, count) && m.stable.contains(j)
        implies #[trigger] address(v, j) != address(v, k) by {
        if address(v, j) == address(v, k) {
            repeated_addresses_are_separated_by_a_completed_fence(v, k, j);
            assert(m.issued.contains(j));
            assert(j <= crate::write_protocol::completed_count(m.io, count));
            assert(m.stable.contains(k));
        }
    }
    persisting_one_token_changes_exactly_its_block(before, v, m.stable, k, write_device::total(count));
    apply_preserves_domain(before, v, m.stable, write_device::total(count));
}

pub proof fn apply_frames_every_unwritten_block(before: Disk, v: write_io::Images, stable: Set<nat>, limit: nat, block: u32)
    requires before.dom().contains(block),
        forall|k: nat| k < limit && write_device::is_write(k, v.tx.payloads.len()) && stable.contains(k)
            ==> #[trigger] address(v, k) != block,
    ensures apply(before, v, stable, limit)[block] == before[block],
    decreases limit,
{
    if limit > 0 {
        let k = (limit - 1) as nat;
        apply_frames_every_unwritten_block(before, v, stable, k, block);
        if write_device::is_write(k, v.tx.payloads.len()) && stable.contains(k) { assert(address(v, k) != block); }
    }
}

pub proof fn the_last_stable_write_determines_a_block(before: Disk, v: write_io::Images, stable: Set<nat>, k: nat, limit: nat)
    requires k < limit, write_device::is_write(k, v.tx.payloads.len()), stable.contains(k),
        forall|j: nat| k < j < limit && write_device::is_write(j, v.tx.payloads.len()) && stable.contains(j)
            ==> #[trigger] address(v, j) != address(v, k),
    ensures apply(before, v, stable, limit)[address(v, k)] == image(v, k),
    decreases limit,
{
    let last = (limit - 1) as nat;
    if last > k {
        the_last_stable_write_determines_a_block(before, v, stable, k, last);
        if write_device::is_write(last, v.tx.payloads.len()) && stable.contains(last) { assert(address(v, last) != address(v, k)); }
    }
}

pub proof fn a_unique_address_is_either_old_or_its_frozen_image(before: Disk, v: write_io::Images,
    stable: Set<nat>, k: nat, limit: nat)
    requires k < limit, write_device::is_write(k, v.tx.payloads.len()), before.dom().contains(address(v, k)),
        forall|j: nat| j < limit && j != k && write_device::is_write(j, v.tx.payloads.len()) && stable.contains(j)
            ==> #[trigger] address(v, j) != address(v, k),
    ensures apply(before, v, stable, limit)[address(v, k)] == if stable.contains(k) { image(v, k) } else { before[address(v, k)] },
{
    if stable.contains(k) { the_last_stable_write_determines_a_block(before, v, stable, k, limit); }
    else {
        assert forall|j: nat| j < limit && write_device::is_write(j, v.tx.payloads.len()) && stable.contains(j)
            implies #[trigger] address(v, j) != address(v, k) by { }
        apply_frames_every_unwritten_block(before, v, stable, limit, address(v, k));
    }
}

#[verifier::rlimit(30)]
pub proof fn each_log_record_address_has_one_writer(v: write_io::Images, k: nat, j: nat)
    requires write_io::valid_images(v),
        4 <= k < 5 + v.tx.payloads.len() || k == 6 + v.tx.payloads.len(),
        write_device::is_write(j, v.tx.payloads.len()), j != k,
    ensures address(v, j) != address(v, k),
{
    hide(crate::crc::fold);
    program_context(v);
    let count = v.tx.payloads.len();
    if 8 + count <= j < 8 + 2 * count { home_target(v, (j - (8 + count)) as int); }
}

pub proof fn journal_record_bytes_follow_the_issued_snapshot(m: Machine, before: Disk, v: write_io::Images, k: nat)
    requires write_io::valid_images(v), targets_exist(before, v),
        4 <= k < 5 + v.tx.payloads.len() || k == 6 + v.tx.payloads.len(),
    ensures disk(m, before, v)[address(v, k)] == if m.stable.contains(k) { image(v, k) } else { before[address(v, k)] },
{
    program_context(v);
    assert(write_device::is_write(k, v.tx.payloads.len()));
    assert(before.dom().contains(address(v, k)));
    assert forall|j: nat| j < write_device::total(v.tx.payloads.len()) && j != k
        && write_device::is_write(j, v.tx.payloads.len()) && m.stable.contains(j)
        implies #[trigger] address(v, j) != address(v, k) by { each_log_record_address_has_one_writer(v, k, j); }
    a_unique_address_is_either_old_or_its_frozen_image(before, v, m.stable, k, write_device::total(v.tx.payloads.len()));
}

pub proof fn index_state_is_valid(count: nat, k: nat)
    requires 1 <= count <= 250, k <= write_device::total(count),
    ensures crate::write_protocol::wf(write_device::at(k, count), count),
{
}

pub proof fn every_program_write_has_a_complete_bounded_image(v: write_io::Images, k: nat)
    requires write_io::valid_images(v), write_device::is_write(k, v.tx.payloads.len()),
    ensures command(v, k) is Write, image(v, k).len() == 4096,
        address(v, k) < v.tx.layout.fs_blocks,
        address(v, k) as nat * 4096 + 4096 <= v.partition_bytes,
{
    program_context(v);
    index_state_is_valid(v.tx.payloads.len(), k);
    write_io::expected_command_is_confined(v, write_device::at(k, v.tx.payloads.len()));
}

proof fn mapped_survives_one_block_write(before: Disk, layout: crate::layout::LayoutView, block: u32, bytes: Seq<u8>)
    requires crate::journal_view::mapped(before, layout), bytes.len() == 4096,
    ensures crate::journal_view::mapped(before.insert(block, bytes), layout),
{
    assert forall|logical: u32| logical < layout.journal_blocks implies
        #[trigger] before.insert(block, bytes).dom().contains((layout.start + logical) as u32)
            && before.insert(block, bytes)[(layout.start + logical) as u32].len() == 4096 by {
        assert(before.dom().contains((layout.start + logical) as u32));
    }
}

pub proof fn apply_preserves_initialized_journal_mapping(before: Disk, v: write_io::Images, stable: Set<nat>, limit: nat)
    requires write_io::valid_images(v), crate::journal_view::mapped(before, v.tx.layout),
    ensures crate::journal_view::mapped(apply(before, v, stable, limit), v.tx.layout),
    decreases limit,
{
    if limit > 0 {
        let k = (limit - 1) as nat;
        apply_preserves_initialized_journal_mapping(before, v, stable, k);
        if write_device::is_write(k, v.tx.payloads.len()) && stable.contains(k) {
            every_program_write_has_a_complete_bounded_image(v, k);
            mapped_survives_one_block_write(apply(before, v, stable, k), v.tx.layout, address(v, k), image(v, k));
        }
    }
}

pub proof fn journal_writes_stay_in_the_reserved_record_range(v: write_io::Images, k: nat)
    requires write_io::valid_images(v), write_device::is_write(k, v.tx.payloads.len()),
    ensures v.tx.layout.start <= address(v, k) < v.tx.layout.start as int + v.tx.layout.journal_blocks ==>
        address(v, k) == v.journal_block || v.journal_block as int + 1 <= address(v, k) <= v.journal_block as int + v.tx.payloads.len() + 2,
{
    program_context(v);
    let count = v.tx.payloads.len();
    if 8 + count <= k < 8 + 2 * count { home_target(v, (k - (8 + count)) as int); }
}

pub proof fn only_activation_and_retirement_write_the_journal_superblock(v: write_io::Images, k: nat)
    requires write_io::valid_images(v), write_device::is_write(k, v.tx.payloads.len()),
        k != 2, k != 9 + 2 * v.tx.payloads.len(),
    ensures address(v, k) != v.journal_block,
{
    program_context(v);
    let count = v.tx.payloads.len();
    if 8 + count <= k < 8 + 2 * count { home_target(v, (k - (8 + count)) as int); }
}

pub proof fn untouched_journal_blocks_retain_their_initial_bytes(m: Machine, before: Disk, v: write_io::Images, logical: u32)
    requires write_io::valid_images(v), before.dom().contains((v.journal_block + logical) as u32),
        v.tx.payloads.len() + 3 <= logical < v.tx.layout.journal_blocks,
    ensures disk(m, before, v)[(v.journal_block + logical) as u32] == before[(v.journal_block + logical) as u32],
{
    program_context(v);
    let block = (v.journal_block + logical) as u32;
    assert forall|k: nat| k < write_device::total(v.tx.payloads.len())
        && write_device::is_write(k, v.tx.payloads.len()) && m.stable.contains(k)
        implies #[trigger] address(v, k) != block by { journal_writes_stay_in_the_reserved_record_range(v, k); }
    apply_frames_every_unwritten_block(before, v, m.stable, write_device::total(v.tx.payloads.len()), block);
}

pub proof fn journal_superblock_is_one_of_the_ordered_state_images(m: Machine, before: Disk, v: write_io::Images)
    requires write_io::valid_images(v), targets_exist(before, v),
    ensures disk(m, before, v)[v.journal_block] == if m.stable.contains(9 + 2 * v.tx.payloads.len()) { v.tail }
        else if m.stable.contains(2) { v.activation } else { before[v.journal_block] },
{
    program_context(v);
    let count = v.tx.payloads.len();
    let tail = 9 + 2 * count;
    if m.stable.contains(tail) {
        assert forall|j: nat| tail < j < write_device::total(count) && write_device::is_write(j, count) && m.stable.contains(j)
            implies #[trigger] address(v, j) != address(v, tail) by { }
        the_last_stable_write_determines_a_block(before, v, m.stable, tail, write_device::total(count));
    } else {
        assert(before.dom().contains(address(v, 2)));
        assert forall|j: nat| j < write_device::total(count) && j != 2 && write_device::is_write(j, count) && m.stable.contains(j)
            implies #[trigger] address(v, j) != address(v, 2) by {
            only_activation_and_retirement_write_the_journal_superblock(v, j);
        }
        a_unique_address_is_either_old_or_its_frozen_image(before, v, m.stable, 2, write_device::total(count));
    }
}

pub proof fn a_stable_home_write_has_its_exact_afterimage(m: Machine, before: Disk, v: write_io::Images, index: nat)
    requires write_io::valid_images(v), index < v.tx.original.len(),
        m.stable.contains(8 + v.tx.payloads.len() + index),
    ensures disk(m, before, v)[v.tx.original[index as int].block] == v.tx.original[index as int].image,
{
    program_context(v);
    let count = v.tx.payloads.len();
    let k = 8 + count + index;
    home_target(v, index as int);
    assert forall|j: nat| k < j < write_device::total(count) && write_device::is_write(j, count) && m.stable.contains(j)
        implies #[trigger] address(v, j) != address(v, k) by {
        if 8 + count <= j < 8 + 2 * count {
            let other = (j - (8 + count)) as int;
            assert(v.tx.original[index as int].block != v.tx.original[other].block);
        }
    }
    the_last_stable_write_determines_a_block(before, v, m.stable, k, write_device::total(count));
}

#[verifier::rlimit(20)]
pub proof fn before_checkpoint_block_zero_is_only_the_recovery_flag_image(m: Machine, before: Disk, v: write_io::Images)
    requires write_io::valid_images(v), before.dom().contains(0),
        forall|i: nat| i < v.tx.payloads.len() ==> !#[trigger] m.stable.contains(8 + v.tx.payloads.len() + i),
    ensures disk(m, before, v).dom().contains(0),
        disk(m, before, v)[0] == if m.stable.contains(0) { v.dirty } else { before[0] },
{
    hide(crate::crc::fold);
    program_context(v);
    let count = v.tx.payloads.len();
    assert forall|j: nat| j < write_device::total(count) && j != 0 && write_device::is_write(j, count) && m.stable.contains(j)
        implies #[trigger] address(v, j) != address(v, 0) by {
        if 8 + count <= j < 8 + 2 * count {
            let index = (j - (8 + count)) as nat;
            assert(index < count);
            assert(!m.stable.contains(8 + count + index));
        }
    }
    a_unique_address_is_either_old_or_its_frozen_image(before, v, m.stable, 0, write_device::total(count));
    apply_keeps_every_existing_block(before, v, m.stable, write_device::total(count));
}

pub proof fn a_successful_flush_refines_finitely_many_issued_atomic_writes(m: Machine, before: Disk,
    v: write_io::Images) -> (r: (Seq<Machine>, Seq<write_device::Event>))
    requires write_io::valid_images(v), write_device::inv(m, v.tx.payloads.len()), targets_exist(before, v),
        m.io.pending, write_device::is_fence(crate::write_protocol::completed_count(m.io, v.tx.payloads.len()), v.tx.payloads.len()),
    ensures write_device::execution(r.0, r.1, v.tx.payloads.len()), r.0[0] == m,
        r.0.last() == write_device::next(m, write_device::Event::Complete(true), v.tx.payloads.len()),
        r.1.len() > 0,
        forall|i: int| 0 <= i < r.1.len() - 1 ==> ((#[trigger] r.1[i]) matches write_device::Event::Persist(k)
            && disk(r.0[i + 1], before, v) == disk(r.0[i], before, v).insert(address(v, k), image(v, k))),
        disk(r.0[r.0.len() as int - 2], before, v) == disk(r.0.last(), before, v),
{
    let count = v.tx.payloads.len();
    let (states, events) = write_device::a_successful_flush_has_a_finite_persistence_refinement(m, count);
    write_device::every_finite_io_interleaving(states, events, count);
    assert forall|i: int| 0 <= i < events.len() - 1 implies ((#[trigger] events[i]) matches write_device::Event::Persist(k)
        && disk(states[i + 1], before, v) == disk(states[i], before, v).insert(address(v, k), image(v, k))) by {
        assert(events[i] is Persist);
        let k = events[i]->Persist_0;
        assert(write_device::inv(states[i], count));
        assert(write_device::enabled(states[i], write_device::Event::Persist(k)));
        assert(states[i + 1] == write_device::next(states[i], write_device::Event::Persist(k), count));
        a_ledger_persistence_event_refines_one_atomic_block_write(states[i], before, v, k);
    }
    (states, events)
}

#[verifier::rlimit(20)]
pub proof fn without_a_stable_home_target_zero_only_dirty_marking_changes_block_zero(m: Machine, before: Disk, v: write_io::Images)
    requires write_io::valid_images(v), before.dom().contains(0),
        forall|i: nat| i < v.tx.payloads.len() && v.tx.original[i as int].block == 0
            ==> !#[trigger] m.stable.contains(8 + v.tx.payloads.len() + i),
    ensures disk(m, before, v).dom().contains(0),
        disk(m, before, v)[0] == if m.stable.contains(0) { v.dirty } else { before[0] },
{
    hide(crate::crc::fold);
    program_context(v);
    let count = v.tx.payloads.len();
    assert forall|j: nat| j < write_device::total(count) && j != 0 && write_device::is_write(j, count) && m.stable.contains(j)
        implies #[trigger] address(v, j) != address(v, 0) by {
        if 8 + count <= j < 8 + 2 * count {
            let index = (j - (8 + count)) as nat;
            if v.tx.original[index as int].block == 0 { assert(!m.stable.contains(8 + count + index)); }
        }
    }
    a_unique_address_is_either_old_or_its_frozen_image(before, v, m.stable, 0, write_device::total(count));
    apply_keeps_every_existing_block(before, v, m.stable, write_device::total(count));
}

}
