// SPDX-License-Identifier: MPL-2.0

//! The executable replay plan's selected images equal chronological JBD2 redo
//! with Linux revoke suppression. This proves values as well as target bounds.

use vstd::{assert_maps_equal, prelude::*};
use crate::replay::{self, Revocation, WriteView};

verus! {

pub type Disk = Map<u32, Seq<u8>>;

pub open spec fn chronological(home: Disk, log: Seq<WriteView>, revocations: Seq<Revocation>) -> Disk
    decreases log.len(),
{
    if log.len() == 0 { home }
    else {
        let previous = chronological(home, log.drop_last(), revocations);
        let write = log.last();
        if replay::blocked(write.block, write.sequence, revocations) { previous }
        else { previous.insert(write.block, write.image) }
    }
}

pub open spec fn selected(home: Disk, log: Seq<WriteView>, indices: Seq<usize>) -> Disk
    decreases indices.len(),
{
    if indices.len() == 0 { home }
    else {
        let previous = selected(home, log, indices.drop_last());
        let write = log[indices.last() as int];
        previous.insert(write.block, write.image)
    }
}

pub open spec fn all_targets_exist(home: Disk, log: Seq<WriteView>) -> bool {
    forall|i: int| 0 <= i < log.len() ==> home.dom().contains((#[trigger] log[i]).block)
}

pub open spec fn indices_valid(log: Seq<WriteView>, indices: Seq<usize>) -> bool {
    forall|p: int| 0 <= p < indices.len() ==> (#[trigger] indices[p]) < log.len()
}

pub open spec fn last_eligible(log: Seq<WriteView>, revocations: Seq<Revocation>, block: u32) -> Option<nat>
    decreases log.len(),
{
    if log.len() == 0 { None }
    else if log.last().block == block && !replay::blocked(block, log.last().sequence, revocations) {
        Some((log.len() - 1) as nat)
    } else { last_eligible(log.drop_last(), revocations, block) }
}

pub proof fn last_eligible_characterizes_latest(log: Seq<WriteView>, revocations: Seq<Revocation>, block: u32)
    ensures match last_eligible(log, revocations, block) {
        Some(i) => i < log.len() && log[i as int].block == block && replay::latest(log, revocations, i as int),
        None => forall|i: int| 0 <= i < log.len() && (#[trigger] log[i]).block == block
            ==> replay::blocked(block, log[i].sequence, revocations),
    },
    decreases log.len(),
{
    if log.len() > 0 {
        last_eligible_characterizes_latest(log.drop_last(), revocations, block);
        if log.last().block != block || replay::blocked(block, log.last().sequence, revocations) {
            if let Some(i) = last_eligible(log.drop_last(), revocations, block) {
                assert forall|j: int| i < j < log.len() implies (#[trigger] log[j]).block != block
                    || replay::blocked(block, log[j].sequence, revocations) by {
                    if j < log.len() - 1 {
                        assert(log.drop_last()[j] == log[j]);
                    } else { assert(log[j] == log.last()); }
                }
            } else {
                assert forall|j: int| 0 <= j < log.len() && (#[trigger] log[j]).block == block
                    implies replay::blocked(block, log[j].sequence, revocations) by {
                    if j < log.len() - 1 { assert(log.drop_last()[j] == log[j]); }
                    else { assert(log[j] == log.last()); }
                }
            }
        }
    }
}

pub proof fn latest_index_is_unique(log: Seq<WriteView>, revocations: Seq<Revocation>, i: int, j: int)
    requires replay::latest(log, revocations, i), replay::latest(log, revocations, j), log[i].block == log[j].block,
    ensures i == j,
{
    if i < j { assert(log[j].block != log[i].block || replay::blocked(log[j].block, log[j].sequence, revocations)); }
    if j < i { assert(log[i].block != log[j].block || replay::blocked(log[i].block, log[i].sequence, revocations)); }
}

pub proof fn chronological_lookup(home: Disk, log: Seq<WriteView>, revocations: Seq<Revocation>, block: u32)
    requires all_targets_exist(home, log), home.dom().contains(block),
    ensures chronological(home, log, revocations).dom() == home.dom(),
        chronological(home, log, revocations)[block] == match last_eligible(log, revocations, block) {
            Some(i) => log[i as int].image,
            None => home[block],
        },
    decreases log.len(),
{
    if log.len() > 0 {
        assert(all_targets_exist(home, log.drop_last()));
        chronological_lookup(home, log.drop_last(), revocations, block);
        assert(home.dom().contains(log.last().block));
        if log.last().block != block || replay::blocked(block, log.last().sequence, revocations) {
            last_eligible_characterizes_latest(log.drop_last(), revocations, block);
        }
    }
}

pub proof fn selected_target_lookup(home: Disk, log: Seq<WriteView>, indices: Seq<usize>, p: int)
    requires all_targets_exist(home, log), indices_valid(log, indices), replay::unique_targets(log, indices), 0 <= p < indices.len(),
    ensures selected(home, log, indices).dom() == home.dom(),
        selected(home, log, indices)[log[indices[p] as int].block] == log[indices[p] as int].image,
    decreases indices.len(),
{
    if indices.len() > 0 {
        assert(home.dom().contains(log[indices.last() as int].block));
        if p < indices.len() - 1 {
            assert(indices_valid(log, indices.drop_last()));
            assert(replay::unique_targets(log, indices.drop_last()));
            selected_target_lookup(home, log, indices.drop_last(), p);
            assert(log[indices[p] as int].block != log[indices.last() as int].block);
        } else {
            selected_domain(home, log, indices.drop_last());
        }
    }
}

pub proof fn selected_domain(home: Disk, log: Seq<WriteView>, indices: Seq<usize>)
    requires all_targets_exist(home, log), indices_valid(log, indices),
    ensures selected(home, log, indices).dom() == home.dom(),
    decreases indices.len(),
{
    if indices.len() > 0 {
        assert(indices_valid(log, indices.drop_last()));
        selected_domain(home, log, indices.drop_last());
        assert(home.dom().contains(log[indices.last() as int].block));
    }
}

pub proof fn selected_frame(home: Disk, log: Seq<WriteView>, indices: Seq<usize>, block: u32)
    requires all_targets_exist(home, log), indices_valid(log, indices), home.dom().contains(block),
        forall|p: int| 0 <= p < indices.len() ==> (#[trigger] log[indices[p] as int]).block != block,
    ensures selected(home, log, indices)[block] == home[block],
    decreases indices.len(),
{
    if indices.len() > 0 {
        assert(indices_valid(log, indices.drop_last()));
        assert(log[indices.last() as int].block != block);
        selected_frame(home, log, indices.drop_last(), block);
    }
}

pub proof fn executable_selection_equals_chronological_redo(home: Disk, plan: &replay::ReplayPlan)
    requires plan.refines(), all_targets_exist(home, plan.log()),
    ensures selected(home, plan.log(), plan.selection()) == chronological(home, plan.log(), plan.revocations()),
{
    let log = plan.log();
    let revocations = plan.revocations();
    let indices = plan.selection();
    assert forall|p: int| 0 <= p < indices.len() implies (#[trigger] indices[p]) < log.len() by {
        assert(replay::latest(log, revocations, indices[p] as int));
    }
    assert(indices_valid(log, indices));
    selected_domain(home, log, indices);
    assert_maps_equal!(selected(home, log, indices), chronological(home, log, revocations), block => {
        if home.dom().contains(block) {
            chronological_lookup(home, log, revocations, block);
            last_eligible_characterizes_latest(log, revocations, block);
            if let Some(i) = last_eligible(log, revocations, block) {
                let p = choose|p: int| 0 <= p < indices.len() && indices[p] == i;
                selected_target_lookup(home, log, indices, p);
            } else {
                assert forall|p: int| 0 <= p < indices.len() implies
                    (#[trigger] log[indices[p] as int]).block != block by {
                    assert(replay::latest(log, revocations, indices[p] as int));
                }
                selected_frame(home, log, indices, block);
            }
        } else {
            if log.len() > 0 {
                let existing = log[0].block;
                chronological_lookup(home, log, revocations, existing);
            }
        }
    });
}

/// Any interrupted replay may have changed its selected targets arbitrarily.
/// The immutable log still repairs them; other home blocks must be framed.
pub open spec fn replay_partial(before: Disk, partial: Disk, log: Seq<WriteView>, indices: Seq<usize>) -> bool {
    &&& partial.dom() == before.dom()
    &&& (forall|block: u32| before.dom().contains(block)
        && (forall|p: int| 0 <= p < indices.len() ==> (#[trigger] log[indices[p] as int]).block != block)
        ==> #[trigger] partial[block] == before[block])
}

pub proof fn interrupted_replay_is_restartable(before: Disk, partial: Disk, plan: &replay::ReplayPlan)
    requires plan.refines(), all_targets_exist(before, plan.log()),
        replay_partial(before, partial, plan.log(), plan.selection()),
    ensures selected(partial, plan.log(), plan.selection()) == chronological(before, plan.log(), plan.revocations()),
{
    let log = plan.log();
    let indices = plan.selection();
    assert forall|p: int| 0 <= p < indices.len() implies (#[trigger] indices[p]) < log.len() by {
        assert(replay::latest(log, plan.revocations(), indices[p] as int));
    }
    assert(all_targets_exist(partial, log));
    selected_domain(before, log, indices);
    selected_domain(partial, log, indices);
    assert_maps_equal!(selected(partial, log, indices), selected(before, log, indices), block => {
        if before.dom().contains(block) {
            if exists|p: int| 0 <= p < indices.len() && log[indices[p] as int].block == block {
                let p = choose|p: int| 0 <= p < indices.len() && log[indices[p] as int].block == block;
                selected_target_lookup(before, log, indices, p);
                selected_target_lookup(partial, log, indices, p);
            } else {
                assert forall|p: int| 0 <= p < indices.len() implies
                    (#[trigger] log[indices[p] as int]).block != block by { }
                selected_frame(before, log, indices, block);
                selected_frame(partial, log, indices, block);
                assert(partial[block] == before[block]);
            }
        }
    });
    executable_selection_equals_chronological_redo(before, plan);
}

}
