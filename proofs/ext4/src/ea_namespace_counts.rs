// SPDX-License-Identifier: MPL-2.0

//! Exact references and dot/parent counts over the complete EA namespace index.
//! Slot arithmetic reuses the source-independent namespace counting model.

use vstd::prelude::*;
use crate::{block_claims, ea_directory_index::{self as directory_index, DirectoryIndex, IndexView},
    name_set, namespace_counts::{Slot, SlotView, zero, is_dot, is_dotdot, step, fold,
        prefix_counts_are_bounded, views, matching, dot_ok, dots_valid}};

verus! {

fn check_dot(name: &[u8]) -> (r: bool) ensures r == is_dot(name@) {
    if name.len() != 1 { return false; }
    let result = name[0] == 46;
    if result { assert(name@ =~= seq![46u8]); }
    result
}

fn check_dotdot(name: &[u8]) -> (r: bool) ensures r == is_dotdot(name@) {
    if name.len() != 2 { return false; }
    let result = name[0] == 46 && name[1] == 46;
    if result { assert(name@ =~= seq![46u8, 46u8]); }
    result
}

pub struct CountsView { pub index: IndexView, pub slots: Seq<SlotView> }

#[verifier::opaque]
pub open spec fn valid(v: CountsView) -> bool {
    &&& directory_index::valid(v.index) && v.index.entries.len() <= name_set::MAX_KEYS
    &&& v.slots.len() == v.index.nodes.slots.len() && v.slots.len() <= block_claims::MAX_BLOCKS as nat + 1
    &&& matching(v.slots, v.index.entries, v.index.entries.len())
    &&& dots_valid(v.index.entries, v.index.entries.len())
}

pub struct Counts { index: Ghost<IndexView>, slots: Vec<Slot> }

impl Counts {
    pub closed spec fn view(&self) -> CountsView { CountsView { index: self.index@, slots: views(self.slots@) } }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn get(&self, number: u32) -> (r: Option<Slot>)
        ensures self.wf(), match r {
            Some(slot) => number < self.view().slots.len() && slot.view() == self.view().slots[number as int],
            None => number >= self.view().slots.len(),
        },
    {
        proof { use_type_invariant(self); }
        if number as usize >= self.slots.len() { None } else { Some(self.slots[number as usize]) }
    }
}

pub fn collect(index: &DirectoryIndex<'_>) -> (r: Option<Counts>)
    ensures index.wf(), match r { Some(counts) => counts.wf() && counts.view().index == index.view(), None => true },
{
    let capacity = index.nodes().len();
    if capacity < 3 || capacity > block_claims::MAX_BLOCKS as usize + 1 { return None; }
    let inodes = (capacity - 1) as u32;
    let length = index.len();
    let mut slots = Vec::<Slot>::new();
    let mut n = 0usize;
    while n < capacity
        invariant n == slots.len(), n <= capacity <= block_claims::MAX_BLOCKS as nat + 1,
            forall|i: int| 0 <= i < n ==> #[trigger] views(slots@)[i] == zero(),
        decreases capacity - n,
    {
        let ghost previous = slots@;
        slots.push(Slot { references: 0, dots: 0, dotdots: 0, incoming: 0, parent: 0, named_parent: 0 });
        assert forall|j: int| 0 <= j < n + 1 implies #[trigger] views(slots@)[j] == zero() by {
            if j < n {
                assert(views(previous)[j] == zero());
                assert(slots@[j] == previous[j]);
            }
        }
        n += 1;
    }
    assert(matching(views(slots@), index.view().entries, 0)) by {
        reveal(matching);
        assert forall|number: u32| number < slots.len() implies #[trigger] views(slots@)[number as int] == fold(index.view().entries, 0, number) by {
            reveal(fold);
        }
    }
    assert(dots_valid(index.view().entries, 0)) by { reveal(dots_valid); }
    let mut i = 0usize;
    while i < length
        invariant index.wf(), directory_index::valid(index.view()), capacity == index.view().nodes.slots.len(), capacity == inodes as nat + 1,
            slots.len() == capacity <= block_claims::MAX_BLOCKS as nat + 1,
            i <= length <= name_set::MAX_KEYS, length == index.view().entries.len(),
            matching(views(slots@), index.view().entries, i as nat), dots_valid(index.view().entries, i as nat),
        decreases length - i,
    {
        let entry = index.get(i).unwrap();
        let ghost current = entry.view();
        let (directory, target, _, file_type) = entry.identity();
        let (logical, record) = entry.location();
        let name = entry.name();
        assert(name@ == current.name);
        let dot = check_dot(name);
        let dotdot = check_dotdot(name);
        assert(dot == is_dot(current.name) && dotdot == is_dotdot(current.name));
        if (dot && (target != directory || file_type != 2 || logical != 0 || record != 0))
            || (dotdot && (file_type != 2 || logical != 0 || record != 1)) { return None; }
        assert(dot_ok(current));
        let named = !dot && !dotdot && file_type == 2;
        assert(directory_index::entry_ok(index.view(), entry.view()));
        assert(0 < directory <= inodes && 0 < target <= inodes);
        let ghost before = views(slots@);
        proof {
            prefix_counts_are_bounded(index.view().entries, i as nat, target);
            prefix_counts_are_bounded(index.view().entries, i as nat, directory);
        }
        assert(before[target as int] == fold(index.view().entries, i as nat, target)) by { reveal(matching); }
        assert(before[directory as int] == fold(index.view().entries, i as nat, directory)) by { reveal(matching); }
        let mut target_slot = slots[target as usize];
        assert(target_slot.view() == before[target as int]);
        assert(target_slot.references <= i && target_slot.incoming <= i);
        target_slot.references += 1;
        if named { target_slot.incoming += 1; target_slot.named_parent = directory; }
        slots.set(target as usize, target_slot);
        let mut directory_slot = slots[directory as usize];
        assert(directory_slot.dots as nat == before[directory as int].dots && directory_slot.dotdots as nat == before[directory as int].dotdots);
        if dot { directory_slot.dots += 1; }
        if dotdot { directory_slot.dotdots += 1; directory_slot.parent = target; }
        slots.set(directory as usize, directory_slot);
        assert(matching(views(slots@), index.view().entries, i as nat + 1)) by {
            reveal(matching);
            assert forall|number: u32| number < slots.len() implies #[trigger] views(slots@)[number as int]
                == fold(index.view().entries, i as nat + 1, number) by {
                assert(before[number as int] == fold(index.view().entries, i as nat, number));
                if number != directory && number != target { assert(views(slots@)[number as int] == before[number as int]); }
                assert(views(slots@)[number as int] == step(before[number as int], current, number));
                assert(fold(index.view().entries, i as nat + 1, number) == step(fold(index.view().entries, i as nat, number), current, number)) by { reveal(fold); }
            }
        }
        assert(dots_valid(index.view().entries, i as nat + 1)) by {
            reveal(dots_valid);
            assert forall|j: int| 0 <= j < i + 1 implies #[trigger] dot_ok(index.view().entries[j]) by {
                if j < i { assert(dot_ok(index.view().entries[j])); }
            }
        }
        i += 1;
    }
    let ghost assembled = CountsView { index: index.view(), slots: views(slots@) };
    assert(valid(assembled)) by { reveal(valid); }
    Some(Counts { index: Ghost(index.view()), slots })
}

}
