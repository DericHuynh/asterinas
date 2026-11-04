// SPDX-License-Identifier: MPL-2.0

//! Exact namespace reference/dot/parent accounting from the complete directory
//! index. This is a checked intermediate certificate for topology validation;
//! link-count agreement and rootedness are checked by the next layer.

use vstd::prelude::*;
use crate::{block_claims, directory_index::{self, DirectoryIndex, IndexView},
    name_set, namespace_model::{self as model, EntryView}};

verus! {

pub struct SlotView { pub references: nat, pub dots: nat, pub dotdots: nat, pub incoming: nat, pub parent: u32, pub named_parent: u32 }

#[derive(Clone, Copy)]
pub struct Slot { pub references: u32, pub dots: u32, pub dotdots: u32, pub incoming: u32, pub parent: u32, pub named_parent: u32 }

impl Slot {
    pub open spec fn view(&self) -> SlotView {
        SlotView { references: self.references as nat, dots: self.dots as nat, dotdots: self.dotdots as nat,
            incoming: self.incoming as nat, parent: self.parent, named_parent: self.named_parent }
    }
}

pub open spec fn zero() -> SlotView { SlotView { references: 0, dots: 0, dotdots: 0, incoming: 0, parent: 0, named_parent: 0 } }
pub open spec fn is_dot(name: Seq<u8>) -> bool { name == seq![46u8] }
pub open spec fn is_dotdot(name: Seq<u8>) -> bool { name == seq![46u8, 46u8] }
pub open spec fn normal_directory(e: EntryView) -> bool { e.file_type == 2 && !is_dot(e.name) && !is_dotdot(e.name) }

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

pub open spec fn step(slot: SlotView, e: EntryView, number: u32) -> SlotView {
    SlotView {
        references: slot.references + if e.target == number { 1nat } else { 0nat },
        dots: slot.dots + if e.directory == number && is_dot(e.name) { 1nat } else { 0nat },
        dotdots: slot.dotdots + if e.directory == number && is_dotdot(e.name) { 1nat } else { 0nat },
        incoming: slot.incoming + if e.target == number && normal_directory(e) { 1nat } else { 0nat },
        parent: if e.directory == number && is_dotdot(e.name) { e.target } else { slot.parent },
        named_parent: if e.target == number && normal_directory(e) { e.directory } else { slot.named_parent },
    }
}

#[verifier::opaque]
pub open spec fn fold(entries: Seq<EntryView>, count: nat, number: u32) -> SlotView
    decreases count,
{
    if count == 0 { zero() } else { step(fold(entries, (count - 1) as nat, number), entries[count as int - 1], number) }
}

pub proof fn prefix_counts_are_bounded(entries: Seq<EntryView>, count: nat, number: u32)
    requires count <= entries.len(),
    ensures fold(entries, count, number).references <= count, fold(entries, count, number).dots <= count,
        fold(entries, count, number).dotdots <= count, fold(entries, count, number).incoming <= count,
    decreases count,
{
    reveal(fold);
    if count > 0 { prefix_counts_are_bounded(entries, (count - 1) as nat, number); }
}

pub open spec fn views(slots: Seq<Slot>) -> Seq<SlotView> { Seq::new(slots.len(), |i: int| slots[i].view()) }

#[verifier::opaque]
pub open spec fn matching(slots: Seq<SlotView>, entries: Seq<EntryView>, count: nat) -> bool {
    forall|n: u32| n < slots.len() ==> #[trigger] slots[n as int] == fold(entries, count, n)
}

pub open spec fn dot_ok(e: EntryView) -> bool {
    (is_dot(e.name) ==> e.target == e.directory && e.file_type == 2 && e.logical == 0 && e.record == 0)
        && (is_dotdot(e.name) ==> e.file_type == 2 && e.logical == 0 && e.record == 1)
}

#[verifier::opaque]
pub open spec fn dots_valid(entries: Seq<EntryView>, count: nat) -> bool {
    forall|i: int| 0 <= i < count ==> #[trigger] dot_ok(entries[i])
}

pub struct CountsView { pub index: IndexView, pub slots: Seq<SlotView> }

#[verifier::opaque]
pub open spec fn valid(v: CountsView) -> bool {
    &&& directory_index::valid(v.index) && v.index.entries.len() <= name_set::MAX_KEYS
    &&& v.slots.len() == v.index.volume.index.inodes as nat + 1 && v.slots.len() <= block_claims::MAX_BLOCKS as nat + 1
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

pub fn collect(index: &DirectoryIndex<'_, '_>) -> (r: Option<Counts>)
    ensures index.wf(), match r { Some(counts) => counts.wf() && counts.view().index == index.view(), None => true },
{
    let (_, inodes, _, _) = index.volume().index().parameters();
    if inodes > block_claims::MAX_BLOCKS { return None; }
    let length = index.len();
    let capacity = inodes as usize + 1;
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
        invariant index.wf(), inodes == index.view().volume.index.inodes, capacity == inodes as nat + 1,
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
        assert(model::entry_ok(index.view().volume, entry.view())) by { reveal(directory_index::valid); reveal(model::entries_typed); }
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
