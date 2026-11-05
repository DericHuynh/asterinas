// SPDX-License-Identifier: MPL-2.0

//! Complete bounded EA-enabled physical ownership and allocation inspection.
//! Namespace topology, actual JBD2 state, filesystem operations, durability,
//! mounted permissions and CortenMM/OSTD/device refinement remain separate.

use vstd::prelude::*;
use crate::{block_claims::{self, Census, CensusView, Claim}, bytes,
    ea_allocation_counts as counts, ea_census, ea_index::{self, IndexView},
    ea_integrity::{self, Integrity, IntegrityView}, ea_journal::{self, Journal, JournalView},
    ea_ordinary::{self, Ordinary, OrdinaryView}, ea_reservations, ea_source::{self, NodeView},
    ea_storage, layout::JournalLayout, snapshot::Snapshot};

verus! {

pub enum Class { Empty, Reserved(NodeView), Value(NodeView, usize), Journal(NodeView), Ordinary(OrdinaryView) }
#[verifier::opaque]
pub open spec fn class_valid(integrity: IntegrityView, journal: JournalView, number: u32, class: Class) -> bool {
    let index = integrity.references.index;
    &&& 0 < number <= index.header.inodes
    &&& match class {
        Class::Empty => number > 10 && !ea_index::inode_allocated(index, number),
        Class::Reserved(node) => ea_index::inode_allocated(index, number) && number <= 10 && number != 2 && number != 8
            && ea_source::node_valid(node) && node.header == index.header && node.number == number && ea_census::reserved_ok(node),
        Class::Value(node, stored) => ea_index::inode_allocated(index, number) && (number >= 11 || number == 3 || number == 4)
            && stored < integrity.values.len() && node == integrity.values[stored as int].node
            && node.number == number && node.header == index.header && ea_storage::valid(integrity.values[stored as int]),
        Class::Journal(node) => number == 8 && node == journal.node && ea_journal::valid(journal) && journal.index == index,
        Class::Ordinary(ordinary) => ea_ordinary::valid(ordinary) && ordinary.index == index && ordinary.parent.node.number == number,
    }
}
pub open spec fn ordinary_projection(classes: Seq<Class>) -> Seq<OrdinaryView> decreases classes.len() {
    if classes.len() == 0 { Seq::empty() } else {
        let previous = ordinary_projection(classes.drop_last());
        match classes.last() { Class::Ordinary(ordinary) => previous.push(ordinary), _ => previous }
    }
}
pub open spec fn ordinary_claims(ordinary: Seq<OrdinaryView>) -> Seq<Claim> decreases ordinary.len() {
    if ordinary.len() == 0 { Seq::empty() } else { ordinary_claims(ordinary.drop_last()) + ordinary.last().claims }
}
pub open spec fn fixed_claims(integrity: IntegrityView, journal: JournalView) -> Seq<Claim> {
    integrity.ownership.claims + ea_reservations::reserved(integrity.references.index, integrity.references.index.groups.len())
        + seq![ea_journal::claim(journal.layout)]
}
pub struct AllocationView {
    pub integrity: IntegrityView, pub journal: JournalView, pub ledger: CensusView,
    pub classes: Seq<Class>, pub ordinary: Seq<OrdinaryView>,
}
#[verifier::opaque]
pub open spec fn valid(v: AllocationView) -> bool {
    let index = v.integrity.references.index;
    &&& ea_integrity::valid(v.integrity)
    &&& ea_journal::valid(v.journal) && v.journal.index == index
    &&& block_claims::ledger(v.ledger.roles, v.ledger.claims) && v.ledger.roles.len() == index.header.blocks
    &&& block_claims::preserves_occupied(v.integrity.ownership.roles, v.ledger.roles)
    &&& v.classes.len() == index.header.inodes
    &&& (forall|i: int| 0 <= i < v.classes.len() ==> #[trigger] class_valid(v.integrity, v.journal, (i + 1) as u32, v.classes[i]))
    &&& v.ordinary == ordinary_projection(v.classes)
    &&& v.ledger.claims == fixed_claims(v.integrity, v.journal) + ordinary_claims(v.ordinary)
        + ea_reservations::external_claims(v.integrity.references.external)
    &&& (forall|i: int| 0 <= i < v.ordinary.len() ==> #[trigger] ea_ordinary::valid(v.ordinary[i])
        && v.ordinary[i].index == index && v.ordinary[i].budget == index.header.blocks as nat + 1
        && block_claims::mapped_claims(v.ledger.roles, v.ordinary[i].claims))
    &&& counts::bitmaps_match(index, v.ledger.roles, index.groups.len())
    &&& counts::directory_counts_match(index, v.ordinary, index.groups.len())
    &&& block_claims::free_roles(v.ledger.roles, 0, v.ledger.roles.len()) == bytes::le32(index.header.source, 1036)
}
proof fn assemble(v: AllocationView)
    requires
    (ea_integrity::valid(v.integrity)),
    (ea_journal::valid(v.journal) && v.journal.index == v.integrity.references.index),
    (block_claims::ledger(v.ledger.roles, v.ledger.claims) && v.ledger.roles.len() == v.integrity.references.index.header.blocks),
    (block_claims::preserves_occupied(v.integrity.ownership.roles, v.ledger.roles)),
    (v.classes.len() == v.integrity.references.index.header.inodes),
    ((forall|i: int| 0 <= i < v.classes.len() ==> #[trigger] class_valid(v.integrity, v.journal, (i + 1) as u32, v.classes[i]))),
    (v.ordinary == ordinary_projection(v.classes)),
    (v.ledger.claims == fixed_claims(v.integrity, v.journal) + ordinary_claims(v.ordinary)
        + ea_reservations::external_claims(v.integrity.references.external)),
    ((forall|i: int| 0 <= i < v.ordinary.len() ==> #[trigger] ea_ordinary::valid(v.ordinary[i])
        && v.ordinary[i].index == v.integrity.references.index && v.ordinary[i].budget == v.integrity.references.index.header.blocks as nat + 1
        && block_claims::mapped_claims(v.ledger.roles, v.ordinary[i].claims))),
    (counts::bitmaps_match(v.integrity.references.index, v.ledger.roles, v.integrity.references.index.groups.len())),
    (counts::directory_counts_match(v.integrity.references.index, v.ordinary, v.integrity.references.index.groups.len())),
    (block_claims::free_roles(v.ledger.roles, 0, v.ledger.roles.len()) == bytes::le32(v.integrity.references.index.header.source, 1036)),
    ensures valid(v),
{ reveal(valid); }


pub struct Allocation<'s, 'a> {
    integrity: Integrity<'s, 'a>, journal: Journal, ledger: Census,
    ordinary: Vec<Ordinary>, checked: Ghost<AllocationView>,
}
impl<'s, 'a> Allocation<'s, 'a> {
    pub closed spec fn view(&self) -> AllocationView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        valid(self.view()) && self.integrity.view() == self.view().integrity && self.journal.view() == self.view().journal
            && self.ledger.view() == self.view().ledger && self.ordinary.len() == self.view().ordinary.len()
            && forall|i: int| 0 <= i < self.ordinary.len() ==> (#[trigger] self.ordinary@[i]).view() == self.view().ordinary[i]
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn integrity(&self) -> (r: &Integrity<'s, 'a>)
        ensures self.wf(), valid(self.view()), r.wf(), r.view() == self.view().integrity,
    { proof { use_type_invariant(self); } let _ = self.integrity.value_count(); &self.integrity }
    pub fn ledger(&self) -> (r: &Census)
        ensures self.wf(), valid(self.view()), r.wf(), r.view() == self.view().ledger,
    { proof { use_type_invariant(self); } let _ = self.ledger.block_count(); &self.ledger }
    pub fn journal(&self) -> (r: &JournalLayout)
        ensures self.wf(), valid(self.view()), r.wf(), r.view() == self.view().journal.layout,
    { proof { use_type_invariant(self); } self.journal.layout() }
    pub fn ordinary_count(&self) -> (r: usize)
        ensures self.wf(), valid(self.view()), r == self.view().ordinary.len(),
    { proof { use_type_invariant(self); } self.ordinary.len() }
    pub fn ordinary(&self, index: usize) -> (r: Option<&Ordinary>)
        ensures self.wf(), valid(self.view()), match r { Some(ordinary) => index < self.view().ordinary.len()
            && ordinary.wf() && ea_ordinary::valid(ordinary.view()) && ordinary.view() == self.view().ordinary[index as int],
            None => index >= self.view().ordinary.len() },
    {
        proof { use_type_invariant(self); }
        if index >= self.ordinary.len() { return None; }
        let ordinary = &self.ordinary[index]; let _ = ordinary.number(); Some(ordinary)
    }
}

fn find_value(integrity: &Integrity<'_, '_>, number: u32) -> (r: Option<usize>)
    ensures integrity.wf(), ea_integrity::valid(integrity.view()), match r {
        Some(i) => i < integrity.view().values.len() && integrity.view().values[i as int].info.number == number
            && ea_storage::valid(integrity.view().values[i as int]), None => true },
{
    let count = integrity.value_count(); let mut i = 0usize;
    while i < count
        invariant integrity.wf(), ea_integrity::valid(integrity.view()), count == integrity.view().values.len(), i <= count,
        decreases count - i,
    {
        let value = integrity.value(i).unwrap();
        if value.info().number == number { return Some(i); }
        i += 1;
    }
    None
}

proof fn integrity_value_index(iv: IntegrityView, stored: usize)
    requires ea_integrity::valid(iv), stored < iv.values.len(),
    ensures ea_storage::valid(iv.values[stored as int]), iv.values[stored as int].index == iv.references.index,
{
    reveal(ea_integrity::valid);
    assert(ea_storage::valid(iv.values[stored as int]));
}
proof fn checked_value_class(iv: IntegrityView, jv: JournalView, number: u32, node: NodeView, stored: usize)
    requires 0 < number <= iv.references.index.header.inodes, number >= 11 || number == 3 || number == 4,
        ea_index::inode_allocated(iv.references.index, number), ea_source::node_valid(node),
        node.header == iv.references.index.header, node.number == number, stored < iv.values.len(),
        ea_storage::valid(iv.values[stored as int]), iv.values[stored as int].index == iv.references.index,
        iv.values[stored as int].info.number == number,
    ensures class_valid(iv, jv, number, Class::Value(node, stored)),
{
    reveal(ea_storage::valid);
    ea_integrity::same_source_ea_inode_number_identifies_one_exact_node(node, iv.values[stored as int].node);
    reveal(class_valid);
}
proof fn checked_journal_class(iv: IntegrityView, jv: JournalView, node: NodeView)
    requires ea_journal::valid(jv), jv.index == iv.references.index, ea_source::node_valid(node),
        node.header == iv.references.index.header, node.number == 8,
    ensures class_valid(iv, jv, 8, Class::Journal(node)),
{
    reveal(ea_journal::valid);
    ea_integrity::same_source_ea_inode_number_identifies_one_exact_node(node, jv.node);
    reveal(class_valid);
}

#[verifier::rlimit(20)]
pub fn inspect<'s, 'a>(source: &'s Snapshot<'a>, inode_budget: u32, node_budget: u64, byte_budget: u64)
    -> (r: Option<Allocation<'s, 'a>>)
    ensures match r { Some(allocation) => allocation.wf() && valid(allocation.view())
        && allocation.view().integrity.references.index.header.source == source.view()
        && allocation.view().integrity.inode_budget == inode_budget && allocation.view().integrity.node_budget == node_budget
        && allocation.view().integrity.byte_budget == byte_budget, None => true },
{
    let integrity = match ea_integrity::inspect(source, inode_budget, node_budget, byte_budget) {
        Some(integrity) => integrity, None => { return None; }
    };
    let references = integrity.reference_census(); let index = references.index();
    let (blocks, inodes, _, seed) = index.parameters(); let huge = index.header().huge_files();
    assert(11 <= inodes <= 1048576) by { reveal(ea_index::valid); }
    let initial = integrity.ledger().duplicate();
    let groups = match ea_reservations::reserve_groups(index, initial) { Some(groups) => groups, None => { return None; } };
    let (mut ledger, journal) = match ea_journal::reserve(index, groups) { Some(pair) => pair, None => { return None; } };
    let ghost iv = integrity.view(); let ghost jv = journal.view(); let ghost prefix = fixed_claims(iv, jv);
    assert(ledger.view().claims =~= prefix);
    assert(block_claims::preserves_occupied(iv.ownership.roles, initial.view().roles)) by { reveal(block_claims::preserves_occupied); }
    proof { block_claims::occupied_slot_preservation_is_transitive(iv.ownership.roles, initial.view().roles, groups.view().roles);
        block_claims::occupied_slot_preservation_is_transitive(iv.ownership.roles, groups.view().roles, ledger.view().roles); }
    let mut ordinary: Vec<Ordinary> = Vec::new(); let mut i = 0usize;
    let ghost mut classes: Seq<Class> = Seq::empty(); let ghost mut checked: Seq<OrdinaryView> = Seq::empty();
    let budget = blocks as u64 + 1;
    assert(ledger.view().claims =~= prefix + ordinary_claims(checked));
    while i < inodes as usize
        invariant integrity.wf(), ea_integrity::valid(iv), integrity.view() == iv,
            journal.wf(), ea_journal::valid(jv), journal.view() == jv, jv.index == iv.references.index,
            references.wf(), references.view() == iv.references, index.wf(), index.view() == iv.references.index,
            blocks == index.view().header.blocks, inodes == index.view().header.inodes,
            seed == index.view().header.seed, huge == crate::ea_parent::huge(index.view().header),
            11 <= inodes <= 1048576, budget as nat == blocks as nat + 1,
            ledger.wf(), ledger.view().roles.len() == blocks,
            block_claims::preserves_occupied(iv.ownership.roles, ledger.view().roles),
            prefix == fixed_claims(iv, jv), ledger.view().claims == prefix + ordinary_claims(checked),
            i <= inodes, classes.len() == i, checked.len() == ordinary.len(), checked == ordinary_projection(classes),
            forall|j: int| 0 <= j < i ==> #[trigger] class_valid(iv, jv, (j + 1) as u32, classes[j]),
            forall|j: int| 0 <= j < ordinary.len() ==> (#[trigger] ordinary@[j]).view() == checked[j],
            forall|j: int| 0 <= j < checked.len() ==> #[trigger] ea_ordinary::valid(checked[j])
                && checked[j].index == index.view() && checked[j].budget == budget
                && block_claims::mapped_claims(ledger.view().roles, checked[j].claims),
        decreases inodes as usize - i,
    {
        let number = (i + 1) as u32; let allocated = index.allocated(number).unwrap();
        let ghost mut class = Class::Empty;
        if !allocated {
            if number <= 10 { return None; }
            assert(class_valid(iv, jv, number, class)) by { reveal(class_valid); }
        }
        else {
            let node = match index.node(number) { Some(node) => node, None => { return None; } };
            if bytes::read_le32(node.raw(), 32).unwrap() & crate::ea_inode::FLAG != 0 {
                if number < 11 && number != 3 && number != 4 { return None; }
                let stored = match find_value(&integrity, number) { Some(stored) => stored, None => { return None; } };
                proof {
                    integrity_value_index(iv, stored);
                    checked_value_class(iv, jv, number, node.view(), stored);
                    class = Class::Value(node.view(), stored);
                }
            } else if number == 8 {
                proof {
                    checked_journal_class(iv, jv, node.view());
                    class = Class::Journal(node.view());
                }
            } else if number == 2 || number >= 11 {
                let ghost prior_roles = ledger.view().roles;
                let (next, entry) = match ea_ordinary::collect(index, number, budget, ledger) { Some(pair) => pair, None => { return None; } };
                proof {
                    block_claims::occupied_slot_preservation_is_transitive(iv.ownership.roles, prior_roles, next.view().roles);
                    assert forall|j: int| 0 <= j < checked.len() implies block_claims::mapped_claims(next.view().roles, checked[j].claims) by {
                        assert(ea_ordinary::valid(checked[j]));
                        assert(block_claims::mapped_claims(prior_roles, checked[j].claims));
                        block_claims::occupied_preservation_keeps_mapped_claims(prior_roles, next.view().roles, checked[j].claims);
                    }
                }
                ledger = next;
                let ghost entry_view = entry.view(); let ghost previous = checked;
                ordinary.push(entry); proof { checked = checked.push(entry_view); class = Class::Ordinary(entry_view); }
                assert(checked.drop_last() =~= previous); assert(checked.last() == entry_view);
                assert(class_valid(iv, jv, number, class)) by { reveal(class_valid); }
                assert(ledger.view().claims == prefix + ordinary_claims(checked));
                assert forall|j: int| 0 <= j < ordinary.len() implies (#[trigger] ordinary@[j]).view() == checked[j] by {
                    if j < previous.len() { assert(ordinary@[j].view() == previous[j]); }
                }
                assert forall|j: int| 0 <= j < checked.len() implies #[trigger] ea_ordinary::valid(checked[j])
                    && checked[j].index == index.view() && checked[j].budget == budget
                    && block_claims::mapped_claims(ledger.view().roles, checked[j].claims) by {
                    if j < previous.len() { assert(checked[j] == previous[j]); }
                }
            } else {
                if !ea_census::check_reserved(node.raw(), number, inodes, seed, huge) { return None; }
                proof { class = Class::Reserved(node.view()); }
                assert(class_valid(iv, jv, number, class)) by { reveal(class_valid); }
            }
        }
        assert(class_valid(iv, jv, number, class));
        let ghost previous = classes; proof { classes = classes.push(class); }
        assert(classes.drop_last() =~= previous); assert(classes.last() == class);
        assert(checked == ordinary_projection(classes));
        i += 1;
    }
    let ghost prior_roles = ledger.view().roles;
    let ledger = match ea_reservations::reserve_external(references, ledger) { Some(ledger) => ledger, None => { return None; } };
    proof {
        block_claims::occupied_slot_preservation_is_transitive(iv.ownership.roles, prior_roles, ledger.view().roles);
        assert forall|j: int| 0 <= j < checked.len() implies block_claims::mapped_claims(ledger.view().roles, checked[j].claims) by {
            assert(ea_ordinary::valid(checked[j]));
            block_claims::occupied_preservation_keeps_mapped_claims(prior_roles, ledger.view().roles, checked[j].claims);
        }
    }
    assert(counts::views(ordinary@) =~= checked);
    if !counts::check(index, &ledger, &ordinary) { return None; }
    let ghost view = AllocationView { integrity: iv, journal: jv, ledger: ledger.view(), classes, ordinary: checked };
    proof { assemble(view); }
    Some(Allocation { integrity, journal, ledger, ordinary, checked: Ghost(view) })
}

pub proof fn every_declared_source_inode_has_a_complete_physical_class(v: AllocationView, number: u32)
    requires valid(v), 0 < number <= v.integrity.references.index.header.inodes,
    ensures class_valid(v.integrity, v.journal, number, v.classes[number as int - 1]),
{
    reveal(valid); let i = number as int - 1;
    assert(class_valid(v.integrity, v.journal, (i + 1) as u32, v.classes[i]));
}
pub proof fn ordinary_claims_are_the_complete_source_inode_projection(v: AllocationView)
    requires valid(v),
    ensures v.ordinary == ordinary_projection(v.classes),
        v.ledger.claims == fixed_claims(v.integrity, v.journal) + ordinary_claims(v.ordinary)
            + ea_reservations::external_claims(v.integrity.references.external),
{ reveal(valid); }
pub proof fn every_ea_storage_claim_retains_its_exact_physical_owner(v: AllocationView, value: int)
    requires valid(v), 0 <= value < v.integrity.values.len(),
    ensures block_claims::mapped_claims(v.ledger.roles, v.integrity.values[value].claims),
{
    reveal(valid); reveal(ea_integrity::valid);
    assert(ea_storage::valid(v.integrity.values[value]));
    block_claims::occupied_preservation_keeps_mapped_claims(v.integrity.ownership.roles, v.ledger.roles, v.integrity.values[value].claims);
}
pub proof fn every_ordinary_inode_has_its_complete_physical_extent_claims(v: AllocationView, index: int)
    requires valid(v), 0 <= index < v.ordinary.len(),
    ensures ea_ordinary::valid(v.ordinary[index]), block_claims::mapped_claims(v.ledger.roles, v.ordinary[index].claims),
{ reveal(valid); assert(ea_ordinary::valid(v.ordinary[index])); }
pub proof fn every_source_block_bitmap_bit_equals_global_physical_ownership(v: AllocationView, block: u32)
    requires valid(v), block < v.integrity.references.index.header.blocks,
    ensures crate::ea_block_policy::allocated(v.integrity.references.index, block) == (v.ledger.roles[block as int].kind != 0),
{
    reveal(valid); reveal(ea_integrity::valid); reveal(ea_census::valid);
    counts::matching_group_bitmaps_identify_every_allocated_physical_block(v.integrity.references.index, v.ledger.roles, block);
}
pub proof fn global_physical_ownership_has_the_exact_primary_free_count(v: AllocationView)
    requires valid(v),
    ensures block_claims::free_roles(v.ledger.roles, 0, v.ledger.roles.len()) == bytes::le32(v.integrity.references.index.header.source, 1036),
{ reveal(valid); }

proof fn ea_value_claim_occurs_in_complete_projection(values: Seq<ea_storage::StoredView>, value: int, entry: int)
    requires 0 <= value < values.len(), 0 <= entry < values[value].claims.len(),
    ensures ea_integrity::claims(values).contains(values[value].claims[entry]),
    decreases values.len(),
{
    let prior = values.drop_last(); let claim = values[value].claims[entry];
    reveal(ea_integrity::claims);
    if value < prior.len() {
        assert(prior[value] == values[value]);
        ea_value_claim_occurs_in_complete_projection(prior, value, entry);
        let k = choose|k: int| 0 <= k < ea_integrity::claims(prior).len() && #[trigger] ea_integrity::claims(prior)[k] == claim;
        assert(ea_integrity::claims(values)[k] == claim);
    } else {
        assert(value == values.len() - 1 && values.last() == values[value]);
        let k = ea_integrity::claims(prior).len() as int + entry;
        assert(ea_integrity::claims(values)[k] == claim);
    }
    assert(ea_integrity::claims(values).contains(claim));
}

proof fn ordinary_claim_occurs_in_complete_projection(ordinary: Seq<OrdinaryView>, inode: int, entry: int)
    requires 0 <= inode < ordinary.len(), 0 <= entry < ordinary[inode].claims.len(),
    ensures ordinary_claims(ordinary).contains(ordinary[inode].claims[entry]),
    decreases ordinary.len(),
{
    let prior = ordinary.drop_last(); let claim = ordinary[inode].claims[entry];
    if inode < prior.len() {
        assert(prior[inode] == ordinary[inode]);
        ordinary_claim_occurs_in_complete_projection(prior, inode, entry);
        let k = choose|k: int| 0 <= k < ordinary_claims(prior).len() && #[trigger] ordinary_claims(prior)[k] == claim;
        assert(ordinary_claims(ordinary)[k] == claim);
    } else {
        assert(inode == ordinary.len() - 1 && ordinary.last() == ordinary[inode]);
        let k = ordinary_claims(prior).len() as int + entry;
        assert(ordinary_claims(ordinary)[k] == claim);
    }
    assert(ordinary_claims(ordinary).contains(claim));
}

proof fn separate_final_claim_positions_have_disjoint_ranges(v: CensusView, left: int, right: int)
    requires block_claims::ledger(v.roles, v.claims), 0 <= left < v.claims.len(),
        0 <= right < v.claims.len(), left != right,
    ensures block_claims::disjoint(v.claims[left], v.claims[right]),
{
    reveal(block_claims::ledger);
    if left < right { assert(block_claims::disjoint(v.claims[left], v.claims[right])); }
    else { assert(block_claims::disjoint(v.claims[right], v.claims[left])); }
}

pub proof fn every_source_journal_block_has_its_final_journal_role(v: AllocationView, block: u32)
    requires valid(v), v.journal.layout.start <= block < v.journal.layout.start as nat + v.journal.layout.journal_blocks,
    ensures block < v.ledger.roles.len(), v.ledger.roles[block as int].kind == 2,
{
    reveal(valid);
    let index = v.integrity.references.index;
    let record = ea_journal::claim(v.journal.layout);
    let p = v.integrity.ownership.claims.len() as int + ea_reservations::reserved(index, index.groups.len()).len() as int;
    assert(fixed_claims(v.integrity, v.journal)[p] == record);
    assert(v.ledger.claims[p] == record);
    assert(v.ledger.claims.contains(record));
    assert(block_claims::covers(record, block as int));
    block_claims::a_ledger_claim_determines_its_exact_physical_slot(v.ledger.roles, v.ledger.claims, record, block as int);
}

pub proof fn every_source_external_xattr_pointer_has_one_final_shared_block_role(v: AllocationView, pointer: int)
    requires valid(v), 0 <= pointer < v.integrity.references.external.len(),
    ensures v.integrity.references.external[pointer].address < v.ledger.roles.len(),
        v.ledger.roles[v.integrity.references.external[pointer].address as int].kind == 7,
{
    reveal(valid);
    let records = v.integrity.references.external;
    let record = ea_reservations::external_claim(records[pointer].address);
    ea_reservations::every_source_external_pointer_occurs_in_the_physical_reservation(records, pointer);
    let extra = ea_reservations::external_claims(records);
    let p = choose|p: int| 0 <= p < extra.len() && #[trigger] extra[p] == record;
    let prefix = fixed_claims(v.integrity, v.journal) + ordinary_claims(v.ordinary);
    assert(v.ledger.claims[prefix.len() as int + p] == record);
    assert(v.ledger.claims.contains(record));
    assert(block_claims::covers(record, record.start as int));
    block_claims::a_ledger_claim_determines_its_exact_physical_slot(v.ledger.roles, v.ledger.claims, record, record.start as int);
}

pub proof fn every_source_reserved_metadata_claim_has_its_exact_final_role(v: AllocationView, group: u32, record: Claim, block: int)
    requires valid(v), group < v.integrity.references.index.groups.len(),
        crate::group_claims::claims_for_source(v.integrity.references.index.header.source,
            v.integrity.references.index.groups[group as int].descriptor, group,
            v.integrity.references.index.header.ipg).contains(record), block_claims::covers(record, block),
    ensures 0 <= block < v.ledger.roles.len(), v.ledger.roles[block] == block_claims::at(record, block),
{
    reveal(valid);
    let index = v.integrity.references.index;
    ea_reservations::every_source_group_claim_occurs_in_the_complete_reservation(index, index.groups.len(), group, record);
    let reserved = ea_reservations::reserved(index, index.groups.len());
    let p = choose|p: int| 0 <= p < reserved.len() && #[trigger] reserved[p] == record;
    let at = v.integrity.ownership.claims.len() as int + p;
    assert(fixed_claims(v.integrity, v.journal)[at] == record);
    assert(v.ledger.claims[at] == record);
    assert(v.ledger.claims.contains(record));
    block_claims::a_ledger_claim_determines_its_exact_physical_slot(v.ledger.roles, v.ledger.claims, record, block);
}

pub proof fn ea_storage_is_disjoint_from_every_ordinary_inode_allocation(v: AllocationView,
    value: int, ea_entry: int, ordinary: int, ordinary_entry: int)
    requires valid(v), 0 <= value < v.integrity.values.len(), 0 <= ea_entry < v.integrity.values[value].claims.len(),
        0 <= ordinary < v.ordinary.len(), 0 <= ordinary_entry < v.ordinary[ordinary].claims.len(),
    ensures block_claims::disjoint(v.integrity.values[value].claims[ea_entry], v.ordinary[ordinary].claims[ordinary_entry]),
{
    reveal(valid); reveal(ea_integrity::valid);
    ea_value_claim_occurs_in_complete_projection(v.integrity.values, value, ea_entry);
    ordinary_claim_occurs_in_complete_projection(v.ordinary, ordinary, ordinary_entry);
    let ea = v.integrity.values[value].claims[ea_entry];
    let other = v.ordinary[ordinary].claims[ordinary_entry];
    let p = choose|p: int| 0 <= p < v.integrity.ownership.claims.len() && #[trigger] v.integrity.ownership.claims[p] == ea;
    let q = choose|q: int| 0 <= q < ordinary_claims(v.ordinary).len() && #[trigger] ordinary_claims(v.ordinary)[q] == other;
    let at = fixed_claims(v.integrity, v.journal).len() as int + q;
    assert(v.ledger.claims[p] == ea);
    assert(v.ledger.claims[at] == other);
    assert(p < at);
    separate_final_claim_positions_have_disjoint_ranges(v.ledger, p, at);
}

pub proof fn ea_storage_is_disjoint_from_the_complete_journal_extent(v: AllocationView, value: int, entry: int)
    requires valid(v), 0 <= value < v.integrity.values.len(), 0 <= entry < v.integrity.values[value].claims.len(),
    ensures block_claims::disjoint(v.integrity.values[value].claims[entry], ea_journal::claim(v.journal.layout)),
{
    reveal(valid); reveal(ea_integrity::valid);
    ea_value_claim_occurs_in_complete_projection(v.integrity.values, value, entry);
    let record = v.integrity.values[value].claims[entry];
    let p = choose|p: int| 0 <= p < v.integrity.ownership.claims.len() && #[trigger] v.integrity.ownership.claims[p] == record;
    let index = v.integrity.references.index;
    let q = v.integrity.ownership.claims.len() as int + ea_reservations::reserved(index, index.groups.len()).len() as int;
    assert(v.ledger.claims[p] == record);
    assert(v.ledger.claims[q] == ea_journal::claim(v.journal.layout));
    assert(p < q);
    separate_final_claim_positions_have_disjoint_ranges(v.ledger, p, q);
}

pub proof fn ea_storage_is_disjoint_from_every_source_external_xattr_block(v: AllocationView, value: int, entry: int, pointer: int)
    requires valid(v), 0 <= value < v.integrity.values.len(), 0 <= entry < v.integrity.values[value].claims.len(),
        0 <= pointer < v.integrity.references.external.len(),
    ensures block_claims::disjoint(v.integrity.values[value].claims[entry],
        ea_reservations::external_claim(v.integrity.references.external[pointer].address)),
{
    reveal(valid); reveal(ea_integrity::valid);
    ea_value_claim_occurs_in_complete_projection(v.integrity.values, value, entry);
    let records = v.integrity.references.external;
    ea_reservations::every_source_external_pointer_occurs_in_the_physical_reservation(records, pointer);
    let extra = ea_reservations::external_claims(records);
    let record = v.integrity.values[value].claims[entry];
    let other = ea_reservations::external_claim(records[pointer].address);
    let p = choose|p: int| 0 <= p < v.integrity.ownership.claims.len() && #[trigger] v.integrity.ownership.claims[p] == record;
    let q = choose|q: int| 0 <= q < extra.len() && #[trigger] extra[q] == other;
    let prefix = fixed_claims(v.integrity, v.journal) + ordinary_claims(v.ordinary);
    let at = prefix.len() as int + q;
    assert(v.ledger.claims[p] == record);
    assert(v.ledger.claims[at] == other);
    assert(p < at);
    separate_final_claim_positions_have_disjoint_ranges(v.ledger, p, at);
}

}
