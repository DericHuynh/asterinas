// SPDX-License-Identifier: MPL-2.0

//! Immutable ordinary namespace inode metadata over an actual EA-enabled
//! allocation certificate. EA values, the journal and reserved slots receive
//! no active namespace entry. This supplies no mounted or credential authority.

use vstd::prelude::*;
use crate::{block_claims, bytes, ea_allocation::{self, Allocation, AllocationView},
    ea_integrity, ea_ordinary::{self, OrdinaryView}, ea_parent, ea_source,
    feature_policy};

verus! {

#[derive(Clone, Copy)]
pub struct Node {
    pub number: u32, pub ordinal: usize, pub mode: u16, pub links: u16, pub generation: u32,
}
pub open spec fn matches(node: Node, ordinary: OrdinaryView) -> bool {
    node.number == ordinary.parent.node.number && node.mode as nat == bytes::le16(ordinary.parent.node.raw, 0)
        && node.links as nat == bytes::le16(ordinary.parent.node.raw, 26)
        && node.generation as nat == bytes::le32(ordinary.parent.node.raw, 100)
        && node.mode != 0 && node.links > 0
        && (node.mode & 0xf000 == 0x8000 || node.mode & 0xf000 == 0x4000)
}
pub struct TableView { pub volume: AllocationView, pub slots: Seq<Node> }
pub open spec fn active(v: TableView, number: u32) -> bool {
    0 < number < v.slots.len() && v.slots[number as int].mode != 0
}
pub open spec fn is_directory(v: TableView, number: u32) -> bool {
    active(v, number) && v.slots[number as int].mode & 0xf000 == 0x4000
}
#[verifier::opaque]
pub open spec fn valid(v: TableView) -> bool {
    &&& ea_allocation::valid(v.volume)
    &&& v.slots.len() == v.volume.integrity.references.index.header.inodes as nat + 1
    &&& 3 <= v.slots.len() <= block_claims::MAX_BLOCKS as nat + 1
    &&& v.slots[0].mode == 0
    &&& (forall|n: int| 0 <= n < v.slots.len() ==> (#[trigger] v.slots[n]).number as int == n)
    &&& (forall|n: int| 0 <= n < v.slots.len() && (#[trigger] v.slots[n]).mode != 0 ==>
        v.slots[n].ordinal < v.volume.ordinary.len()
        && matches(v.slots[n], v.volume.ordinary[v.slots[n].ordinal as int]))
    &&& (forall|i: int| #![trigger v.volume.ordinary[i]] 0 <= i < v.volume.ordinary.len() ==> {
        let number = v.volume.ordinary[i].parent.node.number;
        &&& 0 < number < v.slots.len()
        &&& v.slots[number as int].ordinal == i
        &&& matches(v.slots[number as int], v.volume.ordinary[i])
    })
}

pub struct Nodes { slots: Vec<Node>, dir_nlink: bool, checked: Ghost<TableView> }
impl Nodes {
    pub closed spec fn view(&self) -> TableView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        valid(self.view()) && self.slots@ == self.view().slots
            && self.dir_nlink == feature_policy::dir_nlink(self.view().volume.integrity.references.index.header.source.subrange(1024, 2048))
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn len(&self) -> (r: usize)
        ensures self.wf(), valid(self.view()), r == self.view().slots.len(), 3 <= r <= block_claims::MAX_BLOCKS as nat + 1,
    { proof { use_type_invariant(self); reveal(valid); } self.slots.len() }
    pub fn get(&self, number: u32) -> (r: Option<Node>)
        ensures self.wf(), valid(self.view()), match r {
            Some(node) => active(self.view(), number) && node == self.view().slots[number as int]
                && node.number == number && node.ordinal < self.view().volume.ordinary.len()
                && matches(node, self.view().volume.ordinary[node.ordinal as int]),
            None => !active(self.view(), number),
        },
    {
        proof { use_type_invariant(self); reveal(valid); }
        if number == 0 || number as usize >= self.slots.len() || self.slots[number as usize].mode == 0 { None }
        else { Some(self.slots[number as usize]) }
    }
    pub fn slots(&self) -> (r: &[Node])
        ensures self.wf(), valid(self.view()), r@ == self.view().slots,
    { proof { use_type_invariant(self); } &self.slots }
    pub fn dir_nlink(&self) -> (r: bool)
        ensures self.wf(), valid(self.view()),
            r == feature_policy::dir_nlink(self.view().volume.integrity.references.index.header.source.subrange(1024, 2048)),
    { proof { use_type_invariant(self); } self.dir_nlink }
}

proof fn ordinary_at_has_exact_source_index(volume: AllocationView, ordinal: int)
    requires ea_allocation::valid(volume), 0 <= ordinal < volume.ordinary.len(),
    ensures ea_ordinary::valid(volume.ordinary[ordinal]),
        volume.ordinary[ordinal].index == volume.integrity.references.index,
{
    reveal(ea_allocation::valid);
    assert(ea_ordinary::valid(volume.ordinary[ordinal]));
}
proof fn source_node_is_the_ordinary_node(ordinary: OrdinaryView, source: ea_source::NodeView)
    requires ea_ordinary::valid(ordinary), ea_source::node_valid(source),
        source.header == ordinary.index.header, source.number == ordinary.parent.node.number,
    ensures source == ordinary.parent.node,
{
    reveal(ea_ordinary::valid); reveal(ea_parent::valid);
    ea_integrity::same_source_ea_inode_number_identifies_one_exact_node(source, ordinary.parent.node);
}

// The public header API reports absolute snapshot offsets, while the feature
// policy operates on the 1024-byte primary superblock. Bind those views through
// the four actual source bytes rather than assuming a cached feature flag.
proof fn primary_header_dir_nlink_is_the_absolute_source_bit(header: ea_source::HeaderView)
    requires ea_source::header_valid(header),
    ensures 8192 <= header.source.len(),
        feature_policy::dir_nlink(header.source.subrange(1024, 2048))
            == (bytes::le32(header.source, 1124) as u32 & 0x20u32 != 0),
{
    reveal(ea_source::header_valid);
    assert(bytes::le32(header.source.subrange(1024, 2048), 100)
        == bytes::le32(header.source, 1124));
}

pub fn build(volume: &Allocation<'_, '_>) -> (r: Option<Nodes>)
    ensures volume.wf(), ea_allocation::valid(volume.view()), match r {
        Some(nodes) => nodes.wf() && valid(nodes.view()) && nodes.view().volume == volume.view(), None => true },
{
    let count = volume.ordinary_count();
    let index = volume.integrity().reference_census().index();
    let (_, inodes, _, _) = index.parameters();
    if inodes < 2 || inodes > block_claims::MAX_BLOCKS { return None; }
    let header = index.header();
    let (_, ro_flags, _) = header.feature_flags(); let dir_nlink = ro_flags & 0x20 != 0;
    proof {
        assert(header.view() == volume.view().integrity.references.index.header);
        primary_header_dir_nlink_is_the_absolute_source_bit(header.view());
    }
    assert(dir_nlink == feature_policy::dir_nlink(volume.view().integrity.references.index.header.source.subrange(1024, 2048)));
    let length = inodes as usize + 1;
    let ghost vv = volume.view();
    let mut slots: Vec<Node> = Vec::new(); let mut number = 0usize;
    while number < length
        invariant volume.wf(), ea_allocation::valid(vv), volume.view() == vv,
            length == inodes as nat + 1, inodes <= block_claims::MAX_BLOCKS, inodes >= 2,
            number <= length, slots.len() == number,
            forall|n: int| 0 <= n < number ==> (#[trigger] slots@[n]).number as int == n && slots@[n].mode == 0,
        decreases length - number,
    {
        slots.push(Node { number: number as u32, ordinal: 0, mode: 0, links: 0, generation: 0 }); number += 1;
    }
    let mut ordinal = 0usize;
    while ordinal < count
        invariant volume.wf(), ea_allocation::valid(vv), volume.view() == vv,
            index.wf(), index.view() == vv.integrity.references.index,
            inodes == index.view().header.inodes, length == inodes as nat + 1,
            2 <= inodes <= block_claims::MAX_BLOCKS, slots.len() == length,
            count == vv.ordinary.len(), ordinal <= count, slots@[0].mode == 0,
            dir_nlink == feature_policy::dir_nlink(vv.integrity.references.index.header.source.subrange(1024, 2048)),
            forall|n: int| 0 <= n < slots.len() ==> (#[trigger] slots@[n]).number as int == n,
            forall|n: int| 0 <= n < slots.len() && (#[trigger] slots@[n]).mode != 0 ==>
                slots@[n].ordinal < ordinal && matches(slots@[n], vv.ordinary[slots@[n].ordinal as int]),
            forall|i: int| #![trigger vv.ordinary[i]] 0 <= i < ordinal ==> {
                let n = vv.ordinary[i].parent.node.number;
                &&& 0 < n < slots.len()
                &&& slots@[n as int].ordinal == i
                &&& matches(slots@[n as int], vv.ordinary[i])
            },
        decreases count - ordinal,
    {
        let ordinary = volume.ordinary(ordinal).unwrap(); let n = ordinary.number();
        proof { ordinary_at_has_exact_source_index(vv, ordinal as int); }
        if n == 0 || n > inodes || slots[n as usize].mode != 0 { return None; }
        let source = match index.node(n) { Some(source) => source, None => { return None; } };
        let raw = source.raw(); let mode = bytes::read_le16(raw, 0).unwrap(); let links = bytes::read_le16(raw, 26).unwrap();
        let generation = bytes::read_le32(raw, 100).unwrap();
        if mode == 0 || links == 0 || (mode & 0xf000 != 0x8000 && mode & 0xf000 != 0x4000) { return None; }
        proof { source_node_is_the_ordinary_node(ordinary.view(), source.view()); }
        let entry = Node { number: n, ordinal, mode, links, generation };
        assert(matches(entry, vv.ordinary[ordinal as int]));
        let ghost before = slots@;
        slots[n as usize] = entry;
        assert(slots@ == before.update(n as int, entry));
        assert forall|k: int| 0 <= k < slots.len() implies (#[trigger] slots@[k]).number as int == k by {
            if k != n { assert(slots@[k] == before[k]); }
        }
        assert forall|k: int| 0 <= k < slots.len() && (#[trigger] slots@[k]).mode != 0 implies
            slots@[k].ordinal < ordinal + 1 && matches(slots@[k], vv.ordinary[slots@[k].ordinal as int]) by {
            if k == n { assert(slots@[k] == entry); }
            else {
                assert(slots@[k] == before[k]);
                assert(matches(before[k], vv.ordinary[before[k].ordinal as int]));
            }
        }
        assert forall|i: int| #![trigger vv.ordinary[i]] 0 <= i < ordinal + 1 implies {
            let k = vv.ordinary[i].parent.node.number;
            &&& 0 < k < slots.len()
            &&& slots@[k as int].ordinal == i
            &&& matches(slots@[k as int], vv.ordinary[i])
        } by {
            if i < ordinal {
                let k = vv.ordinary[i].parent.node.number;
                assert(matches(before[k as int], vv.ordinary[i]));
                assert(before[k as int].mode != 0);
                assert(k != n);
                assert(slots@[k as int] == before[k as int]);
            } else { assert(i == ordinal && vv.ordinary[i].parent.node.number == n); }
        }
        assert(slots@[0] == before[0]);
        ordinal += 1;
    }
    let ghost view = TableView { volume: vv, slots: slots@ };
    assert(valid(view)) by { reveal(valid); }
    Some(Nodes { slots, dir_nlink, checked: Ghost(view) })
}

pub proof fn every_active_namespace_node_matches_one_exact_source_ordinary_inode(v: TableView, number: u32)
    requires valid(v), active(v, number),
    ensures v.slots[number as int].number == number,
        v.slots[number as int].ordinal < v.volume.ordinary.len(),
        matches(v.slots[number as int], v.volume.ordinary[v.slots[number as int].ordinal as int]),
{
    reveal(valid);
    assert(v.slots[number as int].mode != 0);
}
pub proof fn every_ordinary_inode_has_its_namespace_node(v: TableView, ordinal: int)
    requires valid(v), 0 <= ordinal < v.volume.ordinary.len(),
    ensures 0 < v.volume.ordinary[ordinal].parent.node.number < v.slots.len(),
        active(v, v.volume.ordinary[ordinal].parent.node.number),
        matches(v.slots[v.volume.ordinary[ordinal].parent.node.number as int], v.volume.ordinary[ordinal]),
        v.slots[v.volume.ordinary[ordinal].parent.node.number as int].ordinal == ordinal,
{
    reveal(valid);
    let n = v.volume.ordinary[ordinal].parent.node.number;
    assert(matches(v.slots[n as int], v.volume.ordinary[ordinal]));
}
pub proof fn ordinary_namespace_nodes_have_positive_links_and_supported_types(v: TableView, number: u32)
    requires valid(v), active(v, number),
    ensures v.slots[number as int].links > 0,
        v.slots[number as int].mode & 0xf000 == 0x8000 || v.slots[number as int].mode & 0xf000 == 0x4000,
{
    every_active_namespace_node_matches_one_exact_source_ordinary_inode(v, number);
}
pub proof fn namespace_node_generations_are_the_exact_source_inode_generation(v: TableView, number: u32)
    requires valid(v), active(v, number),
    ensures v.slots[number as int].generation as nat == bytes::le32(
        v.volume.ordinary[v.slots[number as int].ordinal as int].parent.node.raw, 100),
{
    every_active_namespace_node_matches_one_exact_source_ordinary_inode(v, number);
}

pub proof fn distinct_ordinary_source_ordinals_have_distinct_namespace_numbers(v: TableView, a: int, b: int)
    requires valid(v), 0 <= a < v.volume.ordinary.len(), 0 <= b < v.volume.ordinary.len(),
        v.volume.ordinary[a].parent.node.number == v.volume.ordinary[b].parent.node.number,
    ensures a == b,
{
    every_ordinary_inode_has_its_namespace_node(v, a);
    every_ordinary_inode_has_its_namespace_node(v, b);
}

pub proof fn journal_and_reserved_slots_have_no_namespace_node(v: TableView, number: u32)
    requires valid(v), number <= 10, number != 2,
    ensures !active(v, number),
{
    reveal(valid);
    if active(v, number) {
        every_active_namespace_node_matches_one_exact_source_ordinary_inode(v, number);
        let ordinal = v.slots[number as int].ordinal;
        ordinary_at_has_exact_source_index(v.volume, ordinal as int);
        let ordinary = v.volume.ordinary[ordinal as int];
        reveal(ea_ordinary::valid); reveal(ea_parent::valid);
        assert(ordinary.parent.node.number == number);
        assert(ordinary.parent.node.number == 2 || ordinary.parent.node.number >= 11);
        assert(false);
    }
}

pub proof fn ea_value_inodes_have_no_namespace_node(v: TableView, value: int)
    requires valid(v), 0 <= value < v.volume.integrity.values.len(),
    ensures !active(v, v.volume.integrity.values[value].info.number),
{
    reveal(valid); reveal(ea_allocation::valid); reveal(ea_integrity::valid);
    let stored = v.volume.integrity.values[value];
    assert(crate::ea_storage::valid(stored));
    reveal(crate::ea_storage::valid);
    let number = stored.info.number;
    if active(v, number) {
        every_active_namespace_node_matches_one_exact_source_ordinary_inode(v, number);
        let ordinal = v.slots[number as int].ordinal;
        ordinary_at_has_exact_source_index(v.volume, ordinal as int);
        let ordinary = v.volume.ordinary[ordinal as int];
        reveal(ea_ordinary::valid); reveal(ea_parent::valid);
        assert(ordinary.parent.node.number == number);
        assert(stored.node.header == ordinary.parent.node.header);
        ea_integrity::same_source_ea_inode_number_identifies_one_exact_node(stored.node, ordinary.parent.node);
        assert(stored.node.raw == ordinary.parent.node.raw);
        assert(crate::ea_inode::represents(stored.info, stored.node.raw));
        let h = ordinary.parent.node.header;
        assert(stored.info.number == ordinary.parent.node.number);
        assert(stored.info.inodes == h.inodes && stored.info.seed == h.seed);
        assert(crate::inode::metadata_accepted_with_features(stored.node.raw,
            stored.info.number, stored.info.inodes, stored.info.seed, ea_parent::huge(h)));
        crate::ea_inode::ordinary_inode_metadata_does_not_admit_ea_value_inodes(
            stored.node.raw, stored.info.number, stored.info.inodes, stored.info.seed,
            stored.info.status, ea_parent::huge(h));
        assert(false);
    }
}

}
