// SPDX-License-Identifier: MPL-2.0

//! Legacy ext4 s_last_orphan / inode i_dtime links. Source inode lookup,
//! checksum resealing and atomic journal publication belong to the caller;
//! these plans describe exact field changes and do not authorize disk writes.

use vstd::prelude::*;
use crate::{block_size, bytes};

verus! {

pub const INODE_NEXT_OFFSET: usize = 20;
pub const SUPER_HEAD_OFFSET: usize = 232;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Error { Geometry, Inode, Unallocated, Type, Next, Duplicate, Missing, Cycle, Budget, Present, Absent }

pub struct NodeView {
    pub raw: Seq<u8>, pub number: u32, pub next: u32, pub generation: u32, pub mode: u16, pub links: u16,
}
#[verifier::opaque]
pub open spec fn node_valid(v: NodeView) -> bool {
    &&& 128 <= v.raw.len() <= 65536
    &&& (v.raw.len() as usize & ((v.raw.len() - 1) as usize)) == 0 && v.number > 0
    &&& v.next == bytes::le32(v.raw, 20) as u32 && v.generation == bytes::le32(v.raw, 100) as u32
    &&& v.mode == bytes::le16(v.raw, 0) as u16 && v.links == bytes::le16(v.raw, 26) as u16
    &&& v.links != 0 ==> v.mode & 0xf000 == 0x8000 || v.mode & 0xf000 == 0x4000 || v.mode & 0xf000 == 0xa000
}
pub struct ChainView { pub nodes: Seq<NodeView>, pub head: u32, pub inodes: u32 }
#[verifier::opaque]
pub open spec fn valid(v: ChainView) -> bool {
    &&& v.inodes > 0 && v.head <= v.inodes && (v.nodes.len() == 0 <==> v.head == 0)
    &&& forall|i: int| 0 <= i < v.nodes.len() ==> node_valid(#[trigger] v.nodes[i])
        && v.nodes[i].number <= v.inodes && v.nodes[i].next <= v.inodes
    &&& v.nodes.len() > 0 ==> v.nodes[0].number == v.head && v.nodes.last().next == 0
    &&& forall|i: int| 0 <= i < v.nodes.len() - 1 ==> (#[trigger] v.nodes[i]).next == v.nodes[i + 1].number
    &&& forall|i: int, j: int| 0 <= i < j < v.nodes.len() ==> (#[trigger] v.nodes[i]).number != (#[trigger] v.nodes[j]).number
}
pub open spec fn from_catalogue(v: ChainView, catalogue: Seq<NodeView>) -> bool {
    forall|i: int| 0 <= i < v.nodes.len() ==> catalogue.contains(#[trigger] v.nodes[i])
}
pub struct InsertView { pub head_before: u32, pub head_after: u32, pub inode: u32, pub generation: u32, pub next: u32 }
pub open spec fn insert_valid(v: InsertView) -> bool { v.inode > 0 && v.head_after == v.inode && v.next == v.head_before }
pub struct RemoveView { pub head_before: u32, pub head_after: u32, pub inode: u32, pub generation: u32, pub previous: Option<u32>, pub next: u32 }
pub open spec fn remove_valid(v: RemoveView) -> bool {
    v.inode > 0 && match v.previous {
        None => v.head_before == v.inode && v.head_after == v.next,
        Some(number) => number > 0 && number != v.inode && v.head_after == v.head_before,
    }
}

proof fn a_structural_node_has_a_positive_identity(v: NodeView)
    requires node_valid(v),
    ensures v.number > 0,
{ reveal(node_valid); }
proof fn observe_chain_node(v: ChainView, i: int)
    requires valid(v), 0 <= i < v.nodes.len(),
    ensures node_valid(v.nodes[i]), 0 < v.nodes[i].number <= v.inodes,
        v.nodes[i].next <= v.inodes, i == 0 ==> v.nodes[i].number == v.head,
{
    reveal(valid);
    assert(node_valid(v.nodes[i]));
    a_structural_node_has_a_positive_identity(v.nodes[i]);
}
proof fn distinct_chain_indices_have_distinct_identities(v: ChainView, i: int, j: int)
    requires valid(v), 0 <= i < v.nodes.len(), 0 <= j < v.nodes.len(), i != j,
    ensures v.nodes[i].number != v.nodes[j].number,
{
    reveal(valid);
    if i < j { assert(v.nodes[i].number != v.nodes[j].number); }
    else { assert(v.nodes[j].number != v.nodes[i].number); }
}

/// Structural legacy-link envelope only. Allocation truth, variable-inode
/// checksum validation and volume/source ownership must be bound by admission.
pub open spec fn node_admissible(raw: Seq<u8>, number: u32, inodes: u32, allocated: bool, block_bytes: usize) -> bool {
    &&& block_size::accepted(block_bytes as nat) && 128 <= raw.len() <= block_bytes
    &&& (raw.len() as usize & ((raw.len() - 1) as usize)) == 0
    &&& allocated && 0 < number <= inodes && bytes::le32(raw, 20) <= inodes
    &&& bytes::le16(raw, 26) != 0 ==> (bytes::le16(raw, 0) as u16 & 0xf000) == 0x8000
        || (bytes::le16(raw, 0) as u16 & 0xf000) == 0x4000 || (bytes::le16(raw, 0) as u16 & 0xf000) == 0xa000
}

#[derive(Clone, Copy)]
pub struct Node<'a> {
    raw: &'a [u8], number: u32, next: u32, generation: u32, mode: u16, links: u16,
}
impl<'a> Node<'a> {
    pub closed spec fn view(&self) -> NodeView {
        NodeView { raw: self.raw@, number: self.number, next: self.next, generation: self.generation, mode: self.mode, links: self.links }
    }
    pub open spec fn wf(&self) -> bool { node_valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn raw(&self) -> (r: &'a [u8]) ensures r@ == self.view().raw { self.raw }
    pub fn number(&self) -> (r: u32) ensures r == self.view().number { self.number }
    pub fn next(&self) -> (r: u32) ensures r == self.view().next { self.next }
    pub fn generation(&self) -> (r: u32) ensures r == self.view().generation { self.generation }
    pub fn mode(&self) -> (r: u16) ensures r == self.view().mode { self.mode }
    pub fn links(&self) -> (r: u16) ensures r == self.view().links { self.links }
}

pub fn decode<'a>(raw: &'a [u8], number: u32, inodes: u32, allocated: bool,
    block_bytes: usize) -> (r: Result<Node<'a>, Error>)
    ensures (r is Ok) <==> node_admissible(raw@, number, inodes, allocated, block_bytes),
        match r {
        Ok(node) => node.wf() && allocated && 0 < number <= inodes && node.view().number == number
            && node.view().raw == raw@ && node.view().next <= inodes && raw.len() <= block_bytes
            && block_size::accepted(block_bytes as nat),
        Err(_) => true,
    },
{
    reveal(node_valid);
    if !block_size::valid(block_bytes) || raw.len() < 128 || raw.len() > block_bytes {
        return Err(Error::Geometry);
    }
    let len = raw.len();
    if len & (len - 1) != 0 { return Err(Error::Geometry); }
    if number == 0 || number > inodes { return Err(Error::Inode); }
    if !allocated { return Err(Error::Unallocated); }
    let next = match bytes::read_le32(raw, INODE_NEXT_OFFSET) {
        Some(value) => value, None => { return Err(Error::Geometry); }
    };
    if next > inodes { return Err(Error::Next); }
    let mode = match bytes::read_le16(raw, 0) { Some(value) => value, None => { return Err(Error::Geometry); } };
    let links = match bytes::read_le16(raw, 26) { Some(value) => value, None => { return Err(Error::Geometry); } };
    let kind = mode & 0xf000;
    if links != 0 && kind != 0x8000 && kind != 0x4000 && kind != 0xa000 {
        return Err(Error::Type);
    }
    let generation = match bytes::read_le32(raw, 100) {
        Some(value) => value, None => { return Err(Error::Geometry); }
    };
    Ok(Node { raw, number, next, generation, mode, links })
}

pub struct Chain<'a> { nodes: Vec<Node<'a>>, head: u32, inodes: u32 }
pub struct Insert {
    head_before: u32, head_after: u32, inode: u32, generation: u32, next: u32,
}
pub struct Remove {
    head_before: u32, head_after: u32, inode: u32, generation: u32,
    previous: Option<u32>, next: u32,
}

impl Insert {
    pub closed spec fn view(&self) -> InsertView {
        InsertView { head_before: self.head_before, head_after: self.head_after, inode: self.inode, generation: self.generation, next: self.next }
    }
    pub open spec fn wf(&self) -> bool { insert_valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn insert_head_before(&self) -> (r: u32) ensures r == self.view().head_before { self.head_before }
    pub fn insert_head_after(&self) -> (r: u32) ensures r == self.view().head_after { self.head_after }
    pub fn insert_identity(&self) -> (r: (u32, u32)) ensures r == (self.view().inode, self.view().generation) { (self.inode, self.generation) }
    pub fn insert_next(&self) -> (r: u32) ensures r == self.view().next { self.next }
    pub fn insert_next_word(&self) -> (r: [u8; 4]) ensures r@ == bytes::encoded_le(self.view().next) { bytes::encode_le32(self.next) }
    pub fn insert_head_word(&self) -> (r: [u8; 4]) ensures r@ == bytes::encoded_le(self.view().head_after) { bytes::encode_le32(self.head_after) }
}
impl Remove {
    pub closed spec fn view(&self) -> RemoveView {
        RemoveView { head_before: self.head_before, head_after: self.head_after, inode: self.inode, generation: self.generation, previous: self.previous, next: self.next }
    }
    pub open spec fn wf(&self) -> bool { remove_valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn remove_head_before(&self) -> (r: u32) ensures r == self.view().head_before { self.head_before }
    pub fn remove_head_after(&self) -> (r: u32) ensures r == self.view().head_after { self.head_after }
    pub fn remove_identity(&self) -> (r: (u32, u32)) ensures r == (self.view().inode, self.view().generation) { (self.inode, self.generation) }
    pub fn remove_previous(&self) -> (r: Option<u32>) ensures r == self.view().previous { self.previous }
    pub fn remove_replacement_next(&self) -> (r: u32) ensures r == self.view().next { self.next }
    pub fn remove_replacement_word(&self) -> (r: [u8; 4]) ensures r@ == bytes::encoded_le(self.view().next) { bytes::encode_le32(self.next) }
    pub fn remove_head_word(&self) -> (r: [u8; 4]) ensures r@ == bytes::encoded_le(self.view().head_after) { bytes::encode_le32(self.head_after) }
    pub fn remove_cleared_next_word(&self) -> (r: [u8; 4]) ensures r@ == bytes::encoded_le(0) { bytes::encode_le32(0) }
}
impl<'a> Chain<'a> {
    pub closed spec fn view(&self) -> ChainView {
        ChainView { nodes: self.nodes@.map_values(|node: Node<'a>| node.view()), head: self.head, inodes: self.inodes }
    }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn head(&self) -> (r: u32) ensures r == self.view().head { self.head }
    pub fn len(&self) -> (r: usize) ensures r == self.view().nodes.len() { self.nodes.len() }
    pub fn get(&self, ordinal: usize) -> (r: Option<Node<'a>>)
        ensures self.wf(), match r {
            Some(node) => ordinal < self.view().nodes.len() && node.wf()
                && node.view() == self.view().nodes[ordinal as int],
            None => ordinal >= self.view().nodes.len(),
        },
    {
        proof { use_type_invariant(self); }
        if ordinal >= self.nodes.len() { None } else {
            let node = self.nodes[ordinal];
            proof { use_type_invariant(&node); }
            Some(node)
        }
    }
    pub fn find(&self, number: u32) -> (r: Option<usize>)
        ensures self.wf(), match r {
            Some(i) => i < self.view().nodes.len() && self.view().nodes[i as int].number == number
                && forall|j: int| 0 <= j < self.view().nodes.len() && j != i ==> (#[trigger] self.view().nodes[j]).number != number,
            None => forall|j: int| 0 <= j < self.view().nodes.len() ==> (#[trigger] self.view().nodes[j]).number != number,
        },
    { proof { use_type_invariant(self); }
        let mut i = 0usize;
        while i < self.nodes.len()
            invariant self.wf(), i <= self.nodes.len(),
                forall|j: int| 0 <= j < i ==> (#[trigger] self.view().nodes[j]).number != number,
            decreases self.nodes.len() - i,
        {
            if self.nodes[i].number == number {
                proof {
                    assert(self.view().nodes[i as int].number == number);
                    assert forall|j: int| 0 <= j < self.view().nodes.len() && j != i
                        implies (#[trigger] self.view().nodes[j]).number != number by {
                        distinct_chain_indices_have_distinct_identities(self.view(), i as int, j);
                    }
                }
                return Some(i);
            }
            i += 1;
        }
        None
    }
    pub fn prepare_insert(&self, node: &Node<'a>) -> (r: Result<Insert, Error>)
        ensures self.wf(), match r {
            Ok(plan) => plan.wf() && plan.view().head_before == self.view().head && plan.view().inode == node.view().number
                && plan.view().generation == node.view().generation && 0 < plan.view().inode <= self.view().inodes
                && forall|i: int| 0 <= i < self.view().nodes.len() ==> (#[trigger] self.view().nodes[i]).number != plan.view().inode,
            Err(_) => true,
        },
    { proof { use_type_invariant(self); use_type_invariant(node); reveal(valid); }
        if node.number == 0 || node.number > self.inodes { return Err(Error::Inode); }
        if self.find(node.number).is_some() { return Err(Error::Present); }
        Ok(Insert { head_before: self.head, head_after: node.number, inode: node.number,
            generation: node.generation, next: self.head })
    }
    pub fn prepare_remove(&self, number: u32, generation: u32) -> (r: Result<Remove, Error>)
        ensures self.wf(), match r {
            Ok(plan) => plan.wf() && plan.view().head_before == self.view().head && plan.view().inode == number && plan.view().generation == generation
                && exists|i: int| 0 <= i < self.view().nodes.len() && (#[trigger] self.view().nodes[i]).number == number
                    && self.view().nodes[i].generation == generation && plan.view().next == self.view().nodes[i].next
                    && plan.view().previous == if i == 0 { None } else { Some(self.view().nodes[i - 1].number) },
            Err(_) => true,
        },
    { proof { use_type_invariant(self); }
        let ordinal = match self.find(number) { Some(value) => value, None => { return Err(Error::Absent); } };
        let node = &self.nodes[ordinal];
        if node.generation != generation { return Err(Error::Inode); }
        proof {
            observe_chain_node(self.view(), ordinal as int);
            assert(node.number == number);
            assert(self.view().nodes[ordinal as int].generation == generation);
            if ordinal > 0 {
                observe_chain_node(self.view(), ordinal as int - 1);
                distinct_chain_indices_have_distinct_identities(self.view(), ordinal as int - 1, ordinal as int);
            }
        }
        let previous = if ordinal == 0 { None } else { Some(self.nodes[ordinal - 1].number) };
        Ok(Remove { head_before: self.head, head_after: if ordinal == 0 { node.next } else { self.head },
            inode: node.number, generation: node.generation, previous, next: node.next })
    }
}

fn catalogue_slot(catalogue: &[Node<'_>], number: u32) -> (r: Option<usize>)
    ensures match r {
        Some(i) => i < catalogue.len() && catalogue[i as int].number == number,
        None => forall|i: int| 0 <= i < catalogue.len() ==> (#[trigger] catalogue[i]).number != number,
    },
{
    let mut i = 0usize;
    while i < catalogue.len()
        invariant i <= catalogue.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] catalogue[j]).number != number,
        decreases catalogue.len() - i,
    {
        if catalogue[i].number == number { return Some(i); }
        i += 1;
    }
    None
}

/// Validate the source catalogue's identity uniqueness before following links.
/// Budget exhaustion returns no partial chain certificate.
pub fn walk<'a>(catalogue: &[Node<'a>], head: u32, inodes: u32, budget: usize)
    -> (r: Result<Chain<'a>, Error>)
    ensures match r {
        Ok(chain) => chain.wf() && chain.view().head == head && chain.view().inodes == inodes
            && chain.view().nodes.len() <= budget && from_catalogue(chain.view(), catalogue@.map_values(|node: Node<'a>| node.view())),
        Err(_) => true,
    },
{
    if head > inodes || inodes == 0 { return Err(Error::Inode); }
    let mut i = 0usize;
    while i < catalogue.len()
        invariant i <= catalogue.len(),
            forall|k: int| 0 <= k < i ==> (#[trigger] catalogue[k]).wf()
                && 0 < catalogue[k].number <= inodes && catalogue[k].next <= inodes,
            forall|a: int, b: int| 0 <= a < b < i ==> (#[trigger] catalogue[a]).number != (#[trigger] catalogue[b]).number,
        decreases catalogue.len() - i,
    {
        let checked_node = &catalogue[i];
        proof { use_type_invariant(checked_node); }
        if catalogue[i].number == 0 || catalogue[i].number > inodes || catalogue[i].next > inodes {
            return Err(Error::Inode);
        }
        let mut j = 0usize;
        while j < i
            invariant j <= i, i < catalogue.len(),
                forall|k: int| 0 <= k < j ==> (#[trigger] catalogue[k]).number != catalogue[i as int].number,
            decreases i - j,
        {
            if catalogue[j].number == catalogue[i].number { return Err(Error::Duplicate); }
            j += 1;
        }
        i += 1;
    }
    let mut nodes: Vec<Node<'a>> = Vec::new();
    let mut cursor = head;
    let mut left = budget;
    while cursor != 0
        invariant cursor <= inodes, nodes.len() <= budget, left <= budget,
            forall|k: int| 0 <= k < catalogue.len() ==> (#[trigger] catalogue[k]).wf()
                && 0 < catalogue[k].number <= inodes && catalogue[k].next <= inodes,
            nodes.len() + left == budget,
            nodes.len() == 0 ==> cursor == head,
            nodes.len() > 0 ==> nodes[0].number == head && nodes[nodes.len() - 1].next == cursor,
            forall|k: int| 0 <= k < nodes.len() ==> node_valid(nodes[k].view())
                && 0 < nodes[k].number <= inodes && nodes[k].next <= inodes
                && catalogue@.map_values(|node: Node<'a>| node.view()).contains(nodes[k].view()),
            forall|k: int| 0 <= k < nodes.len() - 1 ==> (#[trigger] nodes[k]).next == nodes[k + 1].number,
            forall|a: int, b: int| 0 <= a < b < nodes.len() ==> (#[trigger] nodes[a]).number != (#[trigger] nodes[b]).number,
        decreases left,
    {
        if left == 0 { return Err(Error::Budget); }
        let mut j = 0usize;
        while j < nodes.len()
            invariant j <= nodes.len(),
                forall|k: int| 0 <= k < j ==> (#[trigger] nodes[k]).number != cursor,
            decreases nodes.len() - j,
        {
            if nodes[j].number == cursor { return Err(Error::Cycle); }
            j += 1;
        }
        let at = match catalogue_slot(catalogue, cursor) {
            Some(value) => value, None => { return Err(Error::Missing); }
        };
        let node = catalogue[at];
        proof {
            assert(node.number == cursor);
            assert(catalogue@.map_values(|source: Node<'a>| source.view()).contains(node.view())) by {
                assert(catalogue@.map_values(|source: Node<'a>| source.view())[at as int] == node.view());
            }
        }
        cursor = node.next;
        nodes.push(node);
        left -= 1;
    }
    reveal(valid);
    Ok(Chain { nodes, head, inodes })
}

pub proof fn admitted_legacy_chain_has_no_cycle(v: ChainView, a: int, b: int)
    requires valid(v), 0 <= a < b < v.nodes.len(),
    ensures v.nodes[a].number != v.nodes[b].number,
{ reveal(valid); }
pub proof fn insert_word_points_to_the_exact_previous_head(v: InsertView)
    requires insert_valid(v),
    ensures v.next == v.head_before && v.head_after == v.inode,
{ }
pub proof fn removal_bypasses_only_the_selected_link(v: RemoveView)
    requires remove_valid(v),
    ensures v.previous is Some ==> v.head_after == v.head_before,
        v.previous is None ==> v.head_before == v.inode && v.head_after == v.next,
{ }

}
