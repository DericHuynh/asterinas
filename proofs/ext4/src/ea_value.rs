// SPDX-License-Identifier: MPL-2.0

//! Immutable EA values from one exact inode-table, xattr and extent snapshot.
//! Dense initialized mappings and integrity do not establish a complete
//! filesystem allocation/reference census, caller permissions or I/O authority.

use vstd::prelude::*;
use crate::{bytes, crc, ea_hash, ea_inode::{self, Status}, ea_reference::{self, ReferenceView},
    ea_source::{self, Header, NodeView}, extent_node::BlockChecksum, extent_span::{self, SpanView},
    extent_tree::{self, Context, Mapping}, extent_tree_model, inode, snapshot::Snapshot};

verus! {

pub const MAX_NODES: u64 = 4096;
pub open spec fn context(node: NodeView) -> Context {
    Context { source: node.header.source, root: (node.position as int + 40) as u64, blocks: node.header.blocks as u64, size: 4096,
        checksum: BlockChecksum::Crc32c(crc::fold(crc::fold(node.header.seed, crate::group::encoded_le(node.number)),
            crate::group::encoded_le(bytes::le32(node.raw, 100) as u32))) }
}
#[verifier::opaque]
pub open spec fn mapped(c: Context, logical: int, physical: u64, span: SpanView) -> bool {
    0 <= logical < 4096 && extent_span::valid(span) && span.initialized && span.blocks == c.blocks
        && extent_span::mapping(span, logical as u32) == Some(physical)
        && extent_tree_model::stored_mapping(c, extent_tree::root_node(c), bytes::le16(extent_tree::root_node(c).raw, 6) as u16, logical as u32, span)
}
pub open spec fn content(source: Seq<u8>, maps: Seq<u64>, data: Seq<u8>) -> bool {
    0 < data.len() <= 16777216 && maps.len() == (data.len() + 4095) / 4096
        && (forall|k: int| 0 <= k < maps.len() ==> 0 < #[trigger] maps[k] && (maps[k] as nat + 1) * 4096 <= source.len())
        && forall|i: int| 0 <= i < data.len() ==> #[trigger] data[i] == source[maps[i / 4096] as int * 4096 + i % 4096]
}
pub open spec fn legacy_lustre(reference: ReferenceView, node: NodeView) -> bool {
    reference.selected.hash as nat != bytes::le32(node.raw, 8)
        && bytes::le32(node.raw, 16) == reference.parent.number
        && bytes::le32(node.raw, 100) == bytes::le32(reference.parent.raw, 100)
}
pub struct ValueView { pub reference: ReferenceView, pub node: NodeView, pub maps: Seq<u64>, pub spans: Seq<SpanView>,
    pub data: Seq<u8>, pub budget: u64, pub visits: u64 }
#[verifier::opaque]
pub open spec fn valid(v: ValueView) -> bool {
    let h = v.node.header; let c = context(v.node); let entry = v.reference.selected;
    &&& ea_reference::valid(v.reference) && ea_source::node_valid(v.node) && v.reference.parent.header == h
    &&& v.node.number == entry.value_inode && v.node.number != v.reference.parent.number && !legacy_lustre(v.reference, v.node)
    &&& ea_inode::accepted(v.node.raw, v.node.number, h.inodes, h.seed, Status::Live)
    &&& v.data.len() == entry.value_size && v.data.len() == bytes::le32(v.node.raw, 4)
    &&& 1 <= v.visits <= v.budget <= MAX_NODES && extent_tree::context_valid(c)
    &&& extent_tree::subtree_valid(c, extent_tree::root_node(c), None,
        bytes::le16(extent_tree::root_node(c).raw, 6) as u16, None, crate::extent::MAX_LOGICAL_END)
    &&& v.visits == extent_tree::tree_visits(c, extent_tree::root_node(c), bytes::le16(extent_tree::root_node(c).raw, 6) as u16)
    &&& content(h.source, v.maps, v.data) && v.maps.no_duplicates() && v.spans.len() == v.maps.len()
    &&& forall|i: int| 0 <= i < v.maps.len() ==> #[trigger] mapped(c, i, v.maps[i], v.spans[i])
    &&& crc::fold(h.seed, v.data) == bytes::le32(v.node.raw, 8)
    &&& entry.hash == ea_hash::entry(v.reference.name, bytes::le32(v.node.raw, 8) as u32, false)
        || entry.hash == ea_hash::entry(v.reference.name, bytes::le32(v.node.raw, 8) as u32, true)
}
pub struct Value { data: Vec<u8>, maps: Vec<u64>, number: u32, checked: Ghost<ValueView> }
impl Value {
    pub closed spec fn view(&self) -> ValueView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        valid(self.view()) && self.data@ == self.view().data && self.maps@ == self.view().maps && self.number == self.view().node.number
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn as_slice(&self) -> (r: &[u8]) ensures self.wf(), valid(self.view()), r@ == self.view().data {
        proof { use_type_invariant(self); } &self.data
    }
    pub fn blocks(&self) -> (r: &[u64]) ensures self.wf(), valid(self.view()), r@ == self.view().maps {
        proof { use_type_invariant(self); } &self.maps
    }
    pub fn inode_number(&self) -> (r: u32) ensures self.wf(), valid(self.view()), r == self.view().node.number {
        proof { use_type_invariant(self); } self.number
    }
    pub fn same_bytes(&self, other: &Self) -> (r: bool)
        ensures self.wf(), other.wf(), r == (self.view().data == other.view().data),
    { proof { use_type_invariant(self); use_type_invariant(other); } bytes::equal(&self.data, &other.data) }
}
fn distinct(maps: &[u64]) -> (r: bool) ensures r == maps@.no_duplicates() {
    let mut i = 0usize;
    while i < maps.len()
        invariant i <= maps.len(), forall|a: int, b: int| 0 <= a < b < i ==> #[trigger] maps@[a] != #[trigger] maps@[b],
        decreases maps.len() - i,
    {
        let mut j = 0usize;
        while j < i
            invariant j <= i < maps.len(), forall|a: int, b: int| 0 <= a < b < i ==> #[trigger] maps@[a] != #[trigger] maps@[b],
                forall|a: int| 0 <= a < j ==> #[trigger] maps@[a] != maps@[i as int],
            decreases i - j,
        { if maps[j] == maps[i] { return false; } j += 1; }
        i += 1;
    }
    true
}
// Validate the final owned buffer against actual source ranges, independently
// of the append loop. Only initialized mappings can reach this checker.
fn check_content(source: &Snapshot<'_>, maps: &[u64], data: &[u8]) -> (r: bool)
    ensures r ==> content(source.view(), maps@, data@),
{
    if data.len() == 0 || data.len() > 16777216 || maps.len() != (data.len() + 4095) / 4096 { return false; }
    let mut k = 0usize;
    while k < maps.len()
        invariant 0 < data.len() <= 16777216, maps.len() == (data.len() + 4095) / 4096, k <= maps.len() <= 4096,
            forall|a: int| 0 <= a < k ==> 0 < #[trigger] maps@[a] && (maps@[a] as nat + 1) * 4096 <= source.view().len(),
            forall|i: int| 0 <= i < data.len() && i < k * 4096 ==> #[trigger] data@[i] == source.view()[maps@[i / 4096] as int * 4096 + i % 4096],
        decreases maps.len() - k,
    {
        let physical = maps[k]; if physical == 0 || physical > u32::MAX as u64 { return false; }
        let block = match source.block(physical as u32) { Some(block) => block, None => { return false; } };
        let start = k * 4096; if start >= data.len() { return false; }
        let length = if data.len() - start < 4096 { data.len() - start } else { 4096usize };
        let raw = block.as_slice(); let mut j = 0usize;
        while j < length
            invariant k < maps.len() <= 4096, physical == maps@[k as int], raw.len() == 4096,
                raw@ == source.view().subrange(physical as int * 4096, (physical as int + 1) * 4096),
                start == k * 4096, start < data.len() <= 16777216, 0 < length <= 4096, start + length <= data.len(),
                maps.len() == (data.len() + 4095) / 4096,
                physical > 0, (physical as nat + 1) * 4096 <= source.view().len(),
                forall|q: int| 0 <= q < data.len() && q < k * 4096 ==> #[trigger] data@[q] == source.view()[maps@[q / 4096] as int * 4096 + q % 4096],
                j <= length, forall|a: int| 0 <= a < j ==> #[trigger] data@[start as int + a] == raw@[a],
            decreases length - j,
        { if data[start + j] != raw[j] { return false; } j += 1; }
        assert forall|i: int| 0 <= i < data.len() && i < (k + 1) * 4096 implies #[trigger] data@[i] == source.view()[maps@[i / 4096] as int * 4096 + i % 4096] by {
            if i >= k * 4096 {
                let offset = i - k as int * 4096;
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(i, 4096, k as int, offset);
                assert(0 <= offset < length);
                assert(start as int + offset == i);
                assert(data@[start as int + offset] == raw@[offset]);
                assert(data@[i] == raw@[offset]);
                assert(raw@[offset] == source.view()[physical as int * 4096 + offset]);
                assert(maps@[i / 4096] == physical);
            } else {
                assert(data@[i] == source.view()[maps@[i / 4096] as int * 4096 + i % 4096]);
            }
        }
        k += 1;
    }
    true
}

fn read_tree(tree: &extent_tree::CheckedTree<'_, '_>, source: &Snapshot<'_>, size: u32)
    -> (r: Option<(Vec<u8>, Vec<u64>, Ghost<Seq<SpanView>>)>)
    requires tree.wf(), tree.context().source == source.view(), 0 < size <= 16777216,
    ensures tree.wf(), match r { Some(parts) => parts.0.len() == size && parts.1.len() == (size as nat + 4095) / 4096
        && parts.2@.len() == parts.1.len() && (forall|j: int| 0 <= j < parts.1.len() ==>
            #[trigger] mapped(tree.context(), j, parts.1@[j], parts.2@[j])), None => true },
{
    let ghost c = tree.context();
    let count = (size as usize + 4095) / 4096;
    let mut maps = Vec::new(); let mut data = Vec::new(); let mut i = 0usize;
    let ghost mut spans: Seq<SpanView> = Seq::empty();
    while i < count
        invariant tree.wf(), c == tree.context(), c.source == source.view(), count == (size as nat + 4095) / 4096, 0 < size <= 16777216,
            i <= count <= 4096, maps.len() == i, spans.len() == i, data.len() <= size, data.len() == if i < count { i * 4096 } else { size as int },
            forall|j: int| 0 <= j < i ==> #[trigger] mapped(c, j, maps@[j], spans[j]),
        decreases count - i,
    {
        let path = tree.find(i as u32).unwrap();
        let physical = match path.resolved() { Mapping::Written(physical) => physical, _ => { return None; } };
        if physical > u32::MAX as u64 { return None; }
        let ghost span = path.result().unwrap();
        proof {
            assert(path.result() == Some(span));
            assert(extent_tree::mapping(Some(span), i as u32) == Mapping::Written(physical));
            let visits = path.visits();
            let depth = bytes::le16(visits[0].node.raw, 6) as u16;
            extent_tree::successful_route_has_exact_depths_and_sources(c, visits, i as u32, depth, None, crate::extent::MAX_LOGICAL_END);
            let last = visits.len() - 1;
            assert(extent_tree::node_source(c, visits[last].node, visits[last].address));
            assert(crate::extent_node::leaf_result(visits[last].node, i as u32, Some(span)));
            assert(extent_span::valid(span) && span.blocks == c.blocks);
            assert(tree.maps(i as u32, span));
        }
        assert(mapped(c, i as int, physical, span)) by { reveal(mapped); };
        maps.push(physical); proof { spans = spans.push(span); }
        let block = match source.block(physical as u32) { Some(block) => block, None => { return None; } };
        let length = if size as usize - data.len() < 4096 { size as usize - data.len() } else { 4096usize };
        let start = data.len(); let raw = block.as_slice(); let mut j = 0usize;
        while j < length
            invariant raw.len() == 4096, j <= length <= 4096, start <= size, length <= size as nat - start,
                data.len() == start + j,
            decreases length - j,
        { data.push(raw[j]); j += 1; }
        i += 1;
    }
    Some((data, maps, Ghost(spans)))
}

pub fn inspect(header: &Header<'_, '_>, parent: u32, namespace: u8, name: &[u8], budget: u64) -> (r: Option<Value>)
    ensures header.wf(), match r { Some(value) => value.wf() && valid(value.view()) && value.view().reference.parent.header == header.view()
        && value.view().reference.parent.number == parent && value.view().reference.namespace == namespace && value.view().reference.name == name@
        && value.view().budget == budget, None => true },
{
    hide(inode::checksum);
    let (blocks, inodes, _, seed) = header.parameters();
    if budget == 0 || budget > MAX_NODES { return None; }
    let reference = match ea_reference::inspect(header, parent, namespace, name) { Some(reference) => reference, None => { return None; } };
    let (number, size, entry_hash) = reference.parameters();
    if size == 0 || size > ea_inode::MAX_VALUE || number == parent { return None; }
    let node = match header.get(number) { Some(node) => node, None => { return None; } };
    let info = match ea_inode::parse(node.raw(), number, inodes, seed, Status::Live) { Some(info) => info, None => { return None; } };
    if info.size != size { return None; }
    let parent_raw = reference.parent().raw();
    if entry_hash != info.hash && bytes::read_le32(node.raw(), 16).unwrap() == parent
        && info.generation == bytes::read_le32(parent_raw, 100).unwrap() { return None; }
    let position = node.position(); if position > u64::MAX - 40 { return None; }
    let source = header.source(); let root = position + 40;
    let checksum_seed = inode::inode_seed(seed, number, info.generation);
    let tree = match extent_tree::audit(source, root, blocks as u64, 4096, BlockChecksum::Crc32c(checksum_seed), budget) { Ok(tree) => tree, Err(_) => { return None; } };
    let visits = tree.checked_nodes();
    let ghost c = tree.context();
    assert(c == context(node.view()));
    let (data, maps, Ghost(spans)) = match read_tree(&tree, source, size) { Some(parts) => parts, None => { return None; } };
    if !distinct(&maps) || !check_content(source, &maps, &data) { return None; }
    if !ea_hash::matches(reference.name(), &data, seed, info.hash, entry_hash) { return None; }
    let ghost view = ValueView { reference: reference.view(), node: node.view(), maps: maps@, spans, data: data@, budget, visits };
    assert(valid(view)) by { reveal(valid); reveal(ea_inode::accepted); }
    Some(Value { data, maps, number, checked: Ghost(view) })
}

pub proof fn ea_values_use_one_exact_parent_key_and_allocated_value_inode(v: ValueView)
    requires valid(v),
    ensures v.node.header == v.reference.parent.header, v.node.number == v.reference.selected.value_inode,
        v.node.number != v.reference.parent.number, ea_source::node_valid(v.node),
{ reveal(valid); }
pub proof fn every_ea_value_byte_comes_from_an_initialized_source_extent(v: ValueView, i: int)
    requires valid(v), 0 <= i < v.data.len(),
    ensures v.data[i] == v.node.header.source[v.maps[i / 4096] as int * 4096 + i % 4096],
        mapped(context(v.node), i / 4096, v.maps[i / 4096], v.spans[i / 4096]),
{ reveal(valid); }
proof fn map_facts(v: ValueView)
    requires valid(v),
    ensures v.maps.no_duplicates(), v.spans.len() == v.maps.len(),
        forall|k: int| 0 <= k < v.maps.len() ==> #[trigger] mapped(context(v.node), k, v.maps[k], v.spans[k]),
{ reveal(valid); }
proof fn initialized_mapping(c: Context, i: int, physical: u64, span: SpanView)
    requires mapped(c, i, physical, span), ensures span.initialized,
{ reveal(mapped); }
pub proof fn ea_values_have_no_holes_unwritten_blocks_or_repeated_physical_blocks(v: ValueView, i: int, j: int)
    requires valid(v), 0 <= i < j < v.maps.len(),
    ensures v.maps[i] != v.maps[j], v.spans[i].initialized, v.spans[j].initialized,
{
    map_facts(v);
    initialized_mapping(context(v.node), i, v.maps[i], v.spans[i]);
    initialized_mapping(context(v.node), j, v.maps[j], v.spans[j]);
}

pub proof fn successful_ea_values_check_both_the_exact_value_crc_and_entry_hash(v: ValueView)
    requires valid(v),
    ensures crc::fold(v.node.header.seed, v.data) == bytes::le32(v.node.raw, 8),
        v.reference.selected.hash == ea_hash::entry(v.reference.name, bytes::le32(v.node.raw, 8) as u32, false)
        || v.reference.selected.hash == ea_hash::entry(v.reference.name, bytes::le32(v.node.raw, 8) as u32, true),
{ reveal(valid); }

pub proof fn modern_ea_inspection_does_not_apply_linux_lustre_reference_rules(v: ValueView)
    requires valid(v), ensures !legacy_lustre(v.reference, v.node),
{ reveal(valid); }

}
