// SPDX-License-Identifier: MPL-2.0

//! Complete source-bound linear and indexed directory capture over the
//! EA-enabled allocation certificate. Canonical pieces and full HTree hashes
//! are checked without converting or weakening the source feature policy.
//! Name targets, links, topology, journal state and mounted authority are
//! established separately by the namespace layer.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{block_claims::{self, Claim}, bytes, crc, dir_hash::State,
    directory_piece::{self, Piece, PieceView}, ea_allocation::{self, Allocation, AllocationView},
    ea_integrity, ea_ordinary::{self, Ordinary, OrdinaryView}, ea_source::{self, NodeView},
    ea_value, extent_node::BlockChecksum, extent_span::SpanView,
    extent_tree::{self, Mapping}, htree_names::{self, Directory as HashDirectory, DirectoryView as HashView},
    htree_topology, inode, inode_size};

verus! {

pub const MAX_BLOCKS: u32 = 4096;

pub open spec fn piece_views(pieces: Seq<Piece>) -> Seq<PieceView> {
    Seq::new(pieces.len(), |i: int| pieces[i].view())
}
pub open spec fn piece_raws(pieces: Seq<PieceView>) -> Seq<Seq<u8>> {
    Seq::new(pieces.len(), |i: int| pieces[i].block.raw)
}
pub open spec fn large(volume: AllocationView) -> bool {
    bytes::le32(volume.integrity.references.index.header.source, 1120) as u32 & 0x4000 != 0
}
pub open spec fn unsigned(volume: AllocationView) -> bool {
    bytes::le32(volume.integrity.references.index.header.source, 1376) as u32 & 2 != 0
}
pub open spec fn hash_seed(volume: AllocationView) -> State {
    let source = volume.integrity.references.index.header.source;
    State { a: bytes::le32(source, 1260) as u32, b: bytes::le32(source, 1264) as u32,
        c: bytes::le32(source, 1268) as u32, d: bytes::le32(source, 1272) as u32 }
}
pub open spec fn indexed(ordinary: OrdinaryView) -> bool {
    bytes::le32(ordinary.parent.node.raw, 32) as u32 & 0x1000 != 0
}
pub open spec fn seed(ordinary: OrdinaryView) -> u32 {
    crc::fold(crc::fold(ordinary.index.header.seed, crate::group::encoded_le(ordinary.parent.node.number)),
        crate::group::encoded_le(bytes::le32(ordinary.parent.node.raw, 100) as u32))
}
pub open spec fn size(volume: AllocationView, ordinary: OrdinaryView) -> nat {
    inode_size::value(ordinary.parent.node.raw, large(volume))
}
pub open spec fn data_claims_within(ordinary: OrdinaryView, count: u32) -> bool {
    forall|i: int| 0 <= i < ordinary.claims.len() && (#[trigger] ordinary.claims[i]).kind == 5 ==>
        ordinary.claims[i].initialized && ordinary.claims[i].logical as nat + ordinary.claims[i].length <= count
}
pub open spec fn maps(ordinary: OrdinaryView, logical: u32, physical: u32) -> bool {
    exists|span: SpanView| #[trigger] ea_value::mapped(ea_ordinary::context(ordinary.parent.node), logical as int, physical as u64, span)
}
pub open spec fn owned(volume: AllocationView, ordinary: OrdinaryView, logical: u32, physical: u32) -> bool {
    physical < volume.ledger.roles.len()
        && volume.ledger.roles[physical as int].kind == 5
        && volume.ledger.roles[physical as int].inode == ordinary.parent.node.number
        && volume.ledger.roles[physical as int].generation == bytes::le32(ordinary.parent.node.raw, 100)
        && volume.ledger.roles[physical as int].logical == logical && volume.ledger.roles[physical as int].initialized
}
#[verifier::opaque]
pub open spec fn checked_piece(volume: AllocationView, ordinary: OrdinaryView,
    piece: PieceView, physical: u32, logical: u32, count: u32) -> bool {
    &&& directory_piece::valid(piece) && maps(ordinary, logical, physical)
    &&& owned(volume, ordinary, logical, physical)
    &&& piece.logical == logical && piece.blocks == count && piece.indexed == indexed(ordinary)
    &&& piece.large == large(volume) && piece.block.seed == seed(ordinary)
    &&& piece.block.inodes == ordinary.index.header.inodes
    &&& piece.block.raw == ordinary.index.header.source.subrange(physical as int * 4096, (physical as int + 1) * 4096)
}

pub struct DirectoryView {
    pub volume: AllocationView, pub ordinal: usize, pub pieces: Seq<PieceView>,
    pub physical: Seq<u32>, pub tree: Option<HashView>,
}
pub open spec fn ordinary(v: DirectoryView) -> OrdinaryView { v.volume.ordinary[v.ordinal as int] }
pub open spec fn owner(v: DirectoryView) -> u32 { ordinary(v).parent.node.number }
#[verifier::opaque]
pub open spec fn tree_bound(v: DirectoryView, tree: HashView) -> bool {
    &&& htree_names::valid(tree)
    &&& tree.graph.context == (htree_topology::Context { source: piece_raws(v.pieces),
        inodes: ordinary(v).index.header.inodes, seed: seed(ordinary(v)), large: large(v.volume) })
    &&& tree.hash_seed == hash_seed(v.volume)
    &&& tree.version as nat == v.pieces[0].block.raw[28] as nat + if unsigned(v.volume) { 3nat } else { 0nat }
    &&& bytes::le32(v.pieces[0].block.raw, 0) == owner(v)
}
#[verifier::opaque]
pub open spec fn valid(v: DirectoryView) -> bool {
    &&& ea_allocation::valid(v.volume) && v.ordinal < v.volume.ordinary.len()
    &&& ea_ordinary::valid(ordinary(v)) && ea_ordinary::directory(ordinary(v).parent)
    &&& ordinary(v).index == v.volume.integrity.references.index
    &&& 0 < size(v.volume, ordinary(v)) && size(v.volume, ordinary(v)) % 4096 == 0
    &&& 0 < v.pieces.len() <= MAX_BLOCKS && v.pieces.len() * 4096 == size(v.volume, ordinary(v))
    &&& v.physical.len() == v.pieces.len() && data_claims_within(ordinary(v), v.pieces.len() as u32)
    &&& (forall|i: int| 0 <= i < v.pieces.len() ==> #[trigger] checked_piece(v.volume, ordinary(v), v.pieces[i], v.physical[i], i as u32, v.pieces.len() as u32))
    &&& match v.tree { Some(tree) => indexed(ordinary(v)) && tree_bound(v, tree), None => !indexed(ordinary(v)) }
}

pub struct Directory<'a> {
    number: u32, ordinal: usize, pieces: Vec<Piece<'a>>, physical: Vec<u32>, raw: Vec<&'a [u8]>,
    tree: Option<HashDirectory<'a>>, checked: Ghost<DirectoryView>,
}
impl<'a> Directory<'a> {
    pub closed spec fn view(&self) -> DirectoryView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        valid(self.view()) && self.number == owner(self.view()) && self.ordinal == self.view().ordinal
            && piece_views(self.pieces@) == self.view().pieces && self.physical@ == self.view().physical
            && htree_topology::source_views(self.raw@) == piece_raws(self.view().pieces)
            && self.view().tree == match &self.tree { Some(tree) => Some(tree.view()), None => None }
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn number(&self) -> (r: u32) ensures self.wf(), valid(self.view()), r == owner(self.view()) {
        proof { use_type_invariant(self); } self.number
    }
    pub fn ordinal(&self) -> (r: usize) ensures self.wf(), valid(self.view()), r == self.view().ordinal {
        proof { use_type_invariant(self); } self.ordinal
    }
    pub fn block_count(&self) -> (r: u32) ensures self.wf(), valid(self.view()), r == self.view().pieces.len(), 0 < r <= MAX_BLOCKS {
        proof { use_type_invariant(self); reveal(valid); } self.pieces.len() as u32
    }
    pub fn piece(&self, logical: u32) -> (r: Option<&Piece<'a>>)
        ensures self.wf(), valid(self.view()), match r { Some(piece) => logical < self.view().pieces.len()
            && piece.wf() && directory_piece::valid(piece.view()) && piece.view() == self.view().pieces[logical as int],
            None => logical >= self.view().pieces.len() },
    {
        proof { use_type_invariant(self); }
        if logical as usize >= self.pieces.len() { return None; }
        let piece = &self.pieces[logical as usize]; let _ = piece.len(); Some(piece)
    }
    pub fn physical_block(&self, logical: u32) -> (r: Option<u32>)
        ensures self.wf(), valid(self.view()), match r { Some(physical) => logical < self.view().physical.len()
            && physical == self.view().physical[logical as int], None => logical >= self.view().physical.len() },
    {
        proof { use_type_invariant(self); }
        if logical as usize >= self.physical.len() { None } else { Some(self.physical[logical as usize]) }
    }
    pub fn tree(&self) -> (r: Option<&HashDirectory<'a>>)
        ensures self.wf(), valid(self.view()), match r { Some(tree) => tree.wf()
            && self.view().tree == Some(tree.view()) && tree_bound(self.view(), tree.view()), None => self.view().tree is None },
    {
        proof { use_type_invariant(self); reveal(valid); }
        match &self.tree { Some(tree) => { let _ = tree.len(); Some(tree) }, None => None }
    }
    pub fn raw_blocks(&self) -> (r: &[&'a [u8]])
        ensures self.wf(), valid(self.view()), htree_topology::source_views(r@) == piece_raws(self.view().pieces),
    { proof { use_type_invariant(self); } &self.raw }
}

fn check_claims(claims: &[Claim], count: u32) -> (r: bool)
    ensures r ==> forall|i: int| 0 <= i < claims.len() && (#[trigger] claims@[i]).kind == 5 ==>
        claims@[i].initialized && claims@[i].logical as nat + claims@[i].length <= count,
{
    let mut i = 0usize;
    while i < claims.len()
        invariant i <= claims.len(), forall|j: int| 0 <= j < i && (#[trigger] claims@[j]).kind == 5 ==>
            claims@[j].initialized && claims@[j].logical as nat + claims@[j].length <= count,
        decreases claims.len() - i,
    {
        let claim = claims[i];
        if claim.kind == 5 && (!claim.initialized || claim.logical as u64 + claim.length as u64 > count as u64) { return false; }
        i += 1;
    }
    true
}
proof fn the_source_node_is_the_same_ordinary_inode(volume: AllocationView, ordinal: usize, node: NodeView)
    requires ea_allocation::valid(volume), ordinal < volume.ordinary.len(), ea_ordinary::valid(volume.ordinary[ordinal as int]),
        ea_source::node_valid(node), node.header == volume.integrity.references.index.header,
        node.number == volume.ordinary[ordinal as int].parent.node.number,
    ensures node == volume.ordinary[ordinal as int].parent.node,
        volume.ordinary[ordinal as int].index == volume.integrity.references.index,
{
    reveal(ea_allocation::valid);
    assert(ea_ordinary::valid(volume.ordinary[ordinal as int]));
    reveal(ea_ordinary::valid); reveal(crate::ea_parent::valid);
    ea_integrity::same_source_ea_inode_number_identifies_one_exact_node(node, volume.ordinary[ordinal as int].parent.node);
}

// Keep source-route and parsing reasoning outside the catalogue loop. The
// returned bytes are borrowed from the same immutable source, not rebuilt.
#[verifier::rlimit(30)]
fn read_piece<'a>(volume: &Allocation<'_, 'a>, ordinary: &Ordinary,
    source: &crate::snapshot::Snapshot<'a>, tree: &extent_tree::CheckedTree<'_, '_>,
    logical: u32, count: u32, inodes: u32, metadata_seed: u32, generation: u32, indexed: bool, large: bool)
    -> (r: Option<(Piece<'a>, u32, &'a [u8])>)
    requires volume.wf(), ordinary.wf(), tree.wf(),
        source.view() == ordinary.view().index.header.source,
        ordinary.view().index == volume.view().integrity.references.index,
        tree.context() == ea_ordinary::context(ordinary.view().parent.node),
        logical < count <= MAX_BLOCKS, inodes == ordinary.view().index.header.inodes,
        generation as nat == bytes::le32(ordinary.view().parent.node.raw, 100),
        metadata_seed == seed(ordinary.view()), indexed == crate::ea_directory::indexed(ordinary.view()),
        large == crate::ea_directory::large(volume.view()),
    ensures volume.wf(), ordinary.wf(), tree.wf(), match r {
        Some((piece, physical, raw)) => piece.wf()
            && checked_piece(volume.view(), ordinary.view(), piece.view(), physical, logical, count)
            && raw@ == piece.view().block.raw,
        None => true },
{
    let number = ordinary.number();
    let ghost ov = ordinary.view(); let ghost vv = volume.view(); let ghost c = tree.context();
    let path = tree.find(logical).unwrap();
    let address = match path.resolved() { Mapping::Written(address) => address, _ => { return None; } };
    if address > u32::MAX as u64 { return None; }
    let physical = address as u32;
    let ghost span = path.result().unwrap();
    proof {
        assert(path.result() == Some(span));
        assert(extent_tree::mapping(Some(span), logical) == Mapping::Written(address));
        let visits = path.visits(); let depth = bytes::le16(visits[0].node.raw, 6) as u16;
        extent_tree::successful_route_has_exact_depths_and_sources(c, visits, logical, depth, None, crate::extent::MAX_LOGICAL_END);
        let last = visits.len() - 1;
        assert(extent_tree::node_source(c, visits[last].node, visits[last].address));
        assert(crate::extent_node::leaf_result(visits[last].node, logical, Some(span)));
        assert(crate::extent_span::valid(span) && span.blocks == c.blocks);
        assert(tree.maps(logical, span));
        assert(ea_value::mapped(c, logical as int, address, span)) by { reveal(ea_value::mapped); }
        assert(exists|value: SpanView| #[trigger] ea_value::mapped(ea_ordinary::context(ov.parent.node), logical as int, physical as u64, value));
        assert(maps(ov, logical, physical));
    }
    let role = match volume.ledger().role_of(physical) { Some(role) => role, None => { return None; } };
    if role.kind != 5 || role.inode != number || role.generation != generation || role.logical != logical || !role.initialized { return None; }
    let block = match source.block(physical) { Some(block) => block, None => { return None; } };
    let raw = block.as_slice();
    let piece = match directory_piece::parse(raw, inodes, metadata_seed, indexed, logical, count, large) { Some(piece) => piece, None => { return None; } };
    assert(checked_piece(vv, ov, piece.view(), physical, logical, count)) by { reveal(checked_piece); }
    Some((piece, physical, raw))
}

// A vector extension proof carries only the previous opaque certificate,
// so collection never unfolds filesystem geometry, CRCs or extent routes.
#[verifier::rlimit(30)]
fn append_piece<'a>(mut pieces: Vec<Piece<'a>>, mut physicals: Vec<u32>, mut raw_blocks: Vec<&'a [u8]>,
    piece: Piece<'a>, physical: u32, raw: &'a [u8], count: u32,
    Ghost(volume): Ghost<AllocationView>, Ghost(ordinary): Ghost<OrdinaryView>)
    -> (r: (Vec<Piece<'a>>, Vec<u32>, Vec<&'a [u8]>))
    requires pieces.len() < count <= MAX_BLOCKS, physicals.len() == pieces.len(), raw_blocks.len() == pieces.len(),
        htree_topology::source_views(raw_blocks@) == piece_raws(piece_views(pieces@)),
        (forall|j: int| 0 <= j < pieces.len() ==> #[trigger] checked_piece(volume, ordinary,
            piece_views(pieces@)[j], physicals@[j], j as u32, count)),
        checked_piece(volume, ordinary, piece.view(), physical, pieces.len() as u32, count),
        raw@ == piece.view().block.raw,
    ensures r.0.len() == pieces.len() + 1, r.1.len() == r.0.len(), r.2.len() == r.0.len(),
        htree_topology::source_views(r.2@) == piece_raws(piece_views(r.0@)),
        forall|j: int| 0 <= j < r.0.len() ==> #[trigger] checked_piece(volume, ordinary,
            piece_views(r.0@)[j], r.1@[j], j as u32, count),
{
    let ghost before = piece_views(pieces@); let ghost old_physical = physicals@; let ghost old_raw = raw_blocks@;
    assert(old_raw.len() == before.len());
    assert(htree_topology::source_views(old_raw) == piece_raws(before));
    assert forall|j: int| 0 <= j < before.len() implies (#[trigger] old_raw[j])@ == before[j].block.raw by {
        assert(0 <= j < old_raw.len());
        assert(htree_topology::source_views(old_raw)[j] == old_raw[j]@);
        assert(piece_raws(before)[j] == before[j].block.raw);
        assert(htree_topology::source_views(old_raw)[j] == piece_raws(before)[j]);
    }
    let ghost next = piece.view();
    pieces.push(piece); physicals.push(physical); raw_blocks.push(raw);
    assert(piece_views(pieces@) =~= before.push(next));
    assert forall|j: int| 0 <= j < raw_blocks.len() implies (#[trigger] raw_blocks@[j])@ == piece_views(pieces@)[j].block.raw by {
        if j < before.len() {
            assert(raw_blocks@[j] == old_raw[j]);
            assert(piece_views(pieces@)[j] == before[j]);
            assert(old_raw[j]@ == before[j].block.raw);
        } else { assert(j == before.len()); }
    }
    assert(htree_topology::source_views(raw_blocks@) =~= piece_raws(piece_views(pieces@)));
    assert forall|j: int| 0 <= j < pieces.len() implies #[trigger] checked_piece(volume, ordinary,
        piece_views(pieces@)[j], physicals@[j], j as u32, count) by {
        if j < before.len() {
            assert(piece_views(pieces@)[j] == before[j]);
            assert(physicals@[j] == old_physical[j]);
            assert(checked_piece(volume, ordinary, before[j], old_physical[j], j as u32, count));
        } else { assert(j == before.len()); }
    }
    (pieces, physicals, raw_blocks)
}

#[verifier::rlimit(30)]
fn collect_pieces<'a>(volume: &Allocation<'_, 'a>, ordinary: &Ordinary,
    source: &crate::snapshot::Snapshot<'a>, tree: &extent_tree::CheckedTree<'_, '_>,
    count: u32, inodes: u32, metadata_seed: u32, generation: u32, indexed: bool, large: bool)
    -> (r: Option<(Vec<Piece<'a>>, Vec<u32>, Vec<&'a [u8]>)>)
    requires volume.wf(), ordinary.wf(), tree.wf(),
        source.view() == ordinary.view().index.header.source,
        ordinary.view().index == volume.view().integrity.references.index,
        tree.context() == ea_ordinary::context(ordinary.view().parent.node),
        0 < count <= MAX_BLOCKS, inodes == ordinary.view().index.header.inodes,
        generation as nat == bytes::le32(ordinary.view().parent.node.raw, 100),
        metadata_seed == seed(ordinary.view()), indexed == crate::ea_directory::indexed(ordinary.view()),
        large == crate::ea_directory::large(volume.view()),
    ensures volume.wf(), ordinary.wf(), tree.wf(), match r {
        Some((pieces, physicals, raw)) => pieces.len() == count && physicals.len() == count && raw.len() == count
            && htree_topology::source_views(raw@) == piece_raws(piece_views(pieces@))
            && (forall|j: int| 0 <= j < count ==> #[trigger] checked_piece(volume.view(), ordinary.view(),
                piece_views(pieces@)[j], physicals@[j], j as u32, count)),
        None => true },
{
    hide(crc::fold);
    let ghost ov = ordinary.view(); let ghost vv = volume.view();
    let mut pieces: Vec<Piece<'a>> = Vec::new(); let mut physicals: Vec<u32> = Vec::new(); let mut raw_blocks: Vec<&'a [u8]> = Vec::new();
    let mut logical = 0u32;
    assert(htree_topology::source_views(raw_blocks@) =~= piece_raws(piece_views(pieces@)));
    while logical < count
        invariant volume.wf(), volume.view() == vv, ordinary.wf(), ordinary.view() == ov, tree.wf(),
            source.view() == ov.index.header.source, ov.index == vv.integrity.references.index,
            tree.context() == ea_ordinary::context(ov.parent.node),
            0 < count <= MAX_BLOCKS, inodes == ov.index.header.inodes,
            generation as nat == bytes::le32(ov.parent.node.raw, 100), metadata_seed == seed(ov),
            indexed == crate::ea_directory::indexed(ov), large == crate::ea_directory::large(vv),
            logical <= count, pieces.len() == logical, physicals.len() == logical, raw_blocks.len() == logical,
            htree_topology::source_views(raw_blocks@) == piece_raws(piece_views(pieces@)),
            forall|j: int| 0 <= j < logical ==> #[trigger] checked_piece(vv, ov, piece_views(pieces@)[j], physicals@[j], j as u32, count),
        decreases count - logical,
    {
        let (piece, physical, bytes) = match read_piece(volume, ordinary, source, &tree,
            logical, count, inodes, metadata_seed, generation, indexed, large) {
            Some(parts) => parts, None => { return None; }
        };
        let (next_pieces, next_physicals, next_raw) = append_piece(pieces, physicals, raw_blocks,
            piece, physical, bytes, count, Ghost(vv), Ghost(ov));
        pieces = next_pieces; physicals = next_physicals; raw_blocks = next_raw;
        logical += 1;
    }
    Some((pieces, physicals, raw_blocks))
}

// Hash validation reads the actual source primary block and consumes every
// captured directory block. Keep it separate from extent-tree discovery.
#[verifier::rlimit(30)]
fn bind_hash_tree<'a>(source: &crate::snapshot::Snapshot<'a>, raw_blocks: &[&'a [u8]],
    inodes: u32, metadata_seed: u32, number: u32, indexed: bool, large: bool,
    Ghost(v): Ghost<DirectoryView>) -> (r: Option<Option<HashDirectory<'a>>>)
    requires v.ordinal < v.volume.ordinary.len(), 0 < v.pieces.len(),
        source.view() == ordinary(v).index.header.source,
        source.view() == v.volume.integrity.references.index.header.source,
        htree_topology::source_views(raw_blocks@) == piece_raws(v.pieces),
        inodes == ordinary(v).index.header.inodes, metadata_seed == seed(ordinary(v)),
        number == owner(v), indexed == crate::ea_directory::indexed(ordinary(v)),
        large == crate::ea_directory::large(v.volume),
    ensures match r {
        Some(Some(tree)) => tree.wf() && indexed && tree_bound(v, tree.view()),
        Some(None) => !indexed,
        None => true,
    },
{
    hide(seed);
    if !indexed { return Some(None); }
    if raw_blocks.len() == 0 { return None; }
    let primary = match source.block(0) { Some(primary) => primary, None => { return None; } };
    let superblock = primary.as_slice();
    let hash_seed = State { a: bytes::read_le32(superblock, 1260).unwrap(), b: bytes::read_le32(superblock, 1264).unwrap(),
        c: bytes::read_le32(superblock, 1268).unwrap(), d: bytes::read_le32(superblock, 1272).unwrap() };
    let unsigned = bytes::read_le32(superblock, 1376).unwrap() & 2 != 0;
    let tree = match htree_names::build(raw_blocks, inodes, metadata_seed, hash_seed, unsigned, large) {
        Some(tree) => tree, None => { return None; }
    };
    let recorded_owner = match bytes::read_le32(raw_blocks[0], 0) { Some(owner) => owner, None => { return None; } };
    if recorded_owner != number { return None; }
    assert(tree_bound(v, tree.view())) by { reveal(tree_bound); }
    Some(Some(tree))
}

// Binding depends on the retained source blocks and ordinary owner; the
// optional executable tree is attached only after this check succeeds.
proof fn hash_binding_survives_tree_attachment(before: DirectoryView, after: DirectoryView, tree: HashView)
    requires tree_bound(before, tree), before.volume == after.volume,
        before.ordinal == after.ordinal, before.pieces == after.pieces,
    ensures tree_bound(after, tree),
{ reveal(tree_bound); }

proof fn assemble(v: DirectoryView)
    requires
        (ea_allocation::valid(v.volume) && v.ordinal < v.volume.ordinary.len()),
        (ea_ordinary::valid(ordinary(v)) && ea_ordinary::directory(ordinary(v).parent)),
        (ordinary(v).index == v.volume.integrity.references.index),
        (0 < size(v.volume, ordinary(v)) && size(v.volume, ordinary(v)) % 4096 == 0),
        (0 < v.pieces.len() <= MAX_BLOCKS && v.pieces.len() * 4096 == size(v.volume, ordinary(v))),
        (v.physical.len() == v.pieces.len() && data_claims_within(ordinary(v), v.pieces.len() as u32)),
        ((forall|i: int| 0 <= i < v.pieces.len() ==> #[trigger] checked_piece(v.volume, ordinary(v), v.pieces[i], v.physical[i], i as u32, v.pieces.len() as u32))),
        (match v.tree { Some(tree) => indexed(ordinary(v)) && tree_bound(v, tree), None => !indexed(ordinary(v)) }),
    ensures valid(v),
{ reveal(valid); }

// Discovery exports scalar source bindings only. Keep inode decoding, primary
// block slicing and seed construction out of the collection/assembly context.
struct Discovery {
    number: u32, blocks: u32, inodes: u32, count: u32,
    generation: u32, metadata_seed: u32, indexed: bool, large: bool, position: u64,
}

#[verifier::rlimit(30)]
fn discover_directory<'a>(volume: &Allocation<'_, 'a>, ordinary: &Ordinary,
    source: &crate::snapshot::Snapshot<'a>, ordinal: usize) -> (r: Option<Discovery>)
    requires volume.wf(), ordinary.wf(), ea_allocation::valid(volume.view()),
        ordinal < volume.view().ordinary.len(), ordinary.view() == volume.view().ordinary[ordinal as int],
        ea_ordinary::valid(ordinary.view()), ea_ordinary::directory(ordinary.view().parent),
        source.view() == volume.view().integrity.references.index.header.source,
    ensures volume.wf(), ordinary.wf(), match r {
        Some(p) => p.number == ordinary.view().parent.node.number
            && p.blocks == ordinary.view().index.header.blocks
            && p.inodes == ordinary.view().index.header.inodes
            && 0 < p.count <= MAX_BLOCKS
            && p.large == large(volume.view()) && p.indexed == indexed(ordinary.view())
            && p.generation as nat == bytes::le32(ordinary.view().parent.node.raw, 100)
            && p.metadata_seed == seed(ordinary.view())
            && p.position == ordinary.view().parent.node.position && p.position <= u64::MAX - 40
            && ordinary.view().index == volume.view().integrity.references.index
            && ordinary.view().parent.node.header == ordinary.view().index.header
            && source.view() == ordinary.view().index.header.source
            && 0 < size(volume.view(), ordinary.view())
            && size(volume.view(), ordinary.view()) % 4096 == 0
            && p.count as nat * 4096 == size(volume.view(), ordinary.view())
            && data_claims_within(ordinary.view(), p.count),
        None => true,
    },
{
    hide(crate::crc::fold);
    let number = ordinary.number();
    let index = volume.integrity().reference_census().index();
    let (blocks, inodes, _, _) = index.parameters();
    assert(source.view().len() >= 4096) by { reveal(crate::ea_index::valid); reveal(ea_source::header_valid); }
    let node = match index.node(number) { Some(node) => node, None => { return None; } };
    proof { the_source_node_is_the_same_ordinary_inode(volume.view(), ordinal, node.view()); }
    let raw = node.raw(); let primary = source.block(0).unwrap(); let superblock = primary.as_slice();
    let large = bytes::read_le32(superblock, 1120).unwrap() & 0x4000 != 0;
    let indexed = bytes::read_le32(raw, 32).unwrap() & 0x1000 != 0;
    let huge = index.header().huge_files();
    let size = match inode_size::decode(raw, 4096, huge, large) { Some(size) => size, None => { return None; } };
    if size == 0 || size % 4096 != 0 || size / 4096 > MAX_BLOCKS as u64 { return None; }
    let count = (size / 4096) as u32;
    proof { vstd::arithmetic::div_mod::lemma_fundamental_div_mod(size as int, 4096); }
    if !check_claims(ordinary.claims(), count) { return None; }
    let generation = bytes::read_le32(raw, 100).unwrap();
    let metadata_seed = inode::inode_seed(node.inode_parameters().3, number, generation);
    let position = node.position(); if position > u64::MAX - 40 { return None; }
    Some(Discovery { number, blocks, inodes, count, generation, metadata_seed, indexed, large, position })
}

// The audited extent tree is consumed here, so its detailed context and error
// postconditions never enter the public assembly function's solver context.
#[verifier::rlimit(30)]
fn capture_directory<'a>(volume: &Allocation<'_, 'a>, ordinary: &Ordinary,
    source: &crate::snapshot::Snapshot<'a>, p: &Discovery)
    -> (r: Option<(Vec<Piece<'a>>, Vec<u32>, Vec<&'a [u8]>)>)
    requires volume.wf(), ordinary.wf(),
        source.view() == ordinary.view().index.header.source,
        ordinary.view().index == volume.view().integrity.references.index,
        ordinary.view().parent.node.header == ordinary.view().index.header,
        p.position == ordinary.view().parent.node.position, p.position <= u64::MAX - 40,
        p.blocks == ordinary.view().index.header.blocks,
        0 < p.count <= MAX_BLOCKS, p.inodes == ordinary.view().index.header.inodes,
        p.generation as nat == bytes::le32(ordinary.view().parent.node.raw, 100),
        p.metadata_seed == seed(ordinary.view()), p.indexed == indexed(ordinary.view()),
        p.large == large(volume.view()),
    ensures volume.wf(), ordinary.wf(), match r {
        Some((pieces, physicals, raw)) => pieces.len() == p.count && physicals.len() == p.count && raw.len() == p.count
            && htree_topology::source_views(raw@) == piece_raws(piece_views(pieces@))
            && (forall|j: int| 0 <= j < p.count ==> #[trigger] checked_piece(volume.view(), ordinary.view(),
                piece_views(pieces@)[j], physicals@[j], j as u32, p.count)),
        None => true,
    },
{
    hide(crate::crc::fold);
    let tree = match extent_tree::audit(source, p.position + 40, p.blocks as u64, 4096,
        BlockChecksum::Crc32c(p.metadata_seed), p.blocks as u64 + 1) {
        Ok(tree) => tree, Err(_) => { return None; }
    };
    let _ = tree.checked_nodes();
    assert(tree.context() == ea_ordinary::context(ordinary.view().parent.node));
    collect_pieces(volume, ordinary, source, &tree, p.count, p.inodes,
        p.metadata_seed, p.generation, p.indexed, p.large)
}

#[verifier::rlimit(30)]
pub fn inspect<'a>(volume: &Allocation<'_, 'a>, ordinal: usize) -> (r: Option<Directory<'a>>)
    ensures volume.wf(), ea_allocation::valid(volume.view()), match r { Some(directory) => directory.wf()
        && valid(directory.view()) && directory.view().volume == volume.view() && directory.view().ordinal == ordinal,
        None => true },
{
    hide(crate::crc::fold);
    let ordinary = match volume.ordinary(ordinal) { Some(ordinary) => ordinary, None => { return None; } };
    if !ordinary.is_directory() { return None; }
    let index = volume.integrity().reference_census().index(); let source = index.source();
    let p = match discover_directory(volume, ordinary, source, ordinal) {
        Some(p) => p, None => { return None; }
    };
    let (pieces, physicals, raw_blocks) = match capture_directory(volume, ordinary, source, &p) {
        Some(parts) => parts, None => { return None; }
    };
    let ghost vv = volume.view();
    let ghost captured = DirectoryView { volume: vv, ordinal, pieces: piece_views(pieces@), physical: physicals@, tree: None };
    let tree = match bind_hash_tree(source, &raw_blocks, p.inodes, p.metadata_seed, p.number, p.indexed, p.large, Ghost(captured)) {
        Some(tree) => tree, None => { return None; }
    };
    let ghost tree_view = match &tree { Some(tree) => Some(tree.view()), None => None };
    let ghost view = DirectoryView { volume: vv, ordinal, pieces: piece_views(pieces@), physical: physicals@, tree: tree_view };
    proof {
        match tree_view {
            Some(checked_tree) => {
                assert(tree_bound(captured, checked_tree));
                hash_binding_survives_tree_attachment(captured, view, checked_tree);
            },
            None => { },
        }
        assemble(view);
    }
    Some(Directory { number: p.number, ordinal, pieces, physical: physicals, raw: raw_blocks, tree, checked: Ghost(view) })
}

proof fn checked_piece_at(v: DirectoryView, logical: int)
    requires valid(v), 0 <= logical < v.pieces.len(),
    ensures checked_piece(v.volume, ordinary(v), v.pieces[logical], v.physical[logical], logical as u32, v.pieces.len() as u32),
{ reveal(valid); }

pub proof fn every_directory_piece_comes_from_its_initialized_owned_source_mapping(v: DirectoryView, logical: u32)
    requires valid(v), logical < v.pieces.len(),
    ensures checked_piece(v.volume, ordinary(v), v.pieces[logical as int], v.physical[logical as int], logical, v.pieces.len() as u32),
{
    checked_piece_at(v, logical as int);
    assert((logical as int) as u32 == logical);
}

pub proof fn complete_directory_data_allocations_end_within_the_declared_size(v: DirectoryView, claim: int)
    requires valid(v), 0 <= claim < ordinary(v).claims.len(), ordinary(v).claims[claim].kind == 5,
    ensures ordinary(v).claims[claim].initialized,
        ordinary(v).claims[claim].logical as nat + ordinary(v).claims[claim].length <= v.pieces.len(),
{ reveal(valid); }

pub proof fn source_indexed_directories_retain_complete_hash_and_topology_validation(v: DirectoryView)
    requires valid(v), indexed(ordinary(v)),
    ensures v.tree is Some, tree_bound(v, v.tree.unwrap()),
{ reveal(valid); }

pub proof fn distinct_directory_logical_blocks_have_distinct_physical_sources(v: DirectoryView, left: u32, right: u32)
    requires valid(v), left < v.pieces.len(), right < v.pieces.len(), left != right,
    ensures v.physical[left as int] != v.physical[right as int],
{
    every_directory_piece_comes_from_its_initialized_owned_source_mapping(v, left);
    every_directory_piece_comes_from_its_initialized_owned_source_mapping(v, right);
    reveal(checked_piece);
}

}
