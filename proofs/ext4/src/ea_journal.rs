// SPDX-License-Identifier: MPL-2.0

//! Actual-source inode-8 journal mapping and complete physical reservation.
//! This checks the supported single initialized extent and its sector count.
//! It does not inspect JBD2 headers, journal UUID, cleanliness or recovery state,
//! and supplies no filesystem, callback, device or CortenMM authority.

use vstd::prelude::*;
use crate::{block_claims::{self, Census, Claim, Slot}, bytes,
    ea_index::{self, Index, IndexView}, ea_source::{self, NodeView},
    layout::{self, JournalLayout, LayoutView}, xattr};

verus! {

pub open spec fn claim(mapping: LayoutView) -> Claim {
    Claim { start: mapping.start, length: mapping.journal_blocks, kind: 2,
        inode: 0, generation: 0, logical: 0, initialized: false }
}

pub struct JournalView { pub index: IndexView, pub node: NodeView, pub layout: LayoutView }
#[verifier::opaque]
pub open spec fn valid(v: JournalView) -> bool {
    &&& ea_index::valid(v.index) && ea_source::node_valid(v.node)
    &&& v.node.header == v.index.header && v.node.number == 8
    &&& ea_index::inode_allocated(v.index, 8)
    &&& layout::admitted(v.node.raw, v.index.header.inodes, v.index.header.blocks, v.index.header.seed)
    &&& v.layout.fs_blocks == v.index.header.blocks
    &&& v.layout.start > 1 && 1024 <= v.layout.journal_blocks <= 32768
    &&& v.layout.start as nat + v.layout.journal_blocks <= v.layout.fs_blocks
    &&& v.layout.start as nat == bytes::le32(v.node.raw, 60)
    &&& v.layout.journal_blocks as nat == bytes::le32(v.node.raw, 4) / 4096
    &&& bytes::le32(v.node.raw, 28) == v.layout.journal_blocks as nat * 8
    &&& bytes::le16(v.node.raw, 116) == 0
    &&& xattr::inode_address(v.node.raw) == 0
    &&& xattr::body_geometry(v.node.raw) && !xattr::body_present(v.node.raw)
}

pub struct Journal { layout: JournalLayout, checked: Ghost<JournalView> }
impl Journal {
    pub closed spec fn view(&self) -> JournalView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        valid(self.view()) && self.layout.view() == self.view().layout && self.layout.wf()
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn layout(&self) -> (r: &JournalLayout)
        ensures self.wf(), valid(self.view()), r.wf(), r.view() == self.view().layout,
    { proof { use_type_invariant(self); } &self.layout }
}

pub fn reserve(index: &Index<'_, '_>, initial: Census) -> (r: Option<(Census, Journal)>)
    ensures index.wf(), ea_index::valid(index.view()), initial.wf(), match r {
        Some((next, journal)) => journal.wf() && valid(journal.view()) && journal.view().index == index.view()
            && next.wf() && next.view().roles.len() == initial.view().roles.len()
            && next.view().roles.len() == index.view().header.blocks
            && next.view().claims == initial.view().claims.push(claim(journal.view().layout))
            && block_claims::preserves_occupied(initial.view().roles, next.view().roles)
            && block_claims::mapped_claims(next.view().roles, seq![claim(journal.view().layout)]),
        None => true,
    },
{
    let (blocks, inodes, _, seed) = index.parameters();
    if initial.block_count() != blocks { return None; }
    let node = match index.node(8) { Some(node) => node, None => { return None; } };
    let raw = node.raw();
    let mapping = match layout::from_inode(raw, inodes, blocks, seed) { Some(mapping) => mapping, None => { return None; } };
    let journal_blocks = mapping.blocks(); let start = mapping.physical_start();
    if bytes::read_le16(raw, 116).unwrap() != 0
        || bytes::read_le32(raw, 28).unwrap() as u64 != journal_blocks as u64 * 8
        || xattr::inode_pointer(raw).unwrap() != 0 { return None; }
    let body = match xattr::parse_body(raw, true, inodes) { Some(body) => body, None => { return None; } };
    if body.present() { return None; }
    let record = Claim { start, length: journal_blocks, kind: 2,
        inode: 0, generation: 0, logical: 0, initialized: false };
    assert(record == claim(mapping.view()));
    let next = match initial.claim(record) { Ok(next) => next, Err(_) => { return None; } };
    let ghost view = JournalView { index: index.view(), node: node.view(), layout: mapping.view() };
    assert(xattr::body_geometry(node.view().raw)) by { reveal(xattr::valid_body); }
    assert(valid(view)) by { reveal(valid); }
    proof {
        assert(next.view().claims =~= initial.view().claims + seq![record]);
        block_claims::every_appended_claim_has_its_exact_physical_slots(&next, initial.view().claims, seq![record]);
    }
    Some((next, Journal { layout: mapping, checked: Ghost(view) }))
}

pub proof fn the_reserved_journal_uses_the_original_allocated_inode_eight(v: JournalView)
    requires valid(v),
    ensures v.node.number == 8, v.node.header == v.index.header,
        ea_index::inode_allocated(v.index, 8), ea_source::node_valid(v.node),
        layout::admitted(v.node.raw, v.index.header.inodes, v.index.header.blocks, v.index.header.seed),
{ reveal(valid); }

pub proof fn every_reserved_journal_block_has_the_journal_role(v: JournalView, roles: Seq<Slot>, logical: u32)
    requires valid(v), block_claims::mapped_claims(roles, seq![claim(v.layout)]), logical < v.layout.journal_blocks,
    ensures v.layout.start as nat + logical < roles.len(),
        roles[(v.layout.start as nat + logical) as int].kind == 2,
{
    // The exact singleton mapping already supplies the physical bounds and
    // role. Leave the larger source admission predicate opaque in this query.
    let record = claim(v.layout);
    let records = seq![record];
    let block = v.layout.start as int + logical;
    assert(records.len() == 1 && records[0] == record);
    assert(block_claims::mapped_claims(roles, records));
    reveal(block_claims::mapped_claims);
    assert(block_claims::valid_claim(records[0], roles.len()));
    assert(block_claims::covers(records[0], block));
    assert(0 <= block < roles.len());
    assert(roles[block] == block_claims::at(records[0], block));
    assert(block_claims::at(record, block).kind == 2);
}

pub proof fn journal_sectors_exclude_parent_ea_and_external_attribute_charges(v: JournalView)
    requires valid(v),
    ensures bytes::le32(v.node.raw, 28) == 8 * v.layout.journal_blocks as nat,
        bytes::le16(v.node.raw, 116) == 0, xattr::inode_address(v.node.raw) == 0,
        !xattr::body_present(v.node.raw),
{ reveal(valid); }

}
