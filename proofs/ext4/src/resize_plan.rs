// SPDX-License-Identifier: MPL-2.0

//! Checked append-only online-grow planning and geometry publication.
//! Linux resize-inode pointer words and META_BG locations are interpreted by
//! meta_bg. This plan does not contain metadata after-images or authorize I/O.
//! JBD2 credit closure, checksummed super/group encoding, source capture and
//! CortenMM/OSTD publication/driver refinement remain separate.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, meta_bg::{self, Geometry, DescriptorAddress}};

verus! {

pub const MAX_GROW_GROUPS: u32 = 65536;
pub const MAX_DESCRIPTOR_CHANGES: u32 = 4096;

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    Geometry, Shrink, DeviceTooSmall, InodeOverflow, Capacity,
    SparseSuper2, Reservation, LastGroupTooSmall, WrongPhase, Failed, Stale,
}

#[derive(Clone, Copy)]
pub struct GroupEdit {
    pub group: u32,
    pub first: u64,
    pub old_end: u64,
    pub new_end: u64,
    pub new_group: bool,
    pub descriptor: DescriptorAddress,
    pub inode_table_blocks: u32,
    pub base_metadata_blocks: u32,
}

pub struct ReservedGdt {
    number: u32,
    primary: u64,
    geometry: Geometry,
    double_indirect: Vec<u8>,
    backup_words: Vec<u8>,
}

pub struct VersionedGeometry { geometry: Geometry, epoch: u64 }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Event {
    MetadataInitialized,
    SubmitLog,
    LogFlushSucceeded,
    SubmitCommit,
    CommitBecameDurable,
    CommitFlushSucceeded,
    SubmitHomes,
    HomesBecameDurable,
    HomeFlushSucceeded,
    SubmitTail,
    TailBecameDurable,
    TailFlushSucceeded,
    Fail,
    Abort,
}

pub struct Plan {
    before: Geometry,
    after: Geometry,
    before_epoch: u64,
    after_epoch: u64,
    requested_blocks: u64,
    descriptor_changes: u32,
    consumed_reserved_gdt: u16,
    convert_to_meta_bg: bool,
    release_resize_double_indirect: u64,
    edits: Vec<GroupEdit>,
    // 0=prepared,1=initialized,2=log issued,3=log stable,4=commit issued,
    // 5=commit stable,6=homes issued,7=homes stable,8=published,
    // 9=tail issued,10=retired.
    phase: u8,
    faulted: bool,
    commit_durable: bool,
    homes_durable: bool,
    tail_durable: bool,
}


pub struct GeometryVersion { pub geometry: Geometry, pub epoch: u64 }

pub struct ReservationView {
    pub number: u32, pub primary: u64, pub geometry: Geometry,
    pub double_indirect: Seq<u8>, pub backup_words: Seq<u8>,
}

#[verifier::ext_equal]
pub struct State {
    pub phase: u8, pub faulted: bool, pub commit_durable: bool,
    pub homes_durable: bool, pub tail_durable: bool,
}

pub struct PlanView {
    pub before: Geometry, pub after: Geometry,
    pub before_epoch: u64, pub after_epoch: u64, pub requested_blocks: u64,
    pub descriptor_changes: u32, pub consumed_reserved_gdt: u16,
    pub convert_to_meta_bg: bool, pub release_resize_double_indirect: u64,
    pub edits: Seq<GroupEdit>, pub state: State,
}

pub open spec fn version_valid(v: GeometryVersion) -> bool {
    meta_bg::valid(v.geometry) && v.epoch > 0
}

pub open spec fn fixed_geometry(a: Geometry, b: Geometry) -> bool {
    a.first_data == b.first_data && a.blocks_per_group == b.blocks_per_group
        && a.block_bytes == b.block_bytes && a.descriptor_bytes == b.descriptor_bytes
        && a.cluster_ratio == b.cluster_ratio && a.bigalloc == b.bigalloc
        && a.sparse_super == b.sparse_super && a.sparse_super2 == b.sparse_super2
        && a.backup0 == b.backup0 && a.backup1 == b.backup1
}

pub open spec fn state_valid(s: State) -> bool {
    &&& s.phase <= 10
    &&& (s.commit_durable ==> s.phase >= 4)
    &&& (s.homes_durable ==> s.commit_durable && s.phase >= 6)
    &&& (s.tail_durable ==> s.homes_durable && s.phase >= 9)
    &&& (s.phase >= 5 ==> s.commit_durable)
    &&& (s.phase >= 7 ==> s.homes_durable)
    &&& (s.phase == 10 ==> s.tail_durable)
}

pub open spec fn enabled(s: State, e: Event) -> bool {
    match e {
        Event::Fail | Event::Abort => true,
        Event::CommitBecameDurable => s.phase >= 4,
        Event::HomesBecameDurable => s.phase >= 6 && s.commit_durable,
        Event::TailBecameDurable => s.phase >= 9 && s.homes_durable,
        _ => !s.faulted && match e {
            Event::MetadataInitialized => s.phase == 0,
            Event::SubmitLog => s.phase == 1,
            Event::LogFlushSucceeded => s.phase == 2,
            Event::SubmitCommit => s.phase == 3,
            Event::CommitFlushSucceeded => s.phase == 4,
            Event::SubmitHomes => s.phase == 5,
            Event::HomeFlushSucceeded => s.phase == 6,
            Event::SubmitTail => s.phase == 8,
            Event::TailFlushSucceeded => s.phase == 9,
            _ => false,
        },
    }
}

pub open spec fn step(s: State, e: Event) -> State {
    if !enabled(s, e) { s }
    else { match e {
        Event::Fail | Event::Abort => State { faulted: true, ..s },
        Event::CommitBecameDurable => State { commit_durable: true, ..s },
        Event::HomesBecameDurable => State { homes_durable: true, ..s },
        Event::TailBecameDurable => State { tail_durable: true, ..s },
        Event::CommitFlushSucceeded => State { phase: 5, commit_durable: true, ..s },
        Event::HomeFlushSucceeded => State { phase: 7, homes_durable: true, ..s },
        Event::TailFlushSucceeded => State { phase: 10, tail_durable: true, ..s },
        _ => State { phase: (s.phase + 1) as u8, ..s },
    } }
}

pub open spec fn first_grow_group(before: Geometry, after: Geometry) -> nat {
    if before.blocks == after.blocks { after.groups as nat }
    else if before.blocks_per_group > 0
        && (before.blocks as int - before.first_data as int) % before.blocks_per_group as int == 0 {
        before.groups as nat
    } else if before.groups > 0 { (before.groups - 1) as nat } else { 0nat }
}

pub open spec fn edit_valid(before: Geometry, after: Geometry, edit: GroupEdit) -> bool {
    &&& before.groups > 0 && before.groups - 1 <= edit.group < after.groups
    &&& edit.first as nat == meta_bg::first_block(after, edit.group)
    &&& edit.first <= edit.old_end < edit.new_end <= after.blocks
    &&& edit.new_end as nat <= edit.first as nat + after.blocks_per_group
    &&& edit.new_group == (edit.group >= before.groups)
    &&& edit.old_end == if edit.new_group { edit.first } else { before.blocks }
    &&& edit.new_end as nat == if (after.blocks as nat) < edit.first as nat + after.blocks_per_group {
        after.blocks as nat
    } else { (edit.first as nat + after.blocks_per_group) as nat }
    &&& edit.descriptor.block < after.blocks
    &&& edit.descriptor.block as nat == meta_bg::descriptor_location(after,
        (1024nat / after.block_bytes as nat) as u64, edit.group / (after.block_bytes / after.descriptor_bytes))
    &&& edit.descriptor.offset == (edit.group % (after.block_bytes / after.descriptor_bytes)) * after.descriptor_bytes
    &&& edit.descriptor.offset as nat + after.descriptor_bytes <= after.block_bytes
    &&& edit.base_metadata_blocks as nat == meta_bg::base_blocks(after, edit.group)
    &&& edit.inode_table_blocks > 0
    &&& (edit.new_group ==> edit.base_metadata_blocks as nat + 2 + edit.inode_table_blocks + after.cluster_ratio
        < edit.new_end as nat - edit.first)
}

pub open spec fn valid(v: PlanView) -> bool {
    &&& meta_bg::valid(v.before) && meta_bg::valid(v.after)
    &&& fixed_geometry(v.before, v.after)
    &&& v.before.blocks <= v.after.blocks <= v.requested_blocks
    &&& v.before.groups <= v.after.groups <= v.before.groups as nat + MAX_GROW_GROUPS
    &&& v.before_epoch > 0
    &&& v.after_epoch as nat == if v.before.blocks == v.after.blocks {
        v.before_epoch as nat
    } else { v.before_epoch as nat + 1 }
    &&& v.descriptor_changes <= MAX_DESCRIPTOR_CHANGES
    &&& v.descriptor_changes as int == meta_bg::descriptors(v.after) as int - meta_bg::descriptors(v.before) as int
    &&& v.edits.len() <= MAX_GROW_GROUPS as nat + 1
    &&& first_grow_group(v.before, v.after) <= v.after.groups
    &&& v.edits.len() as int == v.after.groups as int - first_grow_group(v.before, v.after) as int
    &&& (forall|i: int| 0 <= i < v.edits.len() ==>
        (#[trigger] v.edits[i]).group as int == first_grow_group(v.before, v.after) as int + i)
    &&& v.consumed_reserved_gdt <= v.before.reserved_gdt
    &&& if v.convert_to_meta_bg { v.consumed_reserved_gdt == v.before.reserved_gdt }
        else { v.consumed_reserved_gdt as nat + v.after.reserved_gdt == v.before.reserved_gdt }
    &&& (forall|i: int| 0 <= i < v.edits.len() ==> edit_valid(v.before, v.after, #[trigger] v.edits[i]))
    &&& (forall|i: int, j: int| 0 <= i < j < v.edits.len() ==> (#[trigger] v.edits[i]).group < (#[trigger] v.edits[j]).group)
    &&& v.convert_to_meta_bg == (!v.before.meta_bg && v.after.meta_bg)
    &&& ((v.release_resize_double_indirect != 0) == (v.convert_to_meta_bg && v.before.resize_inode))
    &&& (v.release_resize_double_indirect != 0 ==> v.release_resize_double_indirect < v.before.blocks)
    &&& state_valid(v.state)
}

pub proof fn every_enabled_resize_event_preserves_durable_order(s: State, e: Event)
    requires state_valid(s), enabled(s, e),
    ensures state_valid(step(s, e)),
        s.commit_durable ==> step(s, e).commit_durable,
        s.homes_durable ==> step(s, e).homes_durable,
        s.tail_durable ==> step(s, e).tail_durable,
{
}

pub proof fn abort_preserves_the_durable_geometry_choice(s: State)
    requires state_valid(s),
    ensures step(s, Event::Abort).faulted,
        step(s, Event::Abort).commit_durable == s.commit_durable,
        enabled(step(s, Event::Abort), Event::CommitBecameDurable) == (s.phase >= 4),
{
}

fn same_geometry(a: Geometry, b: Geometry) -> (r: bool)
    ensures r == (a == b),
{
    a.blocks == b.blocks && a.first_data == b.first_data
        && a.blocks_per_group == b.blocks_per_group && a.groups == b.groups
        && a.block_bytes == b.block_bytes && a.descriptor_bytes == b.descriptor_bytes
        && a.cluster_ratio == b.cluster_ratio && a.bigalloc == b.bigalloc
        && a.meta_bg == b.meta_bg && a.first_meta_bg == b.first_meta_bg
        && a.resize_inode == b.resize_inode && a.reserved_gdt == b.reserved_gdt
        && a.sparse_super == b.sparse_super && a.sparse_super2 == b.sparse_super2
        && a.backup0 == b.backup0 && a.backup1 == b.backup1
}

fn copy(raw: &[u8]) -> (r: Vec<u8>)
    ensures r@ == raw@,
{
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len(), out@ == raw@.take(i as int),
        decreases raw.len() - i,
    {
        out.push(raw[i]); i += 1;
    }
    out
}

impl VersionedGeometry {
    pub closed spec fn view(&self) -> GeometryVersion {
        GeometryVersion { geometry: self.geometry, epoch: self.epoch }
    }
    pub closed spec fn wf(&self) -> bool { version_valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn new(geometry: Geometry, epoch: u64) -> (r: Option<Self>)
        ensures match r { Some(v) => v.wf() && v.view() == (GeometryVersion { geometry, epoch }), None => true },
    {
        if !meta_bg::is_valid(geometry) || epoch == 0 { return None; }
        Some(VersionedGeometry { geometry, epoch })
    }
    pub fn geometry(&self) -> (r: Geometry)
        ensures self.wf(), r == self.view().geometry, meta_bg::valid(r),
    { proof { use_type_invariant(self); } self.geometry }
    pub fn epoch(&self) -> (r: u64) ensures self.wf(), r == self.view().epoch, r > 0,
    { proof { use_type_invariant(self); } self.epoch }
}

impl ReservedGdt {
    pub closed spec fn view(&self) -> ReservationView {
        ReservationView { number: self.number, primary: self.primary, geometry: self.geometry,
            double_indirect: self.double_indirect@, backup_words: self.backup_words@ }
    }
    pub closed spec fn wf(&self) -> bool {
        meta_bg::valid(self.geometry) && self.geometry.resize_inode && !self.geometry.meta_bg
            && self.primary < self.geometry.blocks
            && self.double_indirect.len() == self.geometry.block_bytes
            && self.backup_words.len() == self.geometry.block_bytes
            && meta_bg::resize_pointer_spec(self.geometry, self.double_indirect@, self.number, self.primary)
            && meta_bg::resize_backups_spec(self.geometry, self.backup_words@, self.geometry.groups, self.primary)
            && self.number as nat >= meta_bg::descriptors(self.geometry)
            && (self.number as nat) < meta_bg::descriptors(self.geometry) + self.geometry.reserved_gdt
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    /// Verify actual legacy inode-7 double-indirect and ordered backup words.
    /// Raw block provenance and allocation ownership are supplied separately.
    pub fn inspect(g: Geometry, number: u32, logical_super: u64,
        double_indirect: &[u8], primary_words: &[u8]) -> (r: Result<Self, Error>)
        ensures match r { Ok(receipt) => receipt.wf() && receipt.view().geometry == g
            && receipt.view().number == number && receipt.view().double_indirect == double_indirect@
            && receipt.view().backup_words == primary_words@, Err(_) => true },
    {
        if !meta_bg::is_valid(g) || !g.resize_inode || g.meta_bg || g.sparse_super2 {
            return Err(Error::Geometry);
        }
        let old = match meta_bg::descriptor_blocks(g) { Some(n) => n, None => { return Err(Error::Geometry); } };
        if number < old || (number as u64) >= old as u64 + g.reserved_gdt as u64
            || number as u64 + 1 > 18446744073709551615u64 - logical_super {
            return Err(Error::Reservation);
        }
        let primary = logical_super + number as u64 + 1;
        if primary >= g.blocks { return Err(Error::Reservation); }
        if !meta_bg::resize_pointer_reserved(g, double_indirect, number, primary)
            || !meta_bg::resize_backups_reserved(g, primary_words, g.groups, primary) {
            return Err(Error::Reservation);
        }
        Ok(ReservedGdt { number, primary, geometry: g,
            double_indirect: copy(double_indirect), backup_words: copy(primary_words) })
    }

    pub fn descriptor_number(&self) -> (r: u32) ensures self.wf(), r == self.view().number,
    { proof { use_type_invariant(self); } self.number }
    pub fn primary_block(&self) -> (r: u64) ensures self.wf(), r == self.view().primary, r < self.view().geometry.blocks,
    { proof { use_type_invariant(self); } self.primary }
}

/// Structural check of the actual legacy resize inode's i_block words.
/// Inode checksum and complete pointer ownership are outside this helper.
pub fn resize_double_indirect(g: Geometry, raw: &[u8]) -> (r: Option<u64>)
    ensures match r { Some(block) => meta_bg::valid(g) && raw.len() >= 128 && 0 < block < g.blocks
        && block as nat == bytes::le32(raw@, 92)
        && bytes::le16(raw@, 0) as u16 & 0xf000 == 0x8000
        && bytes::le32(raw@, 32) as u32 & 0x10080000 == 0
        && (forall|i: int| 0 <= i < 15 && i != 13 ==> #[trigger] bytes::le32(raw@, 40+i*4) == 0),
        None => true },
{
    if !meta_bg::is_valid(g) || !g.resize_inode || g.meta_bg || raw.len() < 128
        || bytes::read_le16(raw, 0).unwrap() & 0xf000 != 0x8000
        || bytes::read_le32(raw, 32).unwrap() & 0x10080000 != 0 { return None; }
    let mut index = 0usize;
    while index < 15
        invariant index <= 15, raw.len() >= 128,
            forall|i: int| 0 <= i < index && i != 13 ==> #[trigger] bytes::le32(raw@, 40+i*4) == 0,
        decreases 15 - index,
    {
        if index != 13 && bytes::read_le32(raw, 40 + index * 4).unwrap() != 0 { return None; }
        index += 1;
    }
    let block = bytes::read_le32(raw, 92).unwrap() as u64;
    if block == 0 || block >= g.blocks { None } else { Some(block) }
}

fn target_geometry(before: Geometry, blocks: u64) -> (r: Option<Geometry>)
    ensures match r { Some(g) => meta_bg::valid(g) && g.blocks == blocks
        && before.blocks <= g.blocks && before.groups <= g.groups
        && fixed_geometry(before, g) && (blocks == before.blocks ==> g == before)
        && g.reserved_gdt <= before.reserved_gdt
        && (!before.meta_bg && g.meta_bg ==> !g.resize_inode && g.reserved_gdt == 0
            && g.first_meta_bg as nat == meta_bg::descriptors(before) + before.reserved_gdt
            && meta_bg::descriptors(g) > meta_bg::descriptors(before) + before.reserved_gdt)
        && (!before.meta_bg && !g.meta_bg ==> g.first_meta_bg == before.first_meta_bg
            && g.resize_inode == before.resize_inode
            && meta_bg::descriptors(g) + g.reserved_gdt == meta_bg::descriptors(before) + before.reserved_gdt)
        && (before.meta_bg ==> g.meta_bg && g.resize_inode == before.resize_inode
            && g.first_meta_bg == before.first_meta_bg && g.reserved_gdt == before.reserved_gdt), None => true },
{
    if !meta_bg::is_valid(before) || blocks < before.blocks || blocks <= before.first_data { return None; }
    proof { meta_bg::geometry_facts(before); }
    let span = blocks - before.first_data;
    let quotient = span / before.blocks_per_group as u64;
    let remainder = span % before.blocks_per_group as u64;
    if quotient > 4294967295 || (quotient == 4294967295 && remainder != 0) { return None; }
    let groups = (quotient + if remainder == 0 { 0u64 } else { 1u64 }) as u32;
    if groups < before.groups { return None; }
    let old_desc = match meta_bg::descriptor_blocks(before) { Some(n) => n, None => { return None; } };
    let per = before.block_bytes / before.descriptor_bytes;
    let new_count = (groups as u64 + per as u64 - 1) / per as u64;
    proof { assert(new_count <= groups) by (nonlinear_arith)
        requires per > 0, groups > 0,
            new_count as int == (groups as int + per as int - 1) / per as int; }
    let new_desc = new_count as u32;
    if new_desc < old_desc { return None; }
    let available = old_desc as u64 + before.reserved_gdt as u64;
    let mut after = before;
    after.blocks = blocks;
    after.groups = groups;
    if !before.meta_bg {
        if (new_desc as u64) <= available {
            let used = new_desc - old_desc;
            if used > before.reserved_gdt as u32 { return None; }
            after.reserved_gdt = before.reserved_gdt - used as u16;
        } else {
            if available > 4294967295 { return None; }
            after.meta_bg = true;
            after.first_meta_bg = available as u32;
            after.resize_inode = false;
            after.reserved_gdt = 0;
        }
    }
    if !meta_bg::is_valid(after) { None } else { Some(after) }
}

fn room_in_last_group(g: Geometry, table_blocks: u32) -> (r: bool) {
    if !meta_bg::is_valid(g) || g.groups == 0 { return false; }
    let first = match meta_bg::group_first(g, g.groups - 1) { Some(b) => b, None => { return false; } };
    let overhead = match meta_bg::base_metadata_blocks(g, g.groups - 1) {
        Some(n) => n as u64, None => { return false; },
    };
    let required = overhead + 2 + table_blocks as u64 + g.cluster_ratio as u64;
    required < g.blocks - first
}

pub fn prepare(before: &VersionedGeometry, requested_blocks: u64, device_blocks: u64,
    inodes_per_group: u32, inode_bytes: u32, logical_super: u64,
    reservations: &[ReservedGdt], resize_inode_raw: &[u8]) -> (r: Result<Plan, Error>)
    ensures before.wf(), match r { Ok(plan) => plan.wf() && valid(plan.view())
        && plan.view().before == before.view().geometry && plan.view().before_epoch == before.view().epoch
        && plan.view().requested_blocks == requested_blocks
        && plan.view().after.blocks <= device_blocks, Err(_) => true },
{
    proof { use_type_invariant(before); }
    let old = before.geometry;
    if !meta_bg::is_valid(old) || before.epoch == 0
        || old.meta_bg && old.resize_inode || old.reserved_gdt != 0 && !old.resize_inode
        || logical_super != 1024u64 / old.block_bytes as u64 {
        return Err(Error::Geometry);
    }
    proof { meta_bg::geometry_facts(old); }
    if old.sparse_super2 { return Err(Error::SparseSuper2); }
    if requested_blocks > device_blocks { return Err(Error::DeviceTooSmall); }
    let mut target = requested_blocks;
    if old.bigalloc {
        let ratio = old.cluster_ratio as u64;
        let remainder = target % ratio;
        proof { assert(remainder <= target) by (nonlinear_arith)
            requires ratio > 0, remainder as int == target as int % ratio as int; }
        target -= remainder;
    }
    if target < old.blocks { return Err(Error::Shrink); }
    if target > old.blocks && before.epoch == 18446744073709551615 { return Err(Error::Stale); }
    if inode_bytes < 128 || inode_bytes > old.block_bytes || inode_bytes > 65535
        || inode_bytes & (inode_bytes - 1) != 0 { return Err(Error::Geometry); }
    let inodes_per_block = old.block_bytes / inode_bytes;
    proof { assert(inodes_per_block > 0) by (nonlinear_arith)
        requires 0 < inode_bytes <= old.block_bytes,
            inodes_per_block as int == old.block_bytes as int / inode_bytes as int; }
    if inodes_per_group < inodes_per_block || inodes_per_group > old.block_bytes * 8
        || inodes_per_group % inodes_per_block != 0 { return Err(Error::Geometry); }
    let table_blocks = inodes_per_group / inodes_per_block;
    proof { assert(table_blocks > 0) by (nonlinear_arith)
        requires 0 < inodes_per_block <= inodes_per_group,
            table_blocks as int == inodes_per_group as int / inodes_per_block as int; }
    let mut after = match target_geometry(old, target) { Some(g) => g, None => { return Err(Error::Geometry); } };
    if target != old.blocks && !room_in_last_group(after, table_blocks) {
        target = match meta_bg::group_first(after, after.groups - 1) {
            Some(first) => first, None => { return Err(Error::Geometry); },
        };
        if target < old.blocks { return Err(Error::LastGroupTooSmall); }
        after = match target_geometry(old, target) { Some(g) => g, None => { return Err(Error::Geometry); } };
        if target != old.blocks && !room_in_last_group(after, table_blocks) { return Err(Error::LastGroupTooSmall); }
    }
    if (after.groups as u64) > 4294967295u64 / inodes_per_group as u64 { return Err(Error::InodeOverflow); }
    if after.groups < old.groups || after.groups - old.groups > MAX_GROW_GROUPS { return Err(Error::Capacity); }
    let old_desc = match meta_bg::descriptor_blocks(old) { Some(n) => n, None => { return Err(Error::Geometry); } };
    let new_desc = match meta_bg::descriptor_blocks(after) { Some(n) => n, None => { return Err(Error::Geometry); } };
    if new_desc < old_desc || new_desc - old_desc > MAX_DESCRIPTOR_CHANGES { return Err(Error::Capacity); }
    let converted = !old.meta_bg && after.meta_bg;
    let consumed = if converted { old.reserved_gdt } else { old.reserved_gdt - after.reserved_gdt };
    if reservations.len() != consumed as usize { return Err(Error::Reservation); }
    proof {
        if converted {
            assert(old_desc as nat + consumed == after.first_meta_bg);
        } else if !old.meta_bg {
            assert(old_desc as nat + consumed == new_desc);
        } else {
            assert(consumed == 0);
        }
        assert(old_desc as nat + reservations.len() <= 4294967295);
    }
    let mut i = 0usize;
    while i < reservations.len()
        invariant i <= reservations.len(), old_desc as u64 + reservations.len() <= 4294967296,
            before.wf(), before.view().geometry == old,
            meta_bg::valid(old), meta_bg::valid(after), table_blocks > 0,
            logical_super == 1024u64 / old.block_bytes as u64,
            reservations.len() == consumed,
        decreases reservations.len() - i,
    {
        let receipt = &reservations[i];
        if receipt.number as u64 != old_desc as u64 + i as u64
            || !same_geometry(receipt.geometry, old)
            || receipt.primary != logical_super + receipt.number as u64 + 1
            || !meta_bg::resize_pointer_reserved(old, &receipt.double_indirect, receipt.number, receipt.primary)
            || !meta_bg::resize_backups_reserved(old, &receipt.backup_words, old.groups, receipt.primary) {
            return Err(Error::Reservation);
        }
        i += 1;
    }
    let release_resize_double_indirect = if converted && old.resize_inode {
        match resize_double_indirect(old, resize_inode_raw) {
            Some(block) => block, None => { return Err(Error::Reservation); },
        }
    } else { 0 };
    let mut edits = Vec::<GroupEdit>::new();
    if target > old.blocks {
        let first_changed = if (old.blocks - old.first_data) % old.blocks_per_group as u64 == 0 {
            old.groups
        } else { old.groups - 1 };
        if first_changed >= after.groups { return Err(Error::Geometry); }
        let mut group = first_changed;
        while group < after.groups
            invariant group <= after.groups, group >= old.groups - 1,
                before.wf(), before.view().geometry == old,
                logical_super == 1024u64 / old.block_bytes as u64,
                meta_bg::valid(old), meta_bg::valid(after), fixed_geometry(old, after),
                old.groups > 0, old.groups <= after.groups,
                after.groups - old.groups <= MAX_GROW_GROUPS, table_blocks > 0,
                first_changed as nat == first_grow_group(old, after), first_changed <= group,
                edits.len() as int == group as int - first_changed as int,
                edits.len() <= MAX_GROW_GROUPS as nat + 1,
                forall|i: int| 0 <= i < edits.len() ==> (#[trigger] edits@[i]).group as int == first_changed as int + i,
                forall|i: int| 0 <= i < edits.len() ==> edit_valid(old, after, #[trigger] edits@[i]),
                forall|i: int| 0 <= i < edits.len() ==> (#[trigger] edits@[i]).group < group,
                forall|i: int, j: int| 0 <= i < j < edits.len() ==> (#[trigger] edits@[i]).group < (#[trigger] edits@[j]).group,
            decreases after.groups - group,
        {
            let first = match meta_bg::group_first(after, group) { Some(b) => b, None => { return Err(Error::Geometry); } };
            let available = after.blocks - first;
            let length = if available < after.blocks_per_group as u64 { available } else { after.blocks_per_group as u64 };
            let end = first + length;
            let old_end = if group < old.groups { old.blocks } else { first };
            if end <= old_end { return Err(Error::Geometry); }
            {
                let descriptor = match meta_bg::locate(after, logical_super, group) {
                    Some(address) => address, None => { return Err(Error::Geometry); },
                };
                let overhead = match meta_bg::base_metadata_blocks(after, group) {
                    Some(n) => n, None => { return Err(Error::Geometry); },
                };
                if group >= old.groups && overhead as u64 + 2 + table_blocks as u64 + after.cluster_ratio as u64 >= length {
                    return Err(Error::LastGroupTooSmall);
                }
                if old_end < first || old_end >= end { return Err(Error::Geometry); }
                if edits.len() == MAX_GROW_GROUPS as usize + 1 { return Err(Error::Capacity); }
                let edit = GroupEdit { group, first, old_end, new_end: end, new_group: group >= old.groups,
                    descriptor, inode_table_blocks: table_blocks, base_metadata_blocks: overhead };
                proof {
                    assert(logical_super as nat == 1024nat / (after.block_bytes as nat));
                    assert(logical_super == (1024nat / (after.block_bytes as nat)) as u64);
                    assert(end as nat == if (after.blocks as nat) < first as nat + after.blocks_per_group {
                        after.blocks as nat
                    } else { (first as nat + after.blocks_per_group) as nat });
                    assert(end as nat - first == length);
                }
                assert(edit_valid(old, after, edit));
                edits.push(edit);
            }
            group += 1;
        }
    }
    let ghost checked = PlanView { before: old, after, before_epoch: before.epoch,
        after_epoch: if target == old.blocks { before.epoch } else { (before.epoch + 1) as u64 },
        requested_blocks, descriptor_changes: (new_desc - old_desc) as u32,
        consumed_reserved_gdt: consumed, convert_to_meta_bg: converted,
        release_resize_double_indirect, edits: edits@,
        state: State { phase: if target == old.blocks { 10 } else { 0 }, faulted: false,
            commit_durable: target == old.blocks, homes_durable: target == old.blocks, tail_durable: target == old.blocks } };
    assert(first_grow_group(old, after) <= after.groups);
    assert(checked.edits.len() as int == after.groups as int - first_grow_group(old, after) as int);
    assert forall|i: int| 0 <= i < checked.edits.len() implies
        (#[trigger] checked.edits[i]).group as int == first_grow_group(old, after) as int + i by { }
    assert forall|i: int| 0 <= i < checked.edits.len() implies edit_valid(old, after, #[trigger] checked.edits[i]) by { }
    assert(checked.descriptor_changes as int == meta_bg::descriptors(after) as int - meta_bg::descriptors(old) as int);
    assert(valid(checked));
    Ok(Plan { before: old, after, before_epoch: before.epoch, after_epoch: if target == old.blocks { before.epoch } else { before.epoch + 1 },
        requested_blocks, descriptor_changes: new_desc - old_desc, consumed_reserved_gdt: consumed,
        convert_to_meta_bg: converted, release_resize_double_indirect, edits,
        phase: if target == old.blocks { 10 } else { 0 }, faulted: false,
        commit_durable: target == old.blocks, homes_durable: target == old.blocks, tail_durable: target == old.blocks })
}

impl Plan {
    pub closed spec fn view(&self) -> PlanView {
        PlanView { before: self.before, after: self.after,
            before_epoch: self.before_epoch, after_epoch: self.after_epoch,
            requested_blocks: self.requested_blocks, descriptor_changes: self.descriptor_changes,
            consumed_reserved_gdt: self.consumed_reserved_gdt, convert_to_meta_bg: self.convert_to_meta_bg,
            release_resize_double_indirect: self.release_resize_double_indirect, edits: self.edits@,
            state: State { phase: self.phase, faulted: self.faulted,
                commit_durable: self.commit_durable, homes_durable: self.homes_durable, tail_durable: self.tail_durable } }
    }
    pub closed spec fn wf(&self) -> bool { valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn old_geometry(&self) -> (r: Geometry) ensures self.wf(), r == self.view().before,
    { proof { use_type_invariant(self); } self.before }
    pub fn new_geometry(&self) -> (r: Geometry) ensures self.wf(), r == self.view().after,
    { proof { use_type_invariant(self); } self.after }
    pub fn requested_blocks(&self) -> (r: u64) ensures self.wf(), r == self.view().requested_blocks,
    { proof { use_type_invariant(self); } self.requested_blocks }
    pub fn target_blocks(&self) -> (r: u64) ensures self.wf(), r == self.view().after.blocks,
    { proof { use_type_invariant(self); } self.after.blocks }
    pub fn new_epoch(&self) -> (r: u64) ensures self.wf(), r == self.view().after_epoch,
    { proof { use_type_invariant(self); } self.after_epoch }
    pub fn changes(&self) -> (r: &[GroupEdit]) ensures self.wf(), r@ == self.view().edits,
    { proof { use_type_invariant(self); } self.edits.as_slice() }
    pub fn descriptor_changes(&self) -> (r: u32) ensures self.wf(), r == self.view().descriptor_changes,
    { proof { use_type_invariant(self); } self.descriptor_changes }
    pub fn consumed_reserved(&self) -> (r: u16) ensures self.wf(), r == self.view().consumed_reserved_gdt,
    { proof { use_type_invariant(self); } self.consumed_reserved_gdt }
    pub fn converts_to_meta_bg(&self) -> (r: bool) ensures self.wf(), r == self.view().convert_to_meta_bg,
    { proof { use_type_invariant(self); } self.convert_to_meta_bg }
    pub fn released_resize_pointer(&self) -> (r: u64) ensures self.wf(), r == self.view().release_resize_double_indirect,
    { proof { use_type_invariant(self); } self.release_resize_double_indirect }
    pub fn failed(&self) -> (r: bool) ensures self.wf(), r == self.view().state.faulted,
    { proof { use_type_invariant(self); } self.faulted }
    pub fn finished(&self) -> (r: bool)
        ensures self.wf(), r == (!self.view().state.faulted && self.view().state.phase == 10),
            r ==> self.view().state.commit_durable && self.view().state.homes_durable && self.view().state.tail_durable,
    { proof { use_type_invariant(self); } !self.faulted && self.phase == 10 }
    /// Geometry selected for replay by the admitted durable-commit fact.
    /// The raw crash medium still requires journal replay before discovery.
    pub fn crash_geometry(&self) -> (r: Geometry)
        ensures self.wf(), r == if self.view().state.commit_durable { self.view().after } else { self.view().before },
    { proof { use_type_invariant(self); } if self.commit_durable { self.after } else { self.before } }

    /// Persist events can arrive after failure/abort. They are durable facts,
    /// not acknowledgements; actual device refinement must establish them.
    pub fn advance(&mut self, event: Event) -> (r: Result<(), Error>)
        ensures final(self).wf(), final(self).view().before == old(self).view().before,
            final(self).view().after == old(self).view().after,
            final(self).view().edits == old(self).view().edits,
            match r {
                Ok(()) => enabled(old(self).view().state, event)
                    && final(self).view() == (PlanView { state: step(old(self).view().state, event), ..old(self).view() }),
                Err(_) => !enabled(old(self).view().state, event)
                    && final(self).view() == old(self).view(),
            },
    {
        proof { use_type_invariant(&*self); }
        let ghost before = self.view();
        proof {
            if enabled(before.state, event) {
                every_enabled_resize_event_preserves_durable_order(before.state, event);
            }
        }
        match event {
            Event::Fail | Event::Abort => { self.faulted = true; return Ok(()); },
            Event::CommitBecameDurable => {
                if self.phase < 4 { return Err(Error::WrongPhase); }
                self.commit_durable = true; return Ok(());
            },
            Event::HomesBecameDurable => {
                if self.phase < 6 || !self.commit_durable { return Err(Error::WrongPhase); }
                self.homes_durable = true; return Ok(());
            },
            Event::TailBecameDurable => {
                if self.phase < 9 || !self.homes_durable { return Err(Error::WrongPhase); }
                self.tail_durable = true; return Ok(());
            },
            _ => {},
        }
        if self.faulted { return Err(Error::Failed); }
        match event {
            Event::MetadataInitialized => { if self.phase != 0 { return Err(Error::WrongPhase); } self.phase = 1; },
            Event::SubmitLog => { if self.phase != 1 { return Err(Error::WrongPhase); } self.phase = 2; },
            Event::LogFlushSucceeded => { if self.phase != 2 { return Err(Error::WrongPhase); } self.phase = 3; },
            Event::SubmitCommit => { if self.phase != 3 { return Err(Error::WrongPhase); } self.phase = 4; },
            Event::CommitFlushSucceeded => {
                if self.phase != 4 { return Err(Error::WrongPhase); }
                self.commit_durable = true; self.phase = 5;
            },
            Event::SubmitHomes => { if self.phase != 5 { return Err(Error::WrongPhase); } self.phase = 6; },
            Event::HomeFlushSucceeded => {
                if self.phase != 6 { return Err(Error::WrongPhase); }
                self.homes_durable = true; self.phase = 7;
            },
            Event::SubmitTail => { if self.phase != 8 { return Err(Error::WrongPhase); } self.phase = 9; },
            Event::TailFlushSucceeded => {
                if self.phase != 9 { return Err(Error::WrongPhase); }
                self.tail_durable = true; self.phase = 10;
            },
            _ => { return Err(Error::WrongPhase); },
        }
        Ok(())
    }

    /// Publication is a short mutation of the version holder after homes are
    /// stable. The runtime must hold its exclusive geometry/cache publication
    /// lock; no I/O occurs here. Old bootstrap versions are rejected afterward.
    pub fn publish(&mut self, current: &mut VersionedGeometry) -> (r: Result<(), Error>)
        ensures final(self).wf(), final(current).wf(), match r {
            Ok(()) => old(self).view().state.phase == 7 && !old(self).view().state.faulted
                && old(self).view().state.homes_durable
                && old(current).view() == (GeometryVersion { geometry: old(self).view().before, epoch: old(self).view().before_epoch })
                && final(current).view() == (GeometryVersion { geometry: old(self).view().after, epoch: old(self).view().after_epoch })
                && final(self).view() == (PlanView { state: State { phase: 8, ..old(self).view().state }, ..old(self).view() }),
            Err(_) => final(self).view() == old(self).view() && final(current).view() == old(current).view(),
        },
    {
        proof { use_type_invariant(&*self); use_type_invariant(&*current); }
        if self.faulted { return Err(Error::Failed); }
        if self.phase != 7 || !self.homes_durable { return Err(Error::WrongPhase); }
        if current.epoch != self.before_epoch || !same_geometry(current.geometry, self.before) {
            return Err(Error::Stale);
        }
        current.geometry = self.after;
        current.epoch = self.after_epoch;
        self.phase = 8;
        Ok(())
    }
}

}
