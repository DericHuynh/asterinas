// SPDX-License-Identifier: MPL-2.0

//! Immutable, checked internal-journal mapping. This first concrete layout
//! admits a single initialized extent; fragmented journals fail closed.
//! Whole-volume ownership validation must still bind it to the reserved inode.

use vstd::prelude::*;
use crate::{bytes, extent, inode};

verus! {

pub struct JournalLayout { physical_start: u32, journal_blocks: u32, fs_blocks: u32 }
pub struct LayoutView { pub start: u32, pub journal_blocks: u32, pub fs_blocks: u32 }

pub open spec fn admitted(raw: Seq<u8>, inodes: u32, fs_blocks: u32, seed: u32) -> bool {
    &&& inode::accepted(raw, 8, inodes, fs_blocks, seed)
    &&& (bytes::le16(raw, 0) as u16 & 0xf000) == 0x8000
    &&& bytes::le32(raw, 4) % 4096 == 0
    &&& 1024 <= bytes::le32(raw, 4) / 4096 <= 32768
    &&& bytes::le16(raw, 42) == 1
    &&& bytes::le32(raw, 52) == 0
    &&& bytes::le16(raw, 56) <= 32768
    &&& extent::length(bytes::le16(raw, 56)) == bytes::le32(raw, 4) / 4096
    &&& bytes::le32(raw, 60) > 1
}

impl JournalLayout {
    pub closed spec fn view(&self) -> LayoutView {
        LayoutView { start: self.physical_start, journal_blocks: self.journal_blocks, fs_blocks: self.fs_blocks }
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.view().start > 1
        &&& 1024 <= self.view().journal_blocks <= 32768
        &&& self.view().start as int + self.view().journal_blocks <= self.view().fs_blocks
    }

    pub open spec fn allowed(&self, block: u32) -> bool {
        &&& self.wf()
        &&& block < self.view().fs_blocks
        &&& !(self.view().start <= block < self.view().start as int + self.view().journal_blocks)
    }

    pub fn blocks(&self) -> (r: u32) ensures r == self.view().journal_blocks { self.journal_blocks }
    pub fn physical_start(&self) -> (r: u32) ensures r == self.view().start { self.physical_start }
    pub fn filesystem_blocks(&self) -> (r: u32) ensures r == self.view().fs_blocks { self.fs_blocks }

    pub fn duplicate(&self) -> (r: Self) ensures r.view() == self.view() {
        JournalLayout { physical_start: self.physical_start, journal_blocks: self.journal_blocks, fs_blocks: self.fs_blocks }
    }

    pub fn valid(&self) -> (r: bool) ensures r == self.wf() {
        self.physical_start > 1 && self.journal_blocks >= 1024 && self.journal_blocks <= 32768
            && self.physical_start as u64 + self.journal_blocks as u64 <= self.fs_blocks as u64
    }

    pub fn allows_target(&self, block: u32) -> (r: bool) ensures r == self.allowed(block) {
        self.valid() && block < self.fs_blocks
            && !(self.physical_start <= block && (block as u64) < self.physical_start as u64 + self.journal_blocks as u64)
    }

    pub fn offset(&self, logical: u32, partition_bytes: u64) -> (r: Option<u64>)
        ensures match r {
            Some(o) => self.wf() && logical < self.view().journal_blocks
                && o as int == (self.view().start as int + logical) * 4096
                && o as int + 4096 <= partition_bytes,
            None => !self.wf() || logical >= self.view().journal_blocks
                || (self.view().start as int + logical + 1) * 4096 > partition_bytes,
        },
    {
        if !self.valid() || logical >= self.journal_blocks { return None; }
        bytes::block_offset(self.physical_start + logical, self.fs_blocks, partition_bytes)
    }
}

pub fn from_inode(raw: &[u8], inodes: u32, fs_blocks: u32, uuid_seed: u32) -> (r: Option<JournalLayout>)
    ensures match r {
        Some(layout) => admitted(raw@, inodes, fs_blocks, uuid_seed)
            && layout.wf() && layout.view().fs_blocks == fs_blocks
            && inode::accepted(raw@, 8, inodes, fs_blocks, uuid_seed)
            && layout.view().start as nat == bytes::le32(raw@, 60)
            && layout.view().journal_blocks as nat == bytes::le32(raw@, 4) / 4096,
        None => !admitted(raw@, inodes, fs_blocks, uuid_seed),
    },
{
    let ino = match inode::parse(raw, 8, inodes, fs_blocks, uuid_seed) {
        Some(ino) => ino, None => { return None; }
    };
    if ino.mode & 0xf000 != 0x8000 || ino.size % 4096 != 0 || ino.size / 4096 < 1024 || ino.size / 4096 > 32768
        || bytes::read_le16(raw, 42).unwrap() != 1 { return None; }
    let root = &raw[40..100];
    proof {
        assert(extent::leaf_entries(root@, 1, fs_blocks));
        assert(extent::accepted(root@, extent::entry_offset(0), fs_blocks));
    }
    let e = match extent::parse(root, 12, fs_blocks) { Some(e) => e, None => { return None; } };
    if !e.initialized || e.logical != 0 || e.length != ino.size / 4096 || e.physical <= 1 { return None; }
    Some(JournalLayout { physical_start: e.physical, journal_blocks: e.length, fs_blocks })
}

pub proof fn every_journal_block_is_excluded_from_replay(layout: &JournalLayout, logical: u32)
    requires layout.wf(), logical < layout.view().journal_blocks,
    ensures !layout.allowed((layout.view().start + logical) as u32),
{
}

}
