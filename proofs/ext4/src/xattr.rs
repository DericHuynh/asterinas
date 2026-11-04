// SPDX-License-Identifier: MPL-2.0

//! Linux inode-body and external-block xattr storage. The external checksum
//! binds the complete block to its exact 64-bit physical address. Parsed tables
//! expose immutable bytes or value-inode descriptors, not VFS permissions.

use vstd::prelude::*;
use crate::{block_size, bytes, crc, xattr_table::{self, Table, TableView}};

verus! {

pub const MAGIC: u32 = 0xea020000;
pub const MAX_REFS: u32 = 1024;

pub open spec fn inode_address(raw: Seq<u8>) -> nat {
    bytes::le32(raw, 104) + 4294967296 * bytes::le16(raw, 118)
}
pub open spec fn allocated_block_count(raw: Seq<u8>) -> nat { if inode_address(raw) > 0 { 1nat } else { 0nat } }

pub fn inode_pointer(raw: &[u8]) -> (r: Option<u64>)
    ensures match r { Some(address) => raw.len() >= 120 && address as nat == inode_address(raw@), None => raw.len() < 120 },
{
    if raw.len() < 120 { return None; }
    Some(bytes::read_le32(raw, 104).unwrap() as u64 + 4294967296 * bytes::read_le16(raw, 118).unwrap() as u64)
}

pub open spec fn encoded_address(block: u64) -> Seq<u8> {
    bytes::encoded_le((block % 4294967296) as u32) + bytes::encoded_le((block / 4294967296) as u32)
}

pub open spec fn block_checksum(raw: Seq<u8>, block: u64, seed: u32) -> u32 {
    crc::fold(crc::fold(seed, encoded_address(block)), crc::zero4(raw, 16))
}

pub fn checksum(raw: &[u8], block: u64, seed: u32) -> (r: Option<u32>)
    ensures match r { Some(value) => block_size::accepted(raw.len() as nat) && value == block_checksum(raw@, block, seed),
        None => !block_size::accepted(raw.len() as nat) },
{
    if !block_size::valid(raw.len()) { return None; }
    let low = bytes::encode_le32((block % 4294967296) as u32);
    let high = bytes::encode_le32((block / 4294967296) as u32);
    let address = [low[0], low[1], low[2], low[3], high[0], high[1], high[2], high[3]];
    assert(address@ =~= encoded_address(block));
    let seeded = crc::crc32c(seed, &address);
    crc::crc32c_zero4(seeded, raw, 16)
}

pub open spec fn header(raw: Seq<u8>, block: u64, seed: u32, checksummed: bool) -> bool {
    &&& block_size::accepted(raw.len()) && bytes::le32(raw, 0) == MAGIC
    &&& 1 <= bytes::le32(raw, 4) <= MAX_REFS && bytes::le32(raw, 8) == 1
    &&& bytes::le32(raw, 20) == 0 && bytes::le32(raw, 24) == 0 && bytes::le32(raw, 28) == 0
    &&& (checksummed ==> bytes::le32(raw, 16) == block_checksum(raw, block, seed) as nat)
}

pub struct Block<'a> { table: Table<'a>, physical: u64, seed: u32, checksummed: bool, references: u32 }
impl<'a> Block<'a> {
    pub closed spec fn view(&self) -> TableView { self.table.view() }
    pub closed spec fn address(&self) -> u64 { self.physical }
    pub closed spec fn seed(&self) -> u32 { self.seed }
    pub closed spec fn checksummed(&self) -> bool { self.checksummed }
    pub closed spec fn reference_count(&self) -> u32 { self.references }
    pub open spec fn wf(&self) -> bool {
        xattr_table::valid(self.view()) && self.view().first == 32 && self.view().base == 0 && self.view().sorted
            && header(self.view().raw, self.address(), self.seed(), self.checksummed())
            && self.reference_count() as nat == bytes::le32(self.view().raw, 4)
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn entries(&self) -> (r: &Table<'a>) ensures self.wf(), r.wf(), r.view() == self.view() {
        proof { use_type_invariant(self); } &self.table
    }
    pub fn refcount(&self) -> (r: u32) ensures self.wf(), 1 <= r <= MAX_REFS, r as nat == bytes::le32(self.view().raw, 4) {
        proof { use_type_invariant(self); } self.references
    }
    pub fn physical_block(&self) -> (r: u64) ensures self.wf(), r == self.address() {
        proof { use_type_invariant(self); } self.physical
    }
}

pub fn parse_block(raw: &[u8], block: u64, seed: u32, checksummed: bool, ea: bool, inodes: u32) -> (r: Option<Block<'_>>)
    ensures match r { Some(value) => value.wf() && value.view().raw == raw@ && value.address() == block && value.seed() == seed
        && value.checksummed() == checksummed && value.view().ea == ea && value.view().inodes == inodes, None => true },
{
    if !block_size::valid(raw.len()) { return None; }
    if bytes::read_le32(raw, 0).unwrap() != MAGIC || bytes::read_le32(raw, 8).unwrap() != 1
        || bytes::read_le32(raw, 20).unwrap() != 0 || bytes::read_le32(raw, 24).unwrap() != 0 || bytes::read_le32(raw, 28).unwrap() != 0 { return None; }
    let references = bytes::read_le32(raw, 4).unwrap();
    if references == 0 || references > MAX_REFS { return None; }
    if checksummed && bytes::read_le32(raw, 16).unwrap() != checksum(raw, block, seed).unwrap() { return None; }
    let table = match xattr_table::parse(raw, 32, 0, ea, inodes, true) { Some(table) => table, None => { return None; } };
    Some(Block { table, physical: block, seed, checksummed, references })
}

pub open spec fn body_header(raw: Seq<u8>) -> nat {
    if raw.len() == 128 || bytes::le16(raw, 128) == 0 { 128nat } else { 128 + bytes::le16(raw, 128) }
}

pub open spec fn body_geometry(raw: Seq<u8>) -> bool {
    &&& 128 <= raw.len() <= 65536
    &&& raw.len() == 128 || raw.len() >= 132
    &&& raw.len() == 128 || bytes::le16(raw, 128) == 0 || 4 <= bytes::le16(raw, 128) && body_header(raw) <= raw.len()
}

pub open spec fn body_present(raw: Seq<u8>) -> bool {
    raw.len() > 128 && bytes::le16(raw, 128) > 0 && body_header(raw) + 4 <= raw.len()
        && bytes::le32(raw, body_header(raw) as int) != 0
}

pub struct BodyView { pub raw: Seq<u8>, pub table: Option<TableView>, pub ea: bool, pub inodes: u32 }

pub open spec fn valid_body(v: BodyView) -> bool {
    &&& body_geometry(v.raw)
    &&& if body_present(v.raw) {
        bytes::le32(v.raw, body_header(v.raw) as int) == MAGIC && match v.table {
            Some(table) => xattr_table::valid(table) && table.raw == v.raw && table.ea == v.ea && table.inodes == v.inodes
                && table.first == body_header(v.raw) + 4 && table.base == table.first && !table.sorted,
            None => false,
        }
    } else { v.table is None }
}

pub struct Body<'a> { raw: &'a [u8], table: Option<Table<'a>>, ea: bool, inodes: u32 }
impl<'a> Body<'a> {
    pub closed spec fn view(&self) -> BodyView { BodyView { raw: self.raw@, ea: self.ea, inodes: self.inodes,
        table: match &self.table { Some(table) => Some(table.view()), None => None } } }
    pub open spec fn wf(&self) -> bool { valid_body(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn parameters(&self) -> (r: (bool, u32)) ensures self.wf(), r == (self.view().ea, self.view().inodes) {
        proof { use_type_invariant(self); } (self.ea, self.inodes)
    }
    pub fn entry_table(&self) -> (r: Option<&Table<'a>>)
        ensures self.wf(), match r { Some(table) => table.wf() && self.view().table == Some(table.view()), None => self.view().table is None },
    { proof { use_type_invariant(self); } self.table.as_ref() }
    pub fn present(&self) -> (r: bool) ensures self.wf(), r == body_present(self.view().raw) {
        proof { use_type_invariant(self); }
        match &self.table { Some(_) => true, None => false }
    }
}

pub fn parse_body(raw: &[u8], ea: bool, inodes: u32) -> (r: Option<Body<'_>>)
    ensures match r { Some(value) => value.wf() && value.view().raw == raw@ && value.view().ea == ea && value.view().inodes == inodes, None => true },
{
    if raw.len() < 128 || raw.len() > 65536 || (raw.len() != 128 && raw.len() < 132) { return None; }
    if raw.len() == 128 { return Some(Body { raw, table: None, ea, inodes }); }
    let extra = bytes::read_le16(raw, 128).unwrap() as usize;
    if extra == 0 { return Some(Body { raw, table: None, ea, inodes }); }
    if extra < 4 || extra > raw.len() - 128 { return None; }
    let offset = 128 + extra;
    if raw.len() - offset < 4 || bytes::read_le32(raw, offset).unwrap() == 0 {
        return Some(Body { raw, table: None, ea, inodes });
    }
    if bytes::read_le32(raw, offset).unwrap() != MAGIC { return None; }
    let table = match xattr_table::parse(raw, offset + 4, offset + 4, ea, inodes, false) { Some(table) => table, None => { return None; } };
    Some(Body { raw, table: Some(table), ea, inodes })
}

pub proof fn block_checksums_cover_all_bytes_except_the_checksum_word(raw: Seq<u8>, other: Seq<u8>, block: u64, seed: u32)
    requires raw.len() == other.len(), raw.len() >= 20,
        forall|i: int| 0 <= i < raw.len() && !(16 <= i < 20) ==> #[trigger] other[i] == raw[i],
    ensures block_checksum(raw, block, seed) == block_checksum(other, block, seed),
{
    assert(crc::zero4(raw, 16) =~= crc::zero4(other, 16));
}

}
