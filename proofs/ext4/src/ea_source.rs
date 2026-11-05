// SPDX-License-Identifier: MPL-2.0

//! Isolated EA_INODE read geometry and allocated inode-table provenance.
//! This profile inspects the original snapshot and does not confer ordinary
//! filesystem admission, namespace, reference-count, allocation or I/O authority.

use vstd::prelude::*;
use crate::{bitmap, block_claims, bytes, crc, feature_policy, group, group_fields,
    snapshot::Snapshot, superblock};

verus! {

pub const EA_INODE: u32 = 0x400;

pub open spec fn header_accepted(s: Seq<u8>, partition_bytes: u64) -> bool {
    &&& s.len() == 1024
    &&& bytes::le16(s, 56) == 0xef53 && bytes::le16(s, 58) == 1
    &&& bytes::le32(s, 20) == 0 && bytes::le32(s, 24) == 2 && bytes::le32(s, 28) == 2
    &&& bytes::le32(s, 32) == 32768 && bytes::le32(s, 36) == 32768
    &&& bytes::le32(s, 72) == 0 && bytes::le32(s, 76) == 1 && bytes::le32(s, 84) == 11
    &&& bytes::le16(s, 88) == 256
    &&& feature_policy::compat_allowed(bytes::le32(s, 92) as u32)
    &&& bytes::le32(s, 96) as u32 & EA_INODE != 0
    &&& bytes::le32(s, 96) as u32 & 4u32 == 0
    &&& feature_policy::incompat_allowed(bytes::le32(s, 96) as u32 & !EA_INODE)
    &&& feature_policy::ro_allowed(bytes::le32(s, 100) as u32)
    &&& (if superblock::descriptor_bytes(s) == 64 { bytes::le16(s, 254) == 64 }
        else { bytes::le16(s, 254) == 0 || bytes::le16(s, 254) == 32 })
    &&& bytes::le16(s, 206) == 0 && bytes::le32(s, 228) == 0 && bytes::le32(s, 232) == 0
    &&& bytes::le16(s, 348) == 32 && bytes::le16(s, 350) == 32 && s[373] == 1
    &&& bytes::le32(s, 336) == 0 && bytes::le32(s, 340) == 0 && bytes::le32(s, 344) == 0
    &&& 2 < bytes::le32(s, 4) <= block_claims::MAX_BLOCKS
    &&& bytes::le32(s, 4) * 4096 <= partition_bytes
    &&& bytes::le32(s, 8) <= bytes::le32(s, 4) && bytes::le32(s, 12) <= bytes::le32(s, 4)
    &&& bytes::le32(s, 16) <= bytes::le32(s, 0)
    &&& 0 < bytes::le32(s, 40) <= 32768 && bytes::le32(s, 40) % 16 == 0
    &&& bytes::le32(s, 0) == ((bytes::le32(s, 4) + 32767) / 32768) * bytes::le32(s, 40)
    &&& bytes::le32(s, 224) == 8 && bytes::le32(s, 0) >= 11
    &&& bytes::le32(s, 1020) == crc::fold(0xffffffff, s.subrange(0, 1020)) as nat
}

pub struct HeaderView {
    pub source: Seq<u8>, pub blocks: u32, pub inodes: u32, pub ipg: u32, pub groups: u32,
    pub seed: u32, pub width: usize, pub flex: bool,
}
#[verifier::opaque]
pub open spec fn header_valid(v: HeaderView) -> bool {
    let s = v.source.subrange(1024, 2048);
    &&& 8192 <= v.source.len() <= 18446744073709551615
    &&& header_accepted(s, v.source.len() as u64)
    &&& v.blocks as nat == bytes::le32(s, 4) && v.inodes as nat == bytes::le32(s, 0)
    &&& v.ipg as nat == bytes::le32(s, 40)
    &&& v.groups as nat == (v.blocks as nat + 32767) / 32768 && 0 < v.groups <= 32
    &&& v.seed == superblock::metadata_seed(s) && v.width as nat == superblock::descriptor_bytes(s)
    &&& v.flex == superblock::flex_bg(s)
}

pub struct Header<'s, 'a> {
    source: &'s Snapshot<'a>, blocks: u32, inodes: u32, ipg: u32, groups: u32,
    seed: u32, width: usize, flex: bool, checked: Ghost<HeaderView>,
}
impl<'s, 'a> Header<'s, 'a> {
    pub closed spec fn view(&self) -> HeaderView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        header_valid(self.view()) && self.view().source == self.source.view()
            && self.blocks == self.view().blocks && self.inodes == self.view().inodes
            && self.ipg == self.view().ipg && self.groups == self.view().groups
            && self.seed == self.view().seed && self.width == self.view().width && self.flex == self.view().flex
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn source(&self) -> (r: &'s Snapshot<'a>) ensures self.wf(), header_valid(self.view()), r.view() == self.view().source {
        proof { use_type_invariant(self); } self.source
    }
    pub fn parameters(&self) -> (r: (u32, u32, u32, u32))
        ensures self.wf(), header_valid(self.view()), r == (self.view().blocks, self.view().inodes, self.view().ipg, self.view().seed),
    { proof { use_type_invariant(self); } (self.blocks, self.inodes, self.ipg, self.seed) }
    pub fn descriptor_width(&self) -> (r: usize) ensures self.wf(), header_valid(self.view()), r == self.view().width, r == 32 || r == 64 {
        proof { use_type_invariant(self); reveal(header_valid); }
        self.width
    }
    pub fn huge_files(&self) -> (r: bool)
        ensures self.wf(), header_valid(self.view()), r == (bytes::le32(self.view().source, 1124) as u32 & 8u32 != 0),
    {
        proof { use_type_invariant(self); reveal(header_valid); }
        let primary = self.source.block(0).unwrap();
        bytes::read_le32(primary.as_slice(), 1124).unwrap() & 8u32 != 0
    }
    pub fn feature_flags(&self) -> (r: (u32, u32, u32))
        ensures self.wf(), header_valid(self.view()),
            r == (bytes::le32(self.view().source, 1116) as u32,
                bytes::le32(self.view().source, 1124) as u32, bytes::le32(self.view().source, 1120) as u32),
    {
        proof { use_type_invariant(self); reveal(header_valid); }
        let primary = self.source.block(0).unwrap(); let raw = primary.as_slice();
        (bytes::read_le32(raw, 1116).unwrap(), bytes::read_le32(raw, 1124).unwrap(), bytes::read_le32(raw, 1120).unwrap())
    }
    pub fn get(&self, number: u32) -> (r: Option<Node<'a>>)
        ensures self.wf(), header_valid(self.view()), match r { Some(node) => node.wf() && node_valid(node.view()) && node.view().header == self.view()
            && node.view().number == number, None => true },
    {
        proof { use_type_invariant(self); reveal(header_valid); }
        if number == 0 || number > self.inodes { return None; }
        let group_number = (number - 1) / self.ipg;
        let slot = (number - 1) % self.ipg;
        // Guards make descriptor and table reads total independently of a
        // complete-filesystem admission theorem.
        if group_number >= self.groups || group_number >= 32 || slot >= self.ipg { return None; }
        let width = self.descriptor_width();
        assert(width == self.width && (width == 32 || width == 64));
        let gdt = match self.source.block(1) { Some(block) => block, None => { return None; } };
        let descriptor = match gdt.range(group_number as usize * width, width) {
            Some(raw) => raw, None => { return None; }
        };
        assert(descriptor@ == self.view().source.subrange(4096 + group_number as int * width,
            4096 + (group_number as int + 1) * width)) by {
            if width == 32 {} else { assert(width == 64); }
        }
        let group = match group::parse_with_features(descriptor, group_number, self.blocks, self.ipg, self.seed, self.flex) {
            Some(group) => group, None => { return None; }
        };
        assert(group::accepted_with_features(descriptor@, group_number, self.blocks, self.ipg, self.seed, self.flex));
        assert(bytes::le32(descriptor@, 4) == group.inode_bitmap && bytes::le32(descriptor@, 8) == group.inode_table);
        if bytes::read_le16(descriptor, 18).unwrap() & 1 != 0 { return None; }
        assert(!group::inode_uninitialized(descriptor@));
        let unused = bytes::read_le16(descriptor, 28).unwrap() as u32;
        if unused > self.ipg || slot >= self.ipg - unused { return None; }
        assert(slot as nat + bytes::le16(descriptor@, 28) < self.ipg);
        let inode_bitmap = match self.source.block(group.inode_bitmap) { Some(block) => block, None => { return None; } };
        let bitmap_bytes = inode_bitmap.as_slice();
        assert(bitmap_bytes@ == self.view().source.subrange(bytes::le32(descriptor@, 4) as int * 4096,
            (bytes::le32(descriptor@, 4) as int + 1) * 4096));
        let free = bytes::read_le16(descriptor, 14).unwrap() as u32;
        let checksum = bytes::read_le16(descriptor, 26).unwrap();
        let checked_bitmap = match bitmap::parse(bitmap_bytes, self.ipg, self.ipg, free, checksum, self.seed) {
            Some(bitmap) => bitmap, None => { return None; }
        };
        assert(bitmap::accepted(bitmap_bytes@, self.ipg, self.ipg, free, checksum, self.seed));
        if self.width == 64 {
            let whole = group_fields::read_counter(descriptor, 26, 58, true).unwrap();
            if crc::crc32c(self.seed, &bitmap_bytes[..(self.ipg / 8) as usize]) != whole { return None; }
            assert(crc::fold(self.seed, bitmap_bytes@.take(self.ipg as int / 8))
                == group_fields::counter(descriptor@, 26, 58, true));
        }
        if !checked_bitmap.is_set(slot).unwrap() { return None; }
        assert(bitmap::set(bitmap_bytes@, slot as int));
        // An allocated inode cannot use bytes from an uninitialized group's
        // stale physical inode table, even if they happen to carry a CRC.
        let table_block = group.inode_table + slot / 16;
        if table_block >= self.blocks { return None; }
        let table = match self.source.block(table_block) { Some(block) => block, None => { return None; } };
        let offset = (slot % 16) as usize * 256;
        let raw = match table.range(offset, 256) { Some(raw) => raw, None => { return None; } };
        let position = table_block as u64 * 4096 + offset as u64;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(slot as int, 16);
            assert(position as nat == group.inode_table as nat * 4096 + slot as nat * 256);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(position as int, 4096,
                table_block as int, offset as int);
            assert(position % 4096 <= 3840);
        }
        assert(position as nat + 256 <= self.blocks as nat * 4096 <= self.view().source.len());
        assert(raw.len() == 256 && raw@ == self.view().source.subrange(position as int, position as int + 256));
        let ghost view = NodeView { header: self.view(), number, group: group_number, slot, position,
            descriptor: descriptor@, bitmap: bitmap_bytes@, raw: raw@ };
        assert(header_valid(view.header) && 0 < view.number <= view.header.inodes);
        assert(view.group as int == (view.number as int - 1) / view.header.ipg as int
            && view.slot as int == (view.number as int - 1) % view.header.ipg as int);
        assert(node_valid(view)) by { reveal(node_valid); }
        Some(Node { raw, number, position, blocks: self.blocks, inodes: self.inodes,
            ipg: self.ipg, seed: self.seed, checked: Ghost(view) })
    }
}

pub struct NodeView {
    pub header: HeaderView, pub number: u32, pub group: u32, pub slot: u32, pub position: u64,
    pub descriptor: Seq<u8>, pub bitmap: Seq<u8>, pub raw: Seq<u8>,
}
#[verifier::opaque]
pub open spec fn node_valid(v: NodeView) -> bool {
    &&& header_valid(v.header) && 0 < v.number <= v.header.inodes
    &&& v.group as int == (v.number as int - 1) / v.header.ipg as int && v.slot as int == (v.number as int - 1) % v.header.ipg as int
    &&& v.group < v.header.groups && v.group < 32 && v.slot < v.header.ipg
    &&& v.descriptor == v.header.source.subrange(4096 + v.group as int * v.header.width,
        4096 + (v.group as int + 1) * v.header.width)
    &&& group::accepted_with_features(v.descriptor, v.group, v.header.blocks, v.header.ipg, v.header.seed, v.header.flex)
    &&& !group::inode_uninitialized(v.descriptor)
    &&& v.slot as nat + bytes::le16(v.descriptor, 28) < v.header.ipg
    &&& v.bitmap == v.header.source.subrange(bytes::le32(v.descriptor, 4) as int * 4096,
        (bytes::le32(v.descriptor, 4) as int + 1) * 4096)
    &&& bitmap::accepted(v.bitmap, v.header.ipg, v.header.ipg, bytes::le16(v.descriptor, 14) as u32,
        bytes::le16(v.descriptor, 26) as u16, v.header.seed)
    &&& (v.header.width == 64 ==> crc::fold(v.header.seed, v.bitmap.take(v.header.ipg as int / 8))
        == group_fields::counter(v.descriptor, 26, 58, true))
    &&& bitmap::set(v.bitmap, v.slot as int)
    &&& v.position as nat == bytes::le32(v.descriptor, 8) * 4096 + v.slot as nat * 256
    &&& v.position as nat + 256 <= v.header.blocks as nat * 4096 <= v.header.source.len()
    &&& v.position % 4096 <= 3840
    &&& v.raw.len() == 256 && v.raw == v.header.source.subrange(v.position as int, v.position as int + 256)
}
pub struct Node<'a> { raw: &'a [u8], number: u32, position: u64,
    blocks: u32, inodes: u32, ipg: u32, seed: u32, checked: Ghost<NodeView> }
impl<'a> Node<'a> {
    pub closed spec fn view(&self) -> NodeView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        node_valid(self.view()) && self.raw@ == self.view().raw && self.number == self.view().number && self.position == self.view().position
            && self.blocks == self.view().header.blocks && self.inodes == self.view().header.inodes
            && self.ipg == self.view().header.ipg && self.seed == self.view().header.seed
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn raw(&self) -> (r: &'a [u8]) ensures self.wf(), node_valid(self.view()), r@ == self.view().raw, r.len() == 256 {
        proof { use_type_invariant(self); reveal(node_valid); } self.raw
    }
    pub fn number(&self) -> (r: u32) ensures self.wf(), node_valid(self.view()), r == self.view().number {
        proof { use_type_invariant(self); } self.number
    }
    pub fn position(&self) -> (r: u64) ensures self.wf(), node_valid(self.view()), r == self.view().position {
        proof { use_type_invariant(self); } self.position
    }
    pub fn inode_parameters(&self) -> (r: (u32, u32, u32, u32))
        ensures self.wf(), node_valid(self.view()), r == (self.view().header.blocks, self.view().header.inodes, self.view().header.ipg, self.view().header.seed),
    {
        proof { use_type_invariant(self); }
        (self.blocks, self.inodes, self.ipg, self.seed)
    }
}

pub fn parse<'s, 'a>(source: &'s Snapshot<'a>) -> (r: Option<Header<'s, 'a>>)
    ensures match r { Some(header) => header.wf() && header_valid(header.view()) && header.view().source == source.view(), None => true },
{
    if source.partition_bytes() < 8192 { return None; }
    let primary = match source.block(0) { Some(block) => block, None => { return None; } };
    let s = primary.range(1024, 1024).unwrap();
    if bytes::read_le16(s, 56).unwrap() != 0xef53 || bytes::read_le16(s, 58).unwrap() != 1
        || bytes::read_le32(s, 20).unwrap() != 0 || bytes::read_le32(s, 24).unwrap() != 2
        || bytes::read_le32(s, 28).unwrap() != 2 || bytes::read_le32(s, 32).unwrap() != 32768
        || bytes::read_le32(s, 36).unwrap() != 32768 || bytes::read_le32(s, 72).unwrap() != 0
        || bytes::read_le32(s, 76).unwrap() != 1 || bytes::read_le32(s, 84).unwrap() != 11
        || bytes::read_le16(s, 88).unwrap() != 256 || !feature_policy::compatible_flags(bytes::read_le32(s, 92).unwrap())
    { return None; }
    let incompat = bytes::read_le32(s, 96).unwrap();
    let width = superblock::descriptor_length(s).unwrap();
    let descriptor_size = bytes::read_le16(s, 254).unwrap();
    if incompat & EA_INODE == 0 || incompat & 4u32 != 0 || !feature_policy::incompatible_flags(incompat & !EA_INODE)
        || !feature_policy::readonly_compatible_flags(bytes::read_le32(s, 100).unwrap())
        || (if width == 64 { descriptor_size != 64 } else { descriptor_size != 0 && descriptor_size != 32 })
        || bytes::read_le16(s, 206).unwrap() != 0 || bytes::read_le32(s, 228).unwrap() != 0
        || bytes::read_le32(s, 232).unwrap() != 0 || bytes::read_le16(s, 348).unwrap() != 32
        || bytes::read_le16(s, 350).unwrap() != 32 || s[373] != 1
        || bytes::read_le32(s, 336).unwrap() != 0 || bytes::read_le32(s, 340).unwrap() != 0
        || bytes::read_le32(s, 344).unwrap() != 0
    { return None; }
    let blocks = bytes::read_le32(s, 4).unwrap(); let inodes = bytes::read_le32(s, 0).unwrap();
    let ipg = bytes::read_le32(s, 40).unwrap();
    let groups = ((blocks as u64 + 32767) / 32768) as u32;
    if blocks <= 2 || blocks > block_claims::MAX_BLOCKS || blocks as u64 * 4096 > source.partition_bytes()
        || bytes::read_le32(s, 8).unwrap() > blocks || bytes::read_le32(s, 12).unwrap() > blocks
        || bytes::read_le32(s, 16).unwrap() > inodes || ipg == 0 || ipg > 32768 || ipg % 16 != 0
        || groups == 0 || groups > 32
        || bytes::read_le32(s, 224).unwrap() != 8 || inodes < 11
    { return None; }
    assert(groups as int * ipg as int <= 1048576) by (nonlinear_arith)
        requires groups <= 32, ipg <= 32768;
    if inodes as u64 != groups as u64 * ipg as u64 { return None; }
    let checksum = crc::crc32c(0xffffffff, &s[..1020]);
    if bytes::read_le32(s, 1020).unwrap() != checksum { return None; }
    let seed = superblock::metadata_checksum_seed(s).unwrap();
    let flex = superblock::flex_enabled(s).unwrap();
    let ghost view = HeaderView { source: source.view(), blocks, inodes, ipg, groups, seed, width, flex };
    assert(header_valid(view)) by { reveal(header_valid); }
    Some(Header { source, blocks, inodes, ipg, groups, seed, width, flex, checked: Ghost(view) })
}

pub proof fn allocated_inode_reads_retain_the_exact_source_and_table_slot(v: NodeView)
    requires node_valid(v),
    ensures v.raw == v.header.source.subrange(v.position as int, v.position as int + 256),
        v.raw.len() == 256, bitmap::set(v.bitmap, v.slot as int),
        !group::inode_uninitialized(v.descriptor), v.slot as nat + bytes::le16(v.descriptor, 28) < v.header.ipg,
{ reveal(node_valid); }

pub proof fn ea_headers_from_the_same_source_have_identical_geometry(a: HeaderView, b: HeaderView)
    requires header_valid(a), header_valid(b), a.source == b.source,
    ensures a == b,
{ reveal(header_valid); }

pub proof fn ea_read_headers_do_not_satisfy_ordinary_feature_admission(v: HeaderView)
    requires header_valid(v),
    ensures !feature_policy::incompat_allowed(bytes::le32(v.source, 1120) as u32),
{
    reveal(header_valid);
    let flags = bytes::le32(v.source, 1120) as u32;
    assert(flags & EA_INODE != 0);
    assert(flags & EA_INODE != 0 ==> !feature_policy::incompat_allowed(flags)) by (bit_vector);
}

}
