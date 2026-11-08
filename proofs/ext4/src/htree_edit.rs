// SPDX-License-Identifier: MPL-2.0

//! Complete bounded linear/HTree directory reconstruction and namespace-edge
//! edit plans. Physical pools are checked for shape and aliases, but are not
//! allocation capabilities. Whole-source entry completeness, ownership,
//! child-directory emptiness, journal credits and atomic publication remain
//! requirements of the caller's later admission layer.

use vstd::prelude::*;
use crate::{block_size, bytes, crc, dir_hash, inode, inode_blocks, inode_time, superblock};

verus! {

pub const MAX_ENTRIES: usize = 65536;
pub const MAX_BLOCKS: usize = 65536;
pub const MAX_LOGICAL: u32 = 0x0fffffff;
pub const MAX_PHYSICAL: u64 = 0x0000ffffffffffff;
pub const INDEX_FLAG: u32 = 0x1000;
pub const EXTENTS_FLAG: u32 = 0x80000;
pub const HUGE_FLAG: u32 = 0x40000;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Error {
    Geometry, Feature, Checksum, Inode, Name, Target, Duplicate, Missing,
    Exists, Type, Identity, Budget, Pool, Alias, Depth, Mapping, Links, Time, Version, Accounting,
}
#[derive(Clone, Copy)]
pub struct Budget { pub entries: usize, pub blocks: usize }
#[derive(Clone, Copy)]
pub struct ReservedRange { pub first: u64, pub count: u64 }
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum BlockKind { Linear, Root, Internal(u8), Leaf }
#[derive(Clone, Copy)]
pub struct Mapping { pub logical: u32, pub physical: u64 }
#[derive(Clone, Copy)]
pub struct LinkDelta { pub inode: u32, pub generation: u32, pub file_type: u8, pub delta: i8 }

pub struct EntryView { pub name: Seq<u8>, pub inode: u32, pub generation: u32, pub file_type: u8 }
pub open spec fn name_valid(name: Seq<u8>) -> bool {
    0 < name.len() <= 255 && name != seq![46u8] && name != seq![46u8, 46u8]
        && forall|i: int| 0 <= i < name.len() ==> name[i] != 0 && #[trigger] name[i] != 47
}
pub open spec fn entry_valid(v: EntryView) -> bool { name_valid(v.name) && v.inode > 0 && 1 <= v.file_type <= 7 }

pub struct Entry { name: Vec<u8>, inode: u32, generation: u32, file_type: u8 }
impl Entry {
    pub closed spec fn view(&self) -> EntryView {
        EntryView { name: self.name@, inode: self.inode, generation: self.generation, file_type: self.file_type }
    }
    pub open spec fn wf(&self) -> bool { entry_valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn entry_name(&self) -> (r: &[u8]) ensures r@ == self.view().name { &self.name }
    pub fn entry_target(&self) -> (r: (u32, u32, u8)) ensures r == (self.view().inode, self.view().generation, self.view().file_type) { (self.inode, self.generation, self.file_type) }
}
pub fn entry(name: &[u8], number: u32, generation: u32, file_type: u8) -> (r: Result<Entry, Error>)
    ensures match r { Ok(value) => value.wf()
        && value.view() == (EntryView { name: name@, inode: number, generation, file_type }), Err(_) => true },
{
    if !valid_name(name) { return Err(Error::Name); }
    if number == 0 || file_type == 0 || file_type > 7 { return Err(Error::Target); }
    Ok(Entry { name: copy(name), inode: number, generation, file_type })
}
fn valid_name(name: &[u8]) -> (r: bool) ensures r == name_valid(name@) {
    if name.len() == 0 || name.len() > 255 { return false; }
    let dot = [46u8]; let dotdot = [46u8, 46u8];
    proof {
        assert(dot@ =~= seq![46u8]);
        assert(dotdot@ =~= seq![46u8, 46u8]);
    }
    if bytes::equal(name, dot.as_slice()) || bytes::equal(name, dotdot.as_slice()) { return false; }
    let mut i = 0usize;
    while i < name.len()
        invariant i <= name.len(), 0 < name.len() <= 255,
            name@ != seq![46u8], name@ != seq![46u8, 46u8],
            forall|j: int| 0 <= j < i ==> name@[j] != 0 && #[trigger] name@[j] != 47,
        decreases name.len() - i,
    {
        if name[i] == 0 || name[i] == 47 { return false; }
        i += 1;
    }
    true
}
fn copy(raw: &[u8]) -> (r: Vec<u8>) ensures r@ == raw@ {
    let mut out = Vec::new(); let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len(), out.len() == i, out@ == raw@.take(i as int),
        decreases raw.len() - i,
    { out.push(raw[i]); i += 1; }
    out
}
fn clone_entry(value: &Entry) -> (r: Entry)
    ensures value.wf(), r.wf(), r.view() == value.view(),
{ proof { use_type_invariant(value); }
    Entry { name: copy(&value.name), inode: value.inode, generation: value.generation, file_type: value.file_type }
}
fn zeroes(length: usize) -> (r: Vec<u8>)
    ensures r.len() == length, forall|i: int| 0 <= i < length ==> #[trigger] r@[i] == 0,
{
    let mut out = Vec::new(); let mut i = 0usize;
    while i < length
        invariant i <= length, out.len() == i, forall|j: int| 0 <= j < i ==> #[trigger] out@[j] == 0,
        decreases length - i,
    { out.push(0); i += 1; }
    out
}
pub open spec fn encoded16(value: u16) -> Seq<u8> { seq![(value % 256) as u8, (value / 256) as u8] }
fn put16(raw: &mut Vec<u8>, offset: usize, value: u16) -> (r: bool)
    ensures final(raw).len() == old(raw).len(), r == (offset as int + 2 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, offset as int, encoded16(value)) } else { old(raw)@ },
        r ==> bytes::le16(final(raw)@, offset as int) == value,
{
    let word = bytes::encode_le16(value);
    proof {
        assert(value as int == word@[0] as int + 256 * word@[1] as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            value as int, 256, word@[1] as int, word@[0] as int);
        assert(word@[0] == (value % 256) as u8);
        assert(word@[1] == (value / 256) as u8);
        assert(word@ =~= encoded16(value));
    }
    bytes::write_bytes(raw.as_mut_slice(), offset, &word)
}
fn put32(raw: &mut Vec<u8>, offset: usize, value: u32) -> (r: bool)
    ensures final(raw).len() == old(raw).len(), r == (offset as int + 4 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, offset as int, bytes::encoded_le(value)) } else { old(raw)@ },
        r ==> bytes::le32(final(raw)@, offset as int) == value,
{
    bytes::write_le32(raw.as_mut_slice(), offset, value)
}
fn word64(raw: &[u8], low: usize, high: usize) -> (r: Option<u64>)
    ensures r.is_some() == (low as int + 4 <= raw.len() && high as int + 4 <= raw.len()),
{
    match (bytes::read_le32(raw, low), bytes::read_le32(raw, high)) {
        (Some(a), Some(b)) => Some((a as u64) | ((b as u64) << 32)), _ => None,
    }
}

pub struct ContextView {
    pub source_inode: Seq<u8>, pub number: u32, pub parent: u32, pub generation: u32, pub inodes: u32,
    pub fs_blocks: u64, pub block_bytes: usize, pub fs_seed: u32, pub inode_seed: u32,
    pub hash_seed: dir_hash::State, pub hash_version: u8, pub indexed: bool,
    pub metadata: bool, pub filetype: bool, pub large: bool, pub dir_nlink: bool, pub huge_file: bool,
    pub retained_sectors: u64, pub old_tree_blocks: u64,
}
pub struct Context {
    source_inode: Vec<u8>, number: u32, parent: u32, generation: u32, inodes: u32,
    fs_blocks: u64, block_bytes: usize, fs_seed: u32, inode_seed: u32,
    hash_seed: dir_hash::State, hash_version: u8, indexed: bool,
    metadata: bool, filetype: bool, large: bool, dir_nlink: bool, huge_file: bool,
    retained_sectors: u64, old_tree_blocks: u64,
}
impl Context {
    pub open spec fn wf(&self) -> bool {
        let v = self.view();
        v.source_inode.len() == 256 && block_size::accepted(v.block_bytes as nat)
            && 0 < v.number <= v.inodes && 0 < v.parent <= v.inodes
            && (v.number == 2 ==> v.parent == 2) && v.fs_blocks > 0
            && v.hash_version <= 5
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub closed spec fn view(&self) -> ContextView {
        ContextView { source_inode: self.source_inode@, number: self.number, parent: self.parent,
            generation: self.generation, inodes: self.inodes, fs_blocks: self.fs_blocks,
            block_bytes: self.block_bytes, fs_seed: self.fs_seed, inode_seed: self.inode_seed,
            hash_seed: self.hash_seed, hash_version: self.hash_version, indexed: self.indexed,
            metadata: self.metadata, filetype: self.filetype, large: self.large,
            dir_nlink: self.dir_nlink, huge_file: self.huge_file,
            retained_sectors: self.retained_sectors, old_tree_blocks: self.old_tree_blocks }
    }
    pub fn context_identity(&self) -> (r: (u32, u32, u32)) ensures r == (self.view().number, self.view().generation, self.view().parent) { (self.number, self.generation, self.parent) }
    pub fn context_format(&self) -> (r: (usize, bool, bool, bool)) ensures r == (self.view().block_bytes, self.view().indexed, self.view().metadata, self.view().filetype) {
        (self.block_bytes, self.indexed, self.metadata, self.filetype)
    }
    pub fn context_hash_version(&self) -> (r: u8) ensures r == self.view().hash_version { self.hash_version }
}

/// Source envelope for the current 256-byte inode implementation. The old
/// directory-data plus external-extent-node count must come from the source
/// ownership census; its residual preserves external xattr and EA charges.
pub fn context(primary: &[u8], raw_inode: &[u8], number: u32, parent: u32,
    indexed: bool, disk_hash_version: u8, old_tree_blocks: u64) -> (r: Result<Context, Error>)
    ensures match r { Ok(ctx) => ctx.wf(), Err(_) => true },
{
    if primary.len() != 1024 || bytes::read_le16(primary, 56) != Some(0xef53) { return Err(Error::Geometry); }
    let shift = bytes::read_le32(primary, 24).unwrap();
    if shift > 6 { return Err(Error::Geometry); }
    let block_bytes = 1024usize << shift;
    if !block_size::valid(block_bytes) { return Err(Error::Geometry); }
    let inodes = bytes::read_le32(primary, 0).unwrap();
    if number == 0 || number > inodes || parent == 0 || parent > inodes || (number == 2 && parent != 2) {
        return Err(Error::Inode);
    }
    let compat = bytes::read_le32(primary, 92).unwrap();
    let incompat = bytes::read_le32(primary, 96).unwrap();
    let ro = bytes::read_le32(primary, 100).unwrap();
    if incompat & 0x40 == 0 || (indexed && compat & 0x20 == 0) || disk_hash_version > 2 {
        return Err(Error::Feature);
    }
    let high = bytes::read_le32(primary, 336).unwrap();
    if incompat & 0x80 == 0 && high != 0 { return Err(Error::Geometry); }
    let fs_blocks = (bytes::read_le32(primary, 4).unwrap() as u64) | ((high as u64) << 32);
    if fs_blocks == 0 { return Err(Error::Geometry); }
    let metadata = ro & 0x400 != 0;
    if ro & (0x1000u32 | 0x200u32) != 0 || incompat & 4 != 0 || bytes::read_le32(primary, 72) != Some(0)
        || (incompat & 0x2000 != 0 && !metadata) || (metadata && primary[373] != 1) {
        return Err(Error::Feature);
    }
    if metadata && bytes::read_le32(primary, 1020) != Some(crc::crc32c(0xffffffff, &primary[..1020])) {
        return Err(Error::Checksum);
    }
    if raw_inode.len() != 256 || bytes::read_le16(raw_inode, 128) != Some(32)
        || bytes::read_le16(raw_inode, 0).unwrap() & 0xf000 != 0x4000
        || bytes::read_le16(raw_inode, 26) == Some(0) || bytes::read_le32(raw_inode, 20) != Some(0) {
        return Err(Error::Inode);
    }
    let flags = bytes::read_le32(raw_inode, 32).unwrap();
    if flags & (0x10u32 | 0x20u32 | 0x800u32 | 0x100000u32 | 0x10000000u32 | 0x40000000u32) != 0
        || (flags & INDEX_FLAG != 0 && compat & 0x20 == 0) {
        return Err(Error::Feature);
    }
    let fs_seed = superblock::metadata_checksum_seed(primary).unwrap();
    if metadata {
        let expected = inode::calculated_checksum(raw_inode, number, fs_seed).unwrap();
        let stored = bytes::read_le16(raw_inode, 124).unwrap() as u32
            | ((bytes::read_le16(raw_inode, 130).unwrap() as u32) << 16);
        if stored != expected { return Err(Error::Checksum); }
    }
    // BIGALLOC is rejected above: rebuilding must compose whole-cluster billing
    // before a mapped-block count may replace the old directory charge.
    let huge_file = ro & 0x8 != 0;
    let old_sectors = match inode_blocks::decode(raw_inode, block_bytes as u32, huge_file) {
        Some(value) => value, None => { return Err(Error::Accounting); }
    };
    let sectors_per_block = block_bytes as u64 / 512;
    proof { assert(1024 <= block_bytes <= 65536); assert(2 <= sectors_per_block <= 128); }
    if old_tree_blocks > u64::MAX / sectors_per_block { return Err(Error::Accounting); }
    let tree_sectors = old_tree_blocks * sectors_per_block;
    if tree_sectors > old_sectors { return Err(Error::Accounting); }
    let generation = bytes::read_le32(raw_inode, 100).unwrap();
    let flags2 = bytes::read_le32(primary, 352).unwrap();
    if flags2 & 3 == 3 { return Err(Error::Feature); }
    let hash_version = disk_hash_version + if flags2 & 2 != 0 { 3u8 } else { 0u8 };
    let hash_seed = dir_hash::State { a: bytes::read_le32(primary, 236).unwrap(), b: bytes::read_le32(primary, 240).unwrap(),
        c: bytes::read_le32(primary, 244).unwrap(), d: bytes::read_le32(primary, 248).unwrap() };
    Ok(Context { source_inode: copy(raw_inode), number, parent, generation, inodes,
        fs_blocks, block_bytes, fs_seed, inode_seed: inode::inode_seed(fs_seed, number, generation),
        hash_seed, hash_version, indexed, metadata, filetype: incompat & 2 != 0,
        large: incompat & 0x4000 != 0, dir_nlink: ro & 0x20 != 0, huge_file,
        retained_sectors: old_sectors - tree_sectors, old_tree_blocks })
}

fn lex_less(a: &[u8], b: &[u8]) -> bool {
    let length = if a.len() < b.len() { a.len() } else { b.len() };
    let mut i = 0usize;
    while i < length
        invariant i <= length, length <= a.len(), length <= b.len(),
        decreases length - i,
    {
        if a[i] < b[i] { return true; }
        if a[i] > b[i] { return false; }
        i += 1;
    }
    a.len() < b.len()
}
fn less(a: usize, b: usize, order: u8, entries: &[Entry], hashes: &[dir_hash::Hash]) -> bool
    requires a < entries.len(), b < entries.len(),
        order == 1 ==> a < hashes.len() && b < hashes.len(),
{
    if order == 2 {
        if entries[a].inode != entries[b].inode { return entries[a].inode < entries[b].inode; }
    } else if order == 1 {
        if hashes[a].major != hashes[b].major { return hashes[a].major < hashes[b].major; }
        if hashes[a].minor != hashes[b].minor { return hashes[a].minor < hashes[b].minor; }
    }
    lex_less(&entries[a].name, &entries[b].name)
}
fn sorted(entries: &[Entry], hashes: &[dir_hash::Hash], order: u8) -> (r: Vec<usize>)
    requires entries.len() <= MAX_ENTRIES, order == 1 ==> hashes.len() == entries.len(),
    ensures r.len() == entries.len(),
        forall|i: int| 0 <= i < r.len() ==> #[trigger] r@[i] < entries.len(),
{
    let length = entries.len(); let mut src: Vec<usize> = Vec::new(); let mut dst: Vec<usize> = Vec::new(); let mut i = 0usize;
    while i < length
        invariant length == entries.len(), i <= length <= MAX_ENTRIES, src.len() == i, dst.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] src@[j] < length,
            forall|j: int| 0 <= j < i ==> #[trigger] dst@[j] < length,
        decreases length - i,
    { src.push(i); dst.push(0usize); i += 1; }
    let mut width = 1usize;
    while width < length
        invariant length == entries.len(), 0 < width, src.len() == length, dst.len() == length, length <= MAX_ENTRIES,
            order == 1 ==> hashes.len() == entries.len(),
            forall|j: int| 0 <= j < length ==> #[trigger] src@[j] < length,
            forall|j: int| 0 <= j < length ==> #[trigger] dst@[j] < length,
        decreases length - width,
    {
        let mut left = 0usize;
        while left < length
            invariant length == entries.len(), left <= length, src.len() == length, dst.len() == length, 0 < width, length <= MAX_ENTRIES,
                order == 1 ==> hashes.len() == entries.len(),
                forall|j: int| 0 <= j < length ==> #[trigger] src@[j] < length,
                forall|j: int| 0 <= j < length ==> #[trigger] dst@[j] < length,
            decreases length - left,
        {
            let middle = left + if width < length - left { width } else { length - left };
            let right = middle + if width < length - middle { width } else { length - middle };
            let mut a = left; let mut b = middle; let mut out = left;
            while out < right
                invariant length == entries.len(), left <= a <= middle <= b <= right <= length <= MAX_ENTRIES, left <= out <= right,
                    out as int == a as int + b as int - middle as int,
                    src.len() == length, dst.len() == length,
                    order == 1 ==> hashes.len() == entries.len(),
                    forall|j: int| 0 <= j < length ==> #[trigger] src@[j] < length,
                    forall|j: int| 0 <= j < length ==> #[trigger] dst@[j] < length,
                decreases right - out,
            {
                if a < middle && (b == right || !less(src[b], src[a], order, entries, hashes)) {
                    dst.set(out, src[a]); a += 1;
                } else { dst.set(out, src[b]); b += 1; }
                out += 1;
            }
            left = right;
        }
        let old = src; src = dst; dst = old;
        width = if width > length / 2 { length } else { width * 2 };
    }
    src
}

pub struct ImageView { pub logical: u32, pub physical: u64, pub kind: BlockKind, pub raw: Seq<u8> }
pub struct Image { logical: u32, physical: u64, kind: BlockKind, raw: Vec<u8> }
impl Image {
    pub closed spec fn view(&self) -> ImageView {
        ImageView { logical: self.logical, physical: self.physical, kind: self.kind, raw: self.raw@ }
    }
    pub fn image_logical(&self) -> (r: u32) ensures r == self.view().logical { self.logical }
    pub fn image_physical(&self) -> (r: u64) ensures r == self.view().physical { self.physical }
    pub fn image_kind(&self) -> (r: BlockKind) ensures r == self.view().kind { self.kind }
    pub fn image_bytes(&self) -> (r: &[u8]) ensures r@ == self.view().raw { &self.raw }
}
/// Observational output only. This view describes emitted images/edges;
/// it does not assert allocation, journal or namespace admission authority.
pub struct PlanView {
    pub images: Seq<ImageView>, pub mappings: Seq<Mapping>, pub inode: Seq<u8>, pub extent_root: Seq<u8>,
    pub entries: Seq<EntryView>, pub deltas: Seq<LinkDelta>, pub indexed: bool, pub levels: u8,
    pub old_tree_blocks: u64, pub empty_victim: Option<(u32, u32)>,
}
pub struct Plan {
    images: Vec<Image>, mappings: Vec<Mapping>, inode_image: Vec<u8>, extent_root: Vec<u8>,
    entries: Vec<Entry>, deltas: Vec<LinkDelta>, indexed: bool, levels: u8,
    old_tree_blocks: u64, empty_victim_required: Option<(u32, u32)>,
}
impl Plan {
    pub closed spec fn view(&self) -> PlanView {
        PlanView { images: self.images@.map_values(|image: Image| image.view()), mappings: self.mappings@,
            inode: self.inode_image@, extent_root: self.extent_root@,
            entries: self.entries@.map_values(|entry: Entry| entry.view()), deltas: self.deltas@,
            indexed: self.indexed, levels: self.levels, old_tree_blocks: self.old_tree_blocks,
            empty_victim: self.empty_victim_required }
    }
    pub fn plan_len(&self) -> (r: usize) ensures r == self.view().images.len() { self.images.len() }
    pub fn plan_image(&self, ordinal: usize) -> (r: Option<&Image>)
        ensures match r {
            Some(image) => ordinal < self.view().images.len() && image.view() == self.view().images[ordinal as int],
            None => ordinal >= self.view().images.len(),
        },
    {
        if ordinal >= self.images.len() { None } else { Some(&self.images[ordinal]) }
    }
    pub fn plan_mapping(&self, ordinal: usize) -> (r: Option<Mapping>)
        ensures match r {
            Some(mapping) => ordinal < self.view().mappings.len() && mapping == self.view().mappings[ordinal as int],
            None => ordinal >= self.view().mappings.len(),
        },
    {
        if ordinal >= self.mappings.len() { None } else { Some(self.mappings[ordinal]) }
    }
    pub fn plan_inode(&self) -> (r: &[u8]) ensures r@ == self.view().inode { &self.inode_image }
    pub fn plan_root(&self) -> (r: &[u8]) ensures r@ == self.view().extent_root { &self.extent_root }
    pub fn plan_index(&self) -> (r: (bool, u8)) ensures r == (self.view().indexed, self.view().levels) { (self.indexed, self.levels) }
    pub fn plan_entry_count(&self) -> (r: usize) ensures r == self.view().entries.len() { self.entries.len() }
    pub fn plan_entry(&self, ordinal: usize) -> (r: Option<&Entry>)
        ensures match r {
            Some(entry) => ordinal < self.view().entries.len() && entry.view() == self.view().entries[ordinal as int],
            None => ordinal >= self.view().entries.len(),
        },
    {
        if ordinal >= self.entries.len() { None } else { Some(&self.entries[ordinal]) }
    }
    pub fn plan_delta_count(&self) -> (r: usize) ensures r == self.view().deltas.len() { self.deltas.len() }
    pub fn plan_delta(&self, ordinal: usize) -> (r: Option<LinkDelta>)
        ensures match r {
            Some(delta) => ordinal < self.view().deltas.len() && delta == self.view().deltas[ordinal as int],
            None => ordinal >= self.view().deltas.len(),
        },
    {
        if ordinal >= self.deltas.len() { None } else { Some(self.deltas[ordinal]) }
    }
    pub fn plan_retired_tree_blocks(&self) -> (r: u64) ensures r == self.view().old_tree_blocks { self.old_tree_blocks }
    pub fn plan_requires_empty_victim(&self) -> (r: Option<(u32, u32)>) ensures r == self.view().empty_victim { self.empty_victim_required }
}
pub enum Mutation { NoChange, Rebuild(Plan) }


fn minimal(name_length: usize) -> (r: usize)
    ensures r == if name_length > 255 { 0usize } else { ((8 + name_length + 3) / 4 * 4) as usize },
        name_length <= 255 ==> 8 + name_length <= r <= 264 && r % 4 == 0,
{ if name_length > 255 { 0 } else { (8 + name_length + 3) / 4 * 4 } }
fn put_reclen(raw: &mut Vec<u8>, at: usize, length: usize, block_bytes: usize) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r ==> 8 <= length <= block_bytes <= 65536 && length % 4 == 0
            && crate::htree::record_length(bytes::le16(final(raw)@, at as int) as u16, block_bytes as nat) == length,
{
    if length < 8 || length > block_bytes || length % 4 != 0 || block_bytes > 65536 { return false; }
    let word = if length == 65536 { 65535u16 } else { length as u16 };
    put16(raw, at, word)
}
fn write_record(raw: &mut Vec<u8>, at: usize, number: u32, kind: u8,
    name: &[u8], record_length: usize, filetype: bool, block_bytes: usize) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
{
    let ghost original_length = raw.len();
    if name.len() > 255 || kind > 7 { return false; }
    let needed = minimal(name.len());
    if record_length < needed || at > raw.len() || record_length > raw.len() - at { return false; }
    if !put32(raw, at, number) || !put_reclen(raw, at + 4, record_length, block_bytes) { return false; }
    raw.set(at + 6, name.len() as u8); raw.set(at + 7, if filetype { kind } else { 0 });
    let mut i = 0usize;
    while i < name.len()
        invariant raw.len() == original_length, i <= name.len(), name.len() <= 255, at <= raw.len(),
            at as int + record_length <= raw.len(), 8 + name.len() <= needed <= record_length,
        decreases name.len() - i,
    { raw.set(at + 8 + i, name[i]); i += 1; }
    true
}
fn seal_leaf(raw: &mut Vec<u8>, ctx: &Context, last: usize) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
{
    proof { use_type_invariant(ctx); }

    let usable = ctx.block_bytes - if ctx.metadata { 12usize } else { 0usize };
    if raw.len() != ctx.block_bytes || last >= usable || usable - last < 8 { return false; }
    if !put_reclen(raw, last + 4, usable - last, ctx.block_bytes) { return false; }
    if ctx.metadata {
        if !put32(raw, usable, 0) || !put16(raw, usable + 4, 12) { return false; }
        raw.set(usable + 6, 0); raw.set(usable + 7, 0xde);
        let checksum = crc::crc32c(ctx.inode_seed, &raw[..usable]);
        if !put32(raw, usable + 8, checksum) { return false; }
    }
    true
}
#[derive(Clone, Copy)]
struct Bound { logical: u32, first: u32, last: u32, boundary: u32 }

fn push_leaf(images: &mut Vec<Image>, bounds: &mut Vec<Bound>, mut raw: Vec<u8>,
    last: usize, first_hash: u32, last_hash: u32, ctx: &Context, budget: Budget) -> Result<(), Error>
{
    proof { use_type_invariant(ctx); }

    if images.len() >= budget.blocks || images.len() >= MAX_BLOCKS { return Err(Error::Budget); }
    if !seal_leaf(&mut raw, ctx, last) { return Err(Error::Geometry); }
    let logical = images.len() as u32;
    if ctx.indexed {
        let continuation = if bounds.len() != 0 && bounds[bounds.len() - 1].last == first_hash { 1u32 } else { 0u32 };
        let boundary = if bounds.len() == 0 { 0u32 } else { first_hash | continuation };
        bounds.push(Bound { logical, first: first_hash, last: last_hash, boundary });
    }
    images.push(Image { logical, physical: 0, kind: if ctx.indexed { BlockKind::Leaf } else { BlockKind::Linear }, raw });
    Ok(())
}
fn leaves(ctx: &Context, entries: &[Entry], hashes: &[dir_hash::Hash], order: &[usize], budget: Budget)
    -> Result<(Vec<Image>, Vec<Bound>), Error>
    requires order.len() <= MAX_ENTRIES, hashes.len() == entries.len(),
        forall|i: int| 0 <= i < order.len() ==> #[trigger] order@[i] < entries.len(),
{
    proof { use_type_invariant(ctx); }

    let mut images = Vec::new(); let mut bounds = Vec::new();
    if ctx.indexed {
        images.push(Image { logical: 0, physical: 0, kind: BlockKind::Root, raw: zeroes(ctx.block_bytes) });
    }
    let usable = ctx.block_bytes - if ctx.metadata { 12usize } else { 0usize };
    let mut raw = zeroes(ctx.block_bytes); let mut at = 0usize; let mut last = 0usize;
    let mut first_hash = 0u32; let mut last_hash = 0u32;
    if !ctx.indexed {
        if !write_record(&mut raw, 0, ctx.number, 2, b".", 12, ctx.filetype, ctx.block_bytes)
            || !write_record(&mut raw, 12, ctx.parent, 2, b"..", 12, ctx.filetype, ctx.block_bytes) {
            return Err(Error::Geometry);
        }
        at = 24; last = 12;
    }
    let mut i = 0usize;
    while i < order.len()
        invariant i <= order.len(), at <= usable, raw.len() == ctx.block_bytes,
            ctx.wf(), usable == ctx.block_bytes - if ctx.metadata { 12usize } else { 0usize },
            hashes.len() == entries.len(),
            forall|j: int| 0 <= j < order.len() ==> #[trigger] order@[j] < entries.len(),
        decreases order.len() - i,
    {
        let ordinal = order[i]; let value = &entries[ordinal];
        let length = minimal(value.name.len());
        if length > usable { return Err(Error::Name); }
        if length > usable - at {
            match push_leaf(&mut images, &mut bounds, raw, last, first_hash, last_hash, ctx, budget) {
                Ok(()) => {}, Err(error) => { return Err(error); },
            }
            raw = zeroes(ctx.block_bytes); at = 0; last = 0;
        }
        if at == 0 { first_hash = hashes[ordinal].major; }
        last_hash = hashes[ordinal].major;
        if !write_record(&mut raw, at, value.inode, value.file_type, &value.name, length, ctx.filetype, ctx.block_bytes) {
            return Err(Error::Geometry);
        }
        last = at; at += length; i += 1;
    }
    if at == 0 {
        if !write_record(&mut raw, 0, 0, 0, &[], usable, ctx.filetype, ctx.block_bytes) { return Err(Error::Geometry); }
        last = 0;
    }
    match push_leaf(&mut images, &mut bounds, raw, last, first_hash, last_hash, ctx, budget) {
        Ok(()) => Ok((images, bounds)), Err(error) => Err(error),
    }
}
fn index_capacity(ctx: &Context, root: bool) -> (r: usize)
    ensures 2 <= r <= 8192,
        r == (ctx.block_bytes - if root { 32usize } else { 8usize } - if ctx.metadata { 8usize } else { 0usize }) / 8,
        (r as int) * 8 <= ctx.block_bytes as int - (if root { 32int } else { 8int }) - (if ctx.metadata { 8int } else { 0int }),
{
    proof { use_type_invariant(ctx); }

    (ctx.block_bytes - if root { 32usize } else { 8usize } - if ctx.metadata { 8usize } else { 0usize }) / 8
}
fn index_block(ctx: &Context, children: &[Bound], start: usize, end: usize, root: bool, levels: u8)
    -> Result<Vec<u8>, Error>
{
    proof { use_type_invariant(ctx); }

    if start >= end || end > children.len() { return Err(Error::Geometry); }
    let first = if root { 32usize } else { 8usize };
    let limit = index_capacity(ctx, root);
    let count = end - start;
    if count > limit || limit > 65535 { return Err(Error::Depth); }
    let mut raw = zeroes(ctx.block_bytes);
    if root {
        if !write_record(&mut raw, 0, ctx.number, 2, b".", 12, ctx.filetype, ctx.block_bytes)
            || !write_record(&mut raw, 12, ctx.parent, 2, b"..", ctx.block_bytes - 12, ctx.filetype, ctx.block_bytes) {
            return Err(Error::Geometry);
        }
        if !put32(&mut raw, 24, 0) { return Err(Error::Geometry); }
        raw.set(28, if ctx.hash_version >= 3 { ctx.hash_version - 3 } else { ctx.hash_version });
        raw.set(29, 8); raw.set(30, levels); raw.set(31, 0);
    } else if !write_record(&mut raw, 0, 0, 0, &[], ctx.block_bytes, ctx.filetype, ctx.block_bytes) {
        return Err(Error::Geometry);
    }
    let mut i = 0usize;
    while i < count
        invariant i <= count <= limit <= 8192, first <= 32, start + count == end, end <= children.len(), raw.len() == ctx.block_bytes,
        decreases count - i,
    {
        let value = children[start + i];
        if value.logical == 0 || value.logical > MAX_LOGICAL { return Err(Error::Mapping); }
        if i != 0 && !put32(&mut raw, first + i * 8, value.boundary) { return Err(Error::Geometry); }
        if !put32(&mut raw, first + i * 8 + 4, value.logical) { return Err(Error::Geometry); }
        i += 1;
    }
    if !put16(&mut raw, first, limit as u16) || !put16(&mut raw, first + 2, count as u16) {
        return Err(Error::Geometry);
    }
    if ctx.metadata {
        let tail = first + limit * 8;
        if !put32(&mut raw, tail, 0) { return Err(Error::Geometry); }
        let a = crc::crc32c(ctx.inode_seed, &raw[..first + count * 8]);
        let b = crc::crc32c(a, &raw[tail..tail + 4]);
        let checksum = crc::crc32c(b, &[0u8, 0u8, 0u8, 0u8]);
        if !put32(&mut raw, tail + 4, checksum) { return Err(Error::Geometry); }
    }
    Ok(raw)
}
fn index_tree(ctx: &Context, images: &mut Vec<Image>, mut edges: Vec<Bound>, budget: Budget) -> Result<u8, Error> {
    proof { use_type_invariant(ctx); }

    if edges.len() == 0 || images.len() < 2 { return Err(Error::Geometry); }
    let root_limit = index_capacity(ctx, true);
    let node_limit = index_capacity(ctx, false);
    let mut levels = 0u8;
    while edges.len() > root_limit
        invariant root_limit > 0, node_limit > 1, levels <= 2, images.len() >= 2, ctx.wf(),
        decreases 3 - levels,
    {
        if levels >= if ctx.large { 2u8 } else { 1u8 } { return Err(Error::Depth); }
        let mut parents: Vec<Bound> = Vec::new();
        let mut start = 0usize;
        while start < edges.len()
            invariant start <= edges.len(), node_limit > 1, levels < 2, images.len() >= 2,
            decreases edges.len() - start,
        {
            if images.len() >= budget.blocks || images.len() >= MAX_BLOCKS { return Err(Error::Budget); }
            let end = start + if node_limit < edges.len() - start { node_limit } else { edges.len() - start };
            let raw = match index_block(ctx, &edges, start, end, false, 0) {
                Ok(value) => value, Err(error) => { return Err(error); }
            };
            let logical = images.len() as u32;
            parents.push(Bound { logical, first: edges[start].first, last: edges[end - 1].last, boundary: edges[start].boundary });
            images.push(Image { logical, physical: 0, kind: BlockKind::Internal(levels + 1), raw });
            start = end;
        }
        edges = parents; levels += 1;
    }
    let root = match index_block(ctx, &edges, 0, edges.len(), true, levels) {
        Ok(value) => value, Err(error) => { return Err(error); }
    };
    images.set(0, Image { logical: 0, physical: 0, kind: BlockKind::Root, raw: root });
    Ok(levels)
}
fn extent_root(pool: &[u64], count: usize) -> Result<Vec<u8>, Error> {
    if count == 0 || count > pool.len() || count > MAX_BLOCKS { return Err(Error::Mapping); }
    let mut raw = zeroes(60);
    if !put16(&mut raw, 0, 0xf30a) || !put16(&mut raw, 4, 4) || !put16(&mut raw, 6, 0) {
        return Err(Error::Geometry);
    }
    let mut logical = 0usize; let mut entries = 0usize;
    while logical < count
        invariant logical <= count <= MAX_BLOCKS, count <= pool.len(), entries <= 4,
        decreases count - logical,
    {
        if entries == 4 { return Err(Error::Mapping); }
        let start = logical; let physical = pool[start];
        if physical > MAX_PHYSICAL { return Err(Error::Mapping); }
        logical += 1;
        while logical < count && logical - start < 32768 && pool[logical] == physical + (logical - start) as u64
            invariant start < logical <= count <= MAX_BLOCKS, count <= pool.len(), logical - start <= 32768, physical <= MAX_PHYSICAL,
            decreases count - logical,
        { logical += 1; }
        let offset = 12 + entries * 12;
        if !put32(&mut raw, offset, start as u32) || !put16(&mut raw, offset + 4, (logical - start) as u16)
            || !put16(&mut raw, offset + 6, (physical >> 32) as u16)
            || !put32(&mut raw, offset + 8, (physical & 0xffffffff) as u32) {
            return Err(Error::Geometry);
        }
        entries += 1;
    }
    if !put16(&mut raw, 2, entries as u16) { return Err(Error::Geometry); }
    Ok(raw)
}
fn directory_size(block_bytes: usize, count: usize) -> (r: u64)
    requires block_size::accepted(block_bytes as nat), count <= MAX_BLOCKS,
    ensures r as nat == (count as nat) * (block_bytes as nat), r <= 4294967296,
{
    proof {
        assert(1024 <= block_bytes <= 65536);
        assert((count as int) * (block_bytes as int) <= 4294967296) by (nonlinear_arith)
            requires count <= 65536, block_bytes <= 65536;
    }
    count as u64 * block_bytes as u64
}
fn billed_sectors(block_bytes: usize, count: usize) -> (r: u64)
    requires block_size::accepted(block_bytes as nat), count <= MAX_BLOCKS,
    ensures r as nat == (count as nat) * ((block_bytes as nat) / 512), r <= 8388608,
{
    let per_block = block_bytes as u64 / 512;
    proof {
        assert(1024 <= block_bytes <= 65536);
        assert(2 <= per_block <= 128);
        assert((count as int) * (per_block as int) <= 8388608) by (nonlinear_arith)
            requires count <= 65536, per_block <= 128;
    }
    count as u64 * per_block
}
fn seal_inode(ctx: &Context, root: &[u8], count: usize, subdirectories: usize,
    seconds: i64, nanoseconds: u32) -> Result<Vec<u8>, Error>
    requires count <= MAX_BLOCKS, subdirectories <= MAX_ENTRIES,
{
    hide(bytes::splice);
    proof { use_type_invariant(ctx); }

    if root.len() != 60 || ctx.source_inode.len() != 256 { return Err(Error::Inode); }
    let size = directory_size(ctx.block_bytes, count);
    if !ctx.large && size > 0xffffffffu64 { return Err(Error::Geometry); }
    let base_sectors = billed_sectors(ctx.block_bytes, count);
    if ctx.retained_sectors > u64::MAX - base_sectors { return Err(Error::Accounting); }
    let sectors = base_sectors + ctx.retained_sectors;
    let accounting = match inode_blocks::encode(sectors, ctx.block_bytes as u32, ctx.huge_file) {
        Some(value) => value, None => { return Err(Error::Accounting); }
    };
    let links = subdirectories + 2;
    let stored_links = if links <= 65000 { links as u16 }
        else if ctx.indexed && ctx.dir_nlink { 1u16 } else { return Err(Error::Links); };
    let time = match inode_time::encode_extended(seconds, nanoseconds) {
        Some(value) => value, None => { return Err(Error::Time); }
    };
    let version = word64(&ctx.source_inode, 36, 152).unwrap();
    if version >= 0x7fffffffffffffffu64 { return Err(Error::Version); }
    let version = version + 1;
    let mut raw = copy(&ctx.source_inode);
    let mut flags = bytes::read_le32(&raw, 32).unwrap() | EXTENTS_FLAG;
    flags = if ctx.indexed { flags | INDEX_FLAG } else { flags & !INDEX_FLAG };
    flags = if accounting.huge { flags | HUGE_FLAG } else { flags & !HUGE_FLAG };
    if !put32(&mut raw, 32, flags) || !put32(&mut raw, 4, size as u32)
        || !put32(&mut raw, 108, (size >> 32) as u32) || !put16(&mut raw, 26, stored_links)
        || !put32(&mut raw, 36, version as u32) || !put32(&mut raw, 152, (version >> 32) as u32)
        || !put32(&mut raw, 12, time.base) || !put32(&mut raw, 16, time.base)
        || !put32(&mut raw, 132, time.extra) || !put32(&mut raw, 136, time.extra) {
        return Err(Error::Inode);
    }
    let mut i = 0usize;
    while i < 60
        invariant i <= 60, raw.len() == 256, root.len() == 60,
        decreases 60 - i,
    { raw.set(40 + i, root[i]); i += 1; }
    i = 0;
    while i < 4
        invariant i <= 4, raw.len() == 256,
        decreases 4 - i,
    { raw.set(28 + i, accounting.low[i]); i += 1; }
    raw.set(116, accounting.high[0]); raw.set(117, accounting.high[1]);
    if ctx.metadata {
        let checksum = inode::calculated_checksum(&raw, ctx.number, ctx.fs_seed).unwrap();
        if !put16(&mut raw, 124, (checksum & 0xffff) as u16)
            || !put16(&mut raw, 130, (checksum >> 16) as u16) { return Err(Error::Inode); }
    }
    Ok(raw)
}

fn validate_pool(ctx: &Context, pool: &[u64], forbidden: &[ReservedRange], budget: Budget) -> (r: Result<(), Error>)
    ensures r.is_ok() ==> pool.len() <= MAX_BLOCKS,
{
    proof { use_type_invariant(ctx); }

    if budget.entries > MAX_ENTRIES || budget.blocks == 0 || budget.blocks > MAX_BLOCKS
        || pool.len() > budget.blocks || forbidden.len() > MAX_BLOCKS {
        return Err(Error::Budget);
    }
    let mut j = 0usize;
    while j < forbidden.len()
        invariant j <= forbidden.len(),
        decreases forbidden.len() - j,
    {
        let value = forbidden[j];
        if value.count == 0 || value.first >= ctx.fs_blocks || value.count > ctx.fs_blocks - value.first {
            return Err(Error::Alias);
        }
        j += 1;
    }
    let mut i = 0usize;
    while i < pool.len()
        invariant i <= pool.len(),
        decreases pool.len() - i,
    {
        let physical = pool[i];
        if physical == 0 || physical >= ctx.fs_blocks || physical > MAX_PHYSICAL { return Err(Error::Pool); }
        if i > 0 && pool[i - 1] >= physical { return Err(Error::Alias); }
        j = 0;
        while j < forbidden.len()
            invariant j <= forbidden.len(),
            decreases forbidden.len() - j,
        {
            let range = forbidden[j];
            if physical >= range.first && physical - range.first < range.count { return Err(Error::Alias); }
            j += 1;
        }
        i += 1;
    }
    Ok(())
}

pub fn rebuild(ctx: &Context, entries: &[Entry], pool: &[u64], forbidden: &[ReservedRange],
    budget: Budget, seconds: i64, nanoseconds: u32) -> Result<Plan, Error>
{
    proof { use_type_invariant(ctx); }

    if entries.len() > budget.entries || entries.len() > MAX_ENTRIES { return Err(Error::Budget); }
    match validate_pool(ctx, pool, forbidden, budget) {
        Ok(()) => {}, Err(error) => { return Err(error); }
    }
    if inode_time::encode_extended(seconds, nanoseconds).is_none() { return Err(Error::Time); }
    let mut hashes: Vec<dir_hash::Hash> = Vec::new(); let mut subdirectories = 0usize; let mut i = 0usize;
    while i < entries.len()
        invariant i <= entries.len(), hashes.len() == i, subdirectories <= i,
        decreases entries.len() - i,
    {
        let value = &entries[i];
        if !valid_name(&value.name) { return Err(Error::Name); }
        if value.inode == 0 || value.inode > ctx.inodes || value.file_type == 0 || value.file_type > 7 {
            return Err(Error::Target);
        }
        if value.file_type == 2 {
            if value.inode == ctx.number || value.inode == ctx.parent { return Err(Error::Target); }
            subdirectories += 1;
        }
        let hash = match dir_hash::calculate(&value.name, ctx.hash_seed, ctx.hash_version) {
            Some(value) => value, None => { return Err(Error::Feature); }
        };
        hashes.push(hash); i += 1;
    }
    let names = sorted(entries, &hashes, 0);
    i = 0;
    while i < names.len()
        invariant i <= names.len(), names.len() == entries.len(),
            forall|j: int| 0 <= j < names.len() ==> #[trigger] names@[j] < entries.len(),
        decreases names.len() - i,
    {
        if i > 0 && bytes::equal(&entries[names[i - 1]].name, &entries[names[i]].name) {
            return Err(Error::Duplicate);
        }
        i += 1;
    }
    let targets = sorted(entries, &hashes, 2);
    i = 0;
    while i < targets.len()
        invariant i <= targets.len(), targets.len() == entries.len(),
            forall|j: int| 0 <= j < targets.len() ==> #[trigger] targets@[j] < entries.len(),
        decreases targets.len() - i,
    {
        if i > 0 {
            let a = &entries[targets[i - 1]]; let b = &entries[targets[i]];
            if a.inode == b.inode
                && (a.generation != b.generation || a.file_type != b.file_type || a.file_type == 2) {
                return Err(Error::Target);
            }
        }
        i += 1;
    }
    let order = if ctx.indexed { sorted(entries, &hashes, 1) } else { names };
    let (mut images, edges) = match leaves(ctx, entries, &hashes, &order, budget) {
        Ok(value) => value, Err(error) => { return Err(error); }
    };
    let levels = if ctx.indexed {
        match index_tree(ctx, &mut images, edges, budget) { Ok(value) => value, Err(error) => { return Err(error); } }
    } else { 0u8 };
    if images.len() > pool.len() || images.len() > budget.blocks { return Err(Error::Pool); }
    let root = match extent_root(pool, images.len()) { Ok(value) => value, Err(error) => { return Err(error); } };
    let inode_image = match seal_inode(ctx, &root, images.len(), subdirectories, seconds, nanoseconds) {
        Ok(value) => value, Err(error) => { return Err(error); }
    };
    let mut mappings = Vec::new(); i = 0;
    while i < images.len()
        invariant i <= images.len(), mappings.len() == i, images.len() <= pool.len(),
        decreases images.len() - i,
    {
        images[i].physical = pool[i];
        mappings.push(Mapping { logical: i as u32, physical: pool[i] }); i += 1;
    }
    let mut retained = Vec::new(); i = 0;
    while i < entries.len()
        invariant i <= entries.len(), retained.len() == i,
        decreases entries.len() - i,
    { retained.push(clone_entry(&entries[i])); i += 1; }
    Ok(Plan { images, mappings, inode_image, extent_root: root, entries: retained,
        deltas: Vec::new(), indexed: ctx.indexed, levels, old_tree_blocks: ctx.old_tree_blocks,
        empty_victim_required: None })
}
fn locate(entries: &[Entry], name: &[u8]) -> (r: Option<usize>)
    ensures match r { Some(index) => index < entries.len(), None => true },
{
    let mut i = 0usize;
    while i < entries.len()
        invariant i <= entries.len(),
        decreases entries.len() - i,
    {
        if bytes::equal(&entries[i].name, name) { return Some(i); }
        i += 1;
    }
    None
}
fn copy_entries(entries: &[Entry], skip_a: Option<usize>, skip_b: Option<usize>) -> Vec<Entry> {
    let mut out = Vec::new(); let mut i = 0usize;
    while i < entries.len()
        invariant i <= entries.len(), out.len() <= i,
        decreases entries.len() - i,
    {
        if skip_a != Some(i) && skip_b != Some(i) { out.push(clone_entry(&entries[i])); }
        i += 1;
    }
    out
}

/// Deltas are namespace-edge changes, not permission to increment arbitrary
/// inode fields. The caller composes target initialization, orphan/link-count
/// changes and any child-parent changes before whole-filesystem admission.
pub fn insert(ctx: &Context, entries: &[Entry], value: Entry, pool: &[u64],
    forbidden: &[ReservedRange], budget: Budget, seconds: i64, nanoseconds: u32) -> Result<Plan, Error>
{
    proof { use_type_invariant(ctx); }

    if locate(entries, &value.name).is_some() { return Err(Error::Exists); }
    if entries.len() >= budget.entries || entries.len() >= MAX_ENTRIES { return Err(Error::Budget); }
    let change = LinkDelta { inode: value.inode, generation: value.generation, file_type: value.file_type, delta: 1 };
    let mut changed = copy_entries(entries, None, None); changed.push(value);
    let mut plan = match rebuild(ctx, &changed, pool, forbidden, budget, seconds, nanoseconds) {
        Ok(value) => value, Err(error) => { return Err(error); }
    };
    plan.deltas.push(change); Ok(plan)
}

pub fn delete(ctx: &Context, entries: &[Entry], name: &[u8], expected_inode: u32,
    expected_generation: u32, pool: &[u64], forbidden: &[ReservedRange],
    budget: Budget, seconds: i64, nanoseconds: u32) -> Result<Plan, Error>
{
    proof { use_type_invariant(ctx); }

    if !valid_name(name) { return Err(Error::Name); }
    if entries.len() > budget.entries || entries.len() > MAX_ENTRIES { return Err(Error::Budget); }
    let ordinal = match locate(entries, name) { Some(value) => value, None => { return Err(Error::Missing); } };
    let victim = &entries[ordinal];
    if victim.inode != expected_inode || victim.generation != expected_generation { return Err(Error::Identity); }
    let change = LinkDelta { inode: victim.inode, generation: victim.generation, file_type: victim.file_type, delta: -1 };
    let empty = if victim.file_type == 2 { Some((victim.inode, victim.generation)) } else { None };
    let changed = copy_entries(entries, Some(ordinal), None);
    let mut plan = match rebuild(ctx, &changed, pool, forbidden, budget, seconds, nanoseconds) {
        Ok(value) => value, Err(error) => { return Err(error); }
    };
    plan.deltas.push(change); plan.empty_victim_required = empty; Ok(plan)
}

pub fn rename(ctx: &Context, entries: &[Entry], old_name: &[u8], new_name: &[u8],
    expected_inode: u32, expected_generation: u32, replace: bool, pool: &[u64],
    forbidden: &[ReservedRange], budget: Budget, seconds: i64, nanoseconds: u32) -> Result<Mutation, Error>
{
    proof { use_type_invariant(ctx); }

    if !valid_name(old_name) || !valid_name(new_name) { return Err(Error::Name); }
    if entries.len() > budget.entries || entries.len() > MAX_ENTRIES { return Err(Error::Budget); }
    let source_at = match locate(entries, old_name) { Some(value) => value, None => { return Err(Error::Missing); } };
    let source = &entries[source_at];
    proof { use_type_invariant(source); }
    if source.inode != expected_inode || source.generation != expected_generation { return Err(Error::Identity); }
    if bytes::equal(old_name, new_name) {
        return if replace { Ok(Mutation::NoChange) } else { Err(Error::Exists) };
    }
    let target_at = locate(entries, new_name);
    let mut removed = None; let mut empty = None;
    if let Some(ordinal) = target_at {
        let victim = &entries[ordinal];
        if !replace { return Err(Error::Exists); }
        if victim.inode == source.inode {
            if victim.generation != source.generation || victim.file_type != source.file_type { return Err(Error::Identity); }
            return Ok(Mutation::NoChange);
        }
        if (victim.file_type == 2) != (source.file_type == 2) { return Err(Error::Type); }
        removed = Some(LinkDelta { inode: victim.inode, generation: victim.generation, file_type: victim.file_type, delta: -1 });
        if victim.file_type == 2 { empty = Some((victim.inode, victim.generation)); }
    }
    let mut changed = copy_entries(entries, Some(source_at), target_at);
    changed.push(Entry { name: copy(new_name), inode: source.inode, generation: source.generation, file_type: source.file_type });
    let mut plan = match rebuild(ctx, &changed, pool, forbidden, budget, seconds, nanoseconds) {
        Ok(value) => value, Err(error) => { return Err(error); }
    };
    if let Some(change) = removed { plan.deltas.push(change); }
    plan.empty_victim_required = empty;
    Ok(Mutation::Rebuild(plan))
}

}
