// SPDX-License-Identifier: MPL-2.0

//! Linux direct/single/double/triple-indirect block maps.
//! These standalone structural readers do not confer allocation, credential,
//! mounted-inode, or device-write authority. Source admission is separate.

use vstd::prelude::*;
use crate::{block_size, bytes, inode_blocks, snapshot::Snapshot, source_block, xattr};

verus! {

pub enum Error { Geometry, Inode, Unsupported, OutOfRange, Source, Cycle, Alias, Budget }

pub struct Path { pub root: usize, pub depth: u8, pub offsets: [u32; 3], pub boundary: u32 }

pub open spec fn pointers(block_bytes: u32) -> nat { block_bytes as nat / 4 }
pub open spec fn capacity(block_bytes: u32) -> nat {
    12 + pointers(block_bytes) + pointers(block_bytes)*pointers(block_bytes)
        + pointers(block_bytes)*pointers(block_bytes)*pointers(block_bytes)
}
pub open spec fn path_value(block_bytes: u32, logical: u64) -> Path {
    let n = pointers(block_bytes) as int;
    let square = n*n;
    if logical < 12 {
        Path { root: logical as usize, depth: 0, offsets: [0,0,0], boundary: (11-logical) as u32 }
    } else if logical < 12+n {
        Path { root: 12, depth: 1, offsets: [(logical as nat-12) as u32,0,0], boundary: (n-1-(logical as nat-12)) as u32 }
    } else if logical < 12+n+square {
        let k = logical as int-12-n;
        Path { root: 13, depth: 2, offsets: [(k/n) as u32,(k%n) as u32,0], boundary: (n-1-k%n) as u32 }
    } else {
        let k = logical as int-12-n-square;
        Path { root: 14, depth: 3, offsets: [(k/square) as u32,((k/n)%n) as u32,(k%n) as u32],
            boundary: (n-1-k%n) as u32 }
    }
}
pub open spec fn valid_path(p: Path, block_bytes: u32, logical: u64) -> bool {
    &&& block_size::accepted(block_bytes as nat) && logical <= 4294967295 && logical < capacity(block_bytes)
    &&& p == path_value(block_bytes, logical)
    &&& p.root < 15 && p.depth <= 3 && p.boundary < pointers(block_bytes)
    &&& forall|i: int| 0 <= i < p.depth ==> #[trigger] p.offsets@[i] < pointers(block_bytes)
}
proof fn geometry_bounds(block_bytes: u32)
    requires block_size::accepted(block_bytes as nat),
    ensures 256 <= pointers(block_bytes) <= 16384, pointers(block_bytes)*pointers(block_bytes) <= 268435456,
{
    assert(256 <= pointers(block_bytes) <= 16384);
    assert(pointers(block_bytes)*pointers(block_bytes) <= 268435456) by (nonlinear_arith)
        requires 256 <= pointers(block_bytes) <= 16384;
}

proof fn quotient_below_bound(value: nat, divisor: nat, bound: nat)
    requires divisor > 0, bound > 0,
    ensures (value/divisor < bound) == (value < divisor*bound),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(value as int, divisor as int);
    let q = value as int/divisor as int;
    let r = value as int%divisor as int;
    vstd::arithmetic::mul::lemma_mul_is_commutative(q, divisor as int);
    assert((q < bound) == (value < divisor*bound)) by (nonlinear_arith)
        requires divisor > 0, bound > 0, 0 <= r < divisor, value == q*divisor+r;
}

/// Exact pointer decomposition used by Linux ext4_block_to_path. Logical block
/// numbers retain ext4_lblk_t's 32-bit limit even with 64 KiB filesystem blocks.
pub fn path(block_bytes: u32, logical: u64) -> (r: Result<Path, Error>)
    ensures match r { Ok(p) => valid_path(p, block_bytes, logical),
        Err(_) => !block_size::accepted(block_bytes as nat) || logical > 4294967295 || logical >= capacity(block_bytes) },
{
    if !block_size::valid(block_bytes as usize) { return Err(Error::Geometry); }
    if logical > 4294967295 { return Err(Error::OutOfRange); }
    proof { geometry_bounds(block_bytes); }
    let n = block_bytes as u64 / 4;
    let square = n * n;
    if logical < 12 {
        return Ok(Path { root: logical as usize, depth: 0, offsets: [0, 0, 0],
            boundary: (11 - logical) as u32 });
    }
    let single = logical - 12;
    if single < n {
        return Ok(Path { root: 12, depth: 1, offsets: [single as u32, 0, 0],
            boundary: (n - 1 - single) as u32 });
    }
    let double = single - n;
    if double < square {
        proof {
            quotient_below_bound(double as nat, n as nat, n as nat);
            assert(double/n < n);
            assert(logical < capacity(block_bytes)) by (nonlinear_arith)
                requires logical as int == 12+n as int+double as int, double < square,
                    square as nat == pointers(block_bytes)*pointers(block_bytes),
                    n as nat == pointers(block_bytes), n > 0;
        }
        return Ok(Path { root: 13, depth: 2,
            offsets: [(double / n) as u32, (double % n) as u32, 0],
            boundary: (n - 1 - double % n) as u32 });
    }
    let triple = double - square;
    proof { quotient_below_bound(triple as nat, square as nat, n as nat); }
    if triple / square >= n { return Err(Error::OutOfRange); }
    Ok(Path { root: 14, depth: 3,
        offsets: [(triple / square) as u32, ((triple / n) % n) as u32, (triple % n) as u32],
        boundary: (n - 1 - triple % n) as u32 })
}

pub struct RootView { pub raw: Seq<u8>, pub block_bytes: u32, pub blocks: u64, pub size: u64, pub mode: u16, pub large_directory: bool }
pub open spec fn valid_root(v: RootView) -> bool {
    &&& 128 <= v.raw.len() <= 65536 && block_size::accepted(v.block_bytes as nat)
    &&& 0 < v.blocks <= 4294967296
    &&& v.mode == 0x8000 || v.mode == 0x4000 || v.mode == 0xa000
    &&& v.mode == bytes::le16(v.raw, 0) as u16 & 0xf000
    &&& bytes::le32(v.raw, 32) as u32 & 0x10080000 == 0
    &&& v.size as nat == bytes::le32(v.raw, 4) + if v.mode == 0x8000 || v.mode == 0x4000 && v.large_directory {
        4294967296*bytes::le32(v.raw, 108) } else { 0nat }
    &&& forall|i: int| 0 <= i < 15 ==> #[trigger] bytes::le32(v.raw, 40+4*i) == 0 || bytes::le32(v.raw, 40+4*i) < v.blocks
}
pub open spec fn next_address(source: Seq<u8>, root: u32, p: Path, metadata: Seq<u32>, block_bytes: u32) -> u32 {
    if metadata.len() == 0 { root } else {
        bytes::le32(source, metadata.last() as int*block_bytes as int
            + p.offsets@[metadata.len() as int-1] as int*4) as u32
    }
}
pub open spec fn trace(source: Seq<u8>, root: u32, p: Path, metadata: Seq<u32>, block_bytes: u32) -> bool {
    &&& metadata.len() <= p.depth
    &&& forall|i: int| 0 <= i < metadata.len() ==> #[trigger] metadata[i] != 0
        && metadata[i] == if i == 0 { root } else {
            bytes::le32(source, metadata[i-1] as int*block_bytes as int+p.offsets@[i-1] as int*4) as u32
        }
}
pub open spec fn unique(numbers: Seq<u32>) -> bool {
    forall|i: int,j: int| 0 <= i < j < numbers.len() ==> #[trigger] numbers[i] != #[trigger] numbers[j]
}
/// Pure pointer traversal, retaining holes at every remaining indirection.
pub open spec fn address_at(source: Seq<u8>, first: u32, offsets: Seq<u32>, block_bytes: u32, level: nat) -> u32
    recommends level <= offsets.len(),
    decreases level,
{
    if level == 0 { first } else {
        let previous = address_at(source, first, offsets, block_bytes, (level-1) as nat);
        if previous == 0 { 0 } else {
            bytes::le32(source, previous as int*block_bytes as int+offsets[level as int-1] as int*4) as u32
        }
    }
}

pub open spec fn physical_at(root: RootView, source: Seq<u8>, logical: u64) -> u32 {
    if !block_size::accepted(root.block_bytes as nat) || logical > 4294967295 || logical >= capacity(root.block_bytes) { 0 }
    else {
        let p = path_value(root.block_bytes, logical);
        address_at(source, bytes::le32(root.raw, 40+p.root as int*4) as u32, p.offsets@, root.block_bytes, p.depth as nat)
    }
}

/// Stored bytes only. Permission, decryption and verity are separate layers.
/// The out-of-source case is total and cannot be reached by a successful read.
pub open spec fn stored_byte(root: RootView, source: Seq<u8>, offset: int) -> u8 {
    if root.block_bytes == 0 || offset < 0 { 0 } else {
        let physical = physical_at(root, source, (offset/root.block_bytes as int) as u64);
        let at = physical as int*root.block_bytes as int+offset%root.block_bytes as int;
        if physical == 0 || at < 0 || at >= source.len() { 0 } else { source[at] }
    }
}

proof fn trace_address(source: Seq<u8>, first: u32, p: Path, metadata: Seq<u32>, block_bytes: u32)
    requires p.depth <= 3, trace(source, first, p, metadata, block_bytes),
    ensures next_address(source, first, p, metadata, block_bytes)
        == address_at(source, first, p.offsets@, block_bytes, metadata.len()),
    decreases metadata.len(),
{
    if metadata.len() > 0 {
        let prefix = metadata.drop_last();
        assert(trace(source, first, p, prefix, block_bytes));
        trace_address(source, first, p, prefix, block_bytes);
        assert(metadata.last() != 0);
        assert(metadata.last() == next_address(source, first, p, prefix, block_bytes));
    }
}

proof fn zero_suffix(source: Seq<u8>, first: u32, offsets: Seq<u32>, block_bytes: u32, start: nat, end: nat)
    requires start <= end <= offsets.len(), address_at(source, first, offsets, block_bytes, start) == 0,
    ensures address_at(source, first, offsets, block_bytes, end) == 0,
    decreases end-start,
{
    if start < end { zero_suffix(source, first, offsets, block_bytes, start, (end-1) as nat); }
}

proof fn division_from_remainder(value: int, divisor: int, quotient: int, remainder: int)
    requires divisor > 0, 0 <= remainder < divisor, value == quotient*divisor+remainder,
    ensures value/divisor == quotient, value%divisor == remainder,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(value, divisor);
    let actual_q = value/divisor;
    let actual_r = value%divisor;
    vstd::arithmetic::mul::lemma_mul_is_commutative(actual_q, divisor);
    assert(actual_q == quotient) by (nonlinear_arith)
        requires divisor > 0, 0 <= remainder < divisor, 0 <= actual_r < divisor,
            value == quotient*divisor+remainder, value == actual_q*divisor+actual_r;
}

proof fn same_block(current: u64, block_bytes: u32, extra: usize)
    requires block_bytes > 0, current as nat+extra <= u64::MAX,
        current as nat%block_bytes as nat+extra < block_bytes,
    ensures (current as int+extra as int)/block_bytes as int == current as int/block_bytes as int,
        (current as int+extra as int)%block_bytes as int == current as int%block_bytes as int+extra as int,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(current as int, block_bytes as int);
    division_from_remainder(current as int+extra as int, block_bytes as int,
        current as int/block_bytes as int, current as int%block_bytes as int+extra as int);
}

proof fn source_word(block: source_block::BlockView, offset: int)
    requires source_block::valid(block), 0 <= offset, offset+4 <= block.size,
    ensures bytes::le32(block.bytes, offset) == bytes::le32(block.source, block.number as int*block.size as int+offset),
{
    let start = block.number as int*block.size as int;
    vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(block.size as int, block.number as int, 1);
    vstd::arithmetic::mul::lemma_mul_is_commutative(block.number as int, block.size as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(block.number as int+1, block.size as int);
    assert(start+block.size as int == (block.number as int+1)*block.size as int);
    assert(start+block.size as int <= block.source.len());
    assert(block.bytes == block.source.subrange(start, start+block.size as int));
    assert(block.bytes[offset] == block.source[start+offset]);
    assert(block.bytes[offset+1] == block.source[start+offset+1]);
    assert(block.bytes[offset+2] == block.source[start+offset+2]);
    assert(block.bytes[offset+3] == block.source[start+offset+3]);
}

pub open spec fn mapping_valid(root: RootView, source: Seq<u8>, logical: u64, m: Mapping) -> bool {
    let p = path_value(root.block_bytes, logical);
    let first = bytes::le32(root.raw, 40+p.root as int*4) as u32;
    let last = next_address(source, first, p, m.metadata@, root.block_bytes);
    &&& valid_path(p, root.block_bytes, logical)
    &&& m.boundary == p.boundary && trace(source, first, p, m.metadata@, root.block_bytes)
    &&& unique(m.metadata@)
    &&& m.physical == if physical_at(root, source, logical) == 0 { None } else { Some(physical_at(root, source, logical)) }
    &&& forall|i: int| 0 <= i < m.metadata.len() ==> 0 < #[trigger] m.metadata@[i] < root.blocks
    &&& if m.metadata.len() < p.depth { last == 0 && m.physical is None } else {
        m.physical == if last == 0 { None } else { Some(last) }
    }
    &&& match m.physical { Some(number) => 0 < number < root.blocks
        && forall|i: int| 0 <= i < m.metadata.len() ==> #[trigger] m.metadata@[i] != number,
        None => true }
}

pub struct Root<'a> {
    raw: &'a [u8], block_bytes: u32, blocks: u64, size: u64, mode: u16, large_directory: bool,
}

pub fn parse<'a>(raw: &'a [u8], block_bytes: u32, blocks: u64,
    large_directory: bool, huge_file: bool, cluster_bytes: u32, ea_inode: bool) -> (r: Result<Root<'a>, Error>)
    ensures match r { Ok(root) => root.wf() && root.view().raw == raw@
        && root.view().block_bytes == block_bytes && root.view().blocks == blocks && root.view().large_directory == large_directory
        && root.view().size as nat == bytes::le32(raw@, 4)
            + if root.view().mode == 0x8000 || root.view().mode == 0x4000 && large_directory {
                4294967296 * bytes::le32(raw@, 108) } else { 0nat },
        Err(_) => true },
{
    if !block_size::valid(block_bytes as usize) || blocks == 0 || blocks > 4294967296 {
        return Err(Error::Geometry);
    }
    if raw.len() < 128 || raw.len() > 65536 { return Err(Error::Inode); }
    let mode = bytes::read_le16(raw, 0).unwrap() & 0xf000;
    if mode != 0x8000 && mode != 0x4000 && mode != 0xa000 { return Err(Error::Unsupported); }
    let flags = bytes::read_le32(raw, 32).unwrap();
    if flags & 0x10080000 != 0 { return Err(Error::Unsupported); }
    let low = bytes::read_le32(raw, 4).unwrap() as u64;
    let high = if mode == 0x8000 || mode == 0x4000 && large_directory {
        bytes::read_le32(raw, 108).unwrap() as u64
    } else { 0 };
    let size = low + high * 4294967296;
    if mode == 0xa000 {
        let sectors = match inode_blocks::decode(raw, block_bytes, huge_file) {
            Some(n) => n, None => { return Err(Error::Inode); }
        };
        let address = xattr::inode_pointer(raw).unwrap();
        if cluster_bytes < block_bytes || cluster_bytes % block_bytes != 0 { return Err(Error::Geometry); }
        let ea_sectors = if address != 0 { cluster_bytes as u64 / 512 } else { 0 };
        if ea_inode && size > 0 && size < 60 { return Err(Error::Unsupported); }
        if !ea_inode && sectors == ea_sectors { return Err(Error::Unsupported); }
    }
    let mut i = 0usize;
    while i < 15
        invariant i <= 15, raw.len() >= 128,
            forall|j: int| 0 <= j < i ==> #[trigger] bytes::le32(raw@, 40+4*j) == 0 || bytes::le32(raw@, 40+4*j) < blocks,
        decreases 15-i,
    {
        let address = bytes::read_le32(raw, 40 + i * 4).unwrap() as u64;
        if address >= blocks && address != 0 { return Err(Error::OutOfRange); }
        i += 1;
    }
    Ok(Root { raw, block_bytes, blocks, size, mode, large_directory })
}

pub struct Mapping { pub physical: Option<u32>, pub metadata: Vec<u32>, pub boundary: u32 }

impl<'a> Root<'a> {
    pub closed spec fn view(&self) -> RootView {
        RootView { raw: self.raw@, block_bytes: self.block_bytes, blocks: self.blocks, size: self.size, mode: self.mode, large_directory: self.large_directory }
    }
    pub open spec fn wf(&self) -> bool { valid_root(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn size(&self) -> (r: u64) ensures self.wf(), r == self.view().size {
        proof { use_type_invariant(self); } self.size
    }
    pub fn mode(&self) -> (r: u16) ensures self.wf(), r == self.view().mode {
        proof { use_type_invariant(self); } self.mode
    }
    pub fn geometry(&self) -> (r: (u32, u64)) ensures self.wf(), r == (self.view().block_bytes, self.view().blocks) {
        proof { use_type_invariant(self); } (self.block_bytes, self.blocks)
    }

    pub fn lookup(&self, source: &Snapshot<'_>, logical: u64) -> (r: Result<Mapping, Error>)
        ensures match r { Ok(mapping) => mapping_valid(self.view(), source.view(), logical, mapping), Err(_) => true },
    {
        proof { use_type_invariant(self); }
        if self.blocks > source.partition_bytes() / self.block_bytes as u64 {
            return Err(Error::Source);
        }
        let selected = match path(self.block_bytes, logical) {
            Ok(p) => p, Err(e) => { return Err(e); }
        };
        let mut address = bytes::read_le32(self.raw, 40 + selected.root * 4).unwrap();
        let ghost first = address;
        let mut metadata = Vec::<u32>::new();
        let mut level = 0usize;
        while level < selected.depth as usize
            invariant self.wf(), valid_path(selected, self.block_bytes, logical),
                level == metadata.len() <= selected.depth, unique(metadata@),
                trace(source.view(), first, selected, metadata@, self.block_bytes),
                address == next_address(source.view(), first, selected, metadata@, self.block_bytes),
                first == bytes::le32(self.raw@, 40+selected.root as int*4) as u32,
                forall|j: int| 0 <= j < metadata.len() ==> 0 < #[trigger] metadata@[j] < self.blocks,
            decreases selected.depth as usize-level,
        {
            if address == 0 {
                proof {
                    trace_address(source.view(), first, selected, metadata@, self.block_bytes);
                    zero_suffix(source.view(), first, selected.offsets@, self.block_bytes, level as nat, selected.depth as nat);
                }
                return Ok(Mapping { physical: None, metadata, boundary: selected.boundary });
            }
            if address as u64 >= self.blocks { return Err(Error::OutOfRange); }
            let mut i = 0usize;
            while i < metadata.len()
                invariant i <= metadata.len(),
                    forall|j: int| 0 <= j < i ==> #[trigger] metadata@[j] != address,
                decreases metadata.len()-i,
            {
                if metadata[i] == address { return Err(Error::Cycle); }
                i += 1;
            }
            let ghost prior_metadata = metadata@;
            let ghost prior_address = address;
            metadata.push(address);
            let block = match source_block::capture(source, address as u64, self.block_bytes) {
                Some(block) => block, None => { return Err(Error::Source); }
            };
            proof {
                source_word(block.view(), selected.offsets@[level as int] as int*4);
                assert(trace(source.view(), first, selected, metadata@, self.block_bytes));
            }
            address = match bytes::read_le32(block.raw(), selected.offsets[level] as usize * 4) {
                Some(address) => address, None => { return Err(Error::Source); }
            };
            level += 1;
        }
        if address as u64 >= self.blocks && address != 0 { return Err(Error::OutOfRange); }
        let mut i = 0usize;
        while i < metadata.len()
            invariant i <= metadata.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] metadata@[j] != address || address == 0,
            decreases metadata.len()-i,
        {
            if metadata[i] == address && address != 0 { return Err(Error::Alias); }
            i += 1;
        }
        proof { trace_address(source.view(), first, selected, metadata@, self.block_bytes); }
        Ok(Mapping { physical: if address == 0 { None } else { Some(address) },
            metadata, boundary: selected.boundary })
    }

    /// Read stored bytes with explicit sparse-hole zeros and EOF clipping.
    /// Encryption, verity and permission policy belong to their own layers.
    pub fn read(&self, source: &Snapshot<'_>, offset: u64, length: usize)
        -> (r: Result<Vec<u8>, Error>)
        ensures match r { Ok(data) => length <= 65536 && data.len() <= length
            && data.len() as nat == (if offset >= self.view().size { 0nat }
                else if self.view().size-offset < length { (self.view().size-offset) as nat } else { length as nat })
            && forall|i: int| 0 <= i < data.len() ==> #[trigger] data@[i] == stored_byte(self.view(), source.view(), offset as int+i),
            Err(_) => true },
    {
        proof { use_type_invariant(self); }
        if length > 65536 { return Err(Error::Budget); }
        let count = if offset >= self.size { 0 } else {
            let remaining = self.size - offset;
            if remaining < length as u64 { remaining as usize } else { length }
        };
        let mut out = Vec::<u8>::new();
        let mut done = 0usize;
        while done < count
            invariant self.wf(), done <= count <= length <= 65536, out.len() == done,
                count as nat == if offset >= self.size { 0nat }
                    else if self.size-offset < length { (self.size-offset) as nat } else { length as nat },
                count > 0 ==> offset < self.size && offset as nat+count <= self.size,
                forall|i: int| 0 <= i < done ==> #[trigger] out@[i] == stored_byte(self.view(), source.view(), offset as int+i),
            decreases count-done,
        {
            let current = offset + done as u64;
            let logical = current / self.block_bytes as u64;
            let within = (current % self.block_bytes as u64) as usize;
            let available = self.block_bytes as usize - within;
            let take = if available < count - done { available } else { count - done };
            let mapped = match self.lookup(source, logical) {
                Ok(mapped) => mapped, Err(e) => { return Err(e); }
            };
            match mapped.physical {
                None => {
                    let mut j = 0usize;
                    while j < take
                        invariant j <= take, out.len() == done+j, take <= count-done,
                            self.wf(), self.block_bytes > 0, current == offset+done,
                            within as nat+take <= self.block_bytes, current%self.block_bytes as u64 == within,
                            physical_at(self.view(), source.view(), logical) == 0,
                            logical == current/self.block_bytes as u64,
                            offset as nat+count <= self.size, done < count,
                            forall|i: int| 0 <= i < done+j ==> #[trigger] out@[i] == stored_byte(self.view(), source.view(), offset as int+i),
                        decreases take-j,
                    {
                        proof { same_block(current, self.block_bytes, j); }
                        out.push(0);
                        j += 1;
                    }
                },
                Some(number) => {
                    let block = match source_block::capture(source, number as u64, self.block_bytes) {
                        Some(block) => block, None => { return Err(Error::Source); }
                    };
                    let raw = block.raw();
                    let mut j = 0usize;
                    while j < take
                        invariant j <= take, out.len() == done+j, take <= count-done,
                            within as nat+take <= raw.len(), self.wf(), self.block_bytes > 0,
                            current == offset+done, current%self.block_bytes as u64 == within,
                            block.wf(), block.view().source == source.view(), block.view().size == self.block_bytes,
                            block.view().number == number, raw@ == block.view().bytes,
                            physical_at(self.view(), source.view(), logical) == number, number > 0,
                            logical == current/self.block_bytes as u64,
                            offset as nat+count <= self.size, done < count,
                            forall|i: int| 0 <= i < done+j ==> #[trigger] out@[i] == stored_byte(self.view(), source.view(), offset as int+i),
                        decreases take-j,
                    {
                        proof { same_block(current, self.block_bytes, j); }
                        out.push(raw[within+j]);
                        j += 1;
                    }
                },
            }
            done += take;
        }
        Ok(out)
    }

    /// Enumerate every nonzero pointer, including mappings beyond EOF needed
    /// for safe truncation. Shared metadata/data blocks and cycles are rejected.
    pub fn collect(&self, source: &Snapshot<'_>, node_budget: usize, data_budget: usize)
        -> (r: Result<Collection, Error>)
        ensures match r { Ok(collection) => collection.view().data.len() <= data_budget && collection.view().metadata.len() <= node_budget
            && unique(collection.view().claims) && collection.view().claims.len() == collection.view().data.len()+collection.view().metadata.len(),
            Err(_) => true },
    {
        proof { use_type_invariant(self); geometry_bounds(self.block_bytes); }
        if node_budget > 65536 || data_budget > 65536 { return Err(Error::Budget); }
        if self.blocks > source.partition_bytes() / self.block_bytes as u64 {
            return Err(Error::Source);
        }
        let n = self.block_bytes as u64 / 4;
        let square = n * n;
        let mut result = Collection { data: Vec::new(), metadata: Vec::new(), claims: Vec::new() };
        let mut i = 0usize;
        while i < 12
            invariant self.wf(), i <= 12, data_budget <= 65536, node_budget <= 65536,
                n == self.block_bytes as u64/4, 256 <= n <= 16384, square == n*n <= 268435456,
                result.data.len() <= data_budget, result.metadata.len() == 0,
                result.claims.len() == result.data.len(), unique(result.claims@),
            decreases 12-i,
        {
            let number = bytes::read_le32(self.raw, 40 + i * 4).unwrap();
            if number != 0 {
                if result.data.len() >= data_budget { return Err(Error::Budget); }
                if !claim(&mut result.claims, number) { return Err(Error::Alias); }
                result.data.push(DataBlock { logical: i as u64, physical: number });
            }
            i += 1;
        }
        let mut stack = Vec::<Frame>::new();
        let mut root = 12usize;
        while root < 15
            invariant self.wf(), 12 <= root <= 15, data_budget <= 65536, node_budget <= 65536,
                256 <= n <= 16384, n == self.block_bytes as u64/4, square == n*n <= 268435456,
                result.data.len() <= data_budget, result.metadata.len() <= node_budget,
                result.claims.len() == result.data.len()+result.metadata.len(), unique(result.claims@),
                stack.len() == result.metadata.len(),
                forall|j: int| 0 <= j < stack.len() ==> valid_frame(#[trigger] stack@[j], self.blocks),
            decreases 15-root,
        {
            let number = bytes::read_le32(self.raw, 40 + root * 4).unwrap();
            if number != 0 {
                if result.metadata.len() >= node_budget { return Err(Error::Budget); }
                if !claim(&mut result.claims, number) { return Err(Error::Alias); }
                result.metadata.push(number);
                let (depth, start, stride) = if root == 12 { (1u8, 12u64, 1u64) }
                    else if root == 13 { (2u8, 12 + n, n) }
                    else { (3u8, 12 + n + square, square) };
                let ghost prior_stack = stack@;
                proof {
                    assert(number as nat == bytes::le32(self.raw@, 40+root as int*4));
                    assert(0 < number < self.blocks);
                    assert(valid_frame(Frame { number, depth, start, stride }, self.blocks));
                }
                stack.push(Frame { number, depth, start, stride });
                proof {
                    assert forall|j: int| 0 <= j < stack.len() implies
                        valid_frame(#[trigger] stack@[j], self.blocks) by {
                        if j < prior_stack.len() { assert(stack@[j] == prior_stack[j]); }
                    }
                }
            }
            root += 1;
        }
        while stack.len() > 0
            invariant self.wf(), data_budget <= 65536, node_budget <= 65536,
                256 <= n <= 16384, n == self.block_bytes as u64/4, square == n*n <= 268435456,
                result.data.len() <= data_budget, result.metadata.len() <= node_budget,
                result.claims.len() == result.data.len()+result.metadata.len(), unique(result.claims@),
                stack.len() <= result.metadata.len(),
                forall|j: int| 0 <= j < stack.len() ==> valid_frame(#[trigger] stack@[j], self.blocks),
            decreases node_budget as int-result.metadata.len() as int+stack.len() as int,
        {
            let frame = stack.pop().unwrap();
            let block = match source_block::capture(source, frame.number as u64, self.block_bytes) {
                Some(block) => block, None => { return Err(Error::Source); }
            };
            let ghost work = node_budget as int-result.metadata.len() as int+stack.len() as int;
            let mut at = 0usize;
            while at < self.block_bytes as usize / 4
                invariant self.wf(), at <= self.block_bytes as usize/4, data_budget <= 65536, node_budget <= 65536,
                    256 <= n <= 16384, n == self.block_bytes as u64/4, square == n*n <= 268435456,
                    result.data.len() <= data_budget, result.metadata.len() <= node_budget,
                    result.claims.len() == result.data.len()+result.metadata.len(), unique(result.claims@),
                    stack.len() < result.metadata.len(), valid_frame(frame, self.blocks),
                    forall|j: int| 0 <= j < stack.len() ==> valid_frame(#[trigger] stack@[j], self.blocks),
                    block.wf(), block.view().size == self.block_bytes,
                    node_budget as int-result.metadata.len() as int+stack.len() as int == work,
                decreases self.block_bytes as usize/4-at,
            {
                let number = bytes::read_le32(block.raw(), at * 4).unwrap();
                if number != 0 {
                    if number as u64 >= self.blocks { return Err(Error::OutOfRange); }
                    proof {
                        assert(frame.start as nat + at as nat * frame.stride <= 4398046511104nat + 4294967295nat)
                            by (nonlinear_arith)
                            requires frame.start <= 4294967295, at <= 16384, frame.stride <= 268435456;
                    }
                    let logical = frame.start + at as u64 * frame.stride;
                    if logical > 4294967295 { return Err(Error::OutOfRange); }
                    if !claim(&mut result.claims, number) { return Err(Error::Alias); }
                    if frame.depth == 1 {
                        if result.data.len() >= data_budget { return Err(Error::Budget); }
                        result.data.push(DataBlock { logical, physical: number });
                    } else {
                        if result.metadata.len() >= node_budget { return Err(Error::Budget); }
                        result.metadata.push(number);
                        stack.push(Frame { number, depth: frame.depth - 1, start: logical,
                            stride: frame.stride / n });
                    }
                }
                at += 1;
            }
        }
        Ok(result)
    }
}

pub struct DataBlock { pub logical: u64, pub physical: u32 }
pub struct Collection { pub data: Vec<DataBlock>, pub metadata: Vec<u32>, claims: Vec<u32> }
pub struct CollectionView { pub data: Seq<DataBlock>, pub metadata: Seq<u32>, pub claims: Seq<u32> }
impl Collection {
    pub closed spec fn view(&self) -> CollectionView {
        CollectionView { data: self.data@, metadata: self.metadata@, claims: self.claims@ }
    }
}
struct Frame { number: u32, depth: u8, start: u64, stride: u64 }
spec fn valid_frame(f: Frame, blocks: u64) -> bool {
    0 < f.number < blocks && 1 <= f.depth <= 3 && f.start <= 4294967295 && f.stride <= 268435456
}

fn claim(claims: &mut Vec<u32>, number: u32) -> (r: bool)
    requires unique(old(claims)@), old(claims).len() < usize::MAX,
    ensures if r { final(claims)@ == old(claims)@.push(number) && unique(final(claims)@)
            && !old(claims)@.contains(number) }
        else { final(claims)@ == old(claims)@ && old(claims)@.contains(number) },
{
    let mut i = 0usize;
    while i < claims.len()
        invariant i <= claims.len(), claims@ == old(claims)@, unique(claims@),
            forall|j: int| 0 <= j < i ==> #[trigger] claims@[j] != number,
        decreases claims.len()-i,
    {
        if claims[i] == number { return false; }
        i += 1;
    }
    claims.push(number);
    true
}

}
