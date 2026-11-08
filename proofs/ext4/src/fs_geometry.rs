// SPDX-License-Identifier: MPL-2.0

//! Numeric ext4 filesystem geometry and checked byte/sector placements.
//! These values describe 1--64 KiB blocks in a bounded partition. They grant
//! no source coherence, allocation, CortenMM frame, device or write authority.
//! Sector size 512 is an addressing unit, never an atomicity premise.

use vstd::prelude::*;
use crate::block_size;

verus! {

pub const ADDRESS_SECTOR_BYTES: u32 = 512;
pub const QUOTA_BLOCK_BYTES: u32 = 1024;

#[verifier::ext_equal]
pub struct GeometryView {
    pub block_bytes: u32,
    pub filesystem_blocks: u64,
    pub partition_bytes: u64,
}

pub open spec fn admitted(v: GeometryView) -> bool {
    &&& block_size::accepted(v.block_bytes as nat)
    &&& v.filesystem_blocks > 0
    &&& v.filesystem_blocks as nat * v.block_bytes as nat <= v.partition_bytes
}
pub open spec fn byte_begin(v: GeometryView, block: u64) -> nat {
    block as nat * v.block_bytes as nat
}
pub open spec fn byte_limit(v: GeometryView, block: u64) -> nat {
    (block as nat + 1) * v.block_bytes as nat
}
pub open spec fn sector_begin(v: GeometryView, block: u64) -> nat {
    byte_begin(v, block) / 512
}
pub open spec fn sector_limit(v: GeometryView, block: u64) -> nat {
    byte_limit(v, block) / 512
}
pub open spec fn byte_projection(v: GeometryView, block: u64) -> Option<(u64, u64)> {
    if admitted(v) && block < v.filesystem_blocks {
        Some((byte_begin(v, block) as u64, byte_limit(v, block) as u64))
    } else { None }
}
pub open spec fn sector_projection(v: GeometryView, block: u64) -> Option<(u64, u64)> {
    if admitted(v) && block < v.filesystem_blocks {
        Some((sector_begin(v, block) as u64, sector_limit(v, block) as u64))
    } else { None }
}
// Bounds only the addressable complete-sector prefix. A trailing partial
// sector in partition_bytes is not claimed to fit the parent byte range.
pub open spec fn parent_partition_fits(v: GeometryView, origin: u64, device_sectors: u64) -> bool {
    origin as nat + v.partition_bytes as nat / 512 <= device_sectors
}
pub open spec fn partition_projection(v: GeometryView, block: u64,
    origin: u64, device_sectors: u64) -> Option<(u64, u64)>
{
    if admitted(v) && block < v.filesystem_blocks && parent_partition_fits(v, origin, device_sectors) {
        Some(((origin as nat + sector_begin(v, block)) as u64,
            (origin as nat + sector_limit(v, block)) as u64))
    } else { None }
}
pub open spec fn primary_projection(v: GeometryView) -> Option<(u64, u32)> {
    if admitted(v) && 2048 <= v.filesystem_blocks as nat * v.block_bytes as nat {
        Some(((1024nat / v.block_bytes as nat) as u64,
            (1024nat % v.block_bytes as nat) as u32))
    } else { None }
}
pub open spec fn quota_span_fits(quota_block: u64) -> bool {
    (quota_block as nat + 1) * 1024 <= u64::MAX
}
pub open spec fn quota_projection(v: GeometryView, quota_block: u64) -> Option<(u64, u32)> {
    if admitted(v) && quota_span_fits(quota_block) {
        let ratio = v.block_bytes as nat / 1024;
        Some(((quota_block as nat / ratio) as u64,
            ((quota_block as nat % ratio) * 1024) as u32))
    } else { None }
}

// The same numerical shape used by an exact DMA slice. This is a guard,
// not a proof that a buffer is owned, mapped, initialized or quiescent.
pub open spec fn buffer_range_admission(buffer_bytes: nat, start: nat, end: nat) -> bool {
    start < end && end <= buffer_bytes && start % 512 == 0 && end % 512 == 0
}
pub open spec fn buffer_sector_projection(buffer_bytes: nat, start: nat, end: nat)
    -> Option<(nat, nat)>
{
    if buffer_range_admission(buffer_bytes, start, end) {
        Some((start / 512, end / 512))
    } else { None }
}
proof fn aligned_buffer_difference(start: nat, end: nat)
    requires start < end, start % 512 == 0, end % 512 == 0,
    ensures start / 512 < end / 512,
        (end - start) as nat % 512 == 0,
        (end - start) as nat == (end / 512 - start / 512) as nat * 512,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(start as int, 512);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(end as int, 512);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(start as int, end as int, 512);
    assert(start / 512 < end / 512);
    assert((end - start) as nat == (end / 512 - start / 512) as nat * 512) by(nonlinear_arith)
        requires start == (start / 512) * 512, end == (end / 512) * 512, start < end;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_mod(
        end as int - start as int, 512, end as int / 512 - start as int / 512, 0);
}
pub fn validated_buffer_range(buffer_bytes: usize, start: usize, end: usize) -> (r: bool)
    ensures r == buffer_range_admission(buffer_bytes as nat, start as nat, end as nat),
        r ==> 0 < end as nat - start as nat <= buffer_bytes,
        r ==> (end as nat - start as nat) as nat % 512 == 0,
{
    let valid = start < end && end <= buffer_bytes && start % 512 == 0 && end % 512 == 0;
    proof { if valid { aligned_buffer_difference(start as nat, end as nat); } }
    valid
}
pub fn buffer_sector_range(buffer_bytes: usize, start: usize, end: usize)
    -> (r: Option<(usize, usize)>)
    ensures match r {
        Some((first, last)) => buffer_range_admission(buffer_bytes as nat, start as nat, end as nat)
            && buffer_sector_projection(buffer_bytes as nat, start as nat, end as nat)
                == Some((first as nat, last as nat))
            && first < last && last <= buffer_bytes / 512
            && (last as nat - first as nat) * 512 == end as nat - start as nat,
        None => !buffer_range_admission(buffer_bytes as nat, start as nat, end as nat),
    },
{
    if !validated_buffer_range(buffer_bytes, start, end) { return None; }
    proof {
        aligned_buffer_difference(start as nat, end as nat);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(end as int, buffer_bytes as int, 512);
    }
    Some((start / 512, end / 512))
}

proof fn accepted_size_facts(size: u32)
    requires block_size::accepted(size as nat),
    ensures 1024 <= size <= 65536, size % 512 == 0, size % 1024 == 0,
        2 <= size / 512 <= 128, 1 <= size / 1024 <= 64,
        size as nat == (size / 512) as nat * 512,
        size as nat == (size / 1024) as nat * 1024,
{
}
proof fn quotient_product_bound(length: u64, size: u32, count: u64)
    requires size > 0,
    ensures (count as nat * size as nat <= length)
        <==> (count <= length / size as u64),
{
    let q = length as int / size as int;
    let r = length as int % size as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(length as int, size as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(q, size as int);
    if count as int <= q {
        vstd::arithmetic::mul::lemma_mul_inequality(count as int, q, size as int);
    } else {
        vstd::arithmetic::mul::lemma_mul_inequality(q + 1, count as int, size as int);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(size as int, q, 1);
    }
}
proof fn scale_sector_exact(number: nat, size: u32)
    requires block_size::accepted(size as nat),
    ensures number * size as nat / 512 == number * (size / 512) as nat,
        number * size as nat % 512 == 0,
{
    accepted_size_facts(size);
    assert(number * size as nat == (number * (size / 512) as nat) * 512) by(nonlinear_arith)
        requires size as nat == (size / 512) as nat * 512;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_div(
        number as int * size as int, 512, number as int * (size / 512) as int, 0);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_mod(
        number as int * size as int, 512, number as int * (size / 512) as int, 0);
}
proof fn block_projection_bounds(v: GeometryView, block: u64)
    requires admitted(v), block < v.filesystem_blocks,
    ensures byte_begin(v, block) + v.block_bytes as nat == byte_limit(v, block),
        byte_begin(v, block) < byte_limit(v, block) <= v.partition_bytes,
        sector_begin(v, block) < sector_limit(v, block) <= v.partition_bytes as nat / 512,
        sector_limit(v, block) == sector_begin(v, block) + (v.block_bytes / 512) as nat,
{
    accepted_size_facts(v.block_bytes);
    vstd::arithmetic::mul::lemma_mul_inequality(
        block as int + 1, v.filesystem_blocks as int, v.block_bytes as int);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
        v.block_bytes as int, block as int, 1);
    scale_sector_exact(block as nat, v.block_bytes);
    scale_sector_exact(block as nat + 1, v.block_bytes);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
        (v.block_bytes / 512) as int, block as int, 1);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(
        byte_limit(v, block) as int, v.partition_bytes as int, 512);
}
proof fn primary_placement_facts(v: GeometryView)
    requires admitted(v),
    ensures
        (2048 <= v.filesystem_blocks as nat * v.block_bytes as nat)
            <==> (1024nat / (v.block_bytes as nat) < v.filesystem_blocks),
        (1024nat % v.block_bytes as nat) + 1024 <= v.block_bytes,
        (1024nat / v.block_bytes as nat) * v.block_bytes as nat
            + 1024nat % v.block_bytes as nat == 1024,
{
    accepted_size_facts(v.block_bytes);
    if v.block_bytes == 1024 {
        assert(1024nat / v.block_bytes as nat == 1);
        if v.filesystem_blocks == 1 {
            assert(v.filesystem_blocks as nat * v.block_bytes as nat == 1024);
        } else {
            assert(v.filesystem_blocks >= 2);
            vstd::arithmetic::mul::lemma_mul_inequality(2,v.filesystem_blocks as int,1024);
            assert(2048 <= v.filesystem_blocks as nat * v.block_bytes as nat);
        }
    } else {
        assert(v.block_bytes >= 2048);
        assert(1024nat / v.block_bytes as nat == 0);
        assert(v.filesystem_blocks >= 1);
        vstd::arithmetic::mul::lemma_mul_inequality(1,v.filesystem_blocks as int,v.block_bytes as int);
        assert(2048 <= v.filesystem_blocks as nat * v.block_bytes as nat);
    }
}
proof fn quota_placement_facts(v: GeometryView, quota_block: u64)
    requires admitted(v),
    ensures {
        let ratio = v.block_bytes as nat / 1024;
        let logical = quota_block as nat / ratio;
        let within = (quota_block as nat % ratio) * 1024;
        &&& logical <= quota_block
        &&& within + 1024 <= v.block_bytes
        &&& within % 1024 == 0
        &&& logical * v.block_bytes as nat + within == quota_block as nat * 1024
    },
{
    accepted_size_facts(v.block_bytes);
    let size=v.block_bytes as int;
    let number=quota_block as int;
    let ratio=size/1024;
    let logical=number/ratio;
    let remainder=number%ratio;
    let within=remainder*1024;
    assert(1<=ratio<=64);
    assert(size%1024==0);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(size,1024);
    assert(size==ratio*1024);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(number,ratio);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(number,ratio);
    vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(number,1,ratio);
    vstd::arithmetic::mul::lemma_mul_is_commutative(logical,ratio);
    assert(number==ratio*logical+remainder);
    assert(0<=remainder<ratio);
    assert(logical==(quota_block as nat/(v.block_bytes as nat/1024)) as int);
    assert(remainder==(quota_block as nat%(v.block_bytes as nat/1024)) as int);
    assert(logical*size+within==number*1024) by(nonlinear_arith)
        requires number==ratio*logical+remainder,size==ratio*1024,within==remainder*1024;
    assert(remainder+1<=ratio);
    vstd::arithmetic::mul::lemma_mul_inequality(remainder+1,ratio,1024);
    assert(within+1024<=size);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_mod(within,1024,remainder,0);
}

pub struct FsGeometry {
    block_bytes: u32,
    filesystem_blocks: u64,
    partition_bytes: u64,
}
impl FsGeometry {
    pub closed spec fn view(&self) -> GeometryView {
        GeometryView { block_bytes: self.block_bytes, filesystem_blocks: self.filesystem_blocks,
            partition_bytes: self.partition_bytes }
    }
    pub open spec fn wf(&self) -> bool { admitted(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn new(block_bytes: u32, filesystem_blocks: u64, partition_bytes: u64) -> (r: Option<Self>)
        ensures match r {
            Some(g) => g.wf() && g.view() == (GeometryView { block_bytes, filesystem_blocks, partition_bytes }),
            None => !admitted(GeometryView { block_bytes, filesystem_blocks, partition_bytes }),
        },
    {
        if !block_size::valid(block_bytes as usize) || filesystem_blocks == 0 { return None; }
        proof {
            accepted_size_facts(block_bytes);
            quotient_product_bound(partition_bytes, block_bytes, filesystem_blocks);
        }
        if filesystem_blocks > partition_bytes / block_bytes as u64 { return None; }
        Some(FsGeometry { block_bytes, filesystem_blocks, partition_bytes })
    }
    pub fn block_bytes(&self) -> (r: u32) ensures self.wf(), r == self.view().block_bytes {
        proof { use_type_invariant(self); }
        self.block_bytes
    }
    pub fn filesystem_blocks(&self) -> (r: u64) ensures self.wf(), r == self.view().filesystem_blocks {
        proof { use_type_invariant(self); }
        self.filesystem_blocks
    }
    pub fn partition_bytes(&self) -> (r: u64) ensures self.wf(), r == self.view().partition_bytes {
        proof { use_type_invariant(self); }
        self.partition_bytes
    }
    pub fn partition_sectors(&self) -> (r: u64)
        ensures self.wf(), r as nat == self.view().partition_bytes as nat / 512,
    {
        proof { use_type_invariant(self); }
        self.partition_bytes / 512
    }
    pub fn duplicate(&self) -> (r: Self) ensures self.wf(), r.wf(), r.view() == self.view() {
        proof { use_type_invariant(self); }
        Self { block_bytes: self.block_bytes, filesystem_blocks: self.filesystem_blocks,
            partition_bytes: self.partition_bytes }
    }
    pub fn byte_range(&self, block: u64) -> (r: Option<(u64, u64)>)
        ensures self.wf(), r == byte_projection(self.view(), block),
            r.is_some() <==> block < self.view().filesystem_blocks,
            match r { Some((start, end)) => start < end && end <= self.view().partition_bytes
                && start as nat == block as nat * self.view().block_bytes as nat
                && end as nat == start as nat + self.view().block_bytes as nat,
                None => true },
    {
        proof { use_type_invariant(self); }
        if block >= self.filesystem_blocks { return None; }
        proof { block_projection_bounds(self.view(), block); }
        let start = match block.checked_mul(self.block_bytes as u64) { Some(v) => v, None => return None };
        let end = match start.checked_add(self.block_bytes as u64) { Some(v) => v, None => return None };
        Some((start, end))
    }
    pub fn sector_range(&self, block: u64) -> (r: Option<(u64, u64)>)
        ensures self.wf(), r == sector_projection(self.view(), block),
            r.is_some() <==> block < self.view().filesystem_blocks,
            match r { Some((start, end)) => start < end
                && end as nat <= self.view().partition_bytes as nat / 512
                && end as nat == start as nat + (self.view().block_bytes / 512) as nat,
                None => true },
    {
        proof { use_type_invariant(self); }
        let (start, end) = self.byte_range(block)?;
        proof { block_projection_bounds(self.view(), block); }
        Some((start / 512, end / 512))
    }
    /// Translates complete filesystem blocks within the complete-sector prefix.
    pub fn partition_sector_range(&self, block: u64, origin_sectors: u64, device_sectors: u64)
        -> (r: Option<(u64, u64)>)
        ensures self.wf(), r == partition_projection(self.view(), block, origin_sectors, device_sectors),
            r.is_some() <==> (block < self.view().filesystem_blocks
                && parent_partition_fits(self.view(), origin_sectors, device_sectors)),
            match r { Some((start, end)) => origin_sectors <= start < end <= device_sectors,
                None => true },
    {
        proof { use_type_invariant(self); }
        let length = self.partition_bytes / 512;
        if origin_sectors > device_sectors || length > device_sectors - origin_sectors { return None; }
        let (start, end) = self.sector_range(block)?;
        let start = match origin_sectors.checked_add(start) { Some(v) => v, None => return None };
        let end = match origin_sectors.checked_add(end) { Some(v) => v, None => return None };
        Some((start, end))
    }
    /// Returns the full 1024-byte primary-superblock placement when it fits.
    pub fn primary_superblock(&self) -> (r: Option<(u64, u32)>)
        ensures self.wf(), r == primary_projection(self.view()),
            match r { Some((block, within)) => block < self.view().filesystem_blocks
                && within as nat + 1024 <= self.view().block_bytes
                && block as nat * self.view().block_bytes as nat + within as nat == 1024,
                None => self.view().filesystem_blocks as nat * (self.view().block_bytes as nat) < 2048 },
    {
        proof { use_type_invariant(self); primary_placement_facts(self.view()); }
        let block = 1024u64 / self.block_bytes as u64;
        let within = 1024u32 % self.block_bytes;
        if block >= self.filesystem_blocks { return None; }
        Some((block, within))
    }
    /// Describes quota-file logical placement; it is not a physical mapping.
    pub fn quota_placement(&self, quota_block: u64) -> (r: Option<(u64, u32)>)
        ensures self.wf(), r == quota_projection(self.view(), quota_block),
            r.is_some() <==> quota_span_fits(quota_block),
            match r { Some((logical, within)) => within as nat + 1024 <= self.view().block_bytes
                && within % 1024 == 0
                && logical as nat * self.view().block_bytes as nat + within as nat == quota_block as nat * 1024,
                None => true },
    {
        proof { use_type_invariant(self); quota_placement_facts(self.view(), quota_block); }
        let start = match quota_block.checked_mul(1024) { Some(v) => v, None => return None };
        let _end = match start.checked_add(1024) { Some(v) => v, None => return None };
        let ratio = (self.block_bytes / 1024) as u64;
        let logical = quota_block / ratio;
        let within = ((quota_block % ratio) * 1024) as u32;
        Some((logical, within))
    }
}

pub proof fn distinct_blocks_have_disjoint_byte_and_sector_ranges(v: GeometryView, first: u64, second: u64)
    requires admitted(v), first < second < v.filesystem_blocks,
    ensures byte_limit(v, first) <= byte_begin(v, second),
        sector_limit(v, first) <= sector_begin(v, second),
        byte_projection(v, first).is_some(), byte_projection(v, second).is_some(),
        sector_projection(v, first).is_some(), sector_projection(v, second).is_some(),
{
    block_projection_bounds(v, first); block_projection_bounds(v, second);
    vstd::arithmetic::mul::lemma_mul_inequality(first as int + 1, second as int, v.block_bytes as int);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(
        byte_limit(v, first) as int, byte_begin(v, second) as int, 512);
}
pub proof fn partition_translation_preserves_disjoint_ranges(v: GeometryView, first: u64, second: u64,
    origin: u64, device_sectors: u64)
    requires admitted(v), first < second < v.filesystem_blocks,
        parent_partition_fits(v, origin, device_sectors),
    ensures partition_projection(v, first, origin, device_sectors).is_some(),
        partition_projection(v, second, origin, device_sectors).is_some(),
        partition_projection(v, first, origin, device_sectors).unwrap().1
            <= partition_projection(v, second, origin, device_sectors).unwrap().0,
{
    distinct_blocks_have_disjoint_byte_and_sector_ranges(v, first, second);
    block_projection_bounds(v, first); block_projection_bounds(v, second);
}
pub proof fn legacy_4096_byte_and_sector_projections_are_exact(v: GeometryView, block: u32)
    requires admitted(v), v.block_bytes == 4096, v.filesystem_blocks <= u32::MAX,
    ensures byte_projection(v, block as u64)
        == if (block as u64) < v.filesystem_blocks {
            Some(((block as u64 * 4096) as u64, ((block as u64 + 1) * 4096) as u64))
        } else { None },
        sector_projection(v, block as u64)
        == if (block as u64) < v.filesystem_blocks {
            Some(((block as u64 * 8) as u64, ((block as u64 + 1) * 8) as u64))
        } else { None },
{
    if (block as u64) < v.filesystem_blocks {
        scale_sector_exact(block as nat, 4096);
        scale_sector_exact(block as nat + 1, 4096);
    }
}
pub proof fn legacy_4096_primary_and_quota_placements_are_exact(v: GeometryView, quota_block: u64)
    requires admitted(v), v.block_bytes == 4096,
    ensures primary_projection(v) == Some((0u64, 1024u32)),
        quota_projection(v, quota_block)
            == if quota_span_fits(quota_block) {
                Some(((quota_block / 4) as u64, ((quota_block % 4) * 1024) as u32))
            } else { None },
{
    primary_placement_facts(v);
    quota_placement_facts(v, quota_block);
}

}
