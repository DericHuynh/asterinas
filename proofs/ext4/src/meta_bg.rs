// SPDX-License-Identifier: MPL-2.0

//! Linux ext4 distributed group-descriptor and reserved-GDT coordinates.
//! Addresses are filesystem blocks, not frames or I/O capabilities. These
//! helpers do not admit a filesystem or activate META_BG/RESIZE_INODE.

use vstd::prelude::*;
use crate::bytes;

verus! {

pub const META_BG: u32 = 0x10;
pub const BIT64: u32 = 0x80;
pub const BIGALLOC: u32 = 0x200;
pub const MAX_COPIES: usize = 4096;

#[derive(Clone, Copy)]
pub struct Geometry {
    pub blocks: u64,
    pub first_data: u64,
    pub blocks_per_group: u32,
    pub groups: u32,
    pub block_bytes: u32,
    pub descriptor_bytes: u32,
    pub cluster_ratio: u32,
    pub bigalloc: bool,
    pub meta_bg: bool,
    pub first_meta_bg: u32,
    pub resize_inode: bool,
    pub reserved_gdt: u16,
    pub sparse_super: bool,
    pub sparse_super2: bool,
    pub backup0: u32,
    pub backup1: u32,
}

#[derive(Clone, Copy)]
pub struct DescriptorAddress { pub block: u64, pub offset: u32 }

#[derive(Clone, Copy)]
pub struct DescriptorCopy { pub group: u32, pub block: u64, pub primary: bool }

#[derive(Debug, PartialEq, Eq)]
pub enum Error { Geometry, Group, Descriptor, Overflow, Outside, Capacity, Reservation }

// Thirty-two exact divisions cover every representable u32 power for base>=2.
// The explicit rank makes both the executable and pure definitions total.
pub open spec fn power_steps(value: u32, base: u32, fuel: u8) -> bool
    decreases fuel,
{
    value == 1 || (fuel > 0 && base >= 2 && value > 1 && value % base == 0
        && power_steps(value / base, base, (fuel - 1) as u8))
}

pub open spec fn power(value: u32, base: u32) -> bool { power_steps(value, base, 32) }

fn power_checked(value: u32, base: u32, fuel: u8) -> (r: bool)
    ensures r == power_steps(value, base, fuel),
    decreases fuel,
{
    if value == 1 { return true; }
    if fuel == 0 || value == 0 || base < 2 || value % base != 0 { return false; }
    power_checked(value / base, base, fuel - 1)
}

fn is_power(value: u32, base: u32) -> (r: bool)
    ensures r == power(value, base),
{ power_checked(value, base, 32) }

pub open spec fn has_super_spec(g: Geometry, group: u32) -> bool {
    group == 0 || if g.sparse_super2 {
        group == g.backup0 || group == g.backup1
    } else if !g.sparse_super || group == 1 {
        true
    } else {
        group % 2 == 1 && (power(group, 3) || power(group, 5) || power(group, 7))
    }
}

pub open spec fn valid(g: Geometry) -> bool {
    &&& g.blocks > g.first_data
    &&& g.blocks_per_group > 0 && g.groups > 0
    &&& (g.block_bytes == 1024 || g.block_bytes == 2048 || g.block_bytes == 4096
        || g.block_bytes == 8192 || g.block_bytes == 16384 || g.block_bytes == 32768 || g.block_bytes == 65536)
    &&& (g.descriptor_bytes == 32 || g.descriptor_bytes == 64 || g.descriptor_bytes == 128
        || g.descriptor_bytes == 256 || g.descriptor_bytes == 512 || g.descriptor_bytes == 1024)
    &&& g.descriptor_bytes <= g.block_bytes
    &&& 0 < g.cluster_ratio <= 1048576 && g.cluster_ratio & ((g.cluster_ratio - 1) as u32) == 0
    &&& g.block_bytes as nat * g.cluster_ratio <= 1073741824
    &&& (!g.bigalloc ==> g.cluster_ratio == 1)
    &&& (g.bigalloc ==> g.first_data == 0)
    &&& (g.block_bytes == 1024 && g.cluster_ratio == 1 ==> g.first_data != 0)
    &&& g.blocks_per_group % g.cluster_ratio == 0
    &&& g.blocks_per_group as nat / (g.cluster_ratio as nat) <= g.block_bytes as nat * 8
    &&& g.groups as nat == (g.blocks as nat - g.first_data) / (g.blocks_per_group as int)
        + if (g.blocks as nat - g.first_data) % (g.blocks_per_group as int) == 0 { 0nat } else { 1nat }
    &&& (!g.meta_bg || (g.first_meta_bg as nat) <= (g.groups as nat + (g.block_bytes / g.descriptor_bytes) - 1)
        / ((g.block_bytes / g.descriptor_bytes) as int))
}


pub proof fn geometry_facts(g: Geometry)
    requires valid(g),
    ensures 1 <= g.descriptor_bytes <= g.block_bytes <= 65536,
        1 <= g.block_bytes / g.descriptor_bytes <= 2048,
        g.block_bytes % g.descriptor_bytes == 0,
        (g.block_bytes / g.descriptor_bytes) as nat * g.descriptor_bytes == g.block_bytes,
        0 < g.blocks_per_group, 0 < g.cluster_ratio,
{
    assert(1 <= g.block_bytes / g.descriptor_bytes <= 2048) by (nonlinear_arith)
        requires 32 <= g.descriptor_bytes <= g.block_bytes <= 65536;
    assert(g.block_bytes % g.descriptor_bytes == 0) by (nonlinear_arith)
        requires (g.block_bytes == 1024 || g.block_bytes == 2048 || g.block_bytes == 4096
            || g.block_bytes == 8192 || g.block_bytes == 16384 || g.block_bytes == 32768 || g.block_bytes == 65536),
            (g.descriptor_bytes == 32 || g.descriptor_bytes == 64 || g.descriptor_bytes == 128
            || g.descriptor_bytes == 256 || g.descriptor_bytes == 512 || g.descriptor_bytes == 1024);
}

proof fn product_fits(a: u32, b: u32)
    ensures a as nat * b as nat <= 18446744073709551615,
{
    assert(a as nat * b as nat <= 18446744073709551615) by (nonlinear_arith);
}

pub open spec fn descriptors(g: Geometry) -> nat {
    if g.descriptor_bytes == 0 || g.block_bytes < g.descriptor_bytes { 0nat }
    else {
        let per = (g.block_bytes / g.descriptor_bytes) as nat;
        (g.groups as nat + per - 1) as nat / per
    }
}

pub open spec fn source_fields(g: Geometry, raw: Seq<u8>) -> bool {
    &&& raw.len() == 1024
    &&& bytes::le32(raw, 24) <= 6 && bytes::le32(raw, 24) <= bytes::le32(raw, 28) <= 20
    &&& g.block_bytes == 1024u32 << (bytes::le32(raw, 24) as u32)
    &&& g.cluster_ratio == 1u32 << ((bytes::le32(raw, 28) - bytes::le32(raw, 24)) as u32)
    &&& g.blocks as nat == bytes::le32(raw, 4) + if bytes::le32(raw, 96) as u32 & BIT64 != 0 {
        bytes::le32(raw, 336) * 4294967296
    } else { 0nat }
    &&& g.first_data as nat == bytes::le32(raw, 20)
    &&& g.blocks_per_group as nat == bytes::le32(raw, 32)
    &&& g.descriptor_bytes as nat == if bytes::le32(raw, 96) as u32 & BIT64 != 0 {
        bytes::le16(raw, 254)
    } else { 32nat }
    &&& g.bigalloc == (bytes::le32(raw, 100) as u32 & BIGALLOC != 0)
    &&& g.meta_bg == (bytes::le32(raw, 96) as u32 & META_BG != 0)
    &&& g.first_meta_bg as nat == bytes::le32(raw, 260)
    &&& g.resize_inode == (bytes::le32(raw, 92) as u32 & 0x10u32 != 0)
    &&& g.reserved_gdt as nat == bytes::le16(raw, 206)
    &&& g.sparse_super == (bytes::le32(raw, 100) as u32 & 1u32 != 0)
    &&& g.sparse_super2 == (bytes::le32(raw, 92) as u32 & 0x200u32 != 0)
    &&& g.backup0 as nat == bytes::le32(raw, 588) && g.backup1 as nat == bytes::le32(raw, 592)
}

pub open spec fn first_block(g: Geometry, group: u32) -> nat {
    g.first_data as nat + group as nat * g.blocks_per_group as nat
}

pub open spec fn descriptor_location(g: Geometry, logical_super: u64, number: u32) -> nat {
    if !g.meta_bg || number < g.first_meta_bg { logical_super as nat + number as nat + 1 }
    else {
        let per = if g.descriptor_bytes > 0 { g.block_bytes / g.descriptor_bytes } else { 0u32 };
        let group = (per as nat * number as nat) as u32;
        first_block(g, group) + if has_super_spec(g, group) { 1nat } else { 0nat }
            + if g.block_bytes == 1024 && number == 0 && g.first_data == 0 { 1nat } else { 0nat }
    }
}

pub open spec fn num_gdb(g: Geometry, group: u32) -> nat {
    if g.descriptor_bytes == 0 || g.block_bytes < g.descriptor_bytes { 0nat }
    else {
        let per = g.block_bytes / g.descriptor_bytes;
        if !g.meta_bg || group / per < g.first_meta_bg {
            if has_super_spec(g, group) {
                if g.meta_bg { g.first_meta_bg as nat } else { descriptors(g) }
            } else { 0nat }
        } else {
            let offset = group % per;
            if offset == 0 || offset == 1 || offset as nat + 1 == per { 1nat } else { 0nat }
        }
    }
}

pub open spec fn base_blocks(g: Geometry, group: u32) -> nat {
    num_gdb(g, group) + if has_super_spec(g, group) { 1nat } else { 0nat }
        + if g.descriptor_bytes > 0 && g.block_bytes >= g.descriptor_bytes
            && (!g.meta_bg || group / (g.block_bytes / g.descriptor_bytes) < g.first_meta_bg)
            && has_super_spec(g, group) { g.reserved_gdt as nat } else { 0nat }
}

pub open spec fn copy_ok(g: Geometry, logical_super: u64, number: u32, copy: DescriptorCopy) -> bool {
    &&& copy.group < g.groups && copy.block < g.blocks
    &&& if copy.primary {
        copy.block as nat == descriptor_location(g, logical_super, number)
            && copy.group == if g.meta_bg && number >= g.first_meta_bg {
                (number as nat * (g.block_bytes / g.descriptor_bytes) as nat) as u32
            } else { 0u32 }
    }
        else if g.meta_bg && number >= g.first_meta_bg {
            let first = number as nat * (g.block_bytes / g.descriptor_bytes) as nat;
            &&& (copy.group as nat == first + 1
                || copy.group as nat + 1 == first + (g.block_bytes / g.descriptor_bytes) as nat)
            &&& copy.block as nat == first_block(g, copy.group) + if has_super_spec(g, copy.group) { 1nat } else { 0nat }
        } else {
            has_super_spec(g, copy.group)
                && copy.block as nat == first_block(g, copy.group) + number as nat + 1
        }
}

pub fn is_valid(g: Geometry) -> (r: bool)
    ensures r == valid(g),
{
    if g.blocks <= g.first_data || g.blocks_per_group == 0 || g.groups == 0 { return false; }
    if g.block_bytes != 1024 && g.block_bytes != 2048 && g.block_bytes != 4096
        && g.block_bytes != 8192 && g.block_bytes != 16384 && g.block_bytes != 32768 && g.block_bytes != 65536 { return false; }
    if g.descriptor_bytes != 32 && g.descriptor_bytes != 64 && g.descriptor_bytes != 128
        && g.descriptor_bytes != 256 && g.descriptor_bytes != 512 && g.descriptor_bytes != 1024 { return false; }
    proof { product_fits(g.block_bytes, g.cluster_ratio); }
    if g.descriptor_bytes > g.block_bytes || g.cluster_ratio == 0 || g.cluster_ratio > 1048576
        || g.cluster_ratio & (g.cluster_ratio - 1) != 0
        || g.block_bytes as u64 * (g.cluster_ratio as u64) > 1073741824
        || (!g.bigalloc && g.cluster_ratio != 1)
        || (g.bigalloc && g.first_data != 0)
        || (g.block_bytes == 1024 && g.cluster_ratio == 1 && g.first_data == 0) { return false; }
    if g.blocks_per_group % g.cluster_ratio != 0
        || g.blocks_per_group / g.cluster_ratio > g.block_bytes * 8 { return false; }
    let span = g.blocks - g.first_data;
    let quotient = span / g.blocks_per_group as u64;
    let extra = if span % g.blocks_per_group as u64 == 0 { 0u64 } else { 1u64 };
    if quotient > 4294967295 || quotient + extra != g.groups as u64 { return false; }
    let per = g.block_bytes / g.descriptor_bytes;
    proof { assert(per > 0) by (nonlinear_arith)
        requires 0 < g.descriptor_bytes <= g.block_bytes,
            per as int == g.block_bytes as int / g.descriptor_bytes as int; }
    let descriptors = (g.groups as u64 + per as u64 - 1) / per as u64;
    !g.meta_bg || (g.first_meta_bg as u64) <= descriptors
}

/// Decode layout fields only. Checksums, feature combinations and physical
/// ownership still require their own source-bound admission.
pub fn parse(superblock: &[u8]) -> (r: Option<Geometry>)
    ensures match r { Some(g) => valid(g) && source_fields(g, superblock@), None => true },
{
    if superblock.len() != 1024 || bytes::read_le16(superblock, 56).unwrap() != 0xef53 { return None; }
    let log_block = bytes::read_le32(superblock, 24).unwrap();
    let log_cluster = bytes::read_le32(superblock, 28).unwrap();
    if log_block > 6 || log_cluster > 20 || log_cluster < log_block { return None; }
    let block_bytes = 1024u32 << log_block;
    let incompat = bytes::read_le32(superblock, 96).unwrap();
    let compat = bytes::read_le32(superblock, 92).unwrap();
    let ro = bytes::read_le32(superblock, 100).unwrap();
    let bigalloc = ro & BIGALLOC != 0;
    if !bigalloc && log_cluster != log_block { return None; }
    let cluster_ratio = 1u32 << (log_cluster - log_block);
    let descriptor_bytes = if incompat & BIT64 != 0 {
        bytes::read_le16(superblock, 254).unwrap() as u32
    } else { 32u32 };
    let low = bytes::read_le32(superblock, 4).unwrap() as u64;
    let high = if incompat & BIT64 != 0 { bytes::read_le32(superblock, 336).unwrap() as u64 } else { 0u64 };
    let blocks = low + high * 4294967296u64;
    let first_data = bytes::read_le32(superblock, 20).unwrap() as u64;
    let blocks_per_group = bytes::read_le32(superblock, 32).unwrap();
    let clusters_per_group = bytes::read_le32(superblock, 36).unwrap();
    proof { product_fits(clusters_per_group, cluster_ratio); }
    if blocks_per_group == 0 || blocks <= first_data
        || clusters_per_group as u64 * cluster_ratio as u64 != blocks_per_group as u64 { return None; }
    let span = blocks - first_data;
    let quotient = span / blocks_per_group as u64;
    let remainder = span % blocks_per_group as u64;
    if quotient > 4294967295 || (quotient == 4294967295 && remainder != 0) { return None; }
    let groups = (quotient + if remainder == 0 { 0u64 } else { 1u64 }) as u32;
    let geometry = Geometry {
        blocks, first_data, blocks_per_group, groups, block_bytes, descriptor_bytes,
        cluster_ratio, bigalloc, meta_bg: incompat & META_BG != 0,
        first_meta_bg: bytes::read_le32(superblock, 260).unwrap(),
        resize_inode: compat & 0x10 != 0,
        reserved_gdt: bytes::read_le16(superblock, 206).unwrap(),
        sparse_super: ro & 1 != 0, sparse_super2: compat & 0x200 != 0,
        backup0: bytes::read_le32(superblock, 588).unwrap(),
        backup1: bytes::read_le32(superblock, 592).unwrap(),
    };
    if !is_valid(geometry) { None } else { Some(geometry) }
}

pub fn has_super(g: Geometry, group: u32) -> (r: bool)
    ensures r == has_super_spec(g, group),
{
    if group == 0 { return true; }
    if g.sparse_super2 { return group == g.backup0 || group == g.backup1; }
    if group == 1 || !g.sparse_super { return true; }
    group % 2 == 1 && (is_power(group, 3) || is_power(group, 5) || is_power(group, 7))
}

pub fn group_first(g: Geometry, group: u32) -> (r: Option<u64>)
    ensures match r { Some(block) => valid(g) && group < g.groups
        && block as nat == first_block(g, group) && block < g.blocks, None => true },
{
    if !is_valid(g) || group >= g.groups { return None; }
    proof { product_fits(group, g.blocks_per_group); }
    let offset = group as u64 * g.blocks_per_group as u64;
    if offset > 18446744073709551615u64 - g.first_data { return None; }
    let block = g.first_data + offset;
    if block >= g.blocks { None } else { Some(block) }
}

pub fn descriptor_blocks(g: Geometry) -> (r: Option<u32>)
    ensures match r { Some(count) => valid(g) && 0 < count <= g.groups && count as nat == descriptors(g),
        None => !valid(g) },
{
    if !is_valid(g) { return None; }
    proof { geometry_facts(g); }
    let per = g.block_bytes / g.descriptor_bytes;
    let count = (g.groups as u64 + per as u64 - 1) / per as u64;
    proof { assert(0 < count <= g.groups) by (nonlinear_arith)
        requires g.groups > 0, per > 0,
            count as int == (g.groups as int + per as int - 1) / per as int; }
    Some(count as u32)
}

/// Mirrors Linux descriptor_loc, including the 1KiB META_BG group-zero
/// compensation when first_data_block is zero.
pub fn descriptor_block(g: Geometry, logical_super: u64, number: u32) -> (r: Option<u64>)
    ensures match r { Some(block) => valid(g) && number < descriptors(g)
        && logical_super < g.blocks && block < g.blocks
        && block as nat == descriptor_location(g, logical_super, number)
        && (g.meta_bg && number >= g.first_meta_bg ==>
            number as nat * (g.block_bytes / g.descriptor_bytes) < g.groups), None => true },
{
    let count = match descriptor_blocks(g) { Some(count) => count, None => { return None; } };
    if number >= count || logical_super >= g.blocks { return None; }
    if !g.meta_bg || number < g.first_meta_bg {
        if number as u64 + 1 > 18446744073709551615u64 - logical_super { return None; }
        let block = logical_super + number as u64 + 1;
        return if block < g.blocks { Some(block) } else { None };
    }
    proof { geometry_facts(g); product_fits(g.block_bytes / g.descriptor_bytes, number); }
    let per = g.block_bytes / g.descriptor_bytes;
    let group64 = per as u64 * number as u64;
    if group64 > 4294967295 { return None; }
    let group = group64 as u32;
    let first = match group_first(g, group) { Some(first) => first, None => { return None; } };
    let extra = if g.block_bytes == 1024 && number == 0 && g.first_data == 0 { 1u64 } else { 0u64 };
    let skip = if has_super(g, group) { 1u64 } else { 0u64 };
    if skip + extra > 18446744073709551615u64 - first { return None; }
    let block = first + skip + extra;
    if block < g.blocks { Some(block) } else { None }
}

pub fn locate(g: Geometry, logical_super: u64, group: u32) -> (r: Option<DescriptorAddress>)
    ensures match r { Some(address) => valid(g) && group < g.groups
        && address.block < g.blocks && address.offset as nat + g.descriptor_bytes <= g.block_bytes
        && address.offset == (group % (g.block_bytes / g.descriptor_bytes)) * g.descriptor_bytes
        && address.block as nat == descriptor_location(g, logical_super, group / (g.block_bytes / g.descriptor_bytes)),
        None => true },
{
    if !is_valid(g) || group >= g.groups { return None; }
    proof { geometry_facts(g); }
    let per = g.block_bytes / g.descriptor_bytes;
    let block = match descriptor_block(g, logical_super, group / per) {
        Some(block) => block, None => { return None; },
    };
    proof { assert((group % per) as nat * g.descriptor_bytes + g.descriptor_bytes <= g.block_bytes) by (nonlinear_arith)
        requires per > 0, (group % per) < per,
            per as nat * g.descriptor_bytes == g.block_bytes; }
    Some(DescriptorAddress { block, offset: (group % per) * g.descriptor_bytes })
}

/// Number returned by Linux ext4_bg_num_gdb for this group.
pub fn group_descriptor_blocks(g: Geometry, group: u32) -> (r: Option<u32>)
    ensures match r { Some(count) => valid(g) && group < g.groups && count as nat == num_gdb(g, group), None => true },
{
    if !is_valid(g) || group >= g.groups { return None; }
    proof { geometry_facts(g); }
    let per = g.block_bytes / g.descriptor_bytes;
    if !g.meta_bg || group / per < g.first_meta_bg {
        if !has_super(g, group) { return Some(0); }
        if g.meta_bg { Some(g.first_meta_bg) } else { descriptor_blocks(g) }
    } else {
        let offset = group % per;
        Some(if offset == 0 || offset == 1 || offset == per - 1 { 1u32 } else { 0u32 })
    }
}

pub fn base_metadata_blocks(g: Geometry, group: u32) -> (r: Option<u32>)
    ensures match r { Some(count) => valid(g) && group < g.groups && count as nat == base_blocks(g, group), None => true },
{
    let descriptors = match group_descriptor_blocks(g, group) { Some(n) => n, None => { return None; } };
    proof { geometry_facts(g); }
    let super_blocks = if has_super(g, group) { 1u32 } else { 0u32 };
    let per = g.block_bytes / g.descriptor_bytes;
    let reserved = if (!g.meta_bg || group / per < g.first_meta_bg) && super_blocks != 0 {
        g.reserved_gdt as u32
    } else { 0u32 };
    if descriptors > 4294967295u32 - super_blocks || descriptors + super_blocks > 4294967295u32 - reserved { return None; }
    Some(descriptors + super_blocks + reserved)
}

// Sparse filesystems have only the two explicit backup IDs or powers of
// 3, 5 and 7. Enumerating u32 groups linearly would permit billions of steps
// before reaching these few backups. The capped generators below do 33 steps
// per base; all returned IDs remain sorted, deduplicated and complete.
pub const POWER_SENTINEL: u64 = 4294967296;

pub open spec fn ordered_groups(groups: Seq<u32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < groups.len() ==> #[trigger] groups[i] < #[trigger] groups[j]
}
pub open spec fn eligible_backup(g: Geometry, end: u32, group: u32) -> bool {
    0 < group < end && has_super_spec(g, group)
}
pub open spec fn backup_groups_valid(g: Geometry, end: u32, groups: Seq<u32>) -> bool {
    &&& ordered_groups(groups)
    &&& forall|i: int| 0 <= i < groups.len() ==> eligible_backup(g, end, #[trigger] groups[i])
    &&& forall|group: u32| eligible_backup(g, end, group) ==> groups.contains(group)
}
spec fn capped_power(base: u32, exponent: nat) -> nat
    decreases exponent,
{
    if exponent == 0 { 1nat } else {
        let product = capped_power(base, (exponent - 1) as nat) * (base as nat);
        if product < POWER_SENTINEL { product } else { POWER_SENTINEL as nat }
    }
}

proof fn power_has_capped_witness(value: u32, base: u32, fuel: u8)
    requires base >= 2, power_steps(value, base, fuel),
    ensures exists|exponent: nat| exponent <= fuel && capped_power(base, exponent) == value,
    decreases fuel,
{
    reveal(capped_power);
    if value == 1 {
        assert(capped_power(base, 0) == value);
    } else {
        power_has_capped_witness(value / base, base, (fuel - 1) as u8);
        let exponent = choose|exponent: nat| exponent <= fuel - 1
            && capped_power(base, exponent) == value / base;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(value as int, base as int);
        assert(value as nat == (value / base) as nat * base) by (nonlinear_arith)
            requires value % base == 0, base > 0,
                value as int == (value as int / base as int) * base as int + value as int % base as int;
        assert(capped_power(base, exponent + 1) == value);
    }
}

spec fn inserted(groups: Seq<u32>, at: int, value: u32) -> Seq<u32> {
    groups.subrange(0, at) + seq![value] + groups.subrange(at, groups.len() as int)
}
proof fn sorted_insertion(groups: Seq<u32>, at: int, value: u32)
    requires ordered_groups(groups), 0 <= at <= groups.len(),
        forall|i: int| 0 <= i < at ==> #[trigger] groups[i] < value,
        forall|i: int| at <= i < groups.len() ==> value < #[trigger] groups[i],
    ensures ordered_groups(inserted(groups, at, value)),
        forall|x: u32| inserted(groups, at, value).contains(x) == (groups.contains(x) || x == value),
{
    reveal(inserted);
    assert forall|i: int, j: int| 0 <= i < j < groups.len()+1
        implies #[trigger] inserted(groups, at, value)[i] < #[trigger] inserted(groups, at, value)[j] by {
        if j < at { assert(groups[i] < groups[j]); }
        else if i < at && j == at { assert(groups[i] < value); }
        else if i < at && j > at { assert(groups[i] < groups[j-1]); }
        else if i == at { assert(value < groups[j-1]); }
        else { assert(groups[i-1] < groups[j-1]); }
    }
    assert forall|x: u32| inserted(groups, at, value).contains(x)
        == (groups.contains(x) || x == value) by {
        if inserted(groups, at, value).contains(x) {
            let i = choose|i: int| 0 <= i < inserted(groups, at, value).len()
                && inserted(groups, at, value)[i] == x;
            if i < at { assert(groups[i] == x); }
            else if i > at { assert(groups[i-1] == x); }
        }
        if groups.contains(x) {
            let i = choose|i: int| 0 <= i < groups.len() && groups[i] == x;
            if i < at { assert(inserted(groups, at, value)[i] == x); }
            else { assert(inserted(groups, at, value)[i+1] == x); }
        }
        if x == value { assert(inserted(groups, at, value)[at] == x); }
    }
}

fn insert_group(groups: &mut Vec<u32>, value: u32)
    requires ordered_groups(old(groups)@), old(groups).len() < 16384,
    ensures ordered_groups(final(groups)@), final(groups).len() <= old(groups).len()+1,
        forall|x: u32| final(groups)@.contains(x) == (old(groups)@.contains(x) || x == value),
{
    let ghost before = groups@;
    let mut at = 0usize;
    while at < groups.len() && groups[at] < value
        invariant groups@ == before, before == old(groups)@,
            before.len() < 16384, ordered_groups(before), at <= groups.len(),
            forall|i: int| 0 <= i < at ==> #[trigger] groups@[i] < value,
        decreases groups.len()-at,
    { at += 1; }
    if at < groups.len() && groups[at] == value {
        assert(before.contains(value)) by { assert(before[at as int] == value); }
        return;
    }
    proof {
        assert forall|i: int| at <= i < groups.len() implies value < #[trigger] groups@[i] by {
            if i > at { assert(groups@[at as int] < groups@[i]); }
        }
    }
    let mut result = Vec::<u32>::new();
    let mut i = 0usize;
    while i <= groups.len()
        invariant groups@ == before, before == old(groups)@,
            before.len() < 16384, i <= groups.len()+1,
            at <= groups.len(), ordered_groups(before),
            (forall|j: int| 0 <= j < at ==> #[trigger] before[j] < value),
            (forall|j: int| at <= j < before.len() ==> value < #[trigger] before[j]),
            result@ == inserted(before, at as int, value).subrange(0, i as int),
        decreases groups.len()+1-i,
    {
        result.push(if i < at { groups[i] } else if i == at { value } else { groups[i-1] });
        proof { assert(result@ =~= inserted(before, at as int, value).subrange(0, i as int+1)); }
        i += 1;
    }
    proof {
        assert(result@ =~= inserted(before, at as int, value));
        sorted_insertion(before, at as int, value);
    }
    *groups = result;
}

fn append_powers(g: Geometry, end: u32, base: u32, groups: &mut Vec<u32>)
    requires 2 <= base <= 7, old(groups).len() <= 66, ordered_groups(old(groups)@),
        forall|i: int| 0 <= i < old(groups).len() ==> eligible_backup(g, end, #[trigger] old(groups)@[i]),
    ensures ordered_groups(final(groups)@), final(groups).len() <= old(groups).len()+33,
        (forall|i: int| 0 <= i < final(groups).len() ==> eligible_backup(g, end, #[trigger] final(groups)@[i])),
        (forall|x: u32| old(groups)@.contains(x) ==> final(groups)@.contains(x)),
        (forall|x: u32| eligible_backup(g, end, x) && power(x, base) ==> final(groups)@.contains(x)),
{
    let ghost before = groups@;
    let mut exponent = 0u8;
    let mut value = 1u64;
    while exponent <= 32
        invariant 2 <= base <= 7, exponent <= 33, 1 <= value <= POWER_SENTINEL,
            value as nat == capped_power(base, exponent as nat),
            before.len() <= 66, ordered_groups(groups@), groups.len() <= before.len()+exponent,
            (forall|i: int| 0 <= i < groups.len() ==> eligible_backup(g, end, #[trigger] groups@[i])),
            (forall|x: u32| before.contains(x) ==> groups@.contains(x)),
            (forall|e: nat| e < exponent && 0 < capped_power(base, e) < end
                && has_super_spec(g, capped_power(base, e) as u32)
                ==> groups@.contains(capped_power(base, e) as u32)),
        decreases 33-exponent,
    {
        if value < end as u64 && has_super(g, value as u32) {
            let ghost previous = groups@;
            insert_group(groups, value as u32);
            proof {
                assert forall|i: int| 0 <= i < groups.len()
                    implies eligible_backup(g, end, #[trigger] groups@[i]) by {
                    let x = groups@[i];
                    assert(groups@.contains(x));
                    if x != value as u32 {
                        assert(previous.contains(x));
                        let at = choose|at: int| 0 <= at < previous.len() && previous[at] == x;
                        assert(eligible_backup(g, end, previous[at]));
                    }
                }
            }
        }
        proof {
            assert forall|e: nat| e < exponent as nat+1 && 0 < capped_power(base, e) < end
                && has_super_spec(g, capped_power(base, e) as u32)
                implies groups@.contains(capped_power(base, e) as u32) by {
                if e < exponent { assert(groups@.contains(capped_power(base, e) as u32)); }
            }
        }
        proof {
            assert(2 <= value as nat * base as nat <= 30064771072) by (nonlinear_arith)
                requires 1 <= value <= POWER_SENTINEL, 2 <= base <= 7;
        }
        let product = value * base as u64;
        value = if product < POWER_SENTINEL { product } else { POWER_SENTINEL };
        proof { reveal(capped_power); }
        exponent += 1;
    }
    proof {
        assert forall|x: u32| eligible_backup(g, end, x) && power(x, base)
            implies groups@.contains(x) by {
            power_has_capped_witness(x, base, 32);
            let e = choose|e: nat| e <= 32 && capped_power(base, e) == x;
            assert(e < exponent);
        }
    }
}

fn backup_groups(g: Geometry, end: u32, limit: usize) -> (r: Result<Vec<u32>, Error>)
    requires valid(g), 0 < end <= g.groups, 128 <= limit <= 16384,
    ensures match r {
        Ok(groups) => backup_groups_valid(g, end, groups@) && groups.len() <= limit,
        Err(_) => !g.sparse_super2 && !g.sparse_super && end as nat-1 > limit,
    },
{
    let mut groups = Vec::<u32>::new();
    if g.sparse_super2 {
        let take0 = g.backup0 > 0 && g.backup0 < end;
        let take1 = g.backup1 > 0 && g.backup1 < end;
        if take0 { insert_group(&mut groups, g.backup0); }
        assert forall|x: u32| groups@.contains(x) == (take0 && x == g.backup0) by {};
        if take1 { insert_group(&mut groups, g.backup1); }
        assert forall|x: u32| groups@.contains(x)
            == ((take0 && x == g.backup0) || (take1 && x == g.backup1)) by {};
        assert forall|i: int| 0 <= i < groups.len()
            implies eligible_backup(g, end, #[trigger] groups@[i]) by {
            assert(groups@.contains(groups@[i]));
        }
        assert forall|x: u32| eligible_backup(g, end, x) implies groups@.contains(x) by {
            assert(x == g.backup0 || x == g.backup1);
        }
        assert(backup_groups_valid(g, end, groups@));
    } else if g.sparse_super {
        append_powers(g, end, 3, &mut groups);
        append_powers(g, end, 5, &mut groups);
        append_powers(g, end, 7, &mut groups);
        proof {
            assert forall|group: u32| eligible_backup(g, end, group) implies groups@.contains(group) by {
                if group == 1 { assert(power(group, 3)); }
            }
        }
    } else {
        if end as u64-1 > limit as u64 { return Err(Error::Capacity); }
        let mut group = 1u32;
        while group < end
            invariant !g.sparse_super2, !g.sparse_super,
                1 <= group <= end, groups.len() as nat == group as nat-1,
                end as nat-1 <= limit, groups.len() <= limit,
                groups@ == Seq::new((group as nat-1) as nat, |i: int| (i+1) as u32),
            decreases end-group,
        {
            groups.push(group); group += 1;
        }
        proof {
            assert forall|group: u32| eligible_backup(g, end, group) implies groups@.contains(group) by {
                assert(groups@[group as int-1] == group);
            }
        }
    }
    Ok(groups)
}

pub open spec fn contains_copy_group(copies: Seq<DescriptorCopy>, group: u64) -> bool {
    exists|i: int| 0 <= i < copies.len() && !copies[i].primary && copies[i].group as nat == group
}
proof fn copy_presence_append(copies: Seq<DescriptorCopy>, copy: DescriptorCopy)
    ensures (forall|group: u64| contains_copy_group(copies, group)
        ==> contains_copy_group(copies.push(copy), group)),
        !copy.primary ==> contains_copy_group(copies.push(copy), copy.group as u64),
{
    assert forall|group: u64| contains_copy_group(copies, group)
        implies contains_copy_group(copies.push(copy), group) by {
        let at = choose|at: int| 0 <= at < copies.len() && !copies[at].primary
            && copies[at].group as nat == group;
        assert(copies.push(copy)[at] == copies[at]);
    }
    if !copy.primary { assert(copies.push(copy)[copies.len() as int] == copy); }
}

pub open spec fn expected_copy_group(g: Geometry, number: u32, group: u32) -> bool {
    if g.meta_bg && number >= g.first_meta_bg {
        let first = number as nat*(g.block_bytes/g.descriptor_bytes) as nat;
        group < g.groups && group as nat != first
            && (group as nat == first+1 || group as nat+1 == first+(g.block_bytes/g.descriptor_bytes) as nat)
    } else { eligible_backup(g, g.groups, group) }
}

/// Enumerate existing primary and backup copies of one descriptor block.
/// The bounded result is explicit; no missing backup is silently accepted.
pub fn copies(g: Geometry, logical_super: u64, number: u32)
    -> (r: Result<Vec<DescriptorCopy>, Error>)
    ensures match r { Ok(copies) => valid(g) && 0 < copies.len() <= MAX_COPIES
        && copies@[0].primary && copies@[0].block as nat == descriptor_location(g, logical_super, number)
        && (forall|i: int| 0 <= i < copies.len() ==> copy_ok(g, logical_super, number, #[trigger] copies@[i]))
        && (forall|group: u32| expected_copy_group(g, number, group)
            ==> contains_copy_group(copies@, group as u64)),
        Err(_) => true },
{
    let primary = match descriptor_block(g, logical_super, number) {
        Some(block) => block, None => { return Err(Error::Descriptor); },
    };
    proof { geometry_facts(g); product_fits(number, g.block_bytes / g.descriptor_bytes); }
    let per = g.block_bytes / g.descriptor_bytes;
    let mut copies = Vec::new();
    copies.push(DescriptorCopy { group: 0, block: primary, primary: true });
    if g.meta_bg && number >= g.first_meta_bg {
        let first64 = number as u64 * per as u64;
        if first64 > 4294967295 { return Err(Error::Overflow); }
        let first = first64 as u32;
        copies.set(0, DescriptorCopy { group: first, block: primary, primary: true });
        assert(copy_ok(g, logical_super, number, copies@[0]));
        let second = first64 + 1;
        let last = first64 + per as u64 - 1;
        let mut i = 0u8;
        while i < 2
            invariant i <= 2, 1 <= copies.len() <= 1 + i, per > 0, per <= 2048,
                g.meta_bg, number >= g.first_meta_bg, per == g.block_bytes / g.descriptor_bytes,
                first64 == number as nat * per, first64 <= 4294967295,
                first as nat == first64, second as nat == first64 + 1,
                last as nat + 1 == first64 + per, valid(g), number < descriptors(g),
                copies@[0].primary,
                copies@[0].block as nat == descriptor_location(g, logical_super, number),
                (i >= 1 && second < g.groups && second != first64 ==> contains_copy_group(copies@, second)),
                (i >= 2 && last < g.groups && last != first64 ==> contains_copy_group(copies@, last)),
                forall|j: int| 0 <= j < copies.len() ==> copy_ok(g, logical_super, number, #[trigger] copies@[j]),
            decreases 2 - i,
        {
            let group64 = if i == 0 { second } else { last };
            if group64 < g.groups as u64 && group64 != first64 && (i == 0 || group64 != second) {
                let group = group64 as u32;
                let start = match group_first(g, group) { Some(block) => block, None => { return Err(Error::Group); } };
                let skip = if has_super(g, group) { 1u64 } else { 0u64 };
                if start == 18446744073709551615 && skip != 0 { return Err(Error::Overflow); }
                let block = start + skip;
                if block >= g.blocks { return Err(Error::Outside); }
                let copy = DescriptorCopy { group, block, primary: false };
                assert(copy_ok(g, logical_super, number, copy));
                let ghost previous = copies@;
                copies.push(copy);
                proof { copy_presence_append(previous, copy); }
                assert(contains_copy_group(copies@, group64)) by {
                    assert(!copies@[copies.len() as int-1].primary
                        && copies@[copies.len() as int-1].group as nat == group64);
                }
            }
            i += 1;
        }
        proof {
            assert forall|group: u32| expected_copy_group(g, number, group)
                implies contains_copy_group(copies@, group as u64) by {
                assert(group as nat == second || group as nat == last);
            }
        }
    } else {
        assert(copy_ok(g, logical_super, number, copies@[0]));
        let backups = match backup_groups(g, g.groups, MAX_COPIES-1) {
            Ok(backups) => backups, Err(e) => { return Err(e); }
        };
        let mut index = 0usize;
        while index < backups.len()
            invariant index <= backups.len() < MAX_COPIES, copies.len() == index+1,
                backup_groups_valid(g, g.groups, backups@), valid(g), number < descriptors(g),
                !g.meta_bg || number < g.first_meta_bg,
                copies@[0].primary,
                copies@[0].block as nat == descriptor_location(g, logical_super, number),
                (forall|j: int| 0 <= j < copies.len() ==> copy_ok(g, logical_super, number, #[trigger] copies@[j])),
                (forall|j: int| 0 <= j < index ==> contains_copy_group(copies@, #[trigger] backups@[j] as u64)),
            decreases backups.len()-index,
        {
            let group = backups[index];
            let start = match group_first(g, group) { Some(block) => block, None => { return Err(Error::Group); } };
            if number as u64 + 1 > 18446744073709551615u64 - start { return Err(Error::Overflow); }
            let block = start + number as u64 + 1;
            if block >= g.blocks { return Err(Error::Outside); }
            let copy = DescriptorCopy { group, block, primary: false };
            assert(copy_ok(g, logical_super, number, copy));
            let ghost previous = copies@;
            copies.push(copy);
            proof {
                copy_presence_append(previous, copy);
                assert forall|j: int| 0 <= j < index as int+1
                    implies contains_copy_group(copies@, #[trigger] backups@[j] as u64) by {
                    if j < index { assert(contains_copy_group(previous, backups@[j] as u64)); }
                }
                assert(contains_copy_group(copies@, group as u64)) by {
                    assert(!copies@[copies.len() as int-1].primary
                        && copies@[copies.len() as int-1].group == group);
                }
            }
            index += 1;
        }
        proof {
            assert forall|group: u32| expected_copy_group(g, number, group)
                implies contains_copy_group(copies@, group as u64) by {
                assert(backups@.contains(group));
                let at = choose|at: int| 0 <= at < backups.len() && backups@[at] == group;
            }
        }
    }
    Ok(copies)
}

pub open spec fn resize_pointer_spec(g: Geometry, raw: Seq<u8>, number: u32, primary: u64) -> bool {
    &&& valid(g) && g.resize_inode && !g.meta_bg && raw.len() == g.block_bytes
    &&& primary <= 4294967295
    &&& bytes::le32(raw, ((number % (g.block_bytes / 4)) as int) * 4) == primary
}

// The prefix records the exact source words for all sparse backup groups
// encountered so far. Unused trailing pointer words are deliberately omitted.
pub open spec fn backup_prefix(g: Geometry, raw: Seq<u8>, primary: u64,
    next_group: u32, words: nat) -> bool
    decreases next_group,
{
    if next_group <= 1 { words == 0 }
    else {
        let group = (next_group - 1) as u32;
        if has_super_spec(g, group) {
            &&& words > 0 && words * 4 <= raw.len()
            &&& primary as nat + group as nat * g.blocks_per_group <= 4294967295
            &&& bytes::le32(raw, (words as int - 1) * 4)
                == primary as nat + group as nat * g.blocks_per_group
            &&& backup_prefix(g, raw, primary, group, (words - 1) as nat)
        } else { backup_prefix(g, raw, primary, group, words) }
    }
}

spec fn ordered_pointer_words(g: Geometry, raw: Seq<u8>, primary: u64, groups: Seq<u32>) -> bool {
    groups.len()*4 <= raw.len()
        && forall|i: int| 0 <= i < groups.len() ==>
            primary as nat + (#[trigger] groups[i]) as nat*g.blocks_per_group <= 4294967295
            && bytes::le32(raw, i*4) == primary as nat+groups[i] as nat*g.blocks_per_group
}

// The mathematical induction is erased. The executable validator traverses
// only the bounded generated backup list, while retaining the original exact
// source-word predicate over every group preceding end_group.
proof fn ordered_words_imply_backup_prefix(g: Geometry, raw: Seq<u8>, primary: u64,
    end_group: u32, groups: Seq<u32>)
    requires end_group > 0, backup_groups_valid(g, end_group, groups),
        ordered_pointer_words(g, raw, primary, groups),
    ensures backup_prefix(g, raw, primary, end_group, groups.len()),
    decreases end_group,
{
    if end_group == 1 {
        if groups.len() > 0 { assert(eligible_backup(g, end_group, groups[0])); }
        assert(groups.len() == 0);
    } else {
        let group = (end_group-1) as u32;
        if has_super_spec(g, group) {
            assert(eligible_backup(g, end_group, group));
            assert(groups.contains(group));
            let at = choose|at: int| 0 <= at < groups.len() && groups[at] == group;
            if at < groups.len()-1 {
                assert(groups[at] < groups.last());
                assert(eligible_backup(g, end_group, groups.last()));
            }
            assert(at == groups.len()-1 && groups.last() == group);
            let prefix = groups.drop_last();
            assert forall|i: int| 0 <= i < prefix.len()
                implies eligible_backup(g, group, #[trigger] prefix[i]) by {
                assert(groups[i] < groups.last());
            }
            assert forall|x: u32| eligible_backup(g, group, x) implies prefix.contains(x) by {
                assert(eligible_backup(g, end_group, x));
                assert(groups.contains(x));
                let i = choose|i: int| 0 <= i < groups.len() && groups[i] == x;
                if i == groups.len()-1 { assert(groups[i] == group); }
                assert(i < prefix.len());
                assert(prefix[i] == x);
            }
            assert(backup_groups_valid(g, group, prefix));
            assert(ordered_pointer_words(g, raw, primary, prefix));
            ordered_words_imply_backup_prefix(g, raw, primary, group, prefix);
            assert(backup_prefix(g, raw, primary, end_group, groups.len()));
        } else {
            assert forall|i: int| 0 <= i < groups.len()
                implies eligible_backup(g, group, #[trigger] groups[i]) by {
                assert(groups[i] != group);
            }
            assert forall|x: u32| eligible_backup(g, group, x) implies groups.contains(x) by {
                assert(eligible_backup(g, end_group, x));
            }
            assert(backup_groups_valid(g, group, groups));
            ordered_words_imply_backup_prefix(g, raw, primary, group, groups);
            assert(backup_prefix(g, raw, primary, end_group, groups.len()));
        }
    }
}

pub open spec fn resize_backups_spec(g: Geometry, raw: Seq<u8>, end_group: u32, primary: u64) -> bool {
    &&& valid(g) && g.resize_inode && !g.meta_bg && raw.len() == g.block_bytes
    &&& 0 < end_group <= g.groups && primary <= 4294967295
    &&& exists|words: nat| backup_prefix(g, raw, primary, end_group, words)
}

/// Validate the actual resize inode's double-indirect pointer slot.
pub fn resize_pointer_reserved(g: Geometry, double_indirect: &[u8], number: u32, primary: u64) -> (r: bool)
    ensures r == resize_pointer_spec(g, double_indirect@, number, primary),
{
    if !is_valid(g) || !g.resize_inode || g.meta_bg || double_indirect.len() != g.block_bytes as usize
        || primary > 4294967295 { return false; }
    let addresses = g.block_bytes / 4;
    let offset = (number % addresses) as usize * 4;
    bytes::read_le32(double_indirect, offset).unwrap() as u64 == primary
}

/// Validate Linux's ordered backup-pointer words in one reserved primary GDT
/// block. Trailing words are outside this particular reservation check.
pub fn resize_backups_reserved(g: Geometry, primary_raw: &[u8], end_group: u32, primary: u64) -> (r: bool)
    ensures r ==> resize_backups_spec(g, primary_raw@, end_group, primary),
{
    if !is_valid(g) || !g.resize_inode || g.meta_bg || primary_raw.len() != g.block_bytes as usize
        || end_group == 0 || end_group > g.groups || primary > 4294967295 { return false; }
    proof { geometry_facts(g); }
    let limit = primary_raw.len()/4;
    let backups = match backup_groups(g, end_group, limit) {
        Ok(backups) => backups, Err(_) => { return false; }
    };
    let mut index = 0usize;
    while index < backups.len()
        invariant index <= backups.len() <= primary_raw.len()/4,
            backup_groups_valid(g, end_group, backups@), valid(g),
            (forall|i: int| 0 <= i < index ==>
                primary as nat+(#[trigger] backups@[i]) as nat*g.blocks_per_group <= 4294967295
                && bytes::le32(primary_raw@, i*4) == primary as nat+backups@[i] as nat*g.blocks_per_group),
        decreases backups.len()-index,
    {
        let group = backups[index];
        proof { product_fits(group, g.blocks_per_group); }
        let shift = group as u64*g.blocks_per_group as u64;
        if primary > 18446744073709551615u64-shift { return false; }
        let expected = shift+primary;
        if expected > 4294967295
            || bytes::read_le32(primary_raw, index*4).unwrap() as u64 != expected { return false; }
        index += 1;
    }
    proof {
        assert(ordered_pointer_words(g, primary_raw@, primary, backups@));
        ordered_words_imply_backup_prefix(g, primary_raw@, primary, end_group, backups@);
        assert(exists|words: nat| backup_prefix(g, primary_raw@, primary, end_group, words));
    }
    true
}

}
