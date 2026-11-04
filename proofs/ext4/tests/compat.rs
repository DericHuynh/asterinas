// SPDX-License-Identifier: MPL-2.0

//! Host interoperability/regression tests of the emitted library. This test
//! harness is not part of the formal claim and does not implement a mount.

extern crate verified_ext4 as core;

fn image() -> Vec<u8> {
    std::fs::read(std::env::var("EXT4_TEST_IMAGE").expect("test image path")).unwrap()
}

fn le32(s: &[u8], o: usize) -> u32 {
    core::bytes::read_le32(s, o).unwrap()
}

fn metadata(img: &[u8]) -> (core::superblock::Superblock, core::group::Group, u32) {
    let sb = core::superblock::parse(&img[1024..2048], img.len() as u64).expect("Linux superblock");
    let seed = core::crc::crc32c(0xffffffff, &img[1128..1144]);
    let ipg = le32(&img[1024..2048], 40);
    let g =
        core::group::parse(&img[4096..4128], 0, sb.blocks(), ipg, seed).expect("Linux descriptor");
    (sb, g, seed)
}

fn inode_bytes(img: &[u8], table: u32, number: u32) -> &[u8] {
    let offset = table as usize * 4096 + (number as usize - 1) * 256;
    &img[offset..offset + 256]
}

fn first_data_block(raw: &[u8], blocks: u32) -> u32 {
    let root = &raw[40..100];
    let count = core::extent::validate_inline_root(root, blocks).expect("inline leaf root");
    for i in 0..count as usize {
        let e = core::extent::parse(root, 12 + 12 * i, blocks).unwrap();
        if let Some(core::extent::Mapping::Data(block)) = e.resolve(0, blocks) {
            return block;
        }
    }
    panic!("no initialized logical block zero");
}

#[test]
fn shadow_patches_are_sorted_owned_and_reject_duplicates_without_changes() {
    use core::patch_set::{MAX_PATCHES, PatchSet};
    let mut patches = PatchSet::new();
    let mut payload = vec![0x5a; 4096];
    for block in [u32::MAX, 7, 0, 1, 1024, u32::MAX - 1] {
        payload[0..4].copy_from_slice(&block.to_le_bytes());
        patches = patches.insert(block, &payload).ok().unwrap();
    }
    payload.fill(0);
    let sorted = [0, 1, 7, 1024, u32::MAX - 1, u32::MAX];
    for (index, block) in sorted.into_iter().enumerate() {
        let patch = patches.at(index).unwrap();
        assert_eq!(patch.block(), block);
        assert_eq!(&patch.as_slice()[..4], &block.to_le_bytes());
        assert_eq!(&patch.as_slice()[4..], &[0x5a; 4092]);
        assert_eq!(patches.get(block).unwrap().as_slice(), patch.as_slice());
    }
    assert!(patches.at(sorted.len()).is_none());
    assert!(patches.at(usize::MAX).is_none());
    for block in [2, 6, 8, u32::MAX - 2] {
        assert!(patches.get(block).is_none());
    }
    for (block, input) in [(7, &payload[..]), (2, &payload[..4095]), (2, &[][..])] {
        patches = patches.insert(block, input).err().expect("rejected patch");
        assert_eq!(patches.len(), sorted.len());
        for (index, expected) in sorted.into_iter().enumerate() {
            assert_eq!(patches.at(index).unwrap().block(), expected);
        }
    }
    let images = patches.into_images();
    assert_eq!(images.len(), sorted.len());
    let mut bounded = PatchSet::new();
    for block in (0..MAX_PATCHES as u32).rev() {
        bounded = bounded.insert(block, &payload).ok().unwrap();
    }
    bounded = bounded
        .insert(u32::MAX, &payload)
        .err()
        .expect("patch credit limit");
    assert_eq!(bounded.len(), MAX_PATCHES);
    assert!(bounded.get(u32::MAX).is_none());
    assert_eq!(bounded.at(0).unwrap().block(), 0);
    assert_eq!(
        bounded.at(MAX_PATCHES - 1).unwrap().block(),
        MAX_PATCHES as u32 - 1
    );
}

#[test]
fn shadow_sources_preserve_provenance_overlay_precedence_and_validation() {
    use core::{
        allocated_inode, allocation, directory_index, file_read, namespace, patch_set::PatchSet,
        snapshot::Snapshot,
    };
    let img = image();
    let (sb, group, _) = metadata(&img);
    let block = first_data_block(inode_bytes(&img, group.inode_table, 12), sb.blocks());
    let base = Snapshot::from_bytes(&img);
    let replacement = [0x9d; 4096];
    let patches = PatchSet::new().insert(block, &replacement).ok().unwrap();
    let shadow = base.overlay(&patches).unwrap();
    assert_eq!(shadow.shadow_depth(), 1);
    assert_eq!(shadow.partition_bytes(), img.len() as u64);
    assert_eq!(shadow.block(block).unwrap().as_slice(), &replacement);
    for index in [0, 1, group.inode_table, sb.blocks() - 1] {
        assert_eq!(
            shadow.block(index).unwrap().as_slice(),
            base.block(index).unwrap().as_slice()
        );
    }
    assert!(shadow.block(sb.blocks()).is_none());
    assert!(shadow.block(u32::MAX).is_none());
    let checked = allocation::parse(shadow).unwrap();
    let directories = directory_index::build(&checked).unwrap();
    assert!(namespace::validate(&directories).is_some());
    let node = allocated_inode::get(&checked, 12).unwrap();
    match file_read::chunk(&node, 0, 4096) {
        file_read::Chunk::Data(bytes) => assert_eq!(bytes, &replacement),
        _ => panic!("shadow data was not used by the source-bound file reader"),
    }
    assert_eq!(
        base.block(block).unwrap().as_slice(),
        &img[block as usize * 4096..(block as usize + 1) * 4096]
    );
    let later_bytes = [0xa7; 4096];
    let later = PatchSet::new().insert(block, &later_bytes).ok().unwrap();
    let shadow = base.overlay(&patches).unwrap().overlay(&later).unwrap();
    assert_eq!(shadow.block(block).unwrap().as_slice(), &later_bytes);
    assert_eq!(
        shadow.block(0).unwrap().as_slice(),
        base.block(0).unwrap().as_slice()
    );
    let mut corrupt_inode_table = base.block(group.inode_table).unwrap().as_slice().to_vec();
    corrupt_inode_table[256] ^= 1;
    let corrupt = PatchSet::new()
        .insert(group.inode_table, &corrupt_inode_table)
        .ok()
        .unwrap();
    assert!(
        allocation::parse(base.overlay(&corrupt).unwrap()).is_none(),
        "shadow metadata must be revalidated"
    );
    let outside = PatchSet::new()
        .insert(sb.blocks(), &[0; 4096])
        .ok()
        .unwrap();
    assert!(base.overlay(&outside).is_none());
    let maximum = PatchSet::new().insert(u32::MAX, &[0; 4096]).ok().unwrap();
    assert!(base.overlay(&maximum).is_none());
    let empty = PatchSet::new();
    let mut nested = base.overlay(&empty).unwrap();
    for _ in 1..core::snapshot::MAX_SHADOW_LAYERS {
        nested = nested.overlay(&empty).unwrap();
    }
    assert_eq!(nested.shadow_depth(), core::snapshot::MAX_SHADOW_LAYERS);
    assert_eq!(
        nested.block(block).unwrap().as_slice(),
        base.block(block).unwrap().as_slice()
    );
    assert!(nested.overlay(&empty).is_none());
    for bytes in [&[][..], &[0; 4095][..]] {
        let short = Snapshot::from_bytes(bytes);
        assert!(short.overlay(&patches).is_none());
        assert!(short.block(0).is_none());
        assert!(short.overlay(&empty).is_some());
    }
}

#[test]
fn journal_bootstrap_uses_declared_inode_bytes_before_allocation_validation() {
    use core::{bootstrap, group_index, snapshot::Snapshot};
    let img = image();
    let (sb, group, _) = metadata(&img);
    let source = Snapshot::from_bytes(&img);
    let located = bootstrap::locate(&source).unwrap();
    assert_eq!(located.primary(), &img[..4096]);
    assert_eq!(located.uuid(), &img[1128..1144]);
    assert_eq!(
        located.raw_journal_inode(),
        inode_bytes(&img, group.inode_table, 8)
    );
    let layout = located.layout();
    let start = layout.physical_start() as usize * 4096;
    let end = start + layout.blocks() as usize * 4096;
    assert_eq!(located.capture_journal(), &img[start..end]);
    assert_eq!(located.source().partition_bytes(), img.len() as u64);
    let mut checkpoint_cut = img.clone();
    checkpoint_cut[group.block_bitmap as usize * 4096] ^= 0x80;
    assert!(group_index::parse(Snapshot::from_bytes(&checkpoint_cut)).is_none());
    let cut_source = Snapshot::from_bytes(&checkpoint_cut);
    let cut = bootstrap::locate(&cut_source)
        .expect("recovery discovery does not require consistent home bitmaps");
    assert_eq!(cut.layout().physical_start(), layout.physical_start());
    assert_eq!(cut.capture_journal(), located.capture_journal());
    for offset in [
        1024 + 56,
        4096 + 30,
        group.inode_table as usize * 4096 + 7 * 256 + 60,
    ] {
        let mut bad = img.clone();
        bad[offset] ^= 1;
        assert!(bootstrap::locate(&Snapshot::from_bytes(&bad)).is_none());
    }
    for length in [0, 4095, 4096, 8191, group.inode_table as usize * 4096] {
        assert!(bootstrap::locate(&Snapshot::from_bytes(&img[..length])).is_none());
    }
    assert_eq!(source.capture(0, 2).unwrap(), &img[..8192]);
    for (start, count) in [
        (0, 0),
        (0, 32769),
        (sb.blocks(), 1),
        (u32::MAX, 1),
        (u32::MAX, 2),
    ] {
        assert!(source.capture(start, count).is_none());
    }
}

#[test]
fn static_image_certificates_and_bootstrap_identity_check_different_boundaries() {
    use core::{
        bootstrap, bootstrap_identity, image_validation, patch_set::PatchSet, snapshot::Snapshot,
    };
    let img = image();
    let (_, group, seed) = metadata(&img);
    let source = Snapshot::from_bytes(&img);
    let boot = bootstrap::locate(&source).unwrap();
    let checked = image_validation::inspect(source.duplicate()).unwrap();
    assert_eq!(checked.source().block(0).unwrap().as_slice(), &img[..4096]);
    assert!(bootstrap_identity::check(&boot, checked.source()));
    for (number, permitted) in [(2u32, true), (8, false)] {
        let mut table = source.block(group.inode_table).unwrap().as_slice().to_vec();
        let slot = (number as usize - 1) * 256;
        let inode = &mut table[slot..slot + 256];
        inode[2] ^= 1; // Change the owner, retaining a valid inode and layout.
        let checksum = core::inode::calculated_checksum(inode, number, seed).unwrap();
        inode[124..126].copy_from_slice(&(checksum as u16).to_le_bytes());
        inode[130..132].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
        let patch = PatchSet::new()
            .insert(group.inode_table, &table)
            .ok()
            .unwrap();
        let shadow = source.overlay(&patch).unwrap();
        assert!(
            image_validation::inspect(shadow.duplicate()).is_some(),
            "the static filesystem remains valid"
        );
        assert_eq!(
            bootstrap_identity::check(&boot, &shadow),
            permitted,
            "inode {number}: ordinary inodes sharing inode 8's block may change; inode 8 must remain exact"
        );
    }
    let mut primary = img[..4096].to_vec();
    primary[1144] ^= 1; // The volume label is mutable under replay.
    let checksum = core::crc::crc32c(0xffffffff, &primary[1024..2044]);
    primary[2044..2048].copy_from_slice(&checksum.to_le_bytes());
    let label = PatchSet::new().insert(0, &primary).ok().unwrap();
    let shadow = source.overlay(&label).unwrap();
    assert!(bootstrap_identity::check(&boot, &shadow));
    assert!(image_validation::inspect(shadow).is_some());
    for offset in [1128, 1028] {
        let mut bad = img[..4096].to_vec();
        bad[offset] ^= 1;
        let patch = PatchSet::new().insert(0, &bad).ok().unwrap();
        assert!(!bootstrap_identity::check(
            &boot,
            &source.overlay(&patch).unwrap()
        ));
    }
    let mut descriptor = img[4096..8192].to_vec();
    descriptor[8] ^= 1;
    let patch = PatchSet::new().insert(1, &descriptor).ok().unwrap();
    assert!(!bootstrap_identity::check(
        &boot,
        &source.overlay(&patch).unwrap()
    ));
    descriptor = img[4096..8192].to_vec();
    descriptor[30] ^= 1;
    let patch = PatchSet::new().insert(1, &descriptor).ok().unwrap();
    let shadow = source.overlay(&patch).unwrap();
    assert!(
        bootstrap_identity::check(&boot, &shadow),
        "checksum validation is a separate obligation"
    );
    assert!(image_validation::inspect(shadow).is_none());
    assert!(!bootstrap_identity::check(
        &boot,
        &Snapshot::from_bytes(&img[..img.len() - 1])
    ));
}

#[test]
fn block_ranges_handle_64_bit_limits_and_split_into_disjoint_partitions() {
    use core::block_range::BlockRange;
    assert!(BlockRange::new(0, 0, u64::MAX).is_none());
    assert!(BlockRange::new(u64::MAX, 1, u64::MAX).is_none());
    assert!(BlockRange::new(u64::MAX - 1, 2, u64::MAX).is_none());
    let range = BlockRange::new(u64::MAX - 1024, 1024, u64::MAX).unwrap();
    assert_eq!(range.start(), u64::MAX - 1024);
    assert_eq!(range.length(), 1024);
    assert_eq!(range.limit(), u64::MAX);
    assert!(range.split(0).is_none());
    assert!(range.split(1024).is_none());
    assert!(range.split(u64::MAX).is_none());
    let (a, b) = range.split(511).unwrap();
    assert!(a.is_disjoint(&b) && b.is_disjoint(&a));
    assert!(!range.is_disjoint(&a));
    for offset in 0..1024 {
        let block = range.start() + offset;
        assert!(range.has_block(block));
        assert!(a.has_block(block) ^ b.has_block(block));
    }
    for block in [0, range.start() - 1, u64::MAX] {
        assert!(!range.has_block(block));
        assert!(!a.has_block(block) && !b.has_block(block));
    }
    let zero = BlockRange::new(0, 1, 1).unwrap();
    assert!(zero.has_block(0)); // Geometry descriptions also represent block zero.
}

#[test]
fn extent_spans_preserve_48_bit_addresses_and_every_mapping_across_splits() {
    use core::extent_span::{self, ExtentSpan, ExtentState};
    for physical in [1u64, 0xffff_ffff, 0x1_0000_0000, 0xffff_ffff_ffff] {
        for (length, initialized) in [(1, true), (32768, true), (1, false), (32767, false)] {
            let blocks = physical + length as u64;
            let state = if initialized {
                ExtentState::Written
            } else {
                ExtentState::Unwritten
            };
            let span = ExtentSpan::new(42, length, physical, state, blocks).unwrap();
            let raw = span.encode().unwrap();
            assert_eq!(&raw[6..8], &((physical >> 32) as u16).to_le_bytes());
            assert_eq!(&raw[8..12], &(physical as u32).to_le_bytes());
            let decoded = extent_span::parse(&raw, 0, blocks).unwrap();
            let info = decoded.info();
            assert_eq!(
                (
                    info.logical,
                    info.length,
                    info.physical,
                    info.initialized,
                    info.blocks
                ),
                (42, length, physical, initialized, blocks)
            );
            assert_eq!(decoded.physical_block(41), None);
            assert_eq!(decoded.physical_block(42 + length), None);
            assert_eq!(
                decoded.physical_block(42 + length - 1),
                Some(physical + length as u64 - 1)
            );
            assert!(decoded.split(0).is_none());
            assert!(decoded.split(length).is_none());
            if length > 1 {
                let (left, right) = decoded.split(length / 2).unwrap();
                assert_eq!(left.info().initialized, initialized);
                assert_eq!(right.info().initialized, initialized);
                assert_eq!(left.merge(&right).unwrap().encode().unwrap(), raw);
                assert!(right.merge(&left).is_none());
                for logical in 41..=42 + length {
                    let a = left.physical_block(logical);
                    let b = right.physical_block(logical);
                    assert!(!(a.is_some() && b.is_some()));
                    assert_eq!(a.or(b), decoded.physical_block(logical));
                }
            }
            assert!(extent_span::parse(&raw, usize::MAX, blocks).is_none());
            assert!(extent_span::parse(&raw[..11], 0, blocks).is_none());
            assert!(extent_span::parse(&raw, 0, blocks - 1).is_none());
        }
    }
    assert!(ExtentSpan::new(u32::MAX, 1, 1, ExtentState::Written, 2).is_none());
    assert!(ExtentSpan::new(0, 32768, 1, ExtentState::Unwritten, 65536).is_none());
    assert!(ExtentSpan::new(0, 1, 0, ExtentState::Written, 65536).is_none());
    assert!(ExtentSpan::new(0, 2, u64::MAX - 1, ExtentState::Written, u64::MAX).is_none());
    let description = ExtentSpan::new(0, 1, u64::MAX - 1, ExtentState::Written, u64::MAX).unwrap();
    assert!(
        description.encode().is_none(),
        "a model range is not automatically an encodable 48-bit extent"
    );
    let first = ExtentSpan::new(0, 1, 100, ExtentState::Written, 65536).unwrap();
    for incompatible in [
        ExtentSpan::new(1, 1, 101, ExtentState::Unwritten, 65536).unwrap(),
        ExtentSpan::new(2, 1, 101, ExtentState::Written, 65536).unwrap(),
        ExtentSpan::new(1, 1, 102, ExtentState::Written, 65536).unwrap(),
        ExtentSpan::new(1, 1, 101, ExtentState::Written, 65537).unwrap(),
    ] {
        assert!(first.merge(&incompatible).is_none());
    }
    let a = ExtentSpan::new(0, 20000, 100, ExtentState::Written, 65536).unwrap();
    let b = ExtentSpan::new(20000, 20000, 20100, ExtentState::Written, 65536).unwrap();
    assert!(
        a.merge(&b).is_none(),
        "a merged extent must fit the Linux length encoding"
    );
}

#[test]
fn extent_nodes_check_full_capacity_checksums_depth_and_48_bit_children() {
    use core::{
        extent_node::{self, BlockChecksum},
        extent_span::{ExtentSpan, ExtentState},
    };
    fn header(size: usize, depth: u16, count: u16, maximum: u16) -> Vec<u8> {
        let mut raw = vec![0; size];
        raw[..2].copy_from_slice(&0xf30au16.to_le_bytes());
        raw[2..4].copy_from_slice(&count.to_le_bytes());
        raw[4..6].copy_from_slice(&maximum.to_le_bytes());
        raw[6..8].copy_from_slice(&depth.to_le_bytes());
        raw[8..12].copy_from_slice(&0x789abcdeu32.to_le_bytes());
        raw
    }
    fn seal(raw: &mut [u8], seed: u32) {
        let maximum = u16::from_le_bytes(raw[4..6].try_into().unwrap()) as usize;
        let tail = 12 + maximum * 12;
        let checksum = core::crc::crc32c(seed, &raw[..tail]);
        raw[tail..tail + 4].copy_from_slice(&checksum.to_le_bytes());
    }
    fn index(raw: &mut [u8], ordinal: usize, logical: u32, child: u64) {
        let offset = 12 + ordinal * 12;
        raw[offset..offset + 4].copy_from_slice(&logical.to_le_bytes());
        raw[offset + 4..offset + 8].copy_from_slice(&(child as u32).to_le_bytes());
        raw[offset + 8..offset + 10].copy_from_slice(&((child >> 32) as u16).to_le_bytes());
        raw[offset + 10..offset + 12].copy_from_slice(&0xabcdu16.to_le_bytes()); // Linux's unused field.
    }
    let seed = 0x9abcdef0;
    let physical = 0x1234_5678_9010u64;
    let blocks = physical + 100;
    let first = ExtentSpan::new(1, 3, physical, ExtentState::Written, blocks)
        .unwrap()
        .encode()
        .unwrap();
    let second = ExtentSpan::new(8, 2, physical + 10, ExtentState::Unwritten, blocks)
        .unwrap()
        .encode()
        .unwrap();
    for size in [1024usize, 2048, 4096, 8192, 16384, 32768, 65536] {
        let maximum = ((size - 12) / 12) as u16;
        let tail = 12 + maximum as usize * 12;
        let mut raw = header(size, 0, 2, maximum);
        raw[12..24].copy_from_slice(&first);
        raw[24..36].copy_from_slice(&second);
        seal(&mut raw, seed);
        let node = extent_node::parse_block(&raw, blocks, BlockChecksum::Crc32c(seed)).unwrap();
        assert_eq!(node.header_fields(), (2, maximum, 0));
        assert_eq!(node.raw(), &raw);
        assert_eq!(node.leaf_extent(0).unwrap().info().physical, physical);
        assert!(!node.leaf_extent(1).unwrap().info().initialized);
        assert!(node.leaf_extent(2).is_none() && node.leaf_extent(usize::MAX).is_none());
        assert!(node.index_entry(0).is_none());
        assert!(extent_node::parse_block(&raw, blocks, BlockChecksum::Crc32c(seed ^ 1)).is_none());
        let mut changed = raw.clone();
        changed[40] ^= 1; // Unused record bytes still lie inside the eh_max checksum domain.
        assert!(extent_node::parse_block(&changed, blocks, BlockChecksum::Crc32c(seed)).is_none());
        seal(&mut changed, seed);
        assert!(extent_node::parse_block(&changed, blocks, BlockChecksum::Crc32c(seed)).is_some());
        if tail + 4 < size {
            changed = raw.clone();
            changed[size - 1] ^= 1; // Padding after the tail is outside that domain.
            assert!(
                extent_node::parse_block(&changed, blocks, BlockChecksum::Crc32c(seed)).is_some()
            );
        }
        for (offset, value) in [
            (0, 0u16),
            (4, 0),
            (4, maximum + 1),
            (2, maximum + 1),
            (6, 6),
        ] {
            changed = raw.clone();
            changed[offset..offset + 2].copy_from_slice(&value.to_le_bytes());
            if offset != 4 || value <= maximum {
                seal(&mut changed, seed);
            }
            assert!(
                extent_node::parse_block(&changed, blocks, BlockChecksum::Crc32c(seed)).is_none()
            );
        }
        changed = raw.clone();
        changed[24..28].copy_from_slice(&2u32.to_le_bytes()); // Overlap the first leaf extent.
        seal(&mut changed, seed);
        assert!(extent_node::parse_block(&changed, blocks, BlockChecksum::Crc32c(seed)).is_none());
        for depth in 1..=5 {
            let mut raw = header(size, depth, 2, maximum);
            index(&mut raw, 0, 0, physical);
            index(&mut raw, 1, 64, physical + 5);
            seal(&mut raw, seed);
            let node = extent_node::parse_block(&raw, blocks, BlockChecksum::Crc32c(seed)).unwrap();
            assert_eq!(node.header_fields(), (2, maximum, depth));
            let entry = node.index_entry(1).unwrap();
            assert_eq!((entry.logical, entry.child), (64, physical + 5));
            assert!(node.index_entry(2).is_none() && node.index_entry(usize::MAX).is_none());
            assert!(node.leaf_extent(0).is_none());
            for (logical, child) in [(0, physical + 5), (64, 0), (64, blocks)] {
                let mut bad = raw.clone();
                index(&mut bad, 1, logical, child);
                seal(&mut bad, seed);
                assert!(
                    extent_node::parse_block(&bad, blocks, BlockChecksum::Crc32c(seed)).is_none()
                );
            }
        }
        let mut small = header(size, 0, 2, 2);
        small[12..24].copy_from_slice(&first);
        small[24..36].copy_from_slice(&second);
        seal(&mut small, seed);
        assert!(extent_node::parse_block(&small, blocks, BlockChecksum::Crc32c(seed)).is_some());
    }
    for depth in 1..=5 {
        let mut raw = header(60, depth, 2, 4);
        index(&mut raw, 0, 0, physical);
        index(&mut raw, 1, 64, physical + 5);
        assert!(extent_node::parse_inline_root(&raw, blocks).is_some());
        assert!(extent_node::parse_block(&raw, blocks, BlockChecksum::Legacy).is_none());
    }
    let img = image();
    let (sb, group, _) = metadata(&img);
    for number in [2, 8, 11, 12] {
        let raw = &inode_bytes(&img, group.inode_table, number)[40..100];
        assert!(extent_node::parse_inline_root(raw, sb.blocks() as u64).is_some());
    }
    for length in [0usize, 59, 61, 1023, 65537] {
        assert!(
            extent_node::parse_block(&vec![0; length], blocks, BlockChecksum::Legacy).is_none()
        );
    }
}

#[test]
fn source_blocks_capture_exact_shadow_ranges_across_filesystem_block_sizes() {
    use core::{extent_node::BlockChecksum, patch_set::PatchSet, snapshot::Snapshot, source_block};
    fn empty_node(size: usize, seed: u32) -> Vec<u8> {
        let mut bytes = vec![0; size];
        let maximum = ((size - 12) / 12) as u16;
        bytes[..2].copy_from_slice(&0xf30au16.to_le_bytes());
        bytes[4..6].copy_from_slice(&maximum.to_le_bytes());
        let tail = 12 + maximum as usize * 12;
        let checksum = core::crc::crc32c(seed, &bytes[..tail]);
        bytes[tail..tail + 4].copy_from_slice(&checksum.to_le_bytes());
        bytes
    }
    let mut base = (0..131405).map(|i| (i % 251) as u8).collect::<Vec<_>>();
    let mut expected = base.clone();
    let seed = 0x12345678;
    let small_node = empty_node(1024, seed);
    let wide_node = empty_node(65536, seed);
    let mut first = vec![0x55; 4096];
    first[1024..2048].copy_from_slice(&small_node);
    let mut patches = PatchSet::new().insert(0, &first).ok().unwrap();
    expected[..4096].copy_from_slice(&first);
    patches = patches.insert(2, &[0xa7; 4096]).ok().unwrap();
    expected[8192..12288].fill(0xa7);
    for index in 0..16 {
        let bytes = &wide_node[index * 4096..(index + 1) * 4096];
        patches = patches.insert(16 + index as u32, bytes).ok().unwrap();
    }
    expected[65536..131072].copy_from_slice(&wide_node);
    let owned = {
        let source = Snapshot::from_bytes(&base);
        let shadow = source.overlay(&patches).unwrap();
        for start in [
            0usize,
            1,
            1024,
            4095,
            4096,
            8191,
            65535,
            131072,
            expected.len(),
        ] {
            for length in [0usize, 1, 256, 1024, 2048, 4096, 8192, 65536] {
                let actual = shadow.capture_bytes(start as u64, length);
                if start + length <= expected.len() {
                    assert_eq!(actual.unwrap(), &expected[start..start + length]);
                } else {
                    assert!(actual.is_none());
                }
            }
        }
        assert!(shadow.capture_bytes(0, 65537).is_none());
        assert!(shadow.capture_bytes(u64::MAX, 0).is_none());
        assert!(shadow.capture_bytes(u64::MAX, 1).is_none());
        for size in [1024u32, 2048, 4096, 8192, 16384, 32768, 65536] {
            let count = expected.len() as u64 / size as u64;
            for number in [0, 1, count - 1] {
                let block = source_block::capture(&shadow, number, size).unwrap();
                assert_eq!(block.identity(), (number, size));
                let start = number as usize * size as usize;
                assert_eq!(block.raw(), &expected[start..start + size as usize]);
            }
            assert!(source_block::capture(&shadow, count, size).is_none());
            assert!(source_block::capture(&shadow, u64::MAX, size).is_none());
        }
        for size in [0u32, 60, 512, 4097, 131072, u32::MAX] {
            assert!(source_block::capture(&shadow, 0, size).is_none());
        }
        for size in [1024u32, 65536] {
            let block = source_block::capture(&shadow, 1, size).unwrap();
            let count = expected.len() as u64 / size as u64;
            assert!(
                block
                    .parse_extent_node(count, BlockChecksum::Crc32c(seed))
                    .is_some()
            );
            assert!(
                block
                    .parse_extent_node(count, BlockChecksum::Crc32c(seed ^ 1))
                    .is_none()
            );
            assert!(
                block
                    .parse_extent_node(count + 1, BlockChecksum::Crc32c(seed))
                    .is_none()
            );
            assert!(
                block
                    .parse_extent_node(0, BlockChecksum::Crc32c(seed))
                    .is_none()
            );
        }
        source_block::capture(&shadow, 1, 65536).unwrap()
    };
    base.fill(0);
    assert_eq!(
        owned.raw(),
        wide_node,
        "the returned source block owns its frozen bytes"
    );
}

#[test]
fn linux_created_external_extent_nodes_match_source_capture_and_inode_checksum_seed() {
    use core::{
        extent_node::{self, BlockChecksum},
        snapshot::Snapshot,
        source_block,
    };
    struct ScratchFiles(Vec<String>);
    impl Drop for ScratchFiles {
        fn drop(&mut self) {
            for path in &self.0 {
                let _ = std::fs::remove_file(path);
            }
        }
    }
    let prefix = format!("build/native-extents-{}", std::process::id());
    let image_path = format!("{prefix}.img");
    let commands_path = format!("{prefix}.commands");
    let _cleanup = ScratchFiles(vec![image_path.clone(), commands_path.clone()]);
    std::fs::write(&image_path, image()).unwrap();
    let mut commands = String::from("write /dev/null /extent-native\n");
    for logical in (0..16).step_by(2) {
        commands.push_str(&format!("fallocate /extent-native {logical} {logical}\n"));
    }
    commands.push_str("set_inode_field /extent-native size 65536\nstat /extent-native\n");
    std::fs::write(&commands_path, commands).unwrap();
    let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
    let output = std::process::Command::new(debugfs)
        .args(["-w", "-f", &commands_path, &image_path])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stat = String::from_utf8_lossy(&output.stdout);
    let number = stat
        .lines()
        .find_map(|line| {
            line.strip_prefix("Inode:")?
                .split_whitespace()
                .next()?
                .parse::<u32>()
                .ok()
        })
        .expect("debugfs inode number");
    let img = std::fs::read(&image_path).unwrap();
    let (sb, group, uuid_seed) = metadata(&img);
    let raw = inode_bytes(&img, group.inode_table, number);
    let inode_seed = core::inode::inode_seed(uuid_seed, number, le32(raw, 100));
    let root = extent_node::parse_inline_root(&raw[40..100], sb.blocks() as u64).unwrap();
    let (entries, _, depth) = root.header_fields();
    assert_eq!(
        depth, 1,
        "eight separated logical extents require an external leaf"
    );
    assert!(entries > 0);
    let source = Snapshot::from_bytes(&img);
    let mut logicals = Vec::new();
    for index in 0..entries as usize {
        let entry = root.index_entry(index).unwrap();
        let block = source_block::capture(&source, entry.child, 4096).unwrap();
        let node = block
            .parse_extent_node(sb.blocks() as u64, BlockChecksum::Crc32c(inode_seed))
            .expect(
                "Linux extent-block checksum uses the UUID/inode/generation seed and eh_max domain",
            );
        let (count, _, child_depth) = node.header_fields();
        assert_eq!(child_depth, depth - 1);
        assert_eq!(node.leaf_extent(0).unwrap().info().logical, entry.logical);
        for ordinal in 0..count as usize {
            let span = node.leaf_extent(ordinal).unwrap();
            assert!(!span.info().initialized);
            for logical in span.info().logical..span.info().logical + span.info().length {
                logicals.push(logical);
            }
        }
    }
    assert_eq!(logicals, (0..16).step_by(2).collect::<Vec<u32>>());
    assert!(
        core::allocation::parse(source).is_none(),
        "local wide-node support must not silently widen the initial whole-image admission profile"
    );
}

#[test]
fn codecs_handle_extremes_and_crc_streaming() {
    for v in [0, 1, 255, 256, 65535, 65536, 0x89abcdef, u32::MAX] {
        assert_eq!(
            core::bytes::read_le32(&core::bytes::encode_le32(v), 0),
            Some(v)
        );
        assert_eq!(
            core::bytes::read_be32(&core::bytes::encode_be32(v), 0),
            Some(v)
        );
    }
    for o in [0, 1, 2, usize::MAX - 1, usize::MAX] {
        assert!(core::bytes::read_le32(&[0; 3], o).is_none());
    }
    assert_eq!(core::bytes::checked_range(u64::MAX, 1, u64::MAX), None);
    assert_eq!(
        core::bytes::block_offset(u32::MAX - 1, u32::MAX, 4096),
        None
    );
    assert_eq!(!core::crc::crc32c(0xffffffff, b"123456789"), 0xe3069283);
    let a = core::crc::crc32c(0xffffffff, b"1234");
    assert_eq!(
        core::crc::crc32c(a, b"56789"),
        core::crc::crc32c(0xffffffff, b"123456789")
    );
}

#[test]
fn allocation_bitmaps_match_linux_counts_padding_and_checksum_ranges() {
    let img = image();
    let (sb, group, seed) = metadata(&img);
    let ipg = le32(&img[1024..2048], 40);
    let descriptor = &img[4096..4128];
    for (block, valid, meaningful, free_offset, checksum_offset) in [
        (group.block_bitmap, sb.blocks(), 32768, 12usize, 24usize),
        (group.inode_bitmap, ipg, ipg, 14usize, 26usize),
    ] {
        let raw = &img[block as usize * 4096..(block as usize + 1) * 4096];
        let free = core::bytes::read_le16(descriptor, free_offset).unwrap() as u32;
        let checksum = core::bytes::read_le16(descriptor, checksum_offset).unwrap();
        let bitmap = core::bitmap::parse(raw, valid, meaningful, free, checksum, seed)
            .expect("Linux initialized bitmap");
        assert_eq!(bitmap.entry_count(), valid);
        assert_eq!(bitmap.free_count(), free);
        let counted = (0..valid)
            .filter(|bit| !bitmap.is_set(*bit).unwrap())
            .count();
        assert_eq!(counted, free as usize);
        assert_eq!(bitmap.raw_image(), raw);
        assert!(bitmap.is_set(valid).is_none());
        assert!(bitmap.is_set(u32::MAX).is_none());
        assert!(core::bitmap::parse(raw, valid, meaningful, free + 1, checksum, seed).is_none());
        assert!(core::bitmap::parse(raw, valid, meaningful, free, checksum ^ 1, seed).is_none());
        let mut bad = raw.to_vec();
        bad[valid as usize / 8] &= !(1u8 << (valid % 8));
        let checksum = (core::crc::crc32c(seed, &bad[..meaningful as usize / 8]) & 0xffff) as u16;
        assert!(
            core::bitmap::parse(&bad, valid, meaningful, free, checksum, seed).is_none(),
            "a valid checksum does not permit an unallocated padding bit"
        );
    }
    assert_eq!(core::bitmap::read_bit(&[0x81], 0), Some(true));
    assert_eq!(core::bitmap::read_bit(&[0x81], 1), Some(false));
    assert_eq!(core::bitmap::read_bit(&[0x81], 7), Some(true));
    assert_eq!(core::bitmap::read_bit(&[0x81], 8), None);
    assert_eq!(core::bitmap::read_bit(&[], u32::MAX), None);
    assert!(core::bitmap::parse(&[0xff; 4096], 0, 0, 0, 0, seed).is_none());
    assert!(core::bitmap::parse(&[0xff; 4096], 1, 32769, 0, 0, seed).is_none());
}

#[test]
fn block_claims_reject_aliases_without_partial_changes_and_match_allocation_bits() {
    use core::block_claims::{Census, Claim};
    let metadata = |start, length, kind| Claim {
        start,
        length,
        kind,
        inode: 0,
        generation: 0,
        logical: 0,
        initialized: false,
    };
    let data = |start, length, inode, logical, kind, initialized| Claim {
        start,
        length,
        kind,
        inode,
        generation: 17,
        logical,
        initialized,
    };
    assert!(Census::new(0).is_none());
    assert!(Census::new(2).is_none());
    assert!(Census::new(core::block_claims::MAX_BLOCKS + 1).is_none());
    let mut census = Census::new(64).unwrap();
    for claim in [
        metadata(0, 2, 1),
        metadata(2, 2, 3),
        metadata(8, 8, 2),
        data(4, 4, 12, 0, 4, true),
        data(16, 2, 2, 0, 5, true),
        data(63, 1, 13, u32::MAX, 4, true),
    ] {
        census = census.claim(claim).ok().expect("disjoint candidate ranges");
    }
    assert_eq!(census.role_of(0).unwrap().kind, 1);
    assert_eq!(census.role_of(3).unwrap().kind, 3);
    assert_eq!(census.role_of(8).unwrap().kind, 2);
    assert_eq!(census.role_of(7).unwrap().logical, 3);
    assert_eq!(census.role_of(63).unwrap().logical, u32::MAX);
    assert!(census.role_of(64).is_none());
    for bad in [
        data(6, 2, 12, 10, 4, true),
        data(5, 2, 13, 0, 4, true),
        data(20, 44, 13, 0, 4, true),
        data(20, 2, 13, u32::MAX, 4, true),
        data(20, 1, 2, 2, 5, false),
        metadata(63, 2, 3),
        metadata(u32::MAX, u32::MAX, 1),
    ] {
        census = census
            .claim(bad)
            .err()
            .expect("invalid or overlapping range");
        assert_eq!(census.role_of(20).unwrap().kind, 0);
        assert_eq!(census.role_of(6).unwrap().logical, 2);
        assert_eq!(census.role_of(63).unwrap().inode, 13);
    }
    let mut raw = vec![0xffu8; 4096];
    raw[..8].fill(0);
    for bit in 0..18 {
        raw[bit / 8] |= 1u8 << (bit % 8);
    }
    raw[7] |= 0x80;
    let checksum = (core::crc::crc32c(17, &raw) & 0xffff) as u16;
    let bitmap = core::bitmap::parse(&raw, 64, 32768, 45, checksum, 17).unwrap();
    assert!(census.matches_bitmap(0, &bitmap));
    assert!(!census.matches_bitmap(1, &bitmap));
    for (bit, allocate, free) in [(20usize, true, 44), (5, false, 46)] {
        let mut corrupt = raw.clone();
        if allocate {
            corrupt[bit / 8] |= 1u8 << (bit % 8);
        } else {
            corrupt[bit / 8] &= !(1u8 << (bit % 8));
        }
        let checksum = (core::crc::crc32c(17, &corrupt) & 0xffff) as u16;
        let bitmap = core::bitmap::parse(&corrupt, 64, 32768, free, checksum, 17).unwrap();
        assert!(
            !census.matches_bitmap(0, &bitmap),
            "checksummed allocation/ownership disagreement"
        );
    }
    let raw = [0xffu8; 4096];
    let checksum = (core::crc::crc32c(17, &raw) & 0xffff) as u16;
    let allocated = core::bitmap::parse(&raw, 16, 32768, 0, checksum, 17).unwrap();
    assert!(census.matches_bitmap(0, &allocated));
    assert!(!census.matches_bitmap(16, &allocated));
}

#[test]
fn checked_inode_extents_bind_census_ownership_and_reject_checksummed_aliases() {
    use core::block_claims::Census;
    fn base(img: &[u8], directories: bool) -> Census {
        let (sb, group, seed) = metadata(img);
        let census = core::group_claims::reserve(
            Census::new(sb.blocks()).unwrap(),
            &img[4096..4128],
            0,
            sb.blocks(),
            le32(&img[1024..2048], 40),
            seed,
        )
        .unwrap();
        let (mut census, _) = core::inode_claims::reserve_journal(
            census,
            inode_bytes(img, group.inode_table, 8),
            sb.inodes(),
            sb.blocks(),
            seed,
        )
        .unwrap();
        if directories {
            for number in [2, 11] {
                census = core::inode_claims::collect(
                    census,
                    inode_bytes(img, group.inode_table, number),
                    number,
                    sb.inodes(),
                    sb.blocks(),
                    seed,
                )
                .unwrap();
            }
        }
        census
    }
    fn checksum_inode(raw: &mut [u8], number: u32, seed: u32) {
        let checksum = core::inode::calculated_checksum(raw, number, seed).unwrap();
        raw[124..126].copy_from_slice(&(checksum as u16).to_le_bytes());
        raw[130..132].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
    }
    let img = image();
    let (sb, group, seed) = metadata(&img);
    assert_eq!(
        sb.groups(),
        1,
        "the controlled compatibility fixture has one group"
    );
    let raw = inode_bytes(&img, group.inode_table, 12);
    let file = core::inode::parse(raw, 12, sb.inodes(), sb.blocks(), seed).unwrap();
    let data = first_data_block(raw, sb.blocks());
    let census =
        core::inode_claims::collect(base(&img, true), raw, 12, sb.inodes(), sb.blocks(), seed)
            .unwrap();
    let role = census.role_of(data).unwrap();
    assert_eq!(
        (role.kind, role.inode, role.generation, role.logical),
        (4, 12, file.generation, 0)
    );
    let bitmap_raw =
        &img[group.block_bitmap as usize * 4096..(group.block_bitmap as usize + 1) * 4096];
    let bitmap = core::bitmap::parse(
        bitmap_raw,
        sb.blocks(),
        32768,
        core::bytes::read_le16(&img[4096..4128], 12).unwrap() as u32,
        core::bytes::read_le16(&img[4096..4128], 24).unwrap(),
        seed,
    )
    .unwrap();
    assert!(
        census.matches_bitmap(0, &bitmap),
        "every allocated fixture block has exactly one decoded claim"
    );
    let root_data = first_data_block(inode_bytes(&img, group.inode_table, 2), sb.blocks());
    let mut alias = raw.to_vec();
    alias[60..64].copy_from_slice(&root_data.to_le_bytes());
    checksum_inode(&mut alias, 12, seed);
    assert!(core::inode::parse(&alias, 12, sb.inodes(), sb.blocks(), seed).is_some());
    assert!(
        core::inode_claims::collect(base(&img, true), &alias, 12, sb.inodes(), sb.blocks(), seed)
            .is_none()
    );
    let mut accounting = raw.to_vec();
    let sectors = le32(&accounting, 28);
    accounting[28..32].copy_from_slice(&(sectors + 8).to_le_bytes());
    checksum_inode(&mut accounting, 12, seed);
    assert!(core::inode::parse(&accounting, 12, sb.inodes(), sb.blocks(), seed).is_some());
    assert!(
        core::inode_claims::collect(
            base(&img, true),
            &accounting,
            12,
            sb.inodes(),
            sb.blocks(),
            seed
        )
        .is_none()
    );
    let mut unwritten_directory = inode_bytes(&img, group.inode_table, 2).to_vec();
    let length = core::bytes::read_le16(&unwritten_directory, 56).unwrap();
    unwritten_directory[56..58].copy_from_slice(&(length + 32768).to_le_bytes());
    checksum_inode(&mut unwritten_directory, 2, seed);
    assert!(core::inode::parse(&unwritten_directory, 2, sb.inodes(), sb.blocks(), seed).is_some());
    assert!(
        core::inode_claims::collect(
            base(&img, false),
            &unwritten_directory,
            2,
            sb.inodes(),
            sb.blocks(),
            seed
        )
        .is_none()
    );
    assert!(
        core::inode_claims::collect(
            base(&img, false),
            inode_bytes(&img, group.inode_table, 8),
            8,
            sb.inodes(),
            sb.blocks(),
            seed
        )
        .is_none(),
        "the journal is not regular file data"
    );
}

#[test]
fn sparse_super_and_group_metadata_claims_cover_the_bounded_profile() {
    use core::block_claims::{Census, Claim};
    fn descriptor_for(img: &[u8], number: u32, seed: u32) -> Vec<u8> {
        let mut descriptor = img[4096..4128].to_vec();
        for offset in [0usize, 4, 8] {
            let relative = le32(&descriptor, offset);
            descriptor[offset..offset + 4]
                .copy_from_slice(&(number * 32768 + relative).to_le_bytes());
        }
        checksum(&mut descriptor, number, seed);
        descriptor
    }
    fn checksum(descriptor: &mut [u8], number: u32, seed: u32) {
        let seed = core::crc::crc32c(seed, &number.to_le_bytes());
        let prefix = core::crc::crc32c(seed, &descriptor[..30]);
        let value = (core::crc::crc32c(prefix, &[0u8, 0u8]) & 0xffff) as u16;
        descriptor[30..32].copy_from_slice(&value.to_le_bytes());
    }
    fn power(mut number: u32, base: u32) -> bool {
        while number > 1 && number % base == 0 {
            number /= base;
        }
        number == 1
    }
    let img = image();
    let (sb, _, seed) = metadata(&img);
    let ipg = le32(&img[1024..2048], 40);
    let mut census = Census::new(core::block_claims::MAX_BLOCKS).unwrap();
    for number in 0..32u32 {
        let expected = number <= 1 || power(number, 3) || power(number, 5) || power(number, 7);
        assert_eq!(core::group_claims::backup_group(number), Some(expected));
        let descriptor = descriptor_for(&img, number, seed);
        census = core::group_claims::reserve(
            census,
            &descriptor,
            number,
            core::block_claims::MAX_BLOCKS,
            ipg,
            seed,
        )
        .unwrap();
    }
    for number in 0..32u32 {
        let backup = core::group_claims::backup_group(number).unwrap();
        assert_eq!(
            census.role_of(number * 32768).unwrap().kind,
            if backup { 1 } else { 0 }
        );
        assert_eq!(
            census.role_of(number * 32768 + 1).unwrap().kind,
            if backup { 1 } else { 0 }
        );
        let descriptor = descriptor_for(&img, number, seed);
        assert_eq!(census.role_of(le32(&descriptor, 0)).unwrap().kind, 3);
        assert_eq!(census.role_of(le32(&descriptor, 4)).unwrap().kind, 3);
        assert_eq!(census.role_of(le32(&descriptor, 8)).unwrap().kind, 3);
    }
    assert!(core::group_claims::backup_group(32).is_none());
    assert!(core::group_claims::backup_group(81).is_none());
    let file = Claim {
        start: 3 * 32768,
        length: 1,
        kind: 4,
        inode: 12,
        generation: 1,
        logical: 0,
        initialized: true,
    };
    census = census
        .claim(file)
        .err()
        .expect("a backup superblock is not file data");
    assert_eq!(census.role_of(3 * 32768).unwrap().kind, 1);
    let mut alias = img[4096..4128].to_vec();
    alias[..4].copy_from_slice(&0u32.to_le_bytes());
    checksum(&mut alias, 0, seed);
    assert!(core::group::parse(&alias, 0, sb.blocks(), ipg, seed).is_some());
    assert!(
        core::group_claims::reserve(
            Census::new(sb.blocks()).unwrap(),
            &alias,
            0,
            sb.blocks(),
            ipg,
            seed
        )
        .is_none(),
        "checksummed metadata cannot alias the superblock"
    );
}

#[test]
fn group_index_binds_declared_metadata_and_aggregates_linux_counters() {
    use core::snapshot::Snapshot;
    let img = image();
    let (sb, group, seed) = metadata(&img);
    let ipg = le32(&img, 1064);
    let snapshot = Snapshot::from_bytes(&img);
    assert_eq!(snapshot.partition_bytes(), img.len() as u64);
    let primary = snapshot.block(0).unwrap();
    assert_eq!(primary.range(1024, 1024).unwrap(), &img[1024..2048]);
    assert!(primary.range(usize::MAX, 1).is_none());
    assert!(primary.range(1, usize::MAX).is_none());
    assert_eq!(primary.range(4096, 0), Some(&img[4096..4096]));
    assert!(snapshot.block(u32::MAX).is_none());
    let meta = core::group_metadata::parse(&snapshot, 0).unwrap();
    assert_eq!(meta.parameters(), (sb.blocks(), ipg, seed));
    assert_eq!(meta.descriptor(), &img[4096..4128]);
    assert_eq!(meta.info().inode_table, group.inode_table);
    let (allocation, inodes) = meta.bitmaps();
    for (bitmap, address) in [
        (allocation, group.block_bitmap),
        (inodes, group.inode_bitmap),
    ] {
        let start = address as usize * 4096;
        assert_eq!(bitmap.raw_image(), &img[start..start + 4096]);
    }
    assert!(core::group_metadata::parse(&snapshot, 1).is_none());
    assert!(core::group_metadata::parse(&snapshot, 32).is_none());
    let index = core::group_index::parse(snapshot).unwrap();
    assert_eq!(index.parameters(), (sb.blocks(), sb.inodes(), ipg, seed));
    assert_eq!(index.group_count(), 1);
    assert_eq!(index.get(0).unwrap().descriptor(), meta.descriptor());
    assert!(index.get(1).is_none());
    assert_eq!(index.source().partition_bytes(), img.len() as u64);
    for number in [1u32, 2, 8, 11, 12, sb.inodes()] {
        assert_eq!(
            core::inode_table::read(&index, number).unwrap(),
            inode_bytes(&img, group.inode_table, number)
        );
    }
    assert!(core::inode_table::read(&index, 0).is_none());
    assert!(core::inode_table::read(&index, sb.inodes() + 1).is_none());
    assert!(core::inode_table::read(&index, u32::MAX).is_none());
    for offset in [1036usize, 1040] {
        let mut bad = img.clone();
        let count = le32(&bad, offset);
        bad[offset..offset + 4].copy_from_slice(&(count + 1).to_le_bytes());
        let checksum = core::crc::crc32c(0xffffffff, &bad[1024..2044]);
        bad[2044..2048].copy_from_slice(&checksum.to_le_bytes());
        let source = Snapshot::from_bytes(&bad);
        assert!(core::group_metadata::parse(&source, 0).is_some());
        assert!(
            core::group_index::parse(source).is_none(),
            "valid checksums do not justify inconsistent global counters"
        );
    }
    let mut bad = img.clone();
    let start = group.inode_bitmap as usize * 4096;
    let spare = (sb.blocks() as usize - 1) * 4096;
    bad.copy_within(start..start + 4096, spare);
    bad[start..start + 4096].fill(0);
    assert!(
        core::group_metadata::parse(&Snapshot::from_bytes(&bad), 0).is_none(),
        "only the descriptor's declared address supplies the bitmap"
    );
    for length in [0usize, 4095, 4096] {
        assert!(core::group_index::parse(Snapshot::from_bytes(&img[..length])).is_none());
    }
}

#[test]
fn whole_allocation_rejects_checksummed_omissions_aliases_and_reserved_inode_storage() {
    use core::{allocation, snapshot::Snapshot};
    fn repair_counts_and_checksums(img: &mut [u8]) {
        let blocks = le32(img, 1028);
        let ipg = le32(img, 1064);
        let seed = core::crc::crc32c(0xffffffff, &img[1128..1144]);
        for (address_offset, valid, meaningful, free_offset, checksum_offset, total_offset) in [
            (
                4096usize, blocks, 4096usize, 4108usize, 4120usize, 1036usize,
            ),
            (4100, ipg, ipg as usize / 8, 4110, 4122, 1040),
        ] {
            let address = le32(img, address_offset) as usize * 4096;
            let raw = &img[address..address + 4096];
            let free = (0..valid)
                .filter(|&n| raw[n as usize / 8] & (1 << (n % 8)) == 0)
                .count() as u32;
            let checksum = (core::crc::crc32c(seed, &raw[..meaningful]) & 0xffff) as u16;
            img[free_offset..free_offset + 2].copy_from_slice(&(free as u16).to_le_bytes());
            img[checksum_offset..checksum_offset + 2].copy_from_slice(&checksum.to_le_bytes());
            img[total_offset..total_offset + 4].copy_from_slice(&free.to_le_bytes());
        }
        let group_seed = core::crc::crc32c(seed, &0u32.to_le_bytes());
        let prefix = core::crc::crc32c(group_seed, &img[4096..4126]);
        let checksum = (core::crc::crc32c(prefix, &[0, 0]) & 0xffff) as u16;
        img[4126..4128].copy_from_slice(&checksum.to_le_bytes());
        let checksum = core::crc::crc32c(0xffffffff, &img[1024..2044]);
        img[2044..2048].copy_from_slice(&checksum.to_le_bytes());
    }
    fn checksum_inode(img: &mut [u8], table: u32, number: u32, seed: u32) {
        let start = table as usize * 4096 + (number as usize - 1) * 256;
        let raw = &mut img[start..start + 256];
        let checksum = core::inode::calculated_checksum(raw, number, seed).unwrap();
        raw[124..126].copy_from_slice(&(checksum as u16).to_le_bytes());
        raw[130..132].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
    }
    fn rejected(img: &[u8], reason: &str) {
        assert!(core::group_index::parse(Snapshot::from_bytes(img)).is_some());
        assert!(
            allocation::parse(Snapshot::from_bytes(img)).is_none(),
            "{reason}"
        );
    }
    let img = image();
    let (sb, group, seed) = metadata(&img);
    let volume =
        allocation::parse(Snapshot::from_bytes(&img)).expect("complete fixture allocation");
    let census = volume.census();
    assert_eq!(census.block_count(), sb.blocks());
    assert_eq!(census.role_of(0).unwrap().kind, 1);
    assert_eq!(census.role_of(1).unwrap().kind, 1);
    assert_eq!(census.role_of(group.inode_table).unwrap().kind, 3);
    let root = first_data_block(inode_bytes(&img, group.inode_table, 2), sb.blocks());
    let payload = first_data_block(inode_bytes(&img, group.inode_table, 12), sb.blocks());
    assert_eq!(census.role_of(root).unwrap().kind, 5);
    assert_eq!(census.role_of(payload).unwrap().inode, 12);
    assert_eq!(census.role_of(payload).unwrap().kind, 4);
    let journal = first_data_block(inode_bytes(&img, group.inode_table, 8), sb.blocks());
    assert_eq!(census.role_of(journal).unwrap().kind, 2);
    assert!(!volume.journal().allows_target(journal));
    for number in [2u32, 8] {
        let mut bad = img.clone();
        let bit = number - 1;
        let address = group.inode_bitmap as usize * 4096 + bit as usize / 8;
        bad[address] &= !(1 << (bit % 8));
        repair_counts_and_checksums(&mut bad);
        rejected(&bad, "root and journal inode bitmap markers are mandatory");
    }
    for (offset, value) in [(0usize, 0x8000u16), (26, 1), (28, 8), (40, 1), (104, 1)] {
        let mut bad = img.clone();
        let start = group.inode_table as usize * 4096;
        bad[start + offset..start + offset + 2].copy_from_slice(&value.to_le_bytes());
        rejected(
            &bad,
            "unused reserved inodes cannot hide storage or a live object",
        );
    }
    for (offset, value) in [
        (4112usize, core::bytes::read_le16(&img, 4112).unwrap() + 1),
        (4124, le32(&img, 1064) as u16 - 11),
    ] {
        let mut bad = img.clone();
        bad[offset..offset + 2].copy_from_slice(&value.to_le_bytes());
        repair_counts_and_checksums(&mut bad);
        rejected(
            &bad,
            "directory counts and inode-table unused suffix must agree",
        );
    }
    let mut bad = img.clone();
    let start = group.inode_table as usize * 4096 + 256;
    bad[start..start + 2].copy_from_slice(&0x81edu16.to_le_bytes());
    checksum_inode(&mut bad, group.inode_table, 2, seed);
    rejected(&bad, "inode 2 must be a directory");
    let bitmap = group.block_bitmap as usize * 4096;
    let free = (0..sb.blocks())
        .find(|&b| img[bitmap + b as usize / 8] & (1 << (b % 8)) == 0)
        .unwrap();
    for (block, allocated) in [(free, true), (payload, false)] {
        let mut bad = img.clone();
        let byte = &mut bad[bitmap + block as usize / 8];
        if allocated {
            *byte |= 1 << (block % 8);
        } else {
            *byte &= !(1 << (block % 8));
        }
        repair_counts_and_checksums(&mut bad);
        rejected(
            &bad,
            "every allocated block has exactly its source-bound claim",
        );
    }
    let mut bad = img.clone();
    let start = group.inode_table as usize * 4096 + 11 * 256;
    bad[start + 60..start + 64].copy_from_slice(&journal.to_le_bytes());
    checksum_inode(&mut bad, group.inode_table, 12, seed);
    rejected(&bad, "a checksummed file cannot own journal blocks");
}

#[test]
fn initialized_reads_match_linux_bytes_and_holes_never_expose_backing_storage() {
    use core::{
        allocated_inode, allocation,
        file_read::{self, Chunk, Resolution},
        snapshot::Snapshot,
    };
    let img = image();
    let (sb, group, seed) = metadata(&img);
    let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
    for number in [0u32, 1, 8, 10, 13, sb.inodes(), u32::MAX] {
        assert!(allocated_inode::get(&volume, number).is_none());
    }
    let root = allocated_inode::get(&volume, 2).unwrap();
    assert_eq!(root.info().mode & 0xf000, 0x4000);
    let file = allocated_inode::get(&volume, 12).unwrap();
    assert_eq!(file.number(), 12);
    assert_eq!(file.raw(), inode_bytes(&img, group.inode_table, 12));
    assert_eq!(file.info().size, 8192);
    let first = first_data_block(file.raw(), sb.blocks());
    match file_read::resolve(&file, 0) {
        Resolution::Data(block) => assert_eq!(block, first),
        Resolution::Zero => panic!("initialized extent was lost"),
    }
    assert!(matches!(
        file_read::resolve(&file, u32::MAX),
        Resolution::Zero
    ));
    let mut actual = Vec::new();
    for offset in [0u64, 4096] {
        match file_read::chunk(&file, offset, usize::MAX) {
            Chunk::Data(bytes) => actual.extend_from_slice(bytes),
            _ => panic!("initialized source data was not returned"),
        }
    }
    assert_eq!(
        actual,
        (0..8192).map(|i| (i % 251) as u8).collect::<Vec<_>>()
    );
    for offset in [4095u64, 8191] {
        match file_read::chunk(&file, offset, usize::MAX) {
            Chunk::Data(bytes) => assert_eq!(bytes, &[(offset % 251) as u8]),
            _ => panic!("file or block boundary clipping failed"),
        }
    }
    assert!(matches!(file_read::chunk(&file, 0, 0), Chunk::End));
    for offset in [8192u64, u64::MAX] {
        assert!(matches!(
            file_read::chunk(&file, offset, usize::MAX),
            Chunk::End
        ));
    }
    for unwritten in [false, true] {
        let mut changed = img.clone();
        let start = group.inode_table as usize * 4096 + 11 * 256;
        let raw = &mut changed[start..start + 256];
        if unwritten {
            raw[56..58].copy_from_slice(&32770u16.to_le_bytes());
        } else {
            raw[52..56].copy_from_slice(&1u32.to_le_bytes());
        }
        let checksum = core::inode::calculated_checksum(raw, 12, seed).unwrap();
        raw[124..126].copy_from_slice(&(checksum as u16).to_le_bytes());
        raw[130..132].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
        let backing = first as usize * 4096;
        changed[backing..backing + 8192].fill(0xa5);
        let volume = allocation::parse(Snapshot::from_bytes(&changed)).unwrap();
        let file = allocated_inode::get(&volume, 12).unwrap();
        assert!(matches!(
            file_read::chunk(&file, 0, usize::MAX),
            Chunk::Zero(4096)
        ));
        match file_read::chunk(&file, 4096, usize::MAX) {
            Chunk::Zero(4096) if unwritten => {}
            Chunk::Data(bytes) if !unwritten => assert_eq!(bytes, &[0xa5; 4096]),
            _ => panic!("hole/unwritten mapping exposed incorrect storage"),
        }
        assert!(matches!(
            file_read::chunk(&file, 8192, usize::MAX),
            Chunk::End
        ));
    }
}

#[test]
fn complete_directory_blocks_cover_every_record_and_reject_malformed_suffixes() {
    let img = image();
    let (sb, group, seed) = metadata(&img);
    let inode = core::inode::parse(
        inode_bytes(&img, group.inode_table, 2),
        2,
        sb.inodes(),
        sb.blocks(),
        seed,
    )
    .unwrap();
    let physical = first_data_block(inode_bytes(&img, group.inode_table, 2), sb.blocks());
    let start = physical as usize * 4096;
    let raw = &img[start..start + 4096];
    let seed = core::inode::inode_seed(seed, 2, inode.generation);
    let block = core::directory_block::parse(raw, sb.inodes(), seed).unwrap();
    let mut end = 0usize;
    let mut names = Vec::new();
    for i in 0..block.len() {
        let entry = block.get(i).unwrap();
        assert_eq!(entry.name_offset, end + 8);
        end = entry.next;
        if entry.inode != 0 {
            names.push(block.name(i).unwrap().to_vec());
        }
    }
    assert_eq!(end, 4084);
    assert_eq!(
        names,
        [
            b".".to_vec(),
            b"..".to_vec(),
            b"lost+found".to_vec(),
            b"payload".to_vec()
        ]
    );
    assert!(block.get(usize::MAX).is_none());
    assert!(block.name(usize::MAX).is_none());
    assert!(core::directory_block::parse(raw, sb.inodes(), seed ^ 1).is_none());
    for offset in [4usize, block.get(0).unwrap().next + 4, 8] {
        let mut bad = raw.to_vec();
        bad[offset..offset + 2].fill(0);
        let checksum = core::crc::crc32c(seed, &bad[..4084]);
        bad[4092..4096].copy_from_slice(&checksum.to_le_bytes());
        assert!(core::directory::valid_tail(&bad, seed));
        assert!(core::directory_block::parse(&bad, sb.inodes(), seed).is_none());
    }
}

#[test]
fn directory_reads_bind_the_inode_generation_and_reject_holes() {
    use core::{allocated_inode, allocation, directory_file, snapshot::Snapshot};
    let img = image();
    let (sb, group, seed) = metadata(&img);
    let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
    let root = allocated_inode::get(&volume, 2).unwrap();
    let block = directory_file::read(&root, 0).unwrap();
    assert_eq!(block.name(0), Some(&b"."[..]));
    assert!(directory_file::read(&root, 1).is_none());
    let file = allocated_inode::get(&volume, 12).unwrap();
    assert!(directory_file::read(&file, 0).is_none());
    let lost = allocated_inode::get(&volume, 11).unwrap();
    for logical in 0..lost.info().size / 4096 {
        assert!(directory_file::read(&lost, logical).is_some());
    }
    for generation in [false, true] {
        let mut changed = img.clone();
        let start = group.inode_table as usize * 4096 + 256;
        let raw = &mut changed[start..start + 256];
        if generation {
            raw[100..104].copy_from_slice(&123u32.to_le_bytes());
        } else {
            raw[52..56].copy_from_slice(&1u32.to_le_bytes());
        }
        let checksum = core::inode::calculated_checksum(raw, 2, seed).unwrap();
        raw[124..126].copy_from_slice(&(checksum as u16).to_le_bytes());
        raw[130..132].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
        let volume = allocation::parse(Snapshot::from_bytes(&changed)).unwrap();
        let root = allocated_inode::get(&volume, 2).unwrap();
        assert!(directory_file::read(&root, 0).is_none());
    }
    assert!(allocated_inode::get(&volume, sb.inodes() + 1).is_none());
}

#[test]
fn directory_name_sets_compare_full_keys_own_bytes_and_bound_hash_collisions() {
    use core::name_set::NameSet;
    let mut names = NameSet::new();
    names = names.insert(2, b"alpha").ok().unwrap();
    names = names.insert(11, b"alpha").ok().unwrap();
    assert_eq!(names.len(), 2);
    assert_eq!(names.find(2, b"alpha"), Some(0));
    assert_eq!(names.find(11, b"alpha"), Some(1));
    assert!(names.contains(2, b"alpha") && names.contains(11, b"alpha"));
    names = names
        .insert(2, b"alpha")
        .err()
        .expect("duplicate directory/name");
    assert_eq!(names.len(), 2);
    let mut input = b"immutable".to_vec();
    names = names.insert(2, &input).ok().unwrap();
    input[0] = b'X';
    assert!(names.contains(2, b"immutable"));
    assert!(!names.contains(2, &input));
    names = names.insert(2, &[0xff, 0x80]).ok().unwrap();
    names = names.insert(2, &[b'x'; 255]).ok().unwrap();
    for (directory, name) in [
        (0u32, &b"alpha"[..]),
        (2, &b""[..]),
        (2, &b"a/b"[..]),
        (2, &b"a\0b"[..]),
        (2, &[b'x'; 256][..]),
    ] {
        let before = names.len();
        names = names.insert(directory, name).err().expect("invalid key");
        assert_eq!(names.len(), before);
        assert!(!names.contains(directory, name));
    }
    let mut colliding = Vec::new();
    for index in 0..1_000_000u32 {
        let name = format!("collision-{index:08x}").into_bytes();
        if core::crc::crc32c(2, &name) % 4096 == 0 {
            colliding.push(name);
        }
        if colliding.len() == 65 {
            break;
        }
    }
    assert_eq!(colliding.len(), 65);
    let mut names = NameSet::new();
    for key in &colliding[..64] {
        names = names
            .insert(2, key)
            .ok()
            .expect("distinct keys with equal hashes");
    }
    assert_eq!(names.len(), 64);
    names = names
        .insert(2, &colliding[64])
        .err()
        .expect("bounded collision work");
    assert_eq!(names.len(), 64);
    assert!(!names.contains(2, &colliding[64]));
    for key in &colliding[..64] {
        assert!(names.contains(2, key));
    }
    for (position, key) in colliding[..64].iter().enumerate() {
        assert_eq!(names.find(2, key), Some(position as u32));
    }
}

#[test]
fn directory_index_enumerates_empty_blocks_and_rejects_bad_targets_and_duplicate_names() {
    use core::{
        allocated_inode, allocation, directory_file, directory_index, file_read, snapshot::Snapshot,
    };
    let img = image();
    let (_, group, seed) = metadata(&img);
    let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
    let index = directory_index::build(&volume).unwrap();
    assert_eq!(index.len(), 6);
    let root_blocks = le32(inode_bytes(&img, group.inode_table, 2), 4) / 4096;
    let lost_blocks = le32(inode_bytes(&img, group.inode_table, 11), 4) / 4096;
    assert!(
        lost_blocks > 1,
        "fixture includes empty preallocated directory blocks"
    );
    assert_eq!(index.block_count(), root_blocks + lost_blocks);
    for (directory, name, target, kind) in [
        (2u32, &b"."[..], 2u32, 2u8),
        (2, &b".."[..], 2, 2),
        (2, &b"lost+found"[..], 11, 2),
        (2, &b"payload"[..], 12, 1),
        (11, &b"."[..], 11, 2),
        (11, &b".."[..], 2, 2),
    ] {
        let entry = index.lookup(directory, name).unwrap();
        let identity = entry.identity();
        assert_eq!(
            (identity.0, identity.1, identity.3),
            (directory, target, kind)
        );
        assert_eq!(entry.name(), name);
    }
    assert!(index.get(index.len()).is_none());
    assert!(index.lookup(0, b"payload").is_none());
    assert!(index.lookup(2, b"Payload").is_none());
    assert!(index.lookup(11, b"missing").is_none());
    let root = allocated_inode::get(&volume, 2).unwrap();
    let raw = directory_file::read(&root, 0).unwrap();
    let payload_record = (0..raw.len())
        .find(|&i| raw.name(i) == Some(&b"payload"[..]))
        .unwrap();
    let record = raw.get(payload_record).unwrap().name_offset - 8;
    let root_block = first_data_block(root.raw(), volume.census().block_count()) as usize * 4096;
    let root_seed = core::inode::inode_seed(seed, 2, root.info().generation);
    for variant in 0..6u8 {
        let mut bad = img.clone();
        let block = &mut bad[root_block..root_block + 4096];
        match variant {
            0 => block[record..record + 4].copy_from_slice(&13u32.to_le_bytes()),
            1 => block[record..record + 4].copy_from_slice(&8u32.to_le_bytes()),
            2 => block[record + 7] = 2,
            3 => {
                block[record + 6] = 10;
                block[record + 8..record + 18].copy_from_slice(b"lost+found");
            }
            _ => {}
        }
        let checksum = core::crc::crc32c(root_seed, &block[..4084]);
        block[4092..4096].copy_from_slice(&checksum.to_le_bytes());
        if variant == 4 {
            let lost = allocated_inode::get(&volume, 11).unwrap();
            let logical = lost.info().size / 4096 - 1;
            let physical = match file_read::resolve(&lost, logical) {
                file_read::Resolution::Data(b) => b,
                _ => panic!("lost+found mapping"),
            };
            bad[physical as usize * 4096 + 4092] ^= 0x80;
        }
        if variant == 5 {
            let start = group.inode_table as usize * 4096 + 10 * 256;
            let raw = &mut bad[start..start + 256];
            raw[4..8].copy_from_slice(&(4097u32 * 4096).to_le_bytes());
            let checksum = core::inode::calculated_checksum(raw, 11, seed).unwrap();
            raw[124..126].copy_from_slice(&(checksum as u16).to_le_bytes());
            raw[130..132].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
        }
        let volume = allocation::parse(Snapshot::from_bytes(&bad)).unwrap();
        assert!(
            directory_index::build(&volume).is_none(),
            "variant {variant}"
        );
    }
}

#[test]
fn namespace_checks_links_parents_and_cycles_and_allows_regular_file_hard_links() {
    use core::{
        allocated_inode, allocation, directory_file, directory_index, namespace, snapshot::Snapshot,
    };
    fn seal_inode(img: &mut [u8], table: u32, n: u32, seed: u32) {
        let start = table as usize * 4096 + (n as usize - 1) * 256;
        let raw = &mut img[start..start + 256];
        let checksum = core::inode::calculated_checksum(raw, n, seed).unwrap();
        raw[124..126].copy_from_slice(&(checksum as u16).to_le_bytes());
        raw[130..132].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
    }
    fn links(img: &mut [u8], table: u32, n: u32, value: u16, seed: u32) {
        let offset = table as usize * 4096 + (n as usize - 1) * 256 + 26;
        img[offset..offset + 2].copy_from_slice(&value.to_le_bytes());
        seal_inode(img, table, n, seed);
    }
    fn seal_directory(img: &mut [u8], table: u32, n: u32, physical: u32, seed: u32) {
        let generation = le32(inode_bytes(img, table, n), 100);
        let seed = core::inode::inode_seed(seed, n, generation);
        let start = physical as usize * 4096;
        let raw = &mut img[start..start + 4096];
        let checksum = core::crc::crc32c(seed, &raw[..4084]);
        raw[4092..4096].copy_from_slice(&checksum.to_le_bytes());
    }
    fn add_after(block: &mut [u8], at: usize, target: u32, kind: u8, name: &[u8]) {
        let minimum = (8 + block[at + 6] as usize + 3) / 4 * 4;
        let next = at + minimum;
        block[at + 4..at + 6].copy_from_slice(&(minimum as u16).to_le_bytes());
        block[next..4084].fill(0);
        block[next..next + 4].copy_from_slice(&target.to_le_bytes());
        block[next + 4..next + 6].copy_from_slice(&((4084 - next) as u16).to_le_bytes());
        block[next + 6] = name.len() as u8;
        block[next + 7] = kind;
        block[next + 8..next + 8 + name.len()].copy_from_slice(name);
    }
    let img = image();
    let (sb, group, seed) = metadata(&img);
    let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
    let index = directory_index::build(&volume).unwrap();
    let valid = namespace::validate(&index).expect("native rooted namespace");
    assert_eq!(valid.parent(2), Some(2));
    assert_eq!(valid.parent(11), Some(2));
    assert_eq!(valid.depth(2), Some(0));
    assert_eq!(valid.depth(11), Some(1));
    assert_eq!(valid.parent(12), None);
    assert_eq!(valid.depth(u32::MAX), None);
    assert_eq!(valid.lookup(2, b"payload").unwrap().identity().1, 12);
    let root = allocated_inode::get(&volume, 2).unwrap();
    let lost = allocated_inode::get(&volume, 11).unwrap();
    let root_records = directory_file::read(&root, 0).unwrap();
    let record = |name: &[u8]| {
        let i = (0..root_records.len())
            .find(|&i| root_records.name(i) == Some(name))
            .unwrap();
        root_records.get(i).unwrap().name_offset - 8
    };
    let payload_at = record(b"payload");
    let lost_at = record(b"lost+found");
    let root_physical = first_data_block(root.raw(), sb.blocks());
    let lost_physical = first_data_block(lost.raw(), sb.blocks());
    let root_start = root_physical as usize * 4096;
    let lost_start = lost_physical as usize * 4096;
    for variant in 0..7u8 {
        let mut changed = img.clone();
        match variant {
            0 => links(&mut changed, group.inode_table, 12, 2, seed),
            1 => links(&mut changed, group.inode_table, 2, 4, seed),
            2 => changed[lost_start + 12..lost_start + 16].copy_from_slice(&11u32.to_le_bytes()),
            3 => changed[root_start..root_start + 4].copy_from_slice(&11u32.to_le_bytes()),
            4 => {
                add_after(
                    &mut changed[root_start..root_start + 4096],
                    payload_at,
                    11,
                    2,
                    b"alias",
                );
                links(&mut changed, group.inode_table, 11, 3, seed);
            }
            5 => changed[root_start + payload_at..root_start + payload_at + 4].fill(0),
            6 => {
                changed[root_start + 6] = 2;
                changed[root_start + 8..root_start + 10].copy_from_slice(b"..");
                changed[root_start + 18] = 1;
                changed[root_start + 20] = b'.';
            }
            _ => unreachable!(),
        }
        seal_directory(&mut changed, group.inode_table, 2, root_physical, seed);
        seal_directory(&mut changed, group.inode_table, 11, lost_physical, seed);
        let volume = allocation::parse(Snapshot::from_bytes(&changed)).unwrap();
        let index = directory_index::build(&volume).unwrap();
        assert!(
            namespace::validate(&index).is_none(),
            "namespace variant {variant}"
        );
    }
    let mut changed = img.clone();
    add_after(
        &mut changed[root_start..root_start + 4096],
        payload_at,
        12,
        1,
        b"alias",
    );
    links(&mut changed, group.inode_table, 12, 2, seed);
    seal_directory(&mut changed, group.inode_table, 2, root_physical, seed);
    let volume = allocation::parse(Snapshot::from_bytes(&changed)).unwrap();
    let index = directory_index::build(&volume).unwrap();
    let valid = namespace::validate(&index).expect("regular file hard links are allowed");
    assert_eq!(valid.lookup(2, b"alias").unwrap().identity().1, 12);
    assert_eq!(valid.lookup(2, b"payload").unwrap().identity().1, 12);
    let mut cycle = img.clone();
    cycle[root_start + lost_at..root_start + lost_at + 4].fill(0);
    cycle[lost_start + 12..lost_start + 16].copy_from_slice(&11u32.to_le_bytes());
    add_after(
        &mut cycle[lost_start..lost_start + 4096],
        12,
        11,
        2,
        b"loop",
    );
    links(&mut cycle, group.inode_table, 2, 2, seed);
    links(&mut cycle, group.inode_table, 11, 3, seed);
    seal_directory(&mut cycle, group.inode_table, 2, root_physical, seed);
    seal_directory(&mut cycle, group.inode_table, 11, lost_physical, seed);
    let volume = allocation::parse(Snapshot::from_bytes(&cycle)).unwrap();
    let index = directory_index::build(&volume).unwrap();
    assert!(index.lookup(2, b"lost+found").is_none());
    assert_eq!(index.lookup(11, b"..").unwrap().identity().1, 11);
    assert_eq!(index.lookup(11, b"loop").unwrap().identity().1, 11);
    assert_eq!(
        (0..index.len())
            .filter(|&i| index.get(i).unwrap().identity().1 == 11)
            .count(),
        3
    );
    assert!(
        namespace::validate(&index).is_none(),
        "locally consistent disconnected cycle"
    );
}

#[test]
fn linux_metadata_checksums_and_directory_records_interoperate() {
    let img = image();
    let (sb, g, seed) = metadata(&img);
    assert_eq!(sb.journal_inode(), 8);
    assert!(!sb.needs_recovery());
    let raw = inode_bytes(&img, g.inode_table, 2);
    let root = core::inode::parse(raw, 2, sb.inodes(), sb.blocks(), seed)
        .expect("Linux root inode checksum");
    let block = first_data_block(raw, sb.blocks());
    let dir = &img[block as usize * 4096..(block as usize + 1) * 4096];
    let inode_seed = core::inode::inode_seed(seed, 2, root.generation);
    assert!(core::directory::valid_tail(dir, inode_seed));
    let mut offset = 0;
    let mut names = Vec::new();
    let mut file_inode = 0;
    while offset < 4084 {
        let e = core::directory::parse(dir, offset, sb.inodes()).expect("Linux linear dirent");
        assert!(e.next > offset);
        if e.inode != 0 {
            let name = &dir[e.name_offset..e.name_offset + e.name_length as usize];
            names.push(name.to_vec());
            if name == b"payload" {
                file_inode = e.inode;
            }
        }
        offset = e.next;
    }
    assert_eq!(offset, 4084);
    for name in [b".".as_slice(), b"..", b"lost+found", b"payload"] {
        assert!(names.iter().any(|n| n == name));
    }
    assert!(file_inode >= 11);
    let file_raw = inode_bytes(&img, g.inode_table, file_inode);
    let file = core::inode::parse(file_raw, file_inode, sb.inodes(), sb.blocks(), seed).unwrap();
    assert_eq!(file.size, 8192);
    let data = first_data_block(file_raw, sb.blocks());
    assert_eq!(
        &img[data as usize * 4096..data as usize * 4096 + 8192],
        std::fs::read("build/fixture-file.bin").unwrap()
    );
    let journal_raw = inode_bytes(&img, g.inode_table, 8);
    let journal_inode = core::inode::parse(journal_raw, 8, sb.inodes(), sb.blocks(), seed).unwrap();
    let journal_block = first_data_block(journal_raw, sb.blocks());
    let journal = &img[journal_block as usize * 4096..journal_block as usize * 4096 + 1024];
    let j = core::journal_superblock::parse(journal, &img[1128..1144], journal_inode.size / 4096)
        .unwrap();
    assert_eq!(j.start, 0);
    assert_eq!(j.uuid_seed, seed);
    // Clean mke2fs journals do not yet have the CSUM_V3 feature enabled.
    assert!(!j.csum_v3);
}

#[test]
fn malformed_media_and_unsupported_features_are_rejected() {
    let img = image();
    for n in [0, 1, 56, 88, 1020, 1023] {
        assert!(core::superblock::parse(&img[1024..1024 + n], img.len() as u64).is_none());
    }
    let mut sb = img[1024..2048].to_vec();
    // Give the unsupported feature a correct checksum: rejection must be a
    // profile decision, not an accidental checksum failure.
    sb[96] |= 0x80; // 64BIT
    let checksum = core::crc::crc32c(0xffffffff, &sb[..1020]);
    sb[1020..1024].copy_from_slice(&checksum.to_le_bytes());
    assert!(core::superblock::parse(&sb, img.len() as u64).is_none());
    let (s, g, seed) = metadata(&img);
    let mut ino = inode_bytes(&img, g.inode_table, 2).to_vec();
    ino[4] ^= 1;
    assert!(core::inode::parse(&ino, 2, s.inodes(), s.blocks(), seed).is_none());
    let mut bad = vec![0u8; 4096];
    bad[0..4].copy_from_slice(&2u32.to_le_bytes());
    bad[4..6].copy_from_slice(&12u16.to_le_bytes());
    bad[6] = 1;
    bad[7] = 1;
    bad[8] = b'/';
    assert!(core::directory::parse(&bad, 0, s.inodes()).is_none());
    bad[8] = b'a';
    assert!(core::directory::parse(&bad, 0, s.inodes()).is_some());
    bad[4..6].copy_from_slice(&0u16.to_le_bytes());
    assert!(core::directory::parse(&bad, 0, s.inodes()).is_none());
    assert!(core::directory::parse(&bad, usize::MAX, s.inodes()).is_none());
}

#[test]
fn extent_length_edges_and_unwritten_zero_semantics() {
    let e = core::extent::Extent {
        logical: 10,
        physical: 100,
        length: 32768,
        initialized: true,
    };
    let bytes = e.encode(65536).unwrap();
    assert_eq!(core::bytes::read_le16(&bytes, 4), Some(32768));
    let decoded = core::extent::parse(&bytes, 0, 65536).unwrap();
    assert!(decoded.initialized);
    let e = core::extent::Extent {
        logical: 10,
        physical: 100,
        length: 32767,
        initialized: false,
    };
    let bytes = e.encode(65536).unwrap();
    assert_eq!(core::bytes::read_le16(&bytes, 4), Some(65535));
    assert!(matches!(
        e.resolve(10, 65536),
        Some(core::extent::Mapping::Zero)
    ));
    assert!(e.resolve(9, 65536).is_none());
    let mut bad = bytes;
    bad[4..6].fill(0);
    assert!(core::extent::parse(&bad, 0, 65536).is_none());
    assert!(core::extent::parse(&bytes, usize::MAX, 65536).is_none());
    let overflow = core::extent::Extent {
        logical: u32::MAX,
        physical: 100,
        length: 2,
        initialized: true,
    };
    assert!(overflow.encode(65536).is_none());
    // Linux fs/ext4/extents.c: ext4_valid_extent rejects an exclusive end
    // wrapping to zero, including the terminal logical block with length 1.
    for length in [1, 2, 32768] {
        let valid = core::extent::Extent {
            logical: u32::MAX - length,
            physical: 100,
            length,
            initialized: true,
        };
        let mut encoded = valid.encode(65536).unwrap();
        assert!(core::extent::parse(&encoded, 0, 65536).is_some());
        let invalid = core::extent::Extent {
            logical: valid.logical + 1,
            ..valid
        };
        assert!(invalid.encode(65536).is_none());
        encoded[..4].copy_from_slice(&invalid.logical.to_le_bytes());
        assert!(core::extent::parse(&encoded, 0, 65536).is_none());
    }
    let mut root = [0u8; 60];
    root[0..2].copy_from_slice(&0xf30au16.to_le_bytes());
    root[2..4].copy_from_slice(&2u16.to_le_bytes());
    root[4..6].copy_from_slice(&4u16.to_le_bytes());
    root[12..24].copy_from_slice(&bytes);
    root[24..36].copy_from_slice(&bytes); // overlapping logical intervals
    assert!(core::extent::validate_inline_root(&root, 65536).is_none());
    root[6..8].copy_from_slice(&1u16.to_le_bytes());
    assert!(core::extent::validate_inline_root(&root, 65536).is_none());
}

#[test]
fn frozen_payload_has_no_source_alias_and_escape_roundtrips() {
    let mut input = vec![0x5au8; 4096];
    input[..4].copy_from_slice(&core::jbd2::MAGIC.to_be_bytes());
    let frozen = core::frozen::FrozenBlock::capture(&input).unwrap();
    input[100] = 0;
    assert_eq!(frozen.as_slice()[100], 0x5a);
    let (escaped, flag) = frozen.escape().unwrap();
    assert!(flag);
    assert_eq!(&escaped.as_slice()[..4], &[0u8; 4]);
    assert_eq!(escaped.restore(flag).unwrap().as_slice(), frozen.as_slice());
    assert!(core::frozen::FrozenBlock::capture(&input[..4095]).is_none());
    let seed = core::crc::crc32c(0xffffffff, &[1u8; 16]);
    let checksum = core::jbd2::payload_checksum(seed, 9, escaped.as_slice()).unwrap();
    let expected = core::crc::crc32c(
        core::crc::crc32c(seed, &9u32.to_be_bytes()),
        escaped.as_slice(),
    );
    assert_eq!(checksum, expected);
}

#[test]
fn jbd2_headers_tags_and_commit_checksum_use_linux_byte_order() {
    let header = core::jbd2::encode_header(2, 9).unwrap();
    let parsed = core::jbd2::parse_header(&header, 9).unwrap();
    assert_eq!(parsed.kind, 2);
    assert!(core::jbd2::parse_header(&header, 10).is_none());
    let tag = core::jbd2::Tag {
        block: 123,
        flags: 11,
        checksum: 0x12345678,
    };
    let bytes = core::jbd2::encode_tag(&tag, 1000).unwrap();
    let parsed = core::jbd2::parse_tag(&bytes, 0, 1000).unwrap();
    assert_eq!(
        (parsed.block, parsed.flags, parsed.checksum),
        (123, 11, 0x12345678)
    );
    let invalid = core::jbd2::Tag {
        block: 123,
        flags: 4,
        checksum: 0,
    };
    assert!(core::jbd2::encode_tag(&invalid, 1000).is_none());
    let seed = core::crc::crc32c(0xffffffff, &[1u8; 16]);
    let mut commit = vec![0u8; 4096];
    commit[..12].copy_from_slice(&header);
    let c = core::crc::crc32c_zero4(seed, &commit, 16).unwrap();
    commit[16..20].copy_from_slice(&c.to_be_bytes());
    assert!(core::jbd2::valid_commit(&commit, 9, seed));
    assert!(!core::jbd2::valid_commit(&commit, 10, seed));
    commit[100] ^= 1;
    assert!(!core::jbd2::valid_commit(&commit, 9, seed));
}

#[test]
fn reservations_do_not_alias_and_sequence_never_wraps() {
    for start in [1, 2, 500, 1023] {
        let mut used = std::collections::BTreeSet::new();
        for i in 0..1023 {
            let slot = core::ring::slot(1, 1024, start, i).unwrap();
            assert!((1..1024).contains(&slot));
            assert!(used.insert(slot));
        }
        assert!(core::ring::slot(1, 1024, start, 1023).is_none());
    }
    assert!(core::ring::reserve(250, 251).is_none());
    assert_eq!(core::ring::reserve(250, 252).unwrap().total, 252);
    assert_eq!(core::jbd2::next_sequence(u32::MAX), None);
    assert_eq!(core::jbd2::next_sequence(u32::MAX - 1), Some(u32::MAX));
    assert_eq!(core::jbd2::next_sequence(0), None);
}

#[test]
fn dac_owner_precedence_and_root_execute_rule() {
    let mut c = core::access::Credentials {
        fsuid: 42,
        in_inode_group: true,
        dac_override: false,
        dac_read_search: false,
    };
    assert!(!core::access::allowed(0o070, 42, &c, 4, false));
    assert!(core::access::allowed(0o070, 41, &c, 4, false));
    c.dac_override = true;
    assert!(core::access::allowed(0, 41, &c, 2, false));
    assert!(!core::access::allowed(0, 41, &c, 1, false));
    assert!(core::access::allowed(0o001, 41, &c, 1, false));
    c.dac_override = false;
    c.dac_read_search = true;
    assert!(core::access::allowed(0, 41, &c, 5, true));
    assert!(!core::access::allowed(0, 41, &c, 2, true));
    assert!(!core::access::allowed(0o777, 41, &c, 8, false));
}
