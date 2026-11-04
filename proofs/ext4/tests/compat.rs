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
    let seed = core::superblock::metadata_checksum_seed(&img[1024..2048]).unwrap();
    let ipg = le32(&img[1024..2048], 40);
    let g = core::group::parse_with_features(
        &img[4096..4096 + core::superblock::descriptor_length(&img[1024..2048]).unwrap()],
        0,
        sb.blocks(),
        ipg,
        seed,
        core::superblock::flex_enabled(&img[1024..2048]).unwrap(),
    )
    .expect("Linux descriptor");
    (sb, g, seed)
}

fn inode_bytes(img: &[u8], table: u32, number: u32) -> &[u8] {
    let offset = table as usize * 4096 + (number as usize - 1) * 256;
    &img[offset..offset + 256]
}

fn seal_inode_image(img: &mut [u8], table: u32, number: u32, seed: u32) {
    let start = table as usize * 4096 + (number as usize - 1) * 256;
    let raw = &mut img[start..start + 256];
    let checksum = core::inode::calculated_checksum(raw, number, seed).unwrap();
    raw[124..126].copy_from_slice(&(checksum as u16).to_le_bytes());
    raw[130..132].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
}

fn seal_single_group_allocation(img: &mut [u8]) {
    let blocks = le32(img, 1028);
    assert!(blocks <= 32768);
    let seed = core::superblock::metadata_checksum_seed(&img[1024..2048]).unwrap();
    let offset = le32(img, 4096) as usize * 4096;
    let bitmap = &img[offset..offset + 4096];
    let free = (0..blocks)
        .filter(|&b| bitmap[b as usize / 8] & (1 << (b % 8)) == 0)
        .count() as u32;
    let bitmap_checksum = core::crc::crc32c(seed, bitmap);
    img[1036..1040].copy_from_slice(&free.to_le_bytes());
    img[4108..4110].copy_from_slice(&(free as u16).to_le_bytes());
    img[4120..4122].copy_from_slice(&(bitmap_checksum as u16).to_le_bytes());
    let width = core::superblock::descriptor_length(&img[1024..2048]).unwrap();
    if width == 64 {
        img[4152..4154].copy_from_slice(&((bitmap_checksum >> 16) as u16).to_le_bytes());
    }
    let group_seed = core::crc::crc32c(seed, &0u32.to_le_bytes());
    let partial = core::crc::crc32c(group_seed, &img[4096..4126]);
    let with_zero = core::crc::crc32c(partial, &[0, 0]);
    let checksum = core::crc::crc32c(with_zero, &img[4128..4096 + width]) as u16;
    img[4126..4128].copy_from_slice(&checksum.to_le_bytes());
    let checksum = core::crc::crc32c(0xffffffff, &img[1024..2044]);
    img[2044..2048].copy_from_slice(&checksum.to_le_bytes());
}

fn exercise_complete_owned_tree_depths(img: &[u8], number: u32) {
    use core::{extent_claims, extent_tree, snapshot::Snapshot};
    let (sb, group, uuid_seed) = metadata(img);
    assert_eq!(sb.groups(), 1);
    let start = group.inode_table as usize * 4096 + (number as usize - 1) * 256;
    let first_key = le32(img, start + 52);
    let first_child = le32(img, start + 56);
    let generation = le32(img, start + 100);
    let seed = core::inode::inode_seed(uuid_seed, number, generation);
    for depth in 2..=5u16 {
        let mut deep = img.to_vec();
        let addresses: Vec<u32> = (1..depth).map(|i| sb.blocks() - i as u32).collect();
        let bitmap = group.block_bitmap as usize * 4096;
        for (level, &address) in addresses.iter().enumerate() {
            let bit = address as usize;
            assert_eq!(deep[bitmap + bit / 8] & (1 << (bit % 8)), 0);
            deep[bitmap + bit / 8] |= 1 << (bit % 8);
            let child = addresses.get(level + 1).copied().unwrap_or(first_child);
            let node = &mut deep[address as usize * 4096..(address as usize + 1) * 4096];
            node.fill(0);
            node[..2].copy_from_slice(&0xf30au16.to_le_bytes());
            node[2..4].copy_from_slice(&1u16.to_le_bytes());
            node[4..6].copy_from_slice(&340u16.to_le_bytes());
            node[6..8].copy_from_slice(&(depth - level as u16 - 1).to_le_bytes());
            node[12..16].copy_from_slice(&first_key.to_le_bytes());
            node[16..20].copy_from_slice(&child.to_le_bytes());
            let checksum = core::crc::crc32c(seed, &node[..4092]);
            node[4092..].copy_from_slice(&checksum.to_le_bytes());
        }
        deep[start + 46..start + 48].copy_from_slice(&depth.to_le_bytes());
        deep[start + 56..start + 60].copy_from_slice(&addresses[0].to_le_bytes());
        let sectors = le32(img, start + 28) + (depth as u32 - 1) * 8;
        deep[start + 28..start + 32].copy_from_slice(&sectors.to_le_bytes());
        seal_inode_image(&mut deep, group.inode_table, number, uuid_seed);
        seal_single_group_allocation(&mut deep);
        let source = Snapshot::from_bytes(&deep);
        let index = core::group_index::parse(source.duplicate()).unwrap();
        let bound = extent_claims::bind(&index, number, depth as u64 + 1).unwrap();
        assert_eq!(bound.tree().checked_nodes(), depth as u64 + 1);
        let volume = core::allocation::parse(source)
            .expect("every extent metadata level enters the complete ownership census");
        for address in addresses.iter().copied().chain([first_child]) {
            let role = volume.census().role_of(address).unwrap();
            assert_eq!(
                (role.kind, role.inode, role.generation),
                (6, number, generation)
            );
        }
        let node = core::allocated_inode::get(&volume, number).unwrap();
        assert_eq!(
            extent_tree::lookup_allocated(&node, 0)
                .unwrap()
                .visited_nodes(),
            depth + 1
        );
        assert!(matches!(
            core::file_read::chunk(&node, 0, 4096),
            core::file_read::Chunk::Zero(4096)
        ));
        assert!(core::image_validation::inspect(Snapshot::from_bytes(&deep)).is_some());
    }
}

fn exercise_timed_tree_write(img: &[u8], number: u32, offset: u64) {
    use core::{file_read::Chunk, recovery_request::Completion, snapshot::Snapshot};
    let volume = core::allocation::parse(Snapshot::from_bytes(img)).unwrap();
    let node = core::allocated_inode::get(&volume, number).unwrap();
    let original_root = node.raw()[40..100].to_vec();
    let size = node.info().size;
    let read_file = |node: &core::allocated_inode::AllocatedInode<'_, '_>| {
        let mut bytes = Vec::new();
        while bytes.len() < size as usize {
            match core::file_read::chunk(node, bytes.len() as u64, 4096) {
                Chunk::Data(data) => bytes.extend_from_slice(data),
                Chunk::Zero(length) => bytes.resize(bytes.len() + length, 0),
                Chunk::End => panic!("read stopped before the checked inode size"),
            }
        }
        bytes
    };
    let mut expected = read_file(&node);
    let credentials = core::access::Credentials {
        fsuid: node.info().uid,
        in_inode_group: false,
        dac_override: false,
        dac_read_search: false,
    };
    let input = [0x97; 79];
    let candidate =
        core::content_write::prepare_chunk(&node, offset, &input, &credentials).unwrap();
    let length = candidate.written_prefix();
    expected[offset as usize..offset as usize + length].copy_from_slice(&input[..length]);
    let mut writer = candidate.begin_timed(12345678901, 876543210).unwrap();
    let mut stable = img.to_vec();
    loop {
        let pending = match writer.dispatch() {
            Ok(pending) => pending,
            Err(done) => {
                writer = done;
                break;
            }
        };
        if let core::recovery_io::Command::Write { block, image } = pending.pending_command() {
            stable[block as usize * 4096..(block as usize + 1) * 4096].copy_from_slice(image);
        }
        writer = pending.finish_pending(Completion::Succeeded);
    }
    assert!(writer.finished());
    let after = core::allocation::parse(Snapshot::from_bytes(&stable)).unwrap();
    let updated = core::allocated_inode::get(&after, number).unwrap();
    assert_eq!(updated.raw()[40..100], original_root);
    assert_eq!(read_file(&updated), expected);
    for block in 0..volume.index().parameters().0 {
        if volume.census().role_of(block).unwrap().kind == 6 {
            assert_eq!(
                &stable[block as usize * 4096..(block as usize + 1) * 4096],
                &img[block as usize * 4096..(block as usize + 1) * 4096],
                "every external extent node, including off-path nodes, retains its exact source bytes"
            );
        }
    }
    assert!(core::image_validation::inspect(Snapshot::from_bytes(&stable)).is_some());
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
fn bootstrap_rejects_an_inode_table_in_the_primary_block_even_with_valid_checksums() {
    use core::{bootstrap, snapshot::Snapshot};
    let mut bad = image();
    let (sb, original_group, seed) = metadata(&bad);
    let journal_inode = inode_bytes(&bad, original_group.inode_table, 8).to_vec();
    // Keep the descriptor locally valid while moving inode 8 into block zero.
    // Global allocation is intentionally invalid; bootstrap precedes that check.
    bad[4096..4100].copy_from_slice(&(sb.blocks() - 2).to_le_bytes());
    bad[4100..4104].copy_from_slice(&(sb.blocks() - 1).to_le_bytes());
    bad[4104..4108].fill(0);
    bad[4126..4128].fill(0);
    let width = core::superblock::descriptor_length(&bad[1024..2048]).unwrap();
    let group_seed = core::crc::crc32c(seed, &0u32.to_le_bytes());
    let group_checksum = core::crc::crc32c(group_seed, &bad[4096..4096 + width]) as u16;
    bad[4126..4128].copy_from_slice(&group_checksum.to_le_bytes());
    bad[1792..2048].copy_from_slice(&journal_inode);

    fn flip_variable(bytes: &mut [u8], bit: usize) {
        let (start, within) = if bit < 16 {
            (1792 + 124, bit)
        } else if bit < 32 {
            (1792 + 130, bit - 16)
        } else if bit < 64 {
            (2044, bit - 32)
        } else {
            (1024 + 700, bit - 64)
        };
        bytes[start + within / 8] ^= 1 << (within % 8);
    }
    fn checksum_syndrome(bytes: &[u8], seed: u32) -> u64 {
        let raw = &bytes[1792..2048];
        let inode_crc = core::inode::calculated_checksum(raw, 8, seed).unwrap();
        let stored_inode = core::bytes::read_le16(raw, 124).unwrap() as u32
            | (core::bytes::read_le16(raw, 130).unwrap() as u32) << 16;
        let super_crc = core::crc::crc32c(0xffffffff, &bytes[1024..2044]);
        let stored_super = core::bytes::read_le32(bytes, 2044).unwrap();
        (inode_crc ^ stored_inode) as u64 | ((super_crc ^ stored_super) as u64) << 32
    }
    for (start, length) in [(1792 + 124, 2), (1792 + 130, 2), (2044, 4), (1024 + 700, 4)] {
        bad[start..start + length].fill(0);
    }
    // The inode contains the superblock checksum; the superblock contains the
    // inode checksum. Solve their affine CRC constraints together, with one
    // unused superblock word supplying free variables. Corrupting a checksum would
    // otherwise reject the fixture before the table-address check is reached.
    let constant = checksum_syndrome(&bad, seed);
    let mut columns = [0u64; 96];
    for bit in 0..96 {
        flip_variable(&mut bad, bit);
        columns[bit] = checksum_syndrome(&bad, seed) ^ constant;
        flip_variable(&mut bad, bit);
    }
    let mut rows = [0u128; 64];
    for equation in 0..64 {
        for bit in 0..96 {
            rows[equation] |= (((columns[bit] >> equation) & 1) as u128) << bit;
        }
        rows[equation] |= (((constant >> equation) & 1) as u128) << 96;
    }
    let mut pivots = Vec::new();
    let mut rank = 0usize;
    for column in 0..96 {
        let Some(pivot) = (rank..64).find(|&row| (rows[row] >> column) & 1 != 0) else {
            continue;
        };
        rows.swap(rank, pivot);
        let pivot_row = rows[rank];
        for row in 0..64 {
            if row != rank && (rows[row] >> column) & 1 != 0 {
                rows[row] ^= pivot_row;
            }
        }
        pivots.push(column);
        rank += 1;
        if rank == 64 {
            break;
        }
    }
    assert!(
        rows[rank..].iter().all(|&row| row == 0),
        "CRC fixture must be solvable"
    );
    for (row, &column) in pivots.iter().enumerate() {
        if (rows[row] >> 96) & 1 != 0 {
            flip_variable(&mut bad, column);
        }
    }
    assert_eq!(checksum_syndrome(&bad, seed), 0);
    let (_, descriptor, _) = metadata(&bad);
    assert_eq!(descriptor.inode_table, 0);
    assert!(core::layout::from_inode(&bad[1792..2048], sb.inodes(), sb.blocks(), seed).is_some());
    assert!(bootstrap::locate(&Snapshot::from_bytes(&bad)).is_none());
}

#[test]
fn bootstrap_locates_the_same_journal_through_every_admitted_shadow_depth() {
    use core::{bootstrap, patch_set::PatchSet, snapshot::Snapshot};
    let mut img = image();
    let (_, group, _) = metadata(&img);
    let baseline = Snapshot::from_bytes(&img);
    let found = bootstrap::locate(&baseline).unwrap();
    let journal = found.layout().physical_start();
    let expected = found.capture_journal();
    // A partial checkpoint need not have a valid home allocation bitmap.
    img[group.block_bitmap as usize * 4096] ^= 0x80;
    let targets = [0u32, 1, group.inode_table, journal];
    let patches: Vec<_> = (0..core::snapshot::MAX_SHADOW_LAYERS)
        .map(|depth| {
            let target = targets[depth % targets.len()];
            PatchSet::new()
                .insert(
                    target,
                    &img[target as usize * 4096..(target as usize + 1) * 4096],
                )
                .ok()
                .unwrap()
        })
        .collect();
    let mut source = Snapshot::from_bytes(&img);
    for (depth, patch) in patches.iter().enumerate() {
        source = source.overlay(patch).unwrap();
        assert_eq!(source.shadow_depth(), depth + 1);
        let located = bootstrap::locate(&source).unwrap();
        assert_eq!(located.journal_inode_block(), group.inode_table);
        assert_eq!(located.layout().physical_start(), journal);
        assert_eq!(located.capture_journal(), expected);
    }
    assert!(source.overlay(&patches[0]).is_none());
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
    let root_offset = group.inode_table as u64 * 4096 + (number as u64 - 1) * 256 + 40;
    let tree = core::extent_tree::audit(
        &source,
        root_offset,
        sb.blocks() as u64,
        4096,
        BlockChecksum::Crc32c(inode_seed),
        16,
    )
    .ok()
    .expect("complete Linux-created extent-tree audit");
    assert_eq!(tree.checked_nodes(), entries as u64 + 1);
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
    for logical in 0..18 {
        let path = tree
            .find(logical)
            .expect("audited Linux extent-tree traversal");
        assert_eq!(path.visited_nodes(), depth + 1);
        match path.resolved() {
            core::extent_tree::Mapping::Unwritten(block) => {
                assert!(logical < 16 && logical % 2 == 0);
                assert!(block > 0 && block < sb.blocks() as u64);
            }
            core::extent_tree::Mapping::Hole => assert!(logical >= 16 || logical % 2 == 1),
            core::extent_tree::Mapping::Written(_) => {
                panic!("fallocate produced unwritten extents")
            }
        }
    }
    let index = core::group_index::parse(source.duplicate()).unwrap();
    let bound = core::extent_claims::bind(&index, number, 16)
        .expect("the tree root, feature mode and checksum seed come from the same allocated inode");
    let census = core::extent_claims::collect(
        core::block_claims::Census::new(sb.blocks()).unwrap(),
        &bound,
    )
    .expect("Linux counts external extent metadata as well as data in i_blocks");
    for ordinal in 0..entries as usize {
        let child = root.index_entry(ordinal).unwrap().child as u32;
        let role = census.role_of(child).unwrap();
        assert_eq!(
            (
                role.kind,
                role.inode,
                role.generation,
                role.logical,
                role.initialized
            ),
            (6, number, le32(raw, 100), 0, false)
        );
    }
    for logical in (0..16).step_by(2) {
        let physical = match bound.tree().find(logical).unwrap().resolved() {
            core::extent_tree::Mapping::Unwritten(block) => block as u32,
            _ => panic!("unwritten fallocate extent"),
        };
        let role = census.role_of(physical).unwrap();
        assert_eq!(
            (role.kind, role.inode, role.logical, role.initialized),
            (4, number, logical, false)
        );
    }
    assert!(
        core::extent_claims::collect(census, &bound).is_none(),
        "a second claim cannot reuse either tree metadata or file data"
    );
    let first_child = root.index_entry(0).unwrap().child as u32;
    for kind in [3, 4, 6] {
        let prior = core::block_claims::Claim {
            start: first_child,
            length: 1,
            kind,
            inode: if kind == 3 { 0 } else { 12 },
            generation: 0,
            logical: 0,
            initialized: false,
        };
        let occupied = core::block_claims::Census::new(sb.blocks())
            .unwrap()
            .claim(prior)
            .ok()
            .unwrap();
        assert!(core::extent_claims::collect(occupied, &bound).is_none());
    }
    let inode_start = group.inode_table as usize * 4096 + (number as usize - 1) * 256;
    for mutation in 0..7 {
        let mut bad = img.clone();
        if mutation < 2 {
            let raw = &mut bad[inode_start..inode_start + 256];
            let offset = if mutation == 0 { 100 } else { 28 };
            let value = le32(raw, offset).wrapping_add(if mutation == 0 { 1 } else { 8 });
            raw[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
            let checksum = core::inode::calculated_checksum(raw, number, uuid_seed).unwrap();
            raw[124..126].copy_from_slice(&(checksum as u16).to_le_bytes());
            raw[130..132].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
        } else {
            let raw = &mut bad[first_child as usize * 4096..(first_child as usize + 1) * 4096];
            if mutation != 3 {
                let physical = match mutation {
                    2 => first_child,
                    4 => first_data_block(inode_bytes(&img, group.inode_table, 8), sb.blocks()),
                    5 => first_data_block(inode_bytes(&img, group.inode_table, 2), sb.blocks()),
                    _ => group.block_bitmap,
                };
                raw[20..24].copy_from_slice(&physical.to_le_bytes());
                raw[18..20].fill(0);
            } else {
                let physical = raw[18..24].to_vec();
                raw[30..36].copy_from_slice(&physical);
            }
            let tail = 12 + core::bytes::read_le16(raw, 4).unwrap() as usize * 12;
            let checksum = core::crc::crc32c(inode_seed, &raw[..tail]);
            raw[tail..tail + 4].copy_from_slice(&checksum.to_le_bytes());
        }
        let index = core::group_index::parse(Snapshot::from_bytes(&bad)).unwrap();
        if mutation == 0 {
            assert!(
                core::extent_claims::bind(&index, number, 16).is_none(),
                "an inode generation change cannot retain the old external-node checksum seed"
            );
        } else {
            let bound = core::extent_claims::bind(&index, number, 16)
                .expect("local metadata and the complete tree remain valid");
            let candidate = core::extent_claims::collect(
                core::block_claims::Census::new(sb.blocks()).unwrap(),
                &bound,
            );
            assert_eq!(
                candidate.is_none(),
                mutation < 4,
                "candidate claims have no knowledge of reservations that were not supplied to them"
            );
        }
        assert!(
            core::allocation::parse(Snapshot::from_bytes(&bad)).is_none(),
            "whole-image allocation rejects stale seeds, bad accounting, self-aliases, cross-inode aliases and reserved/journal targets"
        );
    }
    let volume = core::allocation::parse(source)
        .expect("complete source-bound external-tree allocation census");
    let node = core::allocated_inode::get(&volume, number).unwrap();
    for logical in 0..16 {
        assert!(
            matches!(
                core::file_read::chunk(&node, logical * 4096, 4096),
                core::file_read::Chunk::Zero(4096)
            ),
            "holes and unwritten storage return zeros"
        );
    }
    assert!(matches!(
        core::file_read::chunk(&node, 65536, 4096),
        core::file_read::Chunk::End
    ));
    assert_eq!(volume.census().role_of(first_child).unwrap().kind, 6);
    assert!(
        core::image_validation::inspect(Snapshot::from_bytes(&img)).is_some(),
        "allocation, complete namespace and retained image certificates compose for external trees"
    );

    let mut written = img.clone();
    let mut data_patterns = Vec::new();
    for ordinal in 0..entries as usize {
        let child = root.index_entry(ordinal).unwrap().child as usize;
        let leaf = &mut written[child * 4096..(child + 1) * 4096];
        let count = core::bytes::read_le16(leaf, 2).unwrap() as usize;
        for i in 0..count {
            let offset = 12 + 12 * i;
            let logical = le32(leaf, offset);
            let physical = le32(leaf, offset + 8);
            let encoded = core::bytes::read_le16(leaf, offset + 4).unwrap();
            assert!(encoded > 32768);
            leaf[offset + 4..offset + 6].copy_from_slice(&(encoded - 32768).to_le_bytes());
            data_patterns.push((logical, physical, logical as u8 + 31));
        }
        let tail = 12 + core::bytes::read_le16(leaf, 4).unwrap() as usize * 12;
        let checksum = core::crc::crc32c(inode_seed, &leaf[..tail]);
        leaf[tail..tail + 4].copy_from_slice(&checksum.to_le_bytes());
    }
    for &(_, physical, pattern) in &data_patterns {
        written[physical as usize * 4096..(physical as usize + 1) * 4096].fill(pattern);
    }
    let volume = core::allocation::parse(Snapshot::from_bytes(&written)).unwrap();
    let node = core::allocated_inode::get(&volume, number).unwrap();
    for (logical, physical, pattern) in data_patterns {
        let data = match core::file_read::chunk(&node, logical as u64 * 4096 + 7, 32) {
            core::file_read::Chunk::Data(data) => data,
            _ => panic!("initialized external-tree extent must read owned bytes"),
        };
        assert_eq!(data, &[pattern; 32]);
        let role = volume.census().role_of(physical).unwrap();
        assert_eq!(
            (role.kind, role.inode, role.logical, role.initialized),
            (4, number, logical, true)
        );
        assert!(matches!(
            core::file_read::chunk(&node, (logical as u64 + 1) * 4096, 4096),
            core::file_read::Chunk::Zero(4096)
        ));
    }
    assert!(core::image_validation::inspect(Snapshot::from_bytes(&written)).is_some());
    exercise_timed_tree_write(&written, number, 7);
    exercise_complete_owned_tree_depths(&img, number);

    let mut huge_tree = img.clone();
    huge_tree[1124..1128].copy_from_slice(&0x44bu32.to_le_bytes());
    let sectors = le32(raw, 28);
    huge_tree[inode_start + 28..inode_start + 32].copy_from_slice(&(sectors / 8).to_le_bytes());
    huge_tree[inode_start + 32..inode_start + 36].copy_from_slice(&0xc0000u32.to_le_bytes());
    seal_inode_image(&mut huge_tree, group.inode_table, number, uuid_seed);
    seal_single_group_allocation(&mut huge_tree);
    assert_eq!(
        core::inode_blocks::decode(
            inode_bytes(&huge_tree, group.inode_table, number),
            4096,
            true
        ),
        Some(sectors as u64)
    );
    assert!(
        core::image_validation::inspect(Snapshot::from_bytes(&huge_tree)).is_some(),
        "filesystem-block i_blocks units include external extent metadata"
    );

    let mut shared_empty = img.clone();
    let empty = &mut shared_empty[first_child as usize * 4096..(first_child as usize + 1) * 4096];
    empty[2..4].fill(0);
    let checksum = core::crc::crc32c(inode_seed, &empty[..4092]);
    empty[4092..].copy_from_slice(&checksum.to_le_bytes());
    let raw = &mut shared_empty[inode_start..inode_start + 256];
    raw[42..44].copy_from_slice(&2u16.to_le_bytes());
    raw[64..68].copy_from_slice(&16u32.to_le_bytes());
    raw[68..72].copy_from_slice(&first_child.to_le_bytes());
    raw[72..76].fill(0);
    raw[28..32].copy_from_slice(&16u32.to_le_bytes());
    seal_inode_image(&mut shared_empty, group.inode_table, number, uuid_seed);
    let index = core::group_index::parse(Snapshot::from_bytes(&shared_empty)).unwrap();
    let bound = core::extent_claims::bind(&index, number, 3)
        .expect("empty child first-key exception matches Linux structural checks");
    assert!(
        core::extent_claims::collect(
            core::block_claims::Census::new(sb.blocks()).unwrap(),
            &bound
        )
        .is_none(),
        "distinct parent entries cannot share even an empty extent-metadata block"
    );
}

#[test]
fn inode_bound_tree_candidates_reject_reserved_free_and_wrong_source_metadata() {
    use core::{extent_claims, group_index, snapshot::Snapshot};
    let img = image();
    let (sb, group, _) = metadata(&img);
    let index = group_index::parse(Snapshot::from_bytes(&img)).unwrap();
    for number in [2, 11, 12] {
        let bound = extent_claims::bind(&index, number, 1).unwrap();
        let inode = inode_bytes(&img, group.inode_table, number);
        assert_eq!(bound.metadata().generation, le32(inode, 100));
        assert_eq!(bound.tree().checked_nodes(), 1);
        assert_eq!(
            core::inode_table::position(&index, number),
            Some(group.inode_table as u64 * 4096 + (number as u64 - 1) * 256)
        );
    }
    for number in [0, 1, 8, 10, 13, sb.inodes() + 1, u32::MAX] {
        assert!(extent_claims::bind(&index, number, 100).is_none());
    }
    assert!(core::inode_table::position(&index, 0).is_none());
    assert!(core::inode_table::position(&index, u32::MAX).is_none());
    let mut bad = img.clone();
    let offset = group.inode_table as usize * 4096 + 11 * 256;
    bad[offset + 100] ^= 1;
    let index = group_index::parse(Snapshot::from_bytes(&bad)).unwrap();
    assert!(extent_claims::bind(&index, 12, 1).is_none());
}

#[test]
fn extent_metadata_claims_retain_inode_generation_and_reject_forged_shapes() {
    use core::block_claims::{Census, Claim};
    let claim = Claim {
        start: 20,
        length: 1,
        kind: 6,
        inode: 13,
        generation: 17,
        logical: 0,
        initialized: false,
    };
    let census = Census::new(64).unwrap().claim(claim).ok().unwrap();
    let role = census.role_of(20).unwrap();
    assert_eq!(
        (
            role.kind,
            role.inode,
            role.generation,
            role.logical,
            role.initialized
        ),
        (6, 13, 17, 0, false)
    );
    for invalid in [
        Claim { inode: 0, ..claim },
        Claim { length: 2, ..claim },
        Claim {
            logical: 1,
            ..claim
        },
        Claim {
            initialized: true,
            ..claim
        },
        Claim { kind: 7, ..claim },
    ] {
        assert!(Census::new(64).unwrap().claim(invalid).is_err());
    }
}

mod huge_file_tests {
    use core::{inode_blocks, snapshot::Snapshot};

    use super::{
        core, image, inode_bytes, le32, metadata, seal_inode_image, seal_single_group_allocation,
    };

    #[test]
    fn accounting_codecs_preserve_32_48_bit_and_filesystem_block_units_exactly() {
        for block_bytes in [1024u32, 2048, 4096, 8192, 16384, 32768, 65536] {
            let factor = block_bytes as u64 / 512;
            let maximum = ((1u64 << 48) - 1) * factor;
            for count in [
                0,
                1,
                u32::MAX as u64,
                1u64 << 32,
                (1u64 << 48) - 1,
                1u64 << 48,
                (1u64 << 48) + 1,
                maximum,
                maximum + 1,
                u64::MAX,
            ] {
                for feature in [false, true] {
                    let expected = count <= u32::MAX as u64
                        || feature
                            && (count < (1u64 << 48) || count <= maximum && count % factor == 0);
                    let encoded = inode_blocks::encode(count, block_bytes, feature);
                    assert_eq!(encoded.is_some(), expected);
                    if let Some(encoded) = encoded {
                        let mut raw = [0u8; 118];
                        raw[28..32].copy_from_slice(&encoded.low);
                        raw[116..118].copy_from_slice(&encoded.high);
                        raw[32..36].copy_from_slice(
                            &(if encoded.huge { 0xc0000u32 } else { 0x80000 }).to_le_bytes(),
                        );
                        assert_eq!(
                            inode_blocks::decode(&raw, block_bytes, feature),
                            Some(count)
                        );
                        assert_eq!(encoded.huge, count >= (1u64 << 48));
                    }
                }
            }
            let mut raw = [0u8; 118];
            raw[28..32].copy_from_slice(&3u32.to_le_bytes());
            raw[116..118].copy_from_slice(&1u16.to_le_bytes());
            raw[32..36].copy_from_slice(&0xc0000u32.to_le_bytes());
            assert_eq!(
                inode_blocks::decode(&raw, block_bytes, true),
                Some(((1u64 << 32) + 3) * factor)
            );
            assert_eq!(inode_blocks::decode(&raw, block_bytes, false), Some(3));
        }
        for block_bytes in [0, 512, 1536, u32::MAX] {
            assert!(inode_blocks::decode(&[0; 118], block_bytes, true).is_none());
            assert!(inode_blocks::encode(0, block_bytes, true).is_none());
        }
        assert!(inode_blocks::decode(&[0; 117], 4096, true).is_none());
    }

    #[test]
    fn checked_superblock_feature_controls_limits_flags_and_normalized_accounting() {
        let img = image();
        let (_, group, seed) = metadata(&img);
        let start = group.inode_table as usize * 4096 + 11 * 256;
        let maximum = ((1u64 << 32) - 1) * 4096;
        for block_units in [false, true] {
            let mut huge = img.clone();
            huge[1124..1128].copy_from_slice(&0x44bu32.to_le_bytes());
            let raw = &mut huge[start..start + 256];
            raw[4..8].copy_from_slice(&(maximum as u32).to_le_bytes());
            raw[108..112].copy_from_slice(&((maximum >> 32) as u32).to_le_bytes());
            raw[32..36]
                .copy_from_slice(&(if block_units { 0xc0000u32 } else { 0x80000 }).to_le_bytes());
            raw[28..32].copy_from_slice(&(if block_units { 2u32 } else { 16 }).to_le_bytes());
            seal_inode_image(&mut huge, group.inode_table, 12, seed);
            seal_single_group_allocation(&mut huge);
            let index = core::group_index::parse(Snapshot::from_bytes(&huge)).unwrap();
            assert!(index.huge_files());
            let bound = core::extent_claims::bind(&index, 12, 1).unwrap();
            assert_eq!(bound.metadata().size, maximum);
            assert_eq!(
                inode_blocks::decode(inode_bytes(&huge, group.inode_table, 12), 4096, true),
                Some(16)
            );
            let volume = core::allocation::parse(Snapshot::from_bytes(&huge)).unwrap();
            let node = core::allocated_inode::get(&volume, 12).unwrap();
            assert_eq!(node.info().size, maximum);
            assert!(matches!(
                core::file_read::chunk(&node, maximum - 1, usize::MAX),
                core::file_read::Chunk::Zero(1)
            ));
            assert!(core::image_validation::inspect(Snapshot::from_bytes(&huge)).is_some());
        }
        for variant in 0..7 {
            let mut bad = img.clone();
            if variant != 0 && variant != 4 {
                bad[1124..1128].copy_from_slice(&0x44bu32.to_le_bytes());
            }
            let raw = &mut bad[start..start + 256];
            match variant {
                0 | 1 => raw[32..36].copy_from_slice(&0xc0000u32.to_le_bytes()),
                2 => raw[28..32].copy_from_slice(&2u32.to_le_bytes()),
                3 | 4 => raw[116..118].copy_from_slice(&1u16.to_le_bytes()),
                5 => raw[32..36].copy_from_slice(&0x180000u32.to_le_bytes()),
                _ => {
                    raw[4..8].copy_from_slice(&((maximum + 1) as u32).to_le_bytes());
                    raw[108..112].copy_from_slice(&(((maximum + 1) >> 32) as u32).to_le_bytes());
                }
            }
            seal_inode_image(&mut bad, group.inode_table, 12, seed);
            seal_single_group_allocation(&mut bad);
            assert!(
                core::allocation::parse(Snapshot::from_bytes(&bad)).is_none(),
                "mismatched feature/flag/unit/high-field/limit case {variant}"
            );
        }
    }

    #[test]
    fn huge_sparse_limit_reaches_the_last_extent_logical_block_without_wrapping() {
        let mut img = image();
        let (_, group, seed) = metadata(&img);
        let start = group.inode_table as usize * 4096 + 11 * 256;
        let physical = le32(&img, start + 60);
        let maximum = ((1u64 << 32) - 1) * 4096;
        img[1124..1128].copy_from_slice(&0x44bu32.to_le_bytes());
        img[start + 4..start + 8].copy_from_slice(&(maximum as u32).to_le_bytes());
        img[start + 108..start + 112].copy_from_slice(&((maximum >> 32) as u32).to_le_bytes());
        img[start + 52..start + 56].copy_from_slice(&(u32::MAX - 2).to_le_bytes());
        seal_inode_image(&mut img, group.inode_table, 12, seed);
        seal_single_group_allocation(&mut img);
        let volume = core::allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let node = core::allocated_inode::get(&volume, 12).unwrap();
        let data = match core::file_read::chunk(&node, maximum - 1, usize::MAX) {
            core::file_read::Chunk::Data(data) => data,
            _ => panic!("last valid extent logical block"),
        };
        assert_eq!(
            data,
            &img[(physical as usize + 2) * 4096 - 1..(physical as usize + 2) * 4096]
        );
        assert_eq!(
            volume.census().role_of(physical + 1).unwrap().logical,
            u32::MAX - 1
        );
        assert!(matches!(
            core::file_read::chunk(&node, 0, 4096),
            core::file_read::Chunk::Zero(4096)
        ));
        assert!(matches!(
            core::file_read::chunk(&node, maximum, usize::MAX),
            core::file_read::Chunk::End
        ));
        assert!(matches!(
            core::file_read::resolve(&node, u32::MAX),
            core::file_read::Resolution::Zero
        ));
        assert!(core::image_validation::inspect(Snapshot::from_bytes(&img)).is_some());
    }

    #[test]
    fn linux_created_huge_file_feature_supports_a_maximum_size_sparse_inode() {
        struct ImageFile(String);
        impl Drop for ImageFile {
            fn drop(&mut self) {
                let _ = std::fs::remove_file(&self.0);
            }
        }
        let path = ImageFile(format!("build/native-huge-file-{}.img", std::process::id()));
        let mke2fs = std::env::var("MKE2FS_BIN").unwrap_or_else(|_| "mke2fs".into());
        let result = std::process::Command::new(mke2fs).args([
            "-q", "-F", "-t", "ext4", "-b", "4096", "-I", "256", "-O",
            "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum,huge_file",
            "-E", "lazy_itable_init=0,lazy_journal_init=0", &path.0, "16384",
        ]).output().unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        let maximum = (1u64 << 44) - 4096;
        let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
        for request in [
            String::from("write build/fixture-file.bin /payload"),
            format!("set_inode_field /payload size {}", maximum as u32),
            format!("set_inode_field /payload size_hi {}", maximum >> 32),
        ] {
            let result = std::process::Command::new(&debugfs)
                .args(["-w", "-R", &request, &path.0])
                .output()
                .unwrap();
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
        }
        let img = std::fs::read(&path.0).unwrap();
        let volume = core::allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        assert!(volume.index().huge_files());
        let node = core::allocated_inode::get(&volume, 12).unwrap();
        assert_eq!(node.info().size, maximum);
        assert_eq!(inode_blocks::decode(node.raw(), 4096, true), Some(16));
        assert!(matches!(
            core::file_read::chunk(&node, maximum - 1, usize::MAX),
            core::file_read::Chunk::Zero(1)
        ));
        assert!(core::image_validation::inspect(Snapshot::from_bytes(&img)).is_some());
        let e2fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        let result = std::process::Command::new(e2fsck)
            .args(["-fn", &path.0])
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
    }
}

mod inode_size_tests {
    use core::{inode_size, snapshot::Snapshot};

    use super::{core, image, inode_bytes, le32, metadata, seal_inode_image};

    #[test]
    fn linux_size_codecs_cover_high_fields_feature_limits_and_directory_interpretation() {
        for block_bytes in [1024, 2048, 4096, 8192, 16384, 32768, 65536] {
            for huge in [false, true] {
                let maximum = if huge {
                    (1u64 << 32) * block_bytes as u64 - block_bytes as u64
                } else {
                    (1u64 << 41) - block_bytes as u64
                };
                assert_eq!(inode_size::limit(block_bytes, huge), Some(maximum));
                for size in [
                    0,
                    u32::MAX as u64,
                    1u64 << 32,
                    (1u64 << 32) + 17,
                    maximum - 1,
                    maximum,
                    maximum + 1,
                    u64::MAX,
                ] {
                    let mut raw = [0u8; 112];
                    raw[..2].copy_from_slice(&0x81a4u16.to_le_bytes());
                    raw[4..8].copy_from_slice(&(size as u32).to_le_bytes());
                    raw[108..112].copy_from_slice(&((size >> 32) as u32).to_le_bytes());
                    assert_eq!(
                        inode_size::decode(&raw, block_bytes, huge, false),
                        (size <= maximum).then_some(size)
                    );
                    let encoded = inode_size::encode(size, block_bytes, huge);
                    assert_eq!(encoded.is_some(), size <= maximum);
                    if let Some((low, high)) = encoded {
                        raw[4..8].copy_from_slice(&low);
                        raw[108..112].copy_from_slice(&high);
                        assert_eq!(
                            inode_size::decode(&raw, block_bytes, huge, false),
                            Some(size)
                        );
                    }
                }
            }
        }
        let mut raw = [0u8; 112];
        raw[4..8].copy_from_slice(&5u32.to_le_bytes());
        raw[108..112].copy_from_slice(&1u32.to_le_bytes());
        for mode in [0x41edu16, 0xa1ff, 0x1180] {
            raw[..2].copy_from_slice(&mode.to_le_bytes());
            assert_eq!(inode_size::decode(&raw, 4096, false, false), Some(5));
            assert_eq!(
                inode_size::decode(&raw, 4096, false, true),
                Some((1u64 << 32) + 5)
            );
        }
        for length in [0, 1, 107, 108, 111] {
            assert!(inode_size::decode(&raw[..length], 4096, false, false).is_none());
        }
        for block_bytes in [0, 512, 1536, 3072, 65537, u32::MAX] {
            assert!(inode_size::limit(block_bytes, false).is_none());
            assert!(inode_size::decode(&raw, block_bytes, false, false).is_none());
            assert!(inode_size::encode(0, block_bytes, false).is_none());
        }
    }

    #[test]
    fn large_sparse_inodes_preserve_full_size_clipping_and_reject_wrong_feature_interpretations() {
        let img = image();
        let (sb, group, seed) = metadata(&img);
        let start = group.inode_table as usize * 4096 + 11 * 256;
        let maximum = (1u64 << 41) - 4096;
        for size in [
            (1u64 << 32) - 1,
            1u64 << 32,
            (1u64 << 32) + 123,
            1u64 << 40,
            maximum,
        ] {
            let mut sparse = img.clone();
            sparse[start + 4..start + 8].copy_from_slice(&(size as u32).to_le_bytes());
            sparse[start + 108..start + 112].copy_from_slice(&((size >> 32) as u32).to_le_bytes());
            seal_inode_image(&mut sparse, group.inode_table, 12, seed);
            let index = core::group_index::parse(Snapshot::from_bytes(&sparse)).unwrap();
            assert_eq!(
                core::extent_claims::bind(&index, 12, 1)
                    .unwrap()
                    .metadata()
                    .size,
                size
            );
            let volume = core::allocation::parse(Snapshot::from_bytes(&sparse)).unwrap();
            let node = core::allocated_inode::get(&volume, 12).unwrap();
            assert_eq!(node.info().size, size);
            assert!(matches!(
                core::file_read::chunk(&node, 0, 32),
                core::file_read::Chunk::Data(_)
            ));
            assert!(matches!(
                core::file_read::chunk(&node, size - 7, usize::MAX),
                core::file_read::Chunk::Zero(7)
            ));
            assert!(matches!(
                core::file_read::chunk(&node, size, usize::MAX),
                core::file_read::Chunk::End
            ));
            assert!(matches!(
                core::file_read::chunk(&node, u64::MAX, usize::MAX),
                core::file_read::Chunk::End
            ));
            assert!(core::image_validation::inspect(Snapshot::from_bytes(&sparse)).is_some());
        }
        for size in [maximum + 1, 1u64 << 63, u64::MAX] {
            let mut bad = img.clone();
            bad[start + 4..start + 8].copy_from_slice(&(size as u32).to_le_bytes());
            bad[start + 108..start + 112].copy_from_slice(&((size >> 32) as u32).to_le_bytes());
            seal_inode_image(&mut bad, group.inode_table, 12, seed);
            assert!(
                core::inode::parse_metadata(
                    inode_bytes(&bad, group.inode_table, 12),
                    12,
                    sb.inodes(),
                    seed
                )
                .is_none()
            );
            assert!(core::allocation::parse(Snapshot::from_bytes(&bad)).is_none());
        }
        for number in [2, 8] {
            let mut bad = img.clone();
            let offset = group.inode_table as usize * 4096 + (number as usize - 1) * 256;
            bad[offset + 108..offset + 112].copy_from_slice(&1u32.to_le_bytes());
            seal_inode_image(&mut bad, group.inode_table, number, seed);
            assert!(
                core::allocation::parse(Snapshot::from_bytes(&bad)).is_none(),
                "directory/journal high fields cannot silently adopt the regular-file policy"
            );
            if number == 8 {
                assert!(core::bootstrap::locate(&Snapshot::from_bytes(&bad)).is_none());
            }
        }
    }

    #[test]
    fn high_logical_extents_read_the_owned_physical_blocks_without_offset_truncation() {
        let mut img = image();
        let (_, group, seed) = metadata(&img);
        let start = group.inode_table as usize * 4096 + 11 * 256;
        let physical = le32(&img, start + 60);
        let maximum = (1u64 << 41) - 4096;
        let first_logical = (maximum / 4096 - 2) as u32;
        img[start + 4..start + 8].copy_from_slice(&(maximum as u32).to_le_bytes());
        img[start + 108..start + 112].copy_from_slice(&((maximum >> 32) as u32).to_le_bytes());
        img[start + 52..start + 56].copy_from_slice(&first_logical.to_le_bytes());
        seal_inode_image(&mut img, group.inode_table, 12, seed);
        let volume = core::allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let node = core::allocated_inode::get(&volume, 12).unwrap();
        assert!(matches!(
            core::file_read::chunk(&node, 0, 4096),
            core::file_read::Chunk::Zero(4096)
        ));
        for i in 0..2u32 {
            let offset = (first_logical as u64 + i as u64) * 4096 + 3;
            let bytes = match core::file_read::chunk(&node, offset, 31) {
                core::file_read::Chunk::Data(bytes) => bytes,
                _ => panic!("mapped high logical extent"),
            };
            let source_start = (physical as usize + i as usize) * 4096 + 3;
            assert_eq!(bytes, &img[source_start..source_start + 31]);
            assert_eq!(
                volume.census().role_of(physical + i).unwrap().logical,
                first_logical + i
            );
        }
        assert!(
            matches!(core::file_read::chunk(&node, maximum - 1, usize::MAX), core::file_read::Chunk::Data(bytes) if bytes.len() == 1)
        );
        assert!(matches!(
            core::file_read::chunk(&node, maximum, usize::MAX),
            core::file_read::Chunk::End
        ));
        assert!(core::image_validation::inspect(Snapshot::from_bytes(&img)).is_some());
    }

    #[test]
    fn linux_tools_accept_large_sparse_size_fields_and_the_checked_reader_agrees() {
        struct ImageFile(String);
        impl Drop for ImageFile {
            fn drop(&mut self) {
                let _ = std::fs::remove_file(&self.0);
            }
        }
        let path = ImageFile(format!(
            "build/native-large-size-{}.img",
            std::process::id()
        ));
        std::fs::write(&path.0, image()).unwrap();
        let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
        for size in [(1u64 << 32) + 123, (1u64 << 41) - 4096] {
            for (field, value) in [("size", size as u32), ("size_hi", (size >> 32) as u32)] {
                let request = format!("set_inode_field /payload {field} {value}");
                let result = std::process::Command::new(&debugfs)
                    .args(["-w", "-R", &request, &path.0])
                    .output()
                    .unwrap();
                assert!(
                    result.status.success(),
                    "{}",
                    String::from_utf8_lossy(&result.stderr)
                );
            }
            let img = std::fs::read(&path.0).unwrap();
            let volume = core::allocation::parse(Snapshot::from_bytes(&img)).unwrap();
            let node = core::allocated_inode::get(&volume, 12).unwrap();
            assert_eq!(node.info().size, size);
            assert!(matches!(
                core::file_read::chunk(&node, size - 1, usize::MAX),
                core::file_read::Chunk::Zero(1)
            ));
            assert!(core::image_validation::inspect(Snapshot::from_bytes(&img)).is_some());
        }
        let e2fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        let result = std::process::Command::new(e2fsck)
            .args(["-fn", &path.0])
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
    }
}

mod extent_tree_tests {
    use super::core::{
        crc,
        extent_node::{self, BlockChecksum},
        extent_span::{ExtentSpan, ExtentState},
        extent_tree::{self, LookupError, Mapping},
        snapshot::Snapshot,
    };

    const SEED: u32 = 0x8a94b27d;
    const ROOT: u64 = 100;
    const BLOCKS: u64 = 128;

    fn header(length: usize, depth: u16, count: u16) -> Vec<u8> {
        let mut raw = vec![0; length];
        raw[..2].copy_from_slice(&0xf30au16.to_le_bytes());
        raw[2..4].copy_from_slice(&count.to_le_bytes());
        let maximum = if length == 60 {
            4
        } else {
            ((length - 12) / 12) as u16
        };
        raw[4..6].copy_from_slice(&maximum.to_le_bytes());
        raw[6..8].copy_from_slice(&depth.to_le_bytes());
        raw
    }

    fn seal(raw: &mut [u8]) {
        if raw.len() == 60 {
            return;
        }
        let maximum = u16::from_le_bytes(raw[4..6].try_into().unwrap()) as usize;
        let tail = 12 + 12 * maximum;
        let checksum = crc::crc32c(SEED, &raw[..tail]);
        raw[tail..tail + 4].copy_from_slice(&checksum.to_le_bytes());
    }

    fn index(raw: &mut [u8], ordinal: usize, logical: u32, child: u64) {
        let offset = 12 + ordinal * 12;
        raw[offset..offset + 4].copy_from_slice(&logical.to_le_bytes());
        raw[offset + 4..offset + 8].copy_from_slice(&(child as u32).to_le_bytes());
        raw[offset + 8..offset + 10].copy_from_slice(&((child >> 32) as u16).to_le_bytes());
    }

    fn span(
        raw: &mut [u8],
        ordinal: usize,
        logical: u32,
        length: u32,
        physical: u64,
        initialized: bool,
        blocks: u64,
    ) {
        let state = if initialized {
            ExtentState::Written
        } else {
            ExtentState::Unwritten
        };
        let encoded = ExtentSpan::new(logical, length, physical, state, blocks)
            .unwrap()
            .encode()
            .unwrap();
        raw[12 + ordinal * 12..24 + ordinal * 12].copy_from_slice(&encoded);
    }

    fn chain(size: usize, depth: u16) -> Vec<u8> {
        let mut image = vec![0; size * BLOCKS as usize];
        for level in 0..=depth {
            let remaining = depth - level;
            let mut raw = header(
                if level == 0 { 60 } else { size },
                remaining,
                if remaining == 0 { 2 } else { 1 },
            );
            if remaining == 0 {
                span(&mut raw, 0, 10, 2, 100, true, BLOCKS);
                span(&mut raw, 1, 20, 3, 110, false, BLOCKS);
            } else {
                index(&mut raw, 0, 10, level as u64 + 2);
            }
            seal(&mut raw);
            let start = if level == 0 {
                ROOT as usize
            } else {
                (level as usize + 1) * size
            };
            image[start..start + raw.len()].copy_from_slice(&raw);
        }
        image
    }

    #[test]
    fn binary_search_matches_complete_linear_oracle_at_full_node_capacity() {
        for size in [1024, 2048, 4096, 8192, 16384, 32768, 65536] {
            let count = ((size - 12) / 12) as u16;
            let mut raw = header(size, 0, count);
            let keys: Vec<u32> = (0..count as u32).map(|i| 10 + 3 * i).collect();
            for (i, &logical) in keys.iter().enumerate() {
                span(&mut raw, i, logical, 1, 10000 + i as u64, true, 65536);
            }
            seal(&mut raw);
            let node = extent_node::parse_block(&raw, 65536, BlockChecksum::Crc32c(SEED)).unwrap();
            for query in (0..keys.last().unwrap() + 3).chain([u32::MAX - 1, u32::MAX]) {
                let expected = keys.partition_point(|&key| key <= query);
                assert_eq!(node.upper_bound(query), expected);
                let found = node.find_leaf(query);
                if let Ok(index) = keys.binary_search(&query) {
                    assert_eq!(
                        found.unwrap().physical_block(query),
                        Some(10000 + index as u64)
                    );
                } else {
                    assert!(found.is_none());
                }
            }
            assert!(node.key_at(count as usize).is_none());
            assert!(node.key_at(usize::MAX).is_none());
        }
    }

    #[test]
    fn source_paths_cover_all_block_sizes_and_depths_without_exposing_unwritten_as_written() {
        for size in [1024, 2048, 4096, 8192, 16384, 32768, 65536] {
            for depth in 0..=5 {
                let image = chain(size, depth);
                let source = Snapshot::from_bytes(&image);
                let tree = extent_tree::audit(
                    &source,
                    ROOT,
                    BLOCKS,
                    size as u32,
                    BlockChecksum::Crc32c(SEED),
                    depth as u64 + 1,
                )
                .ok()
                .unwrap();
                assert_eq!(tree.checked_nodes(), depth as u64 + 1);
                assert!(tree.find(u32::MAX).is_none());
                for budget in 0..=depth as u64 {
                    assert!(matches!(
                        extent_tree::audit(
                            &source,
                            ROOT,
                            BLOCKS,
                            size as u32,
                            BlockChecksum::Crc32c(SEED),
                            budget
                        ),
                        Err(extent_tree::AuditError::Budget)
                    ));
                }
                for query in [0, 9, 10, 11, 12, 19, 20, 21, 22, 23, u32::MAX - 1] {
                    let path = tree.find(query).unwrap();
                    assert_eq!(path.visited_nodes(), depth + 1);
                    match path.resolved() {
                        Mapping::Written(block) => {
                            assert!((10..12).contains(&query));
                            assert_eq!(block, 100 + (query - 10) as u64);
                        }
                        Mapping::Unwritten(block) => {
                            assert!((20..23).contains(&query));
                            assert_eq!(block, 110 + (query - 20) as u64);
                        }
                        Mapping::Hole => {
                            assert!(!(10..12).contains(&query) && !(20..23).contains(&query))
                        }
                    }
                }
                assert!(matches!(
                    extent_tree::lookup(
                        &source,
                        ROOT,
                        BLOCKS,
                        size as u32,
                        BlockChecksum::Legacy,
                        u32::MAX
                    ),
                    Err(LookupError::Geometry)
                ));
            }
        }
    }

    #[test]
    fn parent_bounds_depth_keys_checksums_and_cycles_fail_as_corruption() {
        let size = 4096;
        let mut image = chain(size, 1);
        let mut root = header(60, 1, 2);
        index(&mut root, 0, 10, 2);
        index(&mut root, 1, 20, 3);
        image[ROOT as usize..ROOT as usize + 60].copy_from_slice(&root);
        let mut left = header(size, 0, 1);
        span(&mut left, 0, 10, 2, 100, true, BLOCKS);
        seal(&mut left);
        image[2 * size..3 * size].copy_from_slice(&left);
        let mut right = header(size, 0, 1);
        span(&mut right, 0, 20, 3, 110, false, BLOCKS);
        seal(&mut right);
        image[3 * size..4 * size].copy_from_slice(&right);
        let source = Snapshot::from_bytes(&image);
        assert_eq!(
            extent_tree::audit(
                &source,
                ROOT,
                BLOCKS,
                size as u32,
                BlockChecksum::Crc32c(SEED),
                3
            )
            .ok()
            .unwrap()
            .checked_nodes(),
            3
        );
        assert!(matches!(
            extent_tree::audit(
                &source,
                ROOT,
                BLOCKS,
                size as u32,
                BlockChecksum::Crc32c(SEED),
                2
            ),
            Err(extent_tree::AuditError::Budget)
        ));
        for query in [0, 10, 19, 20, 22, 23] {
            assert!(
                extent_tree::lookup(
                    &source,
                    ROOT,
                    BLOCKS,
                    size as u32,
                    BlockChecksum::Crc32c(SEED),
                    query
                )
                .is_ok()
            );
        }
        for mutation in 0..6 {
            let mut broken = image.clone();
            let raw = &mut broken[2 * size..3 * size];
            match mutation {
                0 => raw[6..8].copy_from_slice(&1u16.to_le_bytes()), // wrong child depth
                1 => raw[12..16].copy_from_slice(&11u32.to_le_bytes()), // wrong first key
                2 => raw[16..18].copy_from_slice(&11u16.to_le_bytes()), // crosses sibling key 20
                3 => raw[6..8].copy_from_slice(&5u16.to_le_bytes()), // plausible cyclic node
                4 => {
                    raw[6..8].copy_from_slice(&1u16.to_le_bytes());
                    raw[2..4].fill(0);
                }
                _ => {}
            }
            seal(raw);
            if mutation == 5 {
                raw[100] ^= 1;
            } // damaged unused entry is still checksummed
            let source = Snapshot::from_bytes(&broken);
            assert!(
                matches!(
                    extent_tree::audit(
                        &source,
                        ROOT,
                        BLOCKS,
                        size as u32,
                        BlockChecksum::Crc32c(SEED),
                        3
                    ),
                    Err(extent_tree::AuditError::Corrupt)
                ),
                "the audit must reject corruption even outside a requested lookup path"
            );
            assert!(matches!(
                extent_tree::lookup(
                    &source,
                    ROOT,
                    BLOCKS,
                    size as u32,
                    BlockChecksum::Crc32c(SEED),
                    10
                ),
                Err(LookupError::Corrupt)
            ));
            assert!(
                extent_tree::lookup(
                    &source,
                    ROOT,
                    BLOCKS,
                    size as u32,
                    BlockChecksum::Crc32c(SEED),
                    20
                )
                .is_ok(),
                "a path certificate does not claim validation of unvisited subtrees"
            );
        }
        let mut cyclic = chain(size, 2);
        index(&mut cyclic[2 * size..3 * size], 0, 10, 2);
        seal(&mut cyclic[2 * size..3 * size]);
        assert!(matches!(
            extent_tree::lookup(
                &Snapshot::from_bytes(&cyclic),
                ROOT,
                BLOCKS,
                size as u32,
                BlockChecksum::Crc32c(SEED),
                10
            ),
            Err(LookupError::Corrupt)
        ));
        for (root, blocks, size) in [
            (u64::MAX, BLOCKS, size as u32),
            (ROOT, u64::MAX, size as u32),
            (ROOT, BLOCKS, 0),
            (ROOT, BLOCKS, 3072),
        ] {
            assert!(matches!(
                extent_tree::lookup(&source, root, blocks, size, BlockChecksum::Legacy, 0),
                Err(LookupError::Geometry)
            ));
        }
    }

    #[test]
    fn complete_audit_visits_every_branch_and_separates_budget_from_corruption() {
        fn build(
            image: &mut [u8],
            size: usize,
            depth: u16,
            low: u32,
            width: u32,
            address: Option<u64>,
            next: &mut u64,
        ) {
            let mut raw = header(
                if address.is_none() { 60 } else { size },
                depth,
                if depth == 0 { 1 } else { 2 },
            );
            if depth == 0 {
                span(
                    &mut raw,
                    0,
                    low,
                    1,
                    100 + (low - 10) as u64 / 10,
                    low % 20 == 10,
                    BLOCKS,
                );
            } else {
                for ordinal in 0..2 {
                    let child = *next;
                    *next += 1;
                    let first = low + ordinal as u32 * width / 2;
                    index(&mut raw, ordinal, first, child);
                    build(image, size, depth - 1, first, width / 2, Some(child), next);
                }
            }
            seal(&mut raw);
            let start = address.map_or(ROOT as usize, |number| number as usize * size);
            image[start..start + raw.len()].copy_from_slice(&raw);
        }
        for size in [1024, 4096, 65536] {
            let mut image = vec![0; size * BLOCKS as usize];
            let mut next = 2;
            build(&mut image, size, 3, 10, 80, None, &mut next);
            assert_eq!(next, 16);
            let source = Snapshot::from_bytes(&image);
            let tree = extent_tree::audit(
                &source,
                ROOT,
                BLOCKS,
                size as u32,
                BlockChecksum::Crc32c(SEED),
                15,
            )
            .ok()
            .unwrap();
            assert_eq!(tree.checked_nodes(), 15);
            for query in 0..90 {
                let result = tree.find(query).unwrap().resolved();
                if (10..90).contains(&query) && query % 10 == 0 {
                    let block = match result {
                        Mapping::Written(block) | Mapping::Unwritten(block) => block,
                        Mapping::Hole => panic!("missing leaf"),
                    };
                    assert_eq!(block, 100 + (query - 10) as u64 / 10);
                } else {
                    assert!(matches!(result, Mapping::Hole));
                }
            }
            assert!(matches!(
                extent_tree::audit(
                    &source,
                    ROOT,
                    BLOCKS,
                    size as u32,
                    BlockChecksum::Crc32c(SEED),
                    14
                ),
                Err(extent_tree::AuditError::Budget)
            ));
            image[15 * size + 6..15 * size + 8].copy_from_slice(&1u16.to_le_bytes());
            seal(&mut image[15 * size..16 * size]);
            let source = Snapshot::from_bytes(&image);
            assert!(
                extent_tree::lookup(
                    &source,
                    ROOT,
                    BLOCKS,
                    size as u32,
                    BlockChecksum::Crc32c(SEED),
                    10
                )
                .is_ok()
            );
            assert!(matches!(
                extent_tree::audit(
                    &source,
                    ROOT,
                    BLOCKS,
                    size as u32,
                    BlockChecksum::Crc32c(SEED),
                    15
                ),
                Err(extent_tree::AuditError::Corrupt)
            ));
        }
    }

    #[test]
    fn audited_trees_retain_exact_shadow_source_and_allow_empty_leaves() {
        use super::core::patch_set::PatchSet;
        let size = 1024;
        let image = chain(size, 1);
        let base = Snapshot::from_bytes(&image);
        let original = extent_tree::audit(
            &base,
            ROOT,
            BLOCKS,
            size as u32,
            BlockChecksum::Crc32c(SEED),
            2,
        )
        .ok()
        .unwrap();
        let mut page = image[..4096].to_vec();
        span(&mut page[2 * size..3 * size], 0, 10, 2, 105, true, BLOCKS);
        seal(&mut page[2 * size..3 * size]);
        let patches = PatchSet::new().insert(0, &page).ok().unwrap();
        page.fill(0);
        let shadow = base.overlay(&patches).unwrap();
        let modified = extent_tree::audit(
            &shadow,
            ROOT,
            BLOCKS,
            size as u32,
            BlockChecksum::Crc32c(SEED),
            2,
        )
        .ok()
        .unwrap();
        assert!(matches!(
            original.find(10).unwrap().resolved(),
            Mapping::Written(100)
        ));
        assert!(matches!(
            modified.find(10).unwrap().resolved(),
            Mapping::Written(105)
        ));
        assert!(matches!(
            modified.find(20).unwrap().resolved(),
            Mapping::Unwritten(110)
        ));
        assert_eq!(modified.checked_nodes(), 2);

        let mut empty_external = image.clone();
        empty_external[2 * size..3 * size].copy_from_slice(&header(size, 0, 0));
        seal(&mut empty_external[2 * size..3 * size]);
        let source = Snapshot::from_bytes(&empty_external);
        let empty = extent_tree::audit(
            &source,
            ROOT,
            BLOCKS,
            size as u32,
            BlockChecksum::Crc32c(SEED),
            2,
        )
        .ok()
        .unwrap();
        assert_eq!(empty.checked_nodes(), 2);
        for query in [0, 10, 20, u32::MAX - 1] {
            assert!(matches!(
                empty.find(query).unwrap().resolved(),
                Mapping::Hole
            ));
        }
        let mut empty_root = image;
        empty_root[ROOT as usize..ROOT as usize + 60].copy_from_slice(&header(60, 0, 0));
        let source = Snapshot::from_bytes(&empty_root);
        let empty =
            extent_tree::audit(&source, ROOT, BLOCKS, size as u32, BlockChecksum::Legacy, 1)
                .ok()
                .unwrap();
        assert_eq!(empty.checked_nodes(), 1);
        assert!(matches!(empty.find(0).unwrap().resolved(), Mapping::Hole));
        assert!(empty.find(u32::MAX).is_none());
    }
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
        assert!(directory_file::read(&lost, u32::try_from(logical).unwrap()).is_some());
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
            let physical = match file_read::resolve(&lost, u32::try_from(logical).unwrap()) {
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
    let j = core::journal_superblock::parse(
        journal,
        &img[1128..1144],
        u32::try_from(journal_inode.size / 4096).unwrap(),
    )
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

mod checksum_seed_tests {
    use core::{snapshot::Snapshot, super_state, superblock};

    use super::{core, image, le32, metadata};

    fn seal_primary(primary: &mut [u8]) {
        let checksum = core::crc::crc32c(0xffffffff, &primary[1024..2044]);
        primary[2044..2048].copy_from_slice(&checksum.to_le_bytes());
    }

    #[test]
    fn stored_checksum_seed_selection_is_exact_and_total() {
        let image = image();
        let mut raw = image[1024..2048].to_vec();
        let uuid_seed = core::crc::crc32c(0xffffffff, &raw[104..120]);
        for stored in [0, 1, 0x12345678, u32::MAX] {
            raw[624..628].copy_from_slice(&stored.to_le_bytes());
            for flags in [0x42u32, 0x46, 0x2042, 0x2046] {
                raw[96..100].copy_from_slice(&flags.to_le_bytes());
                assert_eq!(
                    superblock::metadata_checksum_seed(&raw),
                    Some(if flags & 0x2000 != 0 {
                        stored
                    } else {
                        uuid_seed
                    })
                );
            }
        }
        for length in [0, 1, 96, 624, 627, 1023, 1025, 4096] {
            assert!(superblock::metadata_checksum_seed(&vec![0; length]).is_none());
        }
    }

    #[test]
    fn recovery_changes_only_recover_and_rejects_other_feature_bit_changes() {
        let mut image = image();
        let seed = superblock::metadata_checksum_seed(&image[1024..2048]).unwrap();
        image[1648..1652].copy_from_slice(&seed.to_le_bytes());
        for flags in [0x42u32, 0x46, 0x2042, 0x2046] {
            image[1120..1124].copy_from_slice(&flags.to_le_bytes());
            seal_primary(&mut image);
            let source = Snapshot::from_bytes(&image);
            let boot = core::bootstrap::locate(&source).unwrap();
            for dirty in [false, true] {
                let updated =
                    super_state::recovery_image(&image[..4096], image.len() as u64, dirty).unwrap();
                let expected = if dirty { flags | 4 } else { flags & !4 };
                assert_eq!(le32(updated.as_slice(), 1120), expected);
                assert_eq!(
                    superblock::parse(&updated.as_slice()[1024..2048], image.len() as u64)
                        .unwrap()
                        .needs_recovery(),
                    dirty
                );
                assert_eq!(le32(updated.as_slice(), 1648), seed);
                assert_eq!(
                    super_state::valid_replay(
                        &image[..4096],
                        updated.as_slice(),
                        image.len() as u64
                    ),
                    dirty
                );
            }
            let mut changed = super_state::recovery_image(&image[..4096], image.len() as u64, true)
                .unwrap()
                .as_slice()
                .to_vec();
            changed[1120..1124].copy_from_slice(&((flags | 4) ^ 0x2000).to_le_bytes());
            seal_primary(&mut changed);
            assert!(superblock::parse(&changed[1024..2048], image.len() as u64).is_some());
            assert!(!super_state::valid_replay(
                &image[..4096],
                &changed,
                image.len() as u64
            ));
            let patches = core::patch_set::PatchSet::new()
                .insert(0, &changed)
                .ok()
                .unwrap();
            let switched = source.overlay(&patches).unwrap();
            assert!(
                core::image_validation::inspect(switched.duplicate()).is_some(),
                "the equal seed makes both format interpretations statically valid"
            );
            assert!(
                !core::bootstrap_identity::check(&boot, &switched),
                "recovery must retain the feature's interpretation even when both seeds coincide"
            );
        }
    }

    fn command(executable: &str, arguments: &[&str]) -> std::process::Output {
        let result = std::process::Command::new(executable)
            .args(arguments)
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{} {:?}: {}\n{}",
            executable,
            arguments,
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
        result
    }

    #[test]
    fn linux_uuid_changes_keep_ext4_metadata_and_jbd2_checksum_domains_distinct() {
        struct ScratchFiles(Vec<String>);
        impl Drop for ScratchFiles {
            fn drop(&mut self) {
                for path in &self.0 {
                    let _ = std::fs::remove_file(path);
                }
            }
        }
        for huge in [false, true] {
            let prefix = format!("build/native-csum-seed-{}-{huge}", std::process::id());
            let image_path = format!("{prefix}.img");
            let commands_path = format!("{prefix}.commands");
            let _cleanup = ScratchFiles(vec![image_path.clone(), commands_path.clone()]);
            let mke2fs = std::env::var("MKE2FS_BIN").unwrap_or_else(|_| "mke2fs".into());
            let features = format!(
                "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum,metadata_csum_seed{}",
                if huge { ",huge_file" } else { "" }
            );
            command(
                &mke2fs,
                &[
                    "-q",
                    "-F",
                    "-t",
                    "ext4",
                    "-b",
                    "4096",
                    "-I",
                    "256",
                    "-O",
                    &features,
                    "-E",
                    "lazy_itable_init=0,lazy_journal_init=0",
                    &image_path,
                    "16384",
                ],
            );
            let mut requests = String::from(
                "write build/fixture-file.bin /payload\nwrite /dev/null /fragmented\n",
            );
            for logical in (0..16).step_by(2) {
                requests.push_str(&format!("fallocate /fragmented {logical} {logical}\n"));
            }
            requests.push_str("set_inode_field /fragmented size 65536\n");
            std::fs::write(&commands_path, requests).unwrap();
            let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
            command(&debugfs, &["-w", "-f", &commands_path, &image_path]);
            let original = std::fs::read(&image_path).unwrap();
            let stored = le32(&original, 1648);
            let tune2fs = std::env::var("TUNE2FS_BIN").unwrap_or_else(|_| "tune2fs".into());
            command(
                &tune2fs,
                &["-U", "be647bc8-42bf-4831-ad30-8d6393f021c6", &image_path],
            );
            let changed_uuid = std::fs::read(&image_path).unwrap();
            assert_ne!(&original[1128..1144], &changed_uuid[1128..1144]);
            assert_eq!(le32(&changed_uuid, 1648), stored);
            // Native feature transitions rewrite ext4 checksums using the
            // changed UUID, while leaving the internal journal UUID alone.
            command(&tune2fs, &["-O", "^metadata_csum_seed", &image_path]);
            command(&tune2fs, &["-O", "metadata_csum_seed", &image_path]);
            command(
                &tune2fs,
                &["-U", "3dfd547c-8f5e-42bf-8954-138c35be1393", &image_path],
            );
            let mut image = std::fs::read(&image_path).unwrap();
            let stored = le32(&image, 1648);
            let (_, group, seed) = metadata(&image);
            assert_eq!(seed, stored);
            let journal_base =
                le32(super::inode_bytes(&image, group.inode_table, 8), 60) as usize * 4096;
            let uuid = image[journal_base + 48..journal_base + 64].to_vec();
            let journal_seed = core::crc::crc32c(0xffffffff, &uuid);
            assert_ne!(&uuid, &image[1128..1144]);
            assert_ne!(
                stored, journal_seed,
                "the test must distinguish checksum domains"
            );
            assert_ne!(stored, core::crc::crc32c(0xffffffff, &image[1128..1144]));
            let volume = core::allocation::parse(Snapshot::from_bytes(&image)).unwrap();
            assert_eq!(volume.index().parameters().3, stored);
            assert_eq!(volume.index().huge_files(), huge);
            let node = core::allocated_inode::get(&volume, 12).unwrap();
            let target = match core::file_read::resolve(&node, 0) {
                core::file_read::Resolution::Data(block) => block,
                _ => panic!("Linux payload must map to initialized data"),
            };
            let bound = core::extent_claims::bind(volume.index(), 13, 16).unwrap();
            assert!(bound.tree().checked_nodes() > 1);
            assert!(core::image_validation::inspect(Snapshot::from_bytes(&image)).is_some());
            super::exercise_complete_owned_tree_depths(&image, 13);
            let source = Snapshot::from_bytes(&image);
            let boot = core::bootstrap::locate(&source).unwrap();
            assert_eq!(boot.uuid(), &image[1128..1144]);
            assert_eq!(boot.journal_uuid(), uuid);
            assert!(boot.prepare_recovery().is_some());
            let layout = boot.layout().duplicate();
            let base = layout.physical_start() as usize * 4096;
            let journal_info =
                core::journal_superblock::parse(&image[base..base + 1024], &uuid, layout.blocks())
                    .unwrap();
            assert_eq!(journal_info.uuid_seed, journal_seed);
            assert!(
                core::journal_superblock::parse(
                    &image[base..base + 1024],
                    &image[1128..1144],
                    layout.blocks()
                )
                .is_none()
            );
            let writer = core::write_io::prepare(
                &image[base..base + layout.blocks() as usize * 4096],
                &uuid,
                layout.duplicate(),
                &image[..4096],
                image.len() as u64,
                vec![core::transaction::AfterImage::capture(target, &vec![0x19; 4096]).unwrap()],
            );
            assert!(
                writer.is_some(),
                "writer admission uses the journal UUID and preserves the separate filesystem UUID"
            );
            assert!(
                core::layout::from_inode(
                    super::inode_bytes(&image, group.inode_table, 8),
                    volume.index().parameters().1,
                    volume.index().parameters().0,
                    journal_seed
                )
                .is_none(),
                "the journal inode itself belongs to the ext4 metadata checksum domain"
            );
            let e2fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
            command(&e2fsck, &["-fn", &image_path]);
            let mut wrong = image.clone();
            wrong[1648] ^= 1;
            seal_primary(&mut wrong);
            assert!(superblock::parse(&wrong[1024..2048], wrong.len() as u64).is_some());
            assert!(core::group_index::parse(Snapshot::from_bytes(&wrong)).is_none());
            assert!(core::bootstrap::locate(&Snapshot::from_bytes(&wrong)).is_none());
            drop(bound);
            drop(node);
            drop(volume);
            drop(boot);
            drop(source);
            let header = core::journal_state::encode(
                &image[base..base + 4096],
                &uuid,
                layout.blocks(),
                9,
                1,
            )
            .unwrap();
            image[base..base + 4096].copy_from_slice(header.as_slice());
            let dirty =
                super_state::recovery_image(&image[..4096], image.len() as u64, true).unwrap();
            image[..4096].copy_from_slice(dirty.as_slice());
            let payload = vec![0x6b; 4096];
            let tx = core::transaction::encode(
                vec![core::transaction::AfterImage::capture(target, &payload).unwrap()],
                &uuid,
                9,
                &layout,
                &image[..4096],
                image.len() as u64,
            )
            .unwrap();
            assert!(core::jbd2::valid_commit(tx.commit_bytes(), 9, journal_seed));
            assert!(!core::jbd2::valid_commit(tx.commit_bytes(), 9, stored));
            for (slot, bytes) in [
                (1, tx.descriptor_bytes()),
                (2, tx.payload_at(0).unwrap()),
                (3, tx.commit_bytes()),
            ] {
                let offset = layout.offset(slot, image.len() as u64).unwrap() as usize;
                image[offset..offset + 4096].copy_from_slice(bytes);
            }
            let source = Snapshot::from_bytes(&image);
            let engine = core::bootstrap::locate(&source)
                .unwrap()
                .prepare_recovery()
                .unwrap();
            assert_eq!(engine.replay_plan().len(), 1);
            assert_eq!(engine.replay_plan().get(0).unwrap().image(), payload);
            let mut admitted = core::recovery_admission::prepare(&source).unwrap();
            let mut recovered = image.clone();
            while !admitted.finished() {
                let pending = admitted.dispatch().ok().unwrap();
                match pending.pending_command() {
                    core::recovery_io::Command::Write { block, image } => {
                        recovered[block as usize * 4096..(block as usize + 1) * 4096]
                            .copy_from_slice(image);
                    }
                    core::recovery_io::Command::Flush => {}
                }
                admitted = pending.finish_pending(core::recovery_request::Completion::Succeeded);
            }
            assert_eq!(
                &recovered[target as usize * 4096..(target as usize + 1) * 4096],
                payload
            );
            assert_eq!(le32(&recovered, 1120), 0x2046);
            assert_eq!(le32(&recovered, 1648), stored);
            assert!(core::image_validation::inspect(Snapshot::from_bytes(&recovered)).is_some());
            std::fs::write(&image_path, &image).unwrap();
            let checked = std::process::Command::new(&e2fsck)
                .args(["-fy", &image_path])
                .output()
                .unwrap();
            assert!(
                matches!(checked.status.code(), Some(0 | 1)),
                "{}\n{}",
                String::from_utf8_lossy(&checked.stdout),
                String::from_utf8_lossy(&checked.stderr)
            );
            let linux = std::fs::read(&image_path).unwrap();
            assert_eq!(
                &linux[target as usize * 4096..(target as usize + 1) * 4096],
                payload
            );
            assert_eq!(le32(&linux, 1120), 0x2042);
            assert_eq!(le32(&linux, 1648), stored);
            assert!(core::image_validation::inspect(Snapshot::from_bytes(&linux)).is_some());
        }
    }
}

mod group64_tests {
    use core::{group_fields, snapshot::Snapshot};

    use super::{core, image, le32, metadata};

    struct ScratchFiles(Vec<String>);
    impl Drop for ScratchFiles {
        fn drop(&mut self) {
            for path in &self.0 {
                let _ = std::fs::remove_file(path);
            }
        }
    }

    pub(super) fn command(name: &str, arguments: &[&str], repair: bool) {
        let executable =
            std::env::var(format!("{name}_BIN")).unwrap_or_else(|_| name.to_lowercase());
        let result = std::process::Command::new(executable)
            .args(arguments)
            .output()
            .unwrap();
        assert!(
            result.status.success() || repair && result.status.code() == Some(1),
            "{name} {arguments:?}: {}\n{}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
    }

    pub(super) fn seal_descriptor(raw: &mut [u8], number: u32, seed: u32) {
        let seed = core::crc::crc32c(seed, &number.to_le_bytes());
        let prefix = core::crc::crc32c(seed, &raw[..30]);
        let zeros = core::crc::crc32c(prefix, &[0, 0]);
        let checksum = core::crc::crc32c(zeros, &raw[32..]) as u16;
        raw[30..32].copy_from_slice(&checksum.to_le_bytes());
    }

    #[test]
    fn high_low_codecs_preserve_all_address_counter_and_superblock_bits() {
        for wide in [false, true] {
            for value in [
                0,
                1,
                u32::MAX as u64,
                1u64 << 32,
                (1u64 << 48) - 1,
                u64::MAX,
            ] {
                let mut raw = vec![0; if wide { 64 } else { 32 }];
                let encoded = group_fields::encode_address(value, wide);
                assert_eq!(encoded.is_some(), wide || value <= u32::MAX as u64);
                if let Some((low, high)) = encoded {
                    for (low_offset, high_offset) in [(0, 32), (4, 36), (8, 40)] {
                        raw[low_offset..low_offset + 4].copy_from_slice(&low);
                        if wide {
                            raw[high_offset..high_offset + 4].copy_from_slice(&high);
                        }
                    }
                    let fields = group_fields::decode(&raw, wide).unwrap();
                    assert_eq!(
                        (fields.block_bitmap, fields.inode_bitmap, fields.inode_table),
                        (value, value, value)
                    );
                    if wide && value > u32::MAX as u64 {
                        assert_ne!(fields.block_bitmap, value as u32 as u64);
                    }
                }
            }
            for value in [0, 1, u16::MAX as u32, 65536, u32::MAX] {
                let encoded = group_fields::encode_counter(value, wide);
                assert_eq!(encoded.is_some(), wide || value <= u16::MAX as u32);
                if let Some((low, high)) = encoded {
                    let mut raw = vec![0; if wide { 64 } else { 32 }];
                    for (low_offset, high_offset) in
                        [(12, 44), (14, 46), (16, 48), (28, 50), (24, 56), (26, 58)]
                    {
                        raw[low_offset..low_offset + 2].copy_from_slice(&low);
                        if wide {
                            raw[high_offset..high_offset + 2].copy_from_slice(&high);
                        }
                    }
                    let f = group_fields::decode(&raw, wide).unwrap();
                    assert_eq!(
                        [
                            f.free_blocks,
                            f.free_inodes,
                            f.directories,
                            f.unused,
                            f.block_checksum,
                            f.inode_checksum
                        ],
                        [value; 6]
                    );
                }
            }
        }
        for length in [0, 1, 31, 33, 63, 65, 1024] {
            for wide in [false, true] {
                assert!(group_fields::decode(&vec![0; length], wide).is_none());
            }
        }
        assert!(group_fields::decode(&[0; 32], true).is_none());
        assert!(group_fields::decode(&[0; 64], false).is_none());
        for offset in [usize::MAX, usize::MAX - 1, 63, 64] {
            assert!(group_fields::read_address(&[0; 64], offset, 0, true).is_none());
            assert!(group_fields::read_counter(&[0; 64], 0, offset, true).is_none());
        }
        assert_eq!(
            group_fields::read_address(&[1; 4], 0, usize::MAX, false),
            Some(0x01010101)
        );
        let mut raw = [0; 1024];
        for (low, high) in [(4, 336), (8, 340), (12, 344)] {
            raw[low..low + 4].copy_from_slice(&u32::MAX.to_le_bytes());
            raw[high..high + 4].copy_from_slice(&u32::MAX.to_le_bytes());
        }
        assert_eq!(
            group_fields::super_counts(&raw, true),
            Some((u64::MAX, u64::MAX, u64::MAX))
        );
        assert_eq!(
            group_fields::super_counts(&raw, false),
            Some((u32::MAX as u64, u32::MAX as u64, u32::MAX as u64))
        );
        assert!(group_fields::super_counts(&raw[..1023], true).is_none());
    }

    #[test]
    fn bounded_group_admission_checks_extended_crc_and_rejects_valid_high_fields() {
        let image = image();
        let (sb, _, seed) = metadata(&image);
        let ipg = le32(&image, 1064);
        let mut raw = image[4096..4128].to_vec();
        raw.resize(64, 0);
        seal_descriptor(&mut raw, 0, seed);
        assert!(core::group::parse(&raw, 0, sb.blocks(), ipg, seed).is_some());
        let mut corrupt = raw.clone();
        corrupt[63] ^= 1;
        assert!(core::group::parse(&corrupt, 0, sb.blocks(), ipg, seed).is_none());
        seal_descriptor(&mut corrupt, 0, seed);
        assert!(
            core::group::parse(&corrupt, 0, sb.blocks(), ipg, seed).is_some(),
            "unused bytes remain covered by CRC"
        );
        for offset in [32, 36, 40, 44, 46, 48, 50] {
            let mut high = raw.clone();
            high[offset] = 1;
            seal_descriptor(&mut high, 0, seed);
            let fields = group_fields::decode(&high, true).unwrap();
            assert!(
                fields.block_bitmap > u32::MAX as u64
                    || fields.inode_bitmap > u32::MAX as u64
                    || fields.inode_table > u32::MAX as u64
                    || fields.free_blocks >= 65536
                    || fields.free_inodes >= 65536
                    || fields.directories >= 65536
                    || fields.unused >= 65536
            );
            assert!(
                core::group::parse(&high, 0, sb.blocks(), ipg, seed).is_none(),
                "high field at {offset} must not disappear"
            );
        }
    }

    #[test]
    fn native_64bit_descriptors_compose_with_huge_file_checksum_seeds_and_owned_trees() {
        for huge in [false, true] {
            for csum_seed in [false, true] {
                let prefix = format!(
                    "build/native-group64-{}-{huge}-{csum_seed}",
                    std::process::id()
                );
                let path = format!("{prefix}.img");
                let script = format!("{prefix}.commands");
                let _cleanup = ScratchFiles(vec![path.clone(), script.clone()]);
                let features = format!(
                    "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum,64bit{}{}",
                    if huge { ",huge_file" } else { "" },
                    if csum_seed { ",metadata_csum_seed" } else { "" }
                );
                command(
                    "MKE2FS",
                    &[
                        "-q",
                        "-F",
                        "-t",
                        "ext4",
                        "-b",
                        "4096",
                        "-I",
                        "256",
                        "-O",
                        &features,
                        "-E",
                        "lazy_itable_init=0,lazy_journal_init=0",
                        &path,
                        "16384",
                    ],
                    false,
                );
                let mut requests = String::from(
                    "write build/fixture-file.bin /payload\nwrite /dev/null /fragmented\n",
                );
                for logical in (0..16).step_by(2) {
                    requests.push_str(&format!("fallocate /fragmented {logical} {logical}\n"));
                }
                requests.push_str("set_inode_field /fragmented size 65536\n");
                std::fs::write(&script, requests).unwrap();
                command("DEBUGFS", &["-w", "-f", &script, &path], false);
                if csum_seed {
                    command(
                        "TUNE2FS",
                        &["-U", "113cda45-32ad-40db-981a-2c3c8baadf21", &path],
                        false,
                    );
                }
                let image = std::fs::read(&path).unwrap();
                let (sb, group, seed) = metadata(&image);
                assert_eq!(
                    core::superblock::descriptor_length(&image[1024..2048]),
                    Some(64)
                );
                let source = Snapshot::from_bytes(&image);
                let volume = core::allocation::parse(source.duplicate()).unwrap();
                assert_eq!(volume.index().get(0).unwrap().descriptor().len(), 64);
                assert!(core::image_validation::inspect(source.duplicate()).is_some());
                let boot = core::bootstrap::locate(&source).unwrap();
                assert_eq!(boot.descriptor_size(), 64);
                assert!(boot.prepare_recovery().is_some());
                assert!(core::recovery_admission::prepare(&source).is_some());
                super::exercise_complete_owned_tree_depths(&image, 13);
                let node = core::allocated_inode::get(&volume, 12).unwrap();
                assert!(matches!(
                    core::file_read::chunk(&node, 0, 8192),
                    core::file_read::Chunk::Data(_)
                ));
                for dirty in [true, false] {
                    let marked = core::super_state::recovery_image(
                        &image[..4096],
                        image.len() as u64,
                        dirty,
                    )
                    .unwrap();
                    assert_eq!(
                        le32(marked.as_slice(), 1120),
                        le32(&image, 1120) | if dirty { 4 } else { 0 }
                    );
                }
                for offset in [56usize, 58] {
                    let mut bad = image.clone();
                    bad[4096 + offset] ^= 1;
                    seal_descriptor(&mut bad[4096..4160], 0, seed);
                    assert!(
                        core::group::parse(
                            &bad[4096..4160],
                            0,
                            sb.blocks(),
                            le32(&image, 1064),
                            seed
                        )
                        .is_some()
                    );
                    assert!(
                        core::group_metadata::parse(&Snapshot::from_bytes(&bad), 0).is_none(),
                        "full bitmap checksum high half at {offset} must be checked"
                    );
                }
                for descriptor_size in [0u16, 32, 63, 128] {
                    let mut raw = image[1024..2048].to_vec();
                    raw[254..256].copy_from_slice(&descriptor_size.to_le_bytes());
                    let checksum = core::crc::crc32c(0xffffffff, &raw[..1020]);
                    raw[1020..].copy_from_slice(&checksum.to_le_bytes());
                    assert!(core::superblock::parse(&raw, image.len() as u64).is_none());
                }
                let mut high = image[1024..2048].to_vec();
                high[336..340].copy_from_slice(&1u32.to_le_bytes());
                let checksum = core::crc::crc32c(0xffffffff, &high[..1020]);
                high[1020..].copy_from_slice(&checksum.to_le_bytes());
                assert!(group_fields::super_counts(&high, true).unwrap().0 > u32::MAX as u64);
                assert!(
                    core::superblock::parse(&high, u64::MAX).is_none(),
                    "bounded geometry rejects the full count"
                );
                assert_eq!(group.inode_table, le32(&image, 4104));
                command("E2FSCK", &["-fn", &path], false);
            }
        }
    }

    #[test]
    fn two_group_64bit_images_use_the_source_stride_and_preserve_high_bootstrap_addresses() {
        let prefix = format!("build/native-group64-multiple-{}", std::process::id());
        let path = format!("{prefix}.img");
        let script = format!("{prefix}.commands");
        let _cleanup = ScratchFiles(vec![path.clone(), script.clone()]);
        command(
            "MKE2FS",
            &[
                "-q",
                "-F",
                "-t",
                "ext4",
                "-b",
                "4096",
                "-I",
                "256",
                "-N",
                "16384",
                "-O",
                "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum,64bit,huge_file,metadata_csum_seed",
                "-E",
                "lazy_itable_init=0,lazy_journal_init=0",
                &path,
                "65536",
            ],
            false,
        );
        // Force an ordinary inode into the second group; e2fsck initializes
        // its bitmap and reconciles native allocation/high-water counters.
        std::fs::write(&script, "write /dev/null /second-group\ncopy_inode /second-group <8193>\nseti <8193>\nunlink /second-group\nlink <8193> /second-group\nfreei <12>\nclri <12>\nset_bg 1 flags 4\n").unwrap();
        command("DEBUGFS", &["-w", "-f", &script, &path], false);
        command("E2FSCK", &["-fy", &path], true);
        command("E2FSCK", &["-fn", &path], false);
        let image = std::fs::read(&path).unwrap();
        let source = Snapshot::from_bytes(&image);
        let volume = core::allocation::parse(source.duplicate()).unwrap();
        assert_eq!(volume.index().group_count(), 2);
        let second = volume.index().get(1).unwrap();
        assert_eq!(second.descriptor(), &image[4160..4224]);
        assert_eq!(second.info().inode_table, le32(&image, 4168));
        assert!(core::allocated_inode::get(&volume, 8193).is_some());
        assert!(core::allocated_inode::get(&volume, 12).is_none());
        assert!(core::image_validation::inspect(source.duplicate()).is_some());
        let boot = core::bootstrap::locate(&source).unwrap();
        assert!(boot.prepare_recovery().is_some());
        assert!(core::bootstrap_identity::check(&boot, &source));
        for offset in [64 + 32, 64 + 36, 64 + 40] {
            let mut gdt = image[4096..8192].to_vec();
            gdt[offset] ^= 1;
            let patch = core::patch_set::PatchSet::new()
                .insert(1, &gdt)
                .ok()
                .unwrap();
            assert!(
                !core::bootstrap_identity::check(&boot, &source.overlay(&patch).unwrap()),
                "second-group high address {offset} must be immutable independently of checksum validation"
            );
        }
    }
}

mod lazy_inode_tests {
    use core::{bitmap, snapshot::Snapshot};

    use super::{
        core,
        group64_tests::{command, seal_descriptor},
        image, inode_bytes, le32, metadata,
    };

    #[test]
    fn synthesized_inode_bitmaps_are_empty_with_allocated_padding_and_total_input_checks() {
        for meaningful in [8u32, 16, 128, 4096, 32768] {
            for seed in [0, 0x12345678, u32::MAX] {
                let bitmap = bitmap::synthesize_free_inodes(meaningful, seed).unwrap();
                assert_eq!(bitmap.free_count(), meaningful);
                assert_eq!(bitmap.entry_count(), meaningful);
                assert_eq!(
                    &bitmap.raw_image()[..meaningful as usize / 8],
                    vec![0; meaningful as usize / 8]
                );
                assert!(
                    bitmap.raw_image()[meaningful as usize / 8..]
                        .iter()
                        .all(|&byte| byte == 255)
                );
                for slot in 0..32768 {
                    assert_eq!(
                        bitmap.is_set(slot),
                        if slot < meaningful { Some(false) } else { None }
                    );
                    assert_eq!(
                        bitmap::read_bit(bitmap.raw_image(), slot),
                        Some(slot >= meaningful)
                    );
                }
            }
        }
        for meaningful in [0, 1, 7, 9, 32767, 32769, u32::MAX] {
            assert!(bitmap::synthesize_free_inodes(meaningful, 0).is_none());
        }
    }

    #[test]
    fn group_zero_cannot_hide_reserved_inodes_as_uninitialized() {
        let image = image();
        let (sb, _, seed) = metadata(&image);
        let ipg = le32(&image, 1064);
        for flags in [1u16, 5] {
            let mut descriptor = image[4096..4128].to_vec();
            descriptor[18..20].copy_from_slice(&flags.to_le_bytes());
            descriptor[14..16].copy_from_slice(&(ipg as u16).to_le_bytes());
            descriptor[16..18].fill(0);
            descriptor[28..30].copy_from_slice(&(ipg as u16).to_le_bytes());
            seal_descriptor(&mut descriptor, 0, seed);
            assert!(core::group::parse(&descriptor, 0, sb.blocks(), ipg, seed).is_none());
        }
        for flags in [0u16, 4] {
            let mut descriptor = image[4096..4128].to_vec();
            descriptor[18..20].copy_from_slice(&flags.to_le_bytes());
            seal_descriptor(&mut descriptor, 0, seed);
            assert!(
                core::group::parse(&descriptor, 0, sb.blocks(), ipg, seed).is_some(),
                "the INODE_ZEROED bookkeeping flag alone does not change live inode semantics"
            );
        }
    }

    #[test]
    fn native_lazy_groups_ignore_stale_bitmaps_and_inodes_without_granting_access() {
        struct ImageFile(String);
        impl Drop for ImageFile {
            fn drop(&mut self) {
                let _ = std::fs::remove_file(&self.0);
            }
        }
        for wide in [false, true] {
            for huge in [false, true] {
                for csum_seed in [false, true] {
                    let path = ImageFile(format!(
                        "build/native-lazy-inodes-{}-{wide}-{huge}-{csum_seed}.img",
                        std::process::id()
                    ));
                    let features = format!(
                        "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum{}{}{}",
                        if wide { ",64bit" } else { "" },
                        if huge { ",huge_file" } else { "" },
                        if csum_seed { ",metadata_csum_seed" } else { "" }
                    );
                    command(
                        "MKE2FS",
                        &[
                            "-q",
                            "-F",
                            "-t",
                            "ext4",
                            "-b",
                            "4096",
                            "-I",
                            "256",
                            "-N",
                            "8192",
                            "-O",
                            &features,
                            "-E",
                            "lazy_itable_init=0,lazy_journal_init=0",
                            &path.0,
                            "40960",
                        ],
                        false,
                    );
                    command(
                        "DEBUGFS",
                        &["-w", "-R", "write build/fixture-file.bin /payload", &path.0],
                        false,
                    );
                    command("E2FSCK", &["-fn", &path.0], false);
                    let image = std::fs::read(&path.0).unwrap();
                    let (sb, first, seed) = metadata(&image);
                    let ipg = le32(&image, 1064);
                    let width = if wide { 64 } else { 32 };
                    let descriptor_start = 4096 + width;
                    let descriptor = &image[descriptor_start..descriptor_start + width];
                    assert_ne!(core::bytes::read_le16(descriptor, 18).unwrap() & 1, 0);
                    let stale_number = ipg + 1;
                    let inode_bitmap = le32(descriptor, 4) as usize * 4096;
                    let inode_table = le32(descriptor, 8) as usize * 4096;
                    let source = Snapshot::from_bytes(&image);
                    let volume = core::allocation::parse(source.duplicate()).unwrap();
                    let (_, logical) = volume.index().get(1).unwrap().bitmaps();
                    assert_eq!(logical.free_count(), ipg);
                    assert!(!logical.is_set(0).unwrap());
                    assert!(core::allocated_inode::get(&volume, stale_number).is_none());
                    assert!(core::extent_claims::bind(volume.index(), stale_number, 16).is_none());
                    assert!(core::image_validation::inspect(source.duplicate()).is_some());
                    assert!(core::recovery_admission::prepare(&source).is_some());
                    for flags in [1u16, 5] {
                        let mut stale = image.clone();
                        stale[inode_bitmap..inode_bitmap + 4096].fill(255);
                        // Even a correctly checksummed old inode and a fully
                        // set physical bitmap cannot make this inode live.
                        stale[inode_table..inode_table + 256].copy_from_slice(inode_bytes(
                            &image,
                            first.inode_table,
                            12,
                        ));
                        let raw = &mut stale[inode_table..inode_table + 256];
                        let checksum =
                            core::inode::calculated_checksum(raw, stale_number, seed).unwrap();
                        raw[124..126].copy_from_slice(&(checksum as u16).to_le_bytes());
                        raw[130..132].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
                        assert!(
                            core::inode::parse_metadata_with_features(
                                raw,
                                stale_number,
                                sb.inodes(),
                                seed,
                                huge
                            )
                            .is_some()
                        );
                        let descriptor = &mut stale[descriptor_start..descriptor_start + width];
                        descriptor[18..20].copy_from_slice(&flags.to_le_bytes());
                        descriptor[26..28].fill(0x79);
                        if wide {
                            descriptor[58..60].fill(0x31);
                        }
                        seal_descriptor(descriptor, 1, seed);
                        let volume = core::allocation::parse(Snapshot::from_bytes(&stale)).unwrap();
                        assert!(core::allocated_inode::get(&volume, stale_number).is_none());
                        assert!(
                            core::extent_claims::bind(volume.index(), stale_number, 16).is_none()
                        );
                        assert!(
                            core::image_validation::inspect(Snapshot::from_bytes(&stale)).is_some()
                        );
                        let root_raw = inode_bytes(&stale, first.inode_table, 2);
                        let root = super::first_data_block(root_raw, sb.blocks()) as usize * 4096;
                        let root_seed = core::inode::inode_seed(seed, 2, le32(root_raw, 100));
                        let mut bad_target = stale.clone();
                        let mut offset = 0;
                        loop {
                            let entry = core::directory::parse(
                                &bad_target[root..root + 4096],
                                offset,
                                sb.inodes(),
                            )
                            .unwrap();
                            let name = &bad_target[root + entry.name_offset
                                ..root + entry.name_offset + entry.name_length as usize];
                            if name == b"payload" {
                                bad_target[root + offset..root + offset + 4]
                                    .copy_from_slice(&stale_number.to_le_bytes());
                                break;
                            }
                            offset = entry.next;
                            assert!(offset < 4084);
                        }
                        let checksum = core::crc::crc32c(root_seed, &bad_target[root..root + 4084]);
                        bad_target[root + 4092..root + 4096]
                            .copy_from_slice(&checksum.to_le_bytes());
                        let allocation =
                            core::allocation::parse(Snapshot::from_bytes(&bad_target)).unwrap();
                        assert!(
                            core::directory_index::build(&allocation).is_none(),
                            "a directory cannot authorize the stale inode"
                        );
                        drop(volume);
                        let descriptor = &mut stale[descriptor_start..descriptor_start + width];
                        descriptor[18..20].copy_from_slice(&4u16.to_le_bytes());
                        seal_descriptor(descriptor, 1, seed);
                        assert!(
                            core::group_metadata::parse(&Snapshot::from_bytes(&stale), 1).is_none(),
                            "clearing UNINIT restores physical bitmap checksum/count validation"
                        );
                    }
                    for (offset, value) in [
                        (14usize, ipg as u16 - 1),
                        (16, 1),
                        (28, ipg as u16 - 1),
                        (18, 8),
                        (18, 9),
                        (18, 0x8000),
                    ] {
                        let mut bad = descriptor.to_vec();
                        bad[offset..offset + 2].copy_from_slice(&value.to_le_bytes());
                        seal_descriptor(&mut bad, 1, seed);
                        assert!(
                            core::group::parse(&bad, 1, sb.blocks(), ipg, seed).is_none(),
                            "lazy counters and unknown group flags must fail closed"
                        );
                    }
                }
            }
        }
    }
}

mod lazy_block_tests {
    use core::{bitmap, block_bitmap, snapshot::Snapshot};

    use super::{
        core,
        group64_tests::{command, seal_descriptor},
        image, le32, metadata,
    };

    #[test]
    fn synthesized_block_bits_match_reserved_ranges_sparse_backups_and_partial_group_padding() {
        let image = image();
        let (_, _, seed) = metadata(&image);
        for wide in [false, true] {
            for number in [0u32, 1, 2, 3, 5, 7, 9, 25, 27, 31] {
                let backup = matches!(number, 0 | 1 | 3 | 5 | 7 | 9 | 25 | 27);
                for valid in [8191u32, 8192, 32768] {
                    for ipg in [16u32, 256, 4096, 32768] {
                        let first = number * 32768;
                        let blocks = first + valid;
                        let mut descriptor = image[4096..4128].to_vec();
                        if wide {
                            descriptor.resize(64, 0);
                        }
                        descriptor[0..4].copy_from_slice(&(first + 2).to_le_bytes());
                        descriptor[4..8].copy_from_slice(&(first + 3).to_le_bytes());
                        descriptor[8..12].copy_from_slice(&(first + 4).to_le_bytes());
                        let mut allocated = std::collections::BTreeSet::new();
                        if backup {
                            allocated.extend([first, first + 1]);
                        }
                        allocated.extend([first + 2, first + 3]);
                        allocated.extend(first + 4..first + 4 + ipg / 16);
                        let free = valid - allocated.len() as u32;
                        descriptor[12..14].copy_from_slice(&(free as u16).to_le_bytes());
                        descriptor[14..16].copy_from_slice(&(ipg as u16).to_le_bytes());
                        descriptor[16..18].fill(0);
                        descriptor[18..20].copy_from_slice(
                            &(if number == 0 { 6u16 } else { 7u16 }).to_le_bytes(),
                        );
                        descriptor[28..30].copy_from_slice(&(ipg as u16).to_le_bytes());
                        seal_descriptor(&mut descriptor, number, seed);
                        let logical =
                            block_bitmap::synthesize(&descriptor, number, blocks, ipg, seed)
                                .unwrap();
                        assert_eq!(logical.entry_count(), valid);
                        assert_eq!(logical.free_count(), free);
                        for bit in 0..32768 {
                            let expected = bit >= valid || allocated.contains(&(first + bit));
                            assert_eq!(
                                bitmap::read_bit(logical.raw_image(), bit),
                                Some(expected),
                                "group {number}, valid {valid}, ipg {ipg}, bit {bit}"
                            );
                            assert_eq!(
                                logical.is_set(bit),
                                if bit < valid { Some(expected) } else { None }
                            );
                        }
                        let mut wrong_count = descriptor.clone();
                        wrong_count[12..14].copy_from_slice(&((free + 1) as u16).to_le_bytes());
                        seal_descriptor(&mut wrong_count, number, seed);
                        assert!(
                            block_bitmap::synthesize(&wrong_count, number, blocks, ipg, seed)
                                .is_none()
                        );
                    }
                }
            }
        }
        for length in [0, 1, 31, 33, 63, 65] {
            assert!(block_bitmap::synthesize(&vec![0; length], 0, 8192, 256, seed).is_none());
        }
        assert!(block_bitmap::synthesize(&image[4096..4128], 32, 1048576, 256, seed).is_none());
        assert!(block_bitmap::synthesize(&image[4096..4128], 0, 1048577, 256, seed).is_none());
    }

    #[test]
    fn native_lazy_block_groups_ignore_stale_bytes_but_reject_metadata_aliases_and_hidden_journal_blocks()
     {
        struct ImageFile(String);
        impl Drop for ImageFile {
            fn drop(&mut self) {
                let _ = std::fs::remove_file(&self.0);
            }
        }
        for wide in [false, true] {
            for huge in [false, true] {
                for csum_seed in [false, true] {
                    let path = ImageFile(format!(
                        "build/native-lazy-blocks-{}-{wide}-{huge}-{csum_seed}.img",
                        std::process::id()
                    ));
                    let features = format!(
                        "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum{}{}{}",
                        if wide { ",64bit" } else { "" },
                        if huge { ",huge_file" } else { "" },
                        if csum_seed { ",metadata_csum_seed" } else { "" }
                    );
                    command(
                        "MKE2FS",
                        &[
                            "-q",
                            "-F",
                            "-t",
                            "ext4",
                            "-b",
                            "4096",
                            "-I",
                            "256",
                            "-N",
                            "16384",
                            "-O",
                            &features,
                            "-E",
                            "lazy_itable_init=0,lazy_journal_init=0",
                            &path.0,
                            "106496",
                        ],
                        false,
                    );
                    command(
                        "DEBUGFS",
                        &["-w", "-R", "write build/fixture-file.bin /payload", &path.0],
                        false,
                    );
                    command("E2FSCK", &["-fn", &path.0], false);
                    let image = std::fs::read(&path.0).unwrap();
                    let (sb, _, seed) = metadata(&image);
                    let width = if wide { 64 } else { 32 };
                    let ipg = le32(&image, 1064);
                    let source = Snapshot::from_bytes(&image);
                    let original = core::allocation::parse(source.duplicate()).unwrap();
                    assert_eq!(original.index().group_count(), 4);
                    assert_ne!(
                        core::bytes::read_le16(&image, 4096 + width + 18).unwrap() & 2,
                        0,
                        "native mke2fs leaves a complete unused group BLOCK_UNINIT"
                    );
                    assert!(core::image_validation::inspect(source.duplicate()).is_some());
                    assert!(core::recovery_admission::prepare(&source).is_some());
                    let mut stale = image.clone();
                    for group in [1usize, 3] {
                        let offset = 4096 + group * width;
                        let block_bitmap = le32(&stale, offset) as usize * 4096;
                        stale[block_bitmap..block_bitmap + 4096].fill(0xa5);
                        let descriptor = &mut stale[offset..offset + width];
                        descriptor[18..20].copy_from_slice(&7u16.to_le_bytes());
                        descriptor[24..28].fill(0x69);
                        if wide {
                            descriptor[56..60].fill(0xb3);
                        }
                        seal_descriptor(descriptor, group as u32, seed);
                    }
                    let volume = core::allocation::parse(Snapshot::from_bytes(&stale)).unwrap();
                    assert!(
                        core::image_validation::inspect(Snapshot::from_bytes(&stale)).is_some()
                    );
                    assert!(
                        core::recovery_admission::prepare(&Snapshot::from_bytes(&stale)).is_some()
                    );
                    for group in [1u32, 3] {
                        let meta = volume.index().get(group).unwrap();
                        let (logical, _) = meta.bitmaps();
                        assert_eq!(
                            logical.raw_image(),
                            block_bitmap::synthesize(
                                meta.descriptor(),
                                group,
                                sb.blocks(),
                                ipg,
                                seed
                            )
                            .unwrap()
                            .raw_image()
                        );
                        let first = group * 32768;
                        assert_eq!(volume.census().role_of(first).unwrap().kind, 1);
                        assert_eq!(volume.census().role_of(first + 1).unwrap().kind, 1);
                        assert_eq!(
                            volume
                                .census()
                                .role_of(meta.info().block_bitmap)
                                .unwrap()
                                .kind,
                            3
                        );
                        assert_eq!(
                            volume
                                .census()
                                .role_of(meta.info().inode_bitmap)
                                .unwrap()
                                .kind,
                            3
                        );
                        assert_eq!(
                            volume
                                .census()
                                .role_of(meta.info().inode_table)
                                .unwrap()
                                .kind,
                            3
                        );
                        assert!(!logical.is_set(260).unwrap());
                        assert_eq!(volume.census().role_of(first + 260).unwrap().kind, 0);
                    }
                    assert_eq!(
                        bitmap::read_bit(
                            volume.index().get(3).unwrap().bitmaps().0.raw_image(),
                            8192
                        ),
                        Some(true)
                    );
                    if !wide && !huge && !csum_seed {
                        for flags in [2u16, 6] {
                            let mut initialized_inodes = stale.clone();
                            let offset = 4096 + width;
                            let address = le32(&initialized_inodes, offset + 4) as usize * 4096;
                            let inode_bits = bitmap::synthesize_free_inodes(ipg, seed).unwrap();
                            initialized_inodes[address..address + 4096]
                                .copy_from_slice(inode_bits.raw_image());
                            let checksum = core::crc::crc32c(
                                seed,
                                &inode_bits.raw_image()[..ipg as usize / 8],
                            );
                            let descriptor = &mut initialized_inodes[offset..offset + width];
                            descriptor[18..20].copy_from_slice(&flags.to_le_bytes());
                            descriptor[26..28].copy_from_slice(&(checksum as u16).to_le_bytes());
                            seal_descriptor(descriptor, 1, seed);
                            assert!(
                                core::image_validation::inspect(Snapshot::from_bytes(
                                    &initialized_inodes
                                ))
                                .is_some()
                            );
                        }
                    }
                    drop(volume);
                    let mut cleared = stale.clone();
                    let offset = 4096 + width;
                    let descriptor = &mut cleared[offset..offset + width];
                    descriptor[18..20].copy_from_slice(&5u16.to_le_bytes());
                    seal_descriptor(descriptor, 1, seed);
                    assert!(
                        core::group_metadata::parse(&Snapshot::from_bytes(&cleared), 1).is_none(),
                        "clearing BLOCK_UNINIT restores physical bitmap checksum/count checks"
                    );
                    if wide && huge && csum_seed {
                        let mut alias = stale.clone();
                        let free = core::bytes::read_le16(&alias, offset + 12).unwrap() + 1;
                        let descriptor = &mut alias[offset..offset + width];
                        descriptor[0..4].copy_from_slice(&(32768u32 + 1).to_le_bytes());
                        descriptor[12..14].copy_from_slice(&free.to_le_bytes());
                        seal_descriptor(descriptor, 1, seed);
                        let total = le32(&alias, 1036) + 1;
                        alias[1036..1040].copy_from_slice(&total.to_le_bytes());
                        let checksum = core::crc::crc32c(0xffffffff, &alias[1024..2044]);
                        alias[2044..2048].copy_from_slice(&checksum.to_le_bytes());
                        assert!(
                            core::group_metadata::parse(&Snapshot::from_bytes(&alias), 1).is_some(),
                            "local synthesized bits can describe the overlapping metadata union"
                        );
                        assert!(
                            core::allocation::parse(Snapshot::from_bytes(&alias)).is_none(),
                            "global disjoint claims reject reuse of a backup GDT block as a bitmap"
                        );
                        let mut hidden_journal = image.clone();
                        let offset = 4096 + 2 * width;
                        let descriptor = &mut hidden_journal[offset..offset + width];
                        let count = 32768 - 2 - ipg / 16; // group 2 has no backup superblock
                        descriptor[12..14].copy_from_slice(&(count as u16).to_le_bytes());
                        descriptor[18..20].copy_from_slice(&7u16.to_le_bytes());
                        seal_descriptor(descriptor, 2, seed);
                        let old = core::bytes::read_le16(&image, offset + 12).unwrap() as u32;
                        let total = le32(&image, 1036) + count - old;
                        hidden_journal[1036..1040].copy_from_slice(&total.to_le_bytes());
                        let checksum = core::crc::crc32c(0xffffffff, &hidden_journal[1024..2044]);
                        hidden_journal[2044..2048].copy_from_slice(&checksum.to_le_bytes());
                        assert!(
                            core::group_metadata::parse(&Snapshot::from_bytes(&hidden_journal), 2)
                                .is_some()
                        );
                        assert!(
                            core::allocation::parse(Snapshot::from_bytes(&hidden_journal))
                                .is_none(),
                            "an uninitialized logical bitmap cannot hide allocated internal journal storage"
                        );
                    }
                }
            }
        }
    }
}

mod flex_group_tests {
    use core::{snapshot::Snapshot, superblock};

    use super::{
        core,
        group64_tests::{command, seal_descriptor},
        image, le32, metadata,
    };

    fn seal_primary(image: &mut [u8]) {
        let checksum = core::crc::crc32c(0xffffffff, &image[1024..2044]);
        image[2044..2048].copy_from_slice(&checksum.to_le_bytes());
    }

    #[test]
    fn flex_size_bookkeeping_is_total_and_normalized_independently_of_placement() {
        let image = image();
        for enabled in [false, true] {
            for raw_shift in 0..=u8::MAX {
                let mut raw = image[1024..2048].to_vec();
                raw[96..100]
                    .copy_from_slice(&(0x42u32 | if enabled { 0x200 } else { 0 }).to_le_bytes());
                raw[372] = raw_shift;
                assert_eq!(superblock::flex_enabled(&raw), Some(enabled));
                assert_eq!(
                    superblock::normalized_flex_shift(&raw),
                    Some(if enabled && (1..=31).contains(&raw_shift) {
                        raw_shift
                    } else {
                        0
                    })
                );
                let checksum = core::crc::crc32c(0xffffffff, &raw[..1020]);
                raw[1020..1024].copy_from_slice(&checksum.to_le_bytes());
                assert!(superblock::parse(&raw, image.len() as u64).is_some());
            }
        }
        for length in [0, 1, 372, 1023, 1025] {
            assert!(superblock::flex_enabled(&vec![0; length]).is_none());
            assert!(superblock::normalized_flex_shift(&vec![0; length]).is_none());
        }
    }

    #[test]
    fn native_flex_metadata_and_live_inode_tables_are_source_bound_and_globally_disjoint() {
        struct ScratchFiles(Vec<String>);
        impl Drop for ScratchFiles {
            fn drop(&mut self) {
                for path in &self.0 {
                    let _ = std::fs::remove_file(path);
                }
            }
        }
        for wide in [false, true] {
            for huge in [false, true] {
                for csum_seed in [false, true] {
                    let prefix = format!(
                        "build/native-flex-{}-{wide}-{huge}-{csum_seed}",
                        std::process::id()
                    );
                    let path = format!("{prefix}.img");
                    let script = format!("{prefix}.commands");
                    let _cleanup = ScratchFiles(vec![path.clone(), script.clone()]);
                    let features = format!(
                        "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum,flex_bg{}{}{}",
                        if wide { ",64bit" } else { "" },
                        if huge { ",huge_file" } else { "" },
                        if csum_seed { ",metadata_csum_seed" } else { "" }
                    );
                    command(
                        "MKE2FS",
                        &[
                            "-q",
                            "-F",
                            "-t",
                            "ext4",
                            "-b",
                            "4096",
                            "-I",
                            "256",
                            "-N",
                            "16384",
                            "-O",
                            &features,
                            "-E",
                            "lazy_itable_init=0,lazy_journal_init=0",
                            &path,
                            "106496",
                        ],
                        false,
                    );
                    let mut requests = String::from(
                        "write build/fixture-file.bin /payload\nwrite /dev/null /fragmented\n",
                    );
                    for logical in (0..16).step_by(2) {
                        requests.push_str(&format!("fallocate /fragmented {logical} {logical}\n"));
                    }
                    requests.push_str("set_inode_field /fragmented size 65536\ncopy_inode /payload <4097>\nseti <4097>\nunlink /payload\nlink <4097> /payload\nfreei <12>\nclri <12>\nset_bg 1 flags 6\n");
                    std::fs::write(&script, requests).unwrap();
                    command("DEBUGFS", &["-w", "-f", &script, &path], false);
                    command("E2FSCK", &["-fy", &path], true);
                    command("E2FSCK", &["-fn", &path], false);
                    if csum_seed {
                        command(
                            "TUNE2FS",
                            &["-U", "82d6883f-825a-42b8-827e-e0c77923c60e", &path],
                            false,
                        );
                    }
                    let image = std::fs::read(&path).unwrap();
                    let (sb, _, seed) = metadata(&image);
                    let width = superblock::descriptor_length(&image[1024..2048]).unwrap();
                    let ipg = le32(&image, 1064);
                    assert_eq!(ipg, 4096);
                    assert_eq!(superblock::flex_enabled(&image[1024..2048]), Some(true));
                    assert_eq!(
                        superblock::normalized_flex_shift(&image[1024..2048]),
                        Some(4)
                    );
                    let source = Snapshot::from_bytes(&image);
                    let volume = core::allocation::parse(source.duplicate()).unwrap();
                    assert!(volume.index().flex_groups());
                    let second = volume.index().get(1).unwrap();
                    let fields = second.info();
                    for address in [fields.block_bitmap, fields.inode_bitmap, fields.inode_table] {
                        assert!(address < 32768, "group 1 metadata is physically in group 0");
                        assert_eq!(volume.census().role_of(address).unwrap().kind, 3);
                    }
                    assert!(
                        core::group::parse(second.descriptor(), 1, sb.blocks(), ipg, seed)
                            .is_none()
                    );
                    assert!(
                        core::group::parse_with_features(
                            second.descriptor(),
                            1,
                            sb.blocks(),
                            ipg,
                            seed,
                            true
                        )
                        .is_some()
                    );
                    assert!(core::allocated_inode::get(&volume, 12).is_none());
                    let node = core::allocated_inode::get(&volume, 4097).unwrap();
                    assert_eq!(node.info().size, 8192);
                    let first = match core::file_read::resolve(&node, 0) {
                        core::file_read::Resolution::Data(block) => block,
                        _ => panic!("relocated inode must retain its initialized payload"),
                    };
                    assert_eq!(volume.census().role_of(first).unwrap().inode, 4097);
                    match core::file_read::chunk(&node, 0, 8192) {
                        core::file_read::Chunk::Data(bytes) => assert_eq!(
                            bytes,
                            &std::fs::read("build/fixture-file.bin").unwrap()[..4096]
                        ),
                        _ => panic!("source-bound payload read"),
                    }
                    let tree = core::extent_claims::bind(volume.index(), 13, 16).unwrap();
                    assert!(tree.tree().checked_nodes() > 1);
                    assert!(core::image_validation::inspect(source.duplicate()).is_some());
                    assert!(core::recovery_admission::prepare(&source).is_some());
                    let credentials = core::access::Credentials {
                        fsuid: node.info().uid,
                        in_inode_group: false,
                        dac_override: false,
                        dac_read_search: false,
                    };
                    let candidate =
                        core::content_write::prepare_chunk(&node, 13, &[0x87; 117], &credentials)
                            .unwrap();
                    let writer = candidate.begin_timed(2147483648, 345678901).unwrap();
                    assert_eq!(writer.engine_ref().original_count(), 2);
                    let metadata = (0..2)
                        .map(|index| writer.engine_ref().original_image(index).unwrap())
                        .find(|(block, _)| *block == fields.inode_table)
                        .unwrap()
                        .1;
                    let inode = &metadata[..256];
                    assert!(
                        core::inode::parse_metadata_with_features(
                            inode,
                            4097,
                            sb.inodes(),
                            seed,
                            huge
                        )
                        .is_some()
                    );
                    let changed_time = core::inode_time_fields::get_time(
                        inode,
                        core::inode_time_fields::Field::Mtime,
                    )
                    .unwrap();
                    assert_eq!(
                        (changed_time.seconds, changed_time.nanoseconds),
                        (2147483648, 345678901)
                    );
                    let boot = core::bootstrap::locate(&source).unwrap();
                    assert!(boot.prepare_recovery().is_some());
                    for dirty in [false, true] {
                        let updated = core::super_state::recovery_image(
                            &image[..4096],
                            image.len() as u64,
                            dirty,
                        )
                        .unwrap();
                        assert_eq!(le32(updated.as_slice(), 1120) & !4, le32(&image, 1120) & !4);
                    }
                    let offset = 4096 + width;
                    for address_offset in [0usize, 4, 8] {
                        let mut bad = second.descriptor().to_vec();
                        bad[address_offset..address_offset + 4]
                            .copy_from_slice(&sb.blocks().to_le_bytes());
                        seal_descriptor(&mut bad, 1, seed);
                        assert!(
                            core::group::parse_with_features(&bad, 1, sb.blocks(), ipg, seed, true)
                                .is_none()
                        );
                    }
                    let mut bad_count = second.descriptor().to_vec();
                    bad_count[12..14].copy_from_slice(&40000u16.to_le_bytes());
                    seal_descriptor(&mut bad_count, 1, seed);
                    assert!(
                        core::group::parse_with_features(
                            &bad_count,
                            1,
                            sb.blocks(),
                            ipg,
                            seed,
                            true
                        )
                        .is_none(),
                        "free-block counters stay within the physical group despite global metadata placement"
                    );
                    let mut without_feature = image[..4096].to_vec();
                    let flags = le32(&image, 1120) & !0x200;
                    without_feature[1120..1124].copy_from_slice(&flags.to_le_bytes());
                    seal_primary(&mut without_feature);
                    assert!(
                        superblock::parse(&without_feature[1024..2048], image.len() as u64)
                            .is_some()
                    );
                    let patch = core::patch_set::PatchSet::new()
                        .insert(0, &without_feature)
                        .ok()
                        .unwrap();
                    let switched = source.overlay(&patch).unwrap();
                    assert!(core::group_index::parse(switched.duplicate()).is_none());
                    assert!(!core::bootstrap_identity::check(&boot, &switched));
                    if wide && huge && csum_seed {
                        let mut alias = image.clone();
                        let first_bitmap = le32(&alias, 4096);
                        let descriptor = &mut alias[offset..offset + width];
                        descriptor[0..4].copy_from_slice(&first_bitmap.to_le_bytes());
                        descriptor[18..20].copy_from_slice(&6u16.to_le_bytes());
                        seal_descriptor(descriptor, 1, seed);
                        assert!(
                            core::group_metadata::parse(&Snapshot::from_bytes(&alias), 1).is_some()
                        );
                        assert!(
                            core::allocation::parse(Snapshot::from_bytes(&alias)).is_none(),
                            "FLEX_BG never permits two descriptors to own the same bitmap block"
                        );
                        let mut hidden_foreign_metadata = image.clone();
                        let free = 32768 - 4 - ipg / 16;
                        let old = core::bytes::read_le16(&image, 4108).unwrap() as u32;
                        let descriptor = &mut hidden_foreign_metadata[4096..4096 + width];
                        descriptor[12..14].copy_from_slice(&(free as u16).to_le_bytes());
                        descriptor[18..20].copy_from_slice(&6u16.to_le_bytes());
                        seal_descriptor(descriptor, 0, seed);
                        let total = le32(&image, 1036) + free - old;
                        hidden_foreign_metadata[1036..1040].copy_from_slice(&total.to_le_bytes());
                        seal_primary(&mut hidden_foreign_metadata);
                        assert!(
                            core::group_metadata::parse(
                                &Snapshot::from_bytes(&hidden_foreign_metadata),
                                0
                            )
                            .is_some()
                        );
                        assert!(
                            core::allocation::parse(Snapshot::from_bytes(&hidden_foreign_metadata))
                                .is_none(),
                            "UNINIT cannot hide metadata belonging to other logical groups"
                        );
                    }
                    command("E2FSCK", &["-fn", &path], false);
                }
            }
        }
    }
}
