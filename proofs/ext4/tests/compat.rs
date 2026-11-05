// SPDX-License-Identifier: MPL-2.0

//! Host interoperability/regression tests of the emitted library. This test
//! harness is not part of the formal claim and does not implement a mount.

extern crate verified_ext4 as core;

mod extended_attributes {
    use core::{xattr, xattr_table::ValueRef};

    use super::*;

    fn entry(
        raw: &mut [u8],
        at: usize,
        namespace: u8,
        name: &[u8],
        offset: u16,
        size: u32,
        inode: u32,
    ) {
        raw[at] = name.len() as u8;
        raw[at + 1] = namespace;
        raw[at + 2..at + 4].copy_from_slice(&offset.to_le_bytes());
        raw[at + 4..at + 8].copy_from_slice(&inode.to_le_bytes());
        raw[at + 8..at + 12].copy_from_slice(&size.to_le_bytes());
        raw[at + 16..at + 16 + name.len()].copy_from_slice(name);
    }

    fn external() -> Vec<u8> {
        let mut raw = vec![0u8; 4096];
        raw[..4].copy_from_slice(&xattr::MAGIC.to_le_bytes());
        raw[4..8].copy_from_slice(&1u32.to_le_bytes());
        raw[8..12].copy_from_slice(&1u32.to_le_bytes());
        raw
    }

    fn seal(raw: &mut [u8], block: u64, seed: u32) {
        let checksum = xattr::checksum(raw, block, seed).unwrap();
        raw[16..20].copy_from_slice(&checksum.to_le_bytes());
    }

    #[test]
    fn inline_offsets_are_relative_to_first_entry_and_lookup_uses_the_full_key() {
        let mut raw = vec![0u8; 256];
        raw[128..130].copy_from_slice(&32u16.to_le_bytes());
        raw[160..164].copy_from_slice(&xattr::MAGIC.to_le_bytes());
        // Linux permits unsorted entries in the inode body, including empty ACL names.
        entry(&mut raw, 164, 6, b"tiny", 84, 5, 0);
        entry(&mut raw, 184, 1, b"tiny", 80, 3, 0);
        entry(&mut raw, 204, 2, b"", 0, 0, 0);
        raw[244..247].copy_from_slice(b"usr");
        raw[248..253].copy_from_slice(b"hello");
        let body = xattr::parse_body(&raw, false, 100).unwrap();
        let table = body.entry_table().unwrap();
        assert_eq!(table.len(), 3);
        assert_eq!(table.find(1, b"tiny"), Some(1));
        assert_eq!(table.find(6, b"tiny"), Some(0));
        assert_eq!(table.find(2, b""), Some(2));
        assert_eq!(table.find(1, b"tin"), None);
        assert!(matches!(table.value(0), Some(ValueRef::Bytes(b"hello"))));
        assert!(matches!(table.value(1), Some(ValueRef::Bytes(b"usr"))));
        assert!(matches!(table.value(2), Some(ValueRef::Bytes(b""))));
        let mut duplicate = raw.clone();
        duplicate[185] = 6;
        assert!(xattr::parse_body(&duplicate, false, 100).is_none());
        let mut nul = raw.clone();
        nul[181] = 0;
        assert!(xattr::parse_body(&nul, false, 100).is_none());
        for offset in [0u16, 4, 56, 92, 65535] {
            let mut invalid = raw.clone();
            invalid[166..168].copy_from_slice(&offset.to_le_bytes());
            assert!(
                xattr::parse_body(&invalid, false, 100).is_none(),
                "offset {offset}"
            );
        }
    }

    #[test]
    fn external_order_bounds_terminator_checksum_and_reference_limits_are_checked() {
        let mut raw = external();
        entry(&mut raw, 32, 1, b"a", 4088, 5, 0);
        entry(&mut raw, 52, 1, b"bb", 0, 0, 0);
        raw[4088..4093].copy_from_slice(b"value");
        seal(&mut raw, 2061, 0x12345678);
        let block = xattr::parse_block(&raw, 2061, 0x12345678, true, false, 100).unwrap();
        assert_eq!(block.refcount(), 1);
        assert_eq!(block.entries().find(1, b"a"), Some(0));
        assert!(matches!(
            block.entries().value(0),
            Some(ValueRef::Bytes(b"value"))
        ));
        assert!(xattr::parse_block(&raw, 2062, 0x12345678, true, false, 100).is_none());
        assert!(xattr::parse_block(&raw, 2061, 0x12345679, true, false, 100).is_none());
        for references in [0u32, 1025, u32::MAX] {
            let mut invalid = raw.clone();
            invalid[4..8].copy_from_slice(&references.to_le_bytes());
            seal(&mut invalid, 2061, 0x12345678);
            assert!(xattr::parse_block(&invalid, 2061, 0x12345678, true, false, 100).is_none());
        }
        for offset in [32u16, 72, 4092, 65535] {
            let mut invalid = raw.clone();
            invalid[34..36].copy_from_slice(&offset.to_le_bytes());
            seal(&mut invalid, 2061, 0x12345678);
            assert!(xattr::parse_block(&invalid, 2061, 0x12345678, true, false, 100).is_none());
        }
        let mut unsorted = raw.clone();
        unsorted[53] = 0;
        assert!(xattr::parse_block(&unsorted, 0, 0, false, false, 100).is_none());
        let mut duplicate = raw.clone();
        duplicate[52] = 1;
        duplicate[68] = b'a';
        assert!(xattr::parse_block(&duplicate, 0, 0, false, false, 100).is_none());
        let mut no_terminator = raw.clone();
        no_terminator[72..].fill(0xff);
        assert!(xattr::parse_block(&no_terminator, 0, 0, false, false, 100).is_none());
    }

    #[test]
    fn value_inode_descriptors_require_the_feature_and_do_not_become_local_slices() {
        let mut raw = external();
        entry(&mut raw, 32, 1, b"large", 65535, 1 << 20, 12);
        assert!(xattr::parse_block(&raw, 1, 0, false, false, 100).is_none());
        let block = xattr::parse_block(&raw, 1, 0, false, true, 100).unwrap();
        assert!(matches!(
            block.entries().value(0),
            Some(ValueRef::Inode {
                number: 12,
                bytes: 1048576,
                hash: 0
            })
        ));
        for number in [1u32, 2, 5, 8, 101] {
            raw[36..40].copy_from_slice(&number.to_le_bytes());
            assert!(xattr::parse_block(&raw, 1, 0, false, true, 100).is_none());
        }
        raw[36..40].copy_from_slice(&12u32.to_le_bytes());
        raw[40..44].copy_from_slice(&((1u32 << 24) + 1).to_le_bytes());
        assert!(xattr::parse_block(&raw, 1, 0, false, true, 100).is_none());
    }

    fn command(binary: &str, args: &[&str]) {
        let result = std::process::Command::new(binary)
            .args(args)
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{args:?}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
    }

    #[test]
    fn linux_inline_external_and_shared_attributes_bind_source_checksums_and_allocation() {
        use core::{allocation, image_validation, snapshot::Snapshot, xattr_inode};
        let mkfs = std::env::var("MKE2FS_BIN").unwrap_or_else(|_| "mke2fs".into());
        let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
        let fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        let path = "build/xattr-linux-storage.img";
        let _ = std::fs::remove_file(path);
        command(
            &mkfs,
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
                "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum,ext_attr",
                "-E",
                "lazy_itable_init=0,lazy_journal_init=0",
                path,
                "16384",
            ],
        );
        let large: Vec<u8> = (0..1000).map(|i| (i % 250) as u8).collect();
        std::fs::write("build/xattr-linux-large.bin", &large).unwrap();
        for instruction in [
            "write build/fixture-file.bin /payload",
            "write build/fixture-file.bin /second",
            "ea_set /payload user.tiny hello",
            "ea_set -f build/xattr-linux-large.bin /payload user.large",
            "ea_set -f build/xattr-linux-large.bin /second user.large",
        ] {
            command(&debugfs, &["-w", "-R", instruction, path]);
        }
        command(&fsck, &["-fn", path]);
        let img = std::fs::read(path).unwrap();
        let (_, group, seed) = metadata(&img);
        let first = xattr::inode_pointer(inode_bytes(&img, group.inode_table, 12)).unwrap() as u32;
        let second = xattr::inode_pointer(inode_bytes(&img, group.inode_table, 13)).unwrap() as u32;
        assert_ne!(first, second);
        let source = Snapshot::from_bytes(&img);
        let volume =
            allocation::parse(source.duplicate()).expect("complete xattr allocation census");
        assert!(image_validation::inspect(source.duplicate()).is_some());
        for block in [first, second] {
            assert_eq!(volume.census().role_of(block).unwrap().kind, 7);
        }
        let attributes = xattr_inode::inspect(volume.index(), 12).unwrap();
        assert!(matches!(
            attributes.get(1, b"tiny"),
            Some(ValueRef::Bytes(b"hello"))
        ));
        match attributes.get(1, b"large").unwrap() {
            ValueRef::Bytes(bytes) => assert_eq!(bytes, large),
            _ => panic!("local block value"),
        }
        assert!(attributes.get(6, b"tiny").is_none());

        let mut shared = img.clone();
        let second_inode = group.inode_table as usize * 4096 + 12 * 256;
        shared[second_inode + 104..second_inode + 108].copy_from_slice(&first.to_le_bytes());
        seal_inode_image(&mut shared, group.inode_table, 13, seed);
        let first_offset = first as usize * 4096;
        shared[first_offset + 4..first_offset + 8].copy_from_slice(&2u32.to_le_bytes());
        seal(
            &mut shared[first_offset..first_offset + 4096],
            first as u64,
            seed,
        );
        let bitmap = group.block_bitmap as usize * 4096;
        shared[bitmap + second as usize / 8] &= !(1 << (second % 8));
        seal_single_group_allocation(&mut shared);
        let shared_path = "build/xattr-linux-shared.img";
        std::fs::write(shared_path, &shared).unwrap();
        command(&fsck, &["-fn", shared_path]);
        let source = Snapshot::from_bytes(&shared);
        let volume = allocation::parse(source.duplicate()).expect("one claim for shared storage");
        assert_eq!(volume.census().role_of(first).unwrap().kind, 7);
        assert_eq!(volume.census().role_of(second).unwrap().kind, 0);
        assert!(image_validation::inspect(source).is_some());
        for number in [12, 13] {
            assert!(
                matches!(xattr_inode::inspect(volume.index(), number).unwrap().get(1, b"large"), Some(ValueRef::Bytes(bytes)) if bytes == large)
            );
        }
        let mut wrong_count = shared.clone();
        wrong_count[first_offset + 4..first_offset + 8].copy_from_slice(&1u32.to_le_bytes());
        seal(
            &mut wrong_count[first_offset..first_offset + 4096],
            first as u64,
            seed,
        );
        assert!(allocation::parse(Snapshot::from_bytes(&wrong_count)).is_none());
        let mut duplicate = img.clone();
        duplicate[first_offset + 32] = 4;
        duplicate[first_offset + 48..first_offset + 52].copy_from_slice(b"tiny");
        duplicate[first_offset + 52..first_offset + 56].fill(0);
        seal(
            &mut duplicate[first_offset..first_offset + 4096],
            first as u64,
            seed,
        );
        assert!(
            allocation::parse(Snapshot::from_bytes(&duplicate)).is_none(),
            "the same key cannot appear in both locations"
        );
        let mut wrong_accounting = img.clone();
        let first_inode = group.inode_table as usize * 4096 + 11 * 256;
        wrong_accounting[first_inode + 28..first_inode + 32].copy_from_slice(&16u32.to_le_bytes());
        seal_inode_image(&mut wrong_accounting, group.inode_table, 12, seed);
        assert!(allocation::parse(Snapshot::from_bytes(&wrong_accounting)).is_none());
        let mut alias = img.clone();
        let data = le32(&img, first_inode + 60);
        let data_offset = data as usize * 4096;
        alias[data_offset..data_offset + 4096]
            .copy_from_slice(&img[first_offset..first_offset + 4096]);
        seal(
            &mut alias[data_offset..data_offset + 4096],
            data as u64,
            seed,
        );
        alias[first_inode + 104..first_inode + 108].copy_from_slice(&data.to_le_bytes());
        seal_inode_image(&mut alias, group.inode_table, 12, seed);
        alias[bitmap + first as usize / 8] &= !(1 << (first % 8));
        seal_single_group_allocation(&mut alias);
        assert!(
            allocation::parse(Snapshot::from_bytes(&alias)).is_none(),
            "valid xattr bytes cannot alias file data"
        );

        let mut with_acl = img.clone();
        let raw = &mut with_acl[first_inode..first_inode + 256];
        // A storage-level ACL value is opaque until the ACL evaluator checks it.
        entry(raw, 184, 2, b"", 0, 0, 0);
        seal_inode_image(&mut with_acl, group.inode_table, 12, seed);
        let volume = allocation::parse(Snapshot::from_bytes(&with_acl)).unwrap();
        let node = core::allocated_inode::get(&volume, 12).unwrap();
        let credentials = core::access::Credentials {
            fsuid: 0,
            in_inode_group: true,
            dac_override: true,
            dac_read_search: true,
        };
        assert!(
            core::content_write::prepare_chunk(&node, 0, b"x", &credentials).is_none(),
            "mode-only authorization must not bypass an access ACL"
        );
        let mut moved = img.clone();
        let available = img.len() / 4096 - 1;
        moved[available * 4096..(available + 1) * 4096]
            .copy_from_slice(&img[first_offset..first_offset + 4096]);
        assert!(
            xattr::parse_block(
                &moved[available * 4096..(available + 1) * 4096],
                available as u64,
                seed,
                true,
                false,
                4096
            )
            .is_none()
        );
        let _ = std::fs::remove_file(path);
        let _ = std::fs::remove_file(shared_path);
        let _ = std::fs::remove_file("build/xattr-linux-large.bin");
    }
}

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
        let complete = extent_claims::audit_allocated(&node);
        assert_eq!(complete.tree().checked_nodes(), depth as u64 + 1);
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

mod feature_coverage {
    use core::{backup_layout, feature_policy, image_validation, snapshot::Snapshot};

    use super::*;

    fn primary_checksum(image: &mut [u8]) {
        let checksum = core::crc::crc32c(0xffffffff, &image[1024..2044]);
        image[2044..2048].copy_from_slice(&checksum.to_le_bytes());
    }

    #[test]
    fn feature_policy_rejects_each_unknown_bit_without_accepting_missing_required_semantics() {
        for bit in 0..32 {
            let compat = 4 | (1u32 << bit);
            assert_eq!(
                feature_policy::compatible_flags(compat),
                matches!(bit, 2 | 3 | 5 | 9 | 11),
                "COMPAT bit {bit}"
            );
            let incompat = 0x42 | (1u32 << bit);
            assert_eq!(
                feature_policy::incompatible_flags(incompat),
                matches!(bit, 1 | 2 | 6 | 7 | 9 | 13 | 14),
                "INCOMPAT bit {bit}"
            );
            let ro = 0x443 | (1u32 << bit);
            assert_eq!(
                feature_policy::readonly_compatible_flags(ro),
                matches!(bit, 0 | 1 | 2 | 3 | 5 | 6 | 10 | 12),
                "RO_COMPAT bit {bit}"
            );
        }
        assert!(!feature_policy::compatible_flags(0xa00));
        for required in [2, 0x40, 0x400] {
            assert!(!feature_policy::readonly_compatible_flags(
                0x146f & !required
            ));
        }
    }

    #[test]
    fn all_backup_policies_match_linux_precedence_and_ignore_out_of_range_backup_slots() {
        let mut sb = vec![0u8; 1024];
        for number in 0..32 {
            assert_eq!(backup_layout::has_backup(&sb, number), Some(true));
        }
        sb[100..104].copy_from_slice(&1u32.to_le_bytes());
        for number in 0..32 {
            assert_eq!(
                backup_layout::has_backup(&sb, number),
                core::group_claims::backup_group(number)
            );
        }
        sb[92..96].copy_from_slice(&0x204u32.to_le_bytes());
        sb[588..592].copy_from_slice(&2u32.to_le_bytes());
        sb[592..596].copy_from_slice(&31u32.to_le_bytes());
        for number in 0..32 {
            assert_eq!(
                backup_layout::has_backup(&sb, number),
                Some(matches!(number, 0 | 2 | 31))
            );
        }
        sb[588..592].copy_from_slice(&u32::MAX.to_le_bytes());
        sb[592..596].copy_from_slice(&u32::MAX.to_le_bytes());
        for number in 0..32 {
            assert_eq!(backup_layout::has_backup(&sb, number), Some(number == 0));
        }
        assert_eq!(backup_layout::has_backup(&sb, 32), None);
        assert_eq!(backup_layout::has_backup(&sb[..1023], 0), None);
    }

    #[test]
    fn readonly_and_stable_inode_markers_bind_actual_source_validation() {
        let mut image = image();
        let compat = le32(&image, 1116) | 0x800;
        image[1116..1120].copy_from_slice(&compat.to_le_bytes());
        let ro = le32(&image, 1124) | 0x1004;
        image[1124..1128].copy_from_slice(&ro.to_le_bytes());
        primary_checksum(&mut image);
        assert_eq!(feature_policy::is_readonly(&image[1024..2048]), Some(true));
        assert_eq!(
            feature_policy::has_stable_inodes(&image[1024..2048]),
            Some(true)
        );
        let source = Snapshot::from_bytes(&image);
        assert!(image_validation::inspect(source.duplicate()).is_some());
        let boot = core::bootstrap::locate(&source).unwrap();
        let mut changed = image.clone();
        changed[1128] ^= 1;
        primary_checksum(&mut changed);
        assert!(!core::bootstrap_identity::check(
            &boot,
            &Snapshot::from_bytes(&changed)
        ));
    }

    #[test]
    fn dir_nlink_unknown_directory_count_keeps_exact_regular_counts_and_topology_checks() {
        let mut image = image();
        let (_, group, seed) = metadata(&image);
        let ro = le32(&image, 1124) | 0x20;
        image[1124..1128].copy_from_slice(&ro.to_le_bytes());
        primary_checksum(&mut image);
        let root = group.inode_table as usize * 4096 + 256;
        image[root + 26..root + 28].copy_from_slice(&1u16.to_le_bytes());
        seal_inode_image(&mut image, group.inode_table, 2, seed);
        assert!(image_validation::inspect(Snapshot::from_bytes(&image)).is_some());
        let mut wrong = image.clone();
        wrong[root + 26..root + 28].copy_from_slice(&2u16.to_le_bytes());
        seal_inode_image(&mut wrong, group.inode_table, 2, seed);
        assert!(image_validation::inspect(Snapshot::from_bytes(&wrong)).is_none());
        let file = group.inode_table as usize * 4096 + 11 * 256;
        image[file + 26..file + 28].copy_from_slice(&2u16.to_le_bytes());
        seal_inode_image(&mut image, group.inode_table, 12, seed);
        assert!(image_validation::inspect(Snapshot::from_bytes(&image)).is_none());
        assert_eq!(core::link_count::increment_directory(65000, true), Some(1));
        assert_eq!(core::link_count::increment_directory(65000, false), None);
        assert_eq!(core::link_count::increment_directory(1, true), Some(1));
        assert_eq!(core::link_count::decrement_directory(1), 1);
        assert_eq!(core::link_count::decrement_directory(3), 2);
    }
    fn command(binary: &str, args: &[&str]) {
        let result = std::process::Command::new(binary)
            .args(args)
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{binary} {args:?}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
    }

    #[test]
    fn linux_sparse_super2_and_nonsparse_volumes_use_the_actual_backup_claims_and_lazy_bitmaps() {
        let mkfs = std::env::var("MKE2FS_BIN").unwrap_or_else(|_| "mke2fs".into());
        let fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        for (label, extra, expected) in [
            ("all", "", [true, true, true]),
            ("explicit", ",sparse_super2", [true, true, true]),
            ("classic", ",sparse_super", [true, true, false]),
            ("explicit-none", ",sparse_super2", [true, false, false]),
            ("wide-flex-all", ",64bit,flex_bg", [true, true, true]),
        ] {
            let path = format!("build/feature-backups-{label}.img");
            let _ = std::fs::remove_file(&path);
            let features = format!(
                "none,has_journal,extent,filetype,large_file,extra_isize,metadata_csum{extra}"
            );
            let extended = if label == "explicit-none" {
                "lazy_itable_init=0,lazy_journal_init=0,num_backup_sb=0"
            } else {
                "lazy_itable_init=0,lazy_journal_init=0"
            };
            command(
                &mkfs,
                &[
                    "-q", "-F", "-t", "ext4", "-b", "4096", "-I", "256", "-O", &features, "-E",
                    extended, &path, "98304",
                ],
            );
            command(&fsck, &["-fn", &path]);
            let image = std::fs::read(&path).unwrap();
            let sb = &image[1024..2048];
            for group in 0..3 {
                assert_eq!(
                    backup_layout::has_backup(sb, group),
                    Some(expected[group as usize]),
                    "{label}, group {group}"
                );
            }
            let source = Snapshot::from_bytes(&image);
            let checked = image_validation::inspect(source.duplicate()).unwrap();
            assert_eq!(checked.source().partition_bytes(), image.len() as u64);
            let volume = core::allocation::parse(source.duplicate()).unwrap();
            let roles = volume.census();
            for number in 1..3 {
                let role = roles.role_of(number * 32768).unwrap();
                if expected[number as usize] {
                    assert_eq!(role.kind, 1, "{label}, backup group {number}");
                } else {
                    assert_ne!(role.kind, 1, "{label}, non-backup group {number}");
                }
            }
            if label == "explicit" {
                let mut changed = image.clone();
                changed[1612..1616].copy_from_slice(&u32::MAX.to_le_bytes());
                changed[1616..1620].copy_from_slice(&u32::MAX.to_le_bytes());
                primary_checksum(&mut changed);
                assert!(
                    image_validation::inspect(Snapshot::from_bytes(&changed)).is_none(),
                    "allocated backup blocks cannot disappear from the source census"
                );
            }
            let _ = std::fs::remove_file(&path);
        }
    }
    #[test]
    fn source_selected_policy_composes_across_all_32_new_feature_combinations() {
        let image = image();
        let source = Snapshot::from_bytes(&image);
        for stable in [false, true] {
            for selected in 0..16 {
                let mut primary = image[..4096].to_vec();
                let compat = le32(&primary, 1116) | if stable { 0x800 } else { 0 };
                primary[1116..1120].copy_from_slice(&compat.to_le_bytes());
                let bits = if selected & 1 != 0 { 8 } else { 0 }
                    | if selected & 2 != 0 { 0x20 } else { 0 }
                    | if selected & 4 != 0 { 4 } else { 0 }
                    | if selected & 8 != 0 { 0x1000 } else { 0 };
                let flags = le32(&primary, 1124) | bits;
                primary[1124..1128].copy_from_slice(&flags.to_le_bytes());
                primary_checksum(&mut primary);
                let patches = core::patch_set::PatchSet::new()
                    .insert(0, &primary)
                    .ok()
                    .unwrap();
                let candidate = source.overlay(&patches).unwrap();
                assert!(
                    image_validation::inspect(candidate.duplicate()).is_some(),
                    "stable={stable}, flags={bits:#x}"
                );
                let boot = core::bootstrap::locate(&candidate).unwrap();
                let parsed =
                    core::superblock::parse(&boot.primary()[1024..2048], image.len() as u64)
                        .unwrap();
                assert_eq!(
                    parsed.feature_flags(),
                    (compat, flags, le32(&primary, 1120))
                );
                assert_eq!(parsed.read_only(), selected & 8 != 0);
                assert_eq!(
                    feature_policy::has_stable_inodes(&boot.primary()[1024..2048]),
                    Some(stable)
                );
                assert_eq!(
                    feature_policy::is_readonly(&boot.primary()[1024..2048]),
                    Some(selected & 8 != 0)
                );
            }
        }
    }
}

mod posix_acl {
    use core::acl;

    use super::*;

    fn disk(entries: &[(u16, u16, u32)]) -> Vec<u8> {
        let mut raw = 1u32.to_le_bytes().to_vec();
        for &(tag, bits, id) in entries {
            raw.extend(tag.to_le_bytes());
            raw.extend(bits.to_le_bytes());
            if tag == 2 || tag == 8 {
                raw.extend(id.to_le_bytes());
            }
        }
        raw
    }

    #[test]
    fn compact_acl_codec_checks_width_order_mask_permission_and_identifier_boundaries() {
        let raw = disk(&[
            (1, 7, 0),
            (2, 4, 1234),
            (4, 0, 0),
            (8, 6, 100),
            (16, 4, 0),
            (32, 0, 0),
        ]);
        let parsed = acl::parse(&raw).unwrap();
        assert_eq!(parsed.count(), 6);
        assert_eq!(parsed.entry(1).unwrap().id, 1234);
        assert_eq!(parsed.entry(3).unwrap().offset, 20);
        assert!(parsed.mode_matches(0o740));
        assert!(!parsed.mode_matches(0o777));
        assert!(parsed.entry(6).is_none());
        for end in 0..raw.len() {
            assert!(acl::parse(&raw[..end]).is_none(), "truncated ACL at {end}");
        }
        let mut wrong_version = raw.clone();
        wrong_version[..4].copy_from_slice(&2u32.to_le_bytes());
        assert!(
            acl::parse(&wrong_version).is_none(),
            "VFS ACL encoding is not the compact ext4 encoding"
        );
        for invalid in [
            vec![(4, 7, 0), (32, 7, 0)],
            vec![(1, 7, 0), (32, 7, 0)],
            vec![(1, 7, 0), (2, 7, 1234), (4, 7, 0), (32, 7, 0)],
            vec![(1, 7, 0), (4, 7, 0), (8, 7, 10), (32, 7, 0)],
            vec![(1, 7, 0), (4, 7, 0), (16, 7, 0), (16, 7, 0), (32, 7, 0)],
            vec![(1, 7, 0), (4, 7, 0), (2, 7, 1234), (16, 7, 0), (32, 7, 0)],
            vec![(1, 8, 0), (4, 7, 0), (32, 7, 0)],
            vec![
                (1, 7, 0),
                (2, 7, u32::MAX),
                (4, 7, 0),
                (16, 7, 0),
                (32, 7, 0),
            ],
            vec![(1, 7, 0), (4, 7, 0), (64, 7, 0), (32, 7, 0)],
        ] {
            assert!(acl::parse(&disk(&invalid)).is_none(), "{invalid:?}");
        }
        let simple = disk(&[(1, 6, 0), (4, 4, 0), (32, 0, 0)]);
        assert!(acl::parse(&simple).is_some(), "base ACL needs no mask");
    }

    #[test]
    fn permission_order_masks_named_users_and_never_combines_distinct_group_grants() {
        for mask in 0..8u16 {
            let raw = disk(&[
                (1, 6, 0),
                (2, 6, 1234),
                (4, 4, 0),
                (8, 2, 200),
                (16, mask, 0),
                (32, 7, 0),
            ]);
            let parsed = acl::parse(&raw).unwrap();
            for request in 0..8u8 {
                assert_eq!(
                    parsed.allows(1000, 100, 1000, &[100, 200], request),
                    6 & request == request,
                    "owner precedes every other entry"
                );
                assert_eq!(
                    parsed.allows(1000, 100, 1234, &[100, 200], request),
                    (6 & mask as u8) & request == request,
                    "named user does not fall through"
                );
                assert_eq!(
                    parsed.allows(1000, 100, 3000, &[100, 200], request),
                    (4 & request == request || 2 & request == request)
                        && mask as u8 & request == request,
                    "one group entry must satisfy the complete request"
                );
                assert_eq!(
                    parsed.allows(1000, 100, 3000, &[], request),
                    true,
                    "other applies only without a matching group"
                );
            }
            assert!(!parsed.allows(1000, 100, 3000, &[100, 200], 6));
            assert!(!parsed.allows(1000, 100, 1234, &[], 1));
            assert!(!parsed.allows(1000, 100, 3000, &[], 8));
        }
        let raw = disk(&[(1, 0, 0), (2, 7, 1000), (4, 7, 0), (16, 7, 0), (32, 7, 0)]);
        let parsed = acl::parse(&raw).unwrap();
        assert!(
            !parsed.allows(1000, 100, 1000, &[100], 4),
            "owner wins even over a matching named-user ID"
        );
    }

    fn command(binary: &str, args: &[&str]) {
        let result = std::process::Command::new(binary)
            .args(args)
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{args:?}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
    }

    #[test]
    fn linux_acl_bytes_bind_authorization_and_the_actual_content_write_candidate() {
        use core::{
            access::Credentials, acl_access, allocated_inode, allocation, content_write,
            snapshot::Snapshot, xattr_inode, xattr_table::ValueRef,
        };
        let path = "build/acl-linux-source.img";
        let value_path = "build/acl-linux-uapi.bin";
        std::fs::write(path, image()).unwrap();
        let mut uapi = 2u32.to_le_bytes().to_vec();
        for (tag, bits, id) in [
            (1u16, 6u16, u32::MAX),
            (2, 4, 1234),
            (4, 0, u32::MAX),
            (16, 4, u32::MAX),
            (32, 0, u32::MAX),
        ] {
            uapi.extend(tag.to_le_bytes());
            uapi.extend(bits.to_le_bytes());
            uapi.extend(id.to_le_bytes());
        }
        std::fs::write(value_path, uapi).unwrap();
        let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
        let fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        command(&debugfs, &["-w", "-R", "feature ext_attr", path]);
        command(
            &debugfs,
            &[
                "-w",
                "-R",
                "ea_set -f build/acl-linux-uapi.bin /payload system.posix_acl_access",
                path,
            ],
        );
        command(&debugfs, &["-w", "-R", "sif /payload mode 0100640", path]);
        command(&fsck, &["-fn", path]);
        let img = std::fs::read(path).unwrap();
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        let attrs = xattr_inode::inspect(volume.index(), 12).unwrap();
        let raw = match attrs.get(2, b"").unwrap() {
            ValueRef::Bytes(raw) => raw,
            _ => panic!("compact local ACL"),
        };
        assert_eq!(le32(raw, 0), 1);
        assert_eq!(acl::parse(raw).unwrap().count(), 5);
        let named = Credentials {
            fsuid: 1234,
            in_inode_group: false,
            dac_override: false,
            dac_read_search: false,
        };
        assert!(acl_access::authorize(&node, &named, &[], 4).is_some());
        assert!(acl_access::authorize(&node, &named, &[], 2).is_none());
        assert!(content_write::prepare_chunk(&node, 0, b"x", &named).is_none());
        let owner = Credentials {
            fsuid: node.info().uid,
            in_inode_group: false,
            dac_override: false,
            dac_read_search: false,
        };
        let grant = acl_access::authorize(&node, &owner, &[], 2).unwrap();
        let candidate = content_write::prepare_authorized(grant, 0, b"verified ACL").unwrap();
        assert_eq!(&candidate.after_image().as_slice()[..12], b"verified ACL");
        assert!(
            candidate.begin_timed(123, 456).is_some(),
            "ACL-authorized data/time closure uses complete writer admission"
        );
        let privileged = Credentials {
            fsuid: 1234,
            in_inode_group: false,
            dac_override: true,
            dac_read_search: false,
        };
        assert!(acl_access::authorize(&node, &privileged, &[], 2).is_some());
        assert!(
            acl_access::authorize(&node, &privileged, &[], 1).is_none(),
            "override cannot execute an inode without execute mode bits"
        );
        let mismatch = Credentials {
            fsuid: 1234,
            in_inode_group: true,
            dac_override: false,
            dac_read_search: false,
        };
        assert!(
            acl_access::authorize(&node, &mismatch, &[], 4).is_none(),
            "mode fallback membership must match the supplied mapped group set"
        );
        let (_, group, seed) = metadata(&img);
        let position = group.inode_table as usize * 4096 + 11 * 256;
        let mut inconsistent = img.clone();
        inconsistent[position..position + 2].copy_from_slice(&0o100644u16.to_le_bytes());
        seal_inode_image(&mut inconsistent, group.inode_table, 12, seed);
        let volume = allocation::parse(Snapshot::from_bytes(&inconsistent)).unwrap();
        let inconsistent_node = allocated_inode::get(&volume, 12).unwrap();
        assert!(
            acl_access::authorize(&inconsistent_node, &privileged, &[], 2).is_none(),
            "mode/ACL disagreement is not bypassed by a capability"
        );
        let body =
            core::xattr::parse_body(inode_bytes(&img, group.inode_table, 12), false, 4096).unwrap();
        let table = body.entry_table().unwrap();
        let value_offset = table
            .metadata(table.find(2, b"").unwrap())
            .unwrap()
            .value_offset;
        let mut malformed = img.clone();
        malformed[position + value_offset..position + value_offset + 4]
            .copy_from_slice(&2u32.to_le_bytes());
        seal_inode_image(&mut malformed, group.inode_table, 12, seed);
        let volume = allocation::parse(Snapshot::from_bytes(&malformed)).unwrap();
        let malformed_node = allocated_inode::get(&volume, 12).unwrap();
        assert!(
            acl_access::authorize(&malformed_node, &privileged, &[], 2).is_none(),
            "malformed ACLs are rejected before capability evaluation"
        );
        let _ = std::fs::remove_file(path);
        let _ = std::fs::remove_file(value_path);
    }
}

mod htree_indexes {
    use core::htree;

    use super::*;

    fn seal(raw: &mut [u8], first: usize, seed: u32) {
        let count = core::bytes::read_le16(raw, first + 2).unwrap() as usize;
        let limit = core::bytes::read_le16(raw, first).unwrap() as usize;
        let tail = first + limit * 8;
        let prefix = core::crc::crc32c(seed, &raw[..first + count * 8]);
        let reserved = core::crc::crc32c(prefix, &raw[tail..tail + 4]);
        let checksum = core::crc::crc32c(reserved, &[0, 0, 0, 0]);
        raw[tail + 4..tail + 8].copy_from_slice(&checksum.to_le_bytes());
    }

    fn block(size: usize, root: bool, checksummed: bool) -> Vec<u8> {
        let mut raw = vec![0u8; size];
        let first = if root { 32 } else { 8 };
        if root {
            raw[0..4].copy_from_slice(&12u32.to_le_bytes());
            raw[4..6].copy_from_slice(&12u16.to_le_bytes());
            raw[6] = 1;
            raw[7] = 2;
            raw[8] = b'.';
            raw[12..16].copy_from_slice(&2u32.to_le_bytes());
            raw[16..18].copy_from_slice(&((size - 12) as u16).to_le_bytes());
            raw[18] = 2;
            raw[19] = 2;
            raw[20] = b'.';
            raw[21] = b'.';
            raw[28] = 1;
            raw[29] = 8;
        } else {
            let record = if size == 65536 { u16::MAX } else { size as u16 };
            raw[4..6].copy_from_slice(&record.to_le_bytes());
        }
        let limit = (size - first - if checksummed { 8 } else { 0 }) / 8;
        raw[first..first + 2].copy_from_slice(&(limit as u16).to_le_bytes());
        raw[first + 2..first + 4].copy_from_slice(&5u16.to_le_bytes());
        for (i, (hash, logical)) in [
            (0u32, 1u32),
            (100, 2),
            (101, 0xa0000003),
            (101, 4),
            (200, 5),
        ]
        .into_iter()
        .enumerate()
        {
            if i > 0 {
                raw[first + i * 8..first + i * 8 + 4].copy_from_slice(&hash.to_le_bytes());
            }
            raw[first + i * 8 + 4..first + i * 8 + 8].copy_from_slice(&logical.to_le_bytes());
        }
        if checksummed {
            seal(&mut raw, first, 0x12345678);
        }
        raw
    }

    #[test]
    fn htree_tables_route_hash_boundaries_and_all_collision_continuations_across_geometries() {
        for size in [1024, 2048, 4096, 8192, 16384, 32768, 65536] {
            for checksummed in [false, true] {
                let raw = block(size, true, checksummed);
                let root =
                    htree::parse_root(&raw, 100, 4096, 0x12345678, checksummed, false).unwrap();
                assert_eq!(root.hash_and_levels(), (1, 0));
                let index = root.routing_index();
                assert_eq!(index.child_count(), 5);
                assert_eq!(
                    index.child(2).unwrap().block,
                    3,
                    "high coalesce bits are masked"
                );
                assert!(index.child(5).is_none());
                for (hash, expected) in [
                    (0, 0),
                    (99, 0),
                    (100, 1),
                    (101, 3),
                    (199, 3),
                    (200, 4),
                    (u32::MAX, 4),
                ] {
                    assert_eq!(
                        index.probe(hash),
                        expected,
                        "{size}, checksum={checksummed}, hash={hash}"
                    );
                }
                assert!(index.continues(100, 2));
                assert!(index.continues(100, 3));
                assert!(!index.continues(100, 0));
                assert!(!index.continues(100, 4));
                assert!(!index.continues(100, usize::MAX));
                let raw = block(size, false, checksummed);
                let index = htree::parse_node(&raw, 100, 0x12345678, checksummed).unwrap();
                assert_eq!(index.probe(100), 1);
                assert!(index.continues(100, 2));
            }
        }
    }

    #[test]
    fn htree_checksums_headers_sorted_keys_and_logical_child_bounds_are_checked() {
        let raw = block(4096, true, true);
        for (offset, byte) in [
            (8usize, b'/'),
            (24, 1),
            (28, 3),
            (29, 0),
            (30, 2),
            (31, 1),
            (32, 0),
            (34, 0),
        ] {
            let mut invalid = raw.clone();
            invalid[offset] = byte;
            seal(&mut invalid, 32, 0x12345678);
            assert!(
                htree::parse_root(&invalid, 100, 4096, 0x12345678, true, false).is_none(),
                "header offset {offset}"
            );
        }
        let mut deep = raw.clone();
        deep[30] = 2;
        seal(&mut deep, 32, 0x12345678);
        assert!(htree::parse_root(&deep, 100, 4096, 0x12345678, true, true).is_some());
        let mut wrong = raw.clone();
        wrong[44] ^= 1;
        assert!(htree::parse_root(&wrong, 100, 4096, 0x12345678, true, false).is_none());
        assert!(htree::parse_root(&raw, 100, 4096, 0x12345679, true, false).is_none());
        let mut unused = raw.clone();
        unused[1000] = 1;
        assert!(
            htree::parse_root(&unused, 100, 4096, 0x12345678, true, false).is_some(),
            "Linux checksum omits unused table slots"
        );
        let mut unsorted = raw.clone();
        unsorted[56..60].copy_from_slice(&99u32.to_le_bytes());
        seal(&mut unsorted, 32, 0x12345678);
        assert!(htree::parse_root(&unsorted, 100, 4096, 0x12345678, true, false).is_none());
        for pointer in [0u32, 100, 0xf0000000, 0xffffffff] {
            let mut invalid = raw.clone();
            invalid[36..40].copy_from_slice(&pointer.to_le_bytes());
            seal(&mut invalid, 32, 0x12345678);
            assert!(htree::parse_root(&invalid, 100, 4096, 0x12345678, true, false).is_none());
        }
    }

    fn command(binary: &str, args: &[&str], modified: bool) -> Vec<u8> {
        let result = std::process::Command::new(binary)
            .args(args)
            .output()
            .unwrap();
        assert!(
            result.status.success() || modified && result.status.code() == Some(1),
            "{args:?}: {} {}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
        result.stdout
    }

    #[test]
    fn linux_indexed_directories_validate_source_names_ranges_namespace_and_deep_largedir_writes() {
        let mkfs = std::env::var("MKE2FS_BIN").unwrap_or_else(|_| "mke2fs".into());
        let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
        let fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        let path = "build/htree-linux.img";
        let _ = std::fs::remove_file(path);
        command(
            &mkfs,
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
                "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum,dir_index",
                "-E",
                "lazy_itable_init=0,lazy_journal_init=0",
                path,
                "16384",
            ],
            false,
        );
        std::fs::write("build/htree-empty.bin", b"").unwrap();
        std::fs::write("build/htree-payload.bin", [0x3au8; 128]).unwrap();
        let mut script = String::from("mkdir /indexed\n");
        for n in 0..300 {
            let input = if n == 0 {
                "build/htree-payload.bin"
            } else {
                "build/htree-empty.bin"
            };
            script += &format!("write {input} /indexed/{n:04}-{}\n", "x".repeat(210));
        }
        std::fs::write("build/htree-debugfs.txt", script).unwrap();
        command(
            &debugfs,
            &["-w", "-f", "build/htree-debugfs.txt", path],
            false,
        );
        command(&fsck, &["-fyD", path], true);
        command(&fsck, &["-fn", path], false);
        let img = std::fs::read(path).unwrap();
        let inodes = le32(&img, 1024);
        let table = le32(&img, 4104);
        let inode = inode_bytes(&img, table, 12);
        assert_ne!(
            le32(inode, 32) & 0x1000,
            0,
            "e2fsck actually enabled the inode index"
        );
        let blocks = le32(inode, 4) / 4096;
        let seed = core::superblock::metadata_checksum_seed(&img[1024..2048]).unwrap();
        let seed = core::inode::inode_seed(seed, 12, le32(inode, 100));
        let mapped = command(&debugfs, &["-R", "bmap /indexed 0", path], false);
        let physical = String::from_utf8(mapped)
            .unwrap()
            .trim()
            .parse::<usize>()
            .unwrap();
        let raw = &img[physical * 4096..(physical + 1) * 4096];
        let root = htree::parse_root(raw, blocks, inodes, seed, true, false).unwrap();
        assert_eq!(root.hash_and_levels().1, 0);
        let index = root.routing_index();
        assert!(index.child_count() > 1);
        let mut logical_blocks = vec![&img[0..0]; blocks as usize];
        logical_blocks[0] = raw;
        for i in 0..index.child_count() {
            let edge = index.child(i).unwrap();
            let hash = edge.hash & !1u32;
            let expected = (0..index.child_count())
                .rfind(|&j| index.child(j).unwrap().hash <= hash)
                .unwrap();
            assert_eq!(index.probe(hash), expected);
            let query = format!("bmap /indexed {}", edge.block);
            let mapped = command(&debugfs, &["-R", &query, path], false);
            let physical = String::from_utf8(mapped)
                .unwrap()
                .trim()
                .parse::<usize>()
                .unwrap();
            logical_blocks[edge.block as usize] = &img[physical * 4096..(physical + 1) * 4096];
            assert!(core::directory::valid_tail(
                &img[physical * 4096..(physical + 1) * 4096],
                seed
            ));
        }
        let graph = core::htree_topology::parse(&logical_blocks, inodes, seed, false).unwrap();
        assert_eq!(graph.logical_block_count(), blocks);
        assert_eq!(graph.logical_role(0), Some(1));
        for logical in 1..blocks {
            assert_eq!(graph.logical_role(logical), Some(3));
        }
        let hash_seed = core::dir_hash::State {
            a: le32(&img, 1260),
            b: le32(&img, 1264),
            c: le32(&img, 1268),
            d: le32(&img, 1272),
        };
        let directory = core::htree_names::build(
            &logical_blocks,
            inodes,
            seed,
            hash_seed,
            le32(&img, 1376) & 2 != 0,
            false,
        )
        .unwrap();
        assert_eq!(directory.len(), 302);
        for n in 0..300 {
            let name = format!("{n:04}-{}", "x".repeat(210));
            let entry = directory.lookup(name.as_bytes()).unwrap();
            assert_eq!(entry.identity().2, 13 + n);
            assert_eq!(entry.name_bytes(), name.as_bytes());
        }
        assert!(directory.lookup(b"missing").is_none());
        let volume = core::allocation::parse(core::snapshot::Snapshot::from_bytes(&img)).unwrap();
        let node = core::allocated_inode::get(&volume, 12).unwrap();
        assert!(core::directory_htree::validate(&node));
        let catalog = core::directory_index::build(&volume).unwrap();
        let namespace = core::namespace::validate(&catalog).unwrap();
        assert_eq!(namespace.parent(12), Some(2));
        assert_eq!(namespace.lookup(12, b".").unwrap().identity().1, 12);
        assert!(
            core::image_validation::inspect(core::snapshot::Snapshot::from_bytes(&img)).is_some()
        );
        // Move whole leaves across valid hash ranges. All records, counters,
        // inode checksums and HTree reachability are still individually valid.
        let mut wrong = img.clone();
        let mut swapped = raw.to_vec();
        let left = le32(&swapped, 36);
        let right = le32(&swapped, 44);
        swapped[36..40].copy_from_slice(&right.to_le_bytes());
        swapped[44..48].copy_from_slice(&left.to_le_bytes());
        seal(&mut swapped, 32, seed);
        wrong[physical * 4096..(physical + 1) * 4096].copy_from_slice(&swapped);
        assert!(core::allocation::parse(core::snapshot::Snapshot::from_bytes(&wrong)).is_some());
        assert!(
            core::image_validation::inspect(core::snapshot::Snapshot::from_bytes(&wrong)).is_none()
        );
        let mut wrong_seed = img.clone();
        wrong_seed[1260] ^= 1;
        let checksum = core::crc::crc32c(0xffffffff, &wrong_seed[1024..2044]);
        wrong_seed[2044..2048].copy_from_slice(&checksum.to_le_bytes());
        assert!(
            core::image_validation::inspect(core::snapshot::Snapshot::from_bytes(&wrong_seed))
                .is_none()
        );
        let mut no_feature = img.clone();
        let compat = le32(&no_feature, 1116) & !0x20;
        no_feature[1116..1120].copy_from_slice(&compat.to_le_bytes());
        let checksum = core::crc::crc32c(0xffffffff, &no_feature[1024..2044]);
        no_feature[2044..2048].copy_from_slice(&checksum.to_le_bytes());
        assert!(
            core::allocation::parse(core::snapshot::Snapshot::from_bytes(&no_feature)).is_none(),
            "INDEX inode requires source DIR_INDEX feature"
        );
        let deep = deepen_indexed_image(&img, table, physical, 12, blocks, seed);
        let deep_path = "build/htree-linux-deep.img";
        std::fs::write(deep_path, &deep).unwrap();
        command(&fsck, &["-fn", deep_path], false);
        let deep_volume =
            core::allocation::parse(core::snapshot::Snapshot::from_bytes(&deep)).unwrap();
        let deep_node = core::allocated_inode::get(&deep_volume, 12).unwrap();
        assert!(core::directory_htree::validate(&deep_node));
        let deep_catalog = core::directory_index::build(&deep_volume).unwrap();
        let deep_namespace = core::namespace::validate(&deep_catalog).unwrap();
        let mut deep_source = Vec::new();
        for logical in 0..blocks + 2 {
            match core::file_read::chunk(&deep_node, logical as u64 * 4096, 4096) {
                core::file_read::Chunk::Data(raw) => deep_source.push(raw),
                _ => panic!("every deep directory block must be initialized"),
            }
        }
        for n in 0..300 {
            let name = format!("{n:04}-{}", "x".repeat(210));
            assert_eq!(
                linux_frame_walk(
                    &deep_source,
                    inodes,
                    seed,
                    hash_seed,
                    le32(&deep, 1376) & 2 != 0,
                    name.as_bytes()
                )
                .0,
                Some(13 + n)
            );
            assert_eq!(
                deep_namespace
                    .lookup(12, name.as_bytes())
                    .unwrap()
                    .identity()
                    .1,
                13 + n
            );
        }
        assert_eq!(deep_namespace.parent(12), Some(2));
        assert!(
            core::image_validation::inspect(core::snapshot::Snapshot::from_bytes(&deep)).is_some()
        );
        exercise_timed_tree_write(&deep, 13, 0);
        let mut missing_large = deep.clone();
        let incompat = le32(&missing_large, 1120) & !0x4000;
        missing_large[1120..1124].copy_from_slice(&incompat.to_le_bytes());
        seal_single_group_allocation(&mut missing_large);
        assert!(
            core::allocation::parse(core::snapshot::Snapshot::from_bytes(&missing_large)).is_some()
        );
        assert!(
            core::image_validation::inspect(core::snapshot::Snapshot::from_bytes(&missing_large))
                .is_none(),
            "depth two requires the actual source LARGEDIR bit"
        );
        let mut too_deep = deep.clone();
        let raw = &mut too_deep[physical * 4096..(physical + 1) * 4096];
        raw[30] = 3;
        seal(raw, 32, seed);
        assert!(
            core::image_validation::inspect(core::snapshot::Snapshot::from_bytes(&too_deep))
                .is_none()
        );
        for file in [
            path,
            "build/htree-empty.bin",
            "build/htree-payload.bin",
            "build/htree-debugfs.txt",
            deep_path,
        ] {
            let _ = std::fs::remove_file(file);
        }
    }

    pub(super) fn deepen_indexed_image(
        img: &[u8],
        table: u32,
        root_physical: usize,
        inode_number: u32,
        old_blocks: u32,
        seed: u32,
    ) -> Vec<u8> {
        let mut deep = img.to_vec();
        let total = le32(img, 1028);
        let bitmap = le32(img, 4096) as usize * 4096;
        let free: Vec<u32> = (1..total)
            .rev()
            .filter(|&b| img[bitmap + b as usize / 8] & (1 << (b % 8)) == 0)
            .take(2)
            .collect();
        assert_eq!(free.len(), 2);
        let root = &img[root_physical * 4096..(root_physical + 1) * 4096];
        let count = core::bytes::read_le16(root, 34).unwrap();
        let mut lower = block(4096, false, true);
        lower[8..].fill(0);
        lower[8..10].copy_from_slice(&510u16.to_le_bytes());
        lower[10..12].copy_from_slice(&count.to_le_bytes());
        lower[12..16].copy_from_slice(&root[36..40]);
        lower[16..8 + count as usize * 8].copy_from_slice(&root[40..32 + count as usize * 8]);
        seal(&mut lower, 8, seed);
        let mut upper = block(4096, false, true);
        upper[8..].fill(0);
        upper[8..10].copy_from_slice(&510u16.to_le_bytes());
        upper[10..12].copy_from_slice(&1u16.to_le_bytes());
        upper[12..16].copy_from_slice(&(old_blocks + 1).to_le_bytes());
        seal(&mut upper, 8, seed);
        let mut new_root = root.to_vec();
        new_root[30] = 2;
        new_root[34..36].copy_from_slice(&1u16.to_le_bytes());
        new_root[36..40].copy_from_slice(&old_blocks.to_le_bytes());
        seal(&mut new_root, 32, seed);
        deep[root_physical * 4096..(root_physical + 1) * 4096].copy_from_slice(&new_root);
        for (physical, raw) in [(free[0], &upper), (free[1], &lower)] {
            deep[physical as usize * 4096..(physical as usize + 1) * 4096].copy_from_slice(raw);
            deep[bitmap + physical as usize / 8] |= 1 << (physical % 8);
        }
        let at = table as usize * 4096 + (inode_number as usize - 1) * 256;
        let extents = core::bytes::read_le16(img, at + 42).unwrap() as usize;
        assert_eq!(core::bytes::read_le16(img, at + 46).unwrap(), 0);
        assert!(
            extents <= 2,
            "two free inode extent entries for additional logical index blocks"
        );
        for (i, physical) in free.iter().enumerate() {
            let e = at + 52 + (extents + i) * 12;
            deep[e..e + 4].copy_from_slice(&(old_blocks + i as u32).to_le_bytes());
            deep[e + 4..e + 6].copy_from_slice(&1u16.to_le_bytes());
            deep[e + 6..e + 8].fill(0);
            deep[e + 8..e + 12].copy_from_slice(&physical.to_le_bytes());
        }
        deep[at + 42..at + 44].copy_from_slice(&((extents + 2) as u16).to_le_bytes());
        deep[at + 4..at + 8].copy_from_slice(&((old_blocks + 2) * 4096).to_le_bytes());
        deep[at + 28..at + 32].copy_from_slice(&(le32(img, at + 28) + 16).to_le_bytes());
        let uuid_seed = core::superblock::metadata_checksum_seed(&img[1024..2048]).unwrap();
        seal_inode_image(&mut deep, table, inode_number, uuid_seed);
        let flags = le32(&deep, 1120) | 0x4000;
        deep[1120..1124].copy_from_slice(&flags.to_le_bytes());
        seal_single_group_allocation(&mut deep);
        deep
    }

    fn empty_leaf(seed: u32) -> Vec<u8> {
        let mut raw = vec![0u8; 4096];
        raw[4..6].copy_from_slice(&4084u16.to_le_bytes());
        raw[4088..4090].copy_from_slice(&12u16.to_le_bytes());
        raw[4091] = 0xde;
        let checksum = core::crc::crc32c(seed, &raw[..4084]);
        raw[4092..4096].copy_from_slice(&checksum.to_le_bytes());
        raw
    }

    #[test]
    fn complete_htree_graph_rejects_orphans_reuse_cycles_and_unchecked_leaves() {
        use core::htree_topology;
        let seed = 0x12345678;
        let mut root = block(4096, true, true);
        root[30] = 2;
        root[34..36].copy_from_slice(&1u16.to_le_bytes());
        root[36..40].copy_from_slice(&1u32.to_le_bytes());
        seal(&mut root, 32, seed);
        let mut node = block(4096, false, true);
        node[10..12].copy_from_slice(&1u16.to_le_bytes());
        node[12..16].copy_from_slice(&2u32.to_le_bytes());
        seal(&mut node, 8, seed);
        let mut nested = node.clone();
        nested[12..16].copy_from_slice(&3u32.to_le_bytes());
        seal(&mut nested, 8, seed);
        let leaf = empty_leaf(seed);
        let source = [&root[..], &node, &nested, &leaf];
        let graph = htree_topology::parse(&source, 4096, seed, true).unwrap();
        assert_eq!(graph.logical_block_count(), 4);
        assert_eq!(graph.logical_role(0), Some(1));
        assert_eq!(graph.logical_role(1), Some(1));
        assert_eq!(graph.logical_role(2), Some(1));
        assert_eq!(graph.logical_role(3), Some(3));
        assert_eq!(graph.logical_role(4), None);
        assert!(htree_topology::parse(&source, 4096, seed, false).is_none());
        let orphan = [&root[..], &node, &nested, &leaf, &leaf];
        assert!(htree_topology::parse(&orphan, 4096, seed, true).is_none());
        let mut cycle = node.clone();
        cycle[12..16].copy_from_slice(&1u32.to_le_bytes());
        seal(&mut cycle, 8, seed);
        assert!(
            htree_topology::parse(&[&root, &cycle, &nested, &leaf], 4096, seed, true).is_none()
        );
        let mut invalid = leaf.clone();
        invalid[4092] ^= 1;
        assert!(
            htree_topology::parse(&[&root, &node, &nested, &invalid], 4096, seed, true).is_none()
        );
        let mut duplicate = block(4096, true, true);
        duplicate[34..36].copy_from_slice(&2u16.to_le_bytes());
        duplicate[36..40].copy_from_slice(&1u32.to_le_bytes());
        duplicate[44..48].copy_from_slice(&1u32.to_le_bytes());
        seal(&mut duplicate, 32, seed);
        assert!(htree_topology::parse(&[&duplicate, &leaf], 4096, seed, false).is_none());
        duplicate[44..48].copy_from_slice(&2u32.to_le_bytes());
        seal(&mut duplicate, 32, seed);
        assert!(
            htree_topology::parse(&[&duplicate, &leaf, &leaf], 4096, seed, false).is_some(),
            "equal bytes in distinct logical slots need no checksum injectivity assumption"
        );
        duplicate[34..36].copy_from_slice(&1u16.to_le_bytes());
        seal(&mut duplicate, 32, seed);
        let minimal = htree_topology::parse(&[&duplicate, &leaf], 4096, seed, false).unwrap();
        assert_eq!(minimal.logical_block_count(), 2);
        assert_eq!(minimal.logical_role(0), Some(1));
        assert_eq!(minimal.logical_role(1), Some(3));
        assert_eq!(
            minimal.logical_role(2),
            None,
            "private ledger padding is not a directory block"
        );
    }
    #[test]
    fn inherited_hash_intervals_cover_probe_and_every_collision_continuation() {
        use core::htree_range;
        let raw = block(4096, true, true);
        let root = htree::parse_root(&raw, 100, 4096, 0x12345678, true, false).unwrap();
        let index = root.routing_index();
        let full = htree_range::full();
        for hash in [0, 98, 100, 102, 198, 200, u32::MAX - 1] {
            let start = index.probe(hash);
            for child in 0..index.child_count() {
                let bounds = htree_range::subdivide(index, &full, child).unwrap();
                if htree_range::includes(&bounds, hash) {
                    assert!(start <= child);
                    for next in start + 1..=child {
                        assert!(index.continues(hash, next));
                    }
                }
            }
        }
        for child in [1, 2, 3] {
            assert!(htree_range::includes(
                &htree_range::subdivide(index, &full, child).unwrap(),
                100
            ));
        }
        let parent = htree_range::Bounds {
            lower: 150,
            upper: 175,
            inclusive: false,
        };
        assert!(htree_range::subdivide(index, &parent, 2).is_none());
        assert!(htree_range::subdivide(index, &full, usize::MAX).is_none());
        let invalid = htree_range::Bounds {
            lower: 100,
            upper: 50,
            inclusive: false,
        };
        assert!(htree_range::subdivide(index, &invalid, 0).is_none());
    }

    fn named_leaf(seed: u32, target: u32, name: &[u8]) -> Vec<u8> {
        let mut leaf = empty_leaf(seed);
        leaf[..4].copy_from_slice(&target.to_le_bytes());
        leaf[6] = name.len() as u8;
        leaf[7] = 1;
        leaf[8..8 + name.len()].copy_from_slice(name);
        let checksum = core::crc::crc32c(seed, &leaf[..4084]);
        leaf[4092..].copy_from_slice(&checksum.to_le_bytes());
        leaf
    }

    #[test]
    fn complete_name_lookup_keeps_real_hash_collisions_distinct_and_rejects_wrong_ranges() {
        use core::{
            dir_hash::{self, State},
            htree_names,
        };
        let seed = 0x12345678;
        let hash_seed = State {
            a: 0,
            b: 0,
            c: 0,
            d: 0,
        };
        let left_name = b"collision-012141";
        let right_name = b"collision-012441";
        let left_hash = dir_hash::calculate(left_name, hash_seed, 0).unwrap().major;
        assert_eq!(left_hash, 0x80bd17e8);
        assert_eq!(
            left_hash,
            dir_hash::calculate(right_name, hash_seed, 0).unwrap().major
        );
        let mut root = block(4096, true, true);
        root[28] = 0;
        root[34..36].copy_from_slice(&2u16.to_le_bytes());
        root[40..44].copy_from_slice(&(left_hash | 1).to_le_bytes());
        root[44..48].copy_from_slice(&2u32.to_le_bytes());
        seal(&mut root, 32, seed);
        let left = named_leaf(seed, 13, left_name);
        let right = named_leaf(seed, 14, right_name);
        let directory =
            htree_names::build(&[&root, &left, &right], 4096, seed, hash_seed, false, false)
                .unwrap();
        assert_eq!(directory.len(), 4);
        assert_eq!(directory.lookup(b".").unwrap().identity(), (0, 0, 12, 2));
        assert_eq!(directory.lookup(b"..").unwrap().identity(), (0, 1, 2, 2));
        assert_eq!(
            directory.lookup(left_name).unwrap().identity(),
            (1, 0, 13, 1)
        );
        assert_eq!(
            directory.lookup(right_name).unwrap().identity(),
            (2, 0, 14, 1)
        );
        assert!(directory.lookup(b"collision-01214").is_none());
        assert!(directory.lookup(b"collision-012141\0").is_none());
        assert!(directory.get(directory.len()).is_none());
        let duplicate = named_leaf(seed, 14, left_name);
        assert!(
            htree_names::build(
                &[&root, &left, &duplicate],
                4096,
                seed,
                hash_seed,
                false,
                false
            )
            .is_none()
        );
        root[40..44].copy_from_slice(&left_hash.to_le_bytes());
        seal(&mut root, 32, seed);
        assert!(core::htree_topology::parse(&[&root, &left, &right], 4096, seed, false).is_some());
        assert!(
            htree_names::build(&[&root, &left, &right], 4096, seed, hash_seed, false, false)
                .is_none(),
            "an even split excludes the equal hash from the preceding leaf"
        );
    }

    #[test]
    fn deep_htree_names_and_canonical_root_internal_leaf_projections_agree() {
        use core::{dir_hash::State, directory_piece, htree_names};
        let seed = 0x12345678;
        let mut root = block(4096, true, true);
        root[30] = 2;
        root[34..36].copy_from_slice(&1u16.to_le_bytes());
        root[36..40].copy_from_slice(&1u32.to_le_bytes());
        seal(&mut root, 32, seed);
        let mut node = block(4096, false, true);
        node[10..12].copy_from_slice(&1u16.to_le_bytes());
        node[12..16].copy_from_slice(&2u32.to_le_bytes());
        seal(&mut node, 8, seed);
        let mut nested = node.clone();
        nested[12..16].copy_from_slice(&3u32.to_le_bytes());
        seal(&mut nested, 8, seed);
        let leaf = named_leaf(seed, 13, b"deep-name");
        let directory = htree_names::build(
            &[&root, &node, &nested, &leaf],
            4096,
            seed,
            State {
                a: 1,
                b: 2,
                c: 3,
                d: 4,
            },
            false,
            true,
        )
        .unwrap();
        assert_eq!(
            directory.lookup(b"deep-name").unwrap().identity(),
            (3, 0, 13, 1)
        );
        assert!(directory.lookup(b"absent").is_none());
        for (logical, raw, names) in [(0, &root, 2), (1, &node, 0), (2, &nested, 0), (3, &leaf, 1)]
        {
            let piece = directory_piece::parse(raw, 4096, seed, true, logical, 4, true).unwrap();
            assert_eq!(piece.len(), names);
            assert!(piece.get(names).is_none());
        }
        assert!(directory_piece::parse(&root, 4096, seed, false, 0, 4, true).is_none());
        assert!(directory_piece::parse(&node, 4096, seed, false, 1, 4, true).is_none());
        root[28] = 6;
        seal(&mut root, 32, seed);
        assert!(
            htree_names::build(
                &[&root, &node, &nested, &leaf],
                4096,
                seed,
                State {
                    a: 1,
                    b: 2,
                    c: 3,
                    d: 4
                },
                false,
                true
            )
            .is_none(),
            "keyed hashing needs fscrypt authority"
        );
    }
    // Independent control-flow reference: initial descent probes each frame;
    // continued descent enters every newly read frame at entry zero.
    fn linux_frame_walk(
        blocks: &[&[u8]],
        inodes: u32,
        seed: u32,
        hash_seed: core::dir_hash::State,
        unsigned: bool,
        name: &[u8],
    ) -> (Option<u32>, Vec<u32>) {
        let root = blocks[0];
        let levels = root[30] as usize + 1;
        let hash =
            core::dir_hash::calculate(name, hash_seed, root[28] + if unsigned { 3 } else { 0 })
                .unwrap()
                .major;
        let count = |n: u32| {
            core::bytes::read_le16(blocks[n as usize], if n == 0 { 34 } else { 10 }).unwrap()
                as usize
        };
        let word = |n: u32, i: usize, child: bool| {
            le32(
                blocks[n as usize],
                if n == 0 { 32 } else { 8 } + i * 8 + if child { 4 } else { 0 },
            )
        };
        let mut frames: Vec<(u32, usize)> = Vec::new();
        let mut number = 0u32;
        while frames.len() < levels {
            let at = (1..count(number))
                .rfind(|&i| word(number, i, false) <= hash)
                .unwrap_or(0);
            frames.push((number, at));
            number = word(number, at, true) & 0x0fffffff;
        }
        let mut visited = Vec::new();
        loop {
            visited.push(number);
            let leaf = core::directory_block::parse(blocks[number as usize], inodes, seed).unwrap();
            for i in 0..leaf.len() {
                if leaf.get(i).unwrap().inode != 0 && leaf.name(i).unwrap() == name {
                    return (Some(leaf.get(i).unwrap().inode), visited);
                }
            }
            loop {
                let (parent, at) = match frames.pop() {
                    Some(frame) => frame,
                    None => {
                        return (None, visited);
                    }
                };
                if at + 1 == count(parent) {
                    continue;
                }
                if word(parent, at + 1, false) & !1 != hash {
                    return (None, visited);
                }
                frames.push((parent, at + 1));
                number = word(parent, at + 1, true) & 0x0fffffff;
                break;
            }
            while frames.len() < levels {
                frames.push((number, 0));
                number = word(number, 0, true) & 0x0fffffff;
            }
        }
    }

    #[test]
    fn collisions_across_subtrees_follow_linux_first_entry_continuation_descent() {
        let seed = 0x12345678;
        let hash_seed = core::dir_hash::State {
            a: 0,
            b: 0,
            c: 0,
            d: 0,
        };
        let hash = 0x80bd17e8u32;
        let mut root = block(4096, true, true);
        root[28] = 0;
        root[30] = 1;
        root[34..36].copy_from_slice(&2u16.to_le_bytes());
        root[40..44].copy_from_slice(&(hash | 1).to_le_bytes());
        root[44..48].copy_from_slice(&2u32.to_le_bytes());
        seal(&mut root, 32, seed);
        let mut first_node = block(4096, false, true);
        first_node[10..12].copy_from_slice(&1u16.to_le_bytes());
        first_node[12..16].copy_from_slice(&3u32.to_le_bytes());
        seal(&mut first_node, 8, seed);
        let mut continued_node = block(4096, false, true);
        continued_node[10..12].copy_from_slice(&2u16.to_le_bytes());
        continued_node[12..16].copy_from_slice(&4u32.to_le_bytes());
        continued_node[16..20].copy_from_slice(&hash.to_le_bytes());
        continued_node[20..24].copy_from_slice(&5u32.to_le_bytes());
        seal(&mut continued_node, 8, seed);
        let left = named_leaf(seed, 13, b"collision-012141");
        let middle = empty_leaf(seed);
        let right = named_leaf(seed, 14, b"collision-012441");
        let source: [&[u8]; 6] = [&root, &first_node, &continued_node, &left, &middle, &right];
        let directory =
            core::htree_names::build(&source, 4096, seed, hash_seed, false, false).unwrap();
        assert_eq!(
            directory.lookup(b"collision-012141").unwrap().identity().2,
            13
        );
        assert_eq!(
            directory.lookup(b"collision-012441").unwrap().identity().2,
            14
        );
        assert_eq!(
            linux_frame_walk(&source, 4096, seed, hash_seed, false, b"collision-012141"),
            (Some(13), vec![3])
        );
        assert_eq!(
            linux_frame_walk(&source, 4096, seed, hash_seed, false, b"collision-012441"),
            (Some(14), vec![3, 4, 5])
        );
        assert!(directory.lookup(b"collision-012441-").is_none());
        assert_eq!(
            linux_frame_walk(&source, 4096, seed, hash_seed, false, b"collision-012441-").0,
            None
        );
    }
}

mod directory_hashes {
    use core::dir_hash::{self, State};

    use super::*;

    #[test]
    fn unkeyed_hashes_are_total_bounded_and_reserve_collision_and_eof_bits() {
        let zero = State {
            a: 0,
            b: 0,
            c: 0,
            d: 0,
        };
        let custom = State {
            a: 1,
            b: 2,
            c: 3,
            d: 4,
        };
        for version in 0..=5 {
            for length in [0, 1, 3, 4, 15, 16, 17, 31, 32, 33, 254, 255] {
                let name: Vec<u8> = (0..length).map(|i| (i * 37) as u8).collect();
                for seed in [zero, custom] {
                    let hash = dir_hash::calculate(&name, seed, version).unwrap();
                    assert_eq!(hash.major & 1, 0);
                    assert!(hash.major < 0xfffffffe);
                }
            }
            assert!(dir_hash::calculate(&vec![b'x'; 256], zero, version).is_none());
        }
        for version in 6..=255 {
            assert!(dir_hash::calculate(b"test", zero, version).is_none());
        }
        let test = dir_hash::calculate(b"test", zero, 0).unwrap();
        assert_eq!((test.major, test.minor), (0x802cf52c, 0));
        for name in [
            b"test".as_slice(),
            b"a-byte-string-with-no-high-bits".as_slice(),
        ] {
            for version in 0..3 {
                let a = dir_hash::calculate(name, custom, version).unwrap();
                let b = dir_hash::calculate(name, custom, version + 3).unwrap();
                assert_eq!((a.major, a.minor), (b.major, b.minor));
            }
        }
    }

    #[test]
    fn all_six_directory_hashes_match_linux_tools_across_seeds_signed_bytes_and_round_boundaries() {
        let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
        let path = "build/hash-debugfs.txt";
        let mut script = String::new();
        let mut expected = Vec::new();
        let names = [
            "test".to_string(),
            "café".to_string(),
            "x".repeat(15),
            "x".repeat(16),
            "x".repeat(17),
            "x".repeat(31),
            "x".repeat(32),
            "x".repeat(33),
            "x".repeat(255),
            format!("{}z", "é".repeat(127)),
        ];
        for (uuid, seed) in [
            (
                "00000000-0000-0000-0000-000000000000",
                State {
                    a: 0,
                    b: 0,
                    c: 0,
                    d: 0,
                },
            ),
            (
                "00112233-4455-6677-8899-aabbccddeeff",
                State {
                    a: 0x33221100,
                    b: 0x77665544,
                    c: 0xbbaa9988,
                    d: 0xffeeddcc,
                },
            ),
        ] {
            for version in 0..6 {
                for name in &names {
                    script += &format!("dx_hash -h {version} -s {uuid} {name}\n");
                    let hash = dir_hash::calculate(name.as_bytes(), seed, version).unwrap();
                    expected.push((version, name, hash));
                }
            }
        }
        std::fs::write(path, script).unwrap();
        let output = std::process::Command::new(debugfs)
            .args(["-f", path, "build/linux.img"])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let text = String::from_utf8(output.stdout).unwrap();
        let actual: Vec<_> = text
            .lines()
            .filter(|line| line.starts_with("Hash of "))
            .collect();
        assert_eq!(actual.len(), expected.len(), "{text}");
        for ((version, name, hash), line) in expected.into_iter().zip(actual) {
            let words: Vec<u32> = line
                .split_whitespace()
                .filter_map(|word| word.strip_prefix("0x"))
                .map(|word| u32::from_str_radix(word.trim_end_matches(')'), 16).unwrap())
                .collect();
            assert_eq!(
                words,
                [hash.major, hash.minor],
                "version {version}, name length {}: {line}",
                name.len()
            );
        }
        let _ = std::fs::remove_file(path);
    }
}

mod inline_xattr_updates {
    use core::{
        access::Credentials, acl_access, allocated_inode, allocation, recovery_request::Completion,
        snapshot::Snapshot, xattr, xattr_inode, xattr_table::ValueRef, xattr_update,
    };

    use super::*;

    pub(super) fn command(binary: &str, args: &[&str], modified: bool) -> Vec<u8> {
        let output = std::process::Command::new(binary)
            .args(args)
            .output()
            .unwrap();
        assert!(
            output.status.success() || modified && output.status.code() == Some(1),
            "{args:?}: {} {}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        output.stdout
    }
    pub(super) fn fixture(prefix: &str, external: bool) -> Vec<u8> {
        let path = format!("build/{prefix}.img");
        let acl_path = format!("build/{prefix}-acl.bin");
        let large_path = format!("build/{prefix}-large.bin");
        std::fs::write(&path, image()).unwrap();
        let mut acl = 2u32.to_le_bytes().to_vec();
        for (tag, bits, id) in [
            (1u16, 6u16, u32::MAX),
            (2, 2, 1234),
            (4, 0, u32::MAX),
            (16, 2, u32::MAX),
            (32, 0, u32::MAX),
        ] {
            acl.extend(tag.to_le_bytes());
            acl.extend(bits.to_le_bytes());
            acl.extend(id.to_le_bytes());
        }
        std::fs::write(&acl_path, acl).unwrap();
        let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
        command(&debugfs, &["-w", "-R", "feature ext_attr", &path], false);
        command(
            &debugfs,
            &["-w", "-R", "ea_set /payload user.note before7", &path],
            false,
        );
        command(
            &debugfs,
            &[
                "-w",
                "-R",
                &format!("ea_set -f {acl_path} /payload system.posix_acl_access"),
                &path,
            ],
            false,
        );
        command(
            &debugfs,
            &["-w", "-R", "sif /payload mode 0100620", &path],
            false,
        );
        if external {
            std::fs::write(&large_path, [0x59; 512]).unwrap();
            command(
                &debugfs,
                &[
                    "-w",
                    "-R",
                    &format!("ea_set -f {large_path} /payload user.large"),
                    &path,
                ],
                false,
            );
        }
        let fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        command(&fsck, &["-fn", &path], false);
        let bytes = std::fs::read(&path).unwrap();
        for file in [&path, &acl_path, &large_path] {
            let _ = std::fs::remove_file(file);
        }
        bytes
    }
    pub(super) fn named() -> Credentials {
        Credentials {
            fsuid: 1234,
            in_inode_group: false,
            dac_override: false,
            dac_read_search: false,
        }
    }
    pub(super) fn attribute(img: &[u8], namespace: u8, name: &[u8]) -> Vec<u8> {
        let volume = allocation::parse(Snapshot::from_bytes(img)).unwrap();
        let attrs = xattr_inode::inspect(volume.index(), 12).unwrap();
        match attrs.get(namespace, name).unwrap() {
            ValueRef::Bytes(value) => value.to_vec(),
            _ => panic!("local byte value"),
        }
    }
    pub(super) fn recover(mut img: Vec<u8>) -> Vec<u8> {
        let source_bytes = img.clone();
        let source = Snapshot::from_bytes(&source_bytes);
        let mut recovery = core::recovery_admission::prepare(&source).unwrap();
        loop {
            let pending = match recovery.dispatch() {
                Ok(pending) => pending,
                Err(done) => {
                    assert!(done.finished());
                    break;
                }
            };
            if let core::recovery_io::Command::Write { block, image } = pending.pending_command() {
                img[block as usize * 4096..(block as usize + 1) * 4096].copy_from_slice(image);
            }
            recovery = pending.finish_pending(Completion::Succeeded);
        }
        assert!(core::image_validation::inspect(Snapshot::from_bytes(&img)).is_some());
        img
    }

    #[test]
    fn acl_authorized_inline_xattr_update_journals_one_inode_and_recovers_the_committed_value() {
        let img = fixture("xattr-update-authorized", true);
        let (_, group, _) = metadata(&img);
        let original_inode = inode_bytes(&img, group.inode_table, 12).to_vec();
        let body = xattr::parse_body(&original_inode, false, le32(&img, 1024)).unwrap();
        assert!(body.entry_table().unwrap().find(1, b"note").is_some());
        let acl = attribute(&img, 2, b"");
        let external = core::xattr::inode_pointer(&original_inode).unwrap() as usize;
        assert!(external > 0);
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        let user = named();
        assert_eq!(
            node.info().mode & 7,
            0,
            "the named ACL supplies this user's permission"
        );
        let grant = acl_access::authorize(&node, &user, &[], 2).unwrap();
        let candidate =
            xattr_update::prepare(grant, b"note", b"after77", 123456789, 987654321).unwrap();
        let metadata_block = candidate.after_image().block();
        let expected_block = candidate.after_image().as_slice().to_vec();
        let mut writer = candidate.begin().unwrap();
        let mut stable = img.clone();
        let mut committed = false;
        let mut committed_cut = None;
        let mut precommit_cut = None;
        let mut journal_writes = 0;
        loop {
            let pending = match writer.dispatch() {
                Ok(pending) => pending,
                Err(done) => {
                    writer = done;
                    break;
                }
            };
            match pending.pending_command() {
                core::recovery_io::Command::Write { block, image } => {
                    if core::bytes::read_be32(image, 0) == Some(0xc03b3998) {
                        journal_writes += 1;
                        if core::bytes::read_be32(image, 4) == Some(2) {
                            committed = true;
                        }
                    }
                    stable[block as usize * 4096..(block as usize + 1) * 4096]
                        .copy_from_slice(image);
                }
                core::recovery_io::Command::Flush => {
                    if committed && committed_cut.is_none() {
                        committed_cut = Some(stable.clone());
                    } else if !committed && journal_writes > 0 {
                        precommit_cut = Some(stable.clone());
                    }
                }
            }
            writer = pending.finish_pending(Completion::Succeeded);
        }
        assert!(writer.finished());
        assert_eq!(
            &stable[metadata_block as usize * 4096..(metadata_block as usize + 1) * 4096],
            expected_block
        );
        assert_eq!(attribute(&stable, 1, b"note"), b"after77");
        assert_eq!(attribute(&stable, 2, b""), acl);
        assert_eq!(
            &stable[external * 4096..(external + 1) * 4096],
            &img[external * 4096..(external + 1) * 4096]
        );
        for block in 0..volume.index().parameters().0 {
            if (4..=7).contains(&volume.census().role_of(block).unwrap().kind) {
                assert_eq!(
                    &stable[block as usize * 4096..(block as usize + 1) * 4096],
                    &img[block as usize * 4096..(block as usize + 1) * 4096]
                );
            }
        }
        let after_inode = inode_bytes(&stable, group.inode_table, 12);
        assert_eq!(
            &after_inode[16..20],
            &original_inode[16..20],
            "mtime is unchanged"
        );
        assert_eq!(&after_inode[136..140], &original_inode[136..140]);
        assert_eq!(
            core::inode_time_fields::get_time(after_inode, core::inode_time_fields::Field::Ctime)
                .unwrap()
                .seconds,
            123456789
        );
        let old_version =
            le32(&original_inode, 36) as u64 + ((le32(&original_inode, 152) as u64) << 32);
        let new_version = le32(after_inode, 36) as u64 + ((le32(after_inode, 152) as u64) << 32);
        assert_eq!(new_version, old_version + 1);
        let before_commit = recover(precommit_cut.unwrap());
        assert_eq!(attribute(&before_commit, 1, b"note"), b"before7");
        let cut = committed_cut.unwrap();
        assert_eq!(
            attribute(&cut, 1, b"note"),
            b"before7",
            "home inode has not been checkpointed"
        );
        let recovered = recover(cut.clone());
        assert_eq!(attribute(&recovered, 1, b"note"), b"after77");
        assert_eq!(attribute(&recovered, 2, b""), acl);
        let fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
        for (path, bytes) in [
            ("build/xattr-update-linux-final.img", stable),
            ("build/xattr-update-linux-crash.img", cut),
        ] {
            std::fs::write(path, bytes).unwrap();
            command(&fsck, &["-fy", path], true);
            command(&fsck, &["-fn", path], false);
            let linux = std::fs::read(path).unwrap();
            assert_eq!(attribute(&linux, 1, b"note"), b"after77");
            assert_eq!(attribute(&linux, 2, b""), acl);
            let output = command(&debugfs, &["-R", "ea_get /payload user.note", path], false);
            assert!(String::from_utf8_lossy(&output).contains("after77"));
            let _ = std::fs::remove_file(path);
        }
    }

    #[test]
    fn inline_xattr_updates_reject_aliased_acl_storage_wrong_grants_noops_and_version_reuse() {
        let img = fixture("xattr-update-rejection", false);
        let (_, group, seed) = metadata(&img);
        let inodes = le32(&img, 1024);
        let raw = inode_bytes(&img, group.inode_table, 12);
        let body = xattr::parse_body(raw, false, inodes).unwrap();
        let table = body.entry_table().unwrap();
        let slot = table.find(1, b"note").unwrap();
        let selected = table.metadata(slot).unwrap();
        let acl_entry = table.metadata(table.find(2, b"").unwrap()).unwrap();
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        let user = named();
        for (name, data) in [
            (b"note".as_slice(), b"before7".as_slice()),
            (b"note", b"x"),
            (b"missing", b"after77"),
            (b"system.posix_acl_access", b"after77"),
            (b"", b"after77"),
        ] {
            let grant = acl_access::authorize(&node, &user, &[], 2).unwrap();
            assert!(xattr_update::prepare(grant, name, data, 123, 456).is_none());
        }
        let read = acl_access::authorize(&node, &user, &[], 0).unwrap();
        assert!(xattr_update::prepare(read, b"note", b"after77", 123, 456).is_none());
        let denied = Credentials {
            fsuid: 5678,
            ..named()
        };
        assert!(acl_access::authorize(&node, &denied, &[], 2).is_none());
        let at = group.inode_table as usize * 4096 + 11 * 256;
        let mut aliased = img.clone();
        let offset = (acl_entry.value_offset - 164) as u16;
        aliased[at + selected.position + 2..at + selected.position + 4]
            .copy_from_slice(&offset.to_le_bytes());
        seal_inode_image(&mut aliased, group.inode_table, 12, seed);
        assert!(
            core::image_validation::inspect(Snapshot::from_bytes(&aliased)).is_some(),
            "immutable aliasing does not authorize mutation"
        );
        let alias_volume = allocation::parse(Snapshot::from_bytes(&aliased)).unwrap();
        let alias_node = allocated_inode::get(&alias_volume, 12).unwrap();
        let grant = acl_access::authorize(&alias_node, &user, &[], 2).unwrap();
        assert!(xattr_update::prepare(grant, b"note", b"after77", 123, 456).is_none());
        let mut version = raw.to_vec();
        version[36..40].copy_from_slice(&u32::MAX.to_le_bytes());
        version[152..156].copy_from_slice(&0u32.to_le_bytes());
        version[selected.value_offset + selected.value_size as usize] = 0x7f;
        let checksum = core::inode::calculated_checksum(&version, 12, seed).unwrap();
        version[124..126].copy_from_slice(&(checksum as u16).to_le_bytes());
        version[130..132].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
        let source = xattr::parse_body(&version, false, inodes).unwrap();
        let encoded = core::xattr_replace::encode(
            &source, slot, b"after77", 12, inodes, seed, false, 123, 456,
        )
        .unwrap();
        assert_eq!(le32(&encoded, 36), 0);
        assert_eq!(le32(&encoded, 152), 1);
        assert_eq!(
            encoded[selected.value_offset + selected.value_size as usize],
            0
        );
        assert_eq!(
            &encoded
                [acl_entry.value_offset..acl_entry.value_offset + acl_entry.value_size as usize],
            &raw[acl_entry.value_offset..acl_entry.value_offset + acl_entry.value_size as usize]
        );
        let mut last_version = version.clone();
        last_version[36..40].copy_from_slice(&(u32::MAX - 1).to_le_bytes());
        last_version[152..156].copy_from_slice(&0x7fffffffu32.to_le_bytes());
        let checksum = core::inode::calculated_checksum(&last_version, 12, seed).unwrap();
        last_version[124..126].copy_from_slice(&(checksum as u16).to_le_bytes());
        last_version[130..132].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
        let source = xattr::parse_body(&last_version, false, inodes).unwrap();
        let last = core::xattr_replace::encode(
            &source, slot, b"after77", 12, inodes, seed, false, 123, 456,
        )
        .unwrap();
        assert_eq!(le32(&last, 36), u32::MAX);
        assert_eq!(le32(&last, 152), 0x7fffffff);
        let terminal = xattr::parse_body(&last, false, inodes).unwrap();
        assert!(
            core::xattr_replace::encode(
                &terminal, slot, b"again77", 12, inodes, seed, false, 123, 456
            )
            .is_none()
        );
        for old_version in [core::xattr_replace::MAX_VERSION, 1u64 << 63, u64::MAX] {
            let mut maximum = img.clone();
            maximum[at + 36..at + 40].copy_from_slice(&(old_version as u32).to_le_bytes());
            maximum[at + 152..at + 156]
                .copy_from_slice(&((old_version >> 32) as u32).to_le_bytes());
            seal_inode_image(&mut maximum, group.inode_table, 12, seed);
            let max_volume = allocation::parse(Snapshot::from_bytes(&maximum)).unwrap();
            let max_node = allocated_inode::get(&max_volume, 12).unwrap();
            let grant = acl_access::authorize(&max_node, &user, &[], 2).unwrap();
            assert!(xattr_update::prepare(grant, b"note", b"after77", 123, 456).is_none());
        }
        let mut readonly = img.clone();
        let flags = le32(&readonly, 1124) | 0x1000;
        readonly[1124..1128].copy_from_slice(&flags.to_le_bytes());
        let checksum = core::crc::crc32c(0xffffffff, &readonly[1024..2044]);
        readonly[2044..2048].copy_from_slice(&checksum.to_le_bytes());
        let ro_volume = allocation::parse(Snapshot::from_bytes(&readonly)).unwrap();
        let ro_node = allocated_inode::get(&ro_volume, 12).unwrap();
        let grant = acl_access::authorize(&ro_node, &user, &[], 2).unwrap();
        assert!(xattr_update::prepare(grant, b"note", b"after77", 123, 456).is_none());
    }
}

mod xattr_lifecycle_updates {
    use core::{
        access::Credentials,
        acl_access, allocated_inode, allocation,
        recovery_request::Completion,
        snapshot::Snapshot,
        xattr, xattr_inode, xattr_lifecycle as update,
        xattr_store::{Error as StoreError, Store},
        xattr_table::ValueRef,
    };

    use super::{
        inline_xattr_updates::{attribute, command, fixture, named, recover},
        *,
    };

    fn ok<T>(value: Result<T, update::Error>) -> T {
        match value {
            Ok(value) => value,
            Err(_) => panic!("xattr lifecycle candidate rejected"),
        }
    }
    fn set(store: Store, namespace: u8, name: &[u8], value: &[u8], flags: u32) -> Store {
        match store.set(namespace, name, value, flags) {
            Ok(next) => next,
            Err(_) => panic!("owned xattr set rejected"),
        }
    }
    fn pointer(img: &[u8], number: u32) -> u32 {
        let (_, group, _) = metadata(img);
        xattr::inode_pointer(inode_bytes(img, group.inode_table, number)).unwrap() as u32
    }
    fn value(img: &[u8], number: u32, name: &[u8]) -> Option<Vec<u8>> {
        let volume = allocation::parse(Snapshot::from_bytes(img)).unwrap();
        let attrs = xattr_inode::inspect(volume.index(), number).unwrap();
        match attrs.get(1, name) {
            Some(ValueRef::Bytes(value)) => Some(value.to_vec()),
            None => None,
            _ => panic!("local values only"),
        }
    }
    fn owner() -> Credentials {
        Credentials {
            fsuid: 0,
            in_inode_group: true,
            dac_override: false,
            dac_read_search: false,
        }
    }
    fn drive(
        img: &[u8],
        candidate: update::Candidate<'_, '_, '_>,
        cuts: bool,
    ) -> (Vec<u8>, Vec<(bool, Vec<u8>)>) {
        let mut writer = candidate
            .begin()
            .expect("complete before/after writer admission");
        let mut stable = img.to_vec();
        let mut snapshots = Vec::new();
        let mut committed = false;
        loop {
            let pending = match writer.dispatch() {
                Ok(pending) => pending,
                Err(done) => {
                    assert!(done.finished());
                    break;
                }
            };
            if let core::recovery_io::Command::Write { block, image } = pending.pending_command() {
                if core::bytes::read_be32(image, 0) == Some(0xc03b3998)
                    && core::bytes::read_be32(image, 4) == Some(2)
                {
                    committed = true;
                }
                stable[block as usize * 4096..(block as usize + 1) * 4096].copy_from_slice(image);
                if cuts {
                    snapshots.push((committed, stable.clone()));
                }
            }
            writer = pending.finish_pending(Completion::Succeeded);
        }
        assert!(core::image_validation::inspect(Snapshot::from_bytes(&stable)).is_some());
        (stable, snapshots)
    }
    fn update(
        img: &[u8],
        name: &[u8],
        data: Option<&[u8]>,
        flags: u32,
        credentials: &Credentials,
        cuts: bool,
    ) -> (Vec<u8>, Vec<(bool, Vec<u8>)>) {
        let volume = allocation::parse(Snapshot::from_bytes(img)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        let groups: &[u32] = if credentials.in_inode_group {
            &[0]
        } else {
            &[]
        };
        let grant = acl_access::authorize(&node, credentials, groups, 2).unwrap();
        let candidate = match data {
            Some(data) => match ok(update::set_user(
                grant, name, data, flags, 123456789, 987654321,
            )) {
                Some(candidate) => candidate,
                None => {
                    return (img.to_vec(), Vec::new());
                }
            },
            None => ok(update::remove_user(grant, name, 123456789, 987654321)),
        };
        drive(img, candidate, cuts)
    }
    fn linux_check(prefix: &str, img: &[u8]) -> Vec<u8> {
        let path = format!("build/{prefix}.img");
        std::fs::write(&path, img).unwrap();
        let fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        command(&fsck, &["-fy", &path], true);
        command(&fsck, &["-fn", &path], false);
        let result = std::fs::read(&path).unwrap();
        let _ = std::fs::remove_file(path);
        result
    }
    pub(super) fn shared(prefix: &str) -> Vec<u8> {
        let mut img = fixture(prefix, true);
        let path = format!("build/{prefix}-shared.img");
        let data = format!("build/{prefix}-shared.bin");
        std::fs::write(&path, &img).unwrap();
        std::fs::write(&data, [0x59; 512]).unwrap();
        let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
        command(
            &debugfs,
            &["-w", "-R", "write build/fixture-file.bin /peer", &path],
            false,
        );
        command(
            &debugfs,
            &[
                "-w",
                "-R",
                &format!("ea_set -f {data} /peer user.large"),
                &path,
            ],
            false,
        );
        img = std::fs::read(&path).unwrap();
        let (_, group, seed) = metadata(&img);
        let first = pointer(&img, 12);
        let second = pointer(&img, 13);
        assert_ne!(first, second);
        let peer = group.inode_table as usize * 4096 + 12 * 256;
        img[peer + 104..peer + 108].copy_from_slice(&first.to_le_bytes());
        seal_inode_image(&mut img, group.inode_table, 13, seed);
        let start = first as usize * 4096;
        img[start + 4..start + 8].copy_from_slice(&2u32.to_le_bytes());
        let crc = xattr::checksum(&img[start..start + 4096], first as u64, seed).unwrap();
        img[start + 16..start + 20].copy_from_slice(&crc.to_le_bytes());
        img[group.block_bitmap as usize * 4096 + second as usize / 8] &= !(1 << (second % 8));
        seal_single_group_allocation(&mut img);
        assert!(core::image_validation::inspect(Snapshot::from_bytes(&img)).is_some());
        let _ = std::fs::remove_file(path);
        let _ = std::fs::remove_file(data);
        img
    }

    #[test]
    fn owned_xattrs_follow_linux_flag_precedence_and_preserve_errors_and_empty_values() {
        let original = set(Store::new(), 1, b"a", b"", 1);
        assert_eq!(original.item(0).unwrap().bytes(), b"");
        let original = match original.set(1, b"a", b"changed", 1) {
            Err((original, StoreError::Exists)) => original,
            _ => panic!("CREATE existing"),
        };
        let original = match original.set(1, b"absent", b"changed", 2) {
            Err((original, StoreError::Missing)) => original,
            _ => panic!("REPLACE absent"),
        };
        let original = match original.set(1, b"a", b"changed", 3) {
            Err((original, StoreError::Exists)) => original,
            _ => panic!("both flags existing"),
        };
        let original = match original.set(1, b"absent", b"changed", 3) {
            Err((original, StoreError::Missing)) => original,
            _ => panic!("both flags absent"),
        };
        let original = match original.set(1, b"a", b"changed", 4) {
            Err((original, StoreError::InvalidFlags)) => original,
            _ => panic!("unknown flags"),
        };
        assert_eq!(original.item(0).unwrap().bytes(), b"");
        let original = set(original, 2, b"", &[0, 1, 0, 2], 0);
        let original = set(original, 1, b"a", b"longer\0value", 2);
        let result = match original.remove(1, b"a") {
            Ok(result) => result,
            _ => panic!("remove existing"),
        };
        assert!(result.find(1, b"a").is_none());
        assert_eq!(
            result.item(result.find(2, b"").unwrap()).unwrap().bytes(),
            &[0, 1, 0, 2]
        );
        assert!(matches!(
            result.remove(1, b"a"),
            Err((_, StoreError::Missing))
        ));
        assert!(matches!(
            Store::new().set(0, b"a", b"", 0),
            Err((_, StoreError::InvalidKey))
        ));
        assert!(matches!(
            Store::new().set(1, b"a\0b", b"", 0),
            Err((_, StoreError::InvalidKey))
        ));
        assert!(matches!(
            Store::new().set(1, b"a", &[0; 65537], 0),
            Err((_, StoreError::ValueTooLarge))
        ));
    }
    #[test]
    fn xattr_hashes_use_unsigned_names_little_endian_zero_padding_and_sticky_zero_entries() {
        for name in [&b"a"[..], &b"\xff\x80name"[..], &b""[..]] {
            for value in [&b""[..], &b"1"[..], &b"12345"[..], &b"\0\xff\x80\0"[..]] {
                let mut hash = 0u32;
                for byte in name {
                    hash = hash.rotate_left(5) ^ u32::from(*byte);
                }
                for chunk in value.chunks(4) {
                    let mut word = [0; 4];
                    word[..chunk.len()].copy_from_slice(chunk);
                    hash = hash.rotate_left(16) ^ u32::from_le_bytes(word);
                }
                assert_eq!(core::xattr_hash::entry_hash(name, value), Some(hash));
            }
        }
        assert_eq!(core::xattr_hash::block_hash(&[1, 0, 2]), Some(0));
        assert_eq!(core::xattr_hash::block_hash(&[1, 65536, 2]), Some(2));
        let img = fixture("xattr-lifecycle-hashes", true);
        let (_, _, seed) = metadata(&img);
        let block = pointer(&img, 12) as usize;
        let external = xattr::parse_block(
            &img[block * 4096..(block + 1) * 4096],
            block as u64,
            seed,
            true,
            false,
            le32(&img, 1024),
        )
        .unwrap();
        for i in 0..external.entries().len() {
            let (_, name) = external.entries().name(i).unwrap();
            let ValueRef::Bytes(value) = external.entries().value(i).unwrap() else {
                panic!("local")
            };
            assert_eq!(
                core::xattr_hash::entry_hash(name, value),
                Some(external.entries().metadata(i).unwrap().hash)
            );
        }
    }
    #[test]
    fn packing_uses_both_storage_areas_at_the_exact_capacity_boundary() {
        let mut values = Store::new();
        for (name, len) in [(b"a", 40), (b"b", 24), (b"c", 24), (b"d", 3980)] {
            values = set(values, 1, name, &vec![name[0]; len], 0);
        }
        let mut inode = vec![0; 256];
        inode[128..130].copy_from_slice(&32u16.to_le_bytes());
        let packed = core::xattr_pack::encode(&values, &inode, 55, 0x12345678, 100).unwrap();
        let (body, external) = packed.into_parts();
        let body = xattr::parse_body(&body, false, 100).unwrap();
        assert_eq!(body.entry_table().unwrap().len(), 2);
        let bytes = external.unwrap();
        let external = xattr::parse_block(&bytes, 55, 0x12345678, true, false, 100).unwrap();
        assert_eq!(external.entries().len(), 2);
        assert!(body.entry_table().unwrap().find(1, b"b").is_some());
        assert!(body.entry_table().unwrap().find(1, b"c").is_some());
        let too_large = set(Store::new(), 1, b"d", &[1; 4080], 0);
        assert!(core::xattr_pack::encode(&too_large, &inode, 55, 0, 100).is_none());
    }
    #[test]
    fn create_resize_reuse_shrink_empty_and_remove_update_storage_and_sector_accounting() {
        let img = fixture("xattr-lifecycle-storage", false);
        let (_, group, _) = metadata(&img);
        let acl = attribute(&img, 2, b"");
        let free = le32(&img, 1036);
        let count =
            core::inode_blocks::decode(inode_bytes(&img, group.inode_table, 12), 4096, false)
                .unwrap();
        assert_eq!(pointer(&img, 12), 0);
        let (grown, _) = update(&img, b"note", Some(&[0x43; 512]), 2, &named(), false);
        let block = pointer(&grown, 12);
        assert!(block > 0);
        assert_eq!(le32(&grown, 1036), free - 1);
        assert_eq!(
            core::inode_blocks::decode(inode_bytes(&grown, group.inode_table, 12), 4096, false),
            Some(count + 8)
        );
        let (resized, _) = update(&grown, b"note", Some(&[0x44; 1000]), 2, &named(), false);
        assert_eq!(pointer(&resized, 12), block);
        assert_eq!(le32(&resized, 1036), free - 1);
        let (shrunk, _) = update(&resized, b"note", Some(b"x"), 2, &named(), false);
        assert_eq!(pointer(&shrunk, 12), 0);
        assert_eq!(le32(&shrunk, 1036), free);
        assert_eq!(
            core::inode_blocks::decode(inode_bytes(&shrunk, group.inode_table, 12), 4096, false),
            Some(count)
        );
        let (empty, _) = update(&shrunk, b"empty", Some(b""), 1, &named(), false);
        assert_eq!(value(&empty, 12, b"empty"), Some(Vec::new()));
        let (removed, _) = update(&empty, b"empty", None, 0, &named(), false);
        assert_eq!(value(&removed, 12, b"empty"), None);
        let (last, _) = update(&removed, b"note", None, 0, &named(), false);
        assert_eq!(value(&last, 12, b"note"), None);
        assert_eq!(attribute(&last, 2, b""), acl);
        assert_eq!(le32(&last, 1036), free);
        let linux = linux_check("xattr-lifecycle-storage-final", &last);
        assert_eq!(value(&linux, 12, b"note"), None);
    }
    #[test]
    fn first_attribute_promotes_only_ext_attr_and_journals_the_feature_with_the_inode() {
        let img = image();
        assert_eq!(le32(&img, 1116) & 8, 0);
        let (after, cuts) = update(&img, b"first", Some(b"new"), 1, &owner(), true);
        assert_eq!(le32(&after, 1116), le32(&img, 1116) | 8);
        assert_eq!(value(&after, 12, b"first"), Some(b"new".to_vec()));
        for (committed, cut) in cuts {
            let recovered = recover(cut);
            assert_eq!(
                value(&recovered, 12, b"first"),
                committed.then(|| b"new".to_vec())
            );
        }
        let linux = linux_check("xattr-lifecycle-promoted", &after);
        assert_eq!(value(&linux, 12, b"first"), Some(b"new".to_vec()));
    }
    #[test]
    fn shared_block_copy_on_write_preserves_peer_and_recovers_every_writer_cut() {
        let img = shared("xattr-lifecycle-cow");
        let old = pointer(&img, 12);
        let (_, group, _) = metadata(&img);
        let peer = inode_bytes(&img, group.inode_table, 13).to_vec();
        let free = le32(&img, 1036);
        let (after, cuts) = update(&img, b"large", Some(&[0x67; 700]), 2, &named(), true);
        let new = pointer(&after, 12);
        assert_ne!(new, old);
        assert!(new > 0);
        assert_eq!(le32(&after, 1036), free - 1);
        assert_eq!(value(&after, 13, b"large"), Some(vec![0x59; 512]));
        assert_eq!(inode_bytes(&after, group.inode_table, 13), peer);
        assert_eq!(
            &after[old as usize * 4096 + 32..(old as usize + 1) * 4096],
            &img[old as usize * 4096 + 32..(old as usize + 1) * 4096]
        );
        assert_eq!(le32(&after, old as usize * 4096 + 4), 1);
        let mut linux_cut = None;
        for (committed, cut) in cuts {
            if committed && linux_cut.is_none() {
                linux_cut = Some(cut.clone());
            }
            let recovered = recover(cut);
            assert_eq!(
                value(&recovered, 12, b"large"),
                Some(if committed {
                    vec![0x67; 700]
                } else {
                    vec![0x59; 512]
                })
            );
            assert_eq!(value(&recovered, 13, b"large"), Some(vec![0x59; 512]));
            assert_eq!(
                le32(&recovered, 1036),
                if committed { free - 1 } else { free }
            );
        }
        let linux = linux_check("xattr-lifecycle-cow-cut", &linux_cut.unwrap());
        assert_eq!(value(&linux, 12, b"large"), Some(vec![0x67; 700]));
        assert_eq!(value(&linux, 13, b"large"), Some(vec![0x59; 512]));
    }
    #[test]
    fn removing_a_shared_external_value_detaches_without_freeing_the_peers_block() {
        let img = shared("xattr-lifecycle-shared-remove");
        let old = pointer(&img, 12);
        let free = le32(&img, 1036);
        let (after, _) = update(&img, b"large", None, 0, &named(), false);
        assert_eq!(pointer(&after, 12), 0);
        assert_eq!(pointer(&after, 13), old);
        assert_eq!(le32(&after, 1036), free);
        assert_eq!(le32(&after, old as usize * 4096 + 4), 1);
        assert_eq!(value(&after, 13, b"large"), Some(vec![0x59; 512]));
        linux_check("xattr-lifecycle-shared-remove-final", &after);
    }
    #[test]
    fn lifecycle_rejections_leave_the_source_untouched_and_noops_need_no_transaction() {
        let img = fixture("xattr-lifecycle-reject", false);
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        for (name, data, flags) in [
            (&b"note"[..], &b"new"[..], 1),
            (b"absent", b"new", 2),
            (b"note", b"new", 3),
            (b"absent", b"new", 3),
            (b"note", b"new", 4),
            (b"", b"new", 0),
            (b"bad\0name", b"new", 0),
            (b"note", &[1; 4080], 0),
        ] {
            let grant = acl_access::authorize(&node, &named(), &[], 2).unwrap();
            assert!(update::set_user(grant, name, data, flags, 123, 0).is_err());
        }
        let grant = acl_access::authorize(&node, &named(), &[], 2).unwrap();
        assert!(matches!(
            update::set_user(grant, b"note", b"before7", 2, 123, 0),
            Ok(None)
        ));
        let read = acl_access::authorize(&node, &owner(), &[0], 4).unwrap();
        assert!(matches!(
            update::set_user(read, b"note", b"new", 0, 123, 0),
            Err(update::Error::Permission)
        ));
        let grant = acl_access::authorize(&node, &named(), &[], 2).unwrap();
        assert!(matches!(
            update::remove_user(grant, b"absent", 123, 0),
            Err(update::Error::Values(StoreError::Missing))
        ));
        assert_eq!(attribute(&img, 1, b"note"), b"before7");
        assert_eq!(pointer(&img, 12), 0);
    }
    #[test]
    fn rebuilding_an_aliased_input_preserves_the_acl_and_separates_its_value_storage() {
        let mut img = fixture("xattr-lifecycle-alias", false);
        let (_, group, seed) = metadata(&img);
        let raw = inode_bytes(&img, group.inode_table, 12);
        let body = xattr::parse_body(raw, false, le32(&img, 1024)).unwrap();
        let table = body.entry_table().unwrap();
        let note = table.metadata(table.find(1, b"note").unwrap()).unwrap();
        let acl = table.metadata(table.find(2, b"").unwrap()).unwrap();
        let at = group.inode_table as usize * 4096 + 11 * 256;
        img[at + note.position + 2..at + note.position + 4]
            .copy_from_slice(&((acl.value_offset - 164) as u16).to_le_bytes());
        seal_inode_image(&mut img, group.inode_table, 12, seed);
        let old_acl = attribute(&img, 2, b"");
        let (after, _) = update(
            &img,
            b"note",
            Some(b"rebuilt-longer-value"),
            2,
            &named(),
            false,
        );
        assert_eq!(attribute(&after, 2, b""), old_acl);
        assert_eq!(
            value(&after, 12, b"note"),
            Some(b"rebuilt-longer-value".to_vec())
        );
        linux_check("xattr-lifecycle-alias-result", &after);
    }
    #[test]
    fn directory_user_xattrs_preserve_the_namespace_and_the_journal_inode_in_the_same_block() {
        let img = image();
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let node = allocated_inode::get(&volume, 2).unwrap();
        let grant = acl_access::authorize(&node, &owner(), &[0], 2).unwrap();
        let candidate = ok(update::set_user(grant, b"directory", b"value", 1, 123, 0)).unwrap();
        let (after, _) = drive(&img, candidate, false);
        let (_, group, _) = metadata(&img);
        assert_eq!(
            inode_bytes(&after, group.inode_table, 8),
            inode_bytes(&img, group.inode_table, 8)
        );
        assert_eq!(value(&after, 2, b"directory"), Some(b"value".to_vec()));
        linux_check("xattr-lifecycle-directory", &after);
    }
    #[test]
    fn lifecycle_accounting_composes_with_64bit_descriptors_stored_seeds_and_huge_units() {
        for wide in [false, true] {
            for huge in [false, true] {
                let prefix = format!("xattr-lifecycle-formats-{wide}-{huge}");
                let path = format!("build/{prefix}.img");
                let features = format!(
                    "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum,metadata_csum_seed{}{}",
                    if wide { ",64bit" } else { "" },
                    if huge { ",huge_file" } else { "" }
                );
                super::group64_tests::command(
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
                super::group64_tests::command(
                    "DEBUGFS",
                    &["-w", "-R", "write build/fixture-file.bin /payload", &path],
                    false,
                );
                let mut img = std::fs::read(&path).unwrap();
                let (_, group, seed) = metadata(&img);
                let at = group.inode_table as usize * 4096 + 11 * 256;
                if huge {
                    let sectors = le32(&img, at + 28);
                    assert_eq!(sectors % 8, 0);
                    img[at + 28..at + 32].copy_from_slice(&(sectors / 8).to_le_bytes());
                    let flags = le32(&img, at + 32) | core::inode_blocks::HUGE_FLAG;
                    img[at + 32..at + 36].copy_from_slice(&flags.to_le_bytes());
                    seal_inode_image(&mut img, group.inode_table, 12, seed);
                }
                let sectors = core::inode_blocks::decode(
                    inode_bytes(&img, group.inode_table, 12),
                    4096,
                    huge,
                )
                .unwrap();
                let free = le32(&img, 1036);
                let (after, _) = update(&img, b"storage", Some(&[0x79; 512]), 1, &owner(), false);
                assert_eq!(
                    core::inode_blocks::decode(
                        inode_bytes(&after, group.inode_table, 12),
                        4096,
                        huge
                    ),
                    Some(sectors + 8)
                );
                assert_eq!(le32(&after, 1036), free - 1);
                let (removed, _) = update(&after, b"storage", None, 0, &owner(), false);
                assert_eq!(pointer(&removed, 12), 0);
                assert_eq!(le32(&removed, 1036), free);
                assert_eq!(
                    core::inode_blocks::decode(
                        inode_bytes(&removed, group.inode_table, 12),
                        4096,
                        huge
                    ),
                    Some(sectors)
                );
                linux_check(&prefix, &removed);
                let _ = std::fs::remove_file(path);
            }
        }
    }
    #[test]
    fn allocation_accounting_materializes_the_logical_lazy_bitmap_and_preserves_other_bits() {
        for wide in [false, true] {
            let path = format!("build/xattr-lifecycle-lazy-{wide}.img");
            let features = format!(
                "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum{}",
                if wide { ",64bit" } else { "" }
            );
            super::group64_tests::command(
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
            let mut img = std::fs::read(&path).unwrap();
            let width = if wide { 64 } else { 32 };
            let (_, _, seed) = metadata(&img);
            let descriptor = 4096 + width;
            assert_ne!(
                core::bytes::read_le16(&img, descriptor + 18).unwrap() & 2,
                0
            );
            let bitmap = le32(&img, descriptor) as usize;
            img[bitmap * 4096..(bitmap + 1) * 4096].fill(0xa5);
            // The stale physical bitmap is outside the lazy group's source authority.
            let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
            let meta = volume.index().get(1).unwrap();
            let logical = meta.bitmaps().0.raw_image();
            let block = (32768..65536)
                .find(|b| volume.census().role_of(*b).unwrap().kind == 0)
                .unwrap();
            let bit = block % 32768;
            let patches = core::xattr_block_update::accounting(&volume, block, true).unwrap();
            let shadow = volume.index().source().overlay(&patches).unwrap();
            let index = core::group_index::parse(shadow).unwrap();
            let updated = index.get(1).unwrap();
            let mut expected = logical.to_vec();
            expected[bit as usize / 8] |= 1 << (bit % 8);
            assert_eq!(updated.bitmaps().0.raw_image(), expected);
            assert_eq!(
                core::bytes::read_le16(updated.descriptor(), 18).unwrap() & 2,
                0
            );
            assert_eq!(
                updated.bitmaps().0.free_count() + 1,
                meta.bitmaps().0.free_count()
            );
            assert_eq!(
                le32(patches.get(0).unwrap().as_slice(), 1036) + 1,
                le32(&img, 1036)
            );
            assert_eq!(
                core::crc::crc32c(seed, updated.bitmaps().0.raw_image()) as u16,
                core::bytes::read_le16(updated.descriptor(), 24).unwrap()
            );
            let _ = std::fs::remove_file(path);
        }
    }
    #[test]
    fn generated_xattr_padding_and_hashes_are_checked_beyond_structural_parsing() {
        let values = set(Store::new(), 1, b"a", &[0x77; 201], 0);
        let mut inode = vec![0; 256];
        inode[128..130].copy_from_slice(&32u16.to_le_bytes());
        let packed = core::xattr_pack::encode(&values, &inode, 55, 0x12345678, 100).unwrap();
        let (_, external) = packed.into_parts();
        let raw = external.unwrap();
        let original = xattr::parse_block(&raw, 55, 0x12345678, true, false, 100).unwrap();
        assert!(core::xattr_canonical::check(original.entries(), true));
        let e = original.entries().metadata(0).unwrap();
        for byte in [
            e.position + 16 + e.name_length,
            e.value_offset + e.value_size as usize,
            e.position + 12,
            12,
        ] {
            let mut corrupt = raw.clone();
            corrupt[byte] ^= 0x91;
            let checksum = xattr::checksum(&corrupt, 55, 0x12345678).unwrap();
            corrupt[16..20].copy_from_slice(&checksum.to_le_bytes());
            let parsed = xattr::parse_block(&corrupt, 55, 0x12345678, true, false, 100).unwrap();
            assert!(
                !core::xattr_canonical::check(parsed.entries(), true),
                "padding/hash at {byte}"
            );
        }
    }
}

mod acl_xattr_updates {
    use core::{
        access, acl_access,
        acl_update::{self as update, Credentials, Kind},
        acl_xattr, allocated_inode, allocation,
        recovery_request::Completion,
        snapshot::Snapshot,
        xattr_inode,
        xattr_table::ValueRef,
    };

    use super::{
        inline_xattr_updates::{command, fixture, recover},
        *,
    };

    fn wire(entries: &[(u16, u16, u32)]) -> Vec<u8> {
        let mut raw = 2u32.to_le_bytes().to_vec();
        for (tag, bits, id) in entries {
            raw.extend(tag.to_le_bytes());
            raw.extend(bits.to_le_bytes());
            raw.extend(id.to_le_bytes());
        }
        raw
    }
    fn simple(owner: u16, group: u16, other: u16) -> Vec<u8> {
        wire(&[
            (1, owner, u32::MAX),
            (4, group, u32::MAX),
            (32, other, u32::MAX),
        ])
    }
    fn extended(count: u32, mask: u16) -> Vec<u8> {
        let mut entries = vec![(1, 6, u32::MAX), (2, mask, 1234)];
        for id in 0..count {
            entries.push((2, mask, 10000 + id));
        }
        entries.extend([(4, 0, u32::MAX), (16, mask, u32::MAX), (32, 0, u32::MAX)]);
        wire(&entries)
    }
    fn owner() -> Credentials {
        Credentials {
            fsuid: 0,
            fowner: false,
            fsetid: false,
        }
    }
    fn ok<T>(result: Result<T, update::Error>) -> T {
        match result {
            Ok(value) => value,
            Err(_) => panic!("ACL update rejected"),
        }
    }
    fn mode(img: &[u8], number: u32) -> u16 {
        let (_, group, _) = metadata(img);
        core::bytes::read_le16(inode_bytes(img, group.inode_table, number), 0).unwrap()
    }
    fn pointer(img: &[u8], number: u32) -> u32 {
        let (_, group, _) = metadata(img);
        core::xattr::inode_pointer(inode_bytes(img, group.inode_table, number)).unwrap() as u32
    }
    fn attribute(img: &[u8], number: u32, ns: u8, name: &[u8]) -> Option<Vec<u8>> {
        let volume = allocation::parse(Snapshot::from_bytes(img)).unwrap();
        let attrs = xattr_inode::inspect(volume.index(), number).unwrap();
        match attrs.get(ns, name) {
            Some(ValueRef::Bytes(raw)) => Some(raw.to_vec()),
            None => None,
            _ => panic!("local value"),
        }
    }
    fn drive(
        img: &[u8],
        candidate: update::Candidate<'_, '_, '_>,
        cuts: bool,
    ) -> (Vec<u8>, Vec<(bool, Vec<u8>)>) {
        let mut writer = candidate.begin().expect("full ACL transaction admission");
        let mut stable = img.to_vec();
        let mut snapshots = Vec::new();
        let mut committed = false;
        loop {
            let pending = match writer.dispatch() {
                Ok(pending) => pending,
                Err(done) => {
                    assert!(done.finished());
                    break;
                }
            };
            if let core::recovery_io::Command::Write { block, image } = pending.pending_command() {
                if core::bytes::read_be32(image, 0) == Some(0xc03b3998)
                    && core::bytes::read_be32(image, 4) == Some(2)
                {
                    committed = true;
                }
                stable[block as usize * 4096..(block as usize + 1) * 4096].copy_from_slice(image);
                if cuts {
                    snapshots.push((committed, stable.clone()));
                }
            }
            writer = pending.finish_pending(Completion::Succeeded);
        }
        assert!(core::image_validation::inspect(Snapshot::from_bytes(&stable)).is_some());
        (stable, snapshots)
    }
    fn apply(
        img: &[u8],
        number: u32,
        kind: Kind,
        raw: &[u8],
        credentials: &Credentials,
        groups: &[u32],
        cuts: bool,
    ) -> (Vec<u8>, Vec<(bool, Vec<u8>)>) {
        let volume = allocation::parse(Snapshot::from_bytes(img)).unwrap();
        let node = allocated_inode::get(&volume, number).unwrap();
        let grant = update::authorize(&node, credentials, groups, kind)
            .expect("ACL owner or capability authority");
        let candidate = match ok(update::prepare(grant, raw, 123456789, 987654321)) {
            Some(candidate) => candidate,
            None => {
                return (img.to_vec(), Vec::new());
            }
        };
        drive(img, candidate, cuts)
    }
    fn linux(prefix: &str, img: &[u8]) -> Vec<u8> {
        let path = format!("build/{prefix}.img");
        std::fs::write(&path, img).unwrap();
        let fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        command(&fsck, &["-fy", &path], true);
        command(&fsck, &["-fn", &path], false);
        let result = std::fs::read(&path).unwrap();
        let _ = std::fs::remove_file(path);
        result
    }
    fn set_mode(img: &mut [u8], number: u32, value: u16) {
        let (_, group, seed) = metadata(img);
        let at = group.inode_table as usize * 4096 + (number as usize - 1) * 256;
        img[at..at + 2].copy_from_slice(&value.to_le_bytes());
        seal_inode_image(img, group.inode_table, number, seed);
    }
    fn named_allowed(img: &[u8], bits: u8) -> bool {
        let volume = allocation::parse(Snapshot::from_bytes(img)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        let credentials = access::Credentials {
            fsuid: 1234,
            in_inode_group: false,
            dac_override: false,
            dac_read_search: false,
        };
        acl_access::authorize(&node, &credentials, &[], bits).is_some()
    }

    #[test]
    fn acl_uapi_conversion_matches_linux_compact_bytes_and_preserves_named_ids() {
        let input = extended(0, 2);
        let converted = acl_xattr::decode(&input).unwrap();
        let img = fixture("acl-update-codec", false);
        assert_eq!(converted.as_slice(), attribute(&img, 12, 2, b"").unwrap());
        let acl = converted.parsed().unwrap();
        let summary = acl_xattr::summarize(&acl).unwrap();
        assert_eq!(summary.bits, 0o620);
        assert!(summary.extended);
        assert_eq!(acl.entry(1).unwrap().id, 1234);
        let ignored = wire(&[
            (1, 6, 100),
            (2, 2, 1234),
            (4, 0, 200),
            (16, 2, 300),
            (32, 0, 400),
        ]);
        assert_eq!(
            acl_xattr::decode(&ignored).unwrap().as_slice(),
            converted.as_slice(),
            "Linux ignores IDs on short entries"
        );
        let mask_only =
            acl_xattr::decode(&wire(&[(1, 6, 0), (4, 7, 0), (16, 1, 0), (32, 0, 0)])).unwrap();
        assert!(
            acl_xattr::summarize(&mask_only.parsed().unwrap())
                .unwrap()
                .extended
        );
        for raw in [
            vec![1, 0, 0, 0],
            vec![2, 0, 0],
            vec![2, 0, 0, 0, 1],
            simple(8, 0, 0),
            wire(&[
                (1, 6, 0),
                (2, 2, u32::MAX),
                (4, 0, 0),
                (16, 2, 0),
                (32, 0, 0),
            ]),
            wire(&[(1, 6, 0), (2, 2, 1234), (4, 0, 0), (32, 0, 0)]),
        ] {
            assert!(acl_xattr::decode(&raw).is_none());
        }
        assert!(acl_xattr::is_removal(b""));
        assert!(acl_xattr::is_removal(&2u32.to_le_bytes()));
        assert!(!acl_xattr::is_removal(&1u32.to_le_bytes()));
    }
    #[test]
    fn an_owner_without_write_permission_can_set_a_mode_only_acl_without_enabling_ext_attr() {
        let mut img = image();
        set_mode(&mut img, 12, 0o100400);
        assert_eq!(le32(&img, 1116) & 8, 0);
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        let ordinary = access::Credentials {
            fsuid: 0,
            in_inode_group: true,
            dac_override: false,
            dac_read_search: false,
        };
        assert!(acl_access::authorize(&node, &ordinary, &[0], 2).is_none());
        let (after, _) = apply(
            &img,
            12,
            Kind::Access,
            &simple(6, 4, 0),
            &owner(),
            &[],
            false,
        );
        assert_eq!(mode(&after, 12), 0o100640);
        assert_eq!(attribute(&after, 12, 2, b""), None);
        assert_eq!(le32(&after, 1116), le32(&img, 1116));
        assert_eq!(pointer(&after, 12), 0);
        let linux = linux("acl-update-mode-only", &after);
        assert_eq!(mode(&linux, 12), 0o100640);
    }
    #[test]
    fn named_acl_write_permission_cannot_authorize_acl_mutation_or_retarget_a_default_grant() {
        let img = fixture("acl-update-authority", false);
        assert!(named_allowed(&img, 2));
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        let user = Credentials {
            fsuid: 1234,
            fowner: false,
            fsetid: false,
        };
        assert!(update::authorize(&node, &user, &[], Kind::Access).is_none());
        let default = update::authorize(&node, &user, &[], Kind::Default).unwrap();
        assert!(matches!(update::prepare(default, b"", 1, 0), Ok(None)));
        let default = update::authorize(&node, &user, &[], Kind::Default).unwrap();
        assert!(matches!(
            update::prepare(default, &simple(7, 7, 7), 1, 0),
            Err(update::Error::NotDirectory)
        ));
    }
    #[test]
    fn setting_an_access_acl_clears_sgid_unless_group_membership_or_fsetid_preserves_it() {
        for in_group in [false, true] {
            for fsetid in [false, true] {
                let mut img = fixture(&format!("acl-update-sgid-{in_group}-{fsetid}"), false);
                set_mode(&mut img, 12, 0o102620);
                let credentials = Credentials { fsetid, ..owner() };
                let groups: &[u32] = if in_group { &[0] } else { &[] };
                let (after, _) = apply(
                    &img,
                    12,
                    Kind::Access,
                    &extended(0, 4),
                    &credentials,
                    groups,
                    false,
                );
                assert_eq!(
                    mode(&after, 12),
                    if in_group || fsetid {
                        0o102640
                    } else {
                        0o100640
                    }
                );
                assert_eq!(attribute(&after, 12, 1, b"note"), Some(b"before7".to_vec()));
                linux(
                    &format!("acl-update-sgid-result-{in_group}-{fsetid}"),
                    &after,
                );
            }
        }
    }
    #[test]
    fn mask_only_acls_remain_extended_and_mode_only_acls_are_folded() {
        let img = fixture("acl-update-equivalence", false);
        let masked = wire(&[(1, 6, 0), (4, 7, 0), (16, 1, 0), (32, 0, 0)]);
        let (after, _) = apply(&img, 12, Kind::Access, &masked, &owner(), &[0], false);
        assert_eq!(mode(&after, 12), 0o100610);
        assert!(attribute(&after, 12, 2, b"").is_some());
        let (folded, _) = apply(
            &after,
            12,
            Kind::Access,
            &simple(4, 0, 0),
            &owner(),
            &[],
            false,
        );
        assert_eq!(mode(&folded, 12), 0o100400);
        assert_eq!(attribute(&folded, 12, 2, b""), None);
        assert_eq!(
            attribute(&folded, 12, 1, b"note"),
            Some(b"before7".to_vec())
        );
        linux("acl-update-equivalence-result", &folded);
    }
    #[test]
    fn default_acls_are_kept_on_directories_without_changing_mode_or_sgid() {
        let mut img = image();
        set_mode(&mut img, 2, 0o042755);
        let input = simple(7, 0, 0);
        let (after, _) = apply(&img, 2, Kind::Default, &input, &owner(), &[], false);
        assert_eq!(mode(&after, 2), 0o042755);
        assert_eq!(
            attribute(&after, 2, 3, b""),
            Some(acl_xattr::decode(&input).unwrap().as_slice().to_vec())
        );
        let (removed, _) = apply(
            &after,
            2,
            Kind::Default,
            &2u32.to_le_bytes(),
            &owner(),
            &[],
            false,
        );
        assert_eq!(mode(&removed, 2), 0o042755);
        assert_eq!(attribute(&removed, 2, 3, b""), None);
        linux("acl-update-default-result", &removed);
    }
    #[test]
    fn access_acl_removal_preserves_mode_and_is_idempotent_even_when_the_key_is_absent() {
        let img = fixture("acl-update-remove", true);
        let before_mode = mode(&img, 12);
        let (after, _) = apply(&img, 12, Kind::Access, b"", &owner(), &[], false);
        assert_eq!(mode(&after, 12), before_mode);
        assert_eq!(attribute(&after, 12, 2, b""), None);
        assert_eq!(attribute(&after, 12, 1, b"large"), Some(vec![0x59; 512]));
        let (again, _) = apply(
            &after,
            12,
            Kind::Access,
            &2u32.to_le_bytes(),
            &owner(),
            &[],
            false,
        );
        assert_eq!(again, after);
        linux("acl-update-remove-result", &after);
    }
    #[test]
    fn crash_recovery_publishes_acl_mode_permissions_and_allocation_together() {
        let img = fixture("acl-update-crash", false);
        let old = attribute(&img, 12, 2, b"").unwrap();
        let input = extended(32, 4);
        let target = acl_xattr::decode(&input).unwrap().as_slice().to_vec();
        let free = le32(&img, 1036);
        let (after, cuts) = apply(&img, 12, Kind::Access, &input, &owner(), &[0], true);
        assert_eq!(mode(&after, 12), 0o100640);
        assert_eq!(attribute(&after, 12, 2, b""), Some(target.clone()));
        assert_eq!(le32(&after, 1036), free - 1);
        let mut committed = None;
        for (done, cut) in cuts {
            if done && committed.is_none() {
                committed = Some(cut.clone());
            }
            let recovered = recover(cut);
            assert_eq!(mode(&recovered, 12), if done { 0o100640 } else { 0o100620 });
            assert_eq!(
                attribute(&recovered, 12, 2, b""),
                Some(if done { target.clone() } else { old.clone() })
            );
            assert_eq!(named_allowed(&recovered, 4), done);
            assert_eq!(named_allowed(&recovered, 2), !done);
            assert_eq!(le32(&recovered, 1036), if done { free - 1 } else { free });
        }
        let linux = linux("acl-update-crash-linux", &committed.unwrap());
        assert_eq!(mode(&linux, 12), 0o100640);
        assert_eq!(attribute(&linux, 12, 2, b""), Some(target));
    }
    #[test]
    fn invalid_acl_inputs_readonly_sources_and_denied_owners_prepare_no_writes() {
        let img = fixture("acl-update-invalid", false);
        let original = img.clone();
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        for input in [vec![1, 0, 0, 0], simple(8, 0, 0), vec![2, 0, 0, 0, 1]] {
            let grant = update::authorize(&node, &owner(), &[0], Kind::Access).unwrap();
            assert!(matches!(
                update::prepare(grant, &input, 1, 0),
                Err(update::Error::InvalidAcl)
            ));
        }
        let mut readonly = img.clone();
        let flags = le32(&readonly, 1124) | 0x1000;
        readonly[1124..1128].copy_from_slice(&flags.to_le_bytes());
        let checksum = core::crc::crc32c(0xffffffff, &readonly[1024..2044]);
        readonly[2044..2048].copy_from_slice(&checksum.to_le_bytes());
        let volume = allocation::parse(Snapshot::from_bytes(&readonly)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        let grant = update::authorize(&node, &owner(), &[0], Kind::Access).unwrap();
        assert!(matches!(
            update::prepare(grant, &simple(7, 7, 7), 1, 0),
            Err(update::Error::ReadOnly)
        ));
        assert_eq!(img, original);
    }
    #[test]
    fn shared_acl_blocks_use_copy_on_write_and_folding_releases_only_the_new_exclusive_block() {
        let path = "build/acl-update-shared.img";
        let raw_path = "build/acl-update-shared.bin";
        let old_input = extended(32, 2);
        std::fs::write(path, image()).unwrap();
        std::fs::write(raw_path, &old_input).unwrap();
        let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
        for request in [
            "feature ext_attr".to_string(),
            "write build/fixture-file.bin /peer".to_string(),
            "ea_set /payload user.note before7".to_string(),
            "ea_set /peer user.note peer".to_string(),
            format!("ea_set -f {raw_path} /payload system.posix_acl_access"),
            format!("ea_set -f {raw_path} /peer system.posix_acl_access"),
            "sif /payload mode 0100620".to_string(),
            "sif /peer mode 0100620".to_string(),
        ] {
            command(&debugfs, &["-w", "-R", &request, path], false);
        }
        let mut img = std::fs::read(path).unwrap();
        let (_, group, seed) = metadata(&img);
        let old = pointer(&img, 12);
        let second = pointer(&img, 13);
        assert_ne!(old, second);
        assert!(old > 0 && second > 0);
        let peer = group.inode_table as usize * 4096 + 12 * 256;
        img[peer + 104..peer + 108].copy_from_slice(&old.to_le_bytes());
        seal_inode_image(&mut img, group.inode_table, 13, seed);
        let at = old as usize * 4096;
        img[at + 4..at + 8].copy_from_slice(&2u32.to_le_bytes());
        let checksum = core::xattr::checksum(&img[at..at + 4096], old as u64, seed).unwrap();
        img[at + 16..at + 20].copy_from_slice(&checksum.to_le_bytes());
        img[group.block_bitmap as usize * 4096 + second as usize / 8] &= !(1 << (second % 8));
        seal_single_group_allocation(&mut img);
        assert!(core::image_validation::inspect(Snapshot::from_bytes(&img)).is_some());
        let old_peer = inode_bytes(&img, group.inode_table, 13).to_vec();
        let old_acl = attribute(&img, 13, 2, b"").unwrap();
        let free = le32(&img, 1036);
        let (after, _) = apply(
            &img,
            12,
            Kind::Access,
            &extended(40, 4),
            &owner(),
            &[0],
            false,
        );
        assert_ne!(pointer(&after, 12), old);
        assert_eq!(le32(&after, 1036), free - 1);
        assert_eq!(inode_bytes(&after, group.inode_table, 13), old_peer);
        assert_eq!(attribute(&after, 13, 2, b""), Some(old_acl.clone()));
        assert_eq!(le32(&after, old as usize * 4096 + 4), 1);
        assert_eq!(mode(&after, 12), 0o100640);
        let (folded, _) = apply(
            &after,
            12,
            Kind::Access,
            &simple(6, 0, 0),
            &owner(),
            &[0],
            false,
        );
        assert_eq!(pointer(&folded, 12), 0);
        assert_eq!(le32(&folded, 1036), free);
        assert_eq!(attribute(&folded, 12, 2, b""), None);
        assert_eq!(
            attribute(&folded, 12, 1, b"note"),
            Some(b"before7".to_vec())
        );
        assert_eq!(attribute(&folded, 13, 2, b""), Some(old_acl));
        assert_eq!(mode(&folded, 13), 0o100620);
        linux("acl-update-shared-final", &folded);
        let _ = std::fs::remove_file(path);
        let _ = std::fs::remove_file(raw_path);
    }
    #[test]
    fn scoped_fowner_can_update_another_owners_acl_and_fsetid_alone_cannot() {
        let mut img = fixture("acl-update-fowner", false);
        let (_, group, seed) = metadata(&img);
        let at = group.inode_table as usize * 4096 + 11 * 256;
        img[at + 2..at + 4].copy_from_slice(&1000u16.to_le_bytes());
        seal_inode_image(&mut img, group.inode_table, 12, seed);
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        assert!(update::authorize(&node, &owner(), &[0], Kind::Access).is_none());
        assert!(
            update::authorize(
                &node,
                &Credentials {
                    fsetid: true,
                    ..owner()
                },
                &[0],
                Kind::Access
            )
            .is_none()
        );
        let (after, _) = apply(
            &img,
            12,
            Kind::Access,
            &simple(4, 0, 0),
            &Credentials {
                fowner: true,
                ..owner()
            },
            &[0],
            false,
        );
        assert_eq!(mode(&after, 12), 0o100400);
        assert_eq!(
            core::bytes::read_le16(inode_bytes(&after, group.inode_table, 12), 2),
            Some(1000)
        );
        linux("acl-update-fowner-result", &after);
    }
    #[test]
    fn acl_mode_storage_and_checksums_compose_with_wide_descriptors_stored_seeds_and_huge_units() {
        for wide in [false, true] {
            for huge in [false, true] {
                let prefix = format!("acl-update-formats-{wide}-{huge}");
                let path = format!("build/{prefix}.img");
                let features = format!(
                    "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum,metadata_csum_seed{}{}",
                    if wide { ",64bit" } else { "" },
                    if huge { ",huge_file" } else { "" }
                );
                super::group64_tests::command(
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
                super::group64_tests::command(
                    "DEBUGFS",
                    &["-w", "-R", "write build/fixture-file.bin /payload", &path],
                    false,
                );
                let mut img = std::fs::read(&path).unwrap();
                let (_, group, seed) = metadata(&img);
                let at = group.inode_table as usize * 4096 + 11 * 256;
                if huge {
                    let sectors = le32(&img, at + 28);
                    img[at + 28..at + 32].copy_from_slice(&(sectors / 8).to_le_bytes());
                    let flags = le32(&img, at + 32) | core::inode_blocks::HUGE_FLAG;
                    img[at + 32..at + 36].copy_from_slice(&flags.to_le_bytes());
                    seal_inode_image(&mut img, group.inode_table, 12, seed);
                }
                let sectors = core::inode_blocks::decode(
                    inode_bytes(&img, group.inode_table, 12),
                    4096,
                    huge,
                )
                .unwrap();
                let free = le32(&img, 1036);
                let (after, _) = apply(
                    &img,
                    12,
                    Kind::Access,
                    &extended(32, 2),
                    &owner(),
                    &[0],
                    false,
                );
                assert_eq!(mode(&after, 12), 0o100620);
                assert_eq!(
                    core::inode_blocks::decode(
                        inode_bytes(&after, group.inode_table, 12),
                        4096,
                        huge
                    ),
                    Some(sectors + 8)
                );
                assert_eq!(le32(&after, 1036), free - 1);
                let (folded, _) = apply(
                    &after,
                    12,
                    Kind::Access,
                    &simple(4, 0, 0),
                    &owner(),
                    &[0],
                    false,
                );
                assert_eq!(mode(&folded, 12), 0o100400);
                assert_eq!(pointer(&folded, 12), 0);
                assert_eq!(le32(&folded, 1036), free);
                assert_eq!(
                    core::inode_blocks::decode(
                        inode_bytes(&folded, group.inode_table, 12),
                        4096,
                        huge
                    ),
                    Some(sectors)
                );
                linux(&prefix, &folded);
                let _ = std::fs::remove_file(path);
            }
        }
    }
}

// Execute the emitted ACL transformations; native checks do not discharge proofs.
mod acl_mode_transforms {
    use core::{acl, acl_transform, acl_xattr};

    fn disk(entries: &[(u16, u16, u32)]) -> Vec<u8> {
        let mut input = 2u32.to_le_bytes().to_vec();
        for (tag, permissions, id) in entries {
            input.extend(tag.to_le_bytes());
            input.extend(permissions.to_le_bytes());
            input.extend(id.to_le_bytes());
        }
        acl_xattr::decode(&input).unwrap().as_slice().to_vec()
    }

    fn entries(acl: &acl::Acl<'_>) -> Vec<(u16, u8, u32)> {
        (0..acl.count())
            .map(|i| {
                let e = acl.entry(i).unwrap();
                (e.tag, e.permissions, e.id)
            })
            .collect()
    }

    fn extended() -> Vec<u8> {
        disk(&[
            (1, 6, u32::MAX),
            (2, 7, 1234),
            (2, 5, 9876),
            (4, 3, u32::MAX),
            (8, 6, 4567),
            (16, 5, u32::MAX),
            (32, 2, u32::MAX),
        ])
    }

    #[test]
    fn chmod_updates_owner_mask_other_and_preserves_named_entries_ids_and_group_obj() {
        let raw = extended();
        let before = raw.clone();
        let original = acl::parse(&raw).unwrap();
        for bits in 0u16..=0o777 {
            let requested = 0o106000 | bits;
            let changed = acl_transform::chmod(&original, requested).unwrap();
            let parsed = changed.parsed().unwrap();
            assert_eq!(changed.mode(), requested);
            assert!(changed.extended());
            assert_eq!(
                entries(&parsed),
                vec![
                    (1, ((bits >> 6) & 7) as u8, 0),
                    (2, 7, 1234),
                    (2, 5, 9876),
                    (4, 3, 0),
                    (8, 6, 4567),
                    (16, ((bits >> 3) & 7) as u8, 0),
                    (32, (bits & 7) as u8, 0),
                ]
            );
            let repeated = acl_transform::chmod(&parsed, requested).unwrap();
            assert_eq!(repeated.as_slice(), changed.as_slice());
        }
        assert_eq!(raw, before, "chmod transforms a clone of the source ACL");
    }

    #[test]
    fn chmod_uses_group_obj_without_a_mask_and_retains_mask_only_acls() {
        let basic = disk(&[(1, 6, 0), (4, 3, 0), (32, 2, 0)]);
        let basic_acl = acl::parse(&basic).unwrap();
        let masked = disk(&[(1, 6, 0), (4, 3, 0), (16, 5, 0), (32, 2, 0)]);
        let masked_acl = acl::parse(&masked).unwrap();
        for bits in 0u16..=0o777 {
            let basic_changed = acl_transform::chmod(&basic_acl, bits).unwrap();
            assert!(!basic_changed.extended());
            assert_eq!(
                entries(&basic_changed.parsed().unwrap()),
                vec![
                    (1, ((bits >> 6) & 7) as u8, 0),
                    (4, ((bits >> 3) & 7) as u8, 0),
                    (32, (bits & 7) as u8, 0),
                ]
            );
            let masked_changed = acl_transform::chmod(&masked_acl, bits).unwrap();
            assert!(masked_changed.extended());
            assert_eq!(
                entries(&masked_changed.parsed().unwrap()),
                vec![
                    (1, ((bits >> 6) & 7) as u8, 0),
                    (4, 3, 0),
                    (16, ((bits >> 3) & 7) as u8, 0),
                    (32, (bits & 7) as u8, 0),
                ]
            );
        }
    }

    #[test]
    fn inherited_extended_acl_intersects_requested_classes_without_changing_named_permissions() {
        let raw = extended();
        let before = raw.clone();
        let default = acl::parse(&raw).unwrap();
        for bits in 0u16..=0o777 {
            let requested = 0o046000 | bits;
            let inherited = acl_transform::inherit(&default, requested).unwrap();
            let parsed = inherited.parsed().unwrap();
            assert!(inherited.extended());
            let owner = 6 & ((bits >> 6) & 7) as u8;
            let group = 5 & ((bits >> 3) & 7) as u8;
            let other = 2 & (bits & 7) as u8;
            assert_eq!(
                inherited.mode(),
                (requested & !0o777)
                    | (u16::from(owner) << 6)
                    | (u16::from(group) << 3)
                    | u16::from(other)
            );
            assert_eq!(
                entries(&parsed),
                vec![
                    (1, owner, 0),
                    (2, 7, 1234),
                    (2, 5, 9876),
                    (4, 3, 0),
                    (8, 6, 4567),
                    (16, group, 0),
                    (32, other, 0),
                ]
            );
            for (uid, groups) in [
                (1000, vec![]),
                (1234, vec![]),
                (9876, vec![]),
                (2000, vec![200]),
                (2000, vec![4567]),
                (2000, vec![200, 4567]),
                (3000, vec![]),
            ] {
                for request in 0..=7 {
                    assert!(
                        !parsed.allows(1000, 200, uid, &groups, request)
                            || default.allows(1000, 200, uid, &groups, request),
                        "inheritance broadened source rights: mode={bits:o}, uid={uid}, request={request}"
                    );
                }
            }
        }
        assert_eq!(
            raw, before,
            "the child's default ACL remains the original bytes"
        );
    }

    #[test]
    fn inherited_basic_acl_intersects_group_obj_and_can_fold_to_mode() {
        let raw = disk(&[(1, 6, 0), (4, 3, 0), (32, 2, 0)]);
        let default = acl::parse(&raw).unwrap();
        for bits in 0u16..=0o777 {
            let requested = 0o102000 | bits;
            let inherited = acl_transform::inherit(&default, requested).unwrap();
            assert!(!inherited.extended());
            let owner = 6 & ((bits >> 6) & 7) as u8;
            let group = 3 & ((bits >> 3) & 7) as u8;
            let other = 2 & (bits & 7) as u8;
            assert_eq!(
                inherited.mode(),
                (requested & !0o777)
                    | (u16::from(owner) << 6)
                    | (u16::from(group) << 3)
                    | u16::from(other)
            );
            assert_eq!(
                entries(&inherited.parsed().unwrap()),
                vec![(1, owner, 0), (4, group, 0), (32, other, 0)]
            );
        }
    }

    #[test]
    fn mask_only_inheritance_preserves_group_obj_and_cannot_fold_even_when_mode_is_zero() {
        let raw = disk(&[(1, 7, 0), (4, 7, 0), (16, 6, 0), (32, 7, 0)]);
        let default = acl::parse(&raw).unwrap();
        let inherited = acl_transform::inherit(&default, 0o040000).unwrap();
        assert!(inherited.extended());
        assert_eq!(inherited.mode(), 0o040000);
        assert_eq!(
            entries(&inherited.parsed().unwrap()),
            vec![(1, 0, 0), (4, 7, 0), (16, 0, 0), (32, 0, 0)]
        );
        assert_eq!(default.entry(2).unwrap().permissions, 6);
    }
}

// ACL chmod uses the complete writer on the same Linux-created fixtures.
mod acl_chmod_updates {
    use core::{
        access, acl_access, acl_chmod as chmod, acl_transform,
        acl_update::{self as update, Credentials, Kind},
        acl_xattr, allocated_inode, allocation,
        recovery_request::Completion,
        snapshot::Snapshot,
        xattr_inode,
        xattr_table::ValueRef,
    };

    use super::{
        inline_xattr_updates::{command, fixture, recover},
        *,
    };

    fn owner() -> Credentials {
        Credentials {
            fsuid: 0,
            fowner: false,
            fsetid: false,
        }
    }
    fn wire(entries: &[(u16, u16, u32)]) -> Vec<u8> {
        let mut raw = 2u32.to_le_bytes().to_vec();
        for (tag, bits, id) in entries {
            raw.extend(tag.to_le_bytes());
            raw.extend(bits.to_le_bytes());
            raw.extend(id.to_le_bytes());
        }
        raw
    }
    fn mode(img: &[u8], number: u32) -> u16 {
        let (_, group, _) = metadata(img);
        core::bytes::read_le16(inode_bytes(img, group.inode_table, number), 0).unwrap()
    }
    fn set_mode(img: &mut [u8], number: u32, value: u16) {
        let (_, group, seed) = metadata(img);
        let at = group.inode_table as usize * 4096 + (number as usize - 1) * 256;
        img[at..at + 2].copy_from_slice(&value.to_le_bytes());
        seal_inode_image(img, group.inode_table, number, seed);
    }
    fn attribute(img: &[u8], number: u32, ns: u8, name: &[u8]) -> Option<Vec<u8>> {
        let volume = allocation::parse(Snapshot::from_bytes(img)).unwrap();
        let attrs = xattr_inode::inspect(volume.index(), number).unwrap();
        match attrs.get(ns, name) {
            Some(ValueRef::Bytes(raw)) => Some(raw.to_vec()),
            None => None,
            _ => panic!("local value"),
        }
    }
    fn drive(
        img: &[u8],
        mut writer: core::writer_admission::CheckedWriter<'_, '_>,
        cuts: bool,
    ) -> (Vec<u8>, Vec<(bool, Vec<u8>)>) {
        let mut stable = img.to_vec();
        let mut snapshots = Vec::new();
        let mut committed = false;
        loop {
            let pending = match writer.dispatch() {
                Ok(pending) => pending,
                Err(done) => {
                    assert!(done.finished());
                    break;
                }
            };
            if let core::recovery_io::Command::Write { block, image } = pending.pending_command() {
                if core::bytes::read_be32(image, 0) == Some(0xc03b3998)
                    && core::bytes::read_be32(image, 4) == Some(2)
                {
                    committed = true;
                }
                stable[block as usize * 4096..(block as usize + 1) * 4096].copy_from_slice(image);
                if cuts {
                    snapshots.push((committed, stable.clone()));
                }
            }
            writer = pending.finish_pending(Completion::Succeeded);
        }
        assert!(core::image_validation::inspect(Snapshot::from_bytes(&stable)).is_some());
        (stable, snapshots)
    }
    fn apply(
        img: &[u8],
        number: u32,
        requested: u16,
        credentials: &Credentials,
        groups: &[u32],
        cuts: bool,
    ) -> (Vec<u8>, Vec<(bool, Vec<u8>)>) {
        let volume = allocation::parse(Snapshot::from_bytes(img)).unwrap();
        let node = allocated_inode::get(&volume, number).unwrap();
        let grant = chmod::authorize(&node, credentials, groups).expect("chmod owner/capability");
        let candidate = match chmod::prepare(grant, requested, 123456789, 987654321) {
            Ok(Some(candidate)) => candidate,
            Ok(None) => return (img.to_vec(), Vec::new()),
            Err(_) => panic!("chmod rejected"),
        };
        drive(
            img,
            candidate.begin().expect("full chmod writer admission"),
            cuts,
        )
    }
    fn set_acl(img: &[u8], number: u32, kind: Kind, raw: &[u8]) -> Vec<u8> {
        let volume = allocation::parse(Snapshot::from_bytes(img)).unwrap();
        let node = allocated_inode::get(&volume, number).unwrap();
        let grant = update::authorize(&node, &owner(), &[0], kind).unwrap();
        let candidate = match update::prepare(grant, raw, 123456788, 123456789) {
            Ok(Some(candidate)) => candidate,
            _ => panic!("fixture ACL mutation"),
        };
        drive(img, candidate.begin().unwrap(), false).0
    }
    fn linux(prefix: &str, img: &[u8]) -> Vec<u8> {
        let path = format!("build/{prefix}.img");
        std::fs::write(&path, img).unwrap();
        let fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        command(&fsck, &["-fy", &path], true);
        command(&fsck, &["-fn", &path], false);
        let result = std::fs::read(&path).unwrap();
        let _ = std::fs::remove_file(path);
        result
    }
    fn named_allowed(img: &[u8], request: u8) -> bool {
        let volume = allocation::parse(Snapshot::from_bytes(img)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        let credentials = access::Credentials {
            fsuid: 1234,
            in_inode_group: false,
            dac_override: false,
            dac_read_search: false,
        };
        acl_access::authorize(&node, &credentials, &[], request).is_some()
    }

    #[test]
    fn chmod_without_an_acl_sets_special_bits_and_applies_group_fsetid_policy() {
        let img = image();
        assert_eq!(le32(&img, 1116) & 8, 0);
        for in_group in [false, true] {
            for fsetid in [false, true] {
                let credentials = Credentials { fsetid, ..owner() };
                let groups: &[u32] = if in_group { &[0] } else { &[] };
                let (after, _) = apply(&img, 12, 0o7750, &credentials, groups, false);
                assert_eq!(
                    mode(&after, 12),
                    if in_group || fsetid {
                        0o107750
                    } else {
                        0o105750
                    }
                );
                assert_eq!(attribute(&after, 12, 2, b""), None);
                assert_eq!(le32(&after, 1116), le32(&img, 1116));
                assert_eq!(le32(&after, 1036), le32(&img, 1036));
                linux(&format!("acl-chmod-special-{in_group}-{fsetid}"), &after);
            }
        }
    }

    #[test]
    fn chmod_changes_only_access_acl_owner_mask_other_and_keeps_default_and_other_values() {
        let img = fixture("acl-chmod-preserve", true);
        let before_acl = attribute(&img, 12, 2, b"").unwrap();
        let before = core::acl::parse(&before_acl).unwrap();
        let expected = acl_transform::chmod(&before, 0o100751).unwrap();
        let (after, _) = apply(&img, 12, 0o751, &owner(), &[0], false);
        assert_eq!(mode(&after, 12), 0o100751);
        assert_eq!(
            attribute(&after, 12, 2, b""),
            Some(expected.as_slice().to_vec())
        );
        assert_eq!(attribute(&after, 12, 1, b"note"), Some(b"before7".to_vec()));
        assert_eq!(attribute(&after, 12, 1, b"large"), Some(vec![0x59; 512]));
        let acl = core::acl::parse(expected.as_slice()).unwrap();
        assert_eq!(acl.entry(1).unwrap().id, 1234);
        assert_eq!(acl.entry(1).unwrap().permissions, 2);
        assert_eq!(acl.entry(2).unwrap().permissions, 0);
        linux("acl-chmod-preserve-result", &after);

        let access = wire(&[(1, 7, 0), (2, 6, 1234), (4, 5, 0), (16, 5, 0), (32, 1, 0)]);
        let default = wire(&[(1, 7, 0), (2, 7, 4567), (4, 7, 0), (16, 7, 0), (32, 7, 0)]);
        let directory = set_acl(&after, 2, Kind::Access, &access);
        let directory = set_acl(&directory, 2, Kind::Default, &default);
        let old_default = attribute(&directory, 2, 3, b"").unwrap();
        let old_payload = attribute(&directory, 12, 2, b"").unwrap();
        let (changed, _) = apply(&directory, 2, 0o1700, &owner(), &[0], false);
        assert_eq!(mode(&changed, 2), 0o041700);
        assert_eq!(attribute(&changed, 2, 3, b""), Some(old_default));
        assert_eq!(attribute(&changed, 12, 2, b""), Some(old_payload));
        linux("acl-chmod-directory-result", &changed);
    }

    #[test]
    fn chmod_folds_a_basic_access_acl_but_retains_a_mask_only_access_acl() {
        let path = "build/acl-chmod-basic.img";
        let acl_path = "build/acl-chmod-basic.bin";
        let raw = wire(&[(1, 6, 0), (4, 2, 0), (32, 0, 0)]);
        std::fs::write(path, image()).unwrap();
        std::fs::write(acl_path, raw).unwrap();
        let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
        for request in [
            "feature ext_attr".to_string(),
            format!("ea_set -f {acl_path} /payload system.posix_acl_access"),
            "sif /payload mode 0100620".to_string(),
        ] {
            command(&debugfs, &["-w", "-R", &request, path], false);
        }
        let img = std::fs::read(path).unwrap();
        assert!(attribute(&img, 12, 2, b"").is_some());
        let (folded, _) = apply(&img, 12, 0o640, &owner(), &[0], false);
        assert_eq!(mode(&folded, 12), 0o100640);
        assert_eq!(attribute(&folded, 12, 2, b""), None);
        linux("acl-chmod-basic-result", &folded);
        let masked = wire(&[(1, 6, 0), (4, 7, 0), (16, 2, 0), (32, 0, 0)]);
        let img = set_acl(&folded, 12, Kind::Access, &masked);
        let (after, _) = apply(&img, 12, 0, &owner(), &[0], false);
        assert_eq!(mode(&after, 12), 0o100000);
        let raw = attribute(&after, 12, 2, b"").expect("MASK alone is extended");
        let acl = core::acl::parse(&raw).unwrap();
        assert_eq!(acl.entry(1).unwrap().permissions, 7);
        assert_eq!(acl.entry(2).unwrap().permissions, 0);
        linux("acl-chmod-mask-only-result", &after);
        let _ = std::fs::remove_file(path);
        let _ = std::fs::remove_file(acl_path);
    }

    #[test]
    fn chmod_owner_authority_is_distinct_from_acl_write_access_and_fsetid() {
        let mut img = fixture("acl-chmod-authority", false);
        assert!(named_allowed(&img, 2));
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        let named = Credentials {
            fsuid: 1234,
            fowner: false,
            fsetid: false,
        };
        assert!(chmod::authorize(&node, &named, &[]).is_none());
        let (_, group, seed) = metadata(&img);
        let at = group.inode_table as usize * 4096 + 11 * 256;
        img[at + 2..at + 4].copy_from_slice(&1000u16.to_le_bytes());
        seal_inode_image(&mut img, group.inode_table, 12, seed);
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        assert!(chmod::authorize(&node, &owner(), &[]).is_none());
        assert!(
            chmod::authorize(
                &node,
                &Credentials {
                    fsetid: true,
                    ..owner()
                },
                &[]
            )
            .is_none()
        );
        let (after, _) = apply(
            &img,
            12,
            0o2640,
            &Credentials {
                fowner: true,
                ..owner()
            },
            &[],
            false,
        );
        assert_eq!(
            mode(&after, 12),
            0o100640,
            "FOWNER alone does not preserve requested SGID"
        );
        assert_eq!(
            core::bytes::read_le16(inode_bytes(&after, group.inode_table, 12), 2),
            Some(1000)
        );
        linux("acl-chmod-authority-result", &after);
    }

    #[test]
    fn chmod_rejects_outside_mode_bits_readonly_sources_and_updates_ctime_for_unchanged_modes() {
        let img = fixture("acl-chmod-invalid", false);
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        for requested in [0o10000, 0o100640, u16::MAX] {
            let grant = chmod::authorize(&node, &owner(), &[0]).unwrap();
            assert!(chmod::prepare(grant, requested, 1, 0).is_err());
        }
        let grant = chmod::authorize(&node, &owner(), &[0]).unwrap();
        assert!(matches!(
            chmod::prepare(grant, mode(&img, 12) & 0o7777, 1, 0),
            Ok(Some(_))
        ));
        let (same, _) = apply(&img, 12, mode(&img, 12) & 0o7777, &owner(), &[0], false);
        assert_eq!(mode(&same, 12), mode(&img, 12));
        let (_, group, _) = metadata(&same);
        let before = inode_bytes(&img, group.inode_table, 12);
        let after = inode_bytes(&same, group.inode_table, 12);
        assert_ne!(
            core::inode_time_fields::get_time(before, core::inode_time_fields::Field::Ctime)
                .unwrap()
                .seconds,
            core::inode_time_fields::get_time(after, core::inode_time_fields::Field::Ctime)
                .unwrap()
                .seconds
        );
        assert_eq!(le32(after, 36), le32(before, 36) + 1);
        let mut readonly = img.clone();
        let flags = le32(&readonly, 1124) | 0x1000;
        readonly[1124..1128].copy_from_slice(&flags.to_le_bytes());
        let checksum = core::crc::crc32c(0xffffffff, &readonly[1024..2044]);
        readonly[2044..2048].copy_from_slice(&checksum.to_le_bytes());
        let volume = allocation::parse(Snapshot::from_bytes(&readonly)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        let grant = chmod::authorize(&node, &owner(), &[0]).unwrap();
        assert!(chmod::prepare(grant, 0o620, 1, 0).is_err());
        let mut sgid = img.clone();
        set_mode(&mut sgid, 12, 0o102620);
        let (cleared, _) = apply(&sgid, 12, 0o2620, &owner(), &[], false);
        assert_eq!(mode(&cleared, 12), 0o100620);
    }

    #[test]
    fn every_chmod_writer_cut_recovers_mode_acl_rights_and_storage_together() {
        let img = fixture("acl-chmod-crash", true);
        let old = attribute(&img, 12, 2, b"").unwrap();
        let before = core::acl::parse(&old).unwrap();
        let expected = acl_transform::chmod(&before, 0o100640)
            .unwrap()
            .as_slice()
            .to_vec();
        let free = le32(&img, 1036);
        let (after, cuts) = apply(&img, 12, 0o640, &owner(), &[0], true);
        assert!(!cuts.is_empty());
        assert_eq!(mode(&after, 12), 0o100640);
        assert_eq!(attribute(&after, 12, 2, b""), Some(expected.clone()));
        let mut committed = None;
        for (done, cut) in cuts {
            if done && committed.is_none() {
                committed = Some(cut.clone());
            }
            let recovered = recover(cut);
            assert_eq!(mode(&recovered, 12), if done { 0o100640 } else { 0o100620 });
            assert_eq!(
                attribute(&recovered, 12, 2, b""),
                Some(if done { expected.clone() } else { old.clone() })
            );
            assert_eq!(
                attribute(&recovered, 12, 1, b"note"),
                Some(b"before7".to_vec())
            );
            assert_eq!(
                attribute(&recovered, 12, 1, b"large"),
                Some(vec![0x59; 512])
            );
            assert_eq!(named_allowed(&recovered, 2), !done);
            assert_eq!(le32(&recovered, 1036), free);
        }
        let linux = linux("acl-chmod-crash-linux", &committed.unwrap());
        assert_eq!(mode(&linux, 12), 0o100640);
        assert_eq!(attribute(&linux, 12, 2, b""), Some(expected));
    }
    #[test]
    fn unchanged_acl_chmod_retains_shared_storage_and_updates_only_the_target_inode() {
        let img = super::xattr_lifecycle_updates::shared("acl-chmod-retained-shared");
        let (_, group, _) = metadata(&img);
        let old = le32(inode_bytes(&img, group.inode_table, 12), 104);
        let peer = inode_bytes(&img, group.inode_table, 13).to_vec();
        let block = img[old as usize * 4096..(old as usize + 1) * 4096].to_vec();
        assert_eq!(le32(&block, 4), 2);
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let node = allocated_inode::get(&volume, 12).unwrap();
        let attributes = xattr_inode::inspect(volume.index(), 12).unwrap();
        let (body, external) = attributes.source_tables();
        let canonical = (
            body.map(|t| core::xattr_canonical::check(t, false)),
            external.map(|t| core::xattr_canonical::check(t, true)),
        );
        // Linux permits a zero block sharing-hash hint. A retained block must
        // not need rebuilding merely to normalize this optional hint.
        assert_eq!(le32(&block, 12), 0);
        assert_eq!(canonical, (Some(true), Some(false)));
        let grant = chmod::authorize(&node, &owner(), &[0]).unwrap();
        let candidate = match chmod::prepare(grant, 0o4620, 123456789, 0) {
            Ok(Some(candidate)) => candidate,
            Err(chmod::Error::Storage(core::xattr_transaction::Error::Admission)) => {
                panic!("retained storage admission, input canonical={canonical:?}")
            }
            _ => panic!("retained shared storage, input canonical={canonical:?}"),
        };
        assert_eq!(
            candidate.patches().len(),
            1,
            "no allocator or shared block write"
        );
        assert_ne!(candidate.patches().at(0).unwrap().block(), old);
        let (after, cuts) = drive(&img, candidate.begin().unwrap(), true);
        assert_eq!(mode(&after, 12), 0o104620);
        assert_eq!(inode_bytes(&after, group.inode_table, 13), peer);
        assert_eq!(
            &after[old as usize * 4096..(old as usize + 1) * 4096],
            block
        );
        assert_eq!(le32(&after, 1036), le32(&img, 1036));
        for (committed, cut) in cuts {
            let recovered = recover(cut);
            assert_eq!(
                mode(&recovered, 12),
                if committed { 0o104620 } else { 0o100620 }
            );
            assert_eq!(inode_bytes(&recovered, group.inode_table, 13), peer);
            assert_eq!(
                &recovered[old as usize * 4096..(old as usize + 1) * 4096],
                block
            );
        }
        linux("acl-chmod-retained-shared-result", &after);
    }
}

// Native tests for the source-bound creation/inheritance planner. The planner
// grants no create/write authority and these tests do not claim child creation.
mod acl_inheritance_plans {
    use core::{acl, acl_inherit, acl_xattr, allocated_inode, allocation, snapshot::Snapshot};

    use super::{inline_xattr_updates::command, *};

    fn wire(entries: &[(u16, u16, u32)]) -> Vec<u8> {
        let mut raw = 2u32.to_le_bytes().to_vec();
        for (tag, permissions, id) in entries {
            raw.extend(tag.to_le_bytes());
            raw.extend(permissions.to_le_bytes());
            raw.extend(id.to_le_bytes());
        }
        raw
    }
    fn fixture(prefix: &str, raw: &[u8]) -> Vec<u8> {
        let path = format!("build/{prefix}.img");
        let acl_path = format!("build/{prefix}-default.bin");
        std::fs::write(&path, image()).unwrap();
        std::fs::write(&acl_path, raw).unwrap();
        let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
        command(&debugfs, &["-w", "-R", "feature ext_attr", &path], false);
        command(
            &debugfs,
            &[
                "-w",
                "-R",
                &format!("ea_set -f {acl_path} / system.posix_acl_default"),
                &path,
            ],
            false,
        );
        let img = std::fs::read(&path).unwrap();
        let _ = std::fs::remove_file(path);
        let _ = std::fs::remove_file(acl_path);
        assert!(core::image_validation::inspect(Snapshot::from_bytes(&img)).is_some());
        img
    }

    #[test]
    fn a_parent_without_a_default_acl_applies_umask_and_supplies_no_child_acls() {
        let img = image();
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let parent = allocated_inode::get(&volume, 2).unwrap();
        for (requested, umask, expected) in [
            (0o106777, 0o022, 0o106755),
            (0o042777, 0o777, 0o042000),
            (0o100000, 0, 0o100000),
        ] {
            let plan = acl_inherit::prepare(&parent, requested, umask).unwrap();
            assert_eq!(plan.mode(), expected);
            assert!(plan.access().is_none());
            assert!(plan.default().is_none());
        }
    }

    #[test]
    fn inherited_access_uses_the_default_acl_instead_of_umask_and_preserves_named_ids() {
        let wire = wire(&[(1, 6, 0), (2, 7, 1234), (4, 3, 0), (16, 5, 0), (32, 2, 0)]);
        let img = fixture("acl-inherit-extended", &wire);
        let original = img.clone();
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let parent = allocated_inode::get(&volume, 2).unwrap();
        let plan = acl_inherit::prepare(&parent, 0o100777, 0o777).unwrap();
        assert_eq!(plan.mode(), 0o100652);
        assert!(
            plan.default().is_none(),
            "regular files do not get a default ACL"
        );
        let access = acl::parse(plan.access().unwrap()).unwrap();
        assert_eq!(access.entry(0).unwrap().permissions, 6);
        assert_eq!(access.entry(1).unwrap().id, 1234);
        assert_eq!(access.entry(1).unwrap().permissions, 7);
        assert_eq!(access.entry(2).unwrap().permissions, 3);
        assert_eq!(access.entry(3).unwrap().permissions, 5);
        assert_eq!(access.entry(4).unwrap().permissions, 2);
        assert_eq!(img, original, "planning must not change parent storage");
    }

    #[test]
    fn a_child_directory_keeps_the_unrestricted_original_default_and_gets_a_masked_access_clone() {
        let wire = wire(&[(1, 6, 0), (2, 7, 1234), (4, 3, 0), (16, 5, 0), (32, 2, 0)]);
        let img = fixture("acl-inherit-directory", &wire);
        let disk = acl_xattr::decode(&wire).unwrap().as_slice().to_vec();
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let parent = allocated_inode::get(&volume, 2).unwrap();
        let plan = acl_inherit::prepare(&parent, 0o042770, 0o777).unwrap();
        assert_eq!(plan.mode(), 0o042650);
        assert_eq!(plan.default().unwrap(), disk);
        let access = acl::parse(plan.access().unwrap()).unwrap();
        let default = acl::parse(plan.default().unwrap()).unwrap();
        assert_eq!(access.entry(4).unwrap().permissions, 0);
        assert_eq!(default.entry(4).unwrap().permissions, 2);
        assert_eq!(default.entry(1).unwrap().id, 1234);
        assert_eq!(default.entry(1).unwrap().permissions, 7);
    }

    #[test]
    fn basic_default_acls_fold_the_child_access_into_mode_but_remain_directory_defaults() {
        let wire = wire(&[(1, 6, 0), (4, 3, 0), (32, 2, 0)]);
        let img = fixture("acl-inherit-basic", &wire);
        let disk = acl_xattr::decode(&wire).unwrap().as_slice().to_vec();
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let parent = allocated_inode::get(&volume, 2).unwrap();
        let file = acl_inherit::prepare(&parent, 0o100777, 0o777).unwrap();
        assert_eq!(file.mode(), 0o100632);
        assert!(file.access().is_none());
        assert!(file.default().is_none());
        let directory = acl_inherit::prepare(&parent, 0o040777, 0o777).unwrap();
        assert_eq!(directory.mode(), 0o040632);
        assert!(directory.access().is_none());
        assert_eq!(directory.default().unwrap(), disk);
    }

    #[test]
    fn mask_only_defaults_remain_extended_at_zero_mode_and_symlinks_skip_acl_and_umask() {
        let wire = wire(&[(1, 7, 0), (4, 7, 0), (16, 6, 0), (32, 7, 0)]);
        let img = fixture("acl-inherit-mask-only", &wire);
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let parent = allocated_inode::get(&volume, 2).unwrap();
        let file = acl_inherit::prepare(&parent, 0o100000, 0).unwrap();
        assert_eq!(file.mode(), 0o100000);
        let access = acl::parse(file.access().unwrap()).unwrap();
        assert_eq!(access.entry(1).unwrap().permissions, 7);
        assert_eq!(access.entry(2).unwrap().permissions, 0);
        let link = acl_inherit::prepare(&parent, 0o120777, 0o777).unwrap();
        assert_eq!(link.mode(), 0o120777);
        assert!(link.access().is_none());
        assert!(link.default().is_none());
        let no_default = image();
        let volume = allocation::parse(Snapshot::from_bytes(&no_default)).unwrap();
        let parent = allocated_inode::get(&volume, 2).unwrap();
        let link = acl_inherit::prepare(&parent, 0o120777, 0o777).unwrap();
        assert_eq!(link.mode(), 0o120777);
    }

    #[test]
    fn inheritance_rejects_a_nondirectory_parent_and_a_missing_child_file_type() {
        let img = image();
        let volume = allocation::parse(Snapshot::from_bytes(&img)).unwrap();
        let file = allocated_inode::get(&volume, 12).unwrap();
        assert!(acl_inherit::prepare(&file, 0o100644, 0o022).is_none());
        let parent = allocated_inode::get(&volume, 2).unwrap();
        assert!(acl_inherit::prepare(&parent, 0o777, 0o022).is_none());
    }
}
// Native regression tests for the reverse compact-ext4 -> Linux UAPI codec.
// Append to proofs/ext4/tests/compat.rs after acl_xattr::report is exported.
mod acl_xattr_reporting {
    use core::{acl, acl_xattr};

    fn wire(entries: &[(u16, u16, u32)]) -> Vec<u8> {
        let mut raw = 2u32.to_le_bytes().to_vec();
        for (tag, permissions, id) in entries {
            raw.extend(tag.to_le_bytes());
            raw.extend(permissions.to_le_bytes());
            raw.extend(id.to_le_bytes());
        }
        raw
    }

    #[test]
    fn reporting_preserves_named_ids_and_normalizes_every_short_entry_id() {
        let input = wire(&[
            (1, 7, 100),
            (2, 0, 0),
            (2, 5, u32::MAX - 1),
            (4, 3, 200),
            (8, 6, 0),
            (8, 0, u32::MAX - 1),
            (16, 5, 300),
            (32, 1, 400),
        ]);
        let compact = acl_xattr::decode(&input).unwrap();
        let parsed = compact.parsed().unwrap();
        let reported = acl_xattr::report(&parsed).unwrap();
        assert_eq!(
            reported,
            wire(&[
                (1, 7, u32::MAX),
                (2, 0, 0),
                (2, 5, u32::MAX - 1),
                (4, 3, u32::MAX),
                (8, 6, 0),
                (8, 0, u32::MAX - 1),
                (16, 5, u32::MAX),
                (32, 1, u32::MAX),
            ])
        );
        let roundtrip = acl_xattr::decode(&reported).unwrap();
        assert_eq!(roundtrip.as_slice(), compact.as_slice());
        let reported_again = acl_xattr::report(&roundtrip.parsed().unwrap()).unwrap();
        assert_eq!(reported_again, reported);
    }

    #[test]
    fn basic_and_mask_only_acls_roundtrip_without_adding_or_removing_entries() {
        for entries in [
            vec![(1, 6, 0), (4, 0, 1), (32, 0, 2)],
            vec![(1, 0, 0), (4, 7, 1), (16, 0, 2), (32, 7, 3)],
        ] {
            let compact = acl_xattr::decode(&wire(&entries)).unwrap();
            let reported = acl_xattr::report(&compact.parsed().unwrap()).unwrap();
            assert_eq!(reported.len(), 4 + entries.len() * 8);
            for (i, (tag, permissions, _)) in entries.iter().enumerate() {
                let at = 4 + i * 8;
                assert_eq!(&reported[at..at + 2], &tag.to_le_bytes());
                assert_eq!(&reported[at + 2..at + 4], &permissions.to_le_bytes());
                assert_eq!(&reported[at + 4..at + 8], &u32::MAX.to_le_bytes());
            }
            assert_eq!(
                acl_xattr::decode(&reported).unwrap().as_slice(),
                compact.as_slice()
            );
        }
    }

    fn compact_with_named_users(named: u32) -> Vec<u8> {
        let mut raw = 1u32.to_le_bytes().to_vec();
        raw.extend(1u16.to_le_bytes());
        raw.extend(7u16.to_le_bytes());
        for id in 0..named {
            raw.extend(2u16.to_le_bytes());
            raw.extend(((id % 8) as u16).to_le_bytes());
            raw.extend(id.to_le_bytes());
        }
        for (tag, permissions) in [(4u16, 5u16), (16, 7), (32, 1)] {
            raw.extend(tag.to_le_bytes());
            raw.extend(permissions.to_le_bytes());
        }
        raw
    }

    #[test]
    fn reporting_accepts_8191_entries_and_rejects_the_next_valid_compact_acl() {
        let raw = compact_with_named_users(8187);
        assert_eq!(raw.len(), 65_516);
        let parsed = acl::parse(&raw).unwrap();
        assert_eq!(parsed.count(), 8191);
        let reported = acl_xattr::report(&parsed).unwrap();
        assert_eq!(reported.len(), 65_532);
        assert_eq!(&reported[..4], &2u32.to_le_bytes());
        let roundtrip = acl_xattr::decode(&reported).unwrap();
        assert_eq!(roundtrip.as_slice(), raw);
        assert_eq!(roundtrip.parsed().unwrap().entry(1).unwrap().id, 0);
        assert_eq!(roundtrip.parsed().unwrap().entry(8187).unwrap().id, 8186);

        let too_many = compact_with_named_users(8188);
        assert_eq!(too_many.len(), 65_524);
        assert!(too_many.len() <= 65_536);
        let parsed = acl::parse(&too_many).unwrap();
        assert_eq!(parsed.count(), 8192);
        assert!(
            acl_xattr::report(&parsed).is_none(),
            "expanded UAPI exceeds 64 KiB"
        );
    }
}

// Native EA_INODE fixtures and regression tests for proofs/ext4/tests/compat.rs.
// Isolated source-bound readers do not grant whole-filesystem admission or I/O.
mod ea_inode_values {
    use core::{
        ea_inode::{self, Status},
        ea_source, ea_value,
        snapshot::Snapshot,
    };

    use super::{inline_xattr_updates::command, *};

    pub(super) struct Fixture {
        pub(super) bytes: Vec<u8>,
        pub(super) value: Vec<u8>,
        pub(super) table: u32,
        pub(super) inodes: u32,
        pub(super) seed: u32,
        pub(super) external: u32,
    }
    pub(super) fn parameters(img: &[u8]) -> (u32, u32, u32) {
        (
            le32(img, 4104),
            le32(img, 1024),
            core::superblock::metadata_checksum_seed(&img[1024..2048]).unwrap(),
        )
    }
    pub(super) fn offset(table: u32, number: u32) -> usize {
        table as usize * 4096 + (number as usize - 1) * 256
    }
    pub(super) fn seal_raw(raw: &mut [u8], number: u32, seed: u32) {
        let hash = core::inode::calculated_checksum(raw, number, seed).unwrap();
        raw[124..126].copy_from_slice(&(hash as u16).to_le_bytes());
        raw[130..132].copy_from_slice(&((hash >> 16) as u16).to_le_bytes());
    }
    pub(super) fn entry_hash(name: &[u8], value_hash: u32) -> u32 {
        let name_hash = name
            .iter()
            .fold(0u32, |hash, byte| hash.rotate_left(5) ^ u32::from(*byte));
        name_hash.rotate_left(16) ^ value_hash
    }
    pub(super) fn entry(
        raw: &mut [u8],
        at: usize,
        name: &[u8],
        size: u32,
        value_hash: u32,
    ) -> usize {
        raw[at] = name.len() as u8;
        raw[at + 1] = 1;
        raw[at + 2..at + 4].copy_from_slice(&0u16.to_le_bytes());
        raw[at + 4..at + 8].copy_from_slice(&14u32.to_le_bytes());
        raw[at + 8..at + 12].copy_from_slice(&size.to_le_bytes());
        raw[at + 12..at + 16].copy_from_slice(&entry_hash(name, value_hash).to_le_bytes());
        raw[at + 16..at + 16 + name.len()].copy_from_slice(name);
        at + 16 + (name.len() + 3) / 4 * 4
    }
    pub(super) fn mappings(img: &[u8], table: u32, size: usize) -> Vec<u32> {
        let at = offset(table, 14);
        let raw = &img[at + 40..at + 100];
        assert_eq!(core::bytes::read_le16(raw, 6), Some(0));
        let mut result = vec![0; (size + 4095) / 4096];
        for i in 0..core::bytes::read_le16(raw, 2).unwrap() as usize {
            let e = core::extent::parse(raw, 12 + i * 12, le32(img, 1028)).unwrap();
            assert!(e.initialized);
            for j in 0..e.length {
                let logical = (e.logical + j) as usize;
                assert!(logical < result.len());
                assert_eq!(result[logical], 0);
                result[logical] = e.physical + j;
            }
        }
        assert!(result.iter().all(|physical| *physical != 0));
        result
    }
    pub(super) fn fixture(prefix: &str, size: usize) -> Fixture {
        fixture_with_features(prefix, size, false, false)
    }
    pub(super) fn fixture_with_features(
        prefix: &str,
        size: usize,
        wide: bool,
        stored_seed: bool,
    ) -> Fixture {
        assert!((4096..=65536).contains(&size));
        let features = format!(
            "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum,ea_inode{}{}",
            if wide { ",64bit" } else { "" },
            if stored_seed {
                ",metadata_csum_seed"
            } else {
                ""
            },
        );
        let path = format!("build/{prefix}.img");
        let value_path = format!("build/{prefix}-value.bin");
        let empty_path = format!("build/{prefix}-empty.bin");
        let commands_path = format!("build/{prefix}-commands.txt");
        let extracted_path = format!("build/{prefix}-extracted.bin");
        let value: Vec<u8> = (0..size)
            .map(|i| (i.wrapping_mul(73) + i / 251) as u8)
            .collect();
        std::fs::write(&value_path, &value[..4096]).unwrap();
        std::fs::write(&empty_path, []).unwrap();
        let mke2fs = std::env::var("MKE2FS_BIN").unwrap_or_else(|_| "mke2fs".into());
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
                &path,
                "8192",
            ],
            false,
        );
        let mut requests = vec![
            "feature ext_attr".to_string(),
            "ea_set / user.small local".to_string(),
            format!("write {empty_path} /first"),
            format!("write {empty_path} /second"),
            format!("ea_set -f {value_path} /first user.big"),
            format!("ea_set /first user.filler {}", "s".repeat(200)),
        ];
        for logical in 1..(size + 4095) / 4096 {
            requests.push(format!("bmap -a <14> {logical}"));
        }
        requests.push("quit".into());
        std::fs::write(&commands_path, requests.join("\n") + "\n").unwrap();
        let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
        command(&debugfs, &["-w", "-f", &commands_path, &path], false);
        let mut img = std::fs::read(&path).unwrap();
        let (table, inodes, seed) = parameters(&img);
        let first = offset(table, 12);
        let second = offset(table, 13);
        let ea = offset(table, 14);
        assert_eq!(le32(&img, first + 168), 14);
        let external = le32(&img, first + 104);
        assert!(external != 0);
        let physical = mappings(&img, table, size);
        for (i, block) in physical.iter().enumerate() {
            let part = &value[i * 4096..value.len().min((i + 1) * 4096)];
            let target = &mut img[*block as usize * 4096..(*block as usize + 1) * 4096];
            target.fill(0);
            target[..part.len()].copy_from_slice(part);
        }
        let value_hash = core::crc::crc32c(seed, &value);
        img[ea + 4..ea + 8].copy_from_slice(&(size as u32).to_le_bytes());
        img[ea + 8..ea + 12].copy_from_slice(&value_hash.to_le_bytes());
        img[ea + 12..ea + 16].fill(0);
        img[ea + 36..ea + 40].copy_from_slice(&3u32.to_le_bytes());
        seal_raw(&mut img[ea..ea + 256], 14, seed);

        // One physical external entry is shared by two parents. The EA inode
        // has three references: two distinct inline entries plus this entry.
        img[first + 160..first + 256].fill(0);
        img[first + 160..first + 164].copy_from_slice(&core::xattr::MAGIC.to_le_bytes());
        let next = entry(&mut img, first + 164, b"big", size as u32, value_hash);
        entry(&mut img, next, b"alias", size as u32, value_hash);
        img[second + 160..second + 256].fill(0);
        img[second + 104..second + 108].copy_from_slice(&external.to_le_bytes());
        let block = &mut img[external as usize * 4096..(external as usize + 1) * 4096];
        block.fill(0);
        block[..4].copy_from_slice(&core::xattr::MAGIC.to_le_bytes());
        block[4..8].copy_from_slice(&2u32.to_le_bytes());
        block[8..12].copy_from_slice(&1u32.to_le_bytes());
        block[12..16].copy_from_slice(&entry_hash(b"shared", value_hash).to_le_bytes());
        entry(block, 32, b"shared", size as u32, value_hash);
        let checksum = core::xattr::checksum(block, external as u64, seed).unwrap();
        block[16..20].copy_from_slice(&checksum.to_le_bytes());
        let value_blocks = ((size + 4095) / 4096) as u32;
        img[first + 28..first + 32].copy_from_slice(&(8 * (1 + 3 * value_blocks)).to_le_bytes());
        img[second + 28..second + 32].copy_from_slice(&(8 * (1 + value_blocks)).to_le_bytes());
        seal_raw(&mut img[first..first + 256], 12, seed);
        seal_raw(&mut img[second..second + 256], 13, seed);
        std::fs::write(&path, &img).unwrap();
        let fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        command(&fsck, &["-fn", &path], false);
        command(
            &debugfs,
            &[
                "-R",
                &format!("ea_get -f {extracted_path} /first user.big"),
                &path,
            ],
            false,
        );
        assert_eq!(std::fs::read(&extracted_path).unwrap(), value);
        command(
            &debugfs,
            &[
                "-R",
                &format!("ea_get -f {extracted_path} /second user.shared"),
                &path,
            ],
            false,
        );
        assert_eq!(std::fs::read(&extracted_path).unwrap(), value);
        for file in [
            &path,
            &value_path,
            &empty_path,
            &commands_path,
            &extracted_path,
        ] {
            let _ = std::fs::remove_file(file);
        }
        Fixture {
            bytes: img,
            value,
            table,
            inodes,
            seed,
            external,
        }
    }

    #[test]
    fn linux_ea_inode_metadata_preserves_three_physical_references_with_a_shared_block() {
        let fixture = fixture("ea-inode-physical-refs", 4096);
        let raw = inode_bytes(&fixture.bytes, fixture.table, 14);
        let info = ea_inode::parse(raw, 14, fixture.inodes, fixture.seed, Status::Live).unwrap();
        assert_eq!(info.size, 4096);
        assert_eq!(info.refs, 3);
        assert_eq!(info.hash, core::crc::crc32c(fixture.seed, &fixture.value));
        assert_eq!(
            le32(&fixture.bytes, fixture.external as usize * 4096 + 4),
            2
        );
        assert_eq!(le32(inode_bytes(&fixture.bytes, fixture.table, 12), 28), 32);
        assert_eq!(le32(inode_bytes(&fixture.bytes, fixture.table, 13), 28), 16);
        assert!(core::allocation::parse(Snapshot::from_bytes(&fixture.bytes)).is_none());
        let snapshot = Snapshot::from_bytes(&fixture.bytes);
        let header = ea_source::parse(&snapshot).unwrap();
        let allocated = header.get(14).unwrap();
        assert_eq!(allocated.raw(), raw);
        assert_eq!(allocated.number(), 14);
        assert_eq!(allocated.position(), offset(fixture.table, 14) as u64);
    }

    #[test]
    fn ea_reference_codec_handles_zero_maximum_and_raw_timestamp_high_bits_without_mode_changes() {
        let fixture = fixture("ea-inode-ref-boundaries", 4096);
        let raw = inode_bytes(&fixture.bytes, fixture.table, 14);
        let mutable = |i: usize| {
            (12..16).contains(&i)
                || (26..28).contains(&i)
                || (36..40).contains(&i)
                || (124..126).contains(&i)
                || (130..136).contains(&i)
        };
        for refs in [0, 1, 0x8000_0000_0000_0000, u64::MAX] {
            let changed =
                ea_inode::set_refcount(raw, 14, fixture.inodes, fixture.seed, Status::Live, refs)
                    .unwrap();
            let status = if refs == 0 {
                Status::Unlinked
            } else {
                Status::Live
            };
            let parsed =
                ea_inode::parse(&changed, 14, fixture.inodes, fixture.seed, status).unwrap();
            assert_eq!(parsed.refs, refs);
            assert_eq!(parsed.hash, le32(raw, 8));
            assert_eq!(parsed.mode, core::bytes::read_le16(raw, 0).unwrap());
            assert_eq!(
                le32(&changed, 132),
                if refs >> 32 >= 0x8000_0000 { 1 } else { 0 }
            );
            for i in 0..256 {
                if !mutable(i) {
                    assert_eq!(changed[i], raw[i]);
                }
            }
            let restored =
                ea_inode::set_refcount(&changed, 14, fixture.inodes, fixture.seed, status, 3)
                    .unwrap();
            assert_eq!(
                ea_inode::parse(&restored, 14, fixture.inodes, fixture.seed, Status::Live)
                    .unwrap()
                    .refs,
                3
            );
        }
        for hash in [0, 0x8000_0000, u32::MAX] {
            for extra in [0, 1, u32::MAX] {
                let mut altered = raw.to_vec();
                altered[8..12].copy_from_slice(&hash.to_le_bytes());
                altered[140..144].copy_from_slice(&extra.to_le_bytes());
                seal_raw(&mut altered, 14, fixture.seed);
                assert_eq!(
                    ea_inode::parse(&altered, 14, fixture.inodes, fixture.seed, Status::Live)
                        .unwrap()
                        .hash,
                    hash
                );
            }
        }
    }

    #[test]
    fn ea_metadata_rejects_wrong_flags_nested_attributes_checksums_and_inconsistent_liveness() {
        let fixture = fixture("ea-inode-invalid-metadata", 4096);
        let raw = inode_bytes(&fixture.bytes, fixture.table, 14);
        for (at, replacement) in [
            (0usize, 0x4000u32),
            (4, 0),
            (4, ea_inode::MAX_VALUE + 1),
            (20, 1),
            (26, 0),
            (32, 0x80000),
            (104, fixture.external),
            (108, 1),
            (116, 1),
            (118, 1),
            (128, 0),
            (152, 1),
            (160, core::xattr::MAGIC),
        ] {
            let mut altered = raw.to_vec();
            if [0, 26, 116, 118, 128].contains(&at) {
                altered[at..at + 2].copy_from_slice(&(replacement as u16).to_le_bytes());
            } else {
                altered[at..at + 4].copy_from_slice(&replacement.to_le_bytes());
            }
            seal_raw(&mut altered, 14, fixture.seed);
            assert!(
                ea_inode::parse(&altered, 14, fixture.inodes, fixture.seed, Status::Live).is_none(),
                "offset {at}"
            );
        }
        let mut altered = raw.to_vec();
        altered[100] ^= 1;
        assert!(
            ea_inode::parse(&altered, 14, fixture.inodes, fixture.seed, Status::Live).is_none()
        );
        assert!(ea_inode::parse(raw, 12, fixture.inodes, fixture.seed, Status::Live).is_none());
        assert!(ea_inode::parse(raw, 14, fixture.inodes, fixture.seed ^ 1, Status::Live).is_none());
        assert!(ea_inode::parse(raw, 14, fixture.inodes, fixture.seed, Status::Unlinked).is_none());
    }

    #[test]
    fn source_bound_large_ea_reads_preserve_exact_bytes_aliases_and_physical_block_identity() {
        for size in [16_384usize, 16_401, 65_536] {
            let fixture = fixture(&format!("ea-value-large-{size}"), size);
            let snapshot = Snapshot::from_bytes(&fixture.bytes);
            let header = ea_source::parse(&snapshot).unwrap();
            let first = ea_value::inspect(&header, 12, 1, b"big", 8).unwrap();
            let alias = ea_value::inspect(&header, 12, 1, b"alias", 8).unwrap();
            let shared = ea_value::inspect(&header, 12, 1, b"shared", 8).unwrap();
            let peer = ea_value::inspect(&header, 13, 1, b"shared", 8).unwrap();
            assert_eq!(first.as_slice(), fixture.value);
            assert_eq!(first.inode_number(), 14);
            assert!(first.same_bytes(&alias));
            assert!(first.same_bytes(&shared));
            assert!(first.same_bytes(&peer));
            assert_eq!(first.blocks(), alias.blocks());
            assert_eq!(first.blocks(), shared.blocks());
            assert_eq!(first.blocks(), peer.blocks());
            assert_eq!(
                first.blocks(),
                mappings(&fixture.bytes, fixture.table, size)
                    .into_iter()
                    .map(u64::from)
                    .collect::<Vec<_>>()
            );
            assert_eq!(first.blocks().len(), (size + 4095) / 4096);
            assert!(
                core::image_validation::inspect(Snapshot::from_bytes(&fixture.bytes)).is_none()
            );
            assert!(ea_value::inspect(&header, 12, 1, b"missing", 8).is_none());
            assert!(ea_value::inspect(&header, 12, 2, b"big", 8).is_none());
            assert!(ea_value::inspect(&header, 0, 1, b"big", 8).is_none());
            assert!(ea_value::inspect(&header, 14, 1, b"big", 8).is_none());
            assert!(
                ea_value::inspect(&header, 2, 1, b"small", 8).is_none(),
                "local values are not EA inode values"
            );
            assert!(ea_value::inspect(&header, 12, 1, b"big", 0).is_none());
            assert!(ea_value::inspect(&header, 12, 1, b"big", 4097).is_none());
        }
    }

    #[test]
    fn ea_value_rejects_changed_data_hashes_sizes_self_references_and_unallocated_values() {
        let fixture = fixture("ea-value-corrupt-identity", 16_401);
        let first = offset(fixture.table, 12);
        let ea = offset(fixture.table, 14);
        let rejected = |img: &[u8]| {
            let snapshot = Snapshot::from_bytes(img);
            let header = ea_source::parse(&snapshot).unwrap();
            assert!(ea_value::inspect(&header, 12, 1, b"big", 8).is_none());
        };
        for number in [2u32, 12, 15] {
            let mut img = fixture.bytes.clone();
            img[first + 168..first + 172].copy_from_slice(&number.to_le_bytes());
            seal_raw(&mut img[first..first + 256], 12, fixture.seed);
            rejected(&img);
        }
        for (at, replacement) in [
            (4usize, 16_400u32),
            (8, le32(&fixture.bytes, ea + 8) ^ 1),
            (32, 0x80000),
            (104, fixture.external),
        ] {
            let mut img = fixture.bytes.clone();
            img[ea + at..ea + at + 4].copy_from_slice(&replacement.to_le_bytes());
            seal_raw(&mut img[ea..ea + 256], 14, fixture.seed);
            rejected(&img);
        }
        let mut img = fixture.bytes.clone();
        img[first + 176] ^= 1;
        seal_raw(&mut img[first..first + 256], 12, fixture.seed);
        rejected(&img);
        let mut img = fixture.bytes.clone();
        img[first + 172..first + 176].copy_from_slice(&16_400u32.to_le_bytes());
        seal_raw(&mut img[first..first + 256], 12, fixture.seed);
        rejected(&img);
        let mut img = fixture.bytes.clone();
        let physical = mappings(&img, fixture.table, fixture.value.len());
        img[physical[0] as usize * 4096 + 73] ^= 1;
        rejected(&img);
        let mut img = fixture.bytes.clone();
        img[ea + 100] ^= 1;
        rejected(&img);
    }

    #[test]
    fn ea_value_rejects_sparse_unwritten_and_repeated_physical_mappings() {
        let fixture = fixture("ea-value-corrupt-mappings", 16_401);
        let ea = offset(fixture.table, 14);
        assert_eq!(core::bytes::read_le16(&fixture.bytes, ea + 42), Some(2));
        let rejected = |img: &[u8]| {
            let snapshot = Snapshot::from_bytes(img);
            let header = ea_source::parse(&snapshot).unwrap();
            assert!(ea_value::inspect(&header, 12, 1, b"big", 8).is_none());
        };
        let mut img = fixture.bytes.clone();
        img[ea + 64..ea + 68].copy_from_slice(&2u32.to_le_bytes());
        seal_raw(&mut img[ea..ea + 256], 14, fixture.seed);
        rejected(&img);
        let mut img = fixture.bytes.clone();
        img[ea + 56..ea + 58].copy_from_slice(&0x8001u16.to_le_bytes());
        seal_raw(&mut img[ea..ea + 256], 14, fixture.seed);
        rejected(&img);
        // Hold the exact logical bytes and all hashes fixed so this case
        // specifically exercises the prohibition on physical block aliases.
        let bytes = vec![0x5a; fixture.value.len()];
        let mut img = with_value(&fixture, &bytes);
        let original_maps = mappings(&img, fixture.table, bytes.len());
        for physical in &original_maps {
            img[*physical as usize * 4096..(*physical as usize + 1) * 4096].fill(0x5a);
        }
        {
            let snapshot = Snapshot::from_bytes(&img);
            let header = ea_source::parse(&snapshot).unwrap();
            let value = ea_value::inspect(&header, 12, 1, b"big", 8).unwrap();
            assert_eq!(value.as_slice(), bytes);
        }
        // The second original extent is four contiguous value blocks. Point
        // the first extent at its first block too; both logical extents now
        // read only 0x5a, including the former partial block's unused tail.
        let duplicated = le32(&img, ea + 72);
        img[ea + 60..ea + 64].copy_from_slice(&duplicated.to_le_bytes());
        seal_raw(&mut img[ea..ea + 256], 14, fixture.seed);
        let aliased = mappings(&img, fixture.table, bytes.len());
        assert_eq!(aliased[0], aliased[1]);
        let observed: Vec<_> = aliased
            .iter()
            .flat_map(|physical| {
                img[*physical as usize * 4096..(*physical as usize + 1) * 4096]
                    .iter()
                    .copied()
            })
            .take(bytes.len())
            .collect();
        assert_eq!(observed, bytes);
        assert_eq!(
            core::crc::crc32c(fixture.seed, &observed),
            le32(&img, ea + 8)
        );
        assert_eq!(
            le32(&img, offset(fixture.table, 12) + 176),
            entry_hash(b"big", le32(&img, ea + 8))
        );
        assert!(
            ea_inode::parse(
                &img[ea..ea + 256],
                14,
                fixture.inodes,
                fixture.seed,
                Status::Live
            )
            .is_some()
        );
        {
            let snapshot = Snapshot::from_bytes(&img);
            let seed = core::inode::inode_seed(fixture.seed, 14, le32(&img, ea + 100));
            assert!(
                core::extent_tree::audit(
                    &snapshot,
                    (ea + 40) as u64,
                    le32(&img, 1028) as u64,
                    4096,
                    core::extent_node::BlockChecksum::Crc32c(seed),
                    8
                )
                .is_ok()
            );
        }
        rejected(&img);
    }

    fn forge_crc(mut value: Vec<u8>, seed: u32, target: u32) -> Vec<u8> {
        let end = value.len();
        value[end - 4..].fill(0);
        let base = core::crc::crc32c(seed, &value);
        let mut basis = [0u32; 32];
        let mut masks = [0u32; 32];
        for input in 0..32 {
            value[end - 4 + input / 8] ^= 1 << (input % 8);
            let mut delta = core::crc::crc32c(seed, &value) ^ base;
            value[end - 4 + input / 8] ^= 1 << (input % 8);
            let mut combination = 1u32 << input;
            for bit in (0..32).rev() {
                if delta & (1 << bit) != 0 {
                    if basis[bit] == 0 {
                        basis[bit] = delta;
                        masks[bit] = combination;
                        break;
                    }
                    delta ^= basis[bit];
                    combination ^= masks[bit];
                }
            }
        }
        let mut delta = target ^ base;
        let mut patch = 0u32;
        for bit in (0..32).rev() {
            if delta & (1 << bit) != 0 {
                assert_ne!(basis[bit], 0);
                delta ^= basis[bit];
                patch ^= masks[bit];
            }
        }
        assert_eq!(delta, 0);
        value[end - 4..].copy_from_slice(&patch.to_le_bytes());
        assert_eq!(core::crc::crc32c(seed, &value), target);
        value
    }
    pub(super) fn with_value(fixture: &Fixture, value: &[u8]) -> Vec<u8> {
        assert_eq!(value.len(), fixture.value.len());
        let mut img = fixture.bytes.clone();
        for (i, block) in mappings(&img, fixture.table, value.len())
            .iter()
            .enumerate()
        {
            let part = &value[i * 4096..value.len().min((i + 1) * 4096)];
            let raw = &mut img[*block as usize * 4096..(*block as usize + 1) * 4096];
            raw.fill(0);
            raw[..part.len()].copy_from_slice(part);
        }
        let hash = core::crc::crc32c(fixture.seed, value);
        let first = offset(fixture.table, 12);
        let ea = offset(fixture.table, 14);
        img[ea + 8..ea + 12].copy_from_slice(&hash.to_le_bytes());
        seal_raw(&mut img[ea..ea + 256], 14, fixture.seed);
        img[first + 176..first + 180].copy_from_slice(&entry_hash(b"big", hash).to_le_bytes());
        img[first + 196..first + 200].copy_from_slice(&entry_hash(b"alias", hash).to_le_bytes());
        seal_raw(&mut img[first..first + 256], 12, fixture.seed);
        let block =
            &mut img[fixture.external as usize * 4096..(fixture.external as usize + 1) * 4096];
        let entry_hash = entry_hash(b"shared", hash);
        block[12..16].copy_from_slice(&entry_hash.to_le_bytes());
        block[44..48].copy_from_slice(&entry_hash.to_le_bytes());
        let checksum = core::xattr::checksum(block, fixture.external as u64, fixture.seed).unwrap();
        block[16..20].copy_from_slice(&checksum.to_le_bytes());
        img
    }

    #[test]
    fn zero_and_high_bit_ea_hashes_are_values_and_crc_collisions_do_not_imply_equal_bytes() {
        let fixture = fixture("ea-value-hash-boundaries", 4096);
        let original_snapshot = Snapshot::from_bytes(&fixture.bytes);
        let original_header = ea_source::parse(&original_snapshot).unwrap();
        let original = ea_value::inspect(&original_header, 12, 1, b"big", 8).unwrap();
        for target in [0, 0x8000_0000, u32::MAX, entry_hash(b"big", 0)] {
            let value = forge_crc(fixture.value.clone(), fixture.seed, target);
            let img = with_value(&fixture, &value);
            let snapshot = Snapshot::from_bytes(&img);
            let header = ea_source::parse(&snapshot).unwrap();
            let result = ea_value::inspect(&header, 12, 1, b"big", 8).unwrap();
            assert_eq!(result.as_slice(), value);
            assert_eq!(le32(inode_bytes(&img, fixture.table, 14), 8), target);
            if target == entry_hash(b"big", 0) {
                assert_eq!(le32(inode_bytes(&img, fixture.table, 12), 176), 0);
            }
        }
        let mut different = fixture.value.clone();
        different[0] ^= 1;
        let target = core::crc::crc32c(fixture.seed, &fixture.value);
        let different = forge_crc(different, fixture.seed, target);
        assert_ne!(different, fixture.value);
        let img = with_value(&fixture, &different);
        let snapshot = Snapshot::from_bytes(&img);
        let header = ea_source::parse(&snapshot).unwrap();
        let collision = ea_value::inspect(&header, 12, 1, b"big", 8).unwrap();
        assert_eq!(
            core::crc::crc32c(fixture.seed, collision.as_slice()),
            target
        );
        assert!(!original.same_bytes(&collision));
    }

    #[test]
    fn legacy_signed_high_byte_names_are_accepted_only_with_the_exact_value_hash() {
        let fixture = fixture("ea-value-signed-name", 4096);
        let mut img = fixture.bytes.clone();
        let first = offset(fixture.table, 12);
        let name = [0xffu8, b'x'];
        let value_hash = core::crc::crc32c(fixture.seed, &fixture.value);
        img[first + 160..first + 256].fill(0);
        img[first + 160..first + 164].copy_from_slice(&core::xattr::MAGIC.to_le_bytes());
        let at = entry(
            &mut img,
            first + 164,
            b"big",
            fixture.value.len() as u32,
            value_hash,
        );
        entry(&mut img, at, &name, fixture.value.len() as u32, value_hash);
        let signed = name.iter().fold(0u32, |hash, byte| {
            hash.rotate_left(5) ^ (*byte as i8 as i32 as u32)
        });
        let signed = signed.rotate_left(16) ^ value_hash;
        assert_ne!(signed, entry_hash(&name, value_hash));
        img[at + 12..at + 16].copy_from_slice(&signed.to_le_bytes());
        seal_raw(&mut img[first..first + 256], 12, fixture.seed);
        let snapshot = Snapshot::from_bytes(&img);
        let header = ea_source::parse(&snapshot).unwrap();
        let result = ea_value::inspect(&header, 12, 1, &name, 8).unwrap();
        assert_eq!(result.as_slice(), fixture.value);
        let mut bad = img.clone();
        bad[at + 12] ^= 1;
        seal_raw(&mut bad[first..first + 256], 12, fixture.seed);
        let snapshot = Snapshot::from_bytes(&bad);
        let header = ea_source::parse(&snapshot).unwrap();
        assert!(ea_value::inspect(&header, 12, 1, &name, 8).is_none());
    }

    #[test]
    fn modern_ea_inspection_rejects_linux_lustre_backpointers_even_when_hashes_match_the_bytes() {
        let fixture = fixture("ea-value-lustre-backpointer", 4096);
        let first = offset(fixture.table, 12);
        let ea = offset(fixture.table, 14);
        assert_ne!(
            le32(&fixture.bytes, first + 176),
            le32(&fixture.bytes, ea + 8)
        );
        assert_eq!(
            le32(&fixture.bytes, first + 100),
            le32(&fixture.bytes, ea + 100)
        );
        let mut img = fixture.bytes.clone();
        img[ea + 16..ea + 20].copy_from_slice(&12u32.to_le_bytes());
        seal_raw(&mut img[ea..ea + 256], 14, fixture.seed);
        let snapshot = Snapshot::from_bytes(&img);
        let header = ea_source::parse(&snapshot).unwrap();
        assert!(ea_value::inspect(&header, 12, 1, b"big", 8).is_none());
        let peer = ea_value::inspect(&header, 13, 1, b"shared", 8).unwrap();
        assert_eq!(
            peer.as_slice(),
            fixture.value,
            "the legacy backpointer is parent-specific"
        );
        let mut different_generation = img.clone();
        let generation = le32(&different_generation, first + 100).wrapping_add(1);
        different_generation[ea + 100..ea + 104].copy_from_slice(&generation.to_le_bytes());
        seal_raw(&mut different_generation[ea..ea + 256], 14, fixture.seed);
        let snapshot = Snapshot::from_bytes(&different_generation);
        let header = ea_source::parse(&snapshot).unwrap();
        assert_eq!(
            ea_value::inspect(&header, 12, 1, b"big", 8)
                .unwrap()
                .as_slice(),
            fixture.value
        );
    }

    #[test]
    fn ea_source_headers_read_linux_32_and_64_byte_descriptors_with_both_checksum_seed_profiles() {
        for wide in [false, true] {
            for stored_seed in [false, true] {
                let prefix = format!("ea-source-profile-{wide}-{stored_seed}");
                let fixture = fixture_with_features(&prefix, 4096, wide, stored_seed);
                let primary = &fixture.bytes[1024..2048];
                let width = if wide { 64 } else { 32 };
                assert_eq!(core::superblock::descriptor_length(primary), Some(width));
                assert_eq!(le32(primary, 96) & 0x2000 != 0, stored_seed);
                let snapshot = Snapshot::from_bytes(&fixture.bytes);
                let header = ea_source::parse(&snapshot).unwrap();
                assert_eq!(header.descriptor_width(), width);
                assert_eq!(header.parameters().3, fixture.seed);
                let node = header.get(14).unwrap();
                assert_eq!(node.raw(), inode_bytes(&fixture.bytes, fixture.table, 14));
                let value = ea_value::inspect(&header, 12, 1, b"big", 1).unwrap();
                assert_eq!(value.as_slice(), fixture.value);
                assert_eq!(value.blocks().len(), 1);
                assert!(core::allocation::parse(Snapshot::from_bytes(&fixture.bytes)).is_none());
            }
        }
    }
}

mod ea_reference_accounting {
    use core::ea_refs::{self, Error, Kind, Ledger, Location, ParentReference, Reference};

    fn reference(kind: Kind, owner: u64, offset: u32, size: u32) -> Reference {
        Reference {
            location: Location {
                kind,
                owner,
                offset,
            },
            value: 14,
            size,
        }
    }
    fn records() -> [Reference; 3] {
        [
            reference(Kind::Inline, 12, 164, 16_401),
            reference(Kind::Inline, 12, 184, 16_401),
            reference(Kind::External, 2058, 32, 16_401),
        ]
    }
    fn ok(result: Result<Ledger, (Ledger, Error)>) -> Ledger {
        match result {
            Ok(ledger) => ledger,
            Err(_) => panic!("physical EA ledger operation rejected"),
        }
    }
    fn serialized(ledger: &Ledger) -> Vec<(bool, u64, u32, u32, u32)> {
        ledger
            .records()
            .iter()
            .map(|r| {
                (
                    matches!(r.location.kind, Kind::External),
                    r.location.owner,
                    r.location.offset,
                    r.value,
                    r.size,
                )
            })
            .collect()
    }

    #[test]
    fn physical_ea_entries_and_per_parent_quota_charges_use_independent_ledgers() {
        let records = records();
        let ledger = Ledger::from_records(&records).unwrap();
        assert_eq!(ledger.len(), 3);
        assert_eq!(ledger.refs(14), 3);
        assert_eq!(ledger.refs(15), 0);
        let logical = [
            ParentReference {
                parent: 12,
                physical: records[0],
            },
            ParentReference {
                parent: 12,
                physical: records[1],
            },
            ParentReference {
                parent: 12,
                physical: records[2],
            },
            ParentReference {
                parent: 13,
                physical: records[2],
            },
        ];
        let first = ea_refs::quota_usage(&logical, 12, 4096).unwrap();
        let second = ea_refs::quota_usage(&logical, 13, 4096).unwrap();
        assert_eq!((first.ea_inodes, first.bytes), (3, 61_440));
        assert_eq!((second.ea_inodes, second.bytes), (1, 20_480));
        let large_clusters = ea_refs::quota_usage(&logical, 12, 65_536).unwrap();
        assert_eq!(
            (large_clusters.ea_inodes, large_clusters.bytes),
            (3, 196_608)
        );
        let cloned = ok(ledger.clone_external(2058, 9000));
        assert_eq!(cloned.len(), 4);
        assert_eq!(cloned.refs(14), 4, "cloning creates one new physical entry");
        let released = ok(cloned.remove(records[2].location));
        assert_eq!(
            released.refs(14),
            3,
            "destroying a physical entry drops one reference"
        );
        assert_eq!(released.len(), 3);
    }

    #[test]
    fn rejected_physical_edits_return_the_unchanged_ledger_and_reject_conflicting_sizes() {
        let records = records();
        let ledger = Ledger::from_records(&records).unwrap();
        let before = serialized(&ledger);
        let (ledger, error) = match ledger.add(records[0]) {
            Err(failure) => failure,
            Ok(_) => panic!("duplicate location accepted"),
        };
        assert!(matches!(error, Error::DuplicateLocation));
        assert_eq!(serialized(&ledger), before);
        let conflicting = reference(Kind::External, 9000, 32, 4096);
        let (ledger, error) = match ledger.add(conflicting) {
            Err(failure) => failure,
            Ok(_) => panic!("one EA inode admitted with two sizes"),
        };
        assert!(matches!(error, Error::ConflictingSize));
        assert_eq!(serialized(&ledger), before);
        let (ledger, error) = match ledger.clone_external(2058, 2058) {
            Err(failure) => failure,
            Ok(_) => panic!("self-clone accepted"),
        };
        assert!(matches!(error, Error::InvalidBlock));
        assert_eq!(serialized(&ledger), before);
        let missing = Location {
            kind: Kind::External,
            owner: 9000,
            offset: 32,
        };
        let (ledger, error) = match ledger.remove(missing) {
            Err(failure) => failure,
            Ok(_) => panic!("missing physical entry removed"),
        };
        assert!(matches!(error, Error::Missing));
        assert_eq!(serialized(&ledger), before);
        assert!(Ledger::from_records(&[records[0], records[0]]).is_none());
        assert!(Ledger::from_records(&[records[0], conflicting]).is_none());
        let oversized: Vec<_> = (1..=ea_refs::MAX_RECORDS + 1)
            .map(|owner| reference(Kind::External, owner as u64, 32, 16_401))
            .collect();
        assert!(Ledger::from_records(&oversized).is_none());
    }

    #[test]
    fn quota_validation_rejects_duplicate_parent_entries_mismatched_inline_owners_and_zero_units() {
        let records = records();
        let external = ParentReference {
            parent: 12,
            physical: records[2],
        };
        assert!(ea_refs::quota_usage(&[external, external], 12, 4096).is_none());
        let wrong_parent = ParentReference {
            parent: 13,
            physical: records[0],
        };
        assert!(ea_refs::quota_usage(&[wrong_parent], 13, 4096).is_none());
        assert!(ea_refs::quota_usage(&[external], 0, 4096).is_none());
        assert!(ea_refs::quota_usage(&[external], 12, 0).is_none());
        let empty = ea_refs::quota_usage(&[], 12, 4096).unwrap();
        assert_eq!((empty.ea_inodes, empty.bytes), (0, 0));
        for bad in [
            reference(Kind::External, 0, 32, 4096),
            reference(Kind::External, u64::MAX, 32, 4096),
            reference(Kind::External, 12, 31, 4096),
            reference(Kind::Inline, 12, 32, 4096),
            reference(Kind::Inline, 12, 164, 0),
            reference(Kind::Inline, 12, 164, u32::MAX),
        ] {
            assert!(Ledger::from_records(&[bad]).is_none());
        }
        let mut bad = records[0];
        bad.value = 0;
        assert!(Ledger::from_records(&[bad]).is_none());
    }
}

// Source-bound reference closure on Linux-created fixtures. These checks
// establish no allocation, mount or I/O authority.
mod ea_reference_census {
    use core::{
        ea_census, ea_index,
        ea_inode::{self, Status},
        ea_source,
        snapshot::Snapshot,
    };

    use super::{
        ea_inode_values::{Fixture, fixture, fixture_with_features},
        *,
    };

    fn offset(table: u32, number: u32) -> usize {
        table as usize * 4096 + (number as usize - 1) * 256
    }
    fn seal_inode(img: &mut [u8], table: u32, number: u32, seed: u32) {
        let at = offset(table, number);
        let raw = &mut img[at..at + 256];
        let checksum = core::inode::calculated_checksum(raw, number, seed).unwrap();
        raw[124..126].copy_from_slice(&(checksum as u16).to_le_bytes());
        raw[130..132].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
    }
    fn seal_super(img: &mut [u8]) {
        let checksum = core::crc::crc32c(0xffffffff, &img[1024..2044]);
        img[2044..2048].copy_from_slice(&checksum.to_le_bytes());
    }
    fn seal_group(img: &mut [u8], seed: u32) {
        let width = core::superblock::descriptor_length(&img[1024..2048]).unwrap();
        let group_seed = core::crc::crc32c(seed, &0u32.to_le_bytes());
        let partial = core::crc::crc32c(group_seed, &img[4096..4126]);
        let zeroed = core::crc::crc32c(partial, &[0, 0]);
        let checksum = core::crc::crc32c(zeroed, &img[4128..4096 + width]) as u16;
        img[4126..4128].copy_from_slice(&checksum.to_le_bytes());
    }
    fn seal_external(img: &mut [u8], address: u32, seed: u32) {
        let block = &mut img[address as usize * 4096..(address as usize + 1) * 4096];
        let checksum = core::xattr::checksum(block, address as u64, seed).unwrap();
        block[16..20].copy_from_slice(&checksum.to_le_bytes());
    }
    fn set_inode_allocated(img: &mut [u8], number: u32, allocated: bool, seed: u32) {
        let ipg = le32(img, 1064);
        assert!(number > 0 && number <= ipg);
        let bitmap = le32(img, 4100) as usize * 4096;
        let slot = number as usize - 1;
        if allocated {
            img[bitmap + slot / 8] |= 1 << (slot % 8);
        } else {
            img[bitmap + slot / 8] &= !(1 << (slot % 8));
        }
        let is_set = |n: u32| img[bitmap + n as usize / 8] & (1 << (n % 8)) != 0;
        let free = (0..ipg).filter(|n| !is_set(*n)).count() as u32;
        let used_prefix = (0..ipg).rev().find(|n| is_set(*n)).map_or(0, |n| n + 1);
        let checksum = core::crc::crc32c(seed, &img[bitmap..bitmap + ipg as usize / 8]);
        img[4110..4112].copy_from_slice(&(free as u16).to_le_bytes());
        img[4122..4124].copy_from_slice(&(checksum as u16).to_le_bytes());
        img[4124..4126].copy_from_slice(&((ipg - used_prefix) as u16).to_le_bytes());
        if core::superblock::descriptor_length(&img[1024..2048]) == Some(64) {
            img[4142..4144].fill(0);
            img[4146..4148].fill(0);
            img[4154..4156].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
        }
        img[1040..1044].copy_from_slice(&free.to_le_bytes());
        seal_group(img, seed);
        seal_super(img);
    }
    fn set_references(img: &mut [u8], fixture: &Fixture, next: u64) {
        let at = offset(fixture.table, 14);
        let changed = ea_inode::set_refcount(
            &img[at..at + 256],
            14,
            fixture.inodes,
            fixture.seed,
            Status::Live,
            next,
        )
        .unwrap();
        img[at..at + 256].copy_from_slice(&changed);
    }
    fn index_then_reject(img: &[u8]) {
        let snapshot = Snapshot::from_bytes(img);
        let header = ea_source::parse(&snapshot).expect("primary read profile remains valid");
        let _index = ea_index::parse(header)
            .expect("source allocation and inode-table geometry remain valid");
        assert!(ea_census::inspect(&snapshot, u32::MAX).is_none());
    }
    fn reject_index(img: &[u8]) {
        let snapshot = Snapshot::from_bytes(img);
        let header = ea_source::parse(&snapshot).expect("primary read profile remains valid");
        assert!(ea_index::parse(header).is_none());
        assert!(ea_census::inspect(&snapshot, u32::MAX).is_none());
    }
    fn entry_hash(name: &[u8], value_hash: u32) -> u32 {
        name.iter()
            .fold(0u32, |hash, byte| hash.rotate_left(5) ^ u32::from(*byte))
            .rotate_left(16)
            ^ value_hash
    }

    #[test]
    fn linux_sharing_has_three_physical_references_four_logical_charges_and_two_block_parents() {
        for wide in [false, true] {
            for stored_seed in [false, true] {
                let fixture = fixture_with_features(
                    &format!("ea-census-profile-{wide}-{stored_seed}"),
                    4096,
                    wide,
                    stored_seed,
                );
                let snapshot = Snapshot::from_bytes(&fixture.bytes);
                let census = ea_census::inspect(&snapshot, u32::MAX).unwrap();
                assert_eq!(census.physical().len(), 3);
                assert_eq!(census.physical().refs(14), 3);
                assert_eq!(census.logical().len(), 4);
                assert_eq!(census.external_parents(fixture.external), 2);
                assert_eq!(census.external_parents(1), 0);
                assert_eq!(census.values().len(), 1);
                assert_eq!(census.values()[0].number, 14);
                assert_eq!(census.values()[0].refs, 3);
                assert!(census.logical().iter().all(|entry| entry.parent != 14));
                let first = census.quota(12).unwrap();
                let second = census.quota(13).unwrap();
                assert_eq!((first.ea_inodes, first.bytes), (3, 12_288));
                assert_eq!((second.ea_inodes, second.bytes), (1, 4096));
                assert!(census.quota(0).is_none());
                assert_eq!(census.index().allocated(14), Some(true));
                assert_eq!(census.index().allocated(15), Some(false));
                assert_eq!(census.index().allocated(0), None);
                assert_eq!(
                    census.index().node(14).unwrap().raw(),
                    inode_bytes(&fixture.bytes, fixture.table, 14)
                );
                assert!(census.index().node(15).is_none());
                assert!(core::allocation::parse(Snapshot::from_bytes(&fixture.bytes)).is_none());
                if wide {
                    let mut stale_high_checksum = fixture.bytes.clone();
                    stale_high_checksum[4154] ^= 1;
                    seal_group(&mut stale_high_checksum, fixture.seed);
                    reject_index(&stale_high_checksum);
                }
            }
        }
    }

    #[test]
    fn external_block_reference_counts_must_equal_all_parent_pointers() {
        let fixture = fixture("ea-census-block-refcount", 4096);
        for count in [1u32, 3] {
            let mut img = fixture.bytes.clone();
            let at = fixture.external as usize * 4096;
            img[at + 4..at + 8].copy_from_slice(&count.to_le_bytes());
            seal_external(&mut img, fixture.external, fixture.seed);
            index_then_reject(&img);
        }
    }

    #[test]
    fn stored_ea_refwords_must_equal_physical_indegree_and_zero_ref_orphans_are_excluded() {
        let fixture = fixture("ea-census-value-refcount", 4096);
        for count in [2u64, 4, u64::MAX] {
            let mut img = fixture.bytes.clone();
            set_references(&mut img, &fixture, count);
            index_then_reject(&img);
        }
        let mut orphan = fixture.bytes.clone();
        set_references(&mut orphan, &fixture, 0);
        index_then_reject(&orphan);
    }

    #[test]
    fn references_cannot_dereference_a_stale_inode_image_after_its_allocation_bit_is_cleared() {
        let fixture = fixture("ea-census-unallocated-value", 4096);
        let mut img = fixture.bytes.clone();
        set_inode_allocated(&mut img, 14, false, fixture.seed);
        let snapshot = Snapshot::from_bytes(&img);
        let header = ea_source::parse(&snapshot).unwrap();
        assert!(header.get(14).is_none());
        let index = ea_index::parse(header).unwrap();
        assert_eq!(index.allocated(14), Some(false));
        assert!(index.node(14).is_none());
        assert!(ea_census::inspect(&snapshot, u32::MAX).is_none());
    }

    #[test]
    fn every_allocated_live_ea_inode_requires_an_incoming_physical_record() {
        let fixture = fixture("ea-census-unreferenced-value", 4096);
        let mut img = fixture.bytes.clone();
        let original = inode_bytes(&img, fixture.table, 14).to_vec();
        let at = offset(fixture.table, 15);
        img[at..at + 256].copy_from_slice(&original);
        img[at + 36..at + 40].copy_from_slice(&1u32.to_le_bytes());
        seal_inode(&mut img, fixture.table, 15, fixture.seed);
        set_inode_allocated(&mut img, 15, true, fixture.seed);
        assert!(
            ea_inode::parse(
                inode_bytes(&img, fixture.table, 15),
                15,
                fixture.inodes,
                fixture.seed,
                Status::Live
            )
            .is_some()
        );
        index_then_reject(&img);
    }

    #[test]
    fn all_inline_and_shared_external_references_agree_with_the_value_inode_size() {
        let fixture = fixture("ea-census-conflicting-size", 4096);
        for at in [
            offset(fixture.table, 12) + 192,
            fixture.external as usize * 4096 + 40,
        ] {
            let mut img = fixture.bytes.clone();
            img[at..at + 4].copy_from_slice(&4095u32.to_le_bytes());
            if at < fixture.external as usize * 4096 {
                seal_inode(&mut img, fixture.table, 12, fixture.seed);
            } else {
                seal_external(&mut img, fixture.external, fixture.seed);
            }
            index_then_reject(&img);
        }
        let mut img = fixture.bytes.clone();
        let at = offset(fixture.table, 14);
        img[at + 4..at + 8].copy_from_slice(&4095u32.to_le_bytes());
        seal_inode(&mut img, fixture.table, 14, fixture.seed);
        index_then_reject(&img);
    }

    #[test]
    fn ea_inode_flags_determine_source_classification_and_cannot_hide_nested_parent_records() {
        let fixture = fixture("ea-census-source-classification", 4096);
        let mut ordinary_value = fixture.bytes.clone();
        let ea = offset(fixture.table, 14);
        ordinary_value[ea + 32..ea + 36].copy_from_slice(&0x80000u32.to_le_bytes());
        seal_inode(&mut ordinary_value, fixture.table, 14, fixture.seed);
        index_then_reject(&ordinary_value);
        let mut ea_parent = fixture.bytes.clone();
        let parent = offset(fixture.table, 12);
        ea_parent[parent + 32..parent + 36].copy_from_slice(&0x280000u32.to_le_bytes());
        seal_inode(&mut ea_parent, fixture.table, 12, fixture.seed);
        index_then_reject(&ea_parent);
    }

    #[test]
    fn allocation_census_rejects_stale_itable_unused_bitmap_checksums_and_free_counters() {
        let fixture = fixture("ea-census-stale-allocation", 4096);
        let ipg = le32(&fixture.bytes, 1064);
        let mut stale_tail = fixture.bytes.clone();
        stale_tail[4124..4126].copy_from_slice(&((ipg - 13) as u16).to_le_bytes());
        seal_group(&mut stale_tail, fixture.seed);
        index_then_reject(&stale_tail);
        let old_checksum = fixture.bytes[4122..4124].to_vec();
        let mut stale_bitmap = fixture.bytes.clone();
        set_inode_allocated(&mut stale_bitmap, 14, false, fixture.seed);
        stale_bitmap[4122..4124].copy_from_slice(&old_checksum);
        seal_group(&mut stale_bitmap, fixture.seed);
        reject_index(&stale_bitmap);
        let mut wrong_free = fixture.bytes.clone();
        let free = core::bytes::read_le16(&wrong_free, 4110).unwrap() + 1;
        wrong_free[4110..4112].copy_from_slice(&free.to_le_bytes());
        wrong_free[1040..1044].copy_from_slice(&(free as u32).to_le_bytes());
        seal_group(&mut wrong_free, fixture.seed);
        seal_super(&mut wrong_free);
        reject_index(&wrong_free);
    }

    #[test]
    fn multiple_ea_entries_in_one_shared_block_count_once_each_for_physical_refs_and_per_parent_for_quota()
     {
        let fixture = fixture("ea-census-two-shared-entries", 4096);
        let mut img = fixture.bytes.clone();
        let at = fixture.external as usize * 4096;
        let hash = le32(&img, offset(fixture.table, 14) + 8);
        let second = entry_hash(b"zzzzzz", hash);
        img[at + 56] = 6;
        img[at + 57] = 1;
        img[at + 60..at + 64].copy_from_slice(&14u32.to_le_bytes());
        img[at + 64..at + 68].copy_from_slice(&4096u32.to_le_bytes());
        img[at + 68..at + 72].copy_from_slice(&second.to_le_bytes());
        img[at + 72..at + 78].copy_from_slice(b"zzzzzz");
        let first = le32(&img, at + 44);
        let block_hash = if first == 0 || second == 0 {
            0
        } else {
            first.rotate_left(16) ^ second
        };
        img[at + 12..at + 16].copy_from_slice(&block_hash.to_le_bytes());
        seal_external(&mut img, fixture.external, fixture.seed);
        set_references(&mut img, &fixture, 4);
        for (number, sectors) in [(12, 40u32), (13, 24)] {
            let parent = offset(fixture.table, number);
            img[parent + 28..parent + 32].copy_from_slice(&sectors.to_le_bytes());
            seal_inode(&mut img, fixture.table, number, fixture.seed);
        }
        let snapshot = Snapshot::from_bytes(&img);
        let census = ea_census::inspect(&snapshot, u32::MAX).unwrap();
        assert_eq!(census.physical().len(), 4);
        assert_eq!(census.physical().refs(14), 4);
        assert_eq!(census.logical().len(), 6);
        assert_eq!(census.external_parents(fixture.external), 2);
        let first = census.quota(12).unwrap();
        let second = census.quota(13).unwrap();
        assert_eq!((first.ea_inodes, first.bytes), (4, 16_384));
        assert_eq!((second.ea_inodes, second.bytes), (2, 8192));
    }

    #[test]
    fn reference_census_rejects_parent_specific_lustre_backpointers_and_insufficient_scan_budget() {
        let fixture = fixture("ea-census-lustre-and-budget", 4096);
        let snapshot = Snapshot::from_bytes(&fixture.bytes);
        assert!(ea_census::inspect(&snapshot, u32::MAX).is_some());
        assert!(ea_census::inspect(&snapshot, 0).is_none());
        assert!(ea_census::inspect(&snapshot, fixture.inodes - 1).is_none());
        let mut img = fixture.bytes.clone();
        let ea = offset(fixture.table, 14);
        img[ea + 16..ea + 20].copy_from_slice(&12u32.to_le_bytes());
        seal_inode(&mut img, fixture.table, 14, fixture.seed);
        index_then_reject(&img);
        let generation = le32(&img, offset(fixture.table, 12) + 100).wrapping_add(1);
        img[ea + 100..ea + 104].copy_from_slice(&generation.to_le_bytes());
        seal_inode(&mut img, fixture.table, 14, fixture.seed);
        let snapshot = Snapshot::from_bytes(&img);
        assert!(ea_census::inspect(&snapshot, u32::MAX).is_some());
    }

    #[test]
    fn cloning_a_shared_external_block_adds_physical_references_without_adding_logical_quota_charges()
     {
        let fixture = fixture("ea-census-external-clone", 4096);
        let mut img = fixture.bytes.clone();
        let destination = le32(&img, 1028) - 1;
        let bitmap = le32(&img, 4096) as usize * 4096;
        assert_eq!(
            img[bitmap + destination as usize / 8] & (1 << (destination % 8)),
            0
        );
        let original =
            img[fixture.external as usize * 4096..(fixture.external as usize + 1) * 4096].to_vec();
        img[destination as usize * 4096..(destination as usize + 1) * 4096]
            .copy_from_slice(&original);
        for block in [fixture.external, destination] {
            img[block as usize * 4096 + 4..block as usize * 4096 + 8]
                .copy_from_slice(&1u32.to_le_bytes());
            seal_external(&mut img, block, fixture.seed);
        }
        let peer = offset(fixture.table, 13);
        img[peer + 104..peer + 108].copy_from_slice(&destination.to_le_bytes());
        seal_inode(&mut img, fixture.table, 13, fixture.seed);
        set_references(&mut img, &fixture, 4);
        img[bitmap + destination as usize / 8] |= 1 << (destination % 8);
        seal_single_group_allocation(&mut img);
        let snapshot = Snapshot::from_bytes(&img);
        let census = ea_census::inspect(&snapshot, u32::MAX).unwrap();
        assert_eq!(census.physical().len(), 4);
        assert_eq!(census.physical().refs(14), 4);
        assert_eq!(census.logical().len(), 4);
        assert_eq!(census.external_parents(fixture.external), 1);
        assert_eq!(census.external_parents(destination), 1);
        let first = census.quota(12).unwrap();
        let second = census.quota(13).unwrap();
        assert_eq!((first.ea_inodes, first.bytes), (3, 12_288));
        assert_eq!((second.ea_inodes, second.bytes), (1, 4096));
        let path = "build/ea-census-external-clone-result.img";
        std::fs::write(path, &img).unwrap();
        let fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        super::inline_xattr_updates::command(&fsck, &["-fn", path], false);
        let _ = std::fs::remove_file(path);
    }

    #[test]
    fn external_refcount_closure_includes_shared_blocks_that_contain_only_local_values() {
        let fixture = fixture("ea-census-local-only-shared", 4096);
        let mut img = fixture.bytes.clone();
        let block_number = le32(&img, 1028) - 1;
        let bitmap = le32(&img, 4096) as usize * 4096;
        assert_eq!(
            img[bitmap + block_number as usize / 8] & (1 << (block_number % 8)),
            0
        );
        let hash = entry_hash(b"local", u32::from(b'z'));
        let block = &mut img[block_number as usize * 4096..(block_number as usize + 1) * 4096];
        block.fill(0);
        block[..4].copy_from_slice(&core::xattr::MAGIC.to_le_bytes());
        block[4..8].copy_from_slice(&2u32.to_le_bytes());
        block[8..12].copy_from_slice(&1u32.to_le_bytes());
        block[12..16].copy_from_slice(&hash.to_le_bytes());
        block[32] = 5;
        block[33] = 1;
        block[34..36].copy_from_slice(&4092u16.to_le_bytes());
        block[40..44].copy_from_slice(&1u32.to_le_bytes());
        block[44..48].copy_from_slice(&hash.to_le_bytes());
        block[48..53].copy_from_slice(b"local");
        block[4092] = b'z';
        seal_external(&mut img, block_number, fixture.seed);
        for number in [2, 11] {
            let at = offset(fixture.table, number);
            assert_eq!(le32(&img, at + 104), 0);
            let sectors = le32(&img, at + 28) + 8;
            img[at + 104..at + 108].copy_from_slice(&block_number.to_le_bytes());
            img[at + 28..at + 32].copy_from_slice(&sectors.to_le_bytes());
            seal_inode(&mut img, fixture.table, number, fixture.seed);
        }
        img[bitmap + block_number as usize / 8] |= 1 << (block_number % 8);
        seal_single_group_allocation(&mut img);
        let snapshot = Snapshot::from_bytes(&img);
        let census = ea_census::inspect(&snapshot, u32::MAX).unwrap();
        assert_eq!(census.physical().len(), 3);
        assert_eq!(census.physical().refs(14), 3);
        assert_eq!(census.logical().len(), 4);
        assert_eq!(census.external_parents(block_number), 2);
        assert_eq!(census.quota(2).unwrap().ea_inodes, 0);
        assert_eq!(census.quota(11).unwrap().ea_inodes, 0);
        let mut wrong = img.clone();
        wrong[block_number as usize * 4096 + 4..block_number as usize * 4096 + 8]
            .copy_from_slice(&1u32.to_le_bytes());
        seal_external(&mut wrong, block_number, fixture.seed);
        index_then_reject(&wrong);
    }
    #[test]
    fn reserved_inode_body_attributes_cannot_hide_an_ea_reference_from_the_complete_census() {
        let fixture = fixture("ea-census-reserved-hidden-reference", 4096);
        let mut img = fixture.bytes.clone();
        let at = offset(fixture.table, 5);
        let value_hash = le32(inode_bytes(&img, fixture.table, 14), 8);
        img[at..at + 256].fill(0);
        img[at + 128..at + 130].copy_from_slice(&32u16.to_le_bytes());
        img[at + 160..at + 164].copy_from_slice(&core::xattr::MAGIC.to_le_bytes());
        img[at + 164] = 6;
        img[at + 165] = 1;
        img[at + 168..at + 172].copy_from_slice(&14u32.to_le_bytes());
        img[at + 172..at + 176].copy_from_slice(&(fixture.value.len() as u32).to_le_bytes());
        img[at + 176..at + 180].copy_from_slice(&entry_hash(b"hidden", value_hash).to_le_bytes());
        img[at + 180..at + 186].copy_from_slice(b"hidden");
        seal_inode(&mut img, fixture.table, 5, fixture.seed);
        let raw = inode_bytes(&img, fixture.table, 5);
        assert!(core::inode_group::reserved_is_empty(raw));
        assert!(
            core::xattr::parse_body(raw, true, fixture.inodes)
                .unwrap()
                .present()
        );
        assert_eq!(le32(inode_bytes(&img, fixture.table, 14), 36), 3);
        let snapshot = Snapshot::from_bytes(&img);
        let header = ea_source::parse(&snapshot).unwrap();
        assert_eq!(header.get(5).unwrap().raw(), raw);
        let index = ea_index::parse(header).unwrap();
        assert_eq!(index.allocated(5), Some(true));
        assert_eq!(index.node(5).unwrap().raw(), raw);
        assert!(ea_census::inspect(&snapshot, u32::MAX).is_none());
    }
    #[test]
    fn complete_census_checks_each_ea_entry_hash_against_its_exact_name_and_target_hash() {
        let fixture = fixture("ea-census-entry-name-hashes", 4096);
        for inline in [false, true] {
            for change_name in [false, true] {
                let mut img = fixture.bytes.clone();
                let at = if inline {
                    offset(fixture.table, 12) + 184
                } else {
                    fixture.external as usize * 4096 + 32
                };
                if change_name {
                    img[at + 16] ^= 1;
                } else {
                    img[at + 12] ^= 1;
                    if !inline {
                        let hash = le32(&img, at + 12);
                        let block = fixture.external as usize * 4096;
                        img[block + 12..block + 16].copy_from_slice(&hash.to_le_bytes());
                    }
                }
                if inline {
                    seal_inode(&mut img, fixture.table, 12, fixture.seed);
                } else {
                    seal_external(&mut img, fixture.external, fixture.seed);
                }
                let snapshot = Snapshot::from_bytes(&img);
                let header = ea_source::parse(&snapshot).unwrap();
                assert!(core::ea_parent::inspect(&header, 12).is_some());
                assert!(core::ea_parent::inspect(&header, 13).is_some());
                assert!(ea_census::inspect(&snapshot, u32::MAX).is_none());
            }
        }
    }

    #[test]
    fn complete_census_accepts_unsigned_and_legacy_signed_high_byte_ea_names() {
        let fixture = fixture("ea-census-signed-entry-names", 4096);
        let name = [0xffu8, b'x'];
        let value_hash = le32(inode_bytes(&fixture.bytes, fixture.table, 14), 8);
        let unsigned = entry_hash(&name, value_hash);
        let signed = name
            .iter()
            .fold(0u32, |hash, byte| {
                hash.rotate_left(5) ^ (*byte as i8 as i32 as u32)
            })
            .rotate_left(16)
            ^ value_hash;
        assert_ne!(unsigned, signed);
        for inline in [false, true] {
            for hash in [unsigned, signed] {
                let mut img = fixture.bytes.clone();
                let at = if inline {
                    let parent = offset(fixture.table, 12);
                    img[parent + 184..parent + 256].fill(0);
                    parent + 184
                } else {
                    let block = fixture.external as usize * 4096;
                    img[block + 32..block + 4096].fill(0);
                    img[block + 12..block + 16].copy_from_slice(&hash.to_le_bytes());
                    block + 32
                };
                img[at] = 2;
                img[at + 1] = 1;
                img[at + 4..at + 8].copy_from_slice(&14u32.to_le_bytes());
                img[at + 8..at + 12].copy_from_slice(&(fixture.value.len() as u32).to_le_bytes());
                img[at + 12..at + 16].copy_from_slice(&hash.to_le_bytes());
                img[at + 16..at + 18].copy_from_slice(&name);
                if inline {
                    seal_inode(&mut img, fixture.table, 12, fixture.seed);
                } else {
                    seal_external(&mut img, fixture.external, fixture.seed);
                }
                let snapshot = Snapshot::from_bytes(&img);
                let header = ea_source::parse(&snapshot).unwrap();
                assert!(core::ea_parent::inspect(&header, 12).is_some());
                assert!(core::ea_parent::inspect(&header, 13).is_some());
                let census = ea_census::inspect(&snapshot, u32::MAX).unwrap();
                assert_eq!(census.physical().refs(14), 3);
                assert_eq!(census.physical().len(), 3);
                assert_eq!(census.logical().len(), 4);
            }
        }
    }

    #[test]
    fn flex_groups_keep_lazy_inodes_unallocated_and_reject_aliased_inode_table_ranges() {
        let path = "build/ea-census-two-group-flex-native.img";
        let mke2fs = std::env::var("MKE2FS_BIN").unwrap_or_else(|_| "mke2fs".into());
        super::inline_xattr_updates::command(
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
                "-N",
                "128",
                "-O",
                "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum,ea_inode,flex_bg",
                "-G",
                "2",
                "-E",
                "lazy_itable_init=0,lazy_journal_init=0",
                path,
                "65536",
            ],
            false,
        );
        let mut img = std::fs::read(path).unwrap();
        let _ = std::fs::remove_file(path);
        let primary = &img[1024..2048];
        let width = core::superblock::descriptor_length(primary).unwrap();
        let seed = core::superblock::metadata_checksum_seed(primary).unwrap();
        let blocks = le32(&img, 1028);
        let inodes = le32(&img, 1024);
        let ipg = le32(&img, 1064);
        let first_group_one_inode = ipg + 1;
        let group_one = 4096 + width;
        let first_table = le32(&img, 4104);
        let second_table = le32(&img, group_one + 8);
        let table_blocks = ipg / 16;
        assert_eq!((blocks, inodes, ipg), (65_536, 128, 64));
        assert_eq!(le32(&img, 1120) & 0x200, 0x200);
        assert!(core::bytes::read_le16(&img, group_one + 18).unwrap() & 1 != 0);
        assert_eq!(
            core::bytes::read_le16(&img, group_one + 14),
            Some(ipg as u16)
        );
        assert_eq!(
            core::bytes::read_le16(&img, group_one + 28),
            Some(ipg as u16)
        );
        assert!(
            first_table + table_blocks <= second_table
                || second_table + table_blocks <= first_table
        );
        {
            let snapshot = Snapshot::from_bytes(&img);
            let header = ea_source::parse(&snapshot).unwrap();
            let index = ea_index::parse(header).unwrap();
            assert!(index.is_inode_table_block(first_table));
            assert!(index.is_inode_table_block(first_table + table_blocks - 1));
            assert!(index.is_inode_table_block(second_table));
            assert!(index.is_inode_table_block(second_table + table_blocks - 1));
            assert!(!index.is_inode_table_block(0));
            assert_eq!(index.allocated(first_group_one_inode), Some(false));
            assert!(index.node(first_group_one_inode).is_none());
            let census = ea_census::inspect(&snapshot, u32::MAX).unwrap();
            assert!(census.values().is_empty());
            assert_eq!(census.physical().len(), 0);
            assert!(census.logical().is_empty());
        }
        // INODE_UNINIT makes the entire group's logical bitmap empty. Neither
        // stale physical bits nor a locally valid EA image may allocate it.
        let physical_bitmap = le32(&img, group_one + 4) as usize * 4096;
        img[physical_bitmap..physical_bitmap + 4096].fill(0xff);
        let stale = second_table as usize * 4096;
        img[stale..stale + 256].fill(0);
        img[stale..stale + 2].copy_from_slice(&0o100600u16.to_le_bytes());
        img[stale + 4..stale + 8].copy_from_slice(&4096u32.to_le_bytes());
        img[stale + 26..stale + 28].copy_from_slice(&1u16.to_le_bytes());
        img[stale + 32..stale + 36].copy_from_slice(&0x280000u32.to_le_bytes());
        img[stale + 36..stale + 40].copy_from_slice(&1u32.to_le_bytes());
        img[stale + 40..stale + 42].copy_from_slice(&0xf30au16.to_le_bytes());
        img[stale + 44..stale + 46].copy_from_slice(&4u16.to_le_bytes());
        img[stale + 128..stale + 130].copy_from_slice(&32u16.to_le_bytes());
        let checksum =
            core::inode::calculated_checksum(&img[stale..stale + 256], first_group_one_inode, seed)
                .unwrap();
        img[stale + 124..stale + 126].copy_from_slice(&(checksum as u16).to_le_bytes());
        img[stale + 130..stale + 132].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
        assert!(
            ea_inode::parse(
                &img[stale..stale + 256],
                first_group_one_inode,
                inodes,
                seed,
                Status::Live
            )
            .is_some()
        );
        {
            let snapshot = Snapshot::from_bytes(&img);
            let header = ea_source::parse(&snapshot).unwrap();
            assert!(header.get(first_group_one_inode).is_none());
            let index = ea_index::parse(header).unwrap();
            assert_eq!(index.allocated(first_group_one_inode), Some(false));
            assert!(index.node(first_group_one_inode).is_none());
            let census = ea_census::inspect(&snapshot, u32::MAX).unwrap();
            assert!(census.values().is_empty());
            assert_eq!(census.physical().len(), 0);
        }
        // FLEX_BG permits each pointer locally. The complete index must also
        // ensure that two groups do not name the same inode-table frames.
        img[group_one + 8..group_one + 12].copy_from_slice(&first_table.to_le_bytes());
        let group_seed = core::crc::crc32c(seed, &1u32.to_le_bytes());
        let partial = core::crc::crc32c(group_seed, &img[group_one..group_one + 30]);
        let zeroed = core::crc::crc32c(partial, &[0, 0]);
        let checksum = core::crc::crc32c(zeroed, &img[group_one + 32..group_one + width]) as u16;
        img[group_one + 30..group_one + 32].copy_from_slice(&checksum.to_le_bytes());
        assert!(
            core::group::parse_with_features(
                &img[group_one..group_one + width],
                1,
                blocks,
                ipg,
                seed,
                true
            )
            .is_some()
        );
        let snapshot = Snapshot::from_bytes(&img);
        let header = ea_source::parse(&snapshot).unwrap();
        assert!(ea_index::parse(header).is_none());
        assert!(ea_census::inspect(&snapshot, u32::MAX).is_none());
    }
}

// Native source-complete EA value integrity tests. These exercise emitted
// code on Linux-created bytes; they do not discharge formal obligations.
mod ea_value_integrity {
    use core::{
        block_claims, ea_census,
        ea_inode::{self, Status},
        ea_integrity, ea_source, ea_storage, ea_value,
        snapshot::Snapshot,
    };

    use super::{
        ea_inode_values::{
            Fixture, entry_hash, fixture, fixture_with_features, mappings, offset, seal_raw,
        },
        *,
    };

    fn seal_inode(img: &mut [u8], fixture: &Fixture, number: u32) {
        let at = offset(fixture.table, number);
        seal_raw(&mut img[at..at + 256], number, fixture.seed);
    }
    fn seal_group(img: &mut [u8], seed: u32) {
        let width = core::superblock::descriptor_length(&img[1024..2048]).unwrap();
        let group_seed = core::crc::crc32c(seed, &0u32.to_le_bytes());
        let partial = core::crc::crc32c(group_seed, &img[4096..4126]);
        let zeroed = core::crc::crc32c(partial, &[0, 0]);
        let checksum = core::crc::crc32c(zeroed, &img[4128..4096 + width]) as u16;
        img[4126..4128].copy_from_slice(&checksum.to_le_bytes());
    }
    fn seal_super(img: &mut [u8]) {
        let checksum = core::crc::crc32c(0xffffffff, &img[1024..2044]);
        img[2044..2048].copy_from_slice(&checksum.to_le_bytes());
    }
    fn set_inode_allocated(img: &mut [u8], fixture: &Fixture, number: u32) {
        let ipg = le32(img, 1064);
        assert!(number > 0 && number <= ipg);
        let bitmap = le32(img, 4100) as usize * 4096;
        let slot = number as usize - 1;
        assert_eq!(img[bitmap + slot / 8] & (1 << (slot % 8)), 0);
        img[bitmap + slot / 8] |= 1 << (slot % 8);
        let is_set = |n: u32| img[bitmap + n as usize / 8] & (1 << (n % 8)) != 0;
        let free = (0..ipg).filter(|n| !is_set(*n)).count() as u32;
        let used = (0..ipg).rev().find(|n| is_set(*n)).map_or(0, |n| n + 1);
        let checksum = core::crc::crc32c(fixture.seed, &img[bitmap..bitmap + ipg as usize / 8]);
        img[4110..4112].copy_from_slice(&(free as u16).to_le_bytes());
        img[4122..4124].copy_from_slice(&(checksum as u16).to_le_bytes());
        img[4124..4126].copy_from_slice(&((ipg - used) as u16).to_le_bytes());
        if core::superblock::descriptor_length(&img[1024..2048]) == Some(64) {
            img[4142..4144].fill(0);
            img[4146..4148].fill(0);
            img[4154..4156].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
        }
        img[1040..1044].copy_from_slice(&free.to_le_bytes());
        seal_group(img, fixture.seed);
        seal_super(img);
    }
    fn set_block_allocated(img: &mut [u8], block: u32, allocated: bool) {
        assert!(block < le32(img, 1028));
        let at = le32(img, 4096) as usize * 4096 + block as usize / 8;
        if allocated {
            assert_eq!(img[at] & (1 << (block % 8)), 0);
            img[at] |= 1 << (block % 8);
        } else {
            assert_ne!(img[at] & (1 << (block % 8)), 0);
            img[at] &= !(1 << (block % 8));
        }
        seal_single_group_allocation(img);
    }
    fn fresh_block(img: &[u8]) -> u32 {
        let blocks = le32(img, 1028);
        let bitmap = le32(img, 4096) as usize * 4096;
        (1..blocks)
            .rev()
            .find(|block| img[bitmap + *block as usize / 8] & (1 << (*block % 8)) == 0)
            .unwrap()
    }
    fn leaf(raw: &mut [u8], index: usize, logical: u32, physical: u32, length: u16) {
        let at = 12 + index * 12;
        raw[at..at + 4].copy_from_slice(&logical.to_le_bytes());
        raw[at + 4..at + 6].copy_from_slice(&length.to_le_bytes());
        raw[at + 6..at + 8].fill(0);
        raw[at + 8..at + 12].copy_from_slice(&physical.to_le_bytes());
    }
    fn single_leaf(img: &mut [u8], fixture: &Fixture, physical: u32, length: u16) {
        let ea = offset(fixture.table, 14);
        let raw = &mut img[ea + 40..ea + 100];
        raw.fill(0);
        raw[..2].copy_from_slice(&0xf30au16.to_le_bytes());
        raw[2..4].copy_from_slice(&1u16.to_le_bytes());
        raw[4..6].copy_from_slice(&4u16.to_le_bytes());
        leaf(raw, 0, 0, physical, length);
    }
    // Bind every source entry to the changed payload while preserving the
    // complete physical/logical reference graph and every parent sector bill.
    fn update_hashes(img: &mut [u8], fixture: &Fixture, content: &[u8]) {
        let hash = core::crc::crc32c(fixture.seed, content);
        let ea = offset(fixture.table, 14);
        img[ea + 4..ea + 8].copy_from_slice(&(content.len() as u32).to_le_bytes());
        img[ea + 8..ea + 12].copy_from_slice(&hash.to_le_bytes());
        let parent = offset(fixture.table, 12);
        for (at, name) in [
            (parent + 164, b"big".as_slice()),
            (parent + 184, b"alias".as_slice()),
        ] {
            img[at + 8..at + 12].copy_from_slice(&(content.len() as u32).to_le_bytes());
            img[at + 12..at + 16].copy_from_slice(&entry_hash(name, hash).to_le_bytes());
        }
        let at = fixture.external as usize * 4096;
        let shared = entry_hash(b"shared", hash);
        img[at + 12..at + 16].copy_from_slice(&shared.to_le_bytes());
        img[at + 40..at + 44].copy_from_slice(&(content.len() as u32).to_le_bytes());
        img[at + 44..at + 48].copy_from_slice(&shared.to_le_bytes());
        let checksum =
            core::xattr::checksum(&img[at..at + 4096], fixture.external as u64, fixture.seed)
                .unwrap();
        img[at + 16..at + 20].copy_from_slice(&checksum.to_le_bytes());
        seal_inode(img, fixture, 12);
        seal_inode(img, fixture, 13);
        seal_inode(img, fixture, 14);
    }
    fn reference_admitted(img: &[u8]) {
        let snapshot = Snapshot::from_bytes(img);
        assert!(
            ea_census::inspect(&snapshot, u32::MAX).is_some(),
            "reference metadata remains valid"
        );
    }
    fn old_reader_admitted(img: &[u8], expected: &[u8], budget: u64) {
        let snapshot = Snapshot::from_bytes(img);
        let header = ea_source::parse(&snapshot).unwrap();
        let value = ea_value::inspect(&header, 12, 1, b"big", budget).unwrap();
        assert_eq!(value.as_slice(), expected);
    }
    fn integrity_rejected(img: &[u8], budget: u64, bytes: u64) {
        let snapshot = Snapshot::from_bytes(img);
        assert!(ea_integrity::inspect(&snapshot, u32::MAX, budget, bytes).is_none());
    }
    fn depth_one(fixture: &Fixture, alias_data: bool) -> (Vec<u8>, u32) {
        assert_eq!(fixture.value.len(), 4096);
        let mut img = fixture.bytes.clone();
        let ea = offset(fixture.table, 14);
        let original = img[ea + 40..ea + 100].to_vec();
        let count = core::bytes::read_le16(&original, 2).unwrap() as usize;
        assert_eq!(count, 1);
        let address = if alias_data {
            mappings(&img, fixture.table, 4096)[0]
        } else {
            fresh_block(&img)
        };
        let generation = le32(&img, ea + 100);
        let checksum_seed = core::inode::inode_seed(fixture.seed, 14, generation);
        let target = &mut img[address as usize * 4096..(address as usize + 1) * 4096];
        target.fill(0);
        target[..12 + count * 12].copy_from_slice(&original[..12 + count * 12]);
        target[4..6].copy_from_slice(&340u16.to_le_bytes());
        let checksum = core::crc::crc32c(checksum_seed, &target[..4092]);
        target[4092..4096].copy_from_slice(&checksum.to_le_bytes());
        let root = &mut img[ea + 40..ea + 100];
        root.fill(0);
        root[..2].copy_from_slice(&0xf30au16.to_le_bytes());
        root[2..4].copy_from_slice(&1u16.to_le_bytes());
        root[4..6].copy_from_slice(&4u16.to_le_bytes());
        root[6..8].copy_from_slice(&1u16.to_le_bytes());
        root[16..20].copy_from_slice(&address.to_le_bytes());
        img[ea + 28..ea + 32].copy_from_slice(&16u32.to_le_bytes());
        if !alias_data {
            set_block_allocated(&mut img, address, true);
        }
        if alias_data {
            let bytes = img[address as usize * 4096..(address as usize + 1) * 4096].to_vec();
            update_hashes(&mut img, fixture, &bytes);
        } else {
            seal_inode(&mut img, fixture, 14);
        }
        (img, address)
    }
    fn peer_value(fixture: &Fixture, share_physical: bool) -> Vec<u8> {
        assert_eq!(fixture.value.len(), 4096);
        let mut img = fixture.bytes.clone();
        let original = inode_bytes(&img, fixture.table, 14).to_vec();
        let other = offset(fixture.table, 15);
        img[other..other + 256].copy_from_slice(&original);
        img[other + 36..other + 40].copy_from_slice(&1u32.to_le_bytes());
        if !share_physical {
            let destination = fresh_block(&img);
            img[destination as usize * 4096..(destination as usize + 1) * 4096]
                .copy_from_slice(&fixture.value);
            let raw = &mut img[other + 40..other + 100];
            raw.fill(0);
            raw[..2].copy_from_slice(&0xf30au16.to_le_bytes());
            raw[2..4].copy_from_slice(&1u16.to_le_bytes());
            raw[4..6].copy_from_slice(&4u16.to_le_bytes());
            leaf(raw, 0, 0, destination, 1);
            set_block_allocated(&mut img, destination, true);
        }
        let first = offset(fixture.table, 14);
        img[first + 36..first + 40].copy_from_slice(&2u32.to_le_bytes());
        let parent = offset(fixture.table, 12);
        img[parent + 188..parent + 192].copy_from_slice(&15u32.to_le_bytes());
        seal_inode(&mut img, fixture, 12);
        seal_inode(&mut img, fixture, 14);
        seal_inode(&mut img, fixture, 15);
        set_inode_allocated(&mut img, fixture, 15);
        img
    }

    #[test]
    fn all_value_integrity_counts_shared_values_once_under_each_linux_descriptor_and_seed_profile()
    {
        for wide in [false, true] {
            for stored_seed in [false, true] {
                let fixture = fixture_with_features(
                    &format!("ea-integrity-profile-{wide}-{stored_seed}"),
                    4096,
                    wide,
                    stored_seed,
                );
                let snapshot = Snapshot::from_bytes(&fixture.bytes);
                let all = ea_integrity::inspect(&snapshot, u32::MAX, 1, 4096).unwrap();
                assert_eq!(all.value_count(), 1);
                assert!(all.value(1).is_none());
                assert_eq!(all.allocated_blocks(), 1);
                assert_eq!(all.reference_census().physical().len(), 3);
                assert_eq!(all.reference_census().logical().len(), 4);
                let value = all.value(0).unwrap();
                assert_eq!(value.info().number, 14);
                assert_eq!(value.info().refs, 3);
                assert_eq!(value.as_slice(), fixture.value);
                assert_eq!(value.claims().len(), 1);
                assert_eq!(value.claims()[0].kind, 4);
                assert_eq!(value.claims()[0].inode, 14);
                assert_eq!(value.blocks().len(), 1);
                assert!(
                    core::image_validation::inspect(Snapshot::from_bytes(&fixture.bytes)).is_none(),
                    "ordinary mount admission remains gated"
                );
            }
        }
    }

    #[test]
    fn all_value_integrity_returns_exact_partial_final_block_bytes_and_physical_charge() {
        for size in [16_384usize, 16_401, 65_536] {
            let fixture = fixture(&format!("ea-integrity-large-{size}"), size);
            let snapshot = Snapshot::from_bytes(&fixture.bytes);
            let all = ea_integrity::inspect(&snapshot, u32::MAX, 8, size as u64).unwrap();
            assert_eq!(all.value_count(), 1);
            assert_eq!(all.value(0).unwrap().as_slice(), fixture.value);
            assert_eq!(all.allocated_blocks(), ((size + 4095) / 4096) as u64);
            assert_eq!(
                all.value(0).unwrap().blocks(),
                mappings(&fixture.bytes, fixture.table, size)
                    .into_iter()
                    .map(u64::from)
                    .collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn value_integrity_reads_every_payload_instead_of_trusting_reference_metadata_hash_words() {
        let fixture = fixture("ea-integrity-corrupt-payload", 16_401);
        let mut img = fixture.bytes.clone();
        let blocks = mappings(&img, fixture.table, fixture.value.len());
        img[blocks[blocks.len() - 1] as usize * 4096] ^= 1;
        reference_admitted(&img);
        integrity_rejected(&img, 8, fixture.value.len() as u64);
    }

    #[test]
    fn value_integrity_requires_exact_inode_sector_accounting_for_every_complete_extent_tree() {
        let fixture = fixture("ea-integrity-exact-sectors", 4096);
        let ea = offset(fixture.table, 14);
        for sectors in [0u32, 1, 16] {
            let mut img = fixture.bytes.clone();
            img[ea + 28..ea + 32].copy_from_slice(&sectors.to_le_bytes());
            seal_inode(&mut img, &fixture, 14);
            reference_admitted(&img);
            old_reader_admitted(&img, &fixture.value, 1);
            integrity_rejected(&img, 1, 4096);
        }
    }

    #[test]
    fn value_integrity_rejects_holes_and_unwritten_blocks_even_with_intact_reference_metadata() {
        let fixture = fixture("ea-integrity-dense-written", 4096);
        let ea = offset(fixture.table, 14);
        for hole in [false, true] {
            let mut img = fixture.bytes.clone();
            if hole {
                img[ea + 52..ea + 56].copy_from_slice(&1u32.to_le_bytes());
            } else {
                img[ea + 56..ea + 58].copy_from_slice(&0x8001u16.to_le_bytes());
            }
            seal_inode(&mut img, &fixture, 14);
            reference_admitted(&img);
            integrity_rejected(&img, 1, 4096);
        }
    }

    #[test]
    fn complete_extent_collection_rejects_initialized_and_unwritten_allocations_beyond_value_eof() {
        let fixture = fixture("ea-integrity-no-extra-eof", 4096);
        let ea = offset(fixture.table, 14);
        for unwritten in [false, true] {
            let mut img = fixture.bytes.clone();
            let extra = fresh_block(&img);
            set_block_allocated(&mut img, extra, true);
            let root = &mut img[ea + 40..ea + 100];
            assert_eq!(core::bytes::read_le16(root, 2), Some(1));
            root[2..4].copy_from_slice(&2u16.to_le_bytes());
            leaf(root, 1, 1, extra, if unwritten { 0x8001 } else { 1 });
            img[ea + 28..ea + 32].copy_from_slice(&16u32.to_le_bytes());
            seal_inode(&mut img, &fixture, 14);
            reference_admitted(&img);
            old_reader_admitted(&img, &fixture.value, 1);
            integrity_rejected(&img, 1, 4096);
        }
    }

    #[test]
    fn external_extent_metadata_is_allocated_charged_and_included_in_the_visit_budget() {
        let fixture = fixture("ea-integrity-external-extent", 4096);
        let (img, metadata) = depth_one(&fixture, false);
        reference_admitted(&img);
        old_reader_admitted(&img, &fixture.value, 2);
        let snapshot = Snapshot::from_bytes(&img);
        assert!(ea_integrity::inspect(&snapshot, u32::MAX, 1, 4096).is_none());
        let all = ea_integrity::inspect(&snapshot, u32::MAX, 2, 4096).unwrap();
        let value = all.value(0).unwrap();
        assert_eq!(value.as_slice(), fixture.value);
        assert_eq!(all.allocated_blocks(), 2);
        assert_eq!(value.claims().len(), 2);
        assert_eq!(value.claims()[0].start, metadata);
        assert_eq!(value.claims()[0].kind, 6);
        assert_eq!(value.claims()[1].kind, 4);
    }

    #[test]
    fn value_data_cannot_reuse_its_own_checksum_valid_extent_metadata_block() {
        let fixture = fixture("ea-integrity-metadata-data-alias", 4096);
        let (img, address) = depth_one(&fixture, true);
        let data = &img[address as usize * 4096..(address as usize + 1) * 4096];
        reference_admitted(&img);
        old_reader_admitted(&img, data, 2);
        integrity_rejected(&img, 2, 4096);
    }

    #[test]
    fn distinct_ea_inodes_may_hold_equal_bytes_but_must_have_disjoint_physical_storage() {
        let fixture = fixture("ea-integrity-independent-values", 4096);
        let img = peer_value(&fixture, false);
        reference_admitted(&img);
        let snapshot = Snapshot::from_bytes(&img);
        let all = ea_integrity::inspect(&snapshot, u32::MAX, 1, 8192).unwrap();
        assert_eq!(all.value_count(), 2);
        assert_eq!(all.allocated_blocks(), 2);
        assert_eq!(all.value(0).unwrap().info().number, 14);
        assert_eq!(all.value(1).unwrap().info().number, 15);
        assert_eq!(all.value(0).unwrap().as_slice(), fixture.value);
        assert_eq!(all.value(1).unwrap().as_slice(), fixture.value);
        assert_ne!(
            all.value(0).unwrap().blocks(),
            all.value(1).unwrap().blocks()
        );
        let path = "build/ea-integrity-independent-values-result.img";
        std::fs::write(path, &img).unwrap();
        let fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        super::inline_xattr_updates::command(&fsck, &["-fn", path], false);
        let _ = std::fs::remove_file(path);

        let aliased = peer_value(&fixture, true);
        reference_admitted(&aliased);
        let snapshot = Snapshot::from_bytes(&aliased);
        let refs = ea_census::inspect(&snapshot, u32::MAX).unwrap();
        assert_eq!(refs.values().len(), 2);
        for number in [14, 15] {
            let empty = block_claims::Census::new(le32(&aliased, 1028)).unwrap();
            let (_, stored) = ea_storage::inspect(refs.index(), number, 1, empty).unwrap();
            assert_eq!(
                stored.as_slice(),
                fixture.value,
                "each inode is locally valid"
            );
        }
        integrity_rejected(&aliased, 1, 8192);
    }

    #[test]
    fn block_bitmap_allocation_is_checked_after_its_checksum_and_free_counters_are_repaired() {
        let fixture = fixture("ea-integrity-unallocated-payload", 4096);
        let mut img = fixture.bytes.clone();
        let physical = mappings(&img, fixture.table, 4096)[0];
        set_block_allocated(&mut img, physical, false);
        reference_admitted(&img);
        old_reader_admitted(&img, &fixture.value, 1);
        integrity_rejected(&img, 1, 4096);
    }

    #[test]
    fn checksum_valid_values_cannot_treat_allocated_allocation_bitmaps_as_payload_storage() {
        let fixture = fixture("ea-integrity-fixed-metadata-alias", 4096);
        for descriptor_offset in [4096, 4100] {
            let mut img = fixture.bytes.clone();
            let physical = le32(&img, descriptor_offset);
            single_leaf(&mut img, &fixture, physical, 1);
            let payload = img[physical as usize * 4096..(physical as usize + 1) * 4096].to_vec();
            update_hashes(&mut img, &fixture, &payload);
            reference_admitted(&img);
            old_reader_admitted(&img, &payload, 1);
            integrity_rejected(&img, 1, 4096);
        }
    }

    #[test]
    fn checksum_valid_value_cannot_alias_the_external_xattr_block_that_references_it() {
        let fixture = fixture("ea-integrity-external-xattr-alias", 4096);
        let mut img = fixture.bytes.clone();
        single_leaf(&mut img, &fixture, fixture.external, 1);
        // The first12 bytes contain only stable header words. Entry/block hash
        // and checksum words lie outside the value, so this is not rejected
        // merely because a self-referential CRC equation was left unsolved.
        let at = fixture.external as usize * 4096;
        let payload = img[at..at + 12].to_vec();
        update_hashes(&mut img, &fixture, &payload);
        reference_admitted(&img);
        old_reader_admitted(&img, &payload, 1);
        integrity_rejected(&img, 1, 12);
    }

    #[test]
    fn complete_value_scan_rejects_insufficient_inode_node_or_byte_budgets_without_partial_success()
    {
        let fixture = fixture("ea-integrity-complete-budget", 4096);
        let snapshot = Snapshot::from_bytes(&fixture.bytes);
        assert!(ea_integrity::inspect(&snapshot, u32::MAX, 1, 4096).is_some());
        assert!(ea_integrity::inspect(&snapshot, fixture.inodes - 1, 1, 4096).is_none());
        assert!(ea_integrity::inspect(&snapshot, u32::MAX, 0, 4096).is_none());
        assert!(ea_integrity::inspect(&snapshot, u32::MAX, 4097, 4096).is_none());
        assert!(ea_integrity::inspect(&snapshot, u32::MAX, 1, 4095).is_none());
        let img = peer_value(&fixture, false);
        let snapshot = Snapshot::from_bytes(&img);
        assert!(
            ea_integrity::inspect(&snapshot, u32::MAX, 1, 4096).is_none(),
            "a valid first value cannot conceal the missing second value"
        );
        assert!(ea_integrity::inspect(&snapshot, u32::MAX, 1, 8192).is_some());
    }

    #[test]
    fn linux_ea_feature_profile_with_no_allocated_values_has_a_complete_empty_integrity_census() {
        let path = "build/ea-integrity-empty-values-native.img";
        let mke2fs = std::env::var("MKE2FS_BIN").unwrap_or_else(|_| "mke2fs".into());
        super::inline_xattr_updates::command(
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
                "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum,ea_inode",
                "-E",
                "lazy_itable_init=0,lazy_journal_init=0",
                path,
                "8192",
            ],
            false,
        );
        let img = std::fs::read(path).unwrap();
        let _ = std::fs::remove_file(path);
        let snapshot = Snapshot::from_bytes(&img);
        let all = ea_integrity::inspect(&snapshot, u32::MAX, 1, 0).unwrap();
        assert_eq!(all.value_count(), 0);
        assert_eq!(all.allocated_blocks(), 0);
        assert!(all.value(0).is_none());
        assert!(all.reference_census().values().is_empty());
        assert!(all.reference_census().logical().is_empty());
    }
}

// Global EA allocation regression tests execute emitted code on Linux-created
// source images. Native tests do not discharge formal obligations.
mod ea_volume_allocation {
    use core::{ea_allocation, ea_integrity, snapshot::Snapshot};

    use super::{
        ea_inode_values::{
            Fixture, entry_hash, fixture, fixture_with_features, mappings, offset, seal_raw,
        },
        *,
    };

    fn seal_inode(img: &mut [u8], fixture: &Fixture, number: u32) {
        let at = offset(fixture.table, number);
        seal_raw(&mut img[at..at + 256], number, fixture.seed);
    }
    fn seal_group(img: &mut [u8], number: u32, seed: u32) {
        let width = core::superblock::descriptor_length(&img[1024..2048]).unwrap();
        let at = 4096 + number as usize * width;
        let group_seed = core::crc::crc32c(seed, &number.to_le_bytes());
        let part = core::crc::crc32c(group_seed, &img[at..at + 30]);
        let zeroed = core::crc::crc32c(part, &[0, 0]);
        let checksum = core::crc::crc32c(zeroed, &img[at + 32..at + width]) as u16;
        img[at + 30..at + 32].copy_from_slice(&checksum.to_le_bytes());
    }
    fn seal_external(img: &mut [u8], fixture: &Fixture, address: u32) {
        let at = address as usize * 4096;
        let checksum =
            core::xattr::checksum(&img[at..at + 4096], address as u64, fixture.seed).unwrap();
        img[at + 16..at + 20].copy_from_slice(&checksum.to_le_bytes());
    }
    fn fresh_block(img: &[u8]) -> u32 {
        let bitmap = le32(img, 4096) as usize * 4096;
        (1..le32(img, 1028))
            .rev()
            .find(|b| img[bitmap + *b as usize / 8] & (1 << (*b % 8)) == 0)
            .unwrap()
    }
    fn set_allocated(img: &mut [u8], block: u32, allocated: bool) {
        assert!(le32(img, 1028) <= 32768);
        let at = le32(img, 4096) as usize * 4096 + block as usize / 8;
        assert_ne!(img[at] & (1 << (block % 8)) != 0, allocated);
        if allocated {
            img[at] |= 1 << (block % 8);
        } else {
            img[at] &= !(1 << (block % 8));
        }
        seal_single_group_allocation(img);
    }
    fn one_extent(
        img: &mut [u8],
        fixture: &Fixture,
        number: u32,
        physical: u32,
        logical: u32,
        length: u16,
    ) {
        let at = offset(fixture.table, number);
        let root = &mut img[at + 40..at + 100];
        root.fill(0);
        root[..2].copy_from_slice(&0xf30au16.to_le_bytes());
        root[2..4].copy_from_slice(&1u16.to_le_bytes());
        root[4..6].copy_from_slice(&4u16.to_le_bytes());
        root[12..16].copy_from_slice(&logical.to_le_bytes());
        root[16..18].copy_from_slice(&length.to_le_bytes());
        root[20..24].copy_from_slice(&physical.to_le_bytes());
    }
    fn add_file_extent(
        img: &mut [u8],
        fixture: &Fixture,
        number: u32,
        physical: u32,
        logical: u32,
        unwritten: bool,
    ) {
        let at = offset(fixture.table, number);
        assert_eq!(core::bytes::read_le16(img, at + 42), Some(0));
        let sectors = le32(img, at + 28) + 8;
        img[at + 4..at + 8].copy_from_slice(&((logical + 1) * 4096).to_le_bytes());
        img[at + 28..at + 32].copy_from_slice(&sectors.to_le_bytes());
        one_extent(
            img,
            fixture,
            number,
            physical,
            logical,
            if unwritten { 0x8001 } else { 1 },
        );
        seal_inode(img, fixture, number);
    }
    fn update_value_hashes(img: &mut [u8], fixture: &Fixture, payload: &[u8]) {
        assert_eq!(payload.len(), 4096);
        let hash = core::crc::crc32c(fixture.seed, payload);
        let value = offset(fixture.table, 14);
        img[value + 8..value + 12].copy_from_slice(&hash.to_le_bytes());
        let parent = offset(fixture.table, 12);
        for (at, name) in [
            (parent + 164, b"big".as_slice()),
            (parent + 184, b"alias".as_slice()),
        ] {
            img[at + 12..at + 16].copy_from_slice(&entry_hash(name, hash).to_le_bytes());
        }
        let external = fixture.external as usize * 4096;
        let shared = entry_hash(b"shared", hash);
        img[external + 12..external + 16].copy_from_slice(&shared.to_le_bytes());
        img[external + 44..external + 48].copy_from_slice(&shared.to_le_bytes());
        seal_external(img, fixture, fixture.external);
        for number in [12, 13, 14] {
            seal_inode(img, fixture, number);
        }
    }
    fn integrity_admitted(img: &[u8], bytes: u64) {
        let snapshot = Snapshot::from_bytes(img);
        assert!(
            ea_integrity::inspect(&snapshot, u32::MAX, 8, bytes).is_some(),
            "all EA values and references remain valid"
        );
    }
    fn rejected(img: &[u8], bytes: u64) {
        let snapshot = Snapshot::from_bytes(img);
        assert!(ea_allocation::inspect(&snapshot, u32::MAX, 8, bytes).is_none());
    }
    fn fsck(img: &[u8], prefix: &str) {
        let path = format!("build/{prefix}.img");
        std::fs::write(&path, img).unwrap();
        let fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        super::inline_xattr_updates::command(&fsck, &["-fn", &path], false);
        let _ = std::fs::remove_file(path);
    }

    #[test]
    fn global_ea_allocation_counts_shared_external_storage_once_in_all_linux_seed_and_descriptor_profiles()
     {
        for wide in [false, true] {
            for stored_seed in [false, true] {
                let fixture = fixture_with_features(
                    &format!("ea-volume-profile-{wide}-{stored_seed}"),
                    4096,
                    wide,
                    stored_seed,
                );
                let snapshot = Snapshot::from_bytes(&fixture.bytes);
                let all = ea_allocation::inspect(&snapshot, u32::MAX, 1, 4096).unwrap();
                assert_eq!(all.integrity().value_count(), 1);
                assert_eq!(all.integrity().value(0).unwrap().as_slice(), fixture.value);
                assert_eq!(all.ordinary_count(), 4);
                assert_eq!(all.ordinary(0).unwrap().number(), 2);
                assert!(all.ordinary(0).unwrap().is_directory());
                assert!(all.ordinary(4).is_none());
                let records = all.ledger().claims();
                assert_eq!(
                    records
                        .iter()
                        .filter(|c| c.kind == 7 && c.start == fixture.external)
                        .count(),
                    1
                );
                assert_eq!(all.ledger().role_of(fixture.external).unwrap().kind, 7);
                assert_eq!(
                    all.ledger()
                        .role_of(mappings(&fixture.bytes, fixture.table, 4096)[0])
                        .unwrap()
                        .inode,
                    14
                );
                let journal = all.journal();
                assert_eq!(
                    all.ledger().role_of(journal.physical_start()).unwrap().kind,
                    2
                );
                assert_eq!(
                    all.ledger()
                        .role_of(journal.physical_start() + journal.blocks() - 1)
                        .unwrap()
                        .kind,
                    2
                );
                let claimed: u64 = records.iter().map(|c| u64::from(c.length)).sum();
                assert_eq!(
                    claimed,
                    u64::from(le32(&fixture.bytes, 1028) - le32(&fixture.bytes, 1036))
                );
                assert!(
                    core::allocation::parse(Snapshot::from_bytes(&fixture.bytes)).is_none(),
                    "ordinary mount profile remains gated"
                );
            }
        }
    }

    #[test]
    fn global_ea_allocation_composes_exact_parent_logical_charges_with_partial_value_block_ownership()
     {
        for size in [16_384usize, 16_401, 65_536] {
            let fixture = fixture(&format!("ea-volume-multiblock-{size}"), size);
            let snapshot = Snapshot::from_bytes(&fixture.bytes);
            let all = ea_allocation::inspect(&snapshot, u32::MAX, 8, size as u64).unwrap();
            assert_eq!(
                all.integrity().allocated_blocks(),
                ((size + 4095) / 4096) as u64
            );
            for i in 0..all.ordinary_count() {
                let ordinary = all.ordinary(i).unwrap();
                if ordinary.number() == 12 {
                    let usage = ordinary.usage();
                    assert_eq!(usage.own, 0);
                    assert_eq!(usage.ea, 3 * ((size + 4095) / 4096) as u64 * 8);
                    assert_eq!(usage.external, 8);
                }
            }
        }
    }

    #[test]
    fn complete_ea_storage_cannot_alias_an_ordinary_file_extent_with_valid_counts_and_payload_hashes()
     {
        let fixture = fixture("ea-volume-ea-file-alias", 4096);
        let mut img = fixture.bytes.clone();
        let physical = mappings(&img, fixture.table, 4096)[0];
        add_file_extent(&mut img, &fixture, 12, physical, 0, false);
        integrity_admitted(&img, 4096);
        rejected(&img, 4096);
    }

    #[test]
    fn complete_ea_storage_cannot_alias_the_source_journal_even_with_a_matching_payload_crc() {
        let fixture = fixture("ea-volume-ea-journal-alias", 4096);
        let mut img = fixture.bytes.clone();
        let old = mappings(&img, fixture.table, 4096)[0];
        let journal = le32(&img, offset(fixture.table, 8) + 60);
        one_extent(&mut img, &fixture, 14, journal, 0, 1);
        let payload = img[journal as usize * 4096..(journal as usize + 1) * 4096].to_vec();
        update_value_hashes(&mut img, &fixture, &payload);
        set_allocated(&mut img, old, false);
        integrity_admitted(&img, 4096);
        rejected(&img, 4096);
    }

    #[test]
    fn distinct_ordinary_files_cannot_share_data_storage_even_when_their_billing_is_exact() {
        let fixture = fixture("ea-volume-file-file-alias", 4096);
        let mut img = fixture.bytes.clone();
        let physical = fresh_block(&img);
        set_allocated(&mut img, physical, true);
        add_file_extent(&mut img, &fixture, 12, physical, 0, false);
        add_file_extent(&mut img, &fixture, 13, physical, 0, false);
        integrity_admitted(&img, 4096);
        rejected(&img, 4096);
    }

    #[test]
    fn ordinary_data_cannot_reuse_a_shared_external_xattr_or_reserved_bitmap_block() {
        let fixture = fixture("ea-volume-file-metadata-alias", 4096);
        for physical in [
            fixture.external,
            le32(&fixture.bytes, 4096),
            le32(&fixture.bytes, 4100),
        ] {
            let mut img = fixture.bytes.clone();
            add_file_extent(&mut img, &fixture, 12, physical, 0, false);
            integrity_admitted(&img, 4096);
            rejected(&img, 4096);
        }
    }

    #[test]
    fn every_ordinary_extent_must_be_allocated_in_the_source_bitmap() {
        let fixture = fixture("ea-volume-referenced-free-block", 4096);
        let mut img = fixture.bytes.clone();
        let physical = fresh_block(&img);
        add_file_extent(&mut img, &fixture, 12, physical, 0, false);
        integrity_admitted(&img, 4096);
        rejected(&img, 4096);
    }

    #[test]
    fn an_allocated_block_without_any_inode_or_metadata_owner_is_rejected_after_resealing_all_counters()
     {
        let fixture = fixture("ea-volume-hidden-allocation", 4096);
        let mut img = fixture.bytes.clone();
        let physical = fresh_block(&img);
        set_allocated(&mut img, physical, true);
        integrity_admitted(&img, 4096);
        rejected(&img, 4096);
    }

    #[test]
    fn an_arithmetic_parent_residual_must_match_its_actual_complete_extent_allocation() {
        let fixture = fixture("ea-volume-parent-residual", 4096);
        for number in [2, 12, 13] {
            let mut img = fixture.bytes.clone();
            let at = offset(fixture.table, number);
            let sectors = le32(&img, at + 28) + 8;
            img[at + 28..at + 32].copy_from_slice(&sectors.to_le_bytes());
            seal_inode(&mut img, &fixture, number);
            integrity_admitted(&img, 4096);
            rejected(&img, 4096);
        }
    }

    #[test]
    fn the_source_journal_sector_count_must_cover_exactly_its_mapped_storage() {
        let fixture = fixture("ea-volume-journal-sectors", 4096);
        let at = offset(fixture.table, 8);
        let correct = le32(&fixture.bytes, at + 28);
        for sectors in [correct - 8, correct + 8] {
            let mut img = fixture.bytes.clone();
            img[at + 28..at + 32].copy_from_slice(&sectors.to_le_bytes());
            seal_inode(&mut img, &fixture, 8);
            integrity_admitted(&img, 4096);
            rejected(&img, 4096);
        }
    }

    #[test]
    fn group_used_directory_counts_are_checked_separately_from_inode_and_block_free_counts() {
        let fixture = fixture("ea-volume-used-directories", 4096);
        assert_eq!(core::bytes::read_le16(&fixture.bytes, 4112), Some(2));
        for count in [1u16, 3] {
            let mut img = fixture.bytes.clone();
            img[4112..4114].copy_from_slice(&count.to_le_bytes());
            seal_group(&mut img, 0, fixture.seed);
            integrity_admitted(&img, 4096);
            rejected(&img, 4096);
        }
    }

    #[test]
    fn ordinary_sparse_and_unwritten_extents_keep_their_source_logical_and_initialization_roles() {
        let fixture = fixture("ea-volume-sparse-ordinary", 4096);
        for unwritten in [false, true] {
            let mut img = fixture.bytes.clone();
            let physical = fresh_block(&img);
            img[physical as usize * 4096..(physical as usize + 1) * 4096].fill(0x39);
            set_allocated(&mut img, physical, true);
            add_file_extent(&mut img, &fixture, 12, physical, 2, unwritten);
            let snapshot = Snapshot::from_bytes(&img);
            let all = ea_allocation::inspect(&snapshot, u32::MAX, 1, 4096).unwrap();
            let role = all.ledger().role_of(physical).unwrap();
            assert_eq!(role.kind, 4);
            assert_eq!(role.inode, 12);
            assert_eq!(role.logical, 2);
            assert_eq!(role.initialized, !unwritten);
            fsck(
                &img,
                &format!("ea-volume-sparse-ordinary-result-{unwritten}"),
            );
        }
    }

    #[test]
    fn ordinary_external_extent_nodes_are_counted_without_consuming_the_ea_node_budget() {
        let fixture = fixture("ea-volume-ordinary-depth-one", 4096);
        let mut img = fixture.bytes.clone();
        let data = fresh_block(&img);
        set_allocated(&mut img, data, true);
        add_file_extent(&mut img, &fixture, 12, data, 0, false);
        let metadata = fresh_block(&img);
        set_allocated(&mut img, metadata, true);
        let at = offset(fixture.table, 12);
        let original = img[at + 40..at + 100].to_vec();
        let seed = core::inode::inode_seed(fixture.seed, 12, le32(&img, at + 100));
        let block = &mut img[metadata as usize * 4096..(metadata as usize + 1) * 4096];
        block.fill(0);
        block[..24].copy_from_slice(&original[..24]);
        block[4..6].copy_from_slice(&340u16.to_le_bytes());
        let checksum = core::crc::crc32c(seed, &block[..4092]);
        block[4092..4096].copy_from_slice(&checksum.to_le_bytes());
        let root = &mut img[at + 40..at + 100];
        root.fill(0);
        root[..2].copy_from_slice(&0xf30au16.to_le_bytes());
        root[2..4].copy_from_slice(&1u16.to_le_bytes());
        root[4..6].copy_from_slice(&4u16.to_le_bytes());
        root[6..8].copy_from_slice(&1u16.to_le_bytes());
        root[16..20].copy_from_slice(&metadata.to_le_bytes());
        let sectors = le32(&img, at + 28) + 8;
        img[at + 28..at + 32].copy_from_slice(&sectors.to_le_bytes());
        seal_inode(&mut img, &fixture, 12);
        integrity_admitted(&img, 4096);
        let snapshot = Snapshot::from_bytes(&img);
        let all = ea_allocation::inspect(&snapshot, u32::MAX, 1, 4096).unwrap();
        assert_eq!(all.ledger().role_of(metadata).unwrap().kind, 6);
        assert_eq!(all.ledger().role_of(metadata).unwrap().inode, 12);
        let ordinary = (0..all.ordinary_count())
            .map(|i| all.ordinary(i).unwrap())
            .find(|o| o.number() == 12)
            .unwrap();
        assert_eq!(ordinary.allocated_blocks(), 2);
        assert_eq!(ordinary.usage().own, 16);
        fsck(&img, "ea-volume-ordinary-depth-one-result");
    }

    #[test]
    fn shared_external_blocks_with_only_local_values_are_reserved_once_even_without_ea_graph_entries()
     {
        let fixture = fixture("ea-volume-local-only-sharing", 4096);
        let mut img = fixture.bytes.clone();
        let physical = fresh_block(&img);
        let hash = core::xattr_hash::entry_hash(b"local", b"z").unwrap();
        let block = &mut img[physical as usize * 4096..(physical as usize + 1) * 4096];
        block.fill(0);
        block[..4].copy_from_slice(&core::xattr::MAGIC.to_le_bytes());
        block[4..8].copy_from_slice(&2u32.to_le_bytes());
        block[8..12].copy_from_slice(&1u32.to_le_bytes());
        block[12..16].copy_from_slice(&hash.to_le_bytes());
        block[32] = 5;
        block[33] = 1;
        block[34..36].copy_from_slice(&4092u16.to_le_bytes());
        block[40..44].copy_from_slice(&1u32.to_le_bytes());
        block[44..48].copy_from_slice(&hash.to_le_bytes());
        block[48..53].copy_from_slice(b"local");
        block[4092] = b'z';
        seal_external(&mut img, &fixture, physical);
        for number in [2, 11] {
            let at = offset(fixture.table, number);
            assert_eq!(le32(&img, at + 104), 0);
            let sectors = le32(&img, at + 28) + 8;
            img[at + 104..at + 108].copy_from_slice(&physical.to_le_bytes());
            img[at + 28..at + 32].copy_from_slice(&sectors.to_le_bytes());
            seal_inode(&mut img, &fixture, number);
        }
        set_allocated(&mut img, physical, true);
        integrity_admitted(&img, 4096);
        let snapshot = Snapshot::from_bytes(&img);
        let all = ea_allocation::inspect(&snapshot, u32::MAX, 1, 4096).unwrap();
        assert_eq!(
            all.integrity()
                .reference_census()
                .external_parents(physical),
            2
        );
        assert_eq!(all.integrity().reference_census().physical().len(), 3);
        assert_eq!(all.ledger().role_of(physical).unwrap().kind, 7);
        assert_eq!(
            all.ledger()
                .claims()
                .iter()
                .filter(|c| c.start == physical)
                .count(),
            1
        );
        fsck(&img, "ea-volume-local-only-sharing-result");
    }

    #[test]
    fn complete_global_ownership_uses_source_selected_backups_and_lazy_flex_group_bitmaps() {
        let mke2fs = std::env::var("MKE2FS_BIN").unwrap_or_else(|_| "mke2fs".into());
        for backup in ["", ",sparse_super", ",sparse_super2"] {
            let name = if backup.is_empty() {
                "all"
            } else {
                &backup[1..]
            };
            let path = format!("build/ea-volume-flex-{name}.img");
            let features = format!(
                "none,has_journal,extent,filetype,large_file,extra_isize,metadata_csum,ea_inode,flex_bg{backup}"
            );
            super::inline_xattr_updates::command(
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
                    "-N",
                    "128",
                    "-O",
                    &features,
                    "-G",
                    "2",
                    "-E",
                    "lazy_itable_init=0,lazy_journal_init=0",
                    &path,
                    "65536",
                ],
                false,
            );
            let img = std::fs::read(&path).unwrap();
            let _ = std::fs::remove_file(&path);
            let snapshot = Snapshot::from_bytes(&img);
            let all = ea_allocation::inspect(&snapshot, 128, 1, 0).unwrap();
            assert_eq!(all.integrity().value_count(), 0);
            assert_eq!(all.integrity().reference_census().index().group_count(), 2);
            assert_eq!(all.ordinary_count(), 2);
            assert_eq!(
                core::bytes::read_le16(
                    &img,
                    4096 + core::superblock::descriptor_length(&img[1024..2048]).unwrap() + 18
                )
                .unwrap()
                    & 1,
                1
            );
            let total: u64 = all
                .ledger()
                .claims()
                .iter()
                .map(|c| u64::from(c.length))
                .sum();
            assert_eq!(total, u64::from(le32(&img, 1028) - le32(&img, 1036)));
            fsck(&img, &format!("ea-volume-flex-{name}-result"));
        }
    }

    #[test]
    fn global_allocation_budget_rejections_never_publish_an_incomplete_source_prefix() {
        let fixture = fixture("ea-volume-budgets", 4096);
        let snapshot = Snapshot::from_bytes(&fixture.bytes);
        assert!(ea_allocation::inspect(&snapshot, fixture.inodes, 1, 4096).is_some());
        assert!(ea_allocation::inspect(&snapshot, fixture.inodes - 1, 1, 4096).is_none());
        assert!(ea_allocation::inspect(&snapshot, u32::MAX, 0, 4096).is_none());
        assert!(ea_allocation::inspect(&snapshot, u32::MAX, 1, 4095).is_none());
        assert!(ea_allocation::inspect(&snapshot, u32::MAX, 4097, 4096).is_none());
    }
}

// Native EA-enabled namespace tests execute emitted code on Linux-created
// images. They do not discharge the formal source and topology obligations.
mod ea_namespace_admission {
    use core::{ea_allocation, ea_namespace, snapshot::Snapshot};

    use super::{
        ea_inode_values::{fixture, fixture_with_features, offset, seal_raw},
        inline_xattr_updates::command,
        *,
    };

    #[derive(Clone)]
    struct Record {
        at: usize,
        next: usize,
        target: u32,
        name: Vec<u8>,
    }
    fn data_blocks(img: &[u8], table: u32, number: u32) -> Vec<u32> {
        let at = offset(table, number);
        let count = le32(img, at + 4) as usize / 4096;
        let root = &img[at + 40..at + 100];
        assert_eq!(core::bytes::read_le16(root, 6), Some(0));
        let mut blocks = vec![0; count];
        for i in 0..core::bytes::read_le16(root, 2).unwrap() as usize {
            let extent = core::extent::parse(root, 12 + 12 * i, le32(img, 1028)).unwrap();
            assert!(extent.initialized);
            for j in 0..extent.length {
                let logical = (extent.logical + j) as usize;
                if logical < blocks.len() {
                    assert_eq!(blocks[logical], 0);
                    blocks[logical] = extent.physical + j;
                }
            }
        }
        assert!(blocks.iter().all(|b| *b > 0));
        blocks
    }
    fn records(img: &[u8], physical: u32) -> Vec<Record> {
        let raw = &img[physical as usize * 4096..(physical as usize + 1) * 4096];
        let mut at = 0;
        let mut result = Vec::new();
        while at < 4084 {
            let next = at + core::bytes::read_le16(raw, at + 4).unwrap() as usize;
            let length = raw[at + 6] as usize;
            assert!(next > at && next <= 4084 && at + 8 + length <= next);
            result.push(Record {
                at,
                next,
                target: le32(raw, at),
                name: raw[at + 8..at + 8 + length].to_vec(),
            });
            at = next;
        }
        assert_eq!(at, 4084);
        result
    }
    fn location(img: &[u8], table: u32, number: u32, name: &[u8]) -> (u32, usize) {
        for physical in data_blocks(img, table, number) {
            if let Some(record) = records(img, physical)
                .into_iter()
                .find(|r| r.target != 0 && r.name == name)
            {
                return (physical, record.at);
            }
        }
        panic!("missing source directory key {name:?}");
    }
    fn seal_inode(img: &mut [u8], table: u32, number: u32, seed: u32) {
        let at = offset(table, number);
        seal_raw(&mut img[at..at + 256], number, seed);
    }
    fn links(img: &mut [u8], table: u32, number: u32, count: u16, seed: u32) {
        let at = offset(table, number);
        img[at + 26..at + 28].copy_from_slice(&count.to_le_bytes());
        seal_inode(img, table, number, seed);
    }
    fn seal_directory(img: &mut [u8], table: u32, number: u32, physical: u32, seed: u32) {
        let seed = core::inode::inode_seed(seed, number, le32(img, offset(table, number) + 100));
        let at = physical as usize * 4096;
        let hash = core::crc::crc32c(seed, &img[at..at + 4084]);
        img[at + 4092..at + 4096].copy_from_slice(&hash.to_le_bytes());
    }
    fn seal_super(img: &mut [u8]) {
        let hash = core::crc::crc32c(0xffffffff, &img[1024..2044]);
        img[2044..2048].copy_from_slice(&hash.to_le_bytes());
    }
    fn append_named(
        img: &mut [u8],
        table: u32,
        number: u32,
        target: u32,
        kind: u8,
        name: &[u8],
        seed: u32,
    ) {
        assert!(!name.is_empty() && name.len() <= 255);
        let physical = data_blocks(img, table, number)[0];
        let previous = records(img, physical).pop().unwrap();
        assert_eq!(previous.next, 4084);
        let minimum = (8 + previous.name.len() + 3) / 4 * 4;
        let next = previous.at + minimum;
        assert!(next + (8 + name.len() + 3) / 4 * 4 <= 4084);
        let at = physical as usize * 4096;
        let raw = &mut img[at..at + 4096];
        raw[previous.at + 4..previous.at + 6].copy_from_slice(&(minimum as u16).to_le_bytes());
        raw[next..4084].fill(0);
        raw[next..next + 4].copy_from_slice(&target.to_le_bytes());
        raw[next + 4..next + 6].copy_from_slice(&((4084 - next) as u16).to_le_bytes());
        raw[next + 6] = name.len() as u8;
        raw[next + 7] = kind;
        raw[next + 8..next + 8 + name.len()].copy_from_slice(name);
        seal_directory(img, table, number, physical, seed);
    }
    fn allocation_admitted(img: &[u8], bytes: u64) {
        let snapshot = Snapshot::from_bytes(img);
        assert!(
            ea_allocation::inspect(&snapshot, u32::MAX, 8, bytes).is_some(),
            "physical allocation remains valid"
        );
    }
    fn rejected(img: &[u8], bytes: u64) {
        allocation_admitted(img, bytes);
        let snapshot = Snapshot::from_bytes(img);
        assert!(ea_namespace::inspect(&snapshot, u32::MAX, 8, bytes).is_none());
    }
    fn fsck(img: &[u8], prefix: &str) {
        let path = format!("build/{prefix}.img");
        std::fs::write(&path, img).unwrap();
        let fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        command(&fsck, &["-fn", &path], false);
        let _ = std::fs::remove_file(path);
    }
    fn seal_index(raw: &mut [u8], first: usize, seed: u32) {
        let count = core::bytes::read_le16(raw, first + 2).unwrap() as usize;
        let limit = core::bytes::read_le16(raw, first).unwrap() as usize;
        let tail = first + limit * 8;
        let prefix = core::crc::crc32c(seed, &raw[..first + count * 8]);
        let reserved = core::crc::crc32c(prefix, &raw[tail..tail + 4]);
        let hash = core::crc::crc32c(reserved, &[0, 0, 0, 0]);
        raw[tail + 4..tail + 8].copy_from_slice(&hash.to_le_bytes());
    }
    fn indexed_image(prefix: &str) -> Vec<u8> {
        let path = format!("build/{prefix}.img");
        let empty = format!("build/{prefix}-empty.bin");
        let script = format!("build/{prefix}-commands.txt");
        let mkfs = std::env::var("MKE2FS_BIN").unwrap_or_else(|_| "mke2fs".into());
        let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
        let fsck = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".into());
        command(
            &mkfs,
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
                "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum,dir_index,ea_inode",
                "-E",
                "lazy_itable_init=0,lazy_journal_init=0",
                &path,
                "16384",
            ],
            false,
        );
        std::fs::write(&empty, []).unwrap();
        let mut requests = String::from("mkdir /indexed\n");
        for i in 0..300 {
            requests += &format!("write {empty} /indexed/{i:04}-{}\n", "x".repeat(210));
        }
        std::fs::write(&script, requests).unwrap();
        command(&debugfs, &["-w", "-f", &script, &path], false);
        command(&fsck, &["-fyD", &path], true);
        command(&fsck, &["-fn", &path], false);
        let img = std::fs::read(&path).unwrap();
        assert_ne!(le32(&img, offset(le32(&img, 4104), 12) + 32) & 0x1000, 0);
        for file in [&path, &empty, &script] {
            let _ = std::fs::remove_file(file);
        }
        img
    }

    #[test]
    fn complete_ea_namespace_retains_rooted_names_and_ea_payloads_under_all_seed_descriptor_profiles()
     {
        for wide in [false, true] {
            for stored in [false, true] {
                let fixture = fixture_with_features(
                    &format!("ea-namespace-profile-{wide}-{stored}"),
                    4096,
                    wide,
                    stored,
                );
                let snapshot = Snapshot::from_bytes(&fixture.bytes);
                let namespace = ea_namespace::inspect(&snapshot, fixture.inodes, 1, 4096).unwrap();
                assert_eq!(namespace.parent(2), Some(2));
                assert_eq!(namespace.parent(11), Some(2));
                assert_eq!(namespace.depth(2), Some(0));
                assert_eq!(namespace.depth(11), Some(1));
                for (name, target, kind) in [
                    (b"first".as_slice(), 12, 1),
                    (b"second".as_slice(), 13, 1),
                    (b"lost+found".as_slice(), 11, 2),
                ] {
                    let entry = namespace.lookup(2, name).unwrap();
                    assert_eq!(
                        (entry.identity().0, entry.identity().1, entry.identity().3),
                        (2, target, kind)
                    );
                    assert_eq!(entry.name(), name);
                }
                assert_eq!(namespace.lookup(11, b"..").unwrap().identity().1, 2);
                assert_eq!(namespace.index().len(), 7);
                assert_eq!(namespace.index().directory_count(), 2);
                let mut total_blocks = 0;
                for ordinal in 0..namespace.index().directory_count() {
                    let directory = namespace.index().directory(ordinal).unwrap();
                    let blocks = data_blocks(&fixture.bytes, fixture.table, directory.number());
                    assert_eq!(directory.block_count() as usize, blocks.len());
                    assert_eq!(directory.raw_blocks().len(), blocks.len());
                    for (logical, physical) in blocks.iter().enumerate() {
                        assert_eq!(directory.physical_block(logical as u32), Some(*physical));
                        let at = *physical as usize * 4096;
                        assert_eq!(
                            directory.raw_blocks()[logical],
                            &fixture.bytes[at..at + 4096]
                        );
                    }
                    total_blocks += directory.block_count();
                }
                assert_eq!(namespace.index().block_count(), total_blocks);
                assert!(
                    namespace
                        .index()
                        .directory(namespace.index().directory_count())
                        .is_none()
                );
                assert_eq!(namespace.lookup(2, b".").unwrap().location(), (0, 0));
                assert_eq!(namespace.lookup(2, b"..").unwrap().location(), (0, 1));
                assert_eq!(
                    namespace
                        .allocation()
                        .integrity()
                        .value(0)
                        .unwrap()
                        .as_slice(),
                    fixture.value
                );
                assert!(
                    namespace.index().nodes().get(14).is_none(),
                    "EA inode is not a namespace target"
                );
                for number in [0, 8, 12, 13, 14, u32::MAX] {
                    assert!(namespace.parent(number).is_none());
                    assert!(namespace.depth(number).is_none());
                }
                assert!(namespace.lookup(2, b"First").is_none());
                assert!(namespace.lookup(2, b"firs").is_none());
                assert!(namespace.lookup(8, b".").is_none());
                assert!(namespace.lookup(14, b".").is_none());
                assert!(namespace.index().get(namespace.index().len()).is_none());
            }
        }
    }

    #[test]
    fn lookup_generation_is_derived_from_the_exact_source_target_inode() {
        let fixture = fixture("ea-namespace-generation", 4096);
        let mut img = fixture.bytes.clone();
        let at = offset(fixture.table, 12);
        let generation = le32(&img, at + 100).wrapping_add(0x8172_3401);
        img[at + 100..at + 104].copy_from_slice(&generation.to_le_bytes());
        seal_inode(&mut img, fixture.table, 12, fixture.seed);
        allocation_admitted(&img, 4096);
        let snapshot = Snapshot::from_bytes(&img);
        let namespace = ea_namespace::inspect(&snapshot, u32::MAX, 1, 4096).unwrap();
        assert_eq!(
            namespace.lookup(2, b"first").unwrap().identity(),
            (2, 12, generation, 1)
        );
        assert_eq!(
            namespace.index().nodes().get(12).unwrap().generation,
            generation
        );
    }

    #[test]
    fn regular_hard_links_compare_complete_byte_names_including_non_utf8_and_maximum_length() {
        let fixture = fixture("ea-namespace-hardlinks", 4096);
        let mut img = fixture.bytes.clone();
        let long = vec![b'x'; 255];
        for name in [
            b"first-extra".as_slice(),
            &[0xff, 0x80, b'x'],
            long.as_slice(),
        ] {
            append_named(&mut img, fixture.table, 2, 12, 1, name, fixture.seed);
        }
        links(&mut img, fixture.table, 12, 4, fixture.seed);
        fsck(&img, "ea-namespace-hardlinks-result");
        let snapshot = Snapshot::from_bytes(&img);
        let namespace = ea_namespace::inspect(&snapshot, u32::MAX, 1, 4096).unwrap();
        for name in [
            b"first".as_slice(),
            b"first-extra".as_slice(),
            &[0xff, 0x80, b'x'],
            long.as_slice(),
        ] {
            assert_eq!(namespace.lookup(2, name).unwrap().identity().1, 12);
        }
        assert!(namespace.lookup(2, b"first-extr").is_none());
        assert!(namespace.lookup(2, &[0xff, 0x80]).is_none());
        assert!(namespace.lookup(2, &long[..254]).is_none());
    }

    #[test]
    fn deleted_records_do_not_hide_a_later_live_source_entry_or_create_lookup_keys() {
        let fixture = fixture("ea-namespace-dead-record", 4096);
        let mut img = fixture.bytes.clone();
        append_named(&mut img, fixture.table, 2, 0, 0, b"dead", fixture.seed);
        append_named(
            &mut img,
            fixture.table,
            2,
            12,
            1,
            b"after-dead",
            fixture.seed,
        );
        links(&mut img, fixture.table, 12, 2, fixture.seed);
        let snapshot = Snapshot::from_bytes(&img);
        let namespace = ea_namespace::inspect(&snapshot, u32::MAX, 1, 4096).unwrap();
        assert!(namespace.lookup(2, b"dead").is_none());
        assert_eq!(namespace.lookup(2, b"after-dead").unwrap().identity().1, 12);
        assert_eq!(namespace.lookup(2, b"first").unwrap().identity().1, 12);
    }

    #[test]
    fn directory_entries_cannot_expose_ea_journal_reserved_or_unallocated_inode_targets() {
        let fixture = fixture("ea-namespace-targets", 4096);
        let (physical, at) = location(&fixture.bytes, fixture.table, 2, b"first");
        for target in [14u32, 8, 5, 15] {
            let mut img = fixture.bytes.clone();
            let start = physical as usize * 4096 + at;
            img[start..start + 4].copy_from_slice(&target.to_le_bytes());
            seal_directory(&mut img, fixture.table, 2, physical, fixture.seed);
            rejected(&img, 4096);
        }
    }

    #[test]
    fn directory_entry_types_must_match_the_source_ordinary_inode_type() {
        let fixture = fixture("ea-namespace-types", 4096);
        for (name, wrong) in [(b"first".as_slice(), 2u8), (b"lost+found".as_slice(), 1u8)] {
            let mut img = fixture.bytes.clone();
            let (physical, at) = location(&img, fixture.table, 2, name);
            img[physical as usize * 4096 + at + 7] = wrong;
            seal_directory(&mut img, fixture.table, 2, physical, fixture.seed);
            rejected(&img, 4096);
        }
    }

    #[test]
    fn every_directory_block_checksum_is_checked_even_when_preallocated_records_are_empty() {
        let fixture = fixture("ea-namespace-empty-checksum", 4096);
        let blocks = data_blocks(&fixture.bytes, fixture.table, 11);
        assert!(blocks.len() > 1);
        let mut img = fixture.bytes.clone();
        img[*blocks.last().unwrap() as usize * 4096 + 4092] ^= 0x80;
        rejected(&img, 4096);
    }

    #[test]
    fn resealed_record_lengths_cannot_skip_or_overrun_the_complete_directory_chain() {
        let fixture = fixture("ea-namespace-record-length", 4096);
        let (physical, at) = location(&fixture.bytes, fixture.table, 2, b"first");
        for length in [0u16, 10, 4092] {
            let mut img = fixture.bytes.clone();
            let start = physical as usize * 4096 + at;
            img[start + 4..start + 6].copy_from_slice(&length.to_le_bytes());
            seal_directory(&mut img, fixture.table, 2, physical, fixture.seed);
            rejected(&img, 4096);
        }
    }

    #[test]
    fn complete_full_key_uniqueness_rejects_duplicate_names_with_distinct_live_targets() {
        let fixture = fixture("ea-namespace-duplicate", 4096);
        let mut img = fixture.bytes.clone();
        let (physical, at) = location(&img, fixture.table, 2, b"second");
        let start = physical as usize * 4096 + at;
        img[start + 6] = 5;
        img[start + 8..start + 13].copy_from_slice(b"first");
        seal_directory(&mut img, fixture.table, 2, physical, fixture.seed);
        rejected(&img, 4096);
    }

    #[test]
    fn live_names_cannot_contain_a_path_separator_or_nul_even_after_crc_resealing() {
        let fixture = fixture("ea-namespace-invalid-names", 4096);
        let (physical, at) = location(&fixture.bytes, fixture.table, 2, b"first");
        for byte in [b'/', 0] {
            let mut img = fixture.bytes.clone();
            img[physical as usize * 4096 + at + 9] = byte;
            seal_directory(&mut img, fixture.table, 2, physical, fixture.seed);
            rejected(&img, 4096);
        }
    }

    #[test]
    fn regular_and_directory_link_counts_equal_complete_source_namespace_references() {
        let fixture = fixture("ea-namespace-link-count", 4096);
        for (number, count) in [(12u32, 2u16), (2, 4)] {
            let mut img = fixture.bytes.clone();
            links(&mut img, fixture.table, number, count, fixture.seed);
            rejected(&img, 4096);
        }
    }

    #[test]
    fn an_allocated_regular_inode_without_a_directory_reference_is_not_a_valid_namespace() {
        let fixture = fixture("ea-namespace-unreferenced-file", 4096);
        let mut img = fixture.bytes.clone();
        let (physical, at) = location(&img, fixture.table, 2, b"first");
        img[physical as usize * 4096 + at..physical as usize * 4096 + at + 4].fill(0);
        seal_directory(&mut img, fixture.table, 2, physical, fixture.seed);
        rejected(&img, 4096);
    }

    #[test]
    fn dot_and_dotdot_are_required_in_their_first_block_source_positions() {
        let fixture = fixture("ea-namespace-dot-positions", 4096);
        let physical = data_blocks(&fixture.bytes, fixture.table, 2)[0];
        let start = physical as usize * 4096;
        for variant in 0..3 {
            let mut img = fixture.bytes.clone();
            if variant < 2 {
                let at = if variant == 0 { 0 } else { 12 };
                img[start + at..start + at + 4].fill(0);
                links(&mut img, fixture.table, 2, 2, fixture.seed);
            } else {
                img[start + 6] = 2;
                img[start + 8..start + 10].copy_from_slice(b"..");
                img[start + 18] = 1;
                img[start + 20] = b'.';
            }
            seal_directory(&mut img, fixture.table, 2, physical, fixture.seed);
            rejected(&img, 4096);
        }
    }

    #[test]
    fn dot_must_target_its_own_directory_when_all_reference_counts_are_repaired() {
        let fixture = fixture("ea-namespace-dot-target", 4096);
        let mut img = fixture.bytes.clone();
        let physical = data_blocks(&img, fixture.table, 2)[0];
        img[physical as usize * 4096..physical as usize * 4096 + 4]
            .copy_from_slice(&11u32.to_le_bytes());
        links(&mut img, fixture.table, 2, 2, fixture.seed);
        links(&mut img, fixture.table, 11, 3, fixture.seed);
        seal_directory(&mut img, fixture.table, 2, physical, fixture.seed);
        rejected(&img, 4096);
    }

    #[test]
    fn dotdot_parent_must_match_the_unique_named_parent_after_link_counts_are_repaired() {
        let fixture = fixture("ea-namespace-parent-mismatch", 4096);
        let mut img = fixture.bytes.clone();
        let physical = data_blocks(&img, fixture.table, 11)[0];
        img[physical as usize * 4096 + 12..physical as usize * 4096 + 16]
            .copy_from_slice(&11u32.to_le_bytes());
        links(&mut img, fixture.table, 2, 2, fixture.seed);
        links(&mut img, fixture.table, 11, 3, fixture.seed);
        seal_directory(&mut img, fixture.table, 11, physical, fixture.seed);
        rejected(&img, 4096);
    }

    #[test]
    fn a_directory_cannot_have_two_named_incoming_links_even_with_exact_stored_counts() {
        let fixture = fixture("ea-namespace-directory-hardlink", 4096);
        let mut img = fixture.bytes.clone();
        append_named(
            &mut img,
            fixture.table,
            2,
            11,
            2,
            b"dir-alias",
            fixture.seed,
        );
        links(&mut img, fixture.table, 11, 3, fixture.seed);
        rejected(&img, 4096);
    }

    #[test]
    fn a_named_edge_to_root_is_rejected_even_when_its_complete_reference_count_matches() {
        let fixture = fixture("ea-namespace-named-root", 4096);
        let mut img = fixture.bytes.clone();
        append_named(
            &mut img,
            fixture.table,
            11,
            2,
            2,
            b"root-alias",
            fixture.seed,
        );
        links(&mut img, fixture.table, 2, 4, fixture.seed);
        rejected(&img, 4096);
    }

    #[test]
    fn locally_consistent_disconnected_directory_cycle_does_not_reach_the_root() {
        let fixture = fixture("ea-namespace-disconnected-cycle", 4096);
        let mut img = fixture.bytes.clone();
        let (root, lost_at) = location(&img, fixture.table, 2, b"lost+found");
        img[root as usize * 4096 + lost_at..root as usize * 4096 + lost_at + 4].fill(0);
        let lost = data_blocks(&img, fixture.table, 11)[0];
        img[lost as usize * 4096 + 12..lost as usize * 4096 + 16]
            .copy_from_slice(&11u32.to_le_bytes());
        append_named(&mut img, fixture.table, 11, 11, 2, b"loop", fixture.seed);
        links(&mut img, fixture.table, 2, 2, fixture.seed);
        links(&mut img, fixture.table, 11, 3, fixture.seed);
        seal_directory(&mut img, fixture.table, 2, root, fixture.seed);
        seal_directory(&mut img, fixture.table, 11, lost, fixture.seed);
        allocation_admitted(&img, 4096);
        let snapshot = Snapshot::from_bytes(&img);
        let allocation = ea_allocation::inspect(&snapshot, u32::MAX, 1, 4096).unwrap();
        let index = core::ea_directory_index::build(&allocation).unwrap();
        assert!(index.lookup(2, b"lost+found").is_none());
        assert_eq!(index.lookup(11, b"..").unwrap().identity().1, 11);
        assert_eq!(index.lookup(11, b"loop").unwrap().identity().1, 11);
        assert_eq!(
            (0..index.len())
                .filter(|i| index.get(*i).unwrap().identity().1 == 11)
                .count(),
            3
        );
        assert!(
            ea_namespace::inspect(&snapshot, u32::MAX, 1, 4096).is_none(),
            "cycle fails beyond local entry/count checks"
        );
    }

    #[test]
    fn linux_nested_directories_and_regular_hard_links_keep_exact_parent_depths() {
        let fixture = fixture("ea-namespace-nested", 4096);
        let path = "build/ea-namespace-nested-work.img";
        let script = "build/ea-namespace-nested-commands.txt";
        std::fs::write(path, &fixture.bytes).unwrap();
        std::fs::write(script, "mkdir /a\nmkdir /a/b\nln /first /a/b/hard\n").unwrap();
        let debugfs = std::env::var("DEBUGFS_BIN").unwrap_or_else(|_| "debugfs".into());
        command(&debugfs, &["-w", "-f", script, path], false);
        let mut img = std::fs::read(path).unwrap();
        links(&mut img, fixture.table, 12, 2, fixture.seed);
        fsck(&img, "ea-namespace-nested-result");
        let snapshot = Snapshot::from_bytes(&img);
        let namespace = ea_namespace::inspect(&snapshot, u32::MAX, 1, 4096).unwrap();
        let a = namespace.lookup(2, b"a").unwrap().identity().1;
        let b = namespace.lookup(a, b"b").unwrap().identity().1;
        assert_eq!(namespace.parent(a), Some(2));
        assert_eq!(namespace.parent(b), Some(a));
        assert_eq!(namespace.depth(a), Some(1));
        assert_eq!(namespace.depth(b), Some(2));
        assert_eq!(namespace.lookup(b, b"hard").unwrap().identity().1, 12);
        assert_eq!(namespace.lookup(2, b"first").unwrap().identity().1, 12);
        for file in [path, script] {
            let _ = std::fs::remove_file(file);
        }
    }

    #[test]
    fn actual_linux_htrees_bind_lookup_names_to_source_hash_seed_and_leaf_ranges() {
        let img = indexed_image("ea-namespace-indexed");
        let table = le32(&img, 4104);
        let seed = core::superblock::metadata_checksum_seed(&img[1024..2048]).unwrap();
        let physical = data_blocks(&img, table, 12)[0];
        let inode_seed = core::inode::inode_seed(seed, 12, le32(&img, offset(table, 12) + 100));
        let start = physical as usize * 4096;
        assert!(core::bytes::read_le16(&img, start + 34).unwrap() > 1);
        let snapshot = Snapshot::from_bytes(&img);
        let namespace = ea_namespace::inspect(&snapshot, u32::MAX, 1, 0).unwrap();
        assert_eq!(namespace.parent(12), Some(2));
        for i in 0..300 {
            let name = format!("{i:04}-{}", "x".repeat(210));
            assert_eq!(
                namespace.lookup(12, name.as_bytes()).unwrap().identity().1,
                13 + i
            );
        }
        assert!(namespace.lookup(12, b"missing").is_none());
        for duplicate in [false, true] {
            let mut wrong = img.clone();
            let left = le32(&wrong, start + 36);
            let right = le32(&wrong, start + 44);
            if duplicate {
                wrong[start + 44..start + 48].copy_from_slice(&left.to_le_bytes());
            } else {
                wrong[start + 36..start + 40].copy_from_slice(&right.to_le_bytes());
                wrong[start + 44..start + 48].copy_from_slice(&left.to_le_bytes());
            }
            seal_index(&mut wrong[start..start + 4096], 32, inode_seed);
            rejected(&wrong, 0);
        }
        let mut wrong_seed = img.clone();
        wrong_seed[1260] ^= 1;
        seal_super(&mut wrong_seed);
        rejected(&wrong_seed, 0);
    }

    #[test]
    fn actual_source_largedir_flag_admits_depth_two_and_rejects_missing_flag_or_depth_three() {
        let img = indexed_image("ea-namespace-largedir");
        let table = le32(&img, 4104);
        let physical = data_blocks(&img, table, 12)[0];
        let blocks = le32(&img, offset(table, 12) + 4) / 4096;
        let seed = core::superblock::metadata_checksum_seed(&img[1024..2048]).unwrap();
        let inode_seed = core::inode::inode_seed(seed, 12, le32(&img, offset(table, 12) + 100));
        let deep = super::htree_indexes::deepen_indexed_image(
            &img,
            table,
            physical as usize,
            12,
            blocks,
            inode_seed,
        );
        fsck(&deep, "ea-namespace-largedir-result");
        let snapshot = Snapshot::from_bytes(&deep);
        let namespace = ea_namespace::inspect(&snapshot, u32::MAX, 1, 0).unwrap();
        for i in 0..300 {
            let name = format!("{i:04}-{}", "x".repeat(210));
            assert_eq!(
                namespace.lookup(12, name.as_bytes()).unwrap().identity().1,
                13 + i
            );
        }
        let mut missing = deep.clone();
        let flags = le32(&missing, 1120) & !0x4000;
        missing[1120..1124].copy_from_slice(&flags.to_le_bytes());
        seal_super(&mut missing);
        rejected(&missing, 0);
        let mut too_deep = deep.clone();
        let at = physical as usize * 4096;
        too_deep[at + 30] = 3;
        seal_index(&mut too_deep[at..at + 4096], 32, inode_seed);
        rejected(&too_deep, 0);
    }

    #[test]
    fn dir_nlink_unknown_directory_marker_never_weakens_regular_reference_counts() {
        let fixture = fixture("ea-namespace-dir-nlink", 4096);
        let mut img = fixture.bytes.clone();
        let flags = le32(&img, 1124) | 0x20;
        img[1124..1128].copy_from_slice(&flags.to_le_bytes());
        seal_super(&mut img);
        links(&mut img, fixture.table, 2, 1, fixture.seed);
        links(&mut img, fixture.table, 11, 1, fixture.seed);
        let snapshot = Snapshot::from_bytes(&img);
        let namespace = ea_namespace::inspect(&snapshot, u32::MAX, 1, 4096).unwrap();
        assert_eq!(namespace.parent(11), Some(2));
        let mut no_feature = img.clone();
        no_feature[1124..1128].copy_from_slice(&(flags & !0x20).to_le_bytes());
        seal_super(&mut no_feature);
        rejected(&no_feature, 4096);
        let mut no_regular_reference = img.clone();
        let (physical, at) = location(&no_regular_reference, fixture.table, 2, b"first");
        let start = physical as usize * 4096 + at;
        no_regular_reference[start..start + 4].fill(0);
        seal_directory(
            &mut no_regular_reference,
            fixture.table,
            2,
            physical,
            fixture.seed,
        );
        rejected(&no_regular_reference, 4096);
        append_named(
            &mut img,
            fixture.table,
            2,
            12,
            1,
            b"file-hard",
            fixture.seed,
        );
        rejected(&img, 4096);
    }

    #[test]
    fn namespace_budgets_never_return_a_silently_partial_directory_or_inode_catalogue() {
        let fixture = fixture("ea-namespace-budgets", 4096);
        let snapshot = Snapshot::from_bytes(&fixture.bytes);
        assert!(ea_namespace::inspect(&snapshot, fixture.inodes, 1, 4096).is_some());
        assert!(ea_namespace::inspect(&snapshot, fixture.inodes - 1, 1, 4096).is_none());
        assert!(ea_namespace::inspect(&snapshot, fixture.inodes, 0, 4096).is_none());
        assert!(ea_namespace::inspect(&snapshot, fixture.inodes, 1, 4095).is_none());
        let mut huge = fixture.bytes.clone();
        let at = offset(fixture.table, 11);
        huge[at + 4..at + 8].copy_from_slice(&(4097u32 * 4096).to_le_bytes());
        seal_inode(&mut huge, fixture.table, 11, fixture.seed);
        rejected(&huge, 4096);
    }
}
