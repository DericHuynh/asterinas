// SPDX-License-Identifier: MPL-2.0
//! Regressions for wide filesystem geometry with legacy LE32 inode pointers.
//! These tests exercise the linked library and real Snapshot APIs.
#![forbid(unsafe_code)]

use verified_ext4::legacy_map::{self, Error, Root};
use verified_ext4::snapshot::Snapshot;

const BLOCK_SIZES: [u32; 7] = [1024, 2048, 4096, 8192, 16384, 32768, 65536];
const WIDE_COUNTS: [u64; 5] = [
    u32::MAX as u64,
    1u64 << 32,
    (1u64 << 32) + 1,
    1u64 << 48,
    u64::MAX,
];

fn inode(size: u64, pointers: &[(usize, u32)]) -> Vec<u8> {
    let mut raw = vec![0; 128];
    raw[0..2].copy_from_slice(&0x8180u16.to_le_bytes());
    raw[4..8].copy_from_slice(&(size as u32).to_le_bytes());
    raw[26..28].copy_from_slice(&1u16.to_le_bytes());
    raw[108..112].copy_from_slice(&((size >> 32) as u32).to_le_bytes());
    for &(index, pointer) in pointers {
        assert!(index < 15);
        raw[40 + 4 * index..44 + 4 * index].copy_from_slice(&pointer.to_le_bytes());
    }
    raw
}

fn parsed(raw: &[u8], block_bytes: u32, blocks: u64) -> Root<'_> {
    match legacy_map::parse(raw, block_bytes, blocks, false, false, block_bytes, false) {
        Ok(root) => root,
        Err(Error::Geometry) => panic!("geometry rejected: block size {block_bytes}, count {blocks}"),
        Err(_) => panic!("legacy inode rejected: block size {block_bytes}, count {blocks}"),
    }
}

fn word(image: &mut [u8], block_bytes: u32, block: u32, index: usize, value: u32) {
    let at = block as usize * block_bytes as usize + index * 4;
    image[at..at + 4].copy_from_slice(&value.to_le_bytes());
}

#[test]
fn wide_filesystem_counts_are_preserved() {
    for block_bytes in BLOCK_SIZES {
        let raw = inode(7, &[(0, 1)]);
        for blocks in WIDE_COUNTS {
            let root = parsed(&raw, block_bytes, blocks);
            assert_eq!(root.geometry(), (block_bytes, blocks));
            assert_eq!(root.size(), 7);
            assert_eq!(root.mode(), 0x8000);
        }
    }
}

#[test]
fn largest_legacy_pointer_stays_a_u32_address() {
    let raw = inode(1, &[(0, u32::MAX)]);
    for block_bytes in BLOCK_SIZES {
        assert!(matches!(
            legacy_map::parse(&raw, block_bytes, u32::MAX as u64, false, false, block_bytes, false),
            Err(Error::OutOfRange)
        ));
        for blocks in WIDE_COUNTS.into_iter().skip(1) {
            assert_eq!(parsed(&raw, block_bytes, blocks).geometry(), (block_bytes, blocks));
        }
    }
}

#[test]
fn small_snapshot_rejects_wide_volume_before_low_pointer_use() {
    for block_bytes in BLOCK_SIZES {
        let raw = inode(7, &[(0, 1)]);
        let image = vec![0x5a; 16 * block_bytes as usize];
        let source = Snapshot::from_bytes(&image);
        for blocks in WIDE_COUNTS.into_iter().skip(1) {
            let root = parsed(&raw, block_bytes, blocks);
            assert!(matches!(root.lookup(&source, 0), Err(Error::Source)));
            assert!(matches!(root.lookup(&source, 1u64 << 32), Err(Error::Source)));
            assert!(matches!(root.collect(&source, 8, 8), Err(Error::Source)));
            assert!(matches!(root.read(&source, 0, 7), Err(Error::Source)));
        }
    }
}

#[test]
fn budgets_and_empty_reads_keep_existing_priority() {
    let raw = inode(7, &[(0, 1)]);
    let root = parsed(&raw, 4096, u64::MAX);
    let image = vec![0; 4096];
    let source = Snapshot::from_bytes(&image);
    assert!(matches!(root.collect(&source, 65537, 8), Err(Error::Budget)));
    assert!(matches!(root.collect(&source, 8, 65537), Err(Error::Budget)));
    assert!(matches!(root.read(&source, 0, 65537), Err(Error::Budget)));
    assert!(matches!(root.read(&source, 0, 0), Ok(bytes) if bytes.is_empty()));
    assert!(matches!(root.read(&source, 7, 8), Ok(bytes) if bytes.is_empty()));
    assert!(matches!(root.read(&source, u64::MAX, 8), Ok(bytes) if bytes.is_empty()));
}

#[test]
fn neighboring_words_are_separate_little_endian_pointers() {
    let block_bytes = 4096;
    let mut raw = inode(block_bytes as u64 + 1, &[]);
    raw[40..48].copy_from_slice(&0x00000001_00000005u64.to_le_bytes());
    let root = parsed(&raw, block_bytes, 16);
    let mut image = vec![0; 16 * block_bytes as usize];
    image[block_bytes as usize..2 * block_bytes as usize].fill(0x11);
    image[5 * block_bytes as usize..6 * block_bytes as usize].fill(0x55);
    let source = Snapshot::from_bytes(&image);
    assert!(matches!(root.lookup(&source, 0), Ok(m) if m.physical == Some(5) && m.metadata.is_empty()));
    assert!(matches!(root.lookup(&source, 1), Ok(m) if m.physical == Some(1) && m.metadata.is_empty()));
    match root.read(&source, 0, block_bytes as usize + 1) {
        Ok(bytes) => {
            assert_eq!(bytes.len(), block_bytes as usize + 1);
            assert!(bytes[..block_bytes as usize].iter().all(|&b| b == 0x55));
            assert_eq!(bytes[block_bytes as usize], 0x11);
        }
        Err(_) => panic!("adjacent legacy words did not read"),
    }
}

#[test]
fn sparse_collection_retains_allocations_beyond_eof() {
    for block_bytes in BLOCK_SIZES {
        let raw = inode(1, &[(0, 1), (4, 2), (12, 3)]);
        let root = parsed(&raw, block_bytes, 16);
        let mut image = vec![0; 16 * block_bytes as usize];
        image[block_bytes as usize] = 0x37;
        word(&mut image, block_bytes, 3, 0, 4);
        let source = Snapshot::from_bytes(&image);
        assert!(matches!(root.read(&source, 0, 32), Ok(bytes) if bytes == [0x37]));
        assert!(matches!(root.lookup(&source, 4), Ok(m) if m.physical == Some(2)));
        assert!(matches!(root.lookup(&source, 12), Ok(m) if m.physical == Some(4) && m.metadata == [3]));
        match root.collect(&source, 1, 3) {
            Ok(collection) => {
                let mut data: Vec<_> = collection.data.iter().map(|d| (d.logical, d.physical)).collect();
                data.sort_unstable();
                assert_eq!(data, [(0, 1), (4, 2), (12, 4)]);
                assert_eq!(collection.metadata, [3]);
            }
            Err(_) => panic!("bounded sparse collection rejected"),
        }
    }
}

#[test]
fn logical_file_block_domain_remains_u32() {
    for block_bytes in BLOCK_SIZES {
        assert!(matches!(legacy_map::path(block_bytes, 1u64 << 32), Err(Error::OutOfRange)));
        assert!(matches!(legacy_map::path(block_bytes, u64::MAX), Err(Error::OutOfRange)));
    }
    assert!(matches!(legacy_map::path(8192, u32::MAX as u64), Ok(p) if p.root == 14 && p.depth == 3));
    assert!(matches!(legacy_map::path(1024, u32::MAX as u64), Err(Error::OutOfRange)));
}

#[test]
fn malformed_geometry_and_unsupported_flags_still_fail() {
    let raw = inode(1, &[]);
    for block_bytes in [0, 512, 3072, 131072, u32::MAX] {
        assert!(matches!(
            legacy_map::parse(&raw, block_bytes, u64::MAX, false, false, block_bytes, false),
            Err(Error::Geometry)
        ));
    }
    assert!(matches!(legacy_map::parse(&raw, 4096, 0, false, false, 4096, false), Err(Error::Geometry)));
    assert!(matches!(legacy_map::parse(&raw[..127], 4096, u64::MAX, false, false, 4096, false), Err(Error::Inode)));
    for flag in [0x80000u32, 0x10000000] {
        let mut raw = inode(1, &[]);
        raw[32..36].copy_from_slice(&flag.to_le_bytes());
        assert!(matches!(legacy_map::parse(&raw, 4096, u64::MAX, false, false, 4096, false), Err(Error::Unsupported)));
    }
    let mut raw = inode(1, &[]);
    raw[0..2].copy_from_slice(&0x1180u16.to_le_bytes());
    assert!(matches!(legacy_map::parse(&raw, 4096, u64::MAX, false, false, 4096, false), Err(Error::Unsupported)));
}

#[test]
fn small_geometry_rejects_pointer_at_filesystem_end() {
    let raw = inode(1, &[(0, 4)]);
    assert!(matches!(legacy_map::parse(&raw, 4096, 4, false, false, 4096, false), Err(Error::OutOfRange)));
    let root = parsed(&raw, 4096, 5);
    let mut image = vec![0; 5 * 4096];
    image[4 * 4096] = 0x6b;
    let source = Snapshot::from_bytes(&image);
    assert!(matches!(root.lookup(&source, 0), Ok(m) if m.physical == Some(4)));
    assert!(matches!(root.read(&source, 0, 1), Ok(bytes) if bytes == [0x6b]));
}

#[test]
fn collection_still_rejects_physical_aliases() {
    let image = vec![0; 16 * 4096];
    let source = Snapshot::from_bytes(&image);
    for pointers in [&[(0, 1), (1, 1)][..], &[(0, 3), (12, 3)][..]] {
        let raw = inode(1, pointers);
        assert!(matches!(parsed(&raw, 4096, 16).collect(&source, 16, 16), Err(Error::Alias)));
    }
}

#[test]
fn sparse_reads_zero_holes_and_clip_eof() {
    let block_bytes = 4096usize;
    let raw = inode((2 * block_bytes + 9) as u64, &[(0, 1), (2, 2)]);
    let root = parsed(&raw, block_bytes as u32, 16);
    let mut image = vec![0; 16 * block_bytes];
    image[block_bytes..2 * block_bytes].fill(0x31);
    image[2 * block_bytes..3 * block_bytes].fill(0x72);
    let source = Snapshot::from_bytes(&image);
    match root.read(&source, (block_bytes - 2) as u64, block_bytes + 5) {
        Ok(bytes) => {
            assert_eq!(&bytes[..2], &[0x31, 0x31]);
            assert!(bytes[2..2 + block_bytes].iter().all(|&b| b == 0));
            assert_eq!(&bytes[2 + block_bytes..], &[0x72; 3]);
        }
        Err(_) => panic!("sparse cross-block read rejected"),
    }
    assert!(matches!(root.read(&source, (2 * block_bytes + 7) as u64, 10), Ok(bytes) if bytes == [0x72; 2]));
}

#[test]
fn collection_still_rejects_logical_block_overflow() {
    let block_bytes = 8192;
    let raw = inode(1, &[(14, 3)]);
    let root = parsed(&raw, block_bytes, 16);
    let mut image = vec![0; 16 * block_bytes as usize];
    word(&mut image, block_bytes, 3, 1024, 4);
    let source = Snapshot::from_bytes(&image);
    assert!(matches!(root.collect(&source, 2, 0), Err(Error::OutOfRange)));
}

#[test]
fn complete_source_geometry_requires_every_declared_byte() {
    for block_bytes in BLOCK_SIZES {
        let raw = inode(1, &[(0, 1)]);
        let root = parsed(&raw, block_bytes, 16);
        let image = vec![0x4c; 16 * block_bytes as usize];
        let complete = Snapshot::from_bytes(&image);
        let short = Snapshot::from_bytes(&image[..image.len() - 1]);
        assert!(matches!(root.lookup(&complete, 0), Ok(m) if m.physical == Some(1)));
        assert!(matches!(root.lookup(&short, 0), Err(Error::Source)));
        assert!(matches!(root.collect(&short, 0, 1), Err(Error::Source)));
        assert!(matches!(root.read(&short, 0, 1), Err(Error::Source)));
    }
}
