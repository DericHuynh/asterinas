// SPDX-License-Identifier: MPL-2.0

//! Linux/e2fsprogs interoperability of the checked byte codecs. This harness
//! supplies controlled fixtures; it is not a durability or hardware proof.

extern crate verified_ext4 as core;

fn fixture() -> (Vec<u8>, core::layout::JournalLayout, u32, u32) {
    let img = std::fs::read(std::env::var("EXT4_TEST_IMAGE").unwrap()).unwrap();
    let (layout, seed, target) = geometry(&img);
    (img, layout, seed, target)
}

fn geometry(img: &[u8]) -> (core::layout::JournalLayout, u32, u32) {
    let sb = core::superblock::parse(&img[1024..2048], img.len() as u64).unwrap();
    let seed = core::crc::crc32c(0xffffffff, &img[1128..1144]);
    let ipg = core::bytes::read_le32(&img[1024..2048], 40).unwrap();
    let group = core::group::parse(&img[4096..4128], 0, sb.blocks(), ipg, seed).unwrap();
    let base = group.inode_table as usize * 4096;
    let journal = &img[base + 7 * 256..base + 8 * 256];
    let layout = core::layout::from_inode(journal, sb.inodes(), sb.blocks(), seed).unwrap();
    let file = &img[base + 11 * 256..base + 12 * 256]; // debugfs fixture allocates inode 12.
    let file_extent = core::extent::parse(file, 52, sb.blocks()).unwrap();
    (layout, seed, file_extent.physical)
}

fn linux_recover(path: &str, image: &[u8]) -> Vec<u8> {
    std::fs::write(path, image).unwrap();
    let executable = std::env::var("E2FSCK_BIN").unwrap_or_else(|_| "e2fsck".to_string());
    let result = std::process::Command::new(executable)
        .args(["-fy", path])
        .output()
        .unwrap();
    assert!(
        matches!(result.status.code(), Some(0 | 1)),
        "{path}: {}\n{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
    let recovered = std::fs::read(path).unwrap();
    std::fs::remove_file(path).unwrap();
    recovered
}

fn payload(
    block: u32,
    sequence: u32,
    seed: u32,
    value: u8,
) -> (core::jbd2::Tag, core::frozen::FrozenBlock) {
    let mut bytes = vec![value; 4096];
    bytes[..4].copy_from_slice(&core::jbd2::MAGIC.to_be_bytes());
    let original = core::frozen::FrozenBlock::capture(&bytes).unwrap();
    let (escaped, flag) = original.escape().unwrap();
    assert!(flag);
    let checksum = core::jbd2::payload_checksum(seed, sequence, escaped.as_slice()).unwrap();
    (
        core::jbd2::Tag {
            block,
            flags: 9,
            checksum,
        },
        escaped,
    )
}

#[test]
fn descriptor_and_revoke_roundtrips_at_capacity() {
    let uuid = [7u8; 16];
    let seed = core::crc::crc32c(0xffffffff, &uuid);
    for n in [1usize, 2, 249, 250] {
        let tags: Vec<_> = (0..n)
            .map(|i| core::jbd2::Tag {
                block: i as u32,
                flags: (if i == 0 { 0 } else { 2 }) + (if i + 1 == n { 8 } else { 0 }),
                checksum: (i as u32).wrapping_mul(0x01020304),
            })
            .collect();
        let bytes = core::descriptor::encode(&tags, &uuid, 9, 32768, seed).unwrap();
        let decoded = core::descriptor::parse(bytes.as_slice(), &uuid, 9, 32768, seed).unwrap();
        assert_eq!(decoded.tags().len(), tags.len());
        for (a, b) in decoded.tags().iter().zip(&tags) {
            assert_eq!(
                (a.block, a.flags, a.checksum),
                (b.block, b.flags, b.checksum)
            );
        }
        assert!(core::descriptor::parse(bytes.as_slice(), &[8u8; 16], 9, 32768, seed).is_none());
    }
    for n in [0usize, 1, 1018, 1019] {
        let blocks: Vec<u32> = (0..n as u32).collect();
        let bytes = core::revoke::encode(&blocks, 9, 32768, seed).unwrap();
        let decoded = core::revoke::parse(bytes.as_slice(), 9, 32768, seed).unwrap();
        assert_eq!(decoded.blocks(), blocks);
    }
    assert!(core::revoke::encode(&vec![0; 1020], 9, 32768, seed).is_none());
    let commit = core::jbd2::encode_commit(9, seed).unwrap();
    assert!(core::jbd2::valid_commit(commit.as_slice(), 9, seed));
    assert!(!core::jbd2::valid_commit(commit.as_slice(), 10, seed));
}

#[test]
fn malformed_descriptor_terminators_flags_and_checksums_are_rejected() {
    let uuid = [7u8; 16];
    let seed = core::crc::crc32c(0xffffffff, &uuid);
    let tags = [core::jbd2::Tag {
        block: 0,
        flags: 8,
        checksum: 0x12345678,
    }];
    let good = core::descriptor::encode(&tags, &uuid, 9, 32768, seed).unwrap();
    for (offset, value) in [(16usize, 0u32), (16, 10), (20, 1)] {
        let mut bad = good.as_slice().to_vec();
        core::bytes::write_be32(&mut bad, offset, value);
        let c = core::crc::crc32c_zero4(seed, &bad, 4092).unwrap();
        core::bytes::write_be32(&mut bad, 4092, c);
        assert!(core::descriptor::parse(&bad, &uuid, 9, 32768, seed).is_none());
    }
    let mut bad = good.as_slice().to_vec();
    bad[128] ^= 1;
    assert!(core::descriptor::parse(&bad, &uuid, 9, 32768, seed).is_none());
    let mut destination = [11u8; 8];
    assert!(!core::bytes::write_bytes(
        &mut destination,
        usize::MAX,
        &[1, 2]
    ));
    assert_eq!(destination, [11u8; 8]);
}

#[test]
fn replay_filter_handles_revoke_and_reallocation_without_journal_targets() {
    let (_, layout, seed, block) = fixture();
    let (tag, data) = payload(block, 9, seed, 0x11);
    let a = core::replay::decode_payload(&tag, data.as_slice(), 9, seed, &layout).unwrap();
    let (tag, data) = payload(block, 11, seed, 0x33);
    let b = core::replay::decode_payload(&tag, data.as_slice(), 11, seed, &layout).unwrap();
    let revokes = vec![core::replay::Revocation {
        block,
        sequence: 10,
    }];
    let plan = core::replay::build(layout, vec![a, b], revokes, 9, 11).unwrap();
    assert_eq!(plan.len(), 1);
    assert_eq!(plan.get(0).unwrap().sequence(), 11);
    assert_eq!(plan.get(0).unwrap().image()[100], 0x33);
    assert!(plan.get(1).is_none());
    let (_, layout, seed, block) = fixture();
    let (tag, data) = payload(block, 9, seed, 0x11);
    let a = core::replay::decode_payload(&tag, data.as_slice(), 9, seed, &layout).unwrap();
    let plan = core::replay::build(
        layout,
        vec![a],
        vec![core::replay::Revocation { block, sequence: 9 }],
        9,
        9,
    )
    .unwrap();
    assert_eq!(plan.len(), 0);
    let (_, layout, seed, _) = fixture();
    let journal_block = (layout.offset(0, u64::MAX).unwrap() / 4096) as u32;
    let (tag, data) = payload(journal_block, 9, seed, 0x55);
    assert!(core::replay::decode_payload(&tag, data.as_slice(), 9, seed, &layout).is_none());
}

fn append_record(
    image: &mut [u8],
    layout: &core::layout::JournalLayout,
    start: u32,
    ordinal: &mut u32,
    bytes: &[u8],
) {
    let slot = core::ring::slot(1, layout.blocks(), start, *ordinal).unwrap();
    let offset = layout.offset(slot, image.len() as u64).unwrap() as usize;
    image[offset..offset + 4096].copy_from_slice(bytes);
    *ordinal += 1;
}

fn append_transaction(
    image: &mut [u8],
    layout: &core::layout::JournalLayout,
    uuid: &[u8],
    seed: u32,
    start: u32,
    ordinal: &mut u32,
    sequence: u32,
    target: Option<(u32, u8)>,
    revoked: Option<u32>,
    commit: bool,
) {
    if let Some((block, value)) = target {
        let (tag, data) = payload(block, sequence, seed, value);
        let descriptor =
            core::descriptor::encode(&[tag], uuid, sequence, layout.filesystem_blocks(), seed)
                .unwrap();
        append_record(image, layout, start, ordinal, descriptor.as_slice());
        append_record(image, layout, start, ordinal, data.as_slice());
    }
    if let Some(block) = revoked {
        let r = core::revoke::encode(&[block], sequence, layout.filesystem_blocks(), seed).unwrap();
        append_record(image, layout, start, ordinal, r.as_slice());
    }
    if commit {
        let c = core::jbd2::encode_commit(sequence, seed).unwrap();
        append_record(image, layout, start, ordinal, c.as_slice());
    }
}

#[test]
fn linux_recovery_accepts_emitted_records_wrap_revoke_and_incomplete_tail() {
    for case in 0..7 {
        let (mut image, layout, seed, target) = fixture();
        let original = image[target as usize * 4096..(target as usize + 1) * 4096].to_vec();
        let uuid = image[1128..1144].to_vec();
        let journal_base = layout.offset(0, image.len() as u64).unwrap() as usize;
        let start = if case == 5 { layout.blocks() - 2 } else { 1 };
        let sb = &mut image[journal_base..journal_base + 1024];
        for (offset, value) in [(24, 9), (28, start), (40, 17)] {
            core::bytes::write_be32(sb, offset, value);
        }
        sb[80] = 4;
        let checksum = core::crc::crc32c_zero4(0xffffffff, sb, 252).unwrap();
        core::bytes::write_be32(sb, 252, checksum);
        let mut ordinal = 0;
        if case == 6 {
            let mut metadata = image[..4096].to_vec();
            metadata[1024 + 96] |= 4; // Keep needs-recovery set through checkpoint.
            metadata[1024 + 120..1024 + 136].copy_from_slice(b"verus-replay-sb0");
            let c = core::crc::crc32c(0xffffffff, &metadata[1024..2044]);
            metadata[2044..2048].copy_from_slice(&c.to_le_bytes());
            let meta_checksum = core::jbd2::payload_checksum(seed, 9, &metadata).unwrap();
            let (mut data_tag, data) = payload(target, 9, seed, 0x11);
            data_tag.flags = 11;
            let tags = [
                core::jbd2::Tag {
                    block: 0,
                    flags: 0,
                    checksum: meta_checksum,
                },
                data_tag,
            ];
            let d = core::descriptor::encode(&tags, &uuid, 9, layout.filesystem_blocks(), seed)
                .unwrap();
            append_record(&mut image, &layout, start, &mut ordinal, d.as_slice());
            append_record(&mut image, &layout, start, &mut ordinal, &metadata);
            append_record(&mut image, &layout, start, &mut ordinal, data.as_slice());
            let c = core::jbd2::encode_commit(9, seed).unwrap();
            append_record(&mut image, &layout, start, &mut ordinal, c.as_slice());
        } else {
            append_transaction(
                &mut image,
                &layout,
                &uuid,
                seed,
                start,
                &mut ordinal,
                9,
                Some((target, 0x11)),
                if case == 3 { Some(target) } else { None },
                true,
            );
        }
        if case == 1 || case == 2 {
            append_transaction(
                &mut image,
                &layout,
                &uuid,
                seed,
                start,
                &mut ordinal,
                10,
                None,
                Some(target),
                true,
            );
        }
        if case == 2 {
            append_transaction(
                &mut image,
                &layout,
                &uuid,
                seed,
                start,
                &mut ordinal,
                11,
                Some((target, 0x33)),
                None,
                true,
            );
        }
        if case == 4 {
            append_transaction(
                &mut image,
                &layout,
                &uuid,
                seed,
                start,
                &mut ordinal,
                10,
                Some((target, 0x55)),
                None,
                false,
            );
        }
        let sb = &mut image[1024..2048];
        sb[96] |= 4;
        let checksum = core::crc::crc32c(0xffffffff, &sb[..1020]);
        sb[1020..1024].copy_from_slice(&checksum.to_le_bytes());
        let scan_layout = geometry(&image).0;
        let snapshot = &image[journal_base..journal_base + layout.blocks() as usize * 4096];
        let scan = core::scan::recover(snapshot, &uuid, scan_layout)
            .expect("checked scanner accepts fixture");
        let transactions = if case == 2 {
            3
        } else if case == 1 {
            2
        } else {
            1
        };
        assert_eq!(scan.committed_transactions(), transactions, "case {case}");
        assert_eq!(scan.next_sequence(), 9 + transactions, "case {case}");
        let plan = scan.replay_plan();
        assert_eq!(
            plan.len(),
            if case == 1 || case == 3 {
                0
            } else if case == 6 {
                2
            } else {
                1
            }
        );
        let mut shadow = image.clone();
        for i in 0..plan.len() {
            let write = plan.get(i).unwrap();
            let offset = write.block() as usize * 4096;
            shadow[offset..offset + 4096].copy_from_slice(write.image());
        }
        let mut engine = core::recovery_io::prepare(
            snapshot,
            &uuid,
            geometry(&image).0,
            &image[..4096],
            image.len() as u64,
        )
        .unwrap();
        let mut protocol_image = image.clone();
        let mut cache: Vec<(u32, Vec<u8>)> = Vec::new();
        let mut operations = 0;
        while let Some(id) = engine.begin() {
            assert!(engine.begin().is_none(), "only one outstanding request");
            assert!(
                !engine.complete(id + 1, true),
                "future callback cannot complete request"
            );
            match engine.command().unwrap() {
                core::recovery_io::Command::Write { block, image } => {
                    cache.push((block, image.to_vec()))
                }
                core::recovery_io::Command::Flush => {
                    for (block, bytes) in cache.drain(..) {
                        let offset = block as usize * 4096;
                        protocol_image[offset..offset + 4096].copy_from_slice(&bytes);
                    }
                }
            }
            if case == 6 {
                // Crash before the callback, permitting every cached write to
                // persist. Even a persisted clear tail must retain the data.
                let mut crash = protocol_image.clone();
                for (block, bytes) in &cache {
                    let offset = *block as usize * 4096;
                    crash[offset..offset + 4096].copy_from_slice(bytes);
                }
                let recovered =
                    linux_recover(&format!("build/recovery-cut-{operations}.img"), &crash);
                assert_eq!(
                    &recovered[target as usize * 4096..(target as usize + 1) * 4096],
                    &shadow[target as usize * 4096..(target as usize + 1) * 4096]
                );
                assert_eq!(&recovered[1144..1160], b"verus-replay-sb0");
            }
            assert!(engine.complete(id, true));
            assert!(
                !engine.complete(id, true),
                "duplicate callback cannot advance protocol"
            );
            operations += 1;
        }
        assert_eq!(operations, plan.len() + 3);
        assert!(engine.finished());
        assert!(!engine.failed());
        assert!(cache.is_empty());
        assert_eq!(
            &protocol_image[target as usize * 4096..(target as usize + 1) * 4096],
            &shadow[target as usize * 4096..(target as usize + 1) * 4096]
        );
        let retired = &protocol_image[journal_base..journal_base + layout.blocks() as usize * 4096];
        let clean = core::scan::recover(retired, &uuid, geometry(&protocol_image).0).unwrap();
        assert_eq!(clean.committed_transactions(), 0);
        assert_eq!(clean.replay_plan().len(), 0);
        assert!(clean.next_sequence() > scan.next_sequence());
        let path = format!("build/linux-replay-{case}.img");
        let recovered = linux_recover(&path, &image);
        let data = &recovered[target as usize * 4096..(target as usize + 1) * 4096];
        assert_eq!(
            data,
            &shadow[target as usize * 4096..(target as usize + 1) * 4096],
            "case {case}"
        );
        if case == 1 || case == 3 {
            assert_eq!(data, original, "case {case}");
        } else {
            assert_eq!(&data[..4], &core::jbd2::MAGIC.to_be_bytes());
            assert_eq!(
                data[100],
                if case == 2 { 0x33 } else { 0x11 },
                "case {case}"
            );
        }
        assert!(core::superblock::parse(&recovered[1024..2048], recovered.len() as u64).is_some());
        if case == 6 {
            assert_eq!(&recovered[1144..1160], b"verus-replay-sb0");
        }
        let retired = linux_recover(&format!("build/linux-retired-{case}.img"), &protocol_image);
        assert_eq!(
            &retired[target as usize * 4096..(target as usize + 1) * 4096],
            data
        );
    }
}

#[test]
fn recovery_protocol_aborts_without_cancelling_and_rejects_stale_completions() {
    let (mut image, layout, seed, target) = fixture();
    let uuid = image[1128..1144].to_vec();
    let base = layout.offset(0, image.len() as u64).unwrap() as usize;
    let sb = core::journal_state::encode(&image[base..base + 4096], &uuid, layout.blocks(), 9, 1)
        .unwrap();
    image[base..base + 4096].copy_from_slice(sb.as_slice());
    append_transaction(
        &mut image,
        &layout,
        &uuid,
        seed,
        1,
        &mut 0,
        9,
        Some((target, 0x11)),
        None,
        true,
    );
    let dirty =
        core::super_state::recovery_image(&image[..4096], image.len() as u64, true).unwrap();
    image[..4096].copy_from_slice(dirty.as_slice());
    let snapshot = &image[base..base + layout.blocks() as usize * 4096];
    for fail_at in 0..4 {
        let mut engine = core::recovery_io::prepare(
            snapshot,
            &uuid,
            geometry(&image).0,
            &image[..4096],
            image.len() as u64,
        )
        .unwrap();
        for _ in 0..fail_at {
            let id = engine.begin().unwrap();
            assert!(engine.complete(id, true));
        }
        let id = engine.begin().unwrap();
        assert!(!engine.complete(id - 1, true));
        engine.abort();
        assert!(engine.failed());
        assert!(
            engine.command().is_some(),
            "abort retains in-flight image/command"
        );
        assert!(engine.begin().is_none());
        assert!(
            engine.complete(id, true),
            "late real completion can be drained"
        );
        assert!(engine.command().is_none());
        assert!(!engine.finished());
        assert!(engine.begin().is_none());
    }
    let mut engine = core::recovery_io::prepare(
        snapshot,
        &uuid,
        geometry(&image).0,
        &image[..4096],
        image.len() as u64,
    )
    .unwrap();
    let id = engine.begin().unwrap();
    assert!(engine.complete(id, false));
    assert!(engine.failed());
    assert!(!engine.finished());
    assert!(engine.begin().is_none());
}

#[test]
fn state_codecs_preserve_unrelated_bytes_and_epochs_do_not_trust_checksums() {
    let (mut image, layout, _, _) = fixture();
    let uuid = image[1128..1144].to_vec();
    let dirty =
        core::super_state::recovery_image(&image[..4096], image.len() as u64, true).unwrap();
    assert!(
        core::superblock::parse(&dirty.as_slice()[1024..2048], image.len() as u64)
            .unwrap()
            .needs_recovery()
    );
    let clean =
        core::super_state::recovery_image(dirty.as_slice(), image.len() as u64, false).unwrap();
    assert_eq!(clean.as_slice(), &image[..4096]);
    assert!(!core::super_state::valid_replay(
        dirty.as_slice(),
        clean.as_slice(),
        image.len() as u64
    ));
    let mut changed_uuid = dirty.as_slice().to_vec();
    changed_uuid[1128] ^= 1;
    let checksum = core::crc::crc32c(0xffffffff, &changed_uuid[1024..2044]);
    changed_uuid[2044..2048].copy_from_slice(&checksum.to_le_bytes());
    assert!(core::superblock::parse(&changed_uuid[1024..2048], image.len() as u64).is_some());
    assert!(!core::super_state::valid_replay(
        dirty.as_slice(),
        &changed_uuid,
        image.len() as u64
    ));
    let mut changed_boot = dirty.as_slice().to_vec();
    changed_boot[0] ^= 1;
    assert!(!core::super_state::valid_replay(
        dirty.as_slice(),
        &changed_boot,
        image.len() as u64
    ));
    let base = layout.offset(0, image.len() as u64).unwrap() as usize;
    let sb = core::journal_state::encode(&image[base..base + 4096], &uuid, layout.blocks(), 17, 1)
        .unwrap();
    let info =
        core::journal_superblock::parse(&sb.as_slice()[..1024], &uuid, layout.blocks()).unwrap();
    assert!(info.csum_v3 && info.revoke);
    assert_eq!((info.sequence, info.start), (17, 1));
    for i in 0..4096 {
        if !(24..32).contains(&i) && !(40..44).contains(&i) && i != 80 && !(252..256).contains(&i) {
            assert_eq!(sb.as_slice()[i], image[base + i]);
        }
    }
    let snapshot = &mut image[base..base + layout.blocks() as usize * 4096];
    let forged = core::jbd2::encode_header(2, 400).unwrap();
    snapshot[4096..4108].copy_from_slice(&forged); // No valid commit checksum.
    assert_eq!(core::epoch::fresh_sequence(snapshot, 10), Some(401));
    let exhausted = core::jbd2::encode_header(1, u32::MAX - 1).unwrap();
    snapshot[8192..8204].copy_from_slice(&exhausted);
    assert!(core::epoch::fresh_sequence(snapshot, 10).is_none());
    let terminal =
        core::journal_state::encode(&snapshot[..4096], &uuid, layout.blocks(), u32::MAX, 0)
            .unwrap();
    snapshot[..4096].copy_from_slice(terminal.as_slice());
    let read = core::scan::recover(
        snapshot,
        &uuid,
        geometry(&std::fs::read("build/linux.img").unwrap()).0,
    )
    .unwrap();
    assert_eq!(read.next_sequence(), u32::MAX);
    assert!(
        core::recovery_io::prepare(
            snapshot,
            &uuid,
            geometry(&std::fs::read("build/linux.img").unwrap()).0,
            dirty.as_slice(),
            64 * 1024 * 1024
        )
        .is_none()
    );
}
