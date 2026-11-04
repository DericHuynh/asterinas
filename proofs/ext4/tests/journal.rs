// SPDX-License-Identifier: MPL-2.0

//! Linux/e2fsprogs interoperability of the checked byte codecs. This harness
//! supplies controlled fixtures; it is not a durability or hardware proof.

extern crate verified_ext4 as core;

use core::recovery_request::Completion;

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
fn scanner_preflights_complete_record_credits_and_reserved_revoke_targets() {
    let (image, layout, seed, target) = fixture();
    let uuid = image[1128..1144].to_vec();
    let base = layout.offset(0, image.len() as u64).unwrap() as usize;
    let header =
        core::journal_state::encode(&image[base..base + 4096], &uuid, layout.blocks(), 9, 1)
            .unwrap();
    for total in [4096usize, 4097] {
        let mut snapshot = vec![0u8; layout.blocks() as usize * 4096];
        snapshot[..4096].copy_from_slice(header.as_slice());
        let mut remaining = total;
        let mut ordinal = 1;
        while remaining > 0 {
            let count = remaining.min(1019);
            let raw =
                core::revoke::encode(&vec![target; count], 9, layout.filesystem_blocks(), seed)
                    .unwrap();
            snapshot[ordinal * 4096..(ordinal + 1) * 4096].copy_from_slice(raw.as_slice());
            remaining -= count;
            ordinal += 1;
        }
        let commit = core::jbd2::encode_commit(9, seed).unwrap();
        snapshot[ordinal * 4096..(ordinal + 1) * 4096].copy_from_slice(commit.as_slice());
        let result = core::scan::recover(&snapshot, &uuid, geometry(&image).0);
        if total == 4096 {
            let scan = result.expect("the exact replay-credit boundary is supported");
            assert_eq!(scan.committed_transactions(), 1);
            assert_eq!(scan.replay_plan().len(), 0);
        } else {
            assert!(result.is_none());
        }
    }
    let mut snapshot = vec![0u8; layout.blocks() as usize * 4096];
    snapshot[..4096].copy_from_slice(header.as_slice());
    let raw =
        core::revoke::encode(&[(base / 4096) as u32], 9, layout.filesystem_blocks(), seed).unwrap();
    snapshot[4096..8192].copy_from_slice(raw.as_slice());
    assert!(core::scan::recover(&snapshot, &uuid, geometry(&image).0).is_none());
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
        let patches = core::recovery_patch::collect(plan);
        assert_eq!(patches.len(), plan.len());
        for ordinal in 0..plan.len() {
            let write = plan.get(ordinal).unwrap();
            assert_eq!(
                patches.get(write.block()).unwrap().as_slice(),
                write.image()
            );
        }
        for ordinal in 1..patches.len() {
            assert!(
                patches.at(ordinal - 1).unwrap().block() < patches.at(ordinal).unwrap().block()
            );
        }
        let source = core::snapshot::Snapshot::from_bytes(&image);
        let checked_shadow = source.overlay(&patches).unwrap();
        for block in [
            0,
            1,
            target,
            layout.physical_start(),
            layout.filesystem_blocks() - 1,
        ] {
            assert_eq!(
                checked_shadow.block(block).unwrap().as_slice(),
                &shadow[block as usize * 4096..(block as usize + 1) * 4096]
            );
        }
        let boot = core::bootstrap::locate(&source).unwrap();
        let mut engine = boot
            .prepare_recovery()
            .expect("same-source recovery preparation");
        assert_eq!(engine.replay_plan().len(), plan.len());
        for ordinal in 0..plan.len() {
            let write = plan.get(ordinal).unwrap();
            let actual = engine.replay_plan().get(ordinal).unwrap();
            assert_eq!(actual.block(), write.block());
            assert_eq!(actual.image(), write.image());
        }
        let (tail_target, tail) = engine.retirement_image();
        assert_eq!(tail_target, layout.physical_start());
        assert_eq!(core::bytes::read_be32(tail, 28), Some(0));
        let mut protocol_image = image.clone();
        let mut cache: Vec<(u32, Vec<u8>)> = Vec::new();
        let mut operations = 0;
        loop {
            let pending = match core::recovery_request::dispatch(engine) {
                Ok(pending) => pending,
                Err(done) => {
                    engine = done;
                    break;
                }
            };
            match pending.pending_command() {
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
            engine = pending.finish_pending(Completion::Succeeded);
            operations += 1;
        }
        assert_eq!(operations, plan.len() + 3);
        assert!(engine.finished());
        assert!(!engine.failed());
        assert!(cache.is_empty());
        let mut admitted =
            core::recovery_admission::prepare(&source).expect("validated final recovered image");
        assert_eq!(admitted.home_patches().len(), plan.len());
        let mut admitted_image = image.clone();
        let mut admitted_cache = Vec::new();
        loop {
            let pending = match admitted.dispatch() {
                Ok(pending) => pending,
                Err(done) => {
                    admitted = done;
                    break;
                }
            };
            match pending.pending_command() {
                core::recovery_io::Command::Write { block, image } => {
                    admitted_cache.push((block, image.to_vec()))
                }
                core::recovery_io::Command::Flush => {
                    for (block, bytes) in admitted_cache.drain(..) {
                        admitted_image[block as usize * 4096..(block as usize + 1) * 4096]
                            .copy_from_slice(&bytes);
                    }
                }
            }
            admitted = pending.finish_pending(Completion::Succeeded);
        }
        assert!(admitted.finished());
        assert!(admitted_cache.is_empty());
        assert_eq!(admitted_image, protocol_image);
        assert!(
            core::image_validation::inspect(core::snapshot::Snapshot::from_bytes(&admitted_image))
                .is_some()
        );
        assert_eq!(
            &protocol_image[target as usize * 4096..(target as usize + 1) * 4096],
            &shadow[target as usize * 4096..(target as usize + 1) * 4096]
        );
        let retired = &protocol_image[journal_base..journal_base + layout.blocks() as usize * 4096];
        let clean = core::scan::recover(retired, &uuid, geometry(&protocol_image).0).unwrap();
        assert_eq!(clean.committed_transactions(), 0);
        assert_eq!(clean.replay_plan().len(), 0);
        assert_eq!(clean.next_sequence(), scan.next_sequence());
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
fn recovery_admission_rejects_invalid_semantics_and_accepts_repaired_home_metadata() {
    fn logged_patch(image: &[u8], target: u32, payload: &[u8]) -> Vec<u8> {
        let mut result = image.to_vec();
        let (layout, seed, _) = geometry(image);
        let uuid = image[1128..1144].to_vec();
        let base = layout.physical_start() as usize * 4096;
        let journal =
            core::journal_state::encode(&image[base..base + 4096], &uuid, layout.blocks(), 9, 1)
                .unwrap();
        result[base..base + 4096].copy_from_slice(journal.as_slice());
        let dirty =
            core::super_state::recovery_image(&image[..4096], image.len() as u64, true).unwrap();
        result[..4096].copy_from_slice(dirty.as_slice());
        let tx = core::transaction::encode(
            vec![core::transaction::AfterImage::capture(target, payload).unwrap()],
            &uuid,
            9,
            &layout,
            &result[..4096],
            result.len() as u64,
        )
        .unwrap();
        let mut ordinal = 0;
        append_record(&mut result, &layout, 1, &mut ordinal, tx.descriptor_bytes());
        append_record(
            &mut result,
            &layout,
            1,
            &mut ordinal,
            tx.payload_at(0).unwrap(),
        );
        append_record(&mut result, &layout, 1, &mut ordinal, tx.commit_bytes());
        assert!(core::jbd2::valid_commit(tx.commit_bytes(), 9, seed));
        result
    }
    let (image, _, seed, target) = fixture();
    let bitmap = core::bytes::read_le32(&image, 4096).unwrap();
    let table = core::bytes::read_le32(&image, 4104).unwrap();
    let mut bad_bitmap = image[bitmap as usize * 4096..(bitmap as usize + 1) * 4096].to_vec();
    bad_bitmap[0] ^= 1;
    let bad = logged_patch(&image, bitmap, &bad_bitmap);
    let source = core::snapshot::Snapshot::from_bytes(&bad);
    assert!(
        core::bootstrap::locate(&source)
            .unwrap()
            .prepare_recovery()
            .is_some(),
        "JBD2 checksums alone admit this payload"
    );
    assert!(
        core::recovery_admission::prepare(&source).is_none(),
        "whole-image checks must reject the invalid allocation bitmap"
    );
    for number in [2u32, 8] {
        let mut payload = image[table as usize * 4096..(table as usize + 1) * 4096].to_vec();
        let offset = (number as usize - 1) * 256;
        let inode = &mut payload[offset..offset + 256];
        if number == 2 {
            inode[26..28].copy_from_slice(&1u16.to_le_bytes());
        } else {
            inode[2] ^= 1;
        }
        let checksum = core::inode::calculated_checksum(inode, number, seed).unwrap();
        inode[124..126].copy_from_slice(&(checksum as u16).to_le_bytes());
        inode[130..132].copy_from_slice(&((checksum >> 16) as u16).to_le_bytes());
        let changed = logged_patch(&image, table, &payload);
        let source = core::snapshot::Snapshot::from_bytes(&changed);
        assert!(
            core::bootstrap::locate(&source)
                .unwrap()
                .prepare_recovery()
                .is_some()
        );
        assert!(
            core::recovery_admission::prepare(&source).is_none(),
            "reject inode {number} namespace or journal identity violation"
        );
    }
    let mut cut = image.clone();
    cut[bitmap as usize * 4096] ^= 1;
    let repair = logged_patch(
        &cut,
        bitmap,
        &image[bitmap as usize * 4096..(bitmap as usize + 1) * 4096],
    );
    let source = core::snapshot::Snapshot::from_bytes(&repair);
    assert!(core::allocation::parse(source.duplicate()).is_none());
    let admitted = core::recovery_admission::prepare(&source)
        .expect("validate repaired shadow, not inconsistent home metadata");
    assert_eq!(
        admitted.home_patches().get(bitmap).unwrap().as_slice(),
        &image[bitmap as usize * 4096..(bitmap as usize + 1) * 4096]
    );
    let good = logged_patch(&image, target, &[0x6a; 4096]);
    let source = core::snapshot::Snapshot::from_bytes(&good);
    let pending = core::recovery_admission::prepare(&source)
        .unwrap()
        .dispatch()
        .ok()
        .unwrap();
    let aborted = pending
        .abort_pending()
        .finish_pending(Completion::Succeeded);
    assert!(aborted.failed() && !aborted.finished());
    assert!(
        aborted.dispatch().is_err(),
        "abort retains completion ownership but cannot start further I/O"
    );
}

#[test]
fn recovery_requests_retain_ownership_through_abort_and_late_completion() {
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
            let pending = core::recovery_request::dispatch(engine).ok().unwrap();
            engine = pending.finish_pending(Completion::Succeeded);
        }
        let pending = core::recovery_request::dispatch(engine)
            .ok()
            .unwrap()
            .abort_pending();
        let _command = pending.pending_command(); // Abort retains the exact owned request.
        let engine = pending.finish_pending(Completion::Succeeded); // Drain a late real callback.
        assert!(engine.failed());
        assert!(!engine.finished());
        assert!(core::recovery_request::dispatch(engine).is_err());
    }
    let engine = core::recovery_io::prepare(
        snapshot,
        &uuid,
        geometry(&image).0,
        &image[..4096],
        image.len() as u64,
    )
    .unwrap();
    let pending = core::recovery_request::dispatch(engine).ok().unwrap();
    let engine = pending.finish_pending(Completion::Failed);
    assert!(engine.failed());
    assert!(!engine.finished());
    assert!(core::recovery_request::dispatch(engine).is_err());
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
        .is_some()
    );
}

#[test]
fn terminal_transaction_recovers_and_retires_without_allocating_an_epoch() {
    let (mut image, layout, seed, target) = fixture();
    let uuid = image[1128..1144].to_vec();
    let base = layout.offset(0, image.len() as u64).unwrap() as usize;
    let header = core::journal_state::encode(
        &image[base..base + 4096],
        &uuid,
        layout.blocks(),
        u32::MAX - 1,
        1,
    )
    .unwrap();
    image[base..base + 4096].copy_from_slice(header.as_slice());
    append_transaction(
        &mut image,
        &layout,
        &uuid,
        seed,
        1,
        &mut 0,
        u32::MAX - 1,
        Some((target, 0x99)),
        None,
        true,
    );
    let dirty =
        core::super_state::recovery_image(&image[..4096], image.len() as u64, true).unwrap();
    image[..4096].copy_from_slice(dirty.as_slice());
    let snapshot = &image[base..base + layout.blocks() as usize * 4096];
    let scanned = core::scan::recover(snapshot, &uuid, geometry(&image).0).unwrap();
    assert_eq!(scanned.committed_transactions(), 1);
    assert_eq!(scanned.next_sequence(), u32::MAX);
    let expected = scanned.replay_plan().get(0).unwrap().image().to_vec();
    let linux = linux_recover("build/terminal-linux.img", &image);
    assert_eq!(
        &linux[target as usize * 4096..(target as usize + 1) * 4096],
        expected
    );
    let mut engine = core::recovery_io::prepare(
        snapshot,
        &uuid,
        geometry(&image).0,
        &image[..4096],
        image.len() as u64,
    )
    .unwrap();
    let mut stable = image.clone();
    let mut operations = 0;
    loop {
        let pending = match core::recovery_request::dispatch(engine) {
            Ok(pending) => pending,
            Err(done) => {
                engine = done;
                break;
            }
        };
        if let core::recovery_io::Command::Write { block, image } = pending.pending_command() {
            stable[block as usize * 4096..(block as usize + 1) * 4096].copy_from_slice(image);
        }
        engine = pending.finish_pending(Completion::Succeeded);
        operations += 1;
    }
    assert_eq!(operations, 4);
    assert!(engine.finished());
    let header =
        core::journal_superblock::parse(&stable[base..base + 1024], &uuid, layout.blocks())
            .unwrap();
    assert_eq!((header.sequence, header.start), (u32::MAX, 0));
    let linux = linux_recover("build/terminal-retired.img", &stable);
    assert_eq!(
        &linux[target as usize * 4096..(target as usize + 1) * 4096],
        expected
    );
    let next = core::transaction::AfterImage::capture(target, &expected).unwrap();
    assert!(
        core::write_io::prepare(
            &stable[base..base + layout.blocks() as usize * 4096],
            &uuid,
            geometry(&stable).0,
            &stable[..4096],
            stable.len() as u64,
            vec![next],
        )
        .is_none()
    );
}

#[test]
fn constructed_transactions_recover_exact_owned_afterimages() {
    let (mut image, layout, seed, target) = fixture();
    let uuid = image[1128..1144].to_vec();
    let targets: Vec<_> = (1..layout.filesystem_blocks())
        .filter(|b| layout.allows_target(*b))
        .take(250)
        .collect();
    for count in [1, 2, 250] {
        let mut input = Vec::new();
        let mut expected = Vec::new();
        for i in 0..count {
            let mut bytes = vec![i as u8; 4096];
            if i % 2 == 0 {
                bytes[..4].copy_from_slice(&core::jbd2::MAGIC.to_be_bytes());
            }
            input.push(core::transaction::AfterImage::capture(targets[i], &bytes).unwrap());
            expected.push(bytes.clone());
            bytes.fill(0x55); // The transaction must not observe a caller's later mutation.
        }
        let tx = core::transaction::encode(
            input,
            &uuid,
            57,
            &layout,
            &image[..4096],
            image.len() as u64,
        )
        .unwrap();
        assert_eq!(tx.payload_count(), count);
        assert_eq!(tx.transaction_id(), 57);
        assert!(core::jbd2::valid_commit(tx.commit_bytes(), 57, seed));
        let descriptor = core::descriptor::parse(
            tx.descriptor_bytes(),
            &uuid,
            57,
            layout.filesystem_blocks(),
            seed,
        )
        .unwrap();
        assert_eq!(descriptor.tags().len(), count);
        for i in 0..count {
            let raw = tx.payload_at(i).unwrap();
            let decoded =
                core::replay::decode_payload(&descriptor.tags()[i], raw, 57, seed, &layout)
                    .unwrap();
            assert_eq!((decoded.block(), decoded.sequence()), (targets[i], 57));
            assert_eq!(decoded.image(), expected[i]);
            assert_eq!(
                tx.original_at(i).unwrap(),
                (targets[i], expected[i].as_slice())
            );
        }
        assert!(tx.payload_at(count).is_none());
        assert!(tx.original_at(count).is_none());
    }
    let same = || core::transaction::AfterImage::capture(target, &[0u8; 4096]).unwrap();
    assert!(
        core::transaction::encode(
            vec![same(), same()],
            &uuid,
            57,
            &layout,
            &image[..4096],
            image.len() as u64
        )
        .is_none()
    );
    assert!(
        core::transaction::encode(
            vec![same()],
            &uuid,
            u32::MAX,
            &layout,
            &image[..4096],
            image.len() as u64
        )
        .is_none()
    );
    let journal_target = (layout.offset(0, image.len() as u64).unwrap() / 4096) as u32;
    let illegal = core::transaction::AfterImage::capture(journal_target, &[0u8; 4096]).unwrap();
    assert!(
        core::transaction::encode(
            vec![illegal],
            &uuid,
            57,
            &layout,
            &image[..4096],
            image.len() as u64
        )
        .is_none()
    );
    let clear = core::transaction::AfterImage::capture(0, &image[..4096]).unwrap();
    assert!(
        core::transaction::encode(
            vec![clear],
            &uuid,
            57,
            &layout,
            &image[..4096],
            image.len() as u64
        )
        .is_none()
    );

    let dirty =
        core::super_state::recovery_image(&image[..4096], image.len() as u64, true).unwrap();
    image[..4096].copy_from_slice(dirty.as_slice());
    let mut metadata = image[..4096].to_vec();
    metadata[1144..1160].copy_from_slice(b"verus-encoded-tx");
    let checksum = core::crc::crc32c(0xffffffff, &metadata[1024..2044]);
    metadata[2044..2048].copy_from_slice(&checksum.to_le_bytes());
    let mut data = vec![0x71u8; 4096];
    data[..4].copy_from_slice(&core::jbd2::MAGIC.to_be_bytes());
    let tx = core::transaction::encode(
        vec![
            core::transaction::AfterImage::capture(0, &metadata).unwrap(),
            core::transaction::AfterImage::capture(target, &data).unwrap(),
        ],
        &uuid,
        57,
        &layout,
        &image[..4096],
        image.len() as u64,
    )
    .unwrap();
    let base = layout.offset(0, image.len() as u64).unwrap() as usize;
    let activated =
        core::journal_state::encode(&image[base..base + 4096], &uuid, layout.blocks(), 57, 1)
            .unwrap();
    image[base..base + 4096].copy_from_slice(activated.as_slice());
    let mut ordinal = 0;
    append_record(&mut image, &layout, 1, &mut ordinal, tx.descriptor_bytes());
    for i in 0..tx.payload_count() {
        append_record(
            &mut image,
            &layout,
            1,
            &mut ordinal,
            tx.payload_at(i).unwrap(),
        );
    }
    append_record(&mut image, &layout, 1, &mut ordinal, tx.commit_bytes());
    let recovered = core::scan::recover(
        &image[base..base + layout.blocks() as usize * 4096],
        &uuid,
        geometry(&image).0,
    )
    .unwrap();
    assert_eq!(recovered.committed_transactions(), 1);
    assert_eq!(recovered.replay_plan().len(), 2);
    for i in 0..2 {
        let w = recovered.replay_plan().get(i).unwrap();
        assert_eq!(
            w.image(),
            if w.block() == 0 {
                metadata.as_slice()
            } else {
                data.as_slice()
            }
        );
    }
    let linux = linux_recover("build/linux-transaction.img", &image);
    assert_eq!(
        &linux[target as usize * 4096..(target as usize + 1) * 4096],
        data
    );
    assert_eq!(&linux[1144..1160], b"verus-encoded-tx");
}

#[test]
fn repeated_recovery_crashes_keep_admission_and_committed_superblock_updates() {
    let (mut stable, layout, _, target) = fixture();
    let uuid = stable[1128..1144].to_vec();
    let base = layout.offset(0, stable.len() as u64).unwrap() as usize;
    let mut primary = core::super_state::recovery_image(&stable[..4096], stable.len() as u64, true)
        .unwrap()
        .as_slice()
        .to_vec();
    primary[1144..1160].copy_from_slice(b"verus-repeat-sb0");
    let checksum = core::crc::crc32c(0xffffffff, &primary[1024..2044]);
    primary[2044..2048].copy_from_slice(&checksum.to_le_bytes());
    let data = vec![0xabu8; 4096];
    let input = vec![
        core::transaction::AfterImage::capture(0, &primary).unwrap(),
        core::transaction::AfterImage::capture(target, &data).unwrap(),
    ];
    let mut writer = core::write_io::prepare(
        &stable[base..base + layout.blocks() as usize * 4096],
        &uuid,
        geometry(&stable).0,
        &stable[..4096],
        stable.len() as u64,
        input,
    )
    .unwrap();
    let mut cache: Vec<(u32, Vec<u8>)> = Vec::new();
    let persist = |stable: &mut Vec<u8>, cache: &mut Vec<(u32, Vec<u8>)>| {
        for (block, bytes) in cache.drain(..) {
            stable[block as usize * 4096..(block as usize + 1) * 4096].copy_from_slice(&bytes);
        }
    };
    let mut fences = 0;
    while fences < 4 {
        let pending = core::write_io::dispatch(writer).ok().unwrap();
        match pending.pending_command() {
            core::recovery_io::Command::Write { block, image } => {
                cache.push((block, image.to_vec()))
            }
            core::recovery_io::Command::Flush => {
                persist(&mut stable, &mut cache);
                fences += 1;
            }
        }
        writer = pending.finish_pending(Completion::Succeeded);
    }
    assert!(!writer.finished());
    assert!(cache.is_empty());
    let scan = core::scan::recover(
        &stable[base..base + layout.blocks() as usize * 4096],
        &uuid,
        geometry(&stable).0,
    )
    .unwrap();
    assert_eq!(scan.committed_transactions(), 1);
    assert_eq!(scan.replay_plan().len(), 2);
    for (attempt, commands) in [1usize, 2, 3, 4].into_iter().enumerate() {
        let mut recovery = core::recovery_io::prepare(
            &stable[base..base + layout.blocks() as usize * 4096],
            &uuid,
            geometry(&stable).0,
            &stable[..4096],
            stable.len() as u64,
        )
        .expect("an interrupted recovery must remain admissible");
        for _ in 0..commands {
            let pending = core::recovery_request::dispatch(recovery).ok().unwrap();
            match pending.pending_command() {
                core::recovery_io::Command::Write { block, image } => {
                    cache.push((block, image.to_vec()))
                }
                core::recovery_io::Command::Flush => persist(&mut stable, &mut cache),
            }
            recovery = pending.finish_pending(Completion::Succeeded);
        }
        assert!(!recovery.finished());
        persist(&mut stable, &mut cache); // A crash may persist all queued writes.
        let linux = linux_recover(&format!("build/repeated-recovery-{attempt}.img"), &stable);
        assert_eq!(
            &linux[target as usize * 4096..(target as usize + 1) * 4096],
            data
        );
        assert_eq!(&linux[1144..1160], b"verus-repeat-sb0");
    }
    let mut recovery = core::recovery_io::prepare(
        &stable[base..base + layout.blocks() as usize * 4096],
        &uuid,
        geometry(&stable).0,
        &stable[..4096],
        stable.len() as u64,
    )
    .unwrap();
    loop {
        let pending = match core::recovery_request::dispatch(recovery) {
            Ok(pending) => pending,
            Err(done) => {
                recovery = done;
                break;
            }
        };
        match pending.pending_command() {
            core::recovery_io::Command::Write { block, image } => {
                cache.push((block, image.to_vec()))
            }
            core::recovery_io::Command::Flush => persist(&mut stable, &mut cache),
        }
        recovery = pending.finish_pending(Completion::Succeeded);
    }
    assert!(recovery.finished());
    assert!(cache.is_empty());
    assert_eq!(
        &stable[target as usize * 4096..(target as usize + 1) * 4096],
        data
    );
    assert_eq!(&stable[1144..1160], b"verus-repeat-sb0");
}

#[test]
fn journal_reuse_preserves_prior_generations_across_every_final_writer_cut() {
    fn pattern(value: u8) -> Vec<u8> {
        let mut image = vec![value; 4096];
        image[..4].copy_from_slice(&core::jbd2::MAGIC.to_be_bytes());
        image
    }
    fn start(image: &[u8], updates: &[(u32, u8)]) -> core::write_io::Writer {
        let layout = geometry(image).0;
        let base = layout.offset(0, image.len() as u64).unwrap() as usize;
        let input = updates
            .iter()
            .map(|&(block, value)| {
                core::transaction::AfterImage::capture(block, &pattern(value)).unwrap()
            })
            .collect();
        core::write_io::prepare(
            &image[base..base + layout.blocks() as usize * 4096],
            &image[1128..1144],
            layout,
            &image[..4096],
            image.len() as u64,
            input,
        )
        .unwrap()
    }
    fn flush(image: &mut [u8], cache: &mut Vec<(u32, Vec<u8>)>) {
        for (block, bytes) in cache.drain(..) {
            image[block as usize * 4096..(block as usize + 1) * 4096].copy_from_slice(&bytes);
        }
    }
    let (mut stable, layout, _, target) = fixture();
    let base = layout.offset(0, stable.len() as u64).unwrap() as usize;
    let mut last_sequence = 0;
    for updates in [
        vec![(target, 0x11), (target + 1, 0x22)],
        vec![(target, 0x33)],
        vec![(target + 1, 0x55)],
    ] {
        let mut writer = start(&stable, &updates);
        let mut cache = Vec::new();
        loop {
            let pending = match core::write_io::dispatch(writer) {
                Ok(pending) => pending,
                Err(done) => {
                    writer = done;
                    break;
                }
            };
            match pending.pending_command() {
                core::recovery_io::Command::Write { block, image } => {
                    cache.push((block, image.to_vec()))
                }
                core::recovery_io::Command::Flush => flush(&mut stable, &mut cache),
            }
            writer = pending.finish_pending(Completion::Succeeded);
        }
        assert!(writer.finished());
        assert!(cache.is_empty());
        let header = core::journal_superblock::parse(
            &stable[base..base + 1024],
            &stable[1128..1144],
            layout.blocks(),
        )
        .unwrap();
        assert_eq!(header.start, 0);
        assert!(header.sequence > last_sequence);
        last_sequence = header.sequence;
    }
    assert_eq!(
        &stable[target as usize * 4096..(target as usize + 1) * 4096],
        pattern(0x33)
    );
    assert_eq!(
        &stable[(target as usize + 1) * 4096..(target as usize + 2) * 4096],
        pattern(0x55)
    );
    let mut writer = start(&stable, &[(target, 0x77)]);
    let mut cache = Vec::new();
    let mut cut = 0;
    loop {
        let pending = match core::write_io::dispatch(writer) {
            Ok(pending) => pending,
            Err(done) => {
                writer = done;
                break;
            }
        };
        match pending.pending_command() {
            core::recovery_io::Command::Write { block, image } => {
                cache.push((block, image.to_vec()))
            }
            core::recovery_io::Command::Flush => flush(&mut stable, &mut cache),
        }
        let mut crash = stable.clone();
        let mut persisted = cache.clone();
        flush(&mut crash, &mut persisted);
        let recovered = linux_recover(&format!("build/multi-generation-cut-{cut}.img"), &crash);
        let first = &recovered[target as usize * 4096..(target as usize + 1) * 4096];
        assert!(
            first == pattern(0x33) || first == pattern(0x77),
            "cut {cut}"
        );
        assert_eq!(
            &recovered[(target as usize + 1) * 4096..(target as usize + 2) * 4096],
            pattern(0x55),
            "cut {cut}: prior acknowledged data"
        );
        writer = pending.finish_pending(Completion::Succeeded);
        cut += 1;
    }
    assert!(writer.finished());
    assert_eq!(cut, 13);
    assert!(cache.is_empty());
    assert_eq!(
        &stable[target as usize * 4096..(target as usize + 1) * 4096],
        pattern(0x77)
    );
}

#[test]
fn writer_crash_cuts_recover_before_or_after_and_success_is_retired() {
    let (mut initial, layout, _, target) = fixture();
    let uuid = initial[1128..1144].to_vec();
    let base = layout.offset(0, initial.len() as u64).unwrap() as usize;
    let stale = core::jbd2::encode_header(2, 400).unwrap();
    let last = base + (layout.blocks() as usize - 1) * 4096;
    initial[last..last + 12].copy_from_slice(&stale); // Freshness must ignore checksum validity.
    let old_data = initial[target as usize * 4096..(target as usize + 1) * 4096].to_vec();
    let old_label = initial[1144..1160].to_vec();
    let dirty =
        core::super_state::recovery_image(&initial[..4096], initial.len() as u64, true).unwrap();
    let mut metadata = dirty.as_slice().to_vec();
    metadata[1144..1160].copy_from_slice(b"verus-writer-tx!");
    let checksum = core::crc::crc32c(0xffffffff, &metadata[1024..2044]);
    metadata[2044..2048].copy_from_slice(&checksum.to_le_bytes());
    let mut data = vec![0x63u8; 4096];
    data[..4].copy_from_slice(&core::jbd2::MAGIC.to_be_bytes());
    let input = || {
        vec![
            core::transaction::AfterImage::capture(0, &metadata).unwrap(),
            core::transaction::AfterImage::capture(target, &data).unwrap(),
        ]
    };
    let mut writer = core::write_io::prepare(
        &initial[base..base + layout.blocks() as usize * 4096],
        &uuid,
        geometry(&initial).0,
        &initial[..4096],
        initial.len() as u64,
        input(),
    )
    .unwrap();
    let mut stable = initial.clone();
    let mut cache: Vec<(u32, Vec<u8>)> = Vec::new();
    let mut committed = false;
    let mut operations = 0;
    loop {
        let pending = match core::write_io::dispatch(writer) {
            Ok(p) => p,
            Err(w) => {
                writer = w;
                break;
            }
        };
        match pending.pending_command() {
            core::recovery_io::Command::Write { block, image } => {
                if core::bytes::read_be32(image, 0) == Some(core::jbd2::MAGIC)
                    && core::bytes::read_be32(image, 4) == Some(2)
                {
                    assert_eq!(core::bytes::read_be32(image, 8), Some(401));
                    committed = true;
                }
                cache.push((block, image.to_vec()));
            }
            core::recovery_io::Command::Flush => {
                for (block, image) in cache.drain(..) {
                    stable[block as usize * 4096..(block as usize + 1) * 4096]
                        .copy_from_slice(&image);
                }
            }
        }
        let mut crash = stable.clone();
        for (block, image) in &cache {
            crash[*block as usize * 4096..(*block as usize + 1) * 4096].copy_from_slice(image);
        }
        let recovered = linux_recover(&format!("build/writer-cut-{operations}.img"), &crash);
        assert_eq!(
            &recovered[target as usize * 4096..(target as usize + 1) * 4096],
            if committed {
                data.as_slice()
            } else {
                old_data.as_slice()
            },
            "cut {operations}"
        );
        assert_eq!(
            &recovered[1144..1160],
            if committed {
                b"verus-writer-tx!".as_slice()
            } else {
                old_label.as_slice()
            }
        );
        writer = pending.finish_pending(Completion::Succeeded);
        operations += 1;
    }
    assert_eq!(operations, 15);
    assert!(writer.finished());
    assert!(!writer.failed());
    assert!(cache.is_empty());
    let journal = &stable[base..base + layout.blocks() as usize * 4096];
    let retired =
        core::journal_superblock::parse(&journal[..1024], &uuid, layout.blocks()).unwrap();
    assert_eq!((retired.sequence, retired.start), (402, 0));
    assert_eq!(
        &stable[target as usize * 4096..(target as usize + 1) * 4096],
        data
    );
    for fail_at in 0..operations {
        let mut writer = core::write_io::prepare(
            &initial[base..base + layout.blocks() as usize * 4096],
            &uuid,
            geometry(&initial).0,
            &initial[..4096],
            initial.len() as u64,
            input(),
        )
        .unwrap();
        for _ in 0..fail_at {
            let pending = core::write_io::dispatch(writer).ok().unwrap();
            writer = pending.finish_pending(Completion::Succeeded);
        }
        let pending = core::write_io::dispatch(writer)
            .ok()
            .unwrap()
            .abort_pending();
        let _ = pending.pending_command();
        let failed = pending.finish_pending(Completion::Failed);
        assert!(failed.failed());
        assert!(!failed.finished());
        assert!(core::write_io::dispatch(failed).is_err());
    }
}
