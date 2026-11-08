// SPDX-License-Identifier: MPL-2.0
//! Prepared native regressions for the sector-crash CANDIDATE RAM model.
//! Not executed yet. These do not model a physical device or calculate CRCs.
#![forbid(unsafe_code)]

use verified_ext4_sector_crash::sector_crash::{Error, RequestId, SectorCrash, PIECE_BYTES};

fn good<T, E>(r: Result<T, E>) -> T {
    match r { Ok(value) => value, Err(_) => panic!("unexpected rejection") }
}
fn id() -> RequestId { RequestId { namespace: 7, epoch: 11, serial: 19, target: 23 } }
fn capture(v: &SectorCrash) -> (Vec<u8>, Vec<u8>, Vec<bool>, RequestId, bool) {
    (v.issued_bytes().to_vec(), v.stable_bytes().to_vec(), v.stable_piece_flags().to_vec(),
        v.request_identity(), v.software_completed())
}
fn reject_completion(v: SectorCrash, report: RequestId, expected: Error) -> SectorCrash {
    let before = capture(&v);
    match v.record_completion(report) {
        Err((owner, error)) => { assert_eq!(error, expected); assert_eq!(capture(&owner), before); owner },
        Ok(_) => panic!("report should reject"),
    }
}
fn reject_piece(v: SectorCrash, report: RequestId, piece: usize, expected: Error) -> SectorCrash {
    let before = capture(&v);
    match v.record_stable_piece(report, piece) {
        Err((owner, error)) => { assert_eq!(error, expected); assert_eq!(capture(&owner), before); owner },
        Ok(_) => panic!("piece should reject"),
    }
}
#[test]
fn all_geometries_copy_exact_issued_piece_and_preserve_every_neighbor() {
    for length in [1024,2048,4096,8192,16384,32768,65536] {
        let base = vec![0x11; length];
        let issued = (0..length).map(|i| (i % 251) as u8).collect::<Vec<_>>();
        let mut v = SectorCrash::candidate(&base, &issued, id()).unwrap();
        assert_eq!(v.issued_bytes(), issued);
        assert_eq!(v.stable_bytes(), base);
        assert_eq!(v.stable_piece_flags().len(), length / PIECE_BYTES);
        let piece = length / PIECE_BYTES - 1;
        v = good(v.record_stable_piece(id(), piece));
        for index in 0..length {
            assert_eq!(v.stable_bytes()[index], if index / PIECE_BYTES == piece { issued[index] } else { base[index] });
        }
        let once = capture(&v);
        v = good(v.record_stable_piece(id(), piece));
        assert_eq!(capture(&v), once);
        assert!(!v.software_completed());
        let flags = v.stable_piece_flags().to_vec();
        assert_eq!(v.candidate_cut(&flags).unwrap(), v.stable_bytes());
        assert!(v.candidate_cut(&vec![false; flags.len()]).is_none());
    }
}
#[test]
fn completion_is_software_only_and_retains_issued_bytes_and_pieces() {
    let base = vec![0x11;4096]; let issued = vec![0x22;4096];
    let v = SectorCrash::candidate(&base,&issued,id()).unwrap();
    let v = good(v.record_completion(id()));
    assert!(v.software_completed());
    assert_eq!(v.stable_bytes(),base);
    assert_ne!(v.stable_bytes(),issued);
    assert!(v.stable_piece_flags().iter().all(|&x|!x));
    assert_eq!(v.issued_bytes(),issued);
    let v = reject_completion(v,id(),Error::AlreadyCompleted);
    let v = good(v.record_stable_piece(id(),3));
    assert!(v.software_completed());
    assert_eq!(&v.stable_bytes()[1536..2048],&issued[1536..2048]);
}
#[test]
fn exact_namespace_epoch_serial_and_target_reports_are_required() {
    let mut v=SectorCrash::candidate(&vec![0;4096],&vec![1;4096],id()).unwrap();
    for report in [
        RequestId{namespace:8,..id()},RequestId{epoch:10,..id()},
        RequestId{serial:18,..id()},RequestId{target:24,..id()},
    ] {
        v=reject_completion(v,report,Error::Identity);
        v=reject_piece(v,report,0,Error::Identity);
    }
    v=reject_piece(v,id(),8,Error::Piece);
    v=reject_piece(v,id(),usize::MAX,Error::Piece);
    assert_eq!(v.stable_bytes(),vec![0;4096]);
    assert!(!v.software_completed());
}
#[test]
fn every_4096_piece_subset_is_available_before_any_stability_event() {
    let base=vec![0x31;4096];let issued=vec![0xa2;4096];
    let v=SectorCrash::candidate(&base,&issued,id()).unwrap();
    for bits in 0u32..256 {
        let mask=(0..8).map(|piece|bits&(1<<piece)!=0).collect::<Vec<_>>();
        let cut=v.candidate_cut(&mask).unwrap();
        for piece in 0..8 {
            assert_eq!(&cut[piece*512..piece*512+512],
                if mask[piece] { &issued[piece*512..piece*512+512] } else { &base[piece*512..piece*512+512] });
        }
    }
}
#[test]
fn changed_bytes_in_separate_sectors_have_a_cut_equal_to_neither_image() {
    let base=vec![0x40;4096];let mut issued=base.clone();
    issued[1120]=0x41;issued[2044]=0x42;
    let v=SectorCrash::candidate(&base,&issued,id()).unwrap();
    let mut mask=vec![false;8];mask[2]=true;
    let cut=v.candidate_cut(&mask).unwrap();
    assert_eq!(1120/512,2);assert_eq!(2044/512,3);
    assert_eq!(cut[1120],issued[1120]);assert_eq!(cut[2044],base[2044]);
    assert_ne!(cut,base);assert_ne!(cut,issued);
    // No checksum is calculated or classified: the test proves only byte mixing.
}
#[test]
fn all_old_or_all_new_masks_recover_the_atomic_whole_image_special_case() {
    let base=vec![0x51;4096];let issued=vec![0x62;4096];
    let v=SectorCrash::candidate(&base,&issued,id()).unwrap();
    assert_eq!(v.candidate_cut(&[false;8]).unwrap(),base);
    assert_eq!(v.candidate_cut(&[true;8]).unwrap(),issued);
}
#[test]
fn invalid_geometry_or_mask_shape_rejects_without_an_image() {
    for length in [0,512,1000,3072,65537] {
        assert!(SectorCrash::candidate(&vec![0;length],&vec![1;length],id()).is_none());
    }
    assert!(SectorCrash::candidate(&vec![0;4096],&vec![1;4095],id()).is_none());
    let v=SectorCrash::candidate(&vec![0;4096],&vec![1;4096],id()).unwrap();
    assert!(v.candidate_cut(&[false;7]).is_none());
    assert!(v.candidate_cut(&[false;9]).is_none());
}
