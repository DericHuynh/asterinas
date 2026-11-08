// SPDX-License-Identifier: MPL-2.0
// Positive model-use control: these values are not physical receipts.
use verified_ext4_sector_crash::sector_crash::{RequestId,SectorCrash};
fn good<T,E>(v:Result<T,E>)->T{match v{Ok(x)=>x,Err(_)=>panic!("unexpected model rejection")}}
fn main(){
 let id=RequestId{namespace:7,epoch:11,serial:19,target:23};
 let v=SectorCrash::candidate(&[0;4096],&[1;4096],id).unwrap();
 let v=good(v.record_completion(id));
 assert!(v.software_completed());assert_eq!(v.stable_bytes(),[0;4096]);
 let v=good(v.record_stable_piece(id,0));
 assert_eq!(&v.stable_bytes()[..512],[1;512]);
 assert_eq!(&v.stable_bytes()[512..],[0;3584]);
 assert_eq!(v.candidate_cut(&[true;8]).unwrap(),[1;4096]);
}
