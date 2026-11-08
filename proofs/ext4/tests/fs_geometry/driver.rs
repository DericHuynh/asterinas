use verified_ext4::fs_geometry::{self,FsGeometry};
fn pair(r:Option<(u64,u64)>){match r{Some((a,b))=>println!("OK {a} {b}"),None=>println!("NONE")}}
fn main(){
 let a:Vec<String>=std::env::args().collect();
 let n=|i:usize|a[i].parse::<u64>().unwrap();
 if a[1]=="buffer" {
  let b=n(2) as usize;let s=n(3) as usize;let e=n(4) as usize;
  print!("{} ",fs_geometry::validated_buffer_range(b,s,e));
  pair(fs_geometry::buffer_sector_range(b,s,e).map(|(x,y)|(x as u64,y as u64)));return;
 }
 let g=match FsGeometry::new(n(2) as u32,n(3),n(4)){Some(g)=>g,None=>{println!("GEOMERR");return}};
 match a[1].as_str(){
  "new"=>{let d=g.duplicate();println!("OK {} {} {} {}",d.block_bytes(),d.filesystem_blocks(),d.partition_bytes(),d.partition_sectors());},
  "byte"=>pair(g.byte_range(n(5))),
  "sector"=>pair(g.sector_range(n(5))),
  "parent"=>pair(g.partition_sector_range(n(5),n(6),n(7))),
  "primary"=>pair(g.primary_superblock().map(|(x,y)|(x,y as u64))),
  "quota"=>pair(g.quota_placement(n(5)).map(|(x,y)|(x,y as u64))),
  _=>panic!("unknown operation"),
 }
}
