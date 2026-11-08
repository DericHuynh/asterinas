use verified_ext4::fs_geometry::FsGeometry; fn main(){let mut g=FsGeometry::new(4096,2,8192).unwrap();g.partition_bytes=0;}
