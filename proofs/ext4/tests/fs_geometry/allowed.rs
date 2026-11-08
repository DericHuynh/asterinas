use verified_ext4::fs_geometry::FsGeometry;
fn main(){let g=FsGeometry::new(1024,2,2048).unwrap();assert_eq!(g.primary_superblock(),Some((1,0)));assert_eq!(g.duplicate().byte_range(1),Some((1024,2048)));}
