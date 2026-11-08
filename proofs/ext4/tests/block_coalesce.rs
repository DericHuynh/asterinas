// SPDX-License-Identifier: MPL-2.0
use verified_ext4::{block_coalesce::BlockEditor, snapshot::Snapshot, source_block};

fn start(data: &[u8], number: u64, size: u32) -> BlockEditor {
    let source = Snapshot::from_bytes(data);
    BlockEditor::from_source(source_block::capture(&source, number, size).unwrap())
}
fn apply(editor: BlockEditor, offset: usize, expected: &[u8], replacement: &[u8]) -> BlockEditor {
    match editor.apply(offset, expected, replacement) {
        Ok(next) => next,
        Err(_) => panic!("valid disjoint edit rejected at {offset}"),
    }
}
fn reject(editor: BlockEditor, offset: usize, expected: &[u8], replacement: &[u8]) -> BlockEditor {
    let before = editor.raw().to_vec();
    let original = editor.original().raw().to_vec();
    match editor.apply(offset, expected, replacement) {
        Ok(_) => panic!("invalid/conflicting edit accepted at {offset}"),
        Err(same) => {
            assert_eq!(same.raw(), before);
            assert_eq!(same.original().raw(), original);
            same
        },
    }
}
fn main() {
    let mut blocks = 0usize;
    let mut edits = 0usize;
    let mut rejects = 0usize;
    for bits in 10..=16 {
        let size = 1usize << bits;
        let data: Vec<u8> = (0..size*3).map(|i| ((i*29+i/251+7)%256) as u8).collect();
        for number in 0..3u64 {
            let base = &data[number as usize*size..(number as usize+1)*size];
            let mut expected = base.to_vec();
            let mut editor = start(&data, number, size as u32);
            assert_eq!(editor.identity(), (number, size as u32));
            assert_eq!(editor.raw(), base);
            assert_eq!(editor.original().raw(), base);
            // Odd then even descending exercises coalescing independently of order.
            let count = size/1024;
            let order: Vec<_> = (0..count).rev().filter(|q| q%2==1)
                .chain((0..count).rev().filter(|q| q%2==0)).collect();
            for q in order {
                let offset=q*1024;
                let replacement: Vec<_> = base[offset..offset+1024].iter().map(|v| v^0xa5).collect();
                editor=apply(editor,offset,&base[offset..offset+1024],&replacement);
                expected[offset..offset+1024].copy_from_slice(&replacement);
                assert_eq!(editor.raw(),expected);
                assert_eq!(editor.original().raw(),base);
                edits+=1;
            }
            // All source bytes are now covered; repeated, partial and same-byte edits fail.
            editor=reject(editor,0,&base[..1024],&expected[..1024]);rejects+=1;
            editor=reject(editor,size-1,&base[size-1..],&expected[size-1..]);rejects+=1;
            editor=reject(editor,0,&[],&[]);rejects+=1;
            editor=reject(editor,usize::MAX,&[0],&[1]);rejects+=1;
            editor=reject(editor,size,&[0],&[1]);rejects+=1;
            editor=reject(editor,0,&[0],&[]);rejects+=1;
            match editor.into_after_image() {
                Ok(image) => {assert_eq!(size,4096);assert_eq!(image.block() as u64,number);assert_eq!(image.as_slice(),expected);},
                Err(same) => {assert_ne!(size,4096);assert_eq!(same.raw(),expected);assert_eq!(same.original().raw(),base);},
            }
            blocks+=1;
        }
        // Stale preimages and invalid spans cannot discard any accepted edit.
        let base=&data[..size];
        let mut editor=start(&data,0,size as u32);
        let stale: Vec<_>=base[..513].iter().map(|v|v^1).collect();
        editor=reject(editor,17,&stale,&stale);rejects+=1;
        editor=reject(editor,size-1,&[0,0],&[1,1]);rejects+=1;
        let replacement=vec![0x62;513];
        editor=apply(editor,17,&base[17..530],&replacement);edits+=1;
        let mut expected=base.to_vec();expected[17..530].copy_from_slice(&replacement);
        assert_eq!(editor.raw(),expected);
        editor=reject(editor,529,&base[529..531],&[9,9]);rejects+=1;
        editor=reject(editor,16,&base[16..18],&[9,9]);rejects+=1;
        editor=reject(editor,0,&base[..600],&vec![9;600]);rejects+=1;
        assert_eq!(editor.raw(),expected);
        // Rejection leaves hidden coverage unchanged, including adjacent bytes.
        editor=apply(editor,530,&base[530..540],&[0x8a;10]);edits+=1;
        expected[530..540].fill(0x8a);assert_eq!(editor.raw(),expected);
        // A no-op still reserves its interval; changed-byte detection is insufficient.
        let no_op=apply(start(&data,0,size as u32),0,&base[..16],&base[..16]);edits+=1;
        let no_op=reject(no_op,0,&base[..16],&[0x71;16]);rejects+=1;
        let no_op=apply(no_op,16,&base[16..32],&[0x71;16]);edits+=1;
        let mut no_op_expected=base.to_vec();no_op_expected[16..32].fill(0x71);
        assert_eq!(no_op.raw(),no_op_expected);
        // Two separated intervals produce the same exact full block in either order.
        let a=vec![0x19;103];let b=vec![0xf4;97];
        let left=apply(apply(start(&data,1,size as u32),7,&data[size+7..size+110],&a),
            size-99,&data[2*size-99..2*size-2],&b);
        let right=apply(apply(start(&data,1,size as u32),size-99,&data[2*size-99..2*size-2],&b),
            7,&data[size+7..size+110],&a);
        assert_eq!(left.raw(),right.raw());
        assert_eq!(left.original().raw(),&data[size..2*size]);
        edits+=4;
    }
    println!("coalesce: {blocks} complete-block cases, {edits} accepted edits, {rejects} rejected edits; all exact byte checks passed");
}
