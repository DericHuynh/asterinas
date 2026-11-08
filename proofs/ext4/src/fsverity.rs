// SPDX-License-Identifier: MPL-2.0

//! Linux fs-verity descriptors, SHA-2 Merkle construction and immutable reads.
//! A descriptor digest must come from an authorized external policy. Matching
//! attacker-selected bytes establishes no signature or filesystem authority.
//! PKCS#7 signature validation, immutable-inode publication and kernel storage
//! integration remain separate. This implementation is awaiting proof.

use vstd::prelude::*;
use crate::{bytes,block_size,crypto_sha2};

verus! {

pub const MAX_DESCRIPTOR_BYTES: usize = 16384;
pub const MAX_LEVELS: usize = 8;
pub const MAX_READ_BYTES: usize = 16777216;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error { Descriptor, Version, Algorithm, BlockSize, Salt, Reserved, Size,
    SignatureBounds, TooDeep, Overflow, TreeBounds, DataBounds, DigestMismatch,
    Corrupt, ResourceLimit, HashFailure, ExtentsRequired }

pub closed spec fn digest_bytes(algorithm:u8) -> nat {if algorithm==1 {32}else if algorithm==2 {64}else{0}}
fn digest_size(algorithm:u8) -> (r:Result<usize,Error>)
    ensures match r {Ok(n)=>n==digest_bytes(algorithm) && (n==32 || n==64),Err(_)=>digest_bytes(algorithm)==0},
{
    if algorithm==1 {Ok(32)}else if algorithm==2 {Ok(64)}else{Err(Error::Algorithm)}
}

pub closed spec fn le64_prefix(raw:Seq<u8>,offset:int,n:nat) -> u64
    decreases n
{
    if n==0 {0u64}
    else {le64_prefix(raw,offset,(n-1) as nat)
        |((raw[offset+(n-1) as int] as u64)<<(((n-1)*8) as u32))}
}
pub closed spec fn encoded64(value:u64) -> Seq<u8> {
    Seq::new(8,|i:int| (value>>((i*8) as u32)) as u8)
}

pub closed spec fn hash_reference(algorithm:u8,raw:Seq<u8>) -> Seq<u8> {
    if algorithm==1 {crypto_sha2::digest256_reference(raw)}
    else if algorithm==2 {crypto_sha2::digest512_reference(raw)}
    else {Seq::empty()}
}
pub closed spec fn salt_prefix(algorithm:u8,salt:Seq<u8>) -> Seq<u8> {
    if salt.len()==0 {Seq::empty()}
    else {Seq::new(if algorithm==1 {64nat}else{128nat},|i:int| if i<salt.len() {salt[i]}else{0u8})}
}
pub closed spec fn salted_hash_reference(algorithm:u8,salt:Seq<u8>,raw:Seq<u8>) -> Seq<u8> {
    hash_reference(algorithm,salt_prefix(algorithm,salt)+raw)
}
pub closed spec fn data_block_reference(data:Seq<u8>,number:nat,size:nat) -> Seq<u8> {
    Seq::new(size,|i:int| if number*size+i<data.len() {data[(number*size) as int+i]}else{0u8})
}
pub closed spec fn tree_block_reference(tree:Seq<u8>,number:nat,size:nat) -> Seq<u8> {
    if number*size+size<=tree.len() {tree.subrange((number*size) as int,(number*size+size) as int)}
    else {Seq::empty()}
}
pub closed spec fn measured_header(raw:Seq<u8>) -> Seq<u8> {
    Seq::new(256,|i:int| if 4<=i<8 {0u8}else{raw[i]})
}
pub closed spec fn descriptor_wire(algorithm:u8,log_blocksize:u8,data_size:u64,root:Seq<u8>,salt:Seq<u8>,signature:Seq<u8>) -> Seq<u8> {
    Seq::new(256,|i:int| {
        if i==0 {1u8}else if i==1 {algorithm}else if i==2 {log_blocksize}else if i==3 {salt.len() as u8}
        else if i<8 {bytes::encoded_le(signature.len() as u32)[i-4]}
        else if i<16 {encoded64(data_size)[i-8]}
        else if 16<=i<16+root.len() {root[i-16]}
        else if 80<=i<80+salt.len() {salt[i-80]}
        else {0u8}
    })+signature
}
fn read_le64(raw:&[u8],offset:usize) -> (r:u64)
    requires offset<=raw.len(),8<=raw.len()-offset,
    ensures r==le64_prefix(raw@,offset as int,8),
{
    let mut value=0u64;let mut i=0usize;
    while i<8
        invariant i<=8,offset<=raw.len(),8<=raw.len()-offset,
            value==le64_prefix(raw@,offset as int,i as nat),
        decreases 8-i,
    {value|=(raw[offset+i] as u64)<<(8*i);i+=1;}value
}
fn write_le64(raw:&mut [u8],offset:usize,value:u64)
    requires offset<=old(raw).len(),8<=old(raw).len()-offset,
    ensures final(raw).len()==old(raw).len(),
        final(raw)@==bytes::splice(old(raw)@,offset as int,encoded64(value)),
{
    let ghost before=raw@;
    let mut i=0usize;
    while i<8
        invariant i<=8,offset<=raw.len(),8<=raw.len()-offset,raw.len()==before.len(),
            forall|j:int| #![trigger raw@[j]] 0<=j<raw.len() ==> raw@[j]==
                if offset<=j<offset+i {encoded64(value)[j-offset as int]}else{before[j]},
        decreases 8-i,
    {raw[offset+i]=(value>>(8*i)) as u8;i+=1;}
}
fn copy(raw:&[u8]) -> (r:Vec<u8>) ensures r@==raw@ {
    let mut v=Vec::new();let mut i=0usize;
    while i<raw.len()
        invariant i<=raw.len(),v@==raw@.take(i as int),
        decreases raw.len()-i,
    {v.push(raw[i]);i+=1;}v
}


pub closed spec fn ceil_arity(blocks:nat,arity:nat) -> nat {
    if arity==0 {0}else{blocks/arity+if blocks%arity==0 {0nat}else{1nat}}
}
pub closed spec fn level_count(data:nat,arity:nat,n:nat) -> nat
    decreases n
{
    if n==0 {data}else{ceil_arity(level_count(data,arity,(n-1) as nat),arity)}
}
pub closed spec fn count_sum(counts:Seq<u64>,n:nat) -> nat
    decreases n
{
    if n==0 {0}else{count_sum(counts,(n-1) as nat)+counts[(n-1) as int] as nat}
}

proof fn rounded_count_bounds(blocks:nat,arity:nat)
    requires arity>=1,
    ensures ceil_arity(blocks,arity)<=blocks,
        blocks>0 ==> ceil_arity(blocks,arity)>0,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(blocks as int,arity as int);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(blocks as int,arity as int);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(blocks as int,arity as int);
    vstd::arithmetic::mul::lemma_mul_inequality(1,arity as int,(blocks/arity) as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(arity as int,(blocks/arity) as int);
    if blocks%arity==0 {
        if blocks>0 {assert(blocks/arity>0);}
    }else{
        assert(blocks%arity>=1);
    }
}
proof fn data_count_bound(size:u64,block:u32)
    requires block>=1024,
    ensures ceil_arity(size as nat,block as nat)<=18014398509481984,
{
    vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(size as int,1024,block as int);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(size as int,u64::MAX as int,1024);
    assert((u64::MAX as nat)/1024==18014398509481983);
}
proof fn count_sum_monotone(counts:Seq<u64>,a:nat,b:nat)
    requires a<=b<=counts.len(),
    ensures count_sum(counts,a)<=count_sum(counts,b),
    decreases b,
{
    if a<b {count_sum_monotone(counts,a,(b-1) as nat);}
}

proof fn parent_slot_bound(children:nat,arity:nat,parent:nat,slot:nat)
    requires arity>0,parent<ceil_arity(children,arity),slot<arity,
    ensures parent*arity<children,parent*arity+slot<children+arity,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(children as int,arity as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(arity as int,(children/arity) as int);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(children as int,arity as int);
    if children%arity==0 {
        assert(parent<children/arity);
        vstd::arithmetic::mul::lemma_mul_strict_inequality(parent as int,(children/arity) as int,arity as int);
    }else{
        assert(parent<=children/arity);
        vstd::arithmetic::mul::lemma_mul_inequality(parent as int,(children/arity) as int,arity as int);
    }
}
proof fn geometry(block:u32,digest:u32)
    requires block_size::accepted(block as nat),digest==32 || digest==64,
    ensures 16<=block/digest<=2048,block%digest==0,
        block as nat==(block/digest) as nat*digest as nat,
{
    if digest==32 {}else{assert(digest==64);}
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(block as int,digest as int);
}
proof fn slot_bounds(slot:u64,arity:u64,digest:u32,block:u32)
    requires slot<arity,digest>0,block as nat==arity as nat*digest as nat,
    ensures (slot as nat)*(digest as nat)<block,
        (slot as nat)*(digest as nat)+(digest as nat)<=block,
{
    vstd::arithmetic::mul::lemma_mul_strict_inequality(slot as int,arity as int,digest as int);
    vstd::arithmetic::mul::lemma_mul_inequality(slot as int+1,arity as int,digest as int);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(digest as int,slot as int,1);
}
proof fn index_parent_bound(index:nat,children:nat,arity:nat)
    requires arity>0,index<children,
    ensures index/arity<ceil_arity(children,arity),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(children as int,arity as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(arity as int,(children/arity) as int);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(index as int,children as int,arity as int);
    if children%arity==0 {
        vstd::arithmetic::div_mod::lemma_div_by_multiple_is_strongly_ordered(
            index as int,children as int,(children/arity) as int,arity as int);
    }
}
proof fn read_block_bounds(data:nat,block:nat,offset:nat,take:nat)
    requires block>0,offset<data,0<take,offset+take<=data,
    ensures offset/block<=((offset+take-1) as nat)/block<ceil_arity(data,block),
{
    vstd::arithmetic::div_mod::lemma_div_is_ordered(offset as int,offset as int+take as int-1,block as int);
    index_parent_bound((offset+take-1) as nat,data,block);
}
proof fn destination_bound(start:nat,parents:nat,parent:nat,slot:u64,arity:u64,digest:u32,block:u32,total:nat)
    requires parent<parents,start+parents<=total,slot<arity,digest>0,
        block as nat==arity as nat*digest as nat,
    ensures (start+parent)*block as nat+slot as nat*digest as nat+digest as nat<=total*block as nat,
{
    slot_bounds(slot,arity,digest,block);
    vstd::arithmetic::mul::lemma_mul_inequality(start as int+parent as int+1,total as int,block as int);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(block as int,start as int+parent as int,1);
}
pub closed spec fn ancestor(index:nat,arity:nat,steps:nat) -> nat
    decreases steps
{
    if steps==0 {index}else if arity==0 {0}
    else {ancestor(index,arity,(steps-1) as nat)/arity}
}
#[derive(Clone, Copy)]
pub struct Layout {
    block_bytes:u32,digest_bytes:u32,data_blocks:u64,levels:u8,
    level_start:[u64;8],level_blocks:[u64;8],tree_blocks:u64,
}
impl Layout {
    pub closed spec fn layout_valid(&self) -> bool {
        block_size::accepted(self.block_bytes as nat)
            && (self.digest_bytes==32 || self.digest_bytes==64)
            && self.levels<=8 && self.data_blocks<=18014398509481984
            && 16<=self.block_bytes/self.digest_bytes<=2048
            && self.block_bytes%self.digest_bytes==0
            && ((self.data_blocks<=1)==(self.levels==0))
            && (self.levels>0 ==> self.level_blocks@[self.levels as int-1]==1)
            && (forall|i:int| #![trigger self.level_blocks@[i]] 0<=i<self.levels as int-1
                ==> self.level_blocks@[i]>1)
            && (forall|i:int| #![trigger self.level_blocks@[i]] 0<=i<self.levels ==> self.level_blocks@[i] as nat
                ==level_count(self.data_blocks as nat,(self.block_bytes/self.digest_bytes) as nat,(i+1) as nat))
            && (forall|i:int| #![trigger self.level_blocks@[i]] 0<=i<self.levels ==> 0<self.level_blocks@[i]<=self.data_blocks
                && self.level_start@[i] as nat+self.level_blocks@[i] as nat<=self.tree_blocks as nat)
            && (forall|i:int| #![trigger self.level_start@[i]] 0<=i<self.levels ==> self.level_start@[i] as nat
                ==count_sum(self.level_blocks@,self.levels as nat)-count_sum(self.level_blocks@,(i+1) as nat))
            && self.tree_blocks==count_sum(self.level_blocks@,self.levels as nat)
            && self.tree_blocks as nat*self.block_bytes as nat<=u64::MAX
    }
    pub closed spec fn layout_fields(&self) -> (u32,u32,u64,u8,u64) {
        (self.block_bytes,self.digest_bytes,self.data_blocks,self.levels,self.tree_blocks)
    }
    pub closed spec fn layout_level(&self,number:u8) -> Option<(u64,u64)> {
        if number>=self.levels {None}else{Some((self.level_start@[number as int],self.level_blocks@[number as int]))}
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {self.layout_valid()}
    proof fn level_children(&self,number:nat)
        requires self.layout_valid(),number<self.levels,
        ensures self.level_blocks@[number as int] as nat
            ==ceil_arity(if number==0 {self.data_blocks as nat}
                else {self.level_blocks@[number as int-1] as nat},
                (self.block_bytes/self.digest_bytes) as nat),
    {
        assert(self.level_blocks@[number as int] as nat
            ==level_count(self.data_blocks as nat,(self.block_bytes/self.digest_bytes) as nat,number+1));
        if number>0 {
            assert(self.level_blocks@[number as int-1] as nat
                ==level_count(self.data_blocks as nat,(self.block_bytes/self.digest_bytes) as nat,number));
        }
    }
    pub fn dimensions(&self) -> (r:(u32,u32,u64,u8,u64)) ensures r==self.layout_fields(),self.layout_valid() {proof {use_type_invariant(self);}(self.block_bytes,self.digest_bytes,self.data_blocks,self.levels,self.tree_blocks)}
    pub fn level(&self,number:u8) -> (r:Option<(u64,u64)>)
        ensures r==self.layout_level(number),
    {
        proof {use_type_invariant(self);}
        if number>=self.levels {None}else{Some((self.level_start[number as usize],self.level_blocks[number as usize]))}
    }
    pub fn tree_bytes(&self) -> (r:Result<u64,Error>)
        ensures match r {Ok(n)=>n as nat==self.layout_fields().4 as nat*self.layout_fields().0 as nat,Err(_)=>false},
    {
        proof {use_type_invariant(self);}
        match self.tree_blocks.checked_mul(self.block_bytes as u64){Some(n)=>Ok(n),None=>Err(Error::Overflow)}
    }
}
pub fn layout(data_size:u64,algorithm:u8,log_blocksize:u8) -> (r:Result<Layout,Error>)
    ensures match r {Ok(l)=>l.layout_valid() && 10<=log_blocksize<=16
        && l.layout_fields().0==1u32<<log_blocksize && l.layout_fields().1==digest_bytes(algorithm)
        && l.layout_fields().2==ceil_arity(data_size as nat,l.layout_fields().0 as nat),Err(_)=>true},
{
    let digest=digest_size(algorithm)? as u32;
    if log_blocksize<10 || log_blocksize>16 {return Err(Error::BlockSize);}
    let block=1u32<<log_blocksize;let arity=(block/digest) as u64;
    proof {
        assert(block==1024 || block==2048 || block==4096 || block==8192
            || block==16384 || block==32768 || block==65536) by(bit_vector)
            requires 10<=log_blocksize<=16,block==1u32<<log_blocksize,;
        assert(block_size::accepted(block as nat));
        geometry(block,digest);
        data_count_bound(data_size,block);
    }
    let data_blocks=data_size/block as u64 + if data_size%block as u64==0 {0}else{1};
    let mut blocks=data_blocks;let mut levels=0usize;let mut counts=[0u64;8];
    while blocks>1
        invariant levels<=8,16<=arity<=2048,block>=1024,
            block_size::accepted(block as nat),digest==32 || digest==64,
            arity==(block/digest) as u64,block%digest==0,
            data_blocks==ceil_arity(data_size as nat,block as nat),
            data_blocks<=18014398509481984,blocks<=data_blocks,
            (data_blocks>0 ==> blocks>0),
            blocks==level_count(data_blocks as nat,arity as nat,levels as nat),
            forall|i:int| #![trigger counts@[i]] 0<=i<levels ==> counts@[i] as nat
                ==level_count(data_blocks as nat,arity as nat,(i+1) as nat)
                && 0<counts@[i]<=data_blocks,
            data_blocks<=1 ==> levels==0,
            levels>0 ==> counts@[levels as int-1]==blocks,
            forall|i:int| #![trigger counts@[i]] 0<=i<levels as int-1 ==> counts@[i]>1,
        decreases 9-levels,
    {
        let ghost previous_blocks=blocks;
        let ghost previous_levels=levels;
        let ghost previous_counts=counts@;
        if levels==8 {return Err(Error::TooDeep);}
        proof {rounded_count_bounds(blocks as nat,arity as nat);}
        blocks=blocks/arity + if blocks%arity==0 {0}else{1};
        counts[levels]=blocks;levels+=1;
        proof {
            assert(counts@==previous_counts.update(previous_levels as int,blocks));
            assert forall|i:int| 0<=i<levels as int-1 implies #[trigger] counts@[i]>1 by {
                assert(i<previous_levels);
                vstd::seq::lemma_seq_update_different(previous_counts,i,previous_levels as int,blocks);
                if i<previous_levels as int-1 {assert(previous_counts[i]>1);}
                else {
                    assert(i==previous_levels as int-1 && previous_levels>0);
                    assert(previous_counts[i]==previous_blocks && previous_blocks>1);
                }
            }
        }
    }
    proof {
        assert((data_blocks<=1)==(levels==0));
        assert(levels>0 ==> counts@[levels as int-1]==1);
    }
    let mut starts=[0u64;8];let mut total=0u64;let mut level=levels;
    while level>0
        invariant level<=levels<=8,total as nat==count_sum(counts@,levels as nat)-count_sum(counts@,level as nat),
            block_size::accepted(block as nat),digest==32 || digest==64,
            16<=arity<=2048,arity==(block/digest) as u64,block%digest==0,
            data_blocks==ceil_arity(data_size as nat,block as nat),
            data_blocks<=18014398509481984,(data_blocks<=1)==(levels==0),
            levels>0 ==> counts@[levels as int-1]==1,
            forall|i:int| #![trigger counts@[i]] 0<=i<levels as int-1 ==> counts@[i]>1,
            forall|i:int| #![trigger counts@[i]] 0<=i<levels ==> counts@[i] as nat
                ==level_count(data_blocks as nat,arity as nat,(i+1) as nat)
                && 0<counts@[i]<=data_blocks,
            forall|j:int| #![trigger starts@[j]] level<=j<levels ==> starts@[j] as nat
                ==count_sum(counts@,levels as nat)-count_sum(counts@,(j+1) as nat),
        decreases level,
    {
        level-=1;starts[level]=total;
        total=match total.checked_add(counts[level]){Some(v)=>v,None=>return Err(Error::Overflow)};
    }
    if total>u64::MAX/block as u64 {return Err(Error::Overflow);}
    proof {
        vstd::arithmetic::mul::lemma_mul_inequality(total as int,(u64::MAX/block as u64) as int,block as int);
        vstd::arithmetic::div_mod::lemma_remainder_lower(u64::MAX as int,block as int);
        assert(total as nat*block as nat<=u64::MAX);
        assert(total as nat==count_sum(counts@,levels as nat));
        assert forall|j:int| #![trigger starts@[j]] 0<=j<levels implies starts@[j] as nat+counts@[j] as nat<=total as nat by {
            count_sum_monotone(counts@,(j+1) as nat,levels as nat);
            assert(count_sum(counts@,(j+1) as nat)==count_sum(counts@,j as nat)+counts@[j] as nat);
        }
    }
    Ok(Layout {block_bytes:block,digest_bytes:digest,data_blocks,levels:levels as u8,level_start:starts,level_blocks:counts,tree_blocks:total})
}

pub struct Descriptor<'a> {
    raw:&'a[u8],algorithm:u8,log_blocksize:u8,salt_size:u8,data_size:u64,signature_size:usize,
}
pub fn parse<'a>(raw:&'a[u8],inode_size:u64,filesystem_block_bits:u8,memory_block_bits:u8) -> (r:Result<Descriptor<'a>,Error>)
    ensures match r {Ok(d)=>d.descriptor_valid() && d.descriptor_raw()==raw@ && d.descriptor_fields().2==inode_size
        && d.descriptor_fields().1<=filesystem_block_bits && d.descriptor_fields().1<=memory_block_bits,Err(_)=>true},
{
    if raw.len()<256 || raw.len()>MAX_DESCRIPTOR_BYTES {return Err(Error::Descriptor);}
    if raw[0]!=1 {return Err(Error::Version);}
    digest_size(raw[1])?;
    if raw[2]<10 || raw[2]>16 || raw[2]>filesystem_block_bits || raw[2]>memory_block_bits {return Err(Error::BlockSize);}
    if raw[3]>32 {return Err(Error::Salt);}
    let mut i=112usize;
    while i<256
        invariant 112<=i<=256,256<=raw.len()<=MAX_DESCRIPTOR_BYTES,
            forall|j:int| #![trigger raw@[j]] 112<=j<i ==> raw@[j]==0,
        decreases 256-i,
    {if raw[i]!=0{return Err(Error::Reserved);}i+=1;}
    let size=read_le64(raw,8);if size!=inode_size{return Err(Error::Size);}
    let signature_size=match bytes::read_le32(raw,4){Some(n)=>n as usize,None=>return Err(Error::Descriptor)};
    if signature_size>raw.len()-256 {return Err(Error::SignatureBounds);}
    layout(size,raw[1],raw[2])?;
    Ok(Descriptor {raw,algorithm:raw[1],log_blocksize:raw[2],salt_size:raw[3],data_size:size,signature_size})
}
impl<'a> Descriptor<'a> {
    pub closed spec fn descriptor_valid(&self) -> bool {
        256<=self.raw.len()<=MAX_DESCRIPTOR_BYTES && (self.algorithm==1 || self.algorithm==2)
            && 10<=self.log_blocksize<=16 && self.salt_size<=32
            && self.signature_size<=self.raw.len()-256
            && self.raw@[0]==1 && self.raw@[1]==self.algorithm
            && self.raw@[2]==self.log_blocksize && self.raw@[3]==self.salt_size
            && self.data_size==le64_prefix(self.raw@,8,8)
            && self.signature_size==bytes::le32(self.raw@,4)
            && forall|i:int| #![trigger self.raw@[i]] 112<=i<256 ==> self.raw@[i]==0
    }
    pub closed spec fn descriptor_raw(&self) -> Seq<u8> {self.raw@}
    pub closed spec fn descriptor_fields(&self) -> (u8,u8,u64) {(self.algorithm,self.log_blocksize,self.data_size)}
    pub closed spec fn descriptor_salt(&self) -> Seq<u8> {self.raw@.subrange(80,80+self.salt_size as int)}
    pub closed spec fn descriptor_root(&self) -> Seq<u8> {self.raw@.subrange(16,16+digest_bytes(self.algorithm) as int)}
    pub closed spec fn descriptor_signature(&self) -> Seq<u8> {self.raw@.subrange(256,256+self.signature_size as int)}
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {self.descriptor_valid()}
    pub fn fields(&self) -> (r:(u8,u8,u64)) ensures r==self.descriptor_fields() {(self.algorithm,self.log_blocksize,self.data_size)}
    pub fn salt(&self) -> (r:&'a[u8])
        ensures r@==self.descriptor_salt(),r.len()<=32,
    {proof {use_type_invariant(self);}&self.raw[80..80+self.salt_size as usize]}
    pub fn root_hash(&self) -> (r:&'a[u8])
        ensures r@==self.descriptor_root(),
            r.len()==digest_bytes(self.descriptor_fields().0),
    {proof {use_type_invariant(self);}&self.raw[16..16+if self.algorithm==1 {32}else{64}]}
    pub fn signature(&self) -> (r:&'a[u8])
        ensures r@==self.descriptor_signature(),
    {proof {use_type_invariant(self);}&self.raw[256..256+self.signature_size]}
    pub fn measure(&self) -> (r:Result<Vec<u8>,Error>)
        ensures match r {Ok(v)=>v.len()==digest_bytes(self.descriptor_fields().0)
            && v@==hash_reference(self.descriptor_fields().0,measured_header(self.descriptor_raw())),Err(_)=>true},
    {
        proof {use_type_invariant(self);}
        let mut header=copy(&self.raw[..256]);let mut i=4usize;
        while i<8
            invariant 4<=i<=8,header.len()==256,
                forall|j:int| #![trigger header@[j]] 0<=j<256 ==> header@[j]==if 4<=j<i {0u8}else{self.raw@[j]},
            decreases 8-i,
        {header[i]=0;i+=1;}
        proof {assert(header@ =~= measured_header(self.raw@));}
        hash_buffer(self.algorithm,header.as_slice())
    }
    pub fn measure_formatted_digest(&self) -> Result<Vec<u8>,Error> {
        let digest=self.measure()?;formatted_digest(self.algorithm,digest.as_slice())
    }
}
fn hash_buffer(algorithm:u8,raw:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==digest_bytes(algorithm)
        && v@==hash_reference(algorithm,raw@),Err(_)=>true},
{
    let result=if algorithm==1 {crypto_sha2::sha256(raw)}
        else if algorithm==2 {crypto_sha2::sha512(raw)}else{return Err(Error::Algorithm)};
    match result {Ok(v)=>Ok(v),Err(_)=>Err(Error::HashFailure)}
}
/// Salt is zero-padded to the hash compression-block size before each hash.
pub fn hash_block(algorithm:u8,salt:&[u8],block:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==digest_bytes(algorithm)
        && v@==salted_hash_reference(algorithm,salt@,block@),Err(_)=>true},
{
    if salt.len()>32 {return Err(Error::Salt);}
    if !block_size::valid(block.len()) {return Err(Error::BlockSize);}
    if algorithm==1 {
        let mut h=crypto_sha2::Sha256::new256();
        if salt.len()>0 {
            let mut prefix=[0u8;64];let mut i=0usize;
            while i<salt.len()
                invariant i<=salt.len()<=32,
                    forall|j:int| #![trigger prefix@[j]] 0<=j<64 ==> prefix@[j]==if j<i {salt@[j]}else{0u8},
                decreases salt.len()-i,
            {prefix[i]=salt[i];i+=1;}
            proof {assert(prefix@ =~= salt_prefix(algorithm,salt@));}
            if h.update256(&prefix).is_err(){return Err(Error::HashFailure);}
        }
        if h.update256(block).is_err(){return Err(Error::HashFailure);}Ok(h.finalize256())
    } else if algorithm==2 {
        let mut h=crypto_sha2::Sha512::new512();
        if salt.len()>0 {
            let mut prefix=[0u8;128];let mut i=0usize;
            while i<salt.len()
                invariant i<=salt.len()<=32,
                    forall|j:int| #![trigger prefix@[j]] 0<=j<128 ==> prefix@[j]==if j<i {salt@[j]}else{0u8},
                decreases salt.len()-i,
            {prefix[i]=salt[i];i+=1;}
            proof {assert(prefix@ =~= salt_prefix(algorithm,salt@));}
            if h.update512(&prefix).is_err(){return Err(Error::HashFailure);}
        }
        if h.update512(block).is_err(){return Err(Error::HashFailure);}Ok(h.finalize512())
    } else {Err(Error::Algorithm)}
}
pub closed spec fn formatted(algorithm:u8,digest:Seq<u8>) -> Seq<u8> {
    seq![70u8,83u8,86u8,101u8,114u8,105u8,116u8,121u8,algorithm,0u8,digest.len() as u8,0u8]+digest
}
pub fn formatted_digest(algorithm:u8,digest:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v@==formatted(algorithm,digest@),Err(_)=>true},
{
    if digest.len()!=digest_size(algorithm)? {return Err(Error::Size);}
    let mut out=Vec::new();let magic=[70u8,83,86,101,114,105,116,121];let mut i=0usize;
    while i<8 invariant i<=8,out@==magic@.take(i as int), decreases 8-i, {out.push(magic[i]);i+=1;}out.push(algorithm);out.push(0);out.push(digest.len() as u8);out.push(0);
    let ghost header=out@;
    i=0;
    while i<digest.len()
        invariant i<=digest.len(),out@==header+digest@.take(i as int),
        decreases digest.len()-i,
    {out.push(digest[i]);i+=1;}Ok(out)
}
pub fn parse_formatted_digest(raw:&[u8]) -> (r:Result<(u8,Vec<u8>),Error>)
    ensures match r {Ok(v)=>(v.0==1 || v.0==2) && v.1.len()==digest_bytes(v.0)
        && raw@==formatted(v.0,v.1@),Err(_)=>true},
{
    if raw.len()<12 {return Err(Error::Size);}
    if !bytes::equal(&raw[..8],&[70u8,83,86,101,114,105,116,121]) {return Err(Error::Descriptor);}
    let algorithm=match bytes::read_le16(raw,8){Some(v)=>v,None=>return Err(Error::Size)};
    if algorithm>255 {return Err(Error::Algorithm);}
    let len=digest_size(algorithm as u8)?;
    if bytes::read_le16(raw,10)!=Some(len as u16) || raw.len()!=12+len {return Err(Error::Size);}
    Ok((algorithm as u8,copy(&raw[12..])))
}
pub fn encode_descriptor(algorithm:u8,log_blocksize:u8,data_size:u64,root_hash:&[u8],salt:&[u8],signature:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v@==descriptor_wire(algorithm,log_blocksize,data_size,root_hash@,salt@,signature@)
        && 256<=v.len()<=MAX_DESCRIPTOR_BYTES && v.len()==256+signature.len()
        && root_hash.len()==digest_bytes(algorithm) && salt.len()<=32
        && 10<=log_blocksize<=16,Err(_)=>true},
{
    if root_hash.len()!=digest_size(algorithm)? {return Err(Error::Size);}
    if salt.len()>32 {return Err(Error::Salt);}
    if signature.len()>MAX_DESCRIPTOR_BYTES-256 {return Err(Error::SignatureBounds);}
    layout(data_size,algorithm,log_blocksize)?;
    let mut out=Vec::new();let mut i=0usize;
    while i<256
        invariant i<=256,out@==Seq::new(i as nat,|j:int| 0u8),
        decreases 256-i,
    {out.push(0);i+=1;}
    out[0]=1;out[1]=algorithm;out[2]=log_blocksize;out[3]=salt.len() as u8;
    let sig=bytes::encode_le32(signature.len() as u32);let ghost fixed=out@;i=0;
    while i<4
        invariant i<=4,out.len()==256,
            forall|j:int| #![trigger out@[j]] 0<=j<256 ==> out@[j]==if 4<=j<4+i {sig@[j-4]}else{fixed[j]},
        decreases 4-i,
    {out[4+i]=sig[i];i+=1;}
    write_le64(out.as_mut_slice(),8,data_size);
    let ghost before_root=out@;i=0;
    while i<root_hash.len()
        invariant i<=root_hash.len()<=64,out.len()==256,
            forall|j:int| #![trigger out@[j]] 0<=j<256 ==> out@[j]==
                if 16<=j<16+i {root_hash@[j-16]}else{before_root[j]},
        decreases root_hash.len()-i,
    {out[16+i]=root_hash[i];i+=1;}
    let ghost before_salt=out@;i=0;
    while i<salt.len()
        invariant i<=salt.len()<=32,out.len()==256,
            forall|j:int| #![trigger out@[j]] 0<=j<256 ==> out@[j]==
                if 80<=j<80+i {salt@[j-80]}else{before_salt[j]},
        decreases salt.len()-i,
    {out[80+i]=salt[i];i+=1;}
    let ghost header=out@;
    proof {
        assert(header =~= descriptor_wire(algorithm,log_blocksize,data_size,root_hash@,salt@,signature@).take(256));
    }
    i=0;
    while i<signature.len()
        invariant i<=signature.len()<=MAX_DESCRIPTOR_BYTES-256,
            out@==header+signature@.take(i as int),
        decreases signature.len()-i,
    {out.push(signature[i]);i+=1;}Ok(out)
}
fn block<'a>(tree:&'a[u8],number:u64,size:u32) -> (r:Result<&'a[u8],Error>)
    ensures match r {Ok(v)=>v.len()==size
        && number as nat*size as nat+size as nat<=tree.len()
        && v@==tree_block_reference(tree@,number as nat,size as nat),Err(_)=>true},
{
    let start=match number.checked_mul(size as u64){Some(n)=>n,None=>return Err(Error::Overflow)};
    if start>usize::MAX as u64 {return Err(Error::TreeBounds);}
    let at=start as usize;
    if at>tree.len() || tree.len()-at<size as usize {return Err(Error::TreeBounds);}
    Ok(&tree[at..at+size as usize])
}
fn padded_data(data:&[u8],number:u64,size:u32) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==size
        && v@==data_block_reference(data@,number as nat,size as nat),Err(_)=>true},
{
    let start=match number.checked_mul(size as u64){Some(n)=>n,None=>return Err(Error::Overflow)};
    if start>usize::MAX as u64 || start as usize>=data.len() {return Err(Error::DataBounds);}
    let at=start as usize;let remain=data.len()-at;let take=if remain<size as usize {remain}else{size as usize};
    let mut out=Vec::new();let mut i=0usize;
    while i<size as usize
        invariant i<=size as usize,at<data.len(),take<=data.len()-at,take<=size as usize,out.len()==i,
            forall|j:int| #![trigger out@[j]] 0<=j<i ==> out@[j]==if j<take {data@[at as int+j]}else{0u8},
        decreases size as usize-i,
    {out.push(if i<take {data[at+i]}else{0});i+=1;}Ok(out)
}

/// Immutable file/tree/descriptor borrow, bound to an externally selected
/// descriptor digest. Opening checks metadata measurement; each read verifies
/// every traversed hash block and data block before returning any file bytes.
pub struct Verifier<'a> {data:&'a[u8],tree:&'a[u8],descriptor:Descriptor<'a>,layout:Layout,digest:Vec<u8>}
impl<'a> Verifier<'a> {
    pub closed spec fn verifier_valid(&self) -> bool {
        self.descriptor.descriptor_valid() && self.layout.layout_valid()
            && self.data.len()==self.descriptor.data_size
            && self.layout.block_bytes==1u32<<self.descriptor.log_blocksize
            && self.layout.digest_bytes==digest_bytes(self.descriptor.algorithm)
            && self.layout.data_blocks==ceil_arity(self.data.len() as nat,self.layout.block_bytes as nat)
            && self.layout.tree_blocks as nat*self.layout.block_bytes as nat<=self.tree.len()
            && self.digest.len()==digest_bytes(self.descriptor.algorithm)
            && self.digest@==hash_reference(self.descriptor.algorithm,measured_header(self.descriptor.raw@))
    }
    pub closed spec fn verified_source(&self) -> Seq<u8> {self.data@}
    pub closed spec fn expected_measurement(&self) -> Seq<u8> {self.digest@}
    pub closed spec fn verifier_descriptor_raw(&self) -> Seq<u8> {self.descriptor.raw@}
    pub closed spec fn source_blocks(&self) -> nat {self.layout.data_blocks as nat}

    spec fn path_block(&self,index:nat,level:nat) -> Seq<u8> {
        let arity=(self.layout.block_bytes/self.layout.digest_bytes) as nat;
        let number=self.layout.level_start@[level as int] as nat+ancestor(index,arity,level+1);
        tree_block_reference(self.tree@,number,self.layout.block_bytes as nat)
    }
    spec fn path_slot(&self,index:nat,level:nat) -> Seq<u8> {
        let arity=(self.layout.block_bytes/self.layout.digest_bytes) as nat;
        let at=(ancestor(index,arity,level)%arity)*self.layout.digest_bytes as nat;
        self.path_block(index,level).subrange(at as int,(at+self.layout.digest_bytes as nat) as int)
    }
    spec fn path_wanted(&self,index:nat,level:nat) -> Seq<u8> {
        if level==self.layout.levels {
            self.descriptor.raw@.subrange(16,16+digest_bytes(self.descriptor.algorithm) as int)
        } else {self.path_slot(index,level)}
    }
    /// Acceptance is a relation on actual borrowed bytes and actual SHA-2
    /// results. It does not assert collision resistance or signature authority.
    pub closed spec fn block_path_accepted(&self,index:nat) -> bool {
        index<self.layout.data_blocks
            && (forall|level:int| #![trigger self.path_block(index,level as nat)]
                0<=level<self.layout.levels ==>
                self.path_block(index,level as nat).len()==self.layout.block_bytes
                && salted_hash_reference(self.descriptor.algorithm,
                    self.descriptor.raw@.subrange(80,80+self.descriptor.salt_size as int),
                    self.path_block(index,level as nat))==self.path_wanted(index,(level+1) as nat))
            && salted_hash_reference(self.descriptor.algorithm,
                self.descriptor.raw@.subrange(80,80+self.descriptor.salt_size as int),
                data_block_reference(self.data@,index,self.layout.block_bytes as nat))==self.path_wanted(index,0)
    }
    pub closed spec fn read_paths_accepted(&self,offset:nat,length:nat) -> bool {
        let take=if offset>=self.data.len() {0nat}
            else if self.data.len()-offset<length {(self.data.len()-offset) as nat}else{length};
        take==0 || forall|index:int| #![trigger self.block_path_accepted(index as nat)]
            offset/(self.layout.block_bytes as nat)<=index<=((offset+take-1) as nat)/(self.layout.block_bytes as nat)
            ==> self.block_path_accepted(index as nat)
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {self.verifier_valid()}
    pub fn open(data:&'a[u8],tree:&'a[u8],raw_descriptor:&'a[u8],expected_digest:&[u8],filesystem_block_bits:u8,memory_block_bits:u8) -> (r:Result<Self,Error>)
        ensures match r {Ok(v)=>v.verifier_valid() && v.verified_source()==data@
            && v.expected_measurement()==expected_digest@ && v.verifier_descriptor_raw()==raw_descriptor@,Err(_)=>true},
    {
        let descriptor=parse(raw_descriptor,data.len() as u64,filesystem_block_bits,memory_block_bits)?;
        let digest=descriptor.measure()?;
        if !bytes::equal(digest.as_slice(),expected_digest) {return Err(Error::DigestMismatch);}
        let l=layout(descriptor.data_size,descriptor.algorithm,descriptor.log_blocksize)?;
        if l.tree_bytes()?>tree.len() as u64 {return Err(Error::TreeBounds);}
        Ok(Self {data,tree,descriptor,layout:l,digest})
    }
    pub fn file_digest(&self) -> (r:&[u8]) ensures r@==self.expected_measurement() {self.digest.as_slice()}
    pub fn verify_block(&self,index:u64) -> (r:Result<(),Error>)
        ensures r.is_ok() ==> self.block_path_accepted(index as nat),
    {
        proof {use_type_invariant(self);use_type_invariant(&self.layout);use_type_invariant(&self.descriptor);}
        if index>=self.layout.data_blocks {return Err(Error::DataBounds);}
        let arity=(self.layout.block_bytes/self.layout.digest_bytes) as u64;
        proof {geometry(self.layout.block_bytes,self.layout.digest_bytes);}
        let mut numbers=[0u64;8];let mut offsets=[0usize;8];let mut child=index;let mut level=0usize;
        while level<self.layout.levels as usize
            invariant level<=self.layout.levels as usize<=8,arity>=16,
                arity==(self.layout.block_bytes/self.layout.digest_bytes) as u64,
                self.layout.block_bytes as nat==arity as nat*self.layout.digest_bytes as nat,
                self.layout.digest_bytes>0,self.layout.block_bytes<=65536,index<self.layout.data_blocks,
                self.verifier_valid(),child==ancestor(index as nat,arity as nat,level as nat),
                forall|i:int| #![trigger numbers@[i]] 0<=i<level ==> numbers@[i] as nat
                    ==self.layout.level_start@[i] as nat+ancestor(index as nat,arity as nat,(i+1) as nat),
                forall|i:int| #![trigger offsets@[i]] 0<=i<level ==> offsets@[i] as nat
                    ==(ancestor(index as nat,arity as nat,i as nat)%arity as nat)*self.layout.digest_bytes as nat,
                forall|i:int| #![trigger offsets@[i]] 0<=i<level ==> offsets@[i]<self.layout.block_bytes,
            decreases self.layout.levels as usize-level,
        {
            let parent=child/arity;
            numbers[level]=match self.layout.level_start[level].checked_add(parent){Some(n)=>n,None=>return Err(Error::Overflow)};
            proof {
                vstd::arithmetic::div_mod::lemma_mod_pos_bound(child as int,arity as int);
                slot_bounds(child%arity,arity,self.layout.digest_bytes,self.layout.block_bytes);
            }
            offsets[level]=((child%arity)*self.layout.digest_bytes as u64) as usize;
            child=parent;level+=1;
        }
        let mut wanted=copy(self.descriptor.root_hash());
        while level>0
            invariant level<=self.layout.levels as usize<=8,self.verifier_valid(),
                index<self.layout.data_blocks,
                arity==(self.layout.block_bytes/self.layout.digest_bytes) as u64,
                wanted@==self.path_wanted(index as nat,level as nat),
                forall|i:int| #![trigger numbers@[i]] 0<=i<self.layout.levels ==> numbers@[i] as nat
                    ==self.layout.level_start@[i] as nat+ancestor(index as nat,arity as nat,(i+1) as nat),
                forall|i:int| #![trigger offsets@[i]] 0<=i<self.layout.levels ==> offsets@[i] as nat
                    ==(ancestor(index as nat,arity as nat,i as nat)%arity as nat)*self.layout.digest_bytes as nat,
                forall|i:int| #![trigger self.path_block(index as nat,i as nat)]
                    level<=i<self.layout.levels ==>
                    self.path_block(index as nat,i as nat).len()==self.layout.block_bytes
                    && salted_hash_reference(self.descriptor.algorithm,
                        self.descriptor.raw@.subrange(80,80+self.descriptor.salt_size as int),
                        self.path_block(index as nat,i as nat))==self.path_wanted(index as nat,(i+1) as nat),
            decreases level,
        {
            let ghost previous_level=level;
            let ghost previous_wanted=wanted@;
            level-=1;
            let raw=block(self.tree,numbers[level],self.layout.block_bytes)?;
            let actual=hash_block(self.descriptor.algorithm,self.descriptor.salt(),raw)?;
            proof {
                assert(raw@==self.path_block(index as nat,level as nat));
                assert(raw.len()==self.layout.block_bytes);
                assert(previous_wanted==self.path_wanted(index as nat,level as nat+1));
                assert(actual@==salted_hash_reference(self.descriptor.algorithm,
                    self.descriptor.raw@.subrange(80,80+self.descriptor.salt_size as int),
                    self.path_block(index as nat,level as nat)));
            }
            if !bytes::equal(wanted.as_slice(),actual.as_slice()){return Err(Error::Corrupt);}
            proof {
                assert(salted_hash_reference(self.descriptor.algorithm,
                    self.descriptor.raw@.subrange(80,80+self.descriptor.salt_size as int),
                    self.path_block(index as nat,level as nat))==self.path_wanted(index as nat,level as nat+1));
            }
            let at=offsets[level];let len=self.layout.digest_bytes as usize;
            if at>raw.len() || raw.len()-at<len {return Err(Error::TreeBounds);}
            wanted=copy(&raw[at..at+len]);
            proof {
                assert(at as nat==(ancestor(index as nat,arity as nat,level as nat)%arity as nat)
                    *self.layout.digest_bytes as nat);
                assert(wanted@==raw@.subrange(at as int,at as int+len as int));
                assert(wanted@==self.path_slot(index as nat,level as nat));
                assert(wanted@==self.path_wanted(index as nat,level as nat));
                assert forall|i:int| #![trigger self.path_block(index as nat,i as nat)]
                    level<=i<self.layout.levels implies
                    self.path_block(index as nat,i as nat).len()==self.layout.block_bytes
                    && salted_hash_reference(self.descriptor.algorithm,
                        self.descriptor.raw@.subrange(80,80+self.descriptor.salt_size as int),
                        self.path_block(index as nat,i as nat))==self.path_wanted(index as nat,(i+1) as nat) by {
                    if i!=level {assert(previous_level<=i);}
                }
            }
        }
        let raw=padded_data(self.data,index,self.layout.block_bytes)?;
        let actual=hash_block(self.descriptor.algorithm,self.descriptor.salt(),raw.as_slice())?;
        if !bytes::equal(wanted.as_slice(),actual.as_slice()){return Err(Error::Corrupt);}
        Ok(())
    }
    pub fn verify_all(&self,block_budget:u64) -> (r:Result<(),Error>)
        ensures r.is_ok() ==> forall|index:int| #![trigger self.block_path_accepted(index as nat)] 0<=index<self.source_blocks()
            ==> self.block_path_accepted(index as nat),
    {
        if self.layout.data_blocks>block_budget{return Err(Error::ResourceLimit);}
        proof {use_type_invariant(self);}
        let mut i=0u64;
        while i<self.layout.data_blocks
            invariant i<=self.layout.data_blocks,self.verifier_valid(),
                forall|index:int| #![trigger self.block_path_accepted(index as nat)] 0<=index<i ==> self.block_path_accepted(index as nat),
            decreases self.layout.data_blocks-i,
        {self.verify_block(i)?;i+=1;}Ok(())
    }
    pub fn read(&self,offset:u64,length:usize) -> (r:Result<Vec<u8>,Error>)
        ensures match r {Ok(v)=>self.read_paths_accepted(offset as nat,length as nat)
            && v@==if offset>=self.verified_source().len() {Seq::<u8>::empty()}
            else {self.verified_source().subrange(offset as int,
                if (self.verified_source().len() - offset as nat) < length {self.verified_source().len() as int}else{offset as int+length as int})},
            Err(_)=>true},
    {
        proof {use_type_invariant(self);}
        if length>MAX_READ_BYTES {return Err(Error::ResourceLimit);}
        if offset>=self.descriptor.data_size {
            proof {assert(self.read_paths_accepted(offset as nat,length as nat));}
            return Ok(Vec::new());
        }
        if length==0 {
            proof {
                assert(self.read_paths_accepted(offset as nat,0));
                assert(self.data@.subrange(offset as int,offset as int) =~= Seq::<u8>::empty());
            }
            return Ok(Vec::new());
        }
        let available=self.descriptor.data_size-offset;
        let take=if available<length as u64 {available as usize}else{length};
        let end=offset+take as u64;
        proof {
            assert(0<take);
            assert(offset as nat+take as nat<=self.data.len());
            read_block_bounds(self.data.len() as nat,self.layout.block_bytes as nat,offset as nat,take as nat);
        }
        let mut i=offset/self.layout.block_bytes as u64;
        let last=(end-1)/self.layout.block_bytes as u64;
        let ghost first=i;
        while i<=last
            invariant first<=i<=last+1,last<self.layout.data_blocks,self.verifier_valid(),
                first==offset/self.layout.block_bytes as u64,
                last==((end-1) as u64)/(self.layout.block_bytes as u64),
                0<take,offset<self.data.len(),end==offset as nat+take as nat,end<=self.data.len(),
                take==if (self.data.len()-offset as nat)<length {(self.data.len()-offset as nat) as nat}else{length as nat},
                forall|index:int| #![trigger self.block_path_accepted(index as nat)]
                    first<=index<i ==> self.block_path_accepted(index as nat),
            decreases last+1-i,
        {
            self.verify_block(i)?;i+=1;
        }
        proof {
            assert(self.read_paths_accepted(offset as nat,length as nat));
            assert(offset as nat+take as nat==if (self.data.len()-offset as nat)<length
                {self.data.len() as nat}else{offset as nat+length as nat});
        }
        let start=offset as usize;
        Ok(copy(&self.data[start..start+take]))
    }
}

#[derive(Clone, Copy)]
pub struct BuildBudget {pub tree_bytes:usize,pub data_blocks:u64}
pub struct BuiltTree {tree:Vec<u8>,descriptor:Vec<u8>,digest:Vec<u8>}
impl BuiltTree {
    pub fn tree(&self) -> &[u8] {self.tree.as_slice()}
    pub fn descriptor(&self) -> &[u8] {self.descriptor.as_slice()}
    pub fn built_digest(&self) -> &[u8] {self.digest.as_slice()}
}
pub fn build(data:&[u8],algorithm:u8,log_blocksize:u8,salt:&[u8],budget:BuildBudget) -> Result<BuiltTree,Error> {
    if salt.len()>32 {return Err(Error::Salt);}
    let l=layout(data.len() as u64,algorithm,log_blocksize)?;let tree_size=l.tree_bytes()?;
    if tree_size>budget.tree_bytes as u64 || tree_size>usize::MAX as u64 || l.data_blocks>budget.data_blocks {return Err(Error::ResourceLimit);}
    let mut tree=Vec::new();let mut i=0usize;
    while i<tree_size as usize
        invariant i<=tree_size as usize,tree.len()==i,tree_size<=usize::MAX,
            forall|j:int| #![trigger tree@[j]] 0<=j<i ==> tree@[j]==0,
        decreases tree_size as usize-i,
    {tree.push(0);i+=1;}
    let arity=(l.block_bytes/l.digest_bytes) as u64;
    proof {geometry(l.block_bytes,l.digest_bytes);}
    let mut level=0usize;
    while level<l.levels as usize
        invariant level<=l.levels as usize<=8,l.layout_valid(),
            tree.len()==tree_size as usize,tree_size<=usize::MAX as u64,
            tree_size as nat==l.tree_blocks as nat*l.block_bytes as nat,
            16<=arity<=2048,l.block_bytes as nat==arity as nat*l.digest_bytes as nat,
            arity==(l.block_bytes/l.digest_bytes) as u64,
            l.digest_bytes==digest_bytes(algorithm),
        decreases l.levels as usize-level,
    {
        let children=if level==0 {l.data_blocks}else{l.level_blocks[level-1]};
        proof {l.level_children(level as nat);}
        let mut parent=0u64;
        while parent<l.level_blocks[level]
            invariant parent<=l.level_blocks@[level as int],
                level<l.levels as usize<=8,l.layout_valid(),
                tree.len()==tree_size as usize,tree_size<=usize::MAX as u64,
                tree_size as nat==l.tree_blocks as nat*l.block_bytes as nat,
                children<=18014398509481984,
                children==if level==0 {l.data_blocks}else{l.level_blocks@[level as int-1]},
                l.level_blocks@[level as int]==ceil_arity(children as nat,arity as nat),
                16<=arity<=2048,l.block_bytes as nat==arity as nat*l.digest_bytes as nat,
            arity==(l.block_bytes/l.digest_bytes) as u64,
                l.digest_bytes==digest_bytes(algorithm),
            decreases l.level_blocks@[level as int]-parent,
        {
            let mut slot=0u64;
            while slot<arity
                invariant slot<=arity,parent<l.level_blocks@[level as int],
                    level<l.levels as usize<=8,l.layout_valid(),
                    tree.len()==tree_size as usize,tree_size<=usize::MAX as u64,
                    tree_size as nat==l.tree_blocks as nat*l.block_bytes as nat,
                    children<=18014398509481984,
                    children==if level==0 {l.data_blocks}else{l.level_blocks@[level as int-1]},
                    l.level_blocks@[level as int]==ceil_arity(children as nat,arity as nat),
                    16<=arity<=2048,l.block_bytes as nat==arity as nat*l.digest_bytes as nat,
            arity==(l.block_bytes/l.digest_bytes) as u64,
                    l.digest_bytes==digest_bytes(algorithm),
                decreases arity-slot,
            {
                proof {
                    parent_slot_bound(children as nat,arity as nat,parent as nat,slot as nat);
                    assert(parent as nat*arity as nat+slot as nat<=u64::MAX);
                }
                let child=parent*arity+slot;if child>=children {break;}
                let digest=if level==0 {
                    let raw=padded_data(data,child,l.block_bytes)?;hash_block(algorithm,salt,raw.as_slice())?
                } else {
                    let number=l.level_start[level-1]+child;
                    let raw=block(tree.as_slice(),number,l.block_bytes)?;hash_block(algorithm,salt,raw)?
                };
                proof {
                    destination_bound(l.level_start@[level as int] as nat,l.level_blocks@[level as int] as nat,
                        parent as nat,slot,arity,l.digest_bytes,l.block_bytes,l.tree_blocks as nat);
                }
                let destination=(l.level_start[level]+parent)*l.block_bytes as u64+slot*l.digest_bytes as u64;
                if destination>usize::MAX as u64 {return Err(Error::Overflow);}
                proof {
                    assert(destination as nat+digest.len()<=tree_size as nat);
                    assert(tree.len() as nat==tree_size as nat);
                }
                let at=destination as usize;i=0;
                proof {assert(at as nat+digest.len()<=tree.len());}
                let ghost before_digest=tree@;
                while i<digest.len()
                    invariant i<=digest.len(),digest.len()==l.digest_bytes,
                        at as nat+digest.len()<=tree.len(),tree.len()==before_digest.len(),
                        forall|j:int| #![trigger tree@[j]] 0<=j<tree.len() ==> tree@[j]==
                            if at<=j<at+i {digest@[j-at as int]}else{before_digest[j]},
                    decreases digest.len()-i,
                {tree[at+i]=digest[i];i+=1;}slot+=1;
            }
            parent+=1;
        }
        level+=1;
    }
    let mut root=Vec::new();
    if l.data_blocks==0 {
        i=0;
        while i<l.digest_bytes as usize
            invariant i<=l.digest_bytes as usize,root.len()==i,
                l.digest_bytes==32 || l.digest_bytes==64,
            decreases l.digest_bytes as usize-i,
        {root.push(0);i+=1;}
    }
    else if l.levels==0 {let raw=padded_data(data,0,l.block_bytes)?;root=hash_block(algorithm,salt,raw.as_slice())?;}
    else {root=hash_block(algorithm,salt,block(tree.as_slice(),0,l.block_bytes)?)?;}
    let descriptor=encode_descriptor(algorithm,log_blocksize,data.len() as u64,root.as_slice(),salt,&[])?;
    let parsed=parse(descriptor.as_slice(),data.len() as u64,log_blocksize,log_blocksize)?;
    let digest=parsed.measure()?;Ok(BuiltTree {tree,descriptor,digest})
}

fn aligned(value:u64,unit:u64) -> (r:Result<u64,Error>)
    ensures match r {Ok(v)=>unit>0 && value<=v && v%unit==0 && (v as nat) < (value as nat+unit as nat),Err(_)=>true},
{
    if unit==0 {return Err(Error::BlockSize);}
    let rem=value%unit;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(value as int,unit as int);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(value as int,unit as int);
    }
    if rem==0 {Ok(value)}else{
        let next=match value.checked_add(unit-rem){Some(v)=>v,None=>return Err(Error::Overflow)};
        proof {
            vstd::arithmetic::mul::lemma_mul_is_commutative(unit as int,(value/unit) as int);
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(unit as int,(value/unit) as int,1);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_mod(
                next as int,unit as int,(value/unit) as int+1,0);
        }
        Ok(next)
    }
}
#[derive(Clone, Copy)]
pub struct Ext4Locations {pub tree_offset:u64,pub descriptor_offset:u64,pub size_word_offset:u64,pub allocated_end:u64}
/// Ext4 stores metadata beyond a 64 KiB-aligned i_size, with the descriptor
/// size in the final four bytes of the last allocated filesystem block.
pub fn ext4_locations(data_size:u64,tree_size:u64,descriptor_size:usize,filesystem_block_bytes:u32) -> Result<Ext4Locations,Error> {
    if !block_size::valid(filesystem_block_bytes as usize) {return Err(Error::BlockSize);}
    if descriptor_size<256 || descriptor_size>MAX_DESCRIPTOR_BYTES {return Err(Error::Descriptor);}
    let tree_offset=aligned(data_size,65536)?;
    let tree_end=match tree_offset.checked_add(tree_size){Some(n)=>n,None=>return Err(Error::Overflow)};
    let descriptor_offset=aligned(tree_end,filesystem_block_bytes as u64)?;
    let desc_end=match descriptor_offset.checked_add(descriptor_size as u64){Some(n)=>n,None=>return Err(Error::Overflow)};
    let with_size=match desc_end.checked_add(4){Some(n)=>n,None=>return Err(Error::Overflow)};
    let allocated_end=aligned(with_size,filesystem_block_bytes as u64)?;
    if allocated_end/filesystem_block_bytes as u64>0xffff_ffff {return Err(Error::Overflow);}
    Ok(Ext4Locations {tree_offset,descriptor_offset,size_word_offset:allocated_end-4,allocated_end})
}
pub fn locate_ext4_descriptor(data_size:u64,last_allocated_end:u64,last_block:&[u8],uses_extents:bool) -> Result<(u64,u32),Error> {
    if !uses_extents {return Err(Error::ExtentsRequired);}
    if !block_size::valid(last_block.len()) || last_allocated_end<last_block.len() as u64 || last_allocated_end%last_block.len() as u64!=0 {return Err(Error::BlockSize);}
    let len=match bytes::read_le32(last_block,last_block.len()-4){Some(n)=>n,None=>return Err(Error::Descriptor)};
    if len<256 || len as usize>MAX_DESCRIPTOR_BYTES {return Err(Error::Descriptor);}
    let word=last_allocated_end-4;if len as u64>word {return Err(Error::Descriptor);}
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(word as int-len as int,last_block.len() as int);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(word as int-len as int,last_block.len() as int);
        vstd::arithmetic::div_mod::lemma_remainder_lower(word as int-len as int,last_block.len() as int);
    }
    let at=((word-len as u64)/last_block.len() as u64)*last_block.len() as u64;
    if at<aligned(data_size,65536)? {return Err(Error::Descriptor);}
    Ok((at,len))
}

}
