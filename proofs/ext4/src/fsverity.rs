// SPDX-License-Identifier: MPL-2.0

//! Linux fs-verity descriptors, SHA-2 Merkle construction and immutable reads.
//! A descriptor digest must come from an authorized external policy. Matching
//! attacker-selected bytes establishes no signature or filesystem authority.
//! PKCS#7 signature validation, immutable-inode publication and kernel storage
//! integration remain separate. This implementation is awaiting proof.

use alloc::vec::Vec;

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
proof fn level_count_monotone(blocks:nat,arity:nat,first:nat,last:nat)
    requires arity>0,first<=last,
    ensures level_count(blocks,arity,last)<=level_count(blocks,arity,first),
    decreases last,
{
    if first<last {
        level_count_monotone(blocks,arity,first,(last-1) as nat);
        rounded_count_bounds(level_count(blocks,arity,(last-1) as nat),arity);
    }
}
proof fn count_sum_upper_bound(counts:Seq<u64>,depth:nat,bound:nat)
    requires depth<=counts.len(),
        forall|k:int| #![trigger counts[k]] 0<=k<depth ==> counts[k]<=bound,
    ensures count_sum(counts,depth)<=depth*bound,
    decreases depth,
{
    if depth>0 {
        count_sum_upper_bound(counts,(depth-1) as nat,bound);
        assert(counts[depth as int-1]<=bound);
        assert(depth*bound==(depth-1)*bound+bound) by(nonlinear_arith);
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
    ensures r.is_ok() <==> layout_admission(data_size as nat,algorithm,log_blocksize),
        match r {Ok(l)=>l.layout_valid() && 10<=log_blocksize<=16
        && l.layout_fields().0==1u32<<log_blocksize && l.layout_fields().1==digest_bytes(algorithm)
        && l.layout_fields().2==ceil_arity(data_size as nat,l.layout_fields().0 as nat)
        && layout_reference(l,data_size,algorithm,log_blocksize),Err(_)=>true},
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
            layout_admission(data_size as nat,algorithm,log_blocksize) ==>
                level_count(data_blocks as nat,arity as nat,8)<=1,
            forall|i:int| #![trigger counts@[i]] 0<=i<levels ==> counts@[i] as nat
                ==level_count(data_blocks as nat,arity as nat,(i+1) as nat)
                && 0<counts@[i]<=data_blocks,
            data_blocks<=1 ==> levels==0,
            levels>0 ==> counts@[levels as int-1]==blocks,
            levels as nat+reference_height(blocks as nat,arity as nat,(8-levels) as nat)
                ==reference_height(data_blocks as nat,arity as nat,8),
            forall|i:int| #![trigger counts@[i]] 0<=i<levels as int-1 ==> counts@[i]>1,
        decreases 9-levels,
    {
        let ghost previous_blocks=blocks;
        let ghost previous_levels=levels;
        let ghost previous_counts=counts@;
        if levels==8 {return Err(Error::TooDeep);}
        proof {
            rounded_count_bounds(blocks as nat,arity as nat);
            reference_height_step(blocks as nat,arity as nat,(8-levels) as nat);
        }
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
        reference_height_small(blocks as nat,arity as nat,(8-levels) as nat);
        assert(levels as nat==reference_height(data_blocks as nat,arity as nat,8));
        assert((data_blocks<=1)==(levels==0));
        assert(levels>0 ==> counts@[levels as int-1]==1);
        count_sum_reference(counts@,data_blocks as nat,arity as nat,levels as nat);
        count_sum_upper_bound(counts@,levels as nat,18014398509481984);
        assert(count_sum(counts@,levels as nat)<=144115188075855872) by(nonlinear_arith)
            requires count_sum(counts@,levels as nat)<=levels as nat*18014398509481984,
                levels<=8;
        assert(layout_admission(data_size as nat,algorithm,log_blocksize) ==>
            count_sum(counts@,levels as nat)*block as nat<=u64::MAX);
    }
    let mut starts=[0u64;8];let mut total=0u64;let mut level=levels;
    while level>0
        invariant level<=levels<=8,total as nat==count_sum(counts@,levels as nat)-count_sum(counts@,level as nat),
            count_sum(counts@,levels as nat)<=144115188075855872,
            count_sum(counts@,levels as nat)==reference_tree_blocks(data_blocks as nat,arity as nat,levels as nat),
            layout_admission(data_size as nat,algorithm,log_blocksize) ==>
                count_sum(counts@,levels as nat)*block as nat<=u64::MAX,
            levels as nat==reference_height(data_blocks as nat,arity as nat,8),
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
        proof {
            count_sum_monotone(counts@,(level+1) as nat,levels as nat);
            assert(count_sum(counts@,(level+1) as nat)
                ==count_sum(counts@,level as nat)+counts@[level as int] as nat);
            assert(total as nat+counts@[level as int] as nat<=count_sum(counts@,levels as nat));
            assert(total as nat+counts@[level as int] as nat<=u64::MAX);
        }
        total=match total.checked_add(counts[level]){Some(v)=>v,None=>return Err(Error::Overflow)};
    }
    proof {
        if layout_admission(data_size as nat,algorithm,log_blocksize) {
            assert(total as nat*block as nat<=u64::MAX);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_div(
                total as int*block as int,block as int,total as int,0);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(
                total as int*block as int,u64::MAX as int,block as int);
            assert(total<=u64::MAX/block as u64);
        }
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
    let ghost result=Layout {block_bytes:block,digest_bytes:digest,data_blocks,levels:levels as u8,level_start:starts,level_blocks:counts,tree_blocks:total};
    proof {
        link_layout(result,data_size,algorithm,log_blocksize);
        layout_reference_admission(result,data_size,algorithm,log_blocksize);
    }
    Ok(Layout {block_bytes:block,digest_bytes:digest,data_blocks,levels:levels as u8,level_start:starts,level_blocks:counts,tree_blocks:total})
}

pub struct Descriptor<'a> {
    raw:&'a[u8],algorithm:u8,log_blocksize:u8,salt_size:u8,data_size:u64,signature_size:usize,
}
pub fn parse<'a>(raw:&'a[u8],inode_size:u64,filesystem_block_bits:u8,memory_block_bits:u8) -> (r:Result<Descriptor<'a>,Error>)
    ensures r.is_ok() <==> descriptor_admission(raw@,inode_size,filesystem_block_bits,memory_block_bits),
        match r {Ok(d)=>d.descriptor_valid() && d.descriptor_raw()==raw@ && d.descriptor_fields().2==inode_size
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
        ensures r.is_ok(),
            match r {Ok(v)=>v.len()==digest_bytes(self.descriptor_fields().0)
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
    ensures r.is_ok() <==> ((algorithm==1 && raw.len()<=2305843009213693951nat)
            || (algorithm==2 && raw.len()<=u64::MAX)),
        match r {Ok(v)=>v.len()==digest_bytes(algorithm)
        && v@==hash_reference(algorithm,raw@),Err(_)=>true},
{
    let result=if algorithm==1 {crypto_sha2::sha256(raw)}
        else if algorithm==2 {crypto_sha2::sha512(raw)}else{return Err(Error::Algorithm)};
    match result {Ok(v)=>Ok(v),Err(_)=>Err(Error::HashFailure)}
}
/// Salt is zero-padded to the hash compression-block size before each hash.
pub fn hash_block(algorithm:u8,salt:&[u8],block:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures r.is_ok() <==> ((algorithm==1 || algorithm==2)
            && salt.len()<=32 && block_size::accepted(block.len() as nat)),
        match r {Ok(v)=>v.len()==digest_bytes(algorithm)
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
        proof {assert(h.input256().len()<=64 && block.len()<=65536);}
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
        proof {assert(h.input512().len()<=128 && block.len()<=65536);}
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
    ensures r.is_ok() <==> ((algorithm==1 || algorithm==2)
            && root_hash.len()==digest_bytes(algorithm) && salt.len()<=32
            && signature.len()<=MAX_DESCRIPTOR_BYTES-256
            && layout_admission(data_size as nat,algorithm,log_blocksize)),
        match r {Ok(v)=>v@==descriptor_wire(algorithm,log_blocksize,data_size,root_hash@,salt@,signature@)
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
    ensures r.is_ok() <==> (number as nat*size as nat<=u64::MAX
            && number as nat*size as nat<=usize::MAX
            && number as nat*size as nat+size as nat<=tree.len()),
        match r {Ok(v)=>v.len()==size
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
    ensures r.is_ok() <==> (number as nat*size as nat<=u64::MAX
            && number as nat*size as nat<=usize::MAX
            && number as nat*(size as nat)<data.len()),
        match r {Ok(v)=>v.len()==size
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


// Exact builder references. Recursive content functions stay opaque; the
// implementation uses one-step observations rather than unfolding SHA rounds.
pub closed spec fn build_profile(algorithm:u8,bits:u8,salt:Seq<u8>) -> bool {
    (algorithm==1 || algorithm==2) && 10<=bits<=16 && salt.len()<=32
}
pub closed spec fn reference_block_bytes(bits:u8) -> u32 {
    if 10<=bits<=16 {1u32<<bits}else{0u32}
}
pub closed spec fn reference_arity(algorithm:u8,bits:u8) -> nat {
    if algorithm==1 || algorithm==2 {
        reference_block_bytes(bits) as nat/digest_bytes(algorithm)
    }else{0}
}
#[verifier::opaque]
pub closed spec fn reference_height(blocks:nat,arity:nat,fuel:nat) -> nat
    decreases fuel
{
    if blocks<=1 || fuel==0 || arity==0 {0}
    else {1+reference_height(ceil_arity(blocks,arity),arity,(fuel-1) as nat)}
}
#[verifier::opaque]
pub closed spec fn reference_tree_blocks(blocks:nat,arity:nat,levels:nat) -> nat
    decreases levels
{
    if levels==0 {0}else{reference_tree_blocks(blocks,arity,(levels-1) as nat)
        +level_count(blocks,arity,levels)}
}
// Admission depends only on file length, geometry and numeric budgets, not on
// an execution result or the content recurrence being proved.
pub closed spec fn reference_tree_bytes(size:nat,algorithm:u8,bits:u8) -> nat {
    let block=reference_block_bytes(bits) as nat;
    let arity=reference_arity(algorithm,bits);
    let blocks=ceil_arity(size,block);
    reference_tree_blocks(blocks,arity,reference_height(blocks,arity,8))*block
}
pub closed spec fn layout_admission(size:nat,algorithm:u8,bits:u8) -> bool {
    &&& size<=u64::MAX && (algorithm==1 || algorithm==2) && 10<=bits<=16
    &&& level_count(ceil_arity(size,reference_block_bytes(bits) as nat),
        reference_arity(algorithm,bits),8)<=1
    &&& reference_tree_bytes(size,algorithm,bits)<=u64::MAX
}
#[verifier::opaque]
pub closed spec fn build_admission(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,budget:BuildBudget) -> bool {
    &&& build_profile(algorithm,bits,salt) && layout_admission(data.len(),algorithm,bits)
    &&& reference_tree_bytes(data.len(),algorithm,bits)<=usize::MAX
    &&& reference_tree_bytes(data.len(),algorithm,bits)<=budget.tree_bytes
    &&& ceil_arity(data.len(),reference_block_bytes(bits) as nat)<=budget.data_blocks
}
pub closed spec fn descriptor_admission(raw:Seq<u8>,size:u64,filesystem_bits:u8,memory_bits:u8) -> bool {
    &&& 256<=raw.len()<=MAX_DESCRIPTOR_BYTES
    &&& raw[0]==1 && (raw[1]==1 || raw[1]==2)
    &&& 10<=raw[2]<=16 && raw[2]<=filesystem_bits && raw[2]<=memory_bits
    &&& raw[3]<=32 && le64_prefix(raw,8,8)==size
    &&& bytes::le32(raw,4)<=raw.len()-256
    &&& (forall|j:int| #![trigger raw[j]] 112<=j<256 ==> raw[j]==0)
    &&& layout_admission(size as nat,raw[1],raw[2])
}

pub closed spec fn reference_data_blocks(data:Seq<u8>,bits:u8) -> nat {
    ceil_arity(data.len(),reference_block_bytes(bits) as nat)
}
pub closed spec fn reference_levels(data:Seq<u8>,algorithm:u8,bits:u8) -> nat {
    reference_height(reference_data_blocks(data,bits),reference_arity(algorithm,bits),8)
}
pub closed spec fn reference_level_start(blocks:nat,arity:nat,levels:nat,level:nat) -> nat {
    if level>=levels {0}else{(reference_tree_blocks(blocks,arity,levels)
        -reference_tree_blocks(blocks,arity,level+1)) as nat}
}
#[verifier::opaque]
pub closed spec fn canonical_level(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,level:nat) -> Seq<u8>
    decreases level
{
    if !build_profile(algorithm,bits,salt) {Seq::empty()}
    else {
        let block=reference_block_bytes(bits) as nat;
        let digest=digest_bytes(algorithm);
        let arity=reference_arity(algorithm,bits);
        let blocks=reference_data_blocks(data,bits);
        let children=level_count(blocks,arity,level);
        let parents=level_count(blocks,arity,level+1);
        Seq::new(parents*block,|j:int| {
            let child=(j / (digest as int)) as nat;
            if child>=children {0u8}else{
                let message=if level==0 {data_block_reference(data,child,block)}
                    else {canonical_level(data,algorithm,bits,salt,(level-1) as nat)
                        .subrange((child*block) as int,((child+1)*block) as int)};
                salted_hash_reference(algorithm,salt,message)[j % (digest as int)]
            }
        })
    }
}
#[verifier::opaque]
pub closed spec fn canonical_wire(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,levels:nat) -> Seq<u8>
    decreases levels
{
    if levels==0 {Seq::empty()}else{
        canonical_level(data,algorithm,bits,salt,(levels-1) as nat)
            +canonical_wire(data,algorithm,bits,salt,(levels-1) as nat)
    }
}
#[verifier::opaque]
pub closed spec fn canonical_tree(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>) -> Seq<u8> {
    canonical_wire(data,algorithm,bits,salt,reference_levels(data,algorithm,bits))
}
#[verifier::opaque]
pub closed spec fn canonical_root(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>) -> Seq<u8> {
    let block=reference_block_bytes(bits) as nat;
    let blocks=reference_data_blocks(data,bits);
    if blocks==0 {Seq::new(digest_bytes(algorithm),|i:int| 0u8)}
    else if blocks==1 {salted_hash_reference(algorithm,salt,data_block_reference(data,0,block))}
    else {
        salted_hash_reference(algorithm,salt,
            canonical_level(data,algorithm,bits,salt,(reference_levels(data,algorithm,bits)-1) as nat)
                .take(block as int))
    }
}
#[verifier::opaque]
pub closed spec fn canonical_descriptor(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>) -> Seq<u8> {
    descriptor_wire(algorithm,bits,data.len() as u64,canonical_root(data,algorithm,bits,salt),salt,Seq::empty())
}
proof fn canonical_tree_unfold(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>)
    ensures canonical_tree(data,algorithm,bits,salt)==canonical_wire(data,algorithm,bits,salt,reference_levels(data,algorithm,bits)),
{reveal_with_fuel(canonical_tree,1);}
proof fn canonical_root_unfold(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>)
    ensures canonical_root(data,algorithm,bits,salt)
        ==if reference_data_blocks(data,bits)==0 {Seq::new(digest_bytes(algorithm),|i:int| 0u8)}
        else if reference_data_blocks(data,bits)==1 {salted_hash_reference(algorithm,salt,
            data_block_reference(data,0,reference_block_bytes(bits) as nat))}
        else {salted_hash_reference(algorithm,salt,canonical_level(data,algorithm,bits,salt,
            (reference_levels(data,algorithm,bits)-1) as nat).take(reference_block_bytes(bits) as int))},
{reveal_with_fuel(canonical_root,1);}
proof fn canonical_descriptor_unfold(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>)
    ensures canonical_descriptor(data,algorithm,bits,salt)==descriptor_wire(algorithm,bits,data.len() as u64,
        canonical_root(data,algorithm,bits,salt),salt,Seq::empty()),
{reveal_with_fuel(canonical_descriptor,1);}

#[verifier::opaque]
pub closed spec fn layout_reference(l:Layout,size:u64,algorithm:u8,bits:u8) -> bool {
    &&& l.layout_valid() && (algorithm==1 || algorithm==2) && 10<=bits<=16
    &&& l.block_bytes==reference_block_bytes(bits) && l.digest_bytes==digest_bytes(algorithm)
    &&& l.data_blocks==ceil_arity(size as nat,l.block_bytes as nat)
    &&& l.levels==reference_height(l.data_blocks as nat,(l.block_bytes/l.digest_bytes) as nat,8)
    &&& l.tree_blocks==reference_tree_blocks(l.data_blocks as nat,(l.block_bytes/l.digest_bytes) as nat,l.levels as nat)
    &&& forall|k:int| #![trigger l.level_start@[k]] 0<=k<l.levels ==>
        l.level_start@[k] as nat==reference_level_start(l.data_blocks as nat,
            (l.block_bytes/l.digest_bytes) as nat,l.levels as nat,k as nat)
}
#[verifier::opaque]
pub closed spec fn construction_frontier(tree:Seq<u8>,data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,
    l:Layout,level:nat,cut:nat) -> bool
{
    &&& layout_reference(l,data.len() as u64,algorithm,bits) && build_profile(algorithm,bits,salt)
    &&& data.len()<=u64::MAX
    &&& tree.len()==l.tree_blocks as nat*l.block_bytes as nat
    &&& level<=l.levels
    &&& (if level<l.levels {cut<=l.level_blocks@[level as int] as nat*l.block_bytes as nat}else{cut==0})
    &&& forall|k:int,j:int| 0<=k<l.levels && 0<=j<l.level_blocks@[k] as nat*l.block_bytes as nat ==>
        #[trigger] tree[l.level_start@[k] as nat*l.block_bytes as nat+j]
            ==if k<level || k==level && j<cut {canonical_level(data,algorithm,bits,salt,k as nat)[j]}else{0u8}
}
#[verifier::ext_equal]
pub struct BuiltView {pub tree:Seq<u8>,pub descriptor:Seq<u8>,pub digest:Seq<u8>}
pub closed spec fn build_content(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,budget:BuildBudget,v:BuiltView) -> bool {
    &&& build_profile(algorithm,bits,salt) && data.len()<=u64::MAX
    &&& v.tree==canonical_tree(data,algorithm,bits,salt)
    &&& v.descriptor==canonical_descriptor(data,algorithm,bits,salt)
    &&& v.digest==hash_reference(algorithm,measured_header(v.descriptor))
    &&& v.descriptor.len()==256 && v.digest.len()==digest_bytes(algorithm)
    &&& v.tree.len()<=budget.tree_bytes && reference_data_blocks(data,bits)<=budget.data_blocks
}
proof fn reference_height_small(blocks:nat,arity:nat,fuel:nat)
    requires blocks<=1,
    ensures reference_height(blocks,arity,fuel)==0,
{reveal_with_fuel(reference_height,1);}
proof fn reference_height_step(blocks:nat,arity:nat,fuel:nat)
    requires blocks>1,arity>0,fuel>0,
    ensures reference_height(blocks,arity,fuel)==1+reference_height(ceil_arity(blocks,arity),arity,(fuel-1) as nat),
{reveal_with_fuel(reference_height,1);}
proof fn reference_sum_zero(blocks:nat,arity:nat)
    ensures reference_tree_blocks(blocks,arity,0)==0,
{reveal_with_fuel(reference_tree_blocks,1);}
proof fn reference_sum_step(blocks:nat,arity:nat,levels:nat)
    ensures reference_tree_blocks(blocks,arity,levels+1)
        ==reference_tree_blocks(blocks,arity,levels)+level_count(blocks,arity,levels+1),
{reveal_with_fuel(reference_tree_blocks,1);}
proof fn count_sum_reference(counts:Seq<u64>,blocks:nat,arity:nat,depth:nat)
    requires depth<=counts.len(),forall|k:int| #![trigger counts[k]] 0<=k<depth ==>
        counts[k] as nat==level_count(blocks,arity,(k+1) as nat),
    ensures count_sum(counts,depth)==reference_tree_blocks(blocks,arity,depth),
    decreases depth,
{
    if depth==0 {reference_sum_zero(blocks,arity);}
    else {
        count_sum_reference(counts,blocks,arity,(depth-1) as nat);
        reference_sum_step(blocks,arity,(depth-1) as nat);
        assert(counts[depth as int-1] as nat==level_count(blocks,arity,depth));
    }
}
proof fn link_layout(l:Layout,size:u64,algorithm:u8,bits:u8)
    requires l.layout_valid(),(algorithm==1 || algorithm==2),10<=bits<=16,
        l.block_bytes==reference_block_bytes(bits),l.digest_bytes==digest_bytes(algorithm),
        l.data_blocks==ceil_arity(size as nat,l.block_bytes as nat),
        l.levels==reference_height(l.data_blocks as nat,(l.block_bytes/l.digest_bytes) as nat,8),
    ensures layout_reference(l,size,algorithm,bits),
{
    reveal(layout_reference);
    count_sum_reference(l.level_blocks@,l.data_blocks as nat,(l.block_bytes/l.digest_bytes) as nat,l.levels as nat);
    assert forall|k:int| #![trigger l.level_start@[k]] 0<=k<l.levels implies
        l.level_start@[k] as nat==reference_level_start(l.data_blocks as nat,
            (l.block_bytes/l.digest_bytes) as nat,l.levels as nat,k as nat) by {
        count_sum_reference(l.level_blocks@,l.data_blocks as nat,(l.block_bytes/l.digest_bytes) as nat,(k+1) as nat);
        count_sum_monotone(l.level_blocks@,(k+1) as nat,l.levels as nat);
    }
}
proof fn layout_reference_admission(l:Layout,size:u64,algorithm:u8,bits:u8)
    requires layout_reference(l,size,algorithm,bits),
    ensures layout_admission(size as nat,algorithm,bits),
        reference_tree_bytes(size as nat,algorithm,bits)
            ==l.tree_blocks as nat*l.block_bytes as nat,
{
    reveal(layout_reference);
    count_sum_reference(l.level_blocks@,l.data_blocks as nat,
        (l.block_bytes/l.digest_bytes) as nat,l.levels as nat);
    if l.levels==0 {assert(l.data_blocks<=1);}
    else {assert(level_count(l.data_blocks as nat,(l.block_bytes/l.digest_bytes) as nat,l.levels as nat)==1);}
    level_count_monotone(l.data_blocks as nat,(l.block_bytes/l.digest_bytes) as nat,l.levels as nat,8);
}
proof fn builder_admission_inputs(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,budget:BuildBudget)
    ensures build_admission(data,algorithm,bits,salt,budget) ==>
        salt.len()<=32 && layout_admission(data.len(),algorithm,bits),
{
    reveal(build_admission);
}
proof fn builder_from_layout(l:Layout,data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,budget:BuildBudget)
    requires layout_reference(l,data.len() as u64,algorithm,bits),data.len()<=u64::MAX,
        salt.len()<=32,l.tree_blocks as nat*l.block_bytes as nat<=usize::MAX,
        l.tree_blocks as nat*l.block_bytes as nat<=budget.tree_bytes,
        l.data_blocks<=budget.data_blocks,
    ensures build_admission(data,algorithm,bits,salt,budget),
{
    reveal(build_admission);
    layout_reference_admission(l,data.len() as u64,algorithm,bits);
    reveal(layout_reference);
}
proof fn builder_budget_is_exact(l:Layout,data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,budget:BuildBudget)
    requires layout_reference(l,data.len() as u64,algorithm,bits),data.len()<=u64::MAX,
        build_admission(data,algorithm,bits,salt,budget),
    ensures l.tree_blocks as nat*l.block_bytes as nat<=budget.tree_bytes,
        l.tree_blocks as nat*l.block_bytes as nat<=usize::MAX,l.data_blocks<=budget.data_blocks,
{
    reveal(build_admission);
    layout_reference_admission(l,data.len() as u64,algorithm,bits);
    reveal(layout_reference);
}
proof fn child_data_offset(data:Seq<u8>,number:u64,size:u32)
    requires size>0,number<ceil_arity(data.len(),size as nat),data.len()<=u64::MAX,
        data.len()<=usize::MAX,
    ensures number as nat*(size as nat)<data.len(),number as nat*size as nat<=u64::MAX,
        number as nat*size as nat<=usize::MAX,
{
    parent_slot_bound(data.len(),size as nat,number as nat,0);
}
proof fn child_tree_offset(l:Layout,tree:Seq<u8>,level:nat,child:u64)
    requires l.layout_valid(),tree.len()==l.tree_blocks as nat*l.block_bytes as nat,
        tree.len()<=usize::MAX,level<l.levels,child<l.level_blocks@[level as int],
    ensures (l.level_start@[level as int] as nat+child as nat)*l.block_bytes as nat+l.block_bytes as nat
        <=tree.len(),
        (l.level_start@[level as int] as nat+child as nat)*l.block_bytes as nat<=u64::MAX,
{
    assert(l.level_start@[level as int] as nat+l.level_blocks@[level as int] as nat<=l.tree_blocks);
    assert(l.level_start@[level as int] as nat+child as nat+1<=l.tree_blocks);
    vstd::arithmetic::mul::lemma_mul_inequality(
        l.level_start@[level as int] as int+child as int+1,l.tree_blocks as int,l.block_bytes as int);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
        l.block_bytes as int,l.level_start@[level as int] as int+child as int,1);
}

proof fn layout_source_data_count(l:Layout,data:Seq<u8>,algorithm:u8,bits:u8)
    requires layout_reference(l,data.len() as u64,algorithm,bits),data.len()<=u64::MAX,
    ensures reference_data_blocks(data,bits)==l.data_blocks,
        l.data_blocks==ceil_arity(data.len(),l.block_bytes as nat),
{
    reveal(layout_reference);
}

proof fn canonical_level_shape(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,level:nat)
    requires build_profile(algorithm,bits,salt),
    ensures canonical_level(data,algorithm,bits,salt,level).len()
        ==level_count(reference_data_blocks(data,bits),reference_arity(algorithm,bits),level+1)
            *reference_block_bytes(bits) as nat,
{
    broadcast use vstd::seq::group_seq_lemmas;
    reveal_with_fuel(canonical_level,1);
}
proof fn canonical_level_byte(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,level:nat,j:int)
    requires build_profile(algorithm,bits,salt),0<=j<canonical_level(data,algorithm,bits,salt,level).len(),
    ensures canonical_level(data,algorithm,bits,salt,level)[j]
        ==if (j / (digest_bytes(algorithm) as int)) as nat>=level_count(reference_data_blocks(data,bits),reference_arity(algorithm,bits),level) {0u8}
        else {salted_hash_reference(algorithm,salt,
            if level==0 {data_block_reference(data,(j / (digest_bytes(algorithm) as int)) as nat,reference_block_bytes(bits) as nat)}
            else {canonical_level(data,algorithm,bits,salt,(level-1) as nat).subrange(
                (((j / (digest_bytes(algorithm) as int)) as nat)*reference_block_bytes(bits) as nat) as int,
                ((((j / (digest_bytes(algorithm) as int)) as nat)+1)*reference_block_bytes(bits) as nat) as int)})
                    [j % (digest_bytes(algorithm) as int)]},
{
    broadcast use vstd::seq::group_seq_lemmas;
    let block=reference_block_bytes(bits) as nat;
    let digest=digest_bytes(algorithm);
    let child=(j / (digest as int)) as nat;
    let children=level_count(reference_data_blocks(data,bits),reference_arity(algorithm,bits),level);
    if child<children {
        if level>0 {
            canonical_level_shape(data,algorithm,bits,salt,(level-1) as nat);
            assert(canonical_level(data,algorithm,bits,salt,(level-1) as nat).len()==children*block);
            assert((child+1)*block<=canonical_level(data,algorithm,bits,salt,(level-1) as nat).len()) by(nonlinear_arith)
                requires child<children,block>=0,
                    canonical_level(data,algorithm,bits,salt,(level-1) as nat).len()==children*block;
        }
        let message=if level==0 {data_block_reference(data,child,block)}
            else {canonical_level(data,algorithm,bits,salt,(level-1) as nat)
                .subrange((child*block) as int,((child+1)*block) as int)};
        salted_reference_length(algorithm,salt,message);
    }
    reveal_with_fuel(canonical_level,1);
}
proof fn canonical_wire_zero(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>)
    ensures canonical_wire(data,algorithm,bits,salt,0)==Seq::<u8>::empty(),
{reveal_with_fuel(canonical_wire,1);}
proof fn canonical_wire_step(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,levels:nat)
    ensures canonical_wire(data,algorithm,bits,salt,levels+1)
        ==canonical_level(data,algorithm,bits,salt,levels)+canonical_wire(data,algorithm,bits,salt,levels),
{reveal_with_fuel(canonical_wire,1);}
proof fn canonical_wire_shape(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,levels:nat)
    requires build_profile(algorithm,bits,salt),
    ensures canonical_wire(data,algorithm,bits,salt,levels).len()
        ==reference_tree_blocks(reference_data_blocks(data,bits),reference_arity(algorithm,bits),levels)
            *reference_block_bytes(bits) as nat,
    decreases levels,
{
    broadcast use vstd::seq::group_seq_lemmas;
    if levels==0 {
        canonical_wire_zero(data,algorithm,bits,salt);
        reference_sum_zero(reference_data_blocks(data,bits),reference_arity(algorithm,bits));
        assert(0nat*reference_block_bytes(bits) as nat==0) by(nonlinear_arith);
    }
    else {
        canonical_wire_shape(data,algorithm,bits,salt,(levels-1) as nat);
        canonical_level_shape(data,algorithm,bits,salt,(levels-1) as nat);
        canonical_wire_step(data,algorithm,bits,salt,(levels-1) as nat);
        reference_sum_step(reference_data_blocks(data,bits),reference_arity(algorithm,bits),(levels-1) as nat);
        assert(canonical_wire(data,algorithm,bits,salt,levels).len()
            ==reference_tree_blocks(reference_data_blocks(data,bits),reference_arity(algorithm,bits),levels)*reference_block_bytes(bits) as nat) by(nonlinear_arith)
            requires canonical_wire(data,algorithm,bits,salt,levels).len()
                ==canonical_level(data,algorithm,bits,salt,(levels-1) as nat).len()
                    +canonical_wire(data,algorithm,bits,salt,(levels-1) as nat).len(),
                reference_tree_blocks(reference_data_blocks(data,bits),reference_arity(algorithm,bits),levels)
                    ==reference_tree_blocks(reference_data_blocks(data,bits),reference_arity(algorithm,bits),(levels-1) as nat)
                        +level_count(reference_data_blocks(data,bits),reference_arity(algorithm,bits),levels),
                canonical_level(data,algorithm,bits,salt,(levels-1) as nat).len()
                    ==level_count(reference_data_blocks(data,bits),reference_arity(algorithm,bits),levels)*reference_block_bytes(bits) as nat,
                canonical_wire(data,algorithm,bits,salt,(levels-1) as nat).len()
                    ==reference_tree_blocks(reference_data_blocks(data,bits),reference_arity(algorithm,bits),(levels-1) as nat)*reference_block_bytes(bits) as nat;
    }
}


proof fn salted_reference_length(algorithm:u8,salt:Seq<u8>,message:Seq<u8>)
    requires algorithm==1 || algorithm==2,
    ensures salted_hash_reference(algorithm,salt,message).len()==digest_bytes(algorithm),
{
    if algorithm==1 {crypto_sha2::digest256_reference_length(salt_prefix(algorithm,salt)+message);}
    else {crypto_sha2::digest512_reference_length(salt_prefix(algorithm,salt)+message);}
}
proof fn level_adjacent(l:Layout,k:nat)
    requires l.layout_valid(),k+1<l.levels,
    ensures l.level_start@[k as int] as nat==l.level_start@[(k+1) as int] as nat
        +l.level_blocks@[(k+1) as int] as nat,
{
    count_sum_monotone(l.level_blocks@,k+1,l.levels as nat);
    count_sum_monotone(l.level_blocks@,k+2,l.levels as nat);
    assert(count_sum(l.level_blocks@,k+2)==count_sum(l.level_blocks@,k+1)+l.level_blocks@[(k+1) as int] as nat);
}
proof fn level_separated(l:Layout,low:nat,high:nat)
    requires l.layout_valid(),low<high<l.levels,
    ensures l.level_start@[high as int] as nat+l.level_blocks@[high as int] as nat
        <=l.level_start@[low as int] as nat,
{
    count_sum_monotone(l.level_blocks@,low+1,high);
    count_sum_monotone(l.level_blocks@,low+1,l.levels as nat);
    count_sum_monotone(l.level_blocks@,high+1,l.levels as nat);
    assert(count_sum(l.level_blocks@,high+1)==count_sum(l.level_blocks@,high)+l.level_blocks@[high as int] as nat);
}
proof fn level_byte_bound(l:Layout,k:nat,j:int)
    requires l.layout_valid(),k<l.levels,0<=j<l.level_blocks@[k as int] as nat*l.block_bytes as nat,
    ensures 0<=l.level_start@[k as int] as nat*l.block_bytes as nat+j
        <l.tree_blocks as nat*l.block_bytes as nat,
{
    assert(l.level_start@[k as int] as nat+l.level_blocks@[k as int] as nat<=l.tree_blocks);
    assert(l.level_start@[k as int] as nat*l.block_bytes as nat+j<l.tree_blocks as nat*l.block_bytes as nat)
        by(nonlinear_arith)
        requires 0<=j<l.level_blocks@[k as int] as nat*l.block_bytes as nat,
            l.level_start@[k as int] as nat+l.level_blocks@[k as int] as nat<=l.tree_blocks,
            l.block_bytes>0;
}
proof fn other_level_outside_write(l:Layout,level:nat,other:nat,cut:nat,amount:nat,j:int)
    requires l.layout_valid(),level<l.levels,other<l.levels,other!=level,
        cut+amount<=l.level_blocks@[level as int] as nat*l.block_bytes as nat,
        0<=j<l.level_blocks@[other as int] as nat*l.block_bytes as nat,
    ensures l.level_start@[other as int] as nat*l.block_bytes as nat+j
            <l.level_start@[level as int] as nat*l.block_bytes as nat+cut
        ||l.level_start@[other as int] as nat*l.block_bytes as nat+j
            >=l.level_start@[level as int] as nat*l.block_bytes as nat+cut+amount,
{
    if other<level {
        level_separated(l,other,level);
        assert(l.level_start@[other as int] as nat*l.block_bytes as nat+j
            >=l.level_start@[level as int] as nat*l.block_bytes as nat+cut+amount) by(nonlinear_arith)
            requires l.level_start@[level as int] as nat+l.level_blocks@[level as int] as nat
                <=l.level_start@[other as int] as nat,
                cut+amount<=l.level_blocks@[level as int] as nat*l.block_bytes as nat,j>=0;
    } else {
        level_separated(l,level,other);
        assert(l.level_start@[other as int] as nat*l.block_bytes as nat+j
            <l.level_start@[level as int] as nat*l.block_bytes as nat+cut) by(nonlinear_arith)
            requires l.level_start@[other as int] as nat+l.level_blocks@[other as int] as nat
                <=l.level_start@[level as int] as nat,
                j<l.level_blocks@[other as int] as nat*l.block_bytes as nat,cut>=0;
    }
}
proof fn zero_frontier(tree:Seq<u8>,data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,l:Layout)
    requires layout_reference(l,data.len() as u64,algorithm,bits),build_profile(algorithm,bits,salt),
        data.len()<=u64::MAX,tree.len()==l.tree_blocks as nat*l.block_bytes as nat,
        forall|i:int| #![trigger tree[i]] 0<=i<tree.len() ==> tree[i]==0,
    ensures construction_frontier(tree,data,algorithm,bits,salt,l,0,0),
{
    reveal(layout_reference);
    reveal(construction_frontier);
    assert forall|k:int,j:int| 0<=k<l.levels && 0<=j<l.level_blocks@[k] as nat*l.block_bytes as nat
        implies #[trigger] tree[l.level_start@[k] as nat*l.block_bytes as nat+j]==0u8 by {
        level_byte_bound(l,k as nat,j);
    }
}
proof fn frontier_splice_advance(before:Seq<u8>,after:Seq<u8>,data:Seq<u8>,algorithm:u8,bits:u8,
    salt:Seq<u8>,l:Layout,level:nat,cut:nat,payload:Seq<u8>)
    requires l.layout_valid(),construction_frontier(before,data,algorithm,bits,salt,l,level,cut),level<l.levels,
        cut+payload.len()<=l.level_blocks@[level as int] as nat*l.block_bytes as nat,
        payload==canonical_level(data,algorithm,bits,salt,level).subrange(cut as int,(cut+payload.len()) as int),
        after.len()==before.len(),
        forall|i:int| #![trigger after[i]] 0<=i<after.len() ==> after[i]==
            if l.level_start@[level as int] as nat*l.block_bytes as nat+cut<=i
                <l.level_start@[level as int] as nat*l.block_bytes as nat+cut+payload.len()
            {payload[i-(l.level_start@[level as int] as nat*l.block_bytes as nat+cut) as int]}else{before[i]},
    ensures construction_frontier(after,data,algorithm,bits,salt,l,level,cut+payload.len()),
{
    reveal(layout_reference);
    reveal(construction_frontier);
    canonical_level_shape(data,algorithm,bits,salt,level);
    assert forall|k:int,j:int| 0<=k<l.levels && 0<=j<l.level_blocks@[k] as nat*l.block_bytes as nat
        implies #[trigger] after[l.level_start@[k] as nat*l.block_bytes as nat+j]
            ==if k<level ||k==level && j<cut+payload.len()
                {canonical_level(data,algorithm,bits,salt,k as nat)[j]}else{0u8} by {
        level_byte_bound(l,k as nat,j);
        if k==level {
            if j<cut {
                assert(after[l.level_start@[k] as nat*l.block_bytes as nat+j]
                    ==before[l.level_start@[k] as nat*l.block_bytes as nat+j]);
            }else if j<cut+payload.len() {
                vstd::seq::lemma_seq_subrange_index(canonical_level(data,algorithm,bits,salt,level),
                    cut as int,(cut+payload.len()) as int,j-cut as int);
                assert(payload[j-cut as int]==canonical_level(data,algorithm,bits,salt,level)[j]);
            }else{
                assert(after[l.level_start@[k] as nat*l.block_bytes as nat+j]
                    ==before[l.level_start@[k] as nat*l.block_bytes as nat+j]);
            }
        }else{
            other_level_outside_write(l,level,k as nat,cut,payload.len(),j);
            assert(after[l.level_start@[k] as nat*l.block_bytes as nat+j]
                ==before[l.level_start@[k] as nat*l.block_bytes as nat+j]);
        }
    }
}
proof fn frontier_zero_extension(tree:Seq<u8>,data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,
    l:Layout,level:nat,cut:nat,end:nat)
    requires l.layout_valid(),construction_frontier(tree,data,algorithm,bits,salt,l,level,cut),level<l.levels,
        cut<=end<=l.level_blocks@[level as int] as nat*l.block_bytes as nat,
        forall|j:int| #![trigger canonical_level(data,algorithm,bits,salt,level)[j]]
            cut<=j<end ==> canonical_level(data,algorithm,bits,salt,level)[j]==0,
    ensures construction_frontier(tree,data,algorithm,bits,salt,l,level,end),
{
    reveal(construction_frontier);
    assert forall|k:int,j:int| 0<=k<l.levels && 0<=j<l.level_blocks@[k] as nat*l.block_bytes as nat
        implies #[trigger] tree[l.level_start@[k] as nat*l.block_bytes as nat+j]
            ==if k<level ||k==level && j<end {canonical_level(data,algorithm,bits,salt,k as nat)[j]}else{0u8} by {
        if k==level && cut<=j<end {assert(canonical_level(data,algorithm,bits,salt,level)[j]==0);}
    }
}
proof fn frontier_finish_level(tree:Seq<u8>,data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,l:Layout,level:nat)
    requires l.layout_valid(),level<l.levels,construction_frontier(tree,data,algorithm,bits,salt,l,level,
        l.level_blocks@[level as int] as nat*l.block_bytes as nat),
    ensures construction_frontier(tree,data,algorithm,bits,salt,l,level+1,0),
{
    reveal(construction_frontier);
    assert forall|k:int,j:int| 0<=k<l.levels && 0<=j<l.level_blocks@[k] as nat*l.block_bytes as nat
        implies #[trigger] tree[l.level_start@[k] as nat*l.block_bytes as nat+j]
            ==if k<level+1 {canonical_level(data,algorithm,bits,salt,k as nat)[j]}else{0u8} by {
        if k==level {assert(j<l.level_blocks@[level as int] as nat*l.block_bytes as nat);}
    }
}
proof fn scaled_child_span(child:nat,block:nat)
    ensures 0<=child*block<=(child+1)*block,child*block+block==(child+1)*block,
{
    assert(0<=child*block<=(child+1)*block && child*block+block==(child+1)*block) by(nonlinear_arith)
        requires child>=0,block>=0;
}

proof fn frontier_completed_block(tree:Seq<u8>,data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,
    l:Layout,frontier_level:nat,cut:nat,level:nat,child:u64)
    requires l.layout_valid(),level<l.levels,
        construction_frontier(tree,data,algorithm,bits,salt,l,frontier_level,cut),
        level<frontier_level,child<l.level_blocks@[level as int],
    ensures canonical_level(data,algorithm,bits,salt,level).len()
            ==l.level_blocks@[level as int] as nat*l.block_bytes as nat,
        (child as nat+1)*l.block_bytes as nat<=canonical_level(data,algorithm,bits,salt,level).len(),
        tree_block_reference(tree,l.level_start@[level as int] as nat+child as nat,l.block_bytes as nat)
        ==canonical_level(data,algorithm,bits,salt,level).subrange(
            (child as nat*l.block_bytes as nat) as int,((child as nat+1)*l.block_bytes as nat) as int),
{
    reveal(layout_reference);
    broadcast use vstd::seq::group_seq_lemmas;
    reveal(construction_frontier);
    canonical_level_shape(data,algorithm,bits,salt,level);
    let first=(l.level_start@[level as int] as nat+child as nat)*l.block_bytes as nat;
    let local=child as nat*l.block_bytes as nat;
    assert(first+l.block_bytes as nat<=tree.len()) by(nonlinear_arith)
        requires first==(l.level_start@[level as int] as nat+child as nat)*l.block_bytes as nat,
            l.level_start@[level as int] as nat+l.level_blocks@[level as int] as nat<=l.tree_blocks,
            child<l.level_blocks@[level as int],tree.len()==l.tree_blocks as nat*l.block_bytes as nat;
    assert(local+l.block_bytes as nat<=canonical_level(data,algorithm,bits,salt,level).len()) by(nonlinear_arith)
        requires local==child as nat*l.block_bytes as nat,child<l.level_blocks@[level as int],
            canonical_level(data,algorithm,bits,salt,level).len()==l.level_blocks@[level as int] as nat*l.block_bytes as nat;
    assert forall|i:int| 0<=i<l.block_bytes implies
        #[trigger] tree.subrange(first as int,(first+l.block_bytes as nat) as int)[i]
        ==#[trigger] canonical_level(data,algorithm,bits,salt,level)
            .subrange(local as int,(local+l.block_bytes as nat) as int)[i] by {
        vstd::seq::lemma_seq_subrange_index(tree,first as int,(first+l.block_bytes as nat) as int,i);
        vstd::seq::lemma_seq_subrange_index(canonical_level(data,algorithm,bits,salt,level),
            local as int,(local+l.block_bytes as nat) as int,i);
        let byte=local as int+i;
        assert(0<=byte<l.level_blocks@[level as int] as nat*l.block_bytes as nat) by(nonlinear_arith)
            requires byte==local as int+i,local==child as nat*l.block_bytes as nat,
                0<=i<l.block_bytes,child<l.level_blocks@[level as int],l.block_bytes>0;
        assert(first+i==l.level_start@[level as int] as nat*l.block_bytes as nat+byte) by(nonlinear_arith)
            requires first==(l.level_start@[level as int] as nat+child as nat)*l.block_bytes as nat,
                local==child as nat*l.block_bytes as nat,byte==local as int+i;
        assert(tree[l.level_start@[level as int] as nat*l.block_bytes as nat+byte]
            ==canonical_level(data,algorithm,bits,salt,level)[byte]);
        assert(tree[first+i]==canonical_level(data,algorithm,bits,salt,level)[local as int+i]);
    }
    assert(tree.subrange(first as int,(first+l.block_bytes as nat) as int)
        =~=canonical_level(data,algorithm,bits,salt,level).subrange(local as int,(local+l.block_bytes as nat) as int));
}
proof fn canonical_child_span(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,l:Layout,level:nat,child:u64)
    requires data.len()<=u64::MAX,l.layout_valid(),layout_reference(l,data.len() as u64,algorithm,bits),
        build_profile(algorithm,bits,salt),level<l.levels,
        child<if level==0 {l.data_blocks}else{l.level_blocks@[level as int-1]},
    ensures level>0 ==> 0<=child as nat*l.block_bytes as nat
        <=(child as nat+1)*l.block_bytes as nat
        <=canonical_level(data,algorithm,bits,salt,(level-1) as nat).len(),
{
    reveal(layout_reference);
    if level>0 {
        canonical_level_shape(data,algorithm,bits,salt,(level-1) as nat);
        scaled_child_span(child as nat,l.block_bytes as nat);
        assert(canonical_level(data,algorithm,bits,salt,(level-1) as nat).len()
            ==l.level_blocks@[level as int-1] as nat*l.block_bytes as nat);
        assert((child as nat+1)*l.block_bytes as nat
            <=canonical_level(data,algorithm,bits,salt,(level-1) as nat).len()) by(nonlinear_arith)
            requires child<l.level_blocks@[level as int-1],l.block_bytes>0,
                canonical_level(data,algorithm,bits,salt,(level-1) as nat).len()
                    ==l.level_blocks@[level as int-1] as nat*l.block_bytes as nat;
    }
}

proof fn canonical_digest_chunk(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,l:Layout,
    level:nat,child:u64,digest:Seq<u8>)
    requires data.len()<=u64::MAX,l.layout_valid(),layout_reference(l,data.len() as u64,algorithm,bits),
        build_profile(algorithm,bits,salt),level<l.levels,
        child<if level==0 {l.data_blocks}else{l.level_blocks@[level as int-1]},
        level>0 ==> 0<=child as nat*l.block_bytes as nat
            <=(child as nat+1)*l.block_bytes as nat
            <=canonical_level(data,algorithm,bits,salt,(level-1) as nat).len(),
        digest.len()==l.digest_bytes,
        digest==salted_hash_reference(algorithm,salt,if level==0
            {data_block_reference(data,child as nat,l.block_bytes as nat)}
            else{canonical_level(data,algorithm,bits,salt,(level-1) as nat).subrange(
                (child as nat*l.block_bytes as nat) as int,((child as nat+1)*l.block_bytes as nat) as int)}),
    ensures canonical_level(data,algorithm,bits,salt,level).len()
            ==l.level_blocks@[level as int] as nat*l.block_bytes as nat,
        child as nat*l.digest_bytes as nat+digest.len()
            <=l.level_blocks@[level as int] as nat*l.block_bytes as nat,
        canonical_level(data,algorithm,bits,salt,level)
        .subrange((child as nat*l.digest_bytes as nat) as int,((child as nat+1)*l.digest_bytes as nat) as int)==digest,
        canonical_level(data,algorithm,bits,salt,level)
            .subrange((child as nat*l.digest_bytes as nat) as int,
                (child as nat*l.digest_bytes as nat+digest.len()) as int)==digest,
{
    reveal(layout_reference);
    broadcast use vstd::seq::group_seq_lemmas;
    canonical_level_shape(data,algorithm,bits,salt,level);
    geometry(l.block_bytes,l.digest_bytes);
    let arity=(l.block_bytes/l.digest_bytes) as u64;
    let children=if level==0 {l.data_blocks}else{l.level_blocks@[level as int-1]};
    assert(l.level_blocks@[level as int] as nat
        ==level_count(l.data_blocks as nat,arity as nat,level+1));
    if level>0 {assert(l.level_blocks@[level as int-1] as nat
        ==level_count(l.data_blocks as nat,arity as nat,level));}
    assert(l.level_blocks@[level as int] as nat==ceil_arity(children as nat,arity as nat));
    index_parent_bound(child as nat,children as nat,arity as nat);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(child as int,arity as int);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(child as int,arity as int);
    destination_bound(0,l.level_blocks@[level as int] as nat,(child/arity) as nat,
        child%arity,arity,l.digest_bytes,l.block_bytes,l.level_blocks@[level as int] as nat);
    let first=child as nat*l.digest_bytes as nat;
    assert(first+l.digest_bytes as nat<=canonical_level(data,algorithm,bits,salt,level).len()) by(nonlinear_arith)
        requires first==child as nat*l.digest_bytes as nat,
            child as int==(child/arity) as int*arity as int+(child%arity) as int,
            l.block_bytes as nat==arity as nat*l.digest_bytes as nat,
            (child/arity) as nat*l.block_bytes as nat+(child%arity) as nat*l.digest_bytes as nat+l.digest_bytes as nat
                <=l.level_blocks@[level as int] as nat*l.block_bytes as nat,
            canonical_level(data,algorithm,bits,salt,level).len()==l.level_blocks@[level as int] as nat*l.block_bytes as nat;
    assert forall|i:int| 0<=i<digest.len() implies
        #[trigger] canonical_level(data,algorithm,bits,salt,level)
            .subrange(first as int,(first+digest.len()) as int)[i]==#[trigger] digest[i] by {
        let j=first as int+i;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j,l.digest_bytes as int);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(j,l.digest_bytes as int);
        assert(j / (l.digest_bytes as int)==(child as int) && j % (l.digest_bytes as int)==i) by(nonlinear_arith)
            requires j==child as nat*l.digest_bytes as nat+i,0<=i<l.digest_bytes,l.digest_bytes>0,
                j==(j / (l.digest_bytes as int))*l.digest_bytes as int+j % (l.digest_bytes as int),
                0 <= j % (l.digest_bytes as int) < (l.digest_bytes as int);
        canonical_level_byte(data,algorithm,bits,salt,level,j);
        vstd::seq::lemma_seq_subrange_index(canonical_level(data,algorithm,bits,salt,level),
            first as int,(first+digest.len()) as int,i);
    }
    assert(canonical_level(data,algorithm,bits,salt,level).subrange(first as int,(first+digest.len()) as int)=~=digest);
    scaled_child_span(child as nat,l.digest_bytes as nat);
    assert(first+digest.len()==(child as nat+1)*l.digest_bytes as nat);
    assert(canonical_level(data,algorithm,bits,salt,level)
        .subrange(first as int,((child as nat+1)*l.digest_bytes as nat) as int)==digest);
}
proof fn canonical_padding_is_zero(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,l:Layout,
    level:nat,first:nat,end:nat)
    requires l.layout_valid(),layout_reference(l,data.len() as u64,algorithm,bits),build_profile(algorithm,bits,salt),
        data.len()<=u64::MAX,level<l.levels,first<=end<=l.level_blocks@[level as int] as nat*l.block_bytes as nat,
        first>=(if level==0 {l.data_blocks as nat}else{l.level_blocks@[level as int-1] as nat})*l.digest_bytes as nat,
    ensures forall|j:int| #![trigger canonical_level(data,algorithm,bits,salt,level)[j]]
        first<=j<end ==> canonical_level(data,algorithm,bits,salt,level)[j]==0,
{
    reveal(layout_reference);
    canonical_level_shape(data,algorithm,bits,salt,level);
    let children=if level==0 {l.data_blocks as nat}else{l.level_blocks@[level as int-1] as nat};
    assert forall|j:int| first<=j<end implies #[trigger] canonical_level(data,algorithm,bits,salt,level)[j]==0 by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j,l.digest_bytes as int);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(j,l.digest_bytes as int);
        assert(j / (l.digest_bytes as int)>=(children as int)) by(nonlinear_arith)
            requires j>=first,first>=children*l.digest_bytes as nat,l.digest_bytes>0,
                j==(j / (l.digest_bytes as int))*l.digest_bytes as int+j % (l.digest_bytes as int),
                0 <= j % (l.digest_bytes as int) < (l.digest_bytes as int);
        canonical_level_byte(data,algorithm,bits,salt,level,j);
    }
}


proof fn concat_prefix_bytes(head:Seq<u8>,tail:Seq<u8>)
    ensures (head+tail).subrange(0,head.len() as int)==head,
{
    let joined=head+tail;
    vstd::seq::lemma_seq_add_len(head,tail);
    vstd::seq::lemma_seq_subrange_len(joined,0,head.len() as int);
    assert forall|i:int| 0<=i<head.len() implies #[trigger] joined.subrange(0,head.len() as int)[i]==#[trigger] head[i] by {
        vstd::seq::lemma_seq_subrange_index(joined,0,head.len() as int,i);
        vstd::seq::lemma_seq_add_index1(head,tail,i);
    }
    assert(joined.subrange(0,head.len() as int)=~=head);
}
proof fn concat_shifted_bytes(head:Seq<u8>,tail:Seq<u8>,lo:int,hi:int)
    requires 0<=lo<=hi<=tail.len(),
    ensures (head+tail).subrange(head.len() as int+lo,head.len() as int+hi)==tail.subrange(lo,hi),
{
    let joined=head+tail;let first=head.len() as int+lo;let end=head.len() as int+hi;
    vstd::seq::lemma_seq_add_len(head,tail);
    vstd::seq::lemma_seq_subrange_len(joined,first,end);
    vstd::seq::lemma_seq_subrange_len(tail,lo,hi);
    assert forall|i:int| 0<=i<hi-lo implies #[trigger] joined.subrange(first,end)[i]==#[trigger] tail.subrange(lo,hi)[i] by {
        vstd::seq::lemma_seq_subrange_index(joined,first,end,i);
        vstd::seq::lemma_seq_add_index2(head,tail,first+i);
        vstd::seq::lemma_seq_subrange_index(tail,lo,hi,i);
    }
    assert(joined.subrange(first,end)=~=tail.subrange(lo,hi));
}
proof fn reference_sum_monotone(blocks:nat,arity:nat,first:nat,end:nat)
    requires first<=end,
    ensures reference_tree_blocks(blocks,arity,first)<=reference_tree_blocks(blocks,arity,end),
    decreases end,
{
    if first<end {
        reference_sum_monotone(blocks,arity,first,(end-1) as nat);
        reference_sum_step(blocks,arity,(end-1) as nat);
    }
}
proof fn canonical_wire_level_projection(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,levels:nat,level:nat)
    requires build_profile(algorithm,bits,salt),level<levels,
    ensures canonical_wire(data,algorithm,bits,salt,levels).subrange(
        (reference_level_start(reference_data_blocks(data,bits),reference_arity(algorithm,bits),levels,level)
            *reference_block_bytes(bits) as nat) as int,
        ((reference_level_start(reference_data_blocks(data,bits),reference_arity(algorithm,bits),levels,level)
            +level_count(reference_data_blocks(data,bits),reference_arity(algorithm,bits),level+1))
            *reference_block_bytes(bits) as nat) as int)==canonical_level(data,algorithm,bits,salt,level),
    decreases levels,
{
    let blocks=reference_data_blocks(data,bits);let arity=reference_arity(algorithm,bits);
    let block=reference_block_bytes(bits) as nat;let previous=(levels-1) as nat;
    let head=canonical_level(data,algorithm,bits,salt,previous);
    let tail=canonical_wire(data,algorithm,bits,salt,previous);
    canonical_wire_step(data,algorithm,bits,salt,previous);
    canonical_level_shape(data,algorithm,bits,salt,previous);
    canonical_wire_shape(data,algorithm,bits,salt,previous);
    canonical_wire_shape(data,algorithm,bits,salt,levels);
    reference_sum_step(blocks,arity,previous);reference_sum_step(blocks,arity,level);
    reference_sum_monotone(blocks,arity,level+1,levels);
    let total=reference_tree_blocks(blocks,arity,levels);
    let previous_total=reference_tree_blocks(blocks,arity,previous);
    let prefix=reference_tree_blocks(blocks,arity,level+1);
    let prefix_before=reference_tree_blocks(blocks,arity,level);
    let count=level_count(blocks,arity,level+1);let top_count=level_count(blocks,arity,levels);
    let start=reference_level_start(blocks,arity,levels,level);
    assert(prefix<=total && start+prefix==total);
    assert(prefix==prefix_before+count && total==previous_total+top_count);
    assert(head.len()==top_count*block && tail.len()==previous_total*block);
    if level==previous {
        assert(start==0);
        assert(start*block==0 && (start+count)*block==head.len()) by(nonlinear_arith)
            requires start==0,head.len()==count*block;
        concat_prefix_bytes(head,tail);
    }else{
        canonical_wire_level_projection(data,algorithm,bits,salt,previous,level);
        reference_sum_monotone(blocks,arity,level+1,previous);
        let old_start=reference_level_start(blocks,arity,previous,level);
        assert(prefix<=previous_total && old_start+prefix==previous_total);
        let lo=old_start*block;let hi=(old_start+count)*block;
        assert(lo<=hi && hi<=tail.len()) by(nonlinear_arith)
            requires lo==old_start*block,hi==(old_start+count)*block,tail.len()==previous_total*block,
                old_start+prefix==previous_total,prefix==prefix_before+count;
        assert(start*block==head.len()+lo && (start+count)*block==head.len()+hi) by(nonlinear_arith)
            requires start+prefix==total,old_start+prefix==previous_total,total==previous_total+top_count,
                head.len()==top_count*block,lo==old_start*block,hi==(old_start+count)*block;
        concat_shifted_bytes(head,tail,lo as int,hi as int);
    }
}
proof fn linked_canonical_level_projection(data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,l:Layout,level:nat)
    requires l.layout_valid(),layout_reference(l,data.len() as u64,algorithm,bits),
        build_profile(algorithm,bits,salt),data.len()<=u64::MAX,level<l.levels,
    ensures canonical_level(data,algorithm,bits,salt,level).len()
            ==l.level_blocks@[level as int] as nat*l.block_bytes as nat,
        canonical_tree(data,algorithm,bits,salt).len()==l.tree_blocks as nat*l.block_bytes as nat,
        canonical_tree(data,algorithm,bits,salt).subrange(
            (l.level_start@[level as int] as nat*l.block_bytes as nat) as int,
            ((l.level_start@[level as int] as nat+l.level_blocks@[level as int] as nat)*l.block_bytes as nat) as int)
            ==canonical_level(data,algorithm,bits,salt,level),
{
    reveal(layout_reference);
    assert(reference_data_blocks(data,bits)==l.data_blocks);
    assert(reference_arity(algorithm,bits)==(l.block_bytes/l.digest_bytes) as nat);
    assert(reference_levels(data,algorithm,bits)==l.levels);
    canonical_tree_unfold(data,algorithm,bits,salt);
    canonical_level_shape(data,algorithm,bits,salt,level);
    canonical_wire_shape(data,algorithm,bits,salt,l.levels as nat);
    canonical_wire_level_projection(data,algorithm,bits,salt,l.levels as nat,level);
    assert(reference_level_start(reference_data_blocks(data,bits),reference_arity(algorithm,bits),l.levels as nat,level)
        ==l.level_start@[level as int]);
    assert(level_count(reference_data_blocks(data,bits),reference_arity(algorithm,bits),level+1)
        ==l.level_blocks@[level as int]);
}

proof fn prefix_weight_cover(counts:Seq<u64>,depth:nat,block:nat,x:nat) -> (k:nat)
    requires block>0,0<depth<=counts.len(),forall|i:int| #![trigger counts[i]] 0<=i<depth ==> counts[i]>0,
        x<count_sum(counts,depth)*block,
    ensures k<depth,count_sum(counts,k)*block<=x,x<count_sum(counts,k+1)*block,
    decreases depth,
{
    let previous=(depth-1) as nat;let boundary=count_sum(counts,previous)*block;
    if x<boundary {
        assert(previous>0) by {
            if previous==0 {
                assert(count_sum(counts,previous)==0);
                assert(boundary==0) by(nonlinear_arith)
                    requires boundary==count_sum(counts,previous)*block,count_sum(counts,previous)==0;
            }
        }
        prefix_weight_cover(counts,previous,block,x)
    }else{previous}
}
proof fn frontier_completed_tree(tree:Seq<u8>,data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,l:Layout)
    requires construction_frontier(tree,data,algorithm,bits,salt,l,l.levels as nat,0),
    ensures tree==canonical_tree(data,algorithm,bits,salt),
{
    reveal(layout_reference);
    broadcast use vstd::seq::group_seq_lemmas;
    reveal(construction_frontier);
    canonical_tree_unfold(data,algorithm,bits,salt);
    canonical_wire_shape(data,algorithm,bits,salt,l.levels as nat);
    assert(reference_levels(data,algorithm,bits)==l.levels);
    assert(tree.len()==canonical_tree(data,algorithm,bits,salt).len());
    assert forall|pos:int| 0<=pos<tree.len() implies #[trigger] tree[pos]==#[trigger] canonical_tree(data,algorithm,bits,salt)[pos] by {
        assert(l.levels>0) by {
            if l.levels==0 {
                assert(count_sum(l.level_blocks@,0)==0 && l.tree_blocks==0);
                assert(tree.len()==0) by(nonlinear_arith)
                    requires tree.len()==l.tree_blocks as nat*l.block_bytes as nat,l.tree_blocks==0;
            }
        }
        let reversed=(tree.len() as int-1-pos) as nat;
        let k=prefix_weight_cover(l.level_blocks@,l.levels as nat,l.block_bytes as nat,reversed);
        let first=l.level_start@[k as int] as nat*l.block_bytes as nat;
        let count=l.level_blocks@[k as int] as nat*l.block_bytes as nat;
        assert(first<=pos<first+count) by(nonlinear_arith)
            requires first==l.level_start@[k as int] as nat*l.block_bytes as nat,
                count==l.level_blocks@[k as int] as nat*l.block_bytes as nat,
                tree.len()==l.tree_blocks as nat*l.block_bytes as nat,
                reversed==tree.len() as int-1-pos,
                l.level_start@[k as int] as nat==count_sum(l.level_blocks@,l.levels as nat)-count_sum(l.level_blocks@,k+1),
                l.tree_blocks==count_sum(l.level_blocks@,l.levels as nat),
                count_sum(l.level_blocks@,k)*l.block_bytes as nat<=reversed
                    <count_sum(l.level_blocks@,k+1)*l.block_bytes as nat,
                count_sum(l.level_blocks@,k+1)==count_sum(l.level_blocks@,k)+l.level_blocks@[k as int] as nat;
        linked_canonical_level_projection(data,algorithm,bits,salt,l,k);
        assert(first+count<=tree.len()) by(nonlinear_arith)
            requires first==l.level_start@[k as int] as nat*l.block_bytes as nat,
                count==l.level_blocks@[k as int] as nat*l.block_bytes as nat,
                l.level_start@[k as int] as nat+l.level_blocks@[k as int] as nat<=l.tree_blocks,
                tree.len()==l.tree_blocks as nat*l.block_bytes as nat;
        assert(first+count==(l.level_start@[k as int] as nat+l.level_blocks@[k as int] as nat)*l.block_bytes as nat) by(nonlinear_arith)
            requires first==l.level_start@[k as int] as nat*l.block_bytes as nat,
                count==l.level_blocks@[k as int] as nat*l.block_bytes as nat;
        assert(canonical_tree(data,algorithm,bits,salt).subrange(first as int,(first+count) as int)
            ==canonical_level(data,algorithm,bits,salt,k));
        let byte=pos-first as int;
        assert(0<=byte<count);
        vstd::seq::lemma_seq_subrange_index(canonical_tree(data,algorithm,bits,salt),
            first as int,(first+count) as int,byte);
        assert(tree[l.level_start@[k as int] as nat*l.block_bytes as nat+byte]
            ==canonical_level(data,algorithm,bits,salt,k)[byte]);
        assert(pos==l.level_start@[k as int] as nat*l.block_bytes as nat+byte);
        assert(tree[pos]==canonical_level(data,algorithm,bits,salt,k)[byte]);
    }
    assert(tree=~=canonical_tree(data,algorithm,bits,salt));
}


proof fn built_root_is_reference(tree:Seq<u8>,data:Seq<u8>,algorithm:u8,bits:u8,salt:Seq<u8>,l:Layout,root:Seq<u8>)
    requires construction_frontier(tree,data,algorithm,bits,salt,l,l.levels as nat,0),
        root==if l.data_blocks==0 {Seq::new(l.digest_bytes as nat,|i:int| 0u8)}
            else if l.levels==0 {salted_hash_reference(algorithm,salt,data_block_reference(data,0,l.block_bytes as nat))}
            else {salted_hash_reference(algorithm,salt,tree_block_reference(tree,0,l.block_bytes as nat))},
    ensures root==canonical_root(data,algorithm,bits,salt),
{
    reveal(layout_reference);
    reveal(construction_frontier);
    canonical_root_unfold(data,algorithm,bits,salt);
    assert(reference_data_blocks(data,bits)==l.data_blocks);
    assert(reference_levels(data,algorithm,bits)==l.levels);
    if l.data_blocks==0 { }
    else if l.levels==0 {assert(l.data_blocks==1);}
    else {
        let top=(l.levels-1) as nat;
        assert(l.level_start@[top as int]==0);
        assert(l.level_blocks@[top as int]==1);
        frontier_completed_block(tree,data,algorithm,bits,salt,l,l.levels as nat,0,top,0);
        assert(0nat*l.block_bytes as nat==0 && (0nat+1)*l.block_bytes as nat==l.block_bytes) by(nonlinear_arith);
        assert(canonical_level(data,algorithm,bits,salt,top).take(l.block_bytes as int)
            ==canonical_level(data,algorithm,bits,salt,top).subrange(0,l.block_bytes as int));
        assert(tree_block_reference(tree,0,l.block_bytes as nat)
            ==canonical_level(data,algorithm,bits,salt,top).take(l.block_bytes as int));
    }
}


proof fn zero_bytes_empty()
    ensures Seq::<u8>::empty()==Seq::new(0,|i:int| 0u8),
{
    broadcast use vstd::seq::group_seq_lemmas;
    assert(Seq::<u8>::empty()=~=Seq::new(0,|i:int| 0u8));
}
proof fn zero_bytes_push(before:Seq<u8>,count:nat)
    requires before==Seq::new(count,|i:int| 0u8),
    ensures before.push(0u8)==Seq::new(count+1,|i:int| 0u8),
{
    broadcast use vstd::seq::group_seq_lemmas;
    assert(before.push(0u8)=~=Seq::new(count+1,|i:int| 0u8));
}
proof fn encoded64_decodes(value:u64)
    ensures le64_prefix(encoded64(value),0,8)==value,
{
    reveal_with_fuel(le64_prefix,9);
    let word=encoded64(value);
    let b0=word[0];
    let b1=word[1];
    let b2=word[2];
    let b3=word[3];
    let b4=word[4];
    let b5=word[5];
    let b6=word[6];
    let b7=word[7];
    assert(b0==(value>>0) as u8);
    assert(b1==(value>>8) as u8);
    assert(b2==(value>>16) as u8);
    assert(b3==(value>>24) as u8);
    assert(b4==(value>>32) as u8);
    assert(b5==(value>>40) as u8);
    assert(b6==(value>>48) as u8);
    assert(b7==(value>>56) as u8);
    let joined=(0u64 | ((b0 as u64)<<0))
        |((b1 as u64)<<8)
        |((b2 as u64)<<16)
        |((b3 as u64)<<24)
        |((b4 as u64)<<32)
        |((b5 as u64)<<40)
        |((b6 as u64)<<48)
        |((b7 as u64)<<56);
    assert(le64_prefix(word,0,8)==joined);
    assert(joined==value) by(bit_vector)
        requires b0==(value>>0) as u8,b1==(value>>8) as u8,b2==(value>>16) as u8,b3==(value>>24) as u8,b4==(value>>32) as u8,b5==(value>>40) as u8,b6==(value>>48) as u8,b7==(value>>56) as u8,
            joined==(0u64 | ((b0 as u64)<<0))
        |((b1 as u64)<<8)
        |((b2 as u64)<<16)
        |((b3 as u64)<<24)
        |((b4 as u64)<<32)
        |((b5 as u64)<<40)
        |((b6 as u64)<<48)
        |((b7 as u64)<<56);
}
proof fn le64_projection_byte(raw:Seq<u8>,offset:int,word:Seq<u8>,index:int)
    requires 0<=offset,offset+8<=raw.len(),word.len()==8,0<=index<8,
        forall|j:int| #![trigger raw[offset+j]] 0<=j<8 ==> raw[offset+j]==word[j],
    ensures raw[offset+index]==word[index],
{
}
proof fn le64_prefix_projection(raw:Seq<u8>,offset:int,word:Seq<u8>,count:nat)
    requires 0<=offset,offset+8<=raw.len(),word.len()==8,count<=8,
        forall|j:int| #![trigger raw[offset+j]] 0<=j<8 ==> raw[offset+j]==word[j],
    ensures le64_prefix(raw,offset,count)==le64_prefix(word,0,count),
    decreases count,
{
    if count>0 {
        le64_prefix_projection(raw,offset,word,(count-1) as nat);
        le64_projection_byte(raw,offset,word,count as int-1);
        assert(raw[offset+count as int-1]==word[count as int-1]);
    }
}
proof fn descriptor_wire_admitted(algorithm:u8,bits:u8,size:u64,root:Seq<u8>,salt:Seq<u8>,signature:Seq<u8>)
    requires layout_admission(size as nat,algorithm,bits),
        root.len()==digest_bytes(algorithm),salt.len()<=32,
        signature.len()<=MAX_DESCRIPTOR_BYTES-256,
    ensures descriptor_admission(descriptor_wire(algorithm,bits,size,root,salt,signature),size,bits,bits),
{
    broadcast use vstd::seq::group_seq_lemmas;
    let raw=descriptor_wire(algorithm,bits,size,root,salt,signature);
    assert(raw.len()==256+signature.len());
    assert forall|j:int| 0<=j<8 implies #[trigger] raw[8+j]==encoded64(size)[j] by {}
    encoded64_decodes(size);
    le64_prefix_projection(raw,8,encoded64(size),8);
    bytes::little_endian_encoding_recovers_every_word(signature.len() as u32);
    assert(bytes::le32(raw,4)==bytes::le32(bytes::encoded_le(signature.len() as u32),0));
    assert(signature.len() as u32==signature.len());
    assert forall|j:int| 112<=j<256 implies #[trigger] raw[j]==0 by {}
}

proof fn descriptor_wire_algorithm(algorithm:u8,bits:u8,size:u64,root:Seq<u8>,salt:Seq<u8>,signature:Seq<u8>)
    ensures descriptor_wire(algorithm,bits,size,root,salt,signature)[1]==algorithm,
        descriptor_wire(algorithm,bits,size,root,salt,signature).len()==256+signature.len(),
{
    broadcast use vstd::seq::group_seq_lemmas;
}

#[derive(Clone, Copy)]
pub struct BuildBudget {pub tree_bytes:usize,pub data_blocks:u64}
pub struct BuiltTree {tree:Vec<u8>,descriptor:Vec<u8>,digest:Vec<u8>}
impl BuiltTree {
    pub closed spec fn built_view(&self) -> BuiltView {BuiltView {tree:self.tree@,descriptor:self.descriptor@,digest:self.digest@}}
    pub fn tree(&self) -> (r:&[u8]) ensures r@==self.built_view().tree {self.tree.as_slice()}
    pub fn descriptor(&self) -> (r:&[u8]) ensures r@==self.built_view().descriptor {self.descriptor.as_slice()}
    pub fn built_digest(&self) -> (r:&[u8]) ensures r@==self.built_view().digest {self.digest.as_slice()}
}
pub fn build(data:&[u8],algorithm:u8,log_blocksize:u8,salt:&[u8],budget:BuildBudget) -> (r:Result<BuiltTree,Error>)
    ensures r.is_ok() <==> build_admission(data@,algorithm,log_blocksize,salt@,budget),
        match r {Ok(v)=>build_content(data@,algorithm,log_blocksize,salt@,budget,v.built_view()),Err(_)=>true},
{
    proof {
        assert(data.len()<=u64::MAX);
        builder_admission_inputs(data@,algorithm,log_blocksize,salt@,budget);
    }
    if salt.len()>32 {return Err(Error::Salt);}
    let l=layout(data.len() as u64,algorithm,log_blocksize)?;let tree_size=l.tree_bytes()?;
    proof {
        layout_reference_admission(l,data.len() as u64,algorithm,log_blocksize);
        if build_admission(data@,algorithm,log_blocksize,salt@,budget) {
            builder_budget_is_exact(l,data@,algorithm,log_blocksize,salt@,budget);
        }
    }
    if tree_size>budget.tree_bytes as u64 || tree_size>usize::MAX as u64 || l.data_blocks>budget.data_blocks {return Err(Error::ResourceLimit);}
    proof {
        assert(data.len()<=u64::MAX);assert(build_profile(algorithm,log_blocksize,salt@));
        builder_from_layout(l,data@,algorithm,log_blocksize,salt@,budget);
        layout_source_data_count(l,data@,algorithm,log_blocksize);
    }
    let mut tree=Vec::new();let mut i=0usize;
    while i<tree_size as usize
        invariant i<=tree_size as usize,tree.len()==i,tree_size<=usize::MAX,
            layout_reference(l,data.len() as u64,algorithm,log_blocksize),
            build_admission(data@,algorithm,log_blocksize,salt@,budget),
            build_profile(algorithm,log_blocksize,salt@),data.len()<=u64::MAX,
            l.data_blocks==ceil_arity(data.len() as nat,l.block_bytes as nat),
            tree_size as nat==l.tree_blocks as nat*l.block_bytes as nat,
            tree_size<=budget.tree_bytes,l.data_blocks<=budget.data_blocks,
            forall|j:int| #![trigger tree@[j]] 0<=j<i ==> tree@[j]==0,
        decreases tree_size as usize-i,
    {tree.push(0);i+=1;}
    proof {zero_frontier(tree@,data@,algorithm,log_blocksize,salt@,l);}
    let arity=(l.block_bytes/l.digest_bytes) as u64;
    proof {geometry(l.block_bytes,l.digest_bytes);}
    let mut level=0usize;
    while level<l.levels as usize
        invariant level<=l.levels as usize<=8,l.layout_valid(),
            layout_reference(l,data.len() as u64,algorithm,log_blocksize),
            build_admission(data@,algorithm,log_blocksize,salt@,budget),
            build_profile(algorithm,log_blocksize,salt@),data.len()<=u64::MAX,
            l.data_blocks==ceil_arity(data.len() as nat,l.block_bytes as nat),
            construction_frontier(tree@,data@,algorithm,log_blocksize,salt@,l,level as nat,0),
            tree_size<=budget.tree_bytes,l.data_blocks<=budget.data_blocks,
            tree.len()==tree_size as usize,tree_size<=usize::MAX as u64,
            tree_size as nat==l.tree_blocks as nat*l.block_bytes as nat,
            16<=arity<=2048,l.block_bytes as nat==arity as nat*l.digest_bytes as nat,
            arity==(l.block_bytes/l.digest_bytes) as u64,l.digest_bytes==digest_bytes(algorithm),
        decreases l.levels as usize-level,
    {
        let children=if level==0 {l.data_blocks}else{l.level_blocks[level-1]};
        proof {l.level_children(level as nat);}
        let mut parent=0u64;
        while parent<l.level_blocks[level]
            invariant parent<=l.level_blocks@[level as int],level<l.levels as usize<=8,l.layout_valid(),
                layout_reference(l,data.len() as u64,algorithm,log_blocksize),
                build_admission(data@,algorithm,log_blocksize,salt@,budget),
                build_profile(algorithm,log_blocksize,salt@),data.len()<=u64::MAX,
                l.data_blocks==ceil_arity(data.len() as nat,l.block_bytes as nat),
                construction_frontier(tree@,data@,algorithm,log_blocksize,salt@,l,level as nat,
                    parent as nat*l.block_bytes as nat),
                tree_size<=budget.tree_bytes,l.data_blocks<=budget.data_blocks,
                tree.len()==tree_size as usize,tree_size<=usize::MAX as u64,
                tree_size as nat==l.tree_blocks as nat*l.block_bytes as nat,children<=18014398509481984,
                children==if level==0 {l.data_blocks}else{l.level_blocks@[level as int-1]},
                l.level_blocks@[level as int]==ceil_arity(children as nat,arity as nat),
                16<=arity<=2048,l.block_bytes as nat==arity as nat*l.digest_bytes as nat,
                arity==(l.block_bytes/l.digest_bytes) as u64,l.digest_bytes==digest_bytes(algorithm),
            decreases l.level_blocks@[level as int]-parent,
        {
            let mut slot=0u64;
            while slot<arity
                invariant slot<=arity,parent<l.level_blocks@[level as int],level<l.levels as usize<=8,l.layout_valid(),
                    slot==arity ==> construction_frontier(tree@,data@,algorithm,log_blocksize,salt@,l,level as nat,
                        (parent as nat+1)*l.block_bytes as nat),
                    layout_reference(l,data.len() as u64,algorithm,log_blocksize),
                    build_admission(data@,algorithm,log_blocksize,salt@,budget),
                    build_profile(algorithm,log_blocksize,salt@),data.len()<=u64::MAX,
                    l.data_blocks==ceil_arity(data.len() as nat,l.block_bytes as nat),
                    construction_frontier(tree@,data@,algorithm,log_blocksize,salt@,l,level as nat,
                        parent as nat*l.block_bytes as nat+slot as nat*l.digest_bytes as nat),
                    tree_size<=budget.tree_bytes,l.data_blocks<=budget.data_blocks,
                    tree.len()==tree_size as usize,tree_size<=usize::MAX as u64,
                    tree_size as nat==l.tree_blocks as nat*l.block_bytes as nat,children<=18014398509481984,
                    children==if level==0 {l.data_blocks}else{l.level_blocks@[level as int-1]},
                    l.level_blocks@[level as int]==ceil_arity(children as nat,arity as nat),
                    16<=arity<=2048,l.block_bytes as nat==arity as nat*l.digest_bytes as nat,
                    arity==(l.block_bytes/l.digest_bytes) as u64,l.digest_bytes==digest_bytes(algorithm),
                ensures construction_frontier(tree@,data@,algorithm,log_blocksize,salt@,l,level as nat,
                    (parent as nat+1)*l.block_bytes as nat),
                decreases arity-slot,
            {
                let ghost cut=parent as nat*l.block_bytes as nat+slot as nat*l.digest_bytes as nat;
                proof {
                    parent_slot_bound(children as nat,arity as nat,parent as nat,slot as nat);
                    assert(parent as nat*arity as nat+slot as nat<=u64::MAX);
                }
                let child=parent*arity+slot;
                if child>=children {
                    proof {
                        let end=(parent as nat+1)*l.block_bytes as nat;
                        assert(cut==child as nat*l.digest_bytes as nat) by(nonlinear_arith)
                            requires child as nat==parent as nat*arity as nat+slot as nat,
                                cut==parent as nat*l.block_bytes as nat+slot as nat*l.digest_bytes as nat,
                                l.block_bytes as nat==arity as nat*l.digest_bytes as nat;
                        assert(cut>=children as nat*l.digest_bytes as nat) by(nonlinear_arith)
                            requires cut==child as nat*l.digest_bytes as nat,child>=children;
                        assert(cut<=end && end<=l.level_blocks@[level as int] as nat*l.block_bytes as nat) by(nonlinear_arith)
                            requires cut==parent as nat*l.block_bytes as nat+slot as nat*l.digest_bytes as nat,
                                end==(parent as nat+1)*l.block_bytes as nat,
                                slot<=arity,l.block_bytes as nat==arity as nat*l.digest_bytes as nat,
                                parent<l.level_blocks@[level as int],l.block_bytes>0,l.digest_bytes>0;
                        canonical_padding_is_zero(data@,algorithm,log_blocksize,salt@,l,level as nat,cut,end);
                        frontier_zero_extension(tree@,data@,algorithm,log_blocksize,salt@,l,level as nat,cut,end);
                        assert(construction_frontier(tree@,data@,algorithm,log_blocksize,salt@,l,level as nat,
                            (parent as nat+1)*l.block_bytes as nat));
                    }
                    break;
                }
                let digest=if level==0 {
                    proof {child_data_offset(data@,child,l.block_bytes);}
                    let raw=padded_data(data,child,l.block_bytes)?;hash_block(algorithm,salt,raw.as_slice())?
                } else {
                    proof {child_tree_offset(l,tree@,(level-1) as nat,child);}
                    let number=l.level_start[level-1]+child;
                    let raw=block(tree.as_slice(),number,l.block_bytes)?;
                    proof {
                        frontier_completed_block(tree@,data@,algorithm,log_blocksize,salt@,l,
                            level as nat,cut,(level-1) as nat,child);
                        scaled_child_span(child as nat,l.block_bytes as nat);
                        assert(0<=child as nat*l.block_bytes as nat
                            <=(child as nat+1)*l.block_bytes as nat
                            <=canonical_level(data@,algorithm,log_blocksize,salt@,(level-1) as nat).len());
                        assert(raw@==canonical_level(data@,algorithm,log_blocksize,salt@,(level-1) as nat)
                            .subrange((child as nat*l.block_bytes as nat) as int,((child as nat+1)*l.block_bytes as nat) as int));
                    }
                    hash_block(algorithm,salt,raw)?
                };
                proof {
                    canonical_child_span(data@,algorithm,log_blocksize,salt@,l,level as nat,child);
                    canonical_digest_chunk(data@,algorithm,log_blocksize,salt@,l,level as nat,child,digest@);
                    assert(cut==child as nat*l.digest_bytes as nat) by(nonlinear_arith)
                        requires child as nat==parent as nat*arity as nat+slot as nat,
                            cut==parent as nat*l.block_bytes as nat+slot as nat*l.digest_bytes as nat,
                            l.block_bytes as nat==arity as nat*l.digest_bytes as nat;
                    assert(cut+digest.len()<=l.level_blocks@[level as int] as nat*l.block_bytes as nat);
                    assert(0<=cut<=cut+digest.len()
                        <=canonical_level(data@,algorithm,log_blocksize,salt@,level as nat).len());
                    assert(digest@==canonical_level(data@,algorithm,log_blocksize,salt@,level as nat)
                        .subrange(cut as int,(cut+digest.len()) as int));
                    destination_bound(l.level_start@[level as int] as nat,l.level_blocks@[level as int] as nat,
                        parent as nat,slot,arity,l.digest_bytes,l.block_bytes,l.tree_blocks as nat);
                }
                let destination=(l.level_start[level]+parent)*l.block_bytes as u64+slot*l.digest_bytes as u64;
                proof {
                    assert(destination as nat+digest.len()<=tree_size as nat);
                    assert(destination<=usize::MAX);
                }
                if destination>usize::MAX as u64 {return Err(Error::Overflow);}
                proof {
                    assert(destination as nat+digest.len()<=tree_size as nat);
                    assert(tree.len() as nat==tree_size as nat);
                    assert(destination as nat==l.level_start@[level as int] as nat*l.block_bytes as nat+cut) by(nonlinear_arith)
                        requires destination as nat==(l.level_start@[level as int] as nat+parent as nat)*l.block_bytes as nat+slot as nat*l.digest_bytes as nat,
                            cut==parent as nat*l.block_bytes as nat+slot as nat*l.digest_bytes as nat;
                }
                let at=destination as usize;i=0;
                proof {assert(at as nat+digest.len()<=tree.len());}
                let ghost before_digest=tree@;
                while i<digest.len()
                    invariant i<=digest.len(),digest.len()==l.digest_bytes,
                        at as nat+digest.len()<=tree.len(),tree.len()==before_digest.len(),
                        tree.len()==tree_size as usize,tree_size<=usize::MAX as u64,
                        slot<=arity,16<=arity<=2048,l.layout_valid(),level<l.levels as usize<=8,
                        arity==(l.block_bytes/l.digest_bytes) as u64,
                        l.block_bytes as nat==arity as nat*l.digest_bytes as nat,
                        children<=18014398509481984,
                        children==if level==0 {l.data_blocks}else{l.level_blocks@[level as int-1]},
                        l.level_blocks@[level as int]==ceil_arity(children as nat,arity as nat),
                        layout_reference(l,data.len() as u64,algorithm,log_blocksize),
                        build_admission(data@,algorithm,log_blocksize,salt@,budget),
                        build_profile(algorithm,log_blocksize,salt@),data.len()<=u64::MAX,
                        l.data_blocks==ceil_arity(data.len() as nat,l.block_bytes as nat),
                        level<l.levels,parent<l.level_blocks@[level as int],
                        tree_size as nat==l.tree_blocks as nat*l.block_bytes as nat,
                        tree_size<=budget.tree_bytes,l.data_blocks<=budget.data_blocks,
                        cut==parent as nat*l.block_bytes as nat+slot as nat*l.digest_bytes as nat,
                        cut+digest.len()<=l.level_blocks@[level as int] as nat*l.block_bytes as nat,
                        canonical_level(data@,algorithm,log_blocksize,salt@,level as nat).len()
                            ==l.level_blocks@[level as int] as nat*l.block_bytes as nat,
                        at as nat==l.level_start@[level as int] as nat*l.block_bytes as nat+cut,
                        construction_frontier(before_digest,data@,algorithm,log_blocksize,salt@,l,level as nat,cut),
                        digest@==canonical_level(data@,algorithm,log_blocksize,salt@,level as nat)
                            .subrange(cut as int,(cut+digest.len()) as int),
                        forall|j:int| #![trigger tree@[j]] 0<=j<tree.len() ==> tree@[j]==
                            if at<=j<at+i {digest@[j-at as int]}else{before_digest[j]},
                    decreases digest.len()-i,
                {tree[at+i]=digest[i];i+=1;}
                proof {
                    frontier_splice_advance(before_digest,tree@,data@,algorithm,log_blocksize,salt@,
                        l,level as nat,cut,digest@);
                }
                let ghost previous_slot=slot;
                slot+=1;
                proof {
                    assert(parent as nat*l.block_bytes as nat+slot as nat*l.digest_bytes as nat==cut+digest.len()) by(nonlinear_arith)
                        requires cut==parent as nat*l.block_bytes as nat+previous_slot as nat*l.digest_bytes as nat,
                            slot as nat==previous_slot as nat+1,digest.len()==l.digest_bytes;
                    if slot==arity {
                        assert(parent as nat*l.block_bytes as nat+slot as nat*l.digest_bytes as nat
                            ==(parent as nat+1)*l.block_bytes as nat) by(nonlinear_arith)
                            requires slot==arity,l.block_bytes as nat==arity as nat*l.digest_bytes as nat;
                        assert(construction_frontier(tree@,data@,algorithm,log_blocksize,salt@,l,level as nat,
                            (parent as nat+1)*l.block_bytes as nat));
                    }
                }
            }
            proof {
                if slot==arity {
                    assert(parent as nat*l.block_bytes as nat+slot as nat*l.digest_bytes as nat
                        ==(parent as nat+1)*l.block_bytes as nat) by(nonlinear_arith)
                        requires slot==arity,l.block_bytes as nat==arity as nat*l.digest_bytes as nat;
                }
                assert(construction_frontier(tree@,data@,algorithm,log_blocksize,salt@,l,level as nat,
                    (parent as nat+1)*l.block_bytes as nat));
            }
            parent+=1;
        }
        proof {frontier_finish_level(tree@,data@,algorithm,log_blocksize,salt@,l,level as nat);}
        level+=1;
    }
    proof {frontier_completed_tree(tree@,data@,algorithm,log_blocksize,salt@,l);}
    let mut root=Vec::new();
    if l.data_blocks==0 {
        i=0;
        proof {zero_bytes_empty();}
        while i<l.digest_bytes as usize
            invariant i<=l.digest_bytes as usize,root.len()==i,root@==Seq::new(i as nat,|j:int| 0u8),
                l.digest_bytes==32 || l.digest_bytes==64,
                layout_reference(l,data.len() as u64,algorithm,log_blocksize),
                build_admission(data@,algorithm,log_blocksize,salt@,budget),
                build_profile(algorithm,log_blocksize,salt@),data.len()<=u64::MAX,
                l.data_blocks==ceil_arity(data.len() as nat,l.block_bytes as nat),l.data_blocks==0,
                construction_frontier(tree@,data@,algorithm,log_blocksize,salt@,l,l.levels as nat,0),
                tree@==canonical_tree(data@,algorithm,log_blocksize,salt@),
                tree.len()<=budget.tree_bytes,l.data_blocks<=budget.data_blocks,
            decreases l.digest_bytes as usize-i,
        {
            let ghost previous_root=root@;
            let ghost previous_i=i;
            root.push(0);i+=1;
            proof {zero_bytes_push(previous_root,previous_i as nat);}
        }
    }
    else if l.levels==0 {
        proof {layout_source_data_count(l,data@,algorithm,log_blocksize);child_data_offset(data@,0,l.block_bytes);}
        let raw=padded_data(data,0,l.block_bytes)?;root=hash_block(algorithm,salt,raw.as_slice())?;
    }
    else {
        proof {
            assert(l.level_start@[l.levels as int-1]==0);
            child_tree_offset(l,tree@,(l.levels-1) as nat,0);
            frontier_completed_block(tree@,data@,algorithm,log_blocksize,salt@,l,l.levels as nat,0,(l.levels-1) as nat,0);
        }
        root=hash_block(algorithm,salt,block(tree.as_slice(),0,l.block_bytes)?)?;
    }
    proof {
        built_root_is_reference(tree@,data@,algorithm,log_blocksize,salt@,l,root@);
        assert(root@==canonical_root(data@,algorithm,log_blocksize,salt@));
    }
    let descriptor=encode_descriptor(algorithm,log_blocksize,data.len() as u64,root.as_slice(),salt,&[])?;
    proof {
        descriptor_wire_algorithm(algorithm,log_blocksize,data.len() as u64,root@,salt@,seq![]);
        descriptor_wire_admitted(algorithm,log_blocksize,data.len() as u64,root@,salt@,seq![]);
    }
    let parsed=parse(descriptor.as_slice(),data.len() as u64,log_blocksize,log_blocksize)?;
    proof {use_type_invariant(&parsed);assert(parsed.descriptor_fields().0==algorithm);}
    let digest=parsed.measure()?;
    proof {
        canonical_descriptor_unfold(data@,algorithm,log_blocksize,salt@);
        layout_source_data_count(l,data@,algorithm,log_blocksize);
        assert(descriptor@==canonical_descriptor(data@,algorithm,log_blocksize,salt@));
        assert(build_content(data@,algorithm,log_blocksize,salt@,budget,
            BuiltView {tree:tree@,descriptor:descriptor@,digest:digest@}));
    }
    Ok(BuiltTree {tree,descriptor,digest})
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
