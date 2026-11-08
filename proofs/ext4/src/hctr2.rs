// SPDX-License-Identifier: MPL-2.0

//! Linux-compatible AES-256-HCTR2 with its 32-byte fscrypt tweak.
//! POLYVAL evaluates the actual tweak and message bytes; XCTR encrypts actual
//! counters with the owned AES key. This is length-preserving encryption,
//! without an authentication or constant-time/physical-erasure claim.
//! Reference: Linux v7.0 hctr2.c, xctr.c and lib/crypto/polyval.c.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::aes::AesKey;

verus! {

pub const MAX_HCTR2_BYTES:usize=16777216;

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Error { KeyLength, Length, Retired, Primitive }

spec fn little_word(raw:Seq<u8>,at:nat,n:nat) -> u64
    decreases n
{
    if n==0 {0u64}else{little_word(raw,at,(n-1) as nat)|((raw[(at+n-1) as int] as u64)<<(((n-1)*8) as u32))}
}
spec fn xor_block(a:Seq<u8>,b:Seq<u8>) -> Seq<u8> {Seq::new(16,|i:int| a[i]^b[i])}
struct Carryless {low:u64,high:u64,shifted_low:u64,shifted_high:u64}
spec fn carryless_steps(a:u64,b:u64,n:nat) -> Carryless
    decreases n
{
    if n==0 {Carryless {low:0,high:0,shifted_low:a,shifted_high:0}}
    else {
        let old=carryless_steps(a,b,(n-1) as nat);
        let selected=(b>>((n-1) as u32))&1!=0;
        Carryless {
            low:old.low^(if selected {old.shifted_low}else{0u64}),
            high:old.high^(if selected {old.shifted_high}else{0u64}),
            shifted_low:old.shifted_low<<1,
            shifted_high:(old.shifted_high<<1)|(old.shifted_low>>63),
        }
    }
}
pub closed spec fn polyval_dot_reference(a:Seq<u8>,b:Seq<u8>) -> Seq<u8> {
    let a0=little_word(a,0,8);let a1=little_word(a,8,8);
    let b0=little_word(b,0,8);let b1=little_word(b,8,8);
    let low=carryless_steps(a0,b0,64);let high=carryless_steps(a1,b1,64);
    let middle=carryless_steps(a0^a1,b0^b1,64);
    let c0=low.low;let c1=low.high^(middle.low^low.low^high.low);
    let c2=high.low^(middle.high^low.high^high.high);let c3=high.high;
    let c1=c1^((c0<<63)^(c0<<62)^(c0<<57));
    let c2=c2^c0^(c0>>1)^(c0>>2)^(c0>>7);
    let c2=c2^(c1<<63)^(c1<<62)^(c1<<57);
    let c3=c3^c1^(c1>>1)^(c1>>2)^(c1>>7);
    Seq::new(16,|i:int| if i<8 {(c2>>((i*8) as u32)) as u8}else{(c3>>(((i-8)*8) as u32)) as u8})
}
spec fn polyval_blocks(h:Seq<u8>,raw:Seq<u8>,n:nat) -> Seq<u8>
    decreases n
{
    if n==0 {Seq::new(16,|i:int|0u8)}
    else {polyval_dot_reference(xor_block(polyval_blocks(h,raw,(n-1) as nat),
        raw.subrange(((n-1)*16) as int,(n*16) as int)),h)}
}
pub closed spec fn hctr2_hash_input(tweak:Seq<u8>,bulk:Seq<u8>,has_remainder:bool) -> Seq<u8> {
    let payload=48+bulk.len()+if has_remainder {1nat}else{0nat};
    let size=((payload+15)/16)*16;
    Seq::new(size,|i:int| {
        if i<16 {
            let domain=if has_remainder {515u64}else{514u64};
            if i<8 {(domain>>((i*8) as u32)) as u8}else{0u8}
        }else if i<48 {tweak[i-16]}
        else if i<48+bulk.len() {bulk[i-48]}
        else if i==48+bulk.len() && has_remainder {1u8}else{0u8}
    })
}
pub closed spec fn hctr2_hash_reference(h:Seq<u8>,tweak:Seq<u8>,bulk:Seq<u8>,has_remainder:bool) -> Seq<u8> {
    let raw=hctr2_hash_input(tweak,bulk,has_remainder);polyval_blocks(h,raw,raw.len()/16)
}
spec fn counter_block(iv:Seq<u8>,counter:nat) -> Seq<u8> {
    Seq::new(16,|i:int| iv[i]^(if i<4 {((counter as u32)>>((i*8) as u32)) as u8}else{0u8}))
}
pub closed spec fn xctr_reference(key:&AesKey,iv:Seq<u8>,input:Seq<u8>) -> Seq<u8> {
    Seq::new(input.len(),|i:int| input[i]^key.aes_encrypt_reference(counter_block(iv,(i/16+1) as nat))[i%16])
}

fn aes_encrypt(key:&AesKey,input:[u8;16]) -> (r:Result<[u8;16],Error>)
    ensures match r {Ok(v)=>!key.aes_retired() && v@==key.aes_encrypt_reference(input@),Err(_)=>key.aes_retired()},
{
    match key.encrypt_aes_block(input) {Ok(v)=>Ok(v),Err(_)=>Err(Error::Primitive)}
}
fn aes_decrypt(key:&AesKey,input:[u8;16]) -> (r:Result<[u8;16],Error>)
    ensures match r {Ok(v)=>!key.aes_retired() && v@==key.aes_decrypt_reference(input@),Err(_)=>key.aes_retired()},
{
    match key.decrypt_aes_block(input) {Ok(v)=>Ok(v),Err(_)=>Err(Error::Primitive)}
}
fn read64(raw:&[u8],at:usize) -> (r:u64)
    requires at<=raw.len(),8<=raw.len()-at,
    ensures r==little_word(raw@,at as nat,8),
{
    let mut word=0u64;let mut i=0usize;while i<8 invariant i<=8,at<=raw.len(),8<=raw.len()-at,word==little_word(raw@,at as nat,i as nat), decreases 8-i, {word|=(raw[at+i] as u64)<<(8*i);i+=1;}word
}
fn write64(raw:&mut [u8;16],at:usize,word:u64)
    requires at<=8,
    ensures forall|i:int| 0<=i<16 ==> final(raw)@[i]==
        if at<=i<at+8 {(word>>(((i-at)*8) as u32)) as u8}else{old(raw)@[i]},
{
    let mut i=0usize;
    while i<8
        invariant i<=8,at<=8,forall|j:int| 0<=j<16 ==> raw@[j]==
            if at<=j<at+i {(word>>(((j-at)*8) as u32)) as u8}else{old(raw)@[j]},
        decreases 8-i,
    {raw[at+i]=(word>>(8*i)) as u8;i+=1;}
}
fn copy_block(raw:&[u8],at:usize) -> (r:[u8;16])
    requires at<=raw.len(),16<=raw.len()-at,
    ensures r@==raw@.subrange(at as int,at as int+16),
{
    let mut b=[0u8;16];let mut i=0usize;while i<16 invariant i<=16,at<=raw.len(),16<=raw.len()-at,forall|j:int| 0<=j<i ==> b@[j]==raw@[at as int+j], decreases 16-i, {b[i]=raw[at+i];i+=1;}b
}
fn xor(a:[u8;16],b:[u8;16]) -> (r:[u8;16]) ensures r@==xor_block(a@,b@), {
    let mut result=[0u8;16];let mut i=0usize;while i<16 invariant i<=16,forall|j:int| 0<=j<i ==> result@[j]==a@[j]^b@[j], decreases 16-i, {result[i]=a[i]^b[i];i+=1;}result
}

// Fixed-step carryless multiplication: (low,high) is the unreduced 128-bit
// polynomial product of two 64-bit coefficient vectors.
fn clmul64(a:u64,b:u64) -> (r:(u64,u64))
    ensures r==(carryless_steps(a,b,64).low,carryless_steps(a,b,64).high),
{
    let mut low=0u64;let mut high=0u64;
    let mut shifted_low=a;let mut shifted_high=0u64;let mut i=0usize;
    while i<64
        invariant i<=64,low==carryless_steps(a,b,i as nat).low,high==carryless_steps(a,b,i as nat).high,
            shifted_low==carryless_steps(a,b,i as nat).shifted_low,shifted_high==carryless_steps(a,b,i as nat).shifted_high,
        decreases 64-i,
    {
        let mask=0u64.wrapping_sub((b>>i)&1);
        low^=shifted_low&mask;high^=shifted_high&mask;
        shifted_high=(shifted_high<<1)|(shifted_low>>63);shifted_low<<=1;i+=1;
    }
    (low,high)
}

// POLYVAL uses dot(a,b)=a*b*x^-128 over
// x^128+x^127+x^126+x^121+1; ordinary field multiplication is insufficient.
fn polyval_dot(a:[u8;16],b:[u8;16]) -> (r:[u8;16]) ensures r@==polyval_dot_reference(a@,b@), {
    let a0=read64(&a,0);let a1=read64(&a,8);let b0=read64(&b,0);let b1=read64(&b,8);
    let (c0,mut c1)=clmul64(a0,b0);let (mut c2,mut c3)=clmul64(a1,b1);
    let (mi0,mi1)=clmul64(a0^a1,b0^b1);
    let middle_low=mi0^c0^c2;let middle_high=mi1^c1^c3;
    c1^=middle_low;c2^=middle_high;
    c1^=(c0<<63)^(c0<<62)^(c0<<57);
    c2^=c0^(c0>>1)^(c0>>2)^(c0>>7);
    c2^=(c1<<63)^(c1<<62)^(c1<<57);
    c3^=c1^(c1>>1)^(c1>>2)^(c1>>7);
    let mut result=[0u8;16];write64(&mut result,0,c2);write64(&mut result,8,c3);result
}
fn hash_message(h:[u8;16],tweak:[u8;32],bulk:&[u8],has_remainder:bool) -> (r:[u8;16])
    requires bulk.len()<=MAX_HCTR2_BYTES,has_remainder==(bulk.len()%16!=0),
    ensures r@==hctr2_hash_reference(h@,tweak@,bulk@,has_remainder),
{
    let mut domain=[0u8;16];write64(&mut domain,0,if has_remainder {515}else{514});
    let mut acc=polyval_dot(domain,h);
    acc=polyval_dot(xor(acc,copy_block(&tweak,0)),h);
    acc=polyval_dot(xor(acc,copy_block(&tweak,16)),h);
    let mut at=0usize;
    while bulk.len()-at>=16
        invariant at<=bulk.len(),at%16==0,bulk.len()<=MAX_HCTR2_BYTES,
        decreases bulk.len()-at,
    {
        acc=polyval_dot(xor(acc,copy_block(bulk,at)),h);at+=16;
    }
    if has_remainder {
        let left=bulk.len()-at;let mut tail=[0u8;16];let mut i=0usize;
        while i<left invariant i<=left<16,at+left==bulk.len(), decreases left-i, {tail[i]=bulk[at+i];i+=1;}tail[left]=1;
        acc=polyval_dot(xor(acc,tail),h);
    }
    acc
}
fn xctr(key:&AesKey,iv:[u8;16],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    requires input.len()<=MAX_HCTR2_BYTES,
    ensures match r {Ok(v)=>v@==xctr_reference(key,iv@,input@),Err(_)=>key.aes_retired()},
{
    let mut out=Vec::new();let mut at=0usize;let mut counter=1u32;
    while at<input.len()
        invariant at<=input.len()<=MAX_HCTR2_BYTES,out.len()==at,counter==at/16+1,at%16==0 || at==input.len(),
            out@==xctr_reference(key,iv@,input@).take(at as int),
        decreases input.len()-at,
    {
        let mut request=iv;let mut i=0usize;while i<4 invariant i<=4, decreases 4-i, {request[i]^=(counter>>(8*i)) as u8;i+=1;}
        let stream=aes_encrypt(key,request)?;
        let remain=input.len()-at;let take=if remain<16 {remain}else{16};i=0;
        while i<take invariant i<=take<=16,at+take<=input.len(),out.len()==at+i, decreases take-i, {out.push(input[at+i]^stream[i]);i+=1;}
        at+=take;counter+=1;
    }
    Ok(out)
}
pub struct Hctr2Key {cipher:AesKey,hbar:[u8;16],l:[u8;16],retired:bool}
impl Hctr2Key {
    pub closed spec fn hctr2_retired(&self) -> bool {self.retired}
    pub closed spec fn hctr2_valid(&self) -> bool {
        self.retired ==> self.cipher.aes_retired()
            && self.hbar@==Seq::new(16,|i:int|0u8) && self.l@==Seq::new(16,|i:int|0u8)
    }
    pub closed spec fn hctr2_derived_from(&self,raw:Seq<u8>) -> bool {
        raw.len()==32 && !self.retired && !self.cipher.aes_retired() && self.cipher.aes_round_count()==14
            && self.cipher.aes_schedule().take(240)==crate::aes::expanded_key_reference(raw,52)
            && self.hbar@==self.cipher.aes_encrypt_reference(Seq::new(16,|i:int|0u8))
            && self.l@==self.cipher.aes_encrypt_reference(Seq::new(16,|i:int|if i==0 {1u8}else{0u8}))
    }
    pub closed spec fn hctr2_reference(&self,tweak:Seq<u8>,input:Seq<u8>,decrypt:bool) -> Seq<u8> {
        let bulk=input.subrange(16,input.len() as int);let remainder=input.len()%16!=0;
        let masked=xor_block(input.take(16),hctr2_hash_reference(self.hbar@,tweak,bulk,remainder));
        let changed=if decrypt {self.cipher.aes_decrypt_reference(masked)}else{self.cipher.aes_encrypt_reference(masked)};
        let iv=xor_block(xor_block(masked,changed),self.l@);let tail=xctr_reference(&self.cipher,iv,bulk);
        xor_block(changed,hctr2_hash_reference(self.hbar@,tweak,tail,remainder))+tail
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {self.hctr2_valid()}
    pub fn new_hctr2_key(raw:&[u8]) -> (r:Result<Self,Error>)
        ensures match r {Ok(k)=>k.hctr2_valid() && k.hctr2_derived_from(raw@),Err(_)=>raw.len()!=32},
    {
        if raw.len()!=32 {return Err(Error::KeyLength);}
        let cipher=match AesKey::new_aes_key(raw) {Ok(v)=>v,Err(_)=>return Err(Error::KeyLength)};
        let hbar=aes_encrypt(&cipher,[0u8;16])?;let mut one=[0u8;16];one[0]=1;
        let l=aes_encrypt(&cipher,one)?;
        Ok(Self {cipher,hbar,l,retired:false})
    }
    fn apply(&self,tweak:[u8;32],input:&[u8],decrypt:bool) -> (r:Result<Vec<u8>,Error>)
        ensures match r {Ok(v)=>!self.hctr2_retired() && 16<=input.len()<=MAX_HCTR2_BYTES && v.len()==input.len()
            && v@==self.hctr2_reference(tweak@,input@,decrypt),Err(_)=>true},
    {
        if self.retired {return Err(Error::Retired);}
        if input.len()<16 || input.len()>MAX_HCTR2_BYTES {return Err(Error::Length);}
        let remainder=input.len()%16!=0;let bulk=&input[16..];
        let hashed=hash_message(self.hbar,tweak,bulk,remainder);
        let masked=xor(copy_block(input,0),hashed);
        let changed=if decrypt {aes_decrypt(&self.cipher,masked)?}else{aes_encrypt(&self.cipher,masked)?};
        let stream_iv=xor(xor(masked,changed),self.l);
        let changed_bulk=xctr(&self.cipher,stream_iv,bulk)?;
        let output_first=xor(changed,hash_message(self.hbar,tweak,changed_bulk.as_slice(),remainder));
        let mut out=Vec::new();let mut i=0usize;while i<16 invariant i<=16,out@==output_first@.take(i as int), decreases 16-i, {out.push(output_first[i]);i+=1;}
        let ghost first=out@;i=0;while i<changed_bulk.len() invariant i<=changed_bulk.len(),out@==first+changed_bulk@.take(i as int), decreases changed_bulk.len()-i, {out.push(changed_bulk[i]);i+=1;}Ok(out)
    }
    pub fn encrypt_hctr2(&self,tweak:[u8;32],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
        ensures match r {Ok(v)=>!self.hctr2_retired() && 16<=input.len()<=MAX_HCTR2_BYTES && v.len()==input.len()
            && v@==self.hctr2_reference(tweak@,input@,false),Err(_)=>true},
    {self.apply(tweak,input,false)}
    pub fn decrypt_hctr2(&self,tweak:[u8;32],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
        ensures match r {Ok(v)=>!self.hctr2_retired() && 16<=input.len()<=MAX_HCTR2_BYTES && v.len()==input.len()
            && v@==self.hctr2_reference(tweak@,input@,true),Err(_)=>true},
    {self.apply(tweak,input,true)}
    pub fn retire_hctr2(&mut self)
        ensures final(self).hctr2_valid(),final(self).hctr2_retired(),
        opens_invariants none
        no_unwind
    {
        proof {use_type_invariant(&*self);}
        self.cipher.retire_aes();self.hbar=[0u8;16];self.l=[0u8;16];self.retired=true;
    }
}
impl Drop for Hctr2Key {
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {self.retire_hctr2();}
}
pub fn encrypt_aes256_hctr2(raw_key:&[u8],tweak:[u8;32],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>raw_key.len()==32 && 16<=input.len()<=MAX_HCTR2_BYTES && v.len()==input.len(),Err(_)=>true},
{
    Hctr2Key::new_hctr2_key(raw_key)?.encrypt_hctr2(tweak,input)
}
pub fn decrypt_aes256_hctr2(raw_key:&[u8],tweak:[u8;32],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>raw_key.len()==32 && 16<=input.len()<=MAX_HCTR2_BYTES && v.len()==input.len(),Err(_)=>true},
{
    Hctr2Key::new_hctr2_key(raw_key)?.decrypt_hctr2(tweak,input)
}

}
