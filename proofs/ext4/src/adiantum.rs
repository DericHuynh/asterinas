// SPDX-License-Identifier: MPL-2.0

//! Adiantum-XChaCha12-AES256 with Linux's 32-byte tweak encoding.
//! Actual XChaCha12, NH and Poly1305 arithmetic are implemented here; AES is
//! supplied by the existing executable AES module. This is length-preserving
//! encryption, not authentication. Constant-time compilation, physical key
//! erasure and nonce-generation policy remain separate obligations.

use vstd::prelude::*;
use crate::aes::AesKey;

verus! {

pub const MAX_ADIANTUM_BYTES:usize=16777216;
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Error {KeyLength,Length,Counter,Primitive}

spec fn add32(a:u32,b:u32) -> u32 {((a as nat+b as nat)%4294967296) as u32}
spec fn rotate(x:u32,count:u32) -> u32 {let n=count%32;if n==0{x}else{(x<<n)|(x>>(32-n))}}
spec fn little(raw:Seq<u8>,at:nat,n:nat) -> nat
    decreases n
{
    if n==0 {0}else{little(raw,at,(n-1) as nat)+(raw[(at+n-1) as int] as nat)*pow256((n-1) as nat)}
}
spec fn pow256(n:nat) -> nat decreases n {if n==0{1}else{256*pow256((n-1) as nat)}}
spec fn initial_state(key:Seq<u8>,iv:Seq<u8>) -> Seq<u32> {
    seq![0x61707865u32,0x3320646eu32,0x79622d32u32,0x6b206574u32]
        +Seq::new(8,|i:int|little(key,(i*4) as nat,4) as u32)
        +Seq::new(4,|i:int|little(iv,(i*4) as nat,4) as u32)
}
spec fn quarter_reference(s:Seq<u32>,a:int,b:int,c:int,d:int) -> Seq<u32> {
    let s=s.update(a,add32(s[a],s[b]));let s=s.update(d,rotate(s[d]^s[a],16));
    let s=s.update(c,add32(s[c],s[d]));let s=s.update(b,rotate(s[b]^s[c],12));
    let s=s.update(a,add32(s[a],s[b]));let s=s.update(d,rotate(s[d]^s[a],8));
    let s=s.update(c,add32(s[c],s[d]));s.update(b,rotate(s[b]^s[c],7))
}
spec fn double_round(s:Seq<u32>) -> Seq<u32> {
    let s=quarter_reference(s,0,4,8,12);let s=quarter_reference(s,1,5,9,13);
    let s=quarter_reference(s,2,6,10,14);let s=quarter_reference(s,3,7,11,15);
    let s=quarter_reference(s,0,5,10,15);let s=quarter_reference(s,1,6,11,12);
    let s=quarter_reference(s,2,7,8,13);quarter_reference(s,3,4,9,14)
}
#[verifier::opaque]
spec fn permuted(s:Seq<u32>,n:nat) -> Seq<u32>
    decreases n
{
    if n==0 {s}else{double_round(permuted(s,(n-1) as nat))}
}
spec fn stream_state(raw_key:Seq<u8>,iv:Seq<u8>) -> Seq<u32> {
    let h=permuted(initial_state(raw_key,iv.take(16)),6);
    let subkey=Seq::new(32,|i:int| {
        let w=if i<16 {h[i/4]}else{h[12+(i-16)/4]};
        (w>>(((i%4)*8) as u32)) as u8
    });
    initial_state(subkey,iv.subrange(24,32)+iv.subrange(16,24))
}
pub closed spec fn xchacha12_reference(raw_key:Seq<u8>,iv:Seq<u8>,input:Seq<u8>) -> Seq<u8> {
    let seed=stream_state(raw_key,iv);
    Seq::new(input.len(),|i:int| {
        let state=seed.update(12,add32(seed[12],(i/64) as u32));
        let result=permuted(state,6);let j=(i%64)/4;
        input[i]^((add32(result[j],state[j])>>(((i%4)*8) as u32)) as u8)
    })
}
spec fn word_modulus() -> nat {(u64::MAX as nat)+1}
spec fn double_word_modulus() -> nat {word_modulus()*word_modulus()}
spec fn p130() -> nat {(4*double_word_modulus()-5) as nat}
spec fn limb_value(a:Seq<u64>) -> nat {a[0] as nat+(a[1] as nat)*word_modulus()+(a[2] as nat)*double_word_modulus()}
spec fn canonical(a:Seq<u64>) -> bool {a.len()==3 && limb_value(a)<p130()}
spec fn clamp(raw:Seq<u8>) -> nat {
    let mask=(0x0fff_fffc_0fff_fffcu128<<64)|0x0fff_fffc_0fff_ffffu128;
    ((little(raw,0,16) as u128)&mask) as nat
}
spec fn poly_blocks(r:nat,input:Seq<u8>,n:nat) -> nat
    decreases n
{
    if n==0 {0}else{((poly_blocks(r,input,(n-1) as nat)+little(input,((n-1)*16) as nat,16)
        +double_word_modulus())*r)%p130()}
}
spec fn encoded128(n:nat) -> Seq<u8> {Seq::new(16,|i:int| ((n as u128)>>((i*8) as u32)) as u8)}
pub closed spec fn poly1305_reference(raw_r:Seq<u8>,input:Seq<u8>) -> Seq<u8> {
    encoded128(poly_blocks(clamp(raw_r),input,input.len()/16))
}
spec fn nh_word(input:Seq<u8>,chunk:nat,unit:nat,word:nat) -> u32 {
    let at=chunk*1024+unit*16+word*4;
    let raw=Seq::new(4,|i:int| if (at as int+i)<input.len() {input[at as int+i]}else{0u8});
    little(raw,0,4) as u32
}
spec fn nh_units(derived:Seq<u8>,input:Seq<u8>,chunk:nat,pass:nat,n:nat) -> u64
    decreases n
{
    if n==0 {0}else {
        let u=(n-1) as nat;let k=64+(u*4+pass*4)*4;
        let a=add32(nh_word(input,chunk,u,0),little(derived,k,4) as u32) as nat;
        let b=add32(nh_word(input,chunk,u,2),little(derived,k+8,4) as u32) as nat;
        let c=add32(nh_word(input,chunk,u,1),little(derived,k+4,4) as u32) as nat;
        let d=add32(nh_word(input,chunk,u,3),little(derived,k+12,4) as u32) as nat;
        ((nh_units(derived,input,chunk,pass,u) as nat+a*b+c*d)%word_modulus()) as u64
    }
}
pub closed spec fn nh_reference(derived:Seq<u8>,input:Seq<u8>) -> Seq<u8> {
    Seq::new(((input.len()+1023)/1024)*32,|i:int| {
        let chunk=(i/32) as nat;let remain=(input.len()-chunk*1024) as nat;
        let take=if remain<1024 {remain}else{1024nat};
        let sum=nh_units(derived,input,chunk,((i%32)/8) as nat,(take+15)/16);
        (sum>>(((i%8)*8) as u32)) as u8
    })
}
pub closed spec fn message_hash_reference(derived:Seq<u8>,input:Seq<u8>) -> Seq<u8> {
    poly1305_reference(derived.subrange(48,64),nh_reference(derived,input))
}
pub closed spec fn header_hash_reference(derived:Seq<u8>,tweak:Seq<u8>,bulk:nat) -> Seq<u8> {
    poly1305_reference(derived.subrange(32,48),encoded128(bulk*8)+tweak)
}
spec fn added128(a:Seq<u8>,b:Seq<u8>) -> Seq<u8> {encoded128(little(a,0,16)+little(b,0,16))}
spec fn subtracted128(a:Seq<u8>,b:Seq<u8>) -> Seq<u8> {
    encoded128((little(a,0,16)+double_word_modulus()-little(b,0,16)) as nat)
}
pub closed spec fn adiantum_derived_reference(raw:Seq<u8>) -> Seq<u8> {
    xchacha12_reference(raw,Seq::new(32,|i:int|if i==0{1u8}else{0u8}),Seq::new(1136,|i:int|0u8))
}
pub closed spec fn adiantum_reference(cipher:&AesKey,raw:Seq<u8>,tweak:Seq<u8>,input:Seq<u8>,decrypt:bool) -> Seq<u8> {
    let derived=adiantum_derived_reference(raw);let bulk=input.take(input.len() as int-16);
    let header=header_hash_reference(derived,tweak,bulk.len());
    let first=message_hash_reference(derived,bulk);
    let middle=added128(added128(input.subrange(input.len() as int-16,input.len() as int),header),first);
    let middle=if decrypt {middle}else{cipher.aes_encrypt_reference(middle)};
    let stream_iv=middle+Seq::new(16,|i:int|if i==0{1u8}else{0u8});
    let out=xchacha12_reference(raw,stream_iv,bulk);
    let changed=if decrypt {cipher.aes_decrypt_reference(middle)}else{middle};
    out+subtracted128(subtracted128(changed,header),message_hash_reference(derived,out))
}
pub closed spec fn adiantum_result_is_standard(raw:Seq<u8>,tweak:Seq<u8>,input:Seq<u8>,output:Seq<u8>,decrypt:bool) -> bool {
    exists|cipher:AesKey| !cipher.aes_retired() && cipher.aes_round_count()==14
        && cipher.aes_schedule().take(240)==crate::aes::expanded_key_reference(adiantum_derived_reference(raw).take(32),52)
        && output==adiantum_reference(&cipher,raw,tweak,input,decrypt)
}

fn rotl(x:u32,count:u32) -> (r:u32) ensures r==rotate(x,count) {let n=count%32;if n==0{x}else{(x<<n)|(x>>(32-n))}}
fn le32(raw:&[u8],at:usize) -> (r:u32) requires at<=raw.len(),4<=raw.len()-at, ensures r==little(raw@,at as nat,4), {
    (raw[at] as u32)|((raw[at+1] as u32)<<8)|((raw[at+2] as u32)<<16)|((raw[at+3] as u32)<<24)
}
fn le64(raw:&[u8],at:usize) -> (r:u64) requires at<=raw.len(),8<=raw.len()-at, ensures r==little(raw@,at as nat,8), {
    let mut value=0u64;let mut i=0usize;while i<8{value|=(raw[at+i] as u64)<<(8*i);i+=1;}value
}
fn put32(out:&mut [u8],at:usize,value:u32) requires at<=old(out).len(),4<=old(out).len()-at, ensures final(out).len()==old(out).len(), {
    let mut i=0usize;while i<4{out[at+i]=(value>>(8*i)) as u8;i+=1;}
}
fn put64(out:&mut [u8],at:usize,value:u64) requires at<=old(out).len(),8<=old(out).len()-at, ensures final(out).len()==old(out).len(), {
    let mut i=0usize;while i<8{out[at+i]=(value>>(8*i)) as u8;i+=1;}
}
fn copy16(raw:&[u8],at:usize) -> (r:[u8;16]) requires at<=raw.len(),16<=raw.len()-at, ensures r@==raw@.subrange(at as int,at as int+16), {let mut out=[0u8;16];let mut i=0usize;while i<16{out[i]=raw[at+i];i+=1;}out}
fn quarter(s:&mut [u32;16],a:usize,b:usize,c:usize,d:usize) requires a<16,b<16,c<16,d<16, ensures final(s)@==quarter_reference(old(s)@,a as int,b as int,c as int,d as int), {
    s[a]=s[a].wrapping_add(s[b]);s[d]=rotl(s[d]^s[a],16);
    s[c]=s[c].wrapping_add(s[d]);s[b]=rotl(s[b]^s[c],12);
    s[a]=s[a].wrapping_add(s[b]);s[d]=rotl(s[d]^s[a],8);
    s[c]=s[c].wrapping_add(s[d]);s[b]=rotl(s[b]^s[c],7);
}
fn permute(s:&mut [u32;16]) ensures final(s)@==permuted(old(s)@,6), {
    proof {reveal(permuted);}
    let mut i=0usize;while i<6 invariant i<=6,s@==permuted(old(s)@,i as nat), decreases 6-i, {
        quarter(s,0,4,8,12);quarter(s,1,5,9,13);quarter(s,2,6,10,14);quarter(s,3,7,11,15);
        quarter(s,0,5,10,15);quarter(s,1,6,11,12);quarter(s,2,7,8,13);quarter(s,3,4,9,14);i+=1;
    }
}
fn initial(key:&[u8],iv:&[u8]) -> (r:[u32;16]) requires key.len()==32,iv.len()==16, ensures r@==initial_state(key@,iv@), {
    let mut s=[0u32;16];s[0]=0x61707865;s[1]=0x3320646e;s[2]=0x79622d32;s[3]=0x6b206574;
    let mut i=0usize;while i<8{s[4+i]=le32(key,i*4);i+=1;}
    i=0;while i<4{s[12+i]=le32(iv,i*4);i+=1;}s
}
pub fn xchacha12_bytes(raw_key:&[u8],iv:[u8;32],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>raw_key.len()==32 && input.len()<=MAX_ADIANTUM_BYTES && v.len()==input.len()
        && v@==xchacha12_reference(raw_key@,iv@,input@),Err(_)=>true},
{
    if raw_key.len()!=32{return Err(Error::KeyLength);}
    if input.len()>MAX_ADIANTUM_BYTES{return Err(Error::Length);}
    let count=le32(&iv,24) as u64;let blocks=(input.len() as u64+63)/64;
    if blocks>4294967296u64-count{return Err(Error::Counter);}
    let mut h=initial(raw_key,&iv[..16]);permute(&mut h);
    let mut subkey=[0u8;32];let mut i=0usize;
    while i<4{put32(&mut subkey,i*4,h[i]);put32(&mut subkey,16+i*4,h[12+i]);i+=1;}
    let mut real_iv=[0u8;16];i=0;
    while i<8{real_iv[i]=iv[24+i];real_iv[8+i]=iv[16+i];i+=1;}
    let mut state=initial(&subkey,&real_iv);let mut at=0usize;let mut out=Vec::new();
    while at<input.len() {
        let mut working=state;permute(&mut working);let mut stream=[0u8;64];i=0;
        while i<16{put32(&mut stream,i*4,working[i].wrapping_add(state[i]));i+=1;}
        let left=input.len()-at;let take=if left<64{left}else{64};i=0;
        while i<take{out.push(input[at+i]^stream[i]);i+=1;}
        state[12]=state[12].wrapping_add(1);at+=take;
    }
    Ok(out)
}

// Canonical arithmetic in GF(2^130-5), represented as three little-endian
// limbs. Fixed 128-step multiplication avoids native wide multiplication.
fn add_mod(a:[u64;3],b:[u64;3]) -> (r:[u64;3])
    requires canonical(a@),canonical(b@),
    ensures canonical(r@),limb_value(r@)==(limb_value(a@)+limb_value(b@))%p130(),
{
    let lo=a[0] as u128+b[0] as u128;
    let mid=a[1] as u128+b[1] as u128+(lo>>64);
    let top=a[2]+b[2]+(mid>>64) as u64;
    let sum=[lo as u64,mid as u64,top];
    let p0=0xffff_ffff_ffff_fffbu64;
    let borrow0=if sum[0]<p0{1u64}else{0u64};
    let borrow1=if sum[1]<u64::MAX || (sum[1]==u64::MAX && borrow0!=0){1u64}else{0u64};
    let difference=[sum[0].wrapping_sub(p0),sum[1].wrapping_sub(u64::MAX).wrapping_sub(borrow0),
        sum[2].wrapping_sub(3).wrapping_sub(borrow1)];
    let reduce=sum[2]>3 || (sum[2]==3 && sum[1]==u64::MAX && sum[0]>=p0);
    let mask=0u64.wrapping_sub(if reduce{1}else{0});
    [sum[0]&!mask|difference[0]&mask,sum[1]&!mask|difference[1]&mask,sum[2]&!mask|difference[2]&mask]
}
fn mul_mod(mut a:[u64;3],r:[u64;2]) -> (result:[u64;3])
    requires canonical(a@),
    ensures canonical(result@),limb_value(result@)==
        (limb_value(a@)*(r@[0] as nat+(r@[1] as nat)*word_modulus()))%p130(),
{
    let mut out=[0u64;3];let mut i=0usize;
    while i<128 {
        let candidate=add_mod(out,a);
        let mask=0u64.wrapping_sub((r[i/64]>>(i%64))&1);
        let mut j=0usize;while j<3{out[j]=out[j]&!mask|candidate[j]&mask;j+=1;}
        a=add_mod(a,a);i+=1;
    }
    out
}
struct Poly {r:[u64;2],h:[u64;3]}
impl Poly {
    spec fn value(&self) -> nat {limb_value(self.h@)}
    spec fn multiplier(&self) -> nat {self.r@[0] as nat+(self.r@[1] as nat)*word_modulus()}
    spec fn valid(&self) -> bool {canonical(self.h@)}
    fn new(raw:&[u8]) -> (r:Self) requires raw.len()==16, ensures r.valid(),r.value()==0,r.multiplier()==clamp(raw@), {
        let mut key=[0u8;16];let mut i=0usize;
        while i<16 {
            let mut b=raw[i];
            if i==3 || i==7 || i==11 || i==15{b&=15;}
            if i==4 || i==8 || i==12{b&=252;}
            key[i]=b;i+=1;
        }
        Self {r:[le64(&key,0),le64(&key,8)],h:[0u64;3]}
    }
    fn update_block(&mut self,raw:&[u8])
        requires old(self).valid(),raw.len()==16,
        ensures final(self).valid(),final(self).multiplier()==old(self).multiplier(),
            final(self).value()==((old(self).value()+little(raw@,0,16)+double_word_modulus())*old(self).multiplier())%p130(),
    {
        let added=add_mod(self.h,[le64(raw,0),le64(raw,8),1]);self.h=mul_mod(added,self.r);
    }
    fn finish(&self) -> (r:[u8;16]) requires self.valid(), ensures r@==encoded128(self.value()), {let mut out=[0u8;16];put64(&mut out,0,self.h[0]);put64(&mut out,8,self.h[1]);out}
}
fn header_hash(derived:&[u8],tweak:&[u8;32],bulk:usize) -> (r:[u8;16]) requires derived.len()==1136,bulk<=MAX_ADIANTUM_BYTES, ensures r@==header_hash_reference(derived@,tweak@,bulk as nat), {
    let mut p=Poly::new(&derived[32..48]);let mut header=[0u8;16];put64(&mut header,0,bulk as u64*8);
    p.update_block(&header);p.update_block(&tweak[..16]);p.update_block(&tweak[16..]);p.finish()
}
fn message_hash(derived:&[u8],input:&[u8]) -> (r:[u8;16]) requires derived.len()==1136,input.len()<=MAX_ADIANTUM_BYTES, ensures r@==message_hash_reference(derived@,input@), {
    let mut poly=Poly::new(&derived[48..64]);let mut at=0usize;
    while at<input.len() {
        let remain=input.len()-at;let take=if remain<1024{remain}else{1024};
        let units=(take+15)/16;let mut padded=[0u8;1024];let mut i=0usize;
        while i<take{padded[i]=input[at+i];i+=1;}
        let mut sums=[0u64;4];let mut unit=0usize;
        while unit<units {
            let x=unit*16;let m0=le32(&padded,x);let m1=le32(&padded,x+4);let m2=le32(&padded,x+8);let m3=le32(&padded,x+12);
            let mut pass=0usize;while pass<4 {
                let key=64+(unit*4+pass*4)*4;
                let a=m0.wrapping_add(le32(derived,key)) as u64;let b=m2.wrapping_add(le32(derived,key+8)) as u64;
                let c=m1.wrapping_add(le32(derived,key+4)) as u64;let d=m3.wrapping_add(le32(derived,key+12)) as u64;
                sums[pass]=sums[pass].wrapping_add(a.wrapping_mul(b)).wrapping_add(c.wrapping_mul(d));pass+=1;
            }
            unit+=1;
        }
        let mut nh=[0u8;32];i=0;while i<4{put64(&mut nh,i*8,sums[i]);i+=1;}
        poly.update_block(&nh[..16]);poly.update_block(&nh[16..]);at+=take;
    }
    poly.finish()
}
fn add128(a:[u8;16],b:[u8;16]) -> (r:[u8;16]) ensures r@==added128(a@,b@), {
    let low=le64(&a,0).wrapping_add(le64(&b,0));let carry=if low<le64(&a,0){1}else{0};
    let high=le64(&a,8).wrapping_add(le64(&b,8)).wrapping_add(carry);
    let mut out=[0u8;16];put64(&mut out,0,low);put64(&mut out,8,high);out
}
fn sub128(a:[u8;16],b:[u8;16]) -> (r:[u8;16]) ensures r@==subtracted128(a@,b@), {
    let low=le64(&a,0).wrapping_sub(le64(&b,0));let borrow=if le64(&a,0)<le64(&b,0){1}else{0};
    let high=le64(&a,8).wrapping_sub(le64(&b,8)).wrapping_sub(borrow);
    let mut out=[0u8;16];put64(&mut out,0,low);put64(&mut out,8,high);out
}
fn apply(raw_key:&[u8],tweak:[u8;32],input:&[u8],decrypt:bool) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>raw_key.len()==32 && 16<=input.len()<=MAX_ADIANTUM_BYTES && v.len()==input.len()
        && adiantum_result_is_standard(raw_key@,tweak@,input@,v@,decrypt),Err(_)=>true},
{
    if raw_key.len()!=32{return Err(Error::KeyLength);}
    if input.len()<16 || input.len()>MAX_ADIANTUM_BYTES{return Err(Error::Length);}
    let mut key_iv=[0u8;32];key_iv[0]=1;
    let zeroes=[0u8;1136];let derived=xchacha12_bytes(raw_key,key_iv,&zeroes)?;
    let aes=match AesKey::new_aes_key(&derived[..32]){Ok(v)=>v,Err(_)=>return Err(Error::Primitive)};
    let bulk=input.len()-16;let header=header_hash(derived.as_slice(),&tweak,bulk);
    let first_hash=message_hash(derived.as_slice(),&input[..bulk]);
    let mut middle=add128(add128(copy16(input,bulk),header),first_hash);
    if !decrypt{middle=match aes.encrypt_aes_block(middle){Ok(v)=>v,Err(_)=>return Err(Error::Primitive)};}
    let mut stream_iv=[0u8;32];let mut i=0usize;while i<16{stream_iv[i]=middle[i];i+=1;}stream_iv[16]=1;
    let mut out=xchacha12_bytes(raw_key,stream_iv,&input[..bulk])?;
    if decrypt{middle=match aes.decrypt_aes_block(middle){Ok(v)=>v,Err(_)=>return Err(Error::Primitive)};}
    let second_hash=message_hash(derived.as_slice(),out.as_slice());let right=sub128(sub128(middle,header),second_hash);
    i=0;while i<16{out.push(right[i]);i+=1;}Ok(out)
}
pub fn encrypt_adiantum_xchacha12_aes(raw_key:&[u8],tweak:[u8;32],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>raw_key.len()==32 && 16<=input.len()<=MAX_ADIANTUM_BYTES && v.len()==input.len()
        && adiantum_result_is_standard(raw_key@,tweak@,input@,v@,false),Err(_)=>true},
{apply(raw_key,tweak,input,false)}
pub fn decrypt_adiantum_xchacha12_aes(raw_key:&[u8],tweak:[u8;32],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>raw_key.len()==32 && 16<=input.len()<=MAX_ADIANTUM_BYTES && v.len()==input.len()
        && adiantum_result_is_standard(raw_key@,tweak@,input@,v@,true),Err(_)=>true},
{apply(raw_key,tweak,input,true)}

}
