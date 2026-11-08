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

#[verifier::opaque]
spec fn add32(a:u32,b:u32) -> u32 {((a as nat+b as nat)%4294967296) as u32}
spec fn rotate(x:u32,count:u32) -> u32 {let n=count%32;if n==0{x}else{(x<<n)|(x>>(32-n))}}
#[verifier::opaque]
spec fn little(raw:Seq<u8>,at:nat,n:nat) -> nat
    decreases n
{
    if n==0 {0}else{little(raw,at,(n-1) as nat)+(raw[(at+n-1) as int] as nat)*pow256((n-1) as nat)}
}
#[verifier::opaque]
spec fn pow256(n:nat) -> nat decreases n {if n==0{1}else{256*pow256((n-1) as nat)}}
spec fn word32(value:u32) -> Seq<u8> {
    Seq::new(4,|i:int| (value>>((i*8) as u32)) as u8)
}
spec fn word64(value:u64) -> Seq<u8> {
    Seq::new(8,|i:int| (value>>((i*8) as u32)) as u8)
}
spec fn replace(raw:Seq<u8>,at:nat,value:Seq<u8>) -> Seq<u8> {
    Seq::new(raw.len(),|i:int| if at<=i<at+value.len() {value[i-at as int]}else{raw[i]})
}
spec fn initial_state(key:Seq<u8>,iv:Seq<u8>) -> Seq<u32> {
    seq![0x61707865u32,0x3320646eu32,0x79622d32u32,0x6b206574u32]
        +Seq::new(8,|i:int|little(key,(i*4) as nat,4) as u32)
        +Seq::new(4,|i:int|little(iv,(i*4) as nat,4) as u32)
}
#[verifier::opaque]
spec fn quarter_reference(s:Seq<u32>,a:int,b:int,c:int,d:int) -> Seq<u32> {
    let s=s.update(a,add32(s[a],s[b]));let s=s.update(d,rotate(s[d]^s[a],16));
    let s=s.update(c,add32(s[c],s[d]));let s=s.update(b,rotate(s[b]^s[c],12));
    let s=s.update(a,add32(s[a],s[b]));let s=s.update(d,rotate(s[d]^s[a],8));
    let s=s.update(c,add32(s[c],s[d]));s.update(b,rotate(s[b]^s[c],7))
}
#[verifier::opaque]
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
spec fn stream_subkey(raw_key:Seq<u8>,iv:Seq<u8>) -> Seq<u8> {
    let h=permuted(initial_state(raw_key,iv.take(16)),6);
    Seq::new(32,|i:int| {
        let w=if i<16 {h[i/4]}else{h[12+(i-16)/4]};
        (w>>(((i%4)*8) as u32)) as u8
    })
}
spec fn stream_state(raw_key:Seq<u8>,iv:Seq<u8>) -> Seq<u32> {
    initial_state(stream_subkey(raw_key,iv),iv.subrange(24,32)+iv.subrange(16,24))
}
#[verifier::opaque]
spec fn stream_block(state:Seq<u32>) -> Seq<u8> {
    let working=permuted(state,6);
    Seq::new(64,|i:int| ((add32(working[i/4],state[i/4]))>>(((i%4)*8) as u32)) as u8)
}
#[verifier::opaque]
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
#[verifier::opaque]
spec fn poly_blocks(r:nat,input:Seq<u8>,n:nat) -> nat
    decreases n
{
    if n==0 {0}else{((poly_blocks(r,input,(n-1) as nat)+little(input,((n-1)*16) as nat,16)
        +double_word_modulus())*r)%p130()}
}
spec fn encoded128(n:nat) -> Seq<u8> {
    let reduced=(n%double_word_modulus()) as u128;
    Seq::new(16,|i:int| (reduced>>((i*8) as u32)) as u8)
}
pub closed spec fn poly1305_reference(raw_r:Seq<u8>,input:Seq<u8>) -> Seq<u8> {
    encoded128(poly_blocks(clamp(raw_r),input,input.len()/16))
}
spec fn nh_word(input:Seq<u8>,chunk:nat,unit:nat,word:nat) -> u32 {
    let at=chunk*1024+unit*16+word*4;
    let raw=Seq::new(4,|i:int| if (at as int+i)<input.len() {input[at as int+i]}else{0u8});
    little(raw,0,4) as u32
}
#[verifier::opaque]
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
#[verifier::opaque]
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
    exists|cipher:AesKey| #![trigger cipher.aes_schedule()] !cipher.aes_retired() && cipher.aes_round_count()==14
        && cipher.aes_schedule().take(240)==crate::aes::expanded_key_reference(adiantum_derived_reference(raw).take(32),52)
        && output==adiantum_reference(&cipher,raw,tweak,input,decrypt)
}

fn wrapping_add32(a:u32,b:u32) -> (r:u32)
    ensures r==add32(a,b),
{proof {reveal(add32);}a.wrapping_add(b)}
proof fn add32_zero(a:u32)
    ensures add32(a,0)==a,
{reveal(add32);}
proof fn pow256_zero()
    ensures pow256(0)==1,
{reveal(pow256);}
proof fn pow256_step(n:nat)
    ensures pow256(n+1)==256*pow256(n),
{reveal(pow256);}
proof fn pow256_add(a:nat,b:nat)
    ensures pow256(a+b)==pow256(a)*pow256(b),
    decreases b,
{
    if b==0 {pow256_zero();}
    else {
        pow256_add(a,(b-1) as nat);
        pow256_step((a+b-1) as nat);pow256_step((b-1) as nat);
        vstd::arithmetic::mul::lemma_mul_is_associative(256,pow256(a) as int,pow256((b-1) as nat) as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(256,pow256(a) as int);
        vstd::arithmetic::mul::lemma_mul_is_associative(pow256(a) as int,256,pow256((b-1) as nat) as int);
    }
}
proof fn little_zero(raw:Seq<u8>,at:nat)
    ensures little(raw,at,0)==0,
{reveal(little);}
proof fn little_step(raw:Seq<u8>,at:nat,n:nat)
    requires at+n<raw.len(),
    ensures little(raw,at,n+1)==little(raw,at,n)+raw[(at+n) as int] as nat*pow256(n),
{reveal(little);}
proof fn pow256_small()
    ensures pow256(0)==1,pow256(1)==256,pow256(2)==65536,
        pow256(3)==16777216,pow256(4)==4294967296,pow256(8)==word_modulus(),
{
    reveal(pow256);
    assert(pow256(0)==1) by(compute);
    assert(pow256(1)==256) by(compute);
    assert(pow256(2)==65536) by(compute);
    assert(pow256(3)==16777216) by(compute);
    assert(pow256(4)==4294967296) by(compute);
    assert(pow256(8)==word_modulus()) by(compute);
}
proof fn little_four(raw:Seq<u8>,at:nat)
    requires at+4<=raw.len(),
    ensures little(raw,at,4)==raw[at as int] as nat+raw[at as int+1] as nat*256
        +raw[at as int+2] as nat*65536+raw[at as int+3] as nat*16777216,
{
    pow256_small();little_zero(raw,at);
    little_step(raw,at,0);little_step(raw,at,1);little_step(raw,at,2);little_step(raw,at,3);
}
proof fn little_concat(raw:Seq<u8>,at:nat,left:nat,right:nat)
    requires at+left+right<=raw.len(),
    ensures little(raw,at,left+right)==little(raw,at,left)+pow256(left)*little(raw,at+left,right),
    decreases right,
{
    if right==0 {little_zero(raw,at+left);}
    else {
        let n=(right-1) as nat;
        little_concat(raw,at,left,n);
        little_step(raw,at,left+n);little_step(raw,at+left,n);pow256_add(left,n);
        assert(little(raw,at,left+right)==little(raw,at,left)+pow256(left)*little(raw,at+left,right))
            by(nonlinear_arith)
            requires little(raw,at,left+n)==little(raw,at,left)+pow256(left)*little(raw,at+left,n),
                little(raw,at,left+n+1)==little(raw,at,left+n)+raw[(at+left+n) as int] as nat*pow256(left+n),
                little(raw,at+left,n+1)==little(raw,at+left,n)+raw[(at+left+n) as int] as nat*pow256(n),
                pow256(left+n)==pow256(left)*pow256(n),right==n+1;
    }
}
proof fn decode_four(b0:u8,b1:u8,b2:u8,b3:u8)
    ensures (((b0 as u32)|((b1 as u32)<<8)|((b2 as u32)<<16)|((b3 as u32)<<24)) as nat)
        ==b0 as nat+b1 as nat*256+b2 as nat*65536+b3 as nat*16777216,
{
    assert((((b0 as u32)|((b1 as u32)<<8)|((b2 as u32)<<16)|((b3 as u32)<<24)) as u64)
        ==b0 as u64+b1 as u64*256+b2 as u64*65536+b3 as u64*16777216) by(bit_vector);
}
proof fn decode_pair(lo:u32,hi:u32)
    ensures (((lo as u64)|((hi as u64)<<32)) as nat)==lo as nat+hi as nat*4294967296,
{
    assert((((lo as u64)|((hi as u64)<<32)) as u128)
        ==lo as u128+hi as u128*4294967296) by(bit_vector);
}
proof fn permuted_zero(state:Seq<u32>)
    ensures permuted(state,0)==state,
{reveal(permuted);}
proof fn permuted_step(state:Seq<u32>,n:nat)
    ensures permuted(state,n+1)==double_round(permuted(state,n)),
{reveal(permuted);}
proof fn quarter_length(state:Seq<u32>,a:int,b:int,c:int,d:int)
    requires state.len()==16,0<=a<16,0<=b<16,0<=c<16,0<=d<16,
    ensures quarter_reference(state,a,b,c,d).len()==16,
{reveal(quarter_reference);}
proof fn double_round_length(state:Seq<u32>)
    requires state.len()==16,
    ensures double_round(state).len()==16,
{
    reveal(double_round);
    quarter_length(state,0,4,8,12);let s=quarter_reference(state,0,4,8,12);
    quarter_length(s,1,5,9,13);let s=quarter_reference(s,1,5,9,13);
    quarter_length(s,2,6,10,14);let s=quarter_reference(s,2,6,10,14);
    quarter_length(s,3,7,11,15);let s=quarter_reference(s,3,7,11,15);
    quarter_length(s,0,5,10,15);let s=quarter_reference(s,0,5,10,15);
    quarter_length(s,1,6,11,12);let s=quarter_reference(s,1,6,11,12);
    quarter_length(s,2,7,8,13);let s=quarter_reference(s,2,7,8,13);
    quarter_length(s,3,4,9,14);
}
proof fn permuted_length(state:Seq<u32>,n:nat)
    requires state.len()==16,
    ensures permuted(state,n).len()==16,
    decreases n,
{
    if n==0 {permuted_zero(state);}
    else {
        permuted_length(state,(n-1) as nat);
        permuted_step(state,(n-1) as nat);
        double_round_length(permuted(state,(n-1) as nat));
    }
}
proof fn stream_block_length(state:Seq<u32>)
    ensures stream_block(state).len()==64,
{reveal(stream_block);}
proof fn replace_prefix(raw:Seq<u8>,target:Seq<u8>,at:nat,value:Seq<u8>)
    requires at+value.len()<=raw.len(),at+value.len()<=target.len(),
        raw.take(at as int)==target.take(at as int),
        value==target.subrange(at as int,(at+value.len()) as int),
    ensures replace(raw,at,value).take((at+value.len()) as int)
        ==target.take((at+value.len()) as int),
{
    assert(replace(raw,at,value).take((at+value.len()) as int)
        =~=target.take((at+value.len()) as int));
}
proof fn full_prefix(left:Seq<u8>,right:Seq<u8>,n:nat)
    requires left.len()==n,right.len()==n,left.take(n as int)==right.take(n as int),
    ensures left==right,
{
    assert(left.take(n as int) =~= left);
    assert(right.take(n as int) =~= right);
}
proof fn push_prefix(before:Seq<u8>,target:Seq<u8>,at:nat,byte:u8)
    requires at<target.len(),before==target.take(at as int),byte==target[at as int],
    ensures before.push(byte)==target.take(at as int+1),
{
    assert(before.push(byte) =~= target.take(at as int+1));
}
proof fn stream_block_word(state:Seq<u32>,i:nat)
    requires state.len()==16,i<16,
    ensures stream_block(state).len()==64,
        stream_block(state).subrange((i*4) as int,(i*4+4) as int)
            ==word32(add32(permuted(state,6)[i as int],state[i as int])),
{
    reveal(stream_block);
    permuted_length(state,6);
    assert(stream_block(state).subrange((i*4) as int,(i*4+4) as int)
        =~=word32(add32(permuted(state,6)[i as int],state[i as int])));
}
proof fn xchacha_length(raw:Seq<u8>,iv:Seq<u8>,input:Seq<u8>)
    ensures xchacha12_reference(raw,iv,input).len()==input.len(),
{reveal(xchacha12_reference);}
proof fn xchacha_block_byte(raw:Seq<u8>,iv:Seq<u8>,input:Seq<u8>,at:nat,i:nat)
    requires at%64==0,i<64,at+i<input.len(),
    ensures xchacha12_reference(raw,iv,input)[(at+i) as int]
        ==input[(at+i) as int]^stream_block(stream_state(raw,iv).update(
            12,add32(stream_state(raw,iv)[12],(at/64) as u32)))[i as int],
{
    reveal(xchacha12_reference);reveal(stream_block);
    assert((at+i)/64==at/64);
    assert((at+i)%64==i);
    assert((at+i)%4==i%4);
}
proof fn advance_chunk(at:nat,take:nat)
    requires at%64==0,1<=take<=64,
    ensures (at+take+63)/64==at/64+1,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(at as int,64);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_div(
        at as int+take as int+63,64,(at/64) as int+1,take as int-1);
}
proof fn counter_successor(seed:u32,n:u32)
    requires n<u32::MAX,
    ensures add32(add32(seed,n),1)==add32(seed,(n+1) as u32),
{reveal(add32);}
fn rotl(x:u32,count:u32) -> (r:u32) ensures r==rotate(x,count) {let n=count%32;if n==0{x}else{(x<<n)|(x>>(32-n))}}
fn le32(raw:&[u8],at:usize) -> (r:u32)
    requires at<=raw.len(),4<=raw.len()-at,
    ensures r==little(raw@,at as nat,4),
{
    proof {
        little_four(raw@,at as nat);
        decode_four(raw@[at as int],raw@[at as int+1],raw@[at as int+2],raw@[at as int+3]);
    }
    (raw[at] as u32)|((raw[at+1] as u32)<<8)|((raw[at+2] as u32)<<16)|((raw[at+3] as u32)<<24)
}
fn le64(raw:&[u8],at:usize) -> (r:u64)
    requires at<=raw.len(),8<=raw.len()-at,
    ensures r==little(raw@,at as nat,8),
{
    let lo=le32(raw,at);let hi=le32(raw,at+4);
    proof {
        pow256_small();little_concat(raw@,at as nat,4,4);
        decode_pair(lo,hi);
    }
    (lo as u64)|((hi as u64)<<32)
}
proof fn little16_split(raw:Seq<u8>,at:nat)
    requires at+16<=raw.len(),
    ensures little(raw,at,16)==little(raw,at,8)+little(raw,at+8,8)*word_modulus(),
{
    pow256_small();little_concat(raw,at,8,8);
    vstd::arithmetic::mul::lemma_mul_is_commutative(word_modulus() as int,little(raw,at+8,8) as int);
}
fn put32(out:&mut [u8],at:usize,value:u32)
    requires at<=old(out).len(),4<=old(out).len()-at,
    ensures final(out).len()==old(out).len(),final(out)@==replace(old(out)@,at as nat,word32(value)),
{
    let ghost before=out@;let mut i=0usize;
    while i<4
        invariant i<=4,at<=out.len(),4<=out.len()-at,out.len()==before.len(),
            forall|j:int| #![trigger out@[j]] 0<=j<out.len() ==> out@[j]
                ==if at<=j<at+i {word32(value)[j-at as int]}else{before[j]},
        decreases 4-i,
    {out[at+i]=(value>>(8*i)) as u8;i+=1;}
}
fn put64(out:&mut [u8],at:usize,value:u64)
    requires at<=old(out).len(),8<=old(out).len()-at,
    ensures final(out).len()==old(out).len(),final(out)@==replace(old(out)@,at as nat,word64(value)),
{
    let ghost before=out@;let mut i=0usize;
    while i<8
        invariant i<=8,at<=out.len(),8<=out.len()-at,out.len()==before.len(),
            forall|j:int| #![trigger out@[j]] 0<=j<out.len() ==> out@[j]
                ==if at<=j<at+i {word64(value)[j-at as int]}else{before[j]},
        decreases 8-i,
    {out[at+i]=(value>>(8*i)) as u8;i+=1;}
}
fn copy16(raw:&[u8],at:usize) -> (r:[u8;16])
    requires at<=raw.len(),16<=raw.len()-at,
    ensures r@==raw@.subrange(at as int,at as int+16),
{
    let mut out=[0u8;16];let mut i=0usize;
    while i<16
        invariant i<=16,at<=raw.len(),16<=raw.len()-at,
            forall|j:int| #![trigger out@[j]] 0<=j<i ==> out@[j]==raw@[at as int+j],
        decreases 16-i,
    {out[i]=raw[at+i];i+=1;}out
}
fn quarter(s:&mut [u32;16],a:usize,b:usize,c:usize,d:usize)
    requires a<16,b<16,c<16,d<16,
    ensures final(s)@==quarter_reference(old(s)@,a as int,b as int,c as int,d as int),
{
    proof {reveal(quarter_reference);}
    s[a]=wrapping_add32(s[a],s[b]);s[d]=rotl(s[d]^s[a],16);
    s[c]=wrapping_add32(s[c],s[d]);s[b]=rotl(s[b]^s[c],12);
    s[a]=wrapping_add32(s[a],s[b]);s[d]=rotl(s[d]^s[a],8);
    s[c]=wrapping_add32(s[c],s[d]);s[b]=rotl(s[b]^s[c],7);
}
fn permute(s:&mut [u32;16]) ensures final(s)@==permuted(old(s)@,6), {
    proof {permuted_zero(s@);}
    let mut i=0usize;while i<6 invariant i<=6,s@==permuted(old(s)@,i as nat), decreases 6-i, {
        proof {permuted_step(old(s)@,i as nat);reveal(double_round);}
        quarter(s,0,4,8,12);quarter(s,1,5,9,13);quarter(s,2,6,10,14);quarter(s,3,7,11,15);
        quarter(s,0,5,10,15);quarter(s,1,6,11,12);quarter(s,2,7,8,13);quarter(s,3,4,9,14);i+=1;
    }
}
fn initial(key:&[u8],iv:&[u8]) -> (r:[u32;16]) requires key.len()==32,iv.len()==16, ensures r@==initial_state(key@,iv@), {
    let mut s=[0u32;16];s[0]=0x61707865;s[1]=0x3320646e;s[2]=0x79622d32;s[3]=0x6b206574;
    let mut i=0usize;
    while i<8
        invariant i<=8,key.len()==32,iv.len()==16,
            forall|j:int| #![trigger s@[j]] 0<=j<16 ==> s@[j]==
                if j<4 {initial_state(key@,iv@)[j]}
                else if j<4+i {initial_state(key@,iv@)[j]}else{0u32},
        decreases 8-i,
    {s[4+i]=le32(key,i*4);i+=1;}
    i=0;
    while i<4
        invariant i<=4,key.len()==32,iv.len()==16,
            forall|j:int| #![trigger s@[j]] 0<=j<16 ==> s@[j]==
                if j<12+i {initial_state(key@,iv@)[j]}else{0u32},
        decreases 4-i,
    {s[12+i]=le32(iv,i*4);i+=1;}s
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
    while i<4
        invariant i<=4,h@==permuted(initial_state(raw_key@,iv@.take(16)),6),
            forall|j:int| #![trigger subkey@[j]] 0<=j<32 ==> subkey@[j]==
                if j%16<i*4 {stream_subkey(raw_key@,iv@)[j]}else{0u8},
        decreases 4-i,
    {put32(&mut subkey,i*4,h[i]);put32(&mut subkey,16+i*4,h[12+i]);i+=1;}
    proof {assert(subkey@ =~= stream_subkey(raw_key@,iv@));}
    let mut real_iv=[0u8;16];i=0;
    while i<8
        invariant i<=8,
            forall|j:int| #![trigger real_iv@[j]] 0<=j<16 ==> real_iv@[j]==
                if j%8<i {(iv@.subrange(24,32)+iv@.subrange(16,24))[j]}else{0u8},
        decreases 8-i,
    {real_iv[i]=iv[24+i];real_iv[8+i]=iv[16+i];i+=1;}
    proof {assert(real_iv@ =~= iv@.subrange(24,32)+iv@.subrange(16,24));}
    let mut state=initial(&subkey,&real_iv);let mut at=0usize;let mut out=Vec::new();
    let ghost seed=stream_state(raw_key@,iv@);
    proof {
        assert(state@==seed);
        assert(seed.len()==16);
        xchacha_length(raw_key@,iv@,input@);
        add32_zero(seed[12]);
        assert(seed.update(12,add32(seed[12],0)) =~= seed);
    }
    while at<input.len()
        invariant at<=input.len()<=MAX_ADIANTUM_BYTES,out.len()==at,seed.len()==16,
            seed==stream_state(raw_key@,iv@),
            at%64==0 || at==input.len(),
            out@==xchacha12_reference(raw_key@,iv@,input@).take(at as int),
            state@==seed.update(12,add32(seed[12],((at+63)/64) as u32)),
        decreases input.len()-at,
    {
        let mut working=state;permute(&mut working);let mut stream=[0u8;64];i=0;
        proof {stream_block_length(state@);}
        while i<16
            invariant i<=16,working@==permuted(state@,6),stream_block(state@).len()==64,
                stream@.take((i*4) as int)==stream_block(state@).take((i*4) as int),
                at<input.len()<=MAX_ADIANTUM_BYTES,at%64==0,seed.len()==16,
                seed==stream_state(raw_key@,iv@),
                out.len()==at,out@==xchacha12_reference(raw_key@,iv@,input@).take(at as int),
                state@==seed.update(12,add32(seed[12],(at/64) as u32)),
            decreases 16-i,
        {
            proof {
                stream_block_word(state@,i as nat);
                replace_prefix(stream@,stream_block(state@),(i*4) as nat,
                    word32(add32(working@[i as int],state@[i as int])));
            }
            put32(&mut stream,i*4,wrapping_add32(working[i],state[i]));i+=1;
        }
        proof {
            stream_block_length(state@);
            assert(i==16);
            assert(stream@.take(64)==stream_block(state@).take(64));
            full_prefix(stream@,stream_block(state@),64);
        }
        let left=input.len()-at;let take=if left<64{left}else{64};i=0;
        while i<take
            invariant i<=take<=64,0<take,at+take<=input.len()<=MAX_ADIANTUM_BYTES,at%64==0,seed.len()==16,
                seed==stream_state(raw_key@,iv@),
                stream@==stream_block(state@),
                state@==seed.update(12,add32(seed[12],(at/64) as u32)),
                out.len()==at+i,out@==xchacha12_reference(raw_key@,iv@,input@).take((at+i) as int),
            decreases take-i,
        {
            proof {
                xchacha_length(raw_key@,iv@,input@);
                xchacha_block_byte(raw_key@,iv@,input@,at as nat,i as nat);
                assert(state@==stream_state(raw_key@,iv@).update(
                    12,add32(stream_state(raw_key@,iv@)[12],(at/64) as u32)));
                assert(stream@[i as int]==stream_block(stream_state(raw_key@,iv@).update(
                    12,add32(stream_state(raw_key@,iv@)[12],(at/64) as u32)))[i as int]);
                push_prefix(out@,xchacha12_reference(raw_key@,iv@,input@),(at+i) as nat,input@[at as int+i as int]^stream@[i as int]);
            }
            out.push(input[at+i]^stream[i]);i+=1;
        }
        proof {
            advance_chunk(at as nat,take as nat);
            counter_successor(seed[12],(at/64) as u32);
        }
        state[12]=wrapping_add32(state[12],1);at+=take;
    }
    Ok(out)
}

// Canonical arithmetic in GF(2^130-5), represented as three little-endian
// limbs. Fixed 128-step multiplication avoids native wide multiplication.

proof fn field_constants()
    ensures
        word_modulus()==(u64::MAX as nat)+1,
        word_modulus()==((1u128<<64) as nat),
        word_modulus()>16,
        double_word_modulus()==word_modulus()*word_modulus(),
        double_word_modulus()==(u128::MAX as nat)+1,
        p130()==4*double_word_modulus()-5,
        0<p130(),
        3*double_word_modulus()<p130(),
        2*word_modulus()-1<=u128::MAX,
{
    assert(((1u128<<64)-1)==u64::MAX as u128) by(bit_vector);
    assert((u64::MAX as u128)*2+1<=u128::MAX) by(bit_vector);
}

proof fn field_canonical_high(a:Seq<u64>)
    requires canonical(a),
    ensures a.len()==3,a[2]<=3,
{
    field_constants();
    assert(limb_value(a)>=a[2] as nat*double_word_modulus()) by(nonlinear_arith);
    assert(a[2]<4) by(nonlinear_arith)
        requires limb_value(a)<4*double_word_modulus(),
            limb_value(a)>=a[2] as nat*double_word_modulus(),
            double_word_modulus()>0;
}

proof fn field_split128(x:u128)
    ensures (x>>64)<=u64::MAX,
        x as nat==(x as u64) as nat+word_modulus()*((x>>64) as nat),
{
    field_constants();
    vstd::arithmetic::power2::lemma2_to64_rest();
    vstd::bits::lemma_low_bits_mask_values();
    vstd::bits::lemma_u128_shr_is_div(x,64u128);
    vstd::bits::lemma_u128_low_bits_mask_is_mod(x,64);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int,word_modulus() as int);
    assert((x>>64)<=u64::MAX as u128) by(bit_vector);
    assert((x as u64 as u128)==(x&(u64::MAX as u128))) by(bit_vector);
}
proof fn field_join128(low:u64,high:u64)
    ensures (((low as u128)|((high as u128)<<64)) as nat)
        ==low as nat+(high as nat)*word_modulus(),
{
    let joined=(low as u128)|((high as u128)<<64);
    field_split128(joined);
    assert(joined as u64==low) by(bit_vector)
        requires joined==(low as u128)|((high as u128)<<64);
    assert((joined>>64)==high as u128) by(bit_vector)
        requires joined==(low as u128)|((high as u128)<<64);
    vstd::arithmetic::mul::lemma_mul_is_commutative(word_modulus() as int,high as int);
}

proof fn field_zero(value:Seq<u64>)
    requires value.len()==3,value[0]==0,value[1]==0,value[2]==0,
    ensures limb_value(value)==0,canonical(value),
{
    field_constants();reveal(limb_value);reveal(canonical);
}
proof fn field_message_pair(low:u64,high:u64)
    ensures canonical(seq![low,high,1u64]),
        limb_value(seq![low,high,1u64])==low as nat+high as nat*word_modulus()+double_word_modulus(),
{
    field_constants();field_join128(low,high);
    reveal(limb_value);reveal(canonical);
}
proof fn field_threshold(s:Seq<u64>)
    requires s.len()==3,
    ensures
        (s[2]>3 || (s[2]==3 && s[1]==u64::MAX && s[0]>=0xffff_ffff_ffff_fffbu64))
            ==(limb_value(s)>=p130()),
{
    field_constants();
    let w=word_modulus();
    let c=double_word_modulus();
    assert((0xffff_ffff_ffff_fffbu64 as nat)==w-5);
    if s[2]>3 {
        assert(limb_value(s)>=4*c) by(nonlinear_arith)
            requires limb_value(s)==s[0] as nat+s[1] as nat*w+s[2] as nat*c,
                s[2]>=4,c>0,w>0;
    } else if s[2]<3 {
        assert(limb_value(s)<3*c) by(nonlinear_arith)
            requires s[2]<=2,s[0]<w,s[1]<w,c==w*w,w>16,
                limb_value(s)==s[0] as nat+s[1] as nat*w+s[2] as nat*c;
    } else if s[1]<u64::MAX {
        assert(limb_value(s)<=4*c-w-1) by(nonlinear_arith)
            requires s[2]==3,s[1]<=w-2,s[0]<=w-1,c==w*w,w>16,
                limb_value(s)==s[0] as nat+s[1] as nat*w+s[2] as nat*c;
    } else {
        assert(s[1] as nat==w-1);
        assert(limb_value(s)==4*c-w+s[0] as nat) by(nonlinear_arith)
            requires s[2]==3,s[1] as nat==w-1,c==w*w,
                limb_value(s)==s[0] as nat+s[1] as nat*w+s[2] as nat*c;
    }
}

proof fn field_subtract_p(s:Seq<u64>,borrow0:u64,borrow1:u64,d:Seq<u64>)
    requires
        s.len()==3,d.len()==3,limb_value(s)>=p130(),
        borrow0==if s[0]<0xffff_ffff_ffff_fffbu64 {1u64}else{0u64},
        borrow1==if s[1]<u64::MAX || (s[1]==u64::MAX && borrow0!=0) {1u64}else{0u64},
        d[0]==vstd::wrapping::u64_specs::wrapping_sub(s[0],0xffff_ffff_ffff_fffbu64),
        d[1]==vstd::wrapping::u64_specs::wrapping_sub(
            vstd::wrapping::u64_specs::wrapping_sub(s[1],u64::MAX),borrow0),
        d[2]==vstd::wrapping::u64_specs::wrapping_sub(
            vstd::wrapping::u64_specs::wrapping_sub(s[2],3),borrow1),
    ensures limb_value(d)==limb_value(s)-p130(),
{
    field_constants();
    field_threshold(s);
    let w=word_modulus();
    let c=double_word_modulus();
    assert(borrow0==0 || borrow0==1);
    assert(borrow1==0 || borrow1==1);
    if s[0]<0xffff_ffff_ffff_fffbu64 {
        assert(borrow0==1);
        assert(d[0] as int==s[0] as int-(w as int-5)+w as int);
    } else {
        assert(borrow0==0);
        assert(d[0] as int==s[0] as int-(w as int-5));
    }
    assert(d[0] as int==s[0] as int-(w as int-5)+(borrow0 as int)*(w as int));

    if borrow0==0 {
        if s[1]==u64::MAX {
            assert(borrow1==0);
            assert(d[1]==0);
        } else {
            assert(borrow1==1);
            assert(d[1] as int==s[1] as int+1);
        }
    } else {
        assert(borrow0==1 && borrow1==1);
        if s[1]==u64::MAX {
            assert(d[1]==u64::MAX);
        } else {
            assert(d[1]==s[1]);
        }
    }
    assert(d[1] as int==s[1] as int-(w as int-1)-borrow0 as int
        +(borrow1 as int)*(w as int));

    if s[2]>3 {
        assert(s[2]>=3+borrow1);
    } else {
        assert(s[2]==3 && s[1]==u64::MAX && s[0]>=0xffff_ffff_ffff_fffbu64);
        assert(borrow0==0 && borrow1==0);
    }
    assert(d[2] as int==s[2] as int-3-borrow1 as int);
    assert(limb_value(d)==limb_value(s)-p130()) by(nonlinear_arith)
        requires
            d[0] as int==s[0] as int-(w as int-5)+(borrow0 as int)*(w as int),
            d[1] as int==s[1] as int-(w as int-1)-borrow0 as int+(borrow1 as int)*(w as int),
            d[2] as int==s[2] as int-3-borrow1 as int,
            c==w*w,
            p130()==4*c-5,
            limb_value(d)==d[0] as nat+d[1] as nat*w+d[2] as nat*c,
            limb_value(s)==s[0] as nat+s[1] as nat*w+s[2] as nat*c;
}

proof fn field_word_select(x:u64,y:u64,mask:u64,use_y:bool)
    requires mask==if use_y {u64::MAX}else{0u64},
    ensures ((x&!mask)|(y&mask))==if use_y {y}else{x},
{
    assert(((x&!mask)|(y&mask))==if use_y {y}else{x}) by(bit_vector)
        requires mask==if use_y {u64::MAX}else{0u64};
}

fn add_mod(a:[u64;3],b:[u64;3]) -> (r:[u64;3])
    requires canonical(a@),canonical(b@),
    ensures canonical(r@),limb_value(r@)==(limb_value(a@)+limb_value(b@))%p130(),
{
    proof {field_constants();field_canonical_high(a@);field_canonical_high(b@);}
    let lo=a[0] as u128+b[0] as u128;
    proof {
        field_split128(lo);
        assert((lo as nat)<=2*word_modulus()-2);
        assert((lo>>64)<=1) by(nonlinear_arith)
            requires lo as nat==(lo as u64) as nat+word_modulus()*((lo>>64) as nat),
                (lo as nat)<2*word_modulus(),word_modulus()>0;
    }
    let mid=a[1] as u128+b[1] as u128+(lo>>64);
    proof {
        field_split128(mid);
        assert((mid as nat)<=2*word_modulus()-1);
        assert((mid>>64)<=1) by(nonlinear_arith)
            requires mid as nat==(mid as u64) as nat+word_modulus()*((mid>>64) as nat),
                (mid as nat)<2*word_modulus(),word_modulus()>0;
    }
    let top=a[2]+b[2]+(mid>>64) as u64;
    let sum=[lo as u64,mid as u64,top];
    proof {
        assert(top<=7);
        assert(limb_value(sum@)==limb_value(a@)+limb_value(b@)) by(nonlinear_arith)
            requires
                lo as nat==a[0] as nat+b[0] as nat,
                lo as nat==(lo as u64) as nat+word_modulus()*((lo>>64) as nat),
                mid as nat==a[1] as nat+b[1] as nat+(lo>>64) as nat,
                mid as nat==(mid as u64) as nat+word_modulus()*((mid>>64) as nat),
                top as nat==a[2] as nat+b[2] as nat+(mid>>64) as nat,
                double_word_modulus()==word_modulus()*word_modulus(),
                limb_value(sum@)==(lo as u64) as nat+(mid as u64) as nat*word_modulus()+top as nat*double_word_modulus(),
                limb_value(a@)==a[0] as nat+a[1] as nat*word_modulus()+a[2] as nat*double_word_modulus(),
                limb_value(b@)==b[0] as nat+b[1] as nat*word_modulus()+b[2] as nat*double_word_modulus();
        assert(limb_value(sum@)<2*p130());
        field_threshold(sum@);
    }
    let p0=0xffff_ffff_ffff_fffbu64;
    let borrow0=if sum[0]<p0{1u64}else{0u64};
    let borrow1=if sum[1]<u64::MAX || (sum[1]==u64::MAX && borrow0!=0){1u64}else{0u64};
    let difference=[sum[0].wrapping_sub(p0),sum[1].wrapping_sub(u64::MAX).wrapping_sub(borrow0),
        sum[2].wrapping_sub(3).wrapping_sub(borrow1)];
    let reduce=sum[2]>3 || (sum[2]==3 && sum[1]==u64::MAX && sum[0]>=p0);
    let mask=0u64.wrapping_sub(if reduce{1}else{0});
    let result=[sum[0]&!mask|difference[0]&mask,sum[1]&!mask|difference[1]&mask,sum[2]&!mask|difference[2]&mask];
    proof {
        assert(mask==if reduce {u64::MAX}else{0u64});
        field_word_select(sum[0],difference[0],mask,reduce);
        field_word_select(sum[1],difference[1],mask,reduce);
        field_word_select(sum[2],difference[2],mask,reduce);
        if reduce {
            assert(result@ =~= difference@);
            field_subtract_p(sum@,borrow0,borrow1,difference@);
            assert(0<=limb_value(result@)<p130());
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_mod(
                limb_value(sum@) as int,p130() as int,1,limb_value(result@) as int);
        } else {
            assert(result@ =~= sum@);
            assert(limb_value(sum@)<p130());
            vstd::arithmetic::div_mod::lemma_small_mod(limb_value(sum@),p130());
        }
    }
    result
}

spec fn remaining_multiplier(r:Seq<u64>,steps:nat) -> u128 {
    if steps>=128 {0u128}else{((r[0] as u128)|((r[1] as u128)<<64))>>(steps as u32)}
}

proof fn field_remaining_step(r:Seq<u64>,steps:nat)
    requires r.len()==2,steps<128,
    ensures
        remaining_multiplier(r,steps) as nat
            ==2*(remaining_multiplier(r,steps+1) as nat)
                +(((r[(steps/64) as int]>>((steps%64) as u32))&1) as nat),
        ((r[(steps/64) as int]>>((steps%64) as u32))&1)<=1,
{
    let low=r[0];let high=r[1];let n=steps as u32;
    let full=(low as u128)|((high as u128)<<64);
    let current=remaining_multiplier(r,steps);
    let next=remaining_multiplier(r,steps+1);
    let selected=(r[(steps/64) as int]>>((steps%64) as u32))&1;
    assert(current==(full>>n));
    if steps<64 {
        assert(steps/64==0 && steps%64==steps);
        assert(((low>>(n%64))&1) as u128==((full>>n)&1)) by(bit_vector)
            requires n<64,full==(low as u128)|((high as u128)<<64);
    } else {
        assert(steps/64==1 && steps%64==steps-64);
        assert(((high>>(n%64))&1) as u128==((full>>n)&1)) by(bit_vector)
            requires 64<=n<128,full==(low as u128)|((high as u128)<<64);
    }
    assert(selected as u128==(current&1));
    assert((current&1)==current%2) by(bit_vector);
    assert((current&1)<=1) by(bit_vector);
    if steps<127 {
        assert((full>>(n+1))==((full>>n)>>1)) by(bit_vector)
            requires n<127;
        assert(next==(current>>1));
    } else {
        assert(steps==127 && next==0);
        assert((full>>127)>>1==0) by(bit_vector);
        assert(next==(current>>1));
    }
    vstd::arithmetic::power2::lemma2_to64();
    vstd::bits::lemma_u128_shr_is_div(current,1u128);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(current as int,2);
}

proof fn field_residual_step(o:nat,a:nat,q:nat,bit:nat)
    ensures
        (((o+bit*a)%p130())+((2*a)%p130())*q)%p130()
            ==(o+a*(2*q+bit))%p130(),
{
    field_constants();
    let p=p130() as int;
    let u=(o+bit*a) as int;
    let v=(((2*a)%p130())*q) as int;
    let w=(2*a*q) as int;
    vstd::arithmetic::div_mod::lemma_add_mod_noop_right(v,u,p);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_left((2*a) as int,q as int,p);
    vstd::arithmetic::div_mod::lemma_add_mod_noop_right(u,v,p);
    vstd::arithmetic::div_mod::lemma_add_mod_noop_right(u,w,p);
    assert(u+w==(o+a*(2*q+bit)) as int) by(nonlinear_arith)
        requires u==(o+bit*a) as int,w==(2*a*q) as int;
}

proof fn remaining_zero(r:Seq<u64>)
    requires r.len()==2,
    ensures remaining_multiplier(r,0) as nat==r[0] as nat+r[1] as nat*word_modulus(),
{
    field_join128(r[0],r[1]);
    let value=(r[0] as u128)|((r[1] as u128)<<64);
    assert((value>>0)==value) by(bit_vector);
    assert(remaining_multiplier(r,0)==value);
}
fn mul_mod(mut a:[u64;3],r:[u64;2]) -> (result:[u64;3])
    requires canonical(a@),
    ensures canonical(result@),limb_value(result@)==
        (limb_value(a@)*(r@[0] as nat+(r@[1] as nat)*word_modulus()))%p130(),
{
    let ghost original=limb_value(a@);
    let ghost multiplier=r@[0] as nat+(r@[1] as nat)*word_modulus();
    proof {
        field_constants();field_join128(r[0],r[1]);
        field_zero(seq![0u64,0u64,0u64]);
    }
    let mut out=[0u64;3];let mut i=0usize;
    proof {
        field_zero(out@);
        field_join128(r[0],r[1]);remaining_zero(r@);
        assert(remaining_multiplier(r@,0) as nat==multiplier);
    }
    while i<128
        invariant i<=128,canonical(a@),canonical(out@),
            (limb_value(out@)+limb_value(a@)*(remaining_multiplier(r@,i as nat) as nat))%p130()
                ==(original*multiplier)%p130(),
        decreases 128-i,
    {
        let ghost accumulator=limb_value(out@);
        let ghost multiplicand=limb_value(a@);
        let ghost previous=out@;
        let ghost residue=remaining_multiplier(r@,i as nat) as nat;
        let ghost next_residue=remaining_multiplier(r@,i as nat+1) as nat;
        proof {field_remaining_step(r@,i as nat);}
        let candidate=add_mod(out,a);
        let selected=(r[i/64]>>(i%64))&1;
        let mask=0u64.wrapping_sub(selected);
        proof {
            assert(selected==0 || selected==1);
            assert(mask==if selected==0 {0u64}else{u64::MAX});
            assert(residue==2*next_residue+selected as nat);
            assert((accumulator+multiplicand*residue)%p130()
                ==(original*multiplier)%p130());
        }
        let mut j=0usize;
        while j<3
            invariant j<=3,previous.len()==3,
                canonical(previous),canonical(candidate@),canonical(a@),
                limb_value(previous)==accumulator,limb_value(a@)==multiplicand,
                limb_value(candidate@)==(accumulator+multiplicand)%p130(),
                selected<=1,mask==if selected==0 {0u64}else{u64::MAX},
                residue==2*next_residue+selected as nat,
                (accumulator+multiplicand*residue)%p130()==(original*multiplier)%p130(),
                forall|k:int| #![trigger out@[k]] 0<=k<3 ==> out@[k]==
                    if k<j {previous[k]&!mask|candidate@[k]&mask}else{previous[k]},
            decreases 3-j,
        {
            out[j]=out[j]&!mask|candidate[j]&mask;j+=1;
        }
        proof {
            assert forall|k:int| #![trigger out@[k]] 0<=k<3 implies out@[k]==
                if selected==0 {previous[k]}else{candidate@[k]} by {
                field_word_select(previous[k],candidate@[k],mask,selected!=0);
            }
            if selected==0 {
                assert(out@ =~= previous);
                vstd::arithmetic::div_mod::lemma_small_mod(accumulator,p130());
            } else {
                assert(out@ =~= candidate@);
            }
            assert(canonical(out@));
            assert(limb_value(out@)==(accumulator+(selected as nat)*multiplicand)%p130());
        }
        a=add_mod(a,a);
        proof {
            assert(limb_value(a@)==(2*multiplicand)%p130());
            field_residual_step(accumulator,multiplicand,next_residue,selected as nat);
            assert(residue==2*next_residue+selected as nat);
        }
        i+=1;
    }
    proof {
        assert(i==128 && remaining_multiplier(r@,i as nat)==0);
        vstd::arithmetic::div_mod::lemma_small_mod(limb_value(out@),p130());
    }
    out
}
spec fn packed64(b0:u8,b1:u8,b2:u8,b3:u8,b4:u8,b5:u8,b6:u8,b7:u8) -> u64 {(b0 as u64)|((b1 as u64)<<8)|((b2 as u64)<<16)|((b3 as u64)<<24)|((b4 as u64)<<32)|((b5 as u64)<<40)|((b6 as u64)<<48)|((b7 as u64)<<56)}
proof fn packed64_halves(b0:u8,b1:u8,b2:u8,b3:u8,b4:u8,b5:u8,b6:u8,b7:u8)
    ensures packed64(b0,b1,b2,b3,b4,b5,b6,b7)==(((b0 as u32)|((b1 as u32)<<8)|((b2 as u32)<<16)|((b3 as u32)<<24)) as u64)|((((b4 as u32)|((b5 as u32)<<8)|((b6 as u32)<<16)|((b7 as u32)<<24)) as u64)<<32),
{
    assert(packed64(b0,b1,b2,b3,b4,b5,b6,b7)==(((b0 as u32)|((b1 as u32)<<8)|((b2 as u32)<<16)|((b3 as u32)<<24)) as u64)|((((b4 as u32)|((b5 as u32)<<8)|((b6 as u32)<<16)|((b7 as u32)<<24)) as u64)<<32)) by(bit_vector);
}
proof fn packed64_clamp(b0:u8,b1:u8,b2:u8,b3:u8,b4:u8,b5:u8,b6:u8,b7:u8,high:bool)
    ensures (if high {packed64(b0&252u8,b1,b2,b3&15u8,b4&252u8,b5,b6,b7&15u8)}else{packed64(b0,b1,b2,b3&15u8,b4&252u8,b5,b6,b7&15u8)})
        ==packed64(b0,b1,b2,b3,b4,b5,b6,b7)&(if high {0x0fff_fffc_0fff_fffcu64}else{0x0fff_fffc_0fff_ffffu64}),
{
    assert((if high {packed64(b0&252u8,b1,b2,b3&15u8,b4&252u8,b5,b6,b7&15u8)}else{packed64(b0,b1,b2,b3&15u8,b4&252u8,b5,b6,b7&15u8)})
        ==packed64(b0,b1,b2,b3,b4,b5,b6,b7)&(if high {0x0fff_fffc_0fff_fffcu64}else{0x0fff_fffc_0fff_ffffu64})) by(bit_vector);
}
proof fn little8_packed(raw:Seq<u8>,at:nat)
    requires at+8<=raw.len(),
    ensures little(raw,at,8)==packed64(raw[at as int],raw[at as int+1],raw[at as int+2],raw[at as int+3],
        raw[at as int+4],raw[at as int+5],raw[at as int+6],raw[at as int+7]) as nat,
        little(raw,at,8)<=u64::MAX,
{
    let b0=raw[at as int];let b1=raw[at as int+1];let b2=raw[at as int+2];let b3=raw[at as int+3];
    let b4=raw[at as int+4];let b5=raw[at as int+5];let b6=raw[at as int+6];let b7=raw[at as int+7];
    let low=(b0 as u32)|((b1 as u32)<<8)|((b2 as u32)<<16)|((b3 as u32)<<24);
    let high=(b4 as u32)|((b5 as u32)<<8)|((b6 as u32)<<16)|((b7 as u32)<<24);
    little_four(raw,at);little_four(raw,at+4);little_concat(raw,at,4,4);pow256_small();
    decode_four(b0,b1,b2,b3);decode_four(b4,b5,b6,b7);decode_pair(low,high);
    packed64_halves(b0,b1,b2,b3,b4,b5,b6,b7);
}
spec fn clamped_byte(raw:Seq<u8>,i:int) -> u8 {
    if i==3 || i==7 || i==11 || i==15 {raw[i]&15u8}
    else if i==4 || i==8 || i==12 {raw[i]&252u8}else{raw[i]}
}
proof fn little16_bound(raw:Seq<u8>,at:nat)
    requires at+16<=raw.len(),
    ensures little(raw,at,16)<double_word_modulus(),
{
    little8_packed(raw,at);little8_packed(raw,at+8);little16_split(raw,at);
    field_constants();field_join128(little(raw,at,8) as u64,little(raw,at+8,8) as u64);
}
proof fn clamp_word(raw:Seq<u8>,key:Seq<u8>,high:bool)
    requires raw.len()==16,key.len()==16,
        forall|i:int| #![trigger key[i]] 0<=i<16 ==> key[i]==clamped_byte(raw,i),
    ensures little(key,if high {8nat}else{0nat},8)
        ==((little(raw,if high {8nat}else{0nat},8) as u64)
            &(if high {0x0fff_fffc_0fff_fffcu64}else{0x0fff_fffc_0fff_ffffu64})) as nat,
{
    let at=if high {8nat}else{0nat};
    little8_packed(raw,at);little8_packed(key,at);
    packed64_clamp(raw[at as int],raw[at as int+1],raw[at as int+2],raw[at as int+3],
        raw[at as int+4],raw[at as int+5],raw[at as int+6],raw[at as int+7],high);
}
proof fn clamp_pair(low:u64,high:u64)
    ensures (((low as u128)|((high as u128)<<64))
        &((0x0fff_fffc_0fff_fffcu128<<64)|0x0fff_fffc_0fff_ffffu128))
        ==(((low&0x0fff_fffc_0fff_ffffu64) as u128)
            |(((high&0x0fff_fffc_0fff_fffcu64) as u128)<<64)),
{
    assert((((low as u128)|((high as u128)<<64))
        &((0x0fff_fffc_0fff_fffcu128<<64)|0x0fff_fffc_0fff_ffffu128))
        ==(((low&0x0fff_fffc_0fff_ffffu64) as u128)
            |(((high&0x0fff_fffc_0fff_fffcu64) as u128)<<64))) by(bit_vector);
}
proof fn clamp_wire(raw:Seq<u8>,key:Seq<u8>)
    requires raw.len()==16,key.len()==16,
        forall|i:int| #![trigger key[i]] 0<=i<16 ==> key[i]==clamped_byte(raw,i),
    ensures little(key,0,16)==clamp(raw),
{
    little8_packed(raw,0);little8_packed(raw,8);
    little16_split(raw,0);little16_split(key,0);
    clamp_word(raw,key,false);clamp_word(raw,key,true);
    let low=little(raw,0,8) as u64;let high=little(raw,8,8) as u64;
    field_join128(low,high);clamp_pair(low,high);
    field_join128(low&0x0fff_fffc_0fff_ffffu64,high&0x0fff_fffc_0fff_fffcu64);
}
proof fn zero_word64()
    ensures word64(0)==Seq::new(8,|i:int|0u8),
{
    assert forall|i:int| #![trigger word64(0)[i]] 0<=i<8 implies word64(0)[i]==0 by {
        let shift=(i*8) as u32;
        assert((0u64>>shift)==0u64) by(bit_vector);
    }
    assert(word64(0) =~=Seq::new(8,|i:int|0u8));
}
proof fn limb_low_mod(value:Seq<u64>)
    requires value.len()==3,
    ensures limb_value(value)%double_word_modulus()==value[0] as nat+value[1] as nat*word_modulus(),
{
    field_constants();field_join128(value[0],value[1]);
    let low=value[0] as nat+value[1] as nat*word_modulus();
    vstd::arithmetic::mul::lemma_mul_is_commutative(value[2] as int,double_word_modulus() as int);
    assert(limb_value(value)==double_word_modulus()*value[2] as nat+low);
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(value[2] as int,low as int,double_word_modulus() as int);
    vstd::arithmetic::div_mod::lemma_small_mod(low,double_word_modulus());
}
proof fn window_region(source:Seq<u8>,start:nat,width:nat,lo:nat,n:nat)
    requires start+width<=source.len(),lo+n<=width,
    ensures source.subrange(start as int,(start+width) as int)
            .subrange(lo as int,(lo+n) as int)
                ==source.subrange((start+lo) as int,(start+lo+n) as int),
        source.subrange(start as int,(start+width) as int).take(n as int)
            ==source.subrange(start as int,(start+n) as int),
{
    let view=source.subrange(start as int,(start+width) as int);
    assert(view.subrange(lo as int,(lo+n) as int)
        =~=source.subrange((start+lo) as int,(start+lo+n) as int));
    assert(view.take(n as int) =~=source.subrange(start as int,(start+n) as int));
}
proof fn concat_parts(left:Seq<u8>,right:Seq<u8>)
    ensures (left+right).subrange(0,left.len() as int)==left,
        (left+right).subrange(left.len() as int,(left.len()+right.len()) as int)==right,
{
    assert((left+right).subrange(0,left.len() as int) =~=left);
    assert((left+right).subrange(left.len() as int,(left.len()+right.len()) as int) =~=right);
}
proof fn encoded_pair_byte(low:u64,high:u64,index:u32)
    requires index<16,
    ensures ((((low as u128)|((high as u128)<<64))>>((index*8) as u32)) as u8)
        ==if index<8 {(low>>((index*8) as u32)) as u8}
            else{(high>>(((index-8)*8) as u32)) as u8},
{
    if index<8 {
        assert(((((low as u128)|((high as u128)<<64))>>((index*8) as u32)) as u8)
            ==(low>>((index*8) as u32)) as u8) by(bit_vector)
            requires index<8;
    }else{
        let shift=((index-8)*8) as u32;
        assert(0<=index-8<8);
        assert(shift<64);
        assert(((((low as u128)|((high as u128)<<64))>>((index*8) as u32)) as u8)
            ==(high>>shift) as u8) by(bit_vector)
            requires 8<=index<16,shift==(((index-8) as u32)*8) as u32;
    }
}
proof fn encoded_pair(low:u64,high:u64,value:nat)
    requires value%double_word_modulus()==low as nat+high as nat*word_modulus(),
    ensures encoded128(value)==word64(low)+word64(high),
{
    field_constants();field_join128(low,high);
    let packed=(low as u128)|((high as u128)<<64);
    assert(((value%double_word_modulus()) as u128)==packed);
    assert forall|i:int| #![trigger encoded128(value)[i]] 0<=i<16 implies
        encoded128(value)[i]==(word64(low)+word64(high))[i] by {
        encoded_pair_byte(low,high,i as u32);
    }
    assert(encoded128(value) =~= word64(low)+word64(high));
}
fn write_pair(low:u64,high:u64) -> (r:[u8;16])
    ensures r@==word64(low)+word64(high),
{
    let mut result=[0u8;16];put64(&mut result,0,low);put64(&mut result,8,high);
    proof {assert(result@ =~= word64(low)+word64(high));}
    result
}
proof fn wrap_add64(a:u64,b:u64)
    ensures vstd::wrapping::u64_specs::wrapping_add(a,b) as nat
        ==(a as nat+b as nat)%word_modulus(),
{
    field_constants();
    if (a as nat+b as nat)<=u64::MAX {
        vstd::arithmetic::div_mod::lemma_small_mod(a as nat+b as nat,word_modulus());
    }else{
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_mod(
            a as int+b as int,word_modulus() as int,1,a as int+b as int-word_modulus() as int);
    }
}
proof fn wrap_sub64(a:u64,b:u64)
    ensures vstd::wrapping::u64_specs::wrapping_sub(a,b) as int
        ==(a as int-b as int)%word_modulus() as int,
{
    field_constants();
    if a>=b {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_mod(
            a as int-b as int,word_modulus() as int,0,a as int-b as int);
    }else{
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_mod(
            a as int-b as int,word_modulus() as int,-1,a as int-b as int+word_modulus() as int);
    }
}
proof fn pair_add(a0:u64,a1:u64,b0:u64,b1:u64,low:u64,high:u64,carry:u64)
    requires low==vstd::wrapping::u64_specs::wrapping_add(a0,b0),
        carry==if low<a0 {1u64}else{0u64},
        high==vstd::wrapping::u64_specs::wrapping_add(
            vstd::wrapping::u64_specs::wrapping_add(a1,b1),carry),
    ensures low as nat+high as nat*word_modulus()
        ==(a0 as nat+a1 as nat*word_modulus()+b0 as nat+b1 as nat*word_modulus())%double_word_modulus(),
{
    field_constants();field_join128(low,high);
    wrap_add64(a0,b0);wrap_add64(a1,b1);
    wrap_add64(vstd::wrapping::u64_specs::wrapping_add(a1,b1),carry);
    if (a0 as nat+b0 as nat)<word_modulus() {assert(carry==0);}
    else {assert(carry==1);}
    assert(a0 as nat+b0 as nat==low as nat+carry as nat*word_modulus());
    let upper=a1 as nat+b1 as nat+carry as nat;
    vstd::arithmetic::div_mod::lemma_add_mod_noop_right(carry as int,a1 as int+b1 as int,word_modulus() as int);
    assert(high as nat==upper%word_modulus());
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(upper as int,word_modulus() as int);
    let result=low as nat+high as nat*word_modulus();
    let source=a0 as nat+a1 as nat*word_modulus()+b0 as nat+b1 as nat*word_modulus();
    assert(source==(upper/word_modulus())*double_word_modulus()+result) by(nonlinear_arith)
        requires a0 as nat+b0 as nat==low as nat+carry as nat*word_modulus(),
            upper==a1 as nat+b1 as nat+carry as nat,
            upper==word_modulus()*(upper/word_modulus())+high as nat,
            source==a0 as nat+a1 as nat*word_modulus()+b0 as nat+b1 as nat*word_modulus(),
            result==low as nat+high as nat*word_modulus(),double_word_modulus()==word_modulus()*word_modulus();
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_mod(
        source as int,double_word_modulus() as int,(upper/word_modulus()) as int,result as int);
}
proof fn pair_sub(a0:u64,a1:u64,b0:u64,b1:u64,low:u64,high:u64,borrow:u64)
    requires low==vstd::wrapping::u64_specs::wrapping_sub(a0,b0),
        borrow==if a0<b0 {1u64}else{0u64},
        high==vstd::wrapping::u64_specs::wrapping_sub(
            vstd::wrapping::u64_specs::wrapping_sub(a1,b1),borrow),
    ensures low as nat+high as nat*word_modulus()
        ==((a0 as int+a1 as int*word_modulus() as int+double_word_modulus() as int)
            -(b0 as int+b1 as int*word_modulus() as int))%double_word_modulus() as int,
{
    field_constants();field_join128(low,high);
    wrap_sub64(a0,b0);wrap_sub64(a1,b1);
    wrap_sub64(vstd::wrapping::u64_specs::wrapping_sub(a1,b1),borrow);
    assert(low as int==a0 as int-b0 as int+borrow as int*word_modulus() as int);
    let upper=a1 as int-b1 as int-borrow as int;
    vstd::arithmetic::div_mod::lemma_small_mod(borrow as nat,word_modulus());
    vstd::arithmetic::div_mod::lemma_sub_mod_noop(a1 as int-b1 as int,borrow as int,word_modulus() as int);
    assert(high as int==upper%word_modulus() as int);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(upper,word_modulus() as int);
    let result=low as int+high as int*word_modulus() as int;
    let source=a0 as int+a1 as int*word_modulus() as int+double_word_modulus() as int
        -b0 as int-b1 as int*word_modulus() as int;
    assert(source==(upper/word_modulus() as int+1)*double_word_modulus() as int+result) by(nonlinear_arith)
        requires low as int==a0 as int-b0 as int+borrow as int*word_modulus() as int,
            upper==a1 as int-b1 as int-borrow as int,
            upper==word_modulus() as int*(upper/word_modulus() as int)+high as int,
            source==a0 as int+a1 as int*word_modulus() as int+double_word_modulus() as int-b0 as int-b1 as int*word_modulus() as int,
            result==low as int+high as int*word_modulus() as int,
            double_word_modulus()==word_modulus()*word_modulus();
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_mod(
        source,double_word_modulus() as int,upper/word_modulus() as int+1,result);
}
struct Poly {r:[u64;2],h:[u64;3]}
impl Poly {
    spec fn value(&self) -> nat {limb_value(self.h@)}
    spec fn multiplier(&self) -> nat {self.r@[0] as nat+(self.r@[1] as nat)*word_modulus()}
    spec fn valid(&self) -> bool {canonical(self.h@)}
    fn new(raw:&[u8]) -> (r:Self) requires raw.len()==16, ensures r.valid(),r.value()==0,r.multiplier()==clamp(raw@), {
        let mut key=[0u8;16];let mut i=0usize;
        while i<16
            invariant i<=16,raw.len()==16,
                forall|j:int| #![trigger key@[j]] 0<=j<i ==> key@[j]==
                    if j==3 || j==7 || j==11 || j==15 {raw@[j]&15u8}
                    else if j==4 || j==8 || j==12 {raw@[j]&252u8}else{raw@[j]},
            decreases 16-i,
        {
            let mut b=raw[i];
            if i==3 || i==7 || i==11 || i==15{b&=15;}
            if i==4 || i==8 || i==12{b&=252;}
            key[i]=b;i+=1;
        }
        let result=Self {r:[le64(&key,0),le64(&key,8)],h:[0u64;3]};
        proof {
            field_zero(result.h@);
            assert forall|j:int| #![trigger key@[j]] 0<=j<16 implies key@[j]==clamped_byte(raw@,j) by {}
            clamp_wire(raw@,key@);little16_split(key@,0);
        }
        result
    }
    fn update_block(&mut self,raw:&[u8])
        requires old(self).valid(),raw.len()==16,
        ensures final(self).valid(),final(self).multiplier()==old(self).multiplier(),
            final(self).value()==((old(self).value()+little(raw@,0,16)+double_word_modulus())*old(self).multiplier())%p130(),
    {
        let ghost before=self.value();
        let ghost multiplier=self.multiplier();
        let lo=le64(raw,0);let hi=le64(raw,8);
        proof {
            field_constants();field_join128(lo,hi);
            little16_split(raw@,0);
            field_message_pair(lo,hi);
            vstd::arithmetic::div_mod::lemma_mul_mod_noop_left(
                before as int+little(raw@,0,16) as int+double_word_modulus() as int,
                multiplier as int,p130() as int);
        }
        let added=add_mod(self.h,[lo,hi,1]);self.h=mul_mod(added,self.r);
    }
    fn finish(&self) -> (r:[u8;16])
        requires self.valid(),
        ensures r@==encoded128(self.value()),
    {
        let out=write_pair(self.h[0],self.h[1]);
        proof {
            field_constants();field_join128(self.h[0],self.h[1]);
            vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(self.h@[2] as int,
                self.h@[0] as int+self.h@[1] as int*word_modulus() as int,double_word_modulus() as int);
            vstd::arithmetic::div_mod::lemma_small_mod(
                self.h@[0] as nat+self.h@[1] as nat*word_modulus(),double_word_modulus());
            limb_low_mod(self.h@);
            encoded_pair(self.h[0],self.h[1],self.value());
        }
        out
    }
}
proof fn little_equal(left:Seq<u8>,at:nat,right:Seq<u8>,bt:nat,n:nat)
    requires at+n<=left.len(),bt+n<=right.len(),
        left.subrange(at as int,(at+n) as int)==right.subrange(bt as int,(bt+n) as int),
    ensures little(left,at,n)==little(right,bt,n),
    decreases n,
{
    if n==0 {little_zero(left,at);little_zero(right,bt);}
    else {
        assert(left.subrange(at as int,(at+n-1) as int)
            =~=right.subrange(bt as int,(bt+n-1) as int));
        little_equal(left,at,right,bt,(n-1) as nat);
        little_step(left,at,(n-1) as nat);little_step(right,bt,(n-1) as nat);
        let last=(n-1) as int;
        assert(0<=last<n);
        assert(left.subrange(at as int,(at+n) as int)[last]
            ==right.subrange(bt as int,(bt+n) as int)[last]);
        assert(left.subrange(at as int,(at+n) as int)[last]==left[at as int+last]);
        assert(right.subrange(bt as int,(bt+n) as int)[last]==right[bt as int+last]);
        assert(left[(at+n-1) as int]==right[(bt+n-1) as int]);
    }
}
proof fn poly_zero(r:nat,input:Seq<u8>)
    ensures poly_blocks(r,input,0)==0,
{reveal(poly_blocks);}
proof fn poly_step(r:nat,input:Seq<u8>,n:nat)
    requires (n+1)*16<=input.len(),
    ensures poly_blocks(r,input,n+1)
        ==((poly_blocks(r,input,n)+little(input,n*16,16)+double_word_modulus())*r)%p130(),
{reveal(poly_blocks);}
proof fn poly_block_view(r:nat,before:nat,after:nat,whole:Seq<u8>,n:nat,part:Seq<u8>)
    requires part.len()==16,(n+1)*16<=whole.len(),
        whole.subrange((n*16) as int,((n+1)*16) as int)==part,
        before==poly_blocks(r,whole,n),
        after==((before+little(part,0,16)+double_word_modulus())*r)%p130(),
    ensures after==poly_blocks(r,whole,n+1),
{
    poly_step(r,whole,n);
    assert(part.subrange(0,16) =~=part);
    little_equal(whole,n*16,part,0,16);
}
proof fn advance_nh_chunk(at:nat,take:nat)
    requires at%1024==0,1<=take<=1024,
    ensures (at+take+1023)/1024==at/1024+1,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(at as int,1024);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_div(
        at as int+take as int+1023,1024,(at/1024) as int+1,take as int-1);
}
fn header_hash(derived:&[u8],tweak:&[u8;32],bulk:usize) -> (r:[u8;16])
    requires derived.len()==1136,bulk<=MAX_ADIANTUM_BYTES,
    ensures r@==header_hash_reference(derived@,tweak@,bulk as nat),
{
    let mut p=Poly::new(&derived[32..48]);
    let bits=bulk as u64*8;
    let mut header=[0u8;16];put64(&mut header,0,bits);
    let ghost whole=encoded128(bulk as nat*8)+tweak@;
    let ghost multiplier=p.multiplier();
    proof {
        field_constants();
        vstd::arithmetic::div_mod::lemma_small_mod(bulk as nat*8,double_word_modulus());
        encoded_pair(bits,0,bulk as nat*8);zero_word64();
        assert(header@ =~=word64(bits)+word64(0));
        assert(header@==encoded128(bulk as nat*8));
        concat_parts(encoded128(bulk as nat*8),tweak@);
        assert(whole.subrange(0,16)==header@);
        poly_zero(multiplier,whole);
    }
    let ghost previous=p.value();p.update_block(&header);
    proof {poly_block_view(multiplier,previous,p.value(),whole,0,header@);}
    let ghost previous=p.value();p.update_block(&tweak[..16]);
    proof {
        window_region(whole,16,32,0,16);
        assert(whole.subrange(16,48)==tweak@);
        assert(whole.subrange(16,32)==tweak@.subrange(0,16));
        poly_block_view(multiplier,previous,p.value(),whole,1,tweak@.subrange(0,16));
    }
    let ghost previous=p.value();p.update_block(&tweak[16..]);
    proof {
        window_region(whole,16,32,16,16);
        assert(whole.subrange(16,48)==tweak@);
        assert(whole.subrange(32,48)==tweak@.subrange(16,32));
        poly_block_view(multiplier,previous,p.value(),whole,2,tweak@.subrange(16,32));
    }
    p.finish()
}
spec fn chunk_data(input:Seq<u8>,at:nat) -> Seq<u8> {
    Seq::new(1024,|i:int| if at+i<input.len() {input[at as int+i]}else{0u8})
}
proof fn chunk_word(input:Seq<u8>,chunk:nat,padded:Seq<u8>,unit:nat,word:nat)
    requires padded==chunk_data(input,chunk*1024),unit<64,word<4,
    ensures little(padded,unit*16+word*4,4)==nh_word(input,chunk,unit,word),
{
    let at=unit*16+word*4;
    let raw=Seq::new(4,|i:int| if chunk*1024+at+i<input.len()
        {input[(chunk*1024+at) as int+i]}else{0u8});
    assert(padded.subrange(at as int,at as int+4) =~= raw);
    assert(raw.subrange(0,4) =~=raw);
    little_equal(padded,at,raw,0,4);
    little_four(raw,0);
    assert(little(raw,0,4)<=u32::MAX);
    assert(nh_word(input,chunk,unit,word)==little(raw,0,4));
}
proof fn nh_units_zero(derived:Seq<u8>,input:Seq<u8>,chunk:nat,pass:nat)
    ensures nh_units(derived,input,chunk,pass,0)==0,
{reveal(nh_units);}
proof fn nh_unit_step(derived:Seq<u8>,input:Seq<u8>,chunk:nat,pass:nat,n:nat)
    ensures nh_units(derived,input,chunk,pass,n+1)=={
        let key=64+(n*4+pass*4)*4;
        let a=add32(nh_word(input,chunk,n,0),little(derived,key,4) as u32) as nat;
        let b=add32(nh_word(input,chunk,n,2),little(derived,key+8,4) as u32) as nat;
        let c=add32(nh_word(input,chunk,n,1),little(derived,key+4,4) as u32) as nat;
        let d=add32(nh_word(input,chunk,n,3),little(derived,key+12,4) as u32) as nat;
        ((nh_units(derived,input,chunk,pass,n) as nat+a*b+c*d)%word_modulus()) as u64
    },
{reveal(nh_units);}
proof fn nh_reference_length(derived:Seq<u8>,input:Seq<u8>)
    ensures nh_reference(derived,input).len()==((input.len()+1023)/1024)*32,
{reveal(nh_reference);}
proof fn nh_reference_byte(derived:Seq<u8>,input:Seq<u8>,index:nat)
    requires index<((input.len()+1023)/1024)*32,
    ensures nh_reference(derived,input)[index as int]=={
        let chunk=index/32;let remain=(input.len()-chunk*1024) as nat;
        let take=if remain<1024 {remain}else{1024nat};
        let sum=nh_units(derived,input,chunk,(index%32)/8,(take+15)/16);
        (sum>>(((index%8)*8) as u32)) as u8
    },
{reveal(nh_reference);}
proof fn nh_word_index(chunk:nat,pass:nat,j:nat)
    requires pass<4,j<8,
    ensures (chunk*32+pass*8+j)/32==chunk,
        ((chunk*32+pass*8+j)%32)/8==pass,
        (chunk*32+pass*8+j)%8==j,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        (chunk*32+pass*8+j) as int,32,chunk as int,(pass*8+j) as int);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        (pass*8+j) as int,8,pass as int,j as int);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        (chunk*32+pass*8+j) as int,8,(chunk*4+pass) as int,j as int);
}
proof fn nh_chunk_shape(derived:Seq<u8>,input:Seq<u8>,chunk:nat)
    requires chunk*1024<input.len(),
    ensures (chunk+1)*32<=nh_reference(derived,input).len(),
        nh_reference(derived,input).subrange((chunk*32) as int,(chunk*32+32) as int).len()==32,
{
    nh_reference_length(derived,input);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(
        ((chunk+1)*1024) as int,input.len() as int+1023,1024);
    vstd::arithmetic::div_mod::lemma_div_by_multiple(chunk as int+1,1024);
}
proof fn nh_chunk_word(derived:Seq<u8>,input:Seq<u8>,chunk:nat,pass:nat)
    requires chunk*1024<input.len(),pass<4,
    ensures nh_reference(derived,input).len()==((input.len()+1023)/1024)*32,
        nh_reference(derived,input).subrange((chunk*32) as int,(chunk*32+32) as int).len()==32,
        nh_reference(derived,input).subrange((chunk*32+pass*8) as int,(chunk*32+pass*8+8) as int)
            ==word64(nh_units(derived,input,chunk,pass,
                ((if input.len()-chunk*1024<1024 {(input.len()-chunk*1024) as nat}else{1024nat})+15)/16)),
{
    nh_reference_length(derived,input);nh_chunk_shape(derived,input,chunk);
    let remain=(input.len()-chunk*1024) as nat;
    let take=if remain<1024 {remain}else{1024nat};
    let sum=nh_units(derived,input,chunk,pass,(take+15)/16);
    let base=(chunk*32+pass*8) as int;
    let view=nh_reference(derived,input).subrange(base,base+8);
    assert(view.len()==8);
    assert forall|j:int| #![trigger view[j]] 0<=j<8 implies view[j]==word64(sum)[j] by {
        nh_word_index(chunk,pass,j as nat);
        nh_reference_byte(derived,input,chunk*32+pass*8+j as nat);
        assert(view[j]==nh_reference(derived,input)[base+j]);
        assert(nh_reference(derived,input)[base+j]==word64(sum)[j]);
    }
    assert(view =~=word64(sum));
}
fn nh_combine(sum:u64,a:u64,b:u64,c:u64,d:u64) -> (r:u64)
    requires a<=u32::MAX,b<=u32::MAX,c<=u32::MAX,d<=u32::MAX,
    ensures r==((sum as nat+a as nat*b as nat+c as nat*d as nat)%word_modulus()) as u64,
{
    proof {
        vstd::arithmetic::mul::lemma_mul_upper_bound(a as int,u32::MAX as int,b as int,u32::MAX as int);
        vstd::arithmetic::mul::lemma_mul_upper_bound(c as int,u32::MAX as int,d as int,u32::MAX as int);
    }
    let ab=a.wrapping_mul(b);let cd=c.wrapping_mul(d);
    proof {
        field_constants();
        vstd::arithmetic::div_mod::lemma_small_mod(a as nat*b as nat,word_modulus());
        vstd::arithmetic::div_mod::lemma_small_mod(c as nat*d as nat,word_modulus());
        wrap_add64(sum,ab);
        wrap_add64(vstd::wrapping::u64_specs::wrapping_add(sum,ab),cd);
        vstd::arithmetic::div_mod::lemma_add_mod_noop_right(cd as int,sum as int+ab as int,word_modulus() as int);
    }
    sum.wrapping_add(ab).wrapping_add(cd)
}
fn message_hash(derived:&[u8],input:&[u8]) -> (r:[u8;16]) requires derived.len()==1136,input.len()<=MAX_ADIANTUM_BYTES, ensures r@==message_hash_reference(derived@,input@), {
    let mut poly=Poly::new(&derived[48..64]);let mut at=0usize;
    proof {
        poly_zero(poly.multiplier(),nh_reference(derived@,input@));
        nh_reference_length(derived@,input@);
    }
    while at<input.len()
        invariant at<=input.len()<=MAX_ADIANTUM_BYTES,derived.len()==1136,
            nh_reference(derived@,input@).len()==((input.len()+1023)/1024)*32,
            at%1024==0 || at==input.len(),poly.valid(),
            poly.multiplier()==clamp(derived@.subrange(48,64)),
            poly.value()==poly_blocks(poly.multiplier(),nh_reference(derived@,input@),(((at+1023)/1024)*2) as nat),
        decreases input.len()-at,
    {
        let remain=input.len()-at;let take=if remain<1024{remain}else{1024};
        let units=(take+15)/16;let mut padded=[0u8;1024];let mut i=0usize;
        while i<take
            invariant i<=take<=1024,at+take<=input.len(),at<input.len(),at%1024==0,
                take as nat==if (input.len() as nat-at as nat)<1024 {(input.len()-at) as nat}else{1024nat},
                forall|j:int| #![trigger padded@[j]] 0<=j<1024 ==> padded@[j]==
                    if j<i {input@[at as int+j]}else{0u8},
            decreases take-i,
        {padded[i]=input[at+i];i+=1;}
        proof {
            assert(padded@ =~=chunk_data(input@,at as nat));
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(at as int,1024);
        }
        let mut sums=[0u64;4];let mut unit=0usize;
        proof {
            assert forall|pass:int| #![trigger sums@[pass]] 0<=pass<4 implies sums@[pass]
                ==nh_units(derived@,input@,(at/1024) as nat,pass as nat,0) by {
                nh_units_zero(derived@,input@,(at/1024) as nat,pass as nat);
            }
        }
        while unit<units
            invariant unit<=units<=64,0<take<=1024,units==(take+15)/16,
                derived.len()==1136,at%1024==0,at+take<=input.len(),at<input.len(),
                padded@==chunk_data(input@,at as nat),
                take as nat==if (input.len() as nat-at as nat)<1024 {(input.len()-at) as nat}else{1024nat},
                forall|pass:int| #![trigger sums@[pass]] 0<=pass<4 ==> sums@[pass]
                    ==nh_units(derived@,input@,(at/1024) as nat,pass as nat,unit as nat),
            decreases units-unit,
        {
            let x=unit*16;let m0=le32(&padded,x);let m1=le32(&padded,x+4);let m2=le32(&padded,x+8);let m3=le32(&padded,x+12);
            proof {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(at as int,1024);
                chunk_word(input@,(at/1024) as nat,padded@,unit as nat,0);
                chunk_word(input@,(at/1024) as nat,padded@,unit as nat,1);
                chunk_word(input@,(at/1024) as nat,padded@,unit as nat,2);
                chunk_word(input@,(at/1024) as nat,padded@,unit as nat,3);
            }
            let mut pass=0usize;
            while pass<4
                invariant pass<=4,unit<units<=64,derived.len()==1136,
                    m0==nh_word(input@,(at/1024) as nat,unit as nat,0),
                    m1==nh_word(input@,(at/1024) as nat,unit as nat,1),
                    m2==nh_word(input@,(at/1024) as nat,unit as nat,2),
                    m3==nh_word(input@,(at/1024) as nat,unit as nat,3),
                    forall|j:int| #![trigger sums@[j]] 0<=j<4 ==> sums@[j]==
                        nh_units(derived@,input@,(at/1024) as nat,j as nat,
                            if j<pass {unit as nat+1}else{unit as nat}),
                decreases 4-pass,
            {
                proof {nh_unit_step(derived@,input@,(at/1024) as nat,pass as nat,unit as nat);}
                let key=64+(unit*4+pass*4)*4;
                let a=wrapping_add32(m0,le32(derived,key)) as u64;let b=wrapping_add32(m2,le32(derived,key+8)) as u64;
                let c=wrapping_add32(m1,le32(derived,key+4)) as u64;let d=wrapping_add32(m3,le32(derived,key+12)) as u64;
                sums[pass]=nh_combine(sums[pass],a,b,c,d);pass+=1;
            }
            unit+=1;
        }
        let mut nh=[0u8;32];i=0;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(at as int,1024);
            nh_chunk_shape(derived@,input@,(at/1024) as nat);
            assert(nh_reference(derived@,input@).subrange(((at/1024)*32) as int,((at/1024)*32) as int)
                =~=Seq::<u8>::empty());
            assert(nh@.take(0) =~=Seq::<u8>::empty());
        }
        while i<4
            invariant i<=4,at<input.len(),at%1024==0,units==(take+15)/16,
                ((at/1024)+1)*32<=nh_reference(derived@,input@).len(),
                take as nat==if (input.len() as nat-at as nat)<1024 {(input.len()-at) as nat}else{1024nat},
                forall|pass:int| #![trigger sums@[pass]] 0<=pass<4 ==> sums@[pass]
                    ==nh_units(derived@,input@,(at/1024) as nat,pass as nat,units as nat),
                nh@.take((i*8) as int)==nh_reference(derived@,input@).subrange(
                    ((at/1024)*32) as int,((at/1024)*32+i*8) as int),
            decreases 4-i,
        {
            proof {
                nh_chunk_word(derived@,input@,(at/1024) as nat,i as nat);
                window_region(nh_reference(derived@,input@),((at/1024)*32) as nat,32,0,(i*8) as nat);
                window_region(nh_reference(derived@,input@),((at/1024)*32) as nat,32,(i*8) as nat,8);
                replace_prefix(nh@,nh_reference(derived@,input@).subrange(
                    ((at/1024)*32) as int,((at/1024)*32+32) as int),(i*8) as nat,word64(sums@[i as int]));
            }
            put64(&mut nh,i*8,sums[i]);i+=1;
        }
        proof {
            assert(nh@ =~=nh_reference(derived@,input@).subrange(
                ((at/1024)*32) as int,((at/1024)*32+32) as int));
            assert((at+1023)/1024==at/1024);
            window_region(nh_reference(derived@,input@),((at/1024)*32) as nat,32,0,16);
            window_region(nh_reference(derived@,input@),((at/1024)*32) as nat,32,16,16);
            assert(nh_reference(derived@,input@).subrange(((at/1024)*32) as int,((at/1024)*32+16) as int)
                ==nh@.subrange(0,16));
            assert(nh_reference(derived@,input@).subrange(((at/1024)*32+16) as int,((at/1024)*32+32) as int)
                ==nh@.subrange(16,32));
        }
        let ghost previous=poly.value();poly.update_block(&nh[..16]);
        proof {poly_block_view(poly.multiplier(),previous,poly.value(),nh_reference(derived@,input@),
            ((at/1024)*2) as nat,nh@.subrange(0,16));}
        let ghost previous=poly.value();poly.update_block(&nh[16..]);
        proof {
            poly_block_view(poly.multiplier(),previous,poly.value(),nh_reference(derived@,input@),
                ((at/1024)*2+1) as nat,nh@.subrange(16,32));
            advance_nh_chunk(at as nat,take as nat);
        }
        at+=take;
        proof {nh_reference_length(derived@,input@);}
    }
    proof {nh_reference_length(derived@,input@);}
    poly.finish()
}
fn add128(a:[u8;16],b:[u8;16]) -> (r:[u8;16]) ensures r@==added128(a@,b@), {
    let low=le64(&a,0).wrapping_add(le64(&b,0));let carry=if low<le64(&a,0){1}else{0};
    let high=le64(&a,8).wrapping_add(le64(&b,8)).wrapping_add(carry);
    let out=write_pair(low,high);
    proof {
        little16_split(a@,0);little16_split(b@,0);field_constants();
        little16_bound(a@,0);little16_bound(b@,0);
        pair_add(little(a@,0,8) as u64,little(a@,8,8) as u64,
            little(b@,0,8) as u64,little(b@,8,8) as u64,low,high,carry);
        encoded_pair(low,high,little(a@,0,16)+little(b@,0,16));
    }
    out
}
fn sub128(a:[u8;16],b:[u8;16]) -> (r:[u8;16]) ensures r@==subtracted128(a@,b@), {
    let low=le64(&a,0).wrapping_sub(le64(&b,0));let borrow=if le64(&a,0)<le64(&b,0){1}else{0};
    let high=le64(&a,8).wrapping_sub(le64(&b,8)).wrapping_sub(borrow);
    let out=write_pair(low,high);
    proof {
        little16_split(a@,0);little16_split(b@,0);field_constants();
        little16_bound(a@,0);little16_bound(b@,0);
        pair_sub(little(a@,0,8) as u64,little(a@,8,8) as u64,
            little(b@,0,8) as u64,little(b@,8,8) as u64,low,high,borrow);
        encoded_pair(low,high,(little(a@,0,16)+double_word_modulus()-little(b@,0,16)) as nat);
    }
    out
}
spec fn derived_aes_binding(cipher:&AesKey,raw:Seq<u8>) -> bool {
    !cipher.aes_retired() && cipher.aes_round_count()==14
        && cipher.aes_schedule().take(240)==crate::aes::expanded_key_reference(adiantum_derived_reference(raw).take(32),52)
}
proof fn standard_witness(cipher:AesKey,raw:Seq<u8>,tweak:Seq<u8>,input:Seq<u8>,output:Seq<u8>,decrypt:bool)
    requires derived_aes_binding(&cipher,raw),
        output==adiantum_reference(&cipher,raw,tweak,input,decrypt),
    ensures adiantum_result_is_standard(raw,tweak,input,output,decrypt),
{}
fn apply(raw_key:&[u8],tweak:[u8;32],input:&[u8],decrypt:bool) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>raw_key.len()==32 && 16<=input.len()<=MAX_ADIANTUM_BYTES && v.len()==input.len()
        && adiantum_result_is_standard(raw_key@,tweak@,input@,v@,decrypt),Err(_)=>true},
{
    if raw_key.len()!=32{return Err(Error::KeyLength);}
    if input.len()<16 || input.len()>MAX_ADIANTUM_BYTES{return Err(Error::Length);}
    let mut key_iv=[0u8;32];key_iv[0]=1;
    let zeroes=[0u8;1136];let derived=xchacha12_bytes(raw_key,key_iv,&zeroes)?;
    proof {
        assert(key_iv@ =~=Seq::new(32,|j:int|if j==0 {1u8}else{0u8}));
        assert(zeroes@ =~=Seq::new(1136,|j:int|0u8));
        assert(derived@==adiantum_derived_reference(raw_key@));
    }
    let aes=match AesKey::new_aes_key(&derived[..32]){Ok(v)=>v,Err(_)=>return Err(Error::Primitive)};
    proof {assert(derived_aes_binding(&aes,raw_key@));}
    let bulk=input.len()-16;let header=header_hash(derived.as_slice(),&tweak,bulk);
    let first_hash=message_hash(derived.as_slice(),&input[..bulk]);
    let mut middle=add128(add128(copy16(input,bulk),header),first_hash);
    let ghost expected_header=header_hash_reference(adiantum_derived_reference(raw_key@),tweak@,bulk as nat);
    let ghost expected_first=message_hash_reference(adiantum_derived_reference(raw_key@),input@.take(bulk as int));
    let ghost first_middle=middle@;
    proof {
        assert(first_middle==added128(added128(input@.subrange(bulk as int,input.len() as int),expected_header),expected_first));
    }
    if !decrypt{middle=match aes.encrypt_aes_block(middle){Ok(v)=>v,Err(_)=>return Err(Error::Primitive)};}
    let ghost stream_middle=middle@;
    let mut stream_iv=[0u8;32];let mut i=0usize;
    while i<16
        invariant i<=16,derived@==adiantum_derived_reference(raw_key@),derived_aes_binding(&aes,raw_key@),
            header@==expected_header,middle@==stream_middle,
            first_middle==added128(added128(input@.subrange(bulk as int,input.len() as int),expected_header),expected_first),
            stream_middle==if decrypt {first_middle}else{aes.aes_encrypt_reference(first_middle)},
            forall|j:int| #![trigger stream_iv@[j]] 0<=j<32 ==> stream_iv@[j]==
                if j<i {middle@[j]}else{0u8},
        decreases 16-i,
    {stream_iv[i]=middle[i];i+=1;}stream_iv[16]=1;
    proof {assert(stream_iv@ =~=stream_middle+Seq::new(16,|j:int|if j==0 {1u8}else{0u8}));}
    let mut out=xchacha12_bytes(raw_key,stream_iv,&input[..bulk])?;
    if decrypt{middle=match aes.decrypt_aes_block(middle){Ok(v)=>v,Err(_)=>return Err(Error::Primitive)};}
    let second_hash=message_hash(derived.as_slice(),out.as_slice());let right=sub128(sub128(middle,header),second_hash);
    let ghost left=out@;
    let ghost full=adiantum_reference(&aes,raw_key@,tweak@,input@,decrypt);
    proof {
        assert(left==xchacha12_reference(raw_key@,
            stream_middle+Seq::new(16,|j:int|if j==0 {1u8}else{0u8}),input@.take(bulk as int)));
        assert(middle@==if decrypt {aes.aes_decrypt_reference(stream_middle)}else{stream_middle});
        assert(left+right@==full);
    }
    i=0;
    while i<16
        invariant i<=16,out@==left+right@.take(i as int),out.len()==bulk+i,
            derived_aes_binding(&aes,raw_key@),left+right@==full,
            full==adiantum_reference(&aes,raw_key@,tweak@,input@,decrypt),
        decreases 16-i,
    {out.push(right[i]);i+=1;}
    proof {
        assert(i==16);
        assert(right@.take(16) =~=right@);
        assert(out@==full);
        standard_witness(aes,raw_key@,tweak@,input@,out@,decrypt);
    }
    Ok(out)
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
