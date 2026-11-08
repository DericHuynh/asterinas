// SPDX-License-Identifier: MPL-2.0

//! Executable SHA-2 and HKDF primitives for the implementation-first feature
//! work. These implement FIPS 180-4 and RFC 2104/5869 byte algorithms; algorithm
//! refinement, side-channel properties and key-memory erasure are proof work.
//! No collision-resistance or authenticity theorem is asserted by this module.

use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error { LengthOverflow, OutputTooLong, InvalidKey }


spec fn add32(a:u32,b:u32) -> u32 {((a as nat+b as nat)%4294967296) as u32}
spec fn add64(a:u64,b:u64) -> u64 {((a as nat+b as nat)%18446744073709551616) as u64}
spec fn rotate32(x:u32,count:u32) -> u32 {
    let n=count%32;if n==0 {x}else{(x>>n)|(x<<(32-n))}
}
spec fn rotate64(x:u64,count:u32) -> u64 {
    let n=count%64;if n==0 {x}else{(x>>n)|(x<<(64-n))}
}
spec fn be_word32(block:Seq<u8>,i:nat) -> u32 {
    ((block[(4*i) as int] as u32)<<24)|((block[(4*i+1) as int] as u32)<<16)
        |((block[(4*i+2) as int] as u32)<<8)|block[(4*i+3) as int] as u32
}
spec fn be_prefix64(block:Seq<u8>,i:nat,n:nat) -> u64
    decreases n
{
    if n==0 {0u64}
    else {(be_prefix64(block,i,(n-1) as nat)<<8)|block[(8*i+n-1) as int] as u64}
}
spec fn schedule32(block:Seq<u8>,i:nat) -> u32
    decreases i
{
    if i<16 {be_word32(block,i)}
    else {
        let x=schedule32(block,(i-15) as nat);let y=schedule32(block,(i-2) as nat);
        let a=rotate32(x,7)^rotate32(x,18)^(x>>3);
        let b=rotate32(y,17)^rotate32(y,19)^(y>>10);
        add32(add32(add32(schedule32(block,(i-16) as nat),a),schedule32(block,(i-7) as nat)),b)
    }
}
spec fn schedule64(block:Seq<u8>,i:nat) -> u64
    decreases i
{
    if i<16 {be_prefix64(block,i,8)}
    else {
        let x=schedule64(block,(i-15) as nat);let y=schedule64(block,(i-2) as nat);
        let a=rotate64(x,1)^rotate64(x,8)^(x>>7);
        let b=rotate64(y,19)^rotate64(y,61)^(y>>6);
        add64(add64(add64(schedule64(block,(i-16) as nat),a),schedule64(block,(i-7) as nat)),b)
    }
}
struct Round32 {a:u32,b:u32,c:u32,d:u32,e:u32,f:u32,g:u32,h:u32}
struct Round64 {a:u64,b:u64,c:u64,d:u64,e:u64,f:u64,g:u64,h:u64}
spec fn seed32(state:Seq<u32>) -> Round32 {
    Round32 {a:state[0],b:state[1],c:state[2],d:state[3],e:state[4],f:state[5],g:state[6],h:state[7]}
}
spec fn seed64(state:Seq<u64>) -> Round64 {
    Round64 {a:state[0],b:state[1],c:state[2],d:state[3],e:state[4],f:state[5],g:state[6],h:state[7]}
}
spec fn round32(s:Round32,word:u32,constant:u32) -> Round32 {
    let sigma1=rotate32(s.e,6)^rotate32(s.e,11)^rotate32(s.e,25);
    let choice=(s.e&s.f)^(!s.e&s.g);
    let t1=add32(add32(add32(add32(s.h,sigma1),choice),constant),word);
    let sigma0=rotate32(s.a,2)^rotate32(s.a,13)^rotate32(s.a,22);
    let majority=(s.a&s.b)^(s.a&s.c)^(s.b&s.c);
    let t2=add32(sigma0,majority);
    Round32 {a:add32(t1,t2),b:s.a,c:s.b,d:s.c,e:add32(s.d,t1),f:s.e,g:s.f,h:s.g}
}
spec fn round64(s:Round64,word:u64,constant:u64) -> Round64 {
    let sigma1=rotate64(s.e,14)^rotate64(s.e,18)^rotate64(s.e,41);
    let choice=(s.e&s.f)^(!s.e&s.g);
    let t1=add64(add64(add64(add64(s.h,sigma1),choice),constant),word);
    let sigma0=rotate64(s.a,28)^rotate64(s.a,34)^rotate64(s.a,39);
    let majority=(s.a&s.b)^(s.a&s.c)^(s.b&s.c);
    let t2=add64(sigma0,majority);
    Round64 {a:add64(t1,t2),b:s.a,c:s.b,d:s.c,e:add64(s.d,t1),f:s.e,g:s.f,h:s.g}
}
spec fn rounds32(seed:Seq<u32>,block:Seq<u8>,n:nat) -> Round32
    decreases n
{
    if n==0 {seed32(seed)}
    else {round32(rounds32(seed,block,(n-1) as nat),schedule32(block,(n-1) as nat),K256@[(n-1) as int])}
}
spec fn rounds64(seed:Seq<u64>,block:Seq<u8>,n:nat) -> Round64
    decreases n
{
    if n==0 {seed64(seed)}
    else {round64(rounds64(seed,block,(n-1) as nat),schedule64(block,(n-1) as nat),K512@[(n-1) as int])}
}
spec fn compressed32(seed:Seq<u32>,block:Seq<u8>) -> Seq<u32> {
    let r=rounds32(seed,block,64);
    seq![add32(seed[0],r.a),add32(seed[1],r.b),add32(seed[2],r.c),add32(seed[3],r.d),
        add32(seed[4],r.e),add32(seed[5],r.f),add32(seed[6],r.g),add32(seed[7],r.h)]
}
spec fn compressed64(seed:Seq<u64>,block:Seq<u8>) -> Seq<u64> {
    let r=rounds64(seed,block,80);
    seq![add64(seed[0],r.a),add64(seed[1],r.b),add64(seed[2],r.c),add64(seed[3],r.d),
        add64(seed[4],r.e),add64(seed[5],r.f),add64(seed[6],r.g),add64(seed[7],r.h)]
}
fn rotr32(x:u32,count:u32) -> (r:u32) ensures r==rotate32(x,count) {
    let n=count%32;
    if n==0 {x}else{(x>>n)|(x<<(32-n))}
}
fn rotr64(x:u64,count:u32) -> (r:u64) ensures r==rotate64(x,count) {
    let n=count%64;
    if n==0 {x}else{(x>>n)|(x<<(64-n))}
}

const K256: [u32; 64] = [
0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2,
];
const K512: [u64; 80] = [
0x428a2f98d728ae22,0x7137449123ef65cd,0xb5c0fbcfec4d3b2f,0xe9b5dba58189dbbc,
0x3956c25bf348b538,0x59f111f1b605d019,0x923f82a4af194f9b,0xab1c5ed5da6d8118,
0xd807aa98a3030242,0x12835b0145706fbe,0x243185be4ee4b28c,0x550c7dc3d5ffb4e2,
0x72be5d74f27b896f,0x80deb1fe3b1696b1,0x9bdc06a725c71235,0xc19bf174cf692694,
0xe49b69c19ef14ad2,0xefbe4786384f25e3,0x0fc19dc68b8cd5b5,0x240ca1cc77ac9c65,
0x2de92c6f592b0275,0x4a7484aa6ea6e483,0x5cb0a9dcbd41fbd4,0x76f988da831153b5,
0x983e5152ee66dfab,0xa831c66d2db43210,0xb00327c898fb213f,0xbf597fc7beef0ee4,
0xc6e00bf33da88fc2,0xd5a79147930aa725,0x06ca6351e003826f,0x142929670a0e6e70,
0x27b70a8546d22ffc,0x2e1b21385c26c926,0x4d2c6dfc5ac42aed,0x53380d139d95b3df,
0x650a73548baf63de,0x766a0abb3c77b2a8,0x81c2c92e47edaee6,0x92722c851482353b,
0xa2bfe8a14cf10364,0xa81a664bbc423001,0xc24b8b70d0f89791,0xc76c51a30654be30,
0xd192e819d6ef5218,0xd69906245565a910,0xf40e35855771202a,0x106aa07032bbd1b8,
0x19a4c116b8d2d0c8,0x1e376c085141ab53,0x2748774cdf8eeb99,0x34b0bcb5e19b48a8,
0x391c0cb3c5c95a63,0x4ed8aa4ae3418acb,0x5b9cca4f7763e373,0x682e6ff3d6b2b8a3,
0x748f82ee5defb2fc,0x78a5636f43172f60,0x84c87814a1f0ab72,0x8cc702081a6439ec,
0x90befffa23631e28,0xa4506cebde82bde9,0xbef9a3f7b2c67915,0xc67178f2e372532b,
0xca273eceea26619c,0xd186b8c721c0c207,0xeada7dd6cde0eb1e,0xf57d4f7fee6ed178,
0x06f067aa72176fba,0x0a637dc5a2c898a6,0x113f9804bef90dae,0x1b710b35131c471b,
0x28db77f523047d84,0x32caab7b40c72493,0x3c9ebe0a15c9bebc,0x431d67c49c100d4c,
0x4cc5d4becb3e42b6,0x597f299cfc657e2a,0x5fcb6fab3ad6faec,0x6c44198c4a475817,
];

fn compress256(state: &mut [u32; 8], block: &[u8; 64])
    ensures final(state)@==compressed32(old(state)@,block@),
{
    let ghost seed=state@;
    let mut w = [0u32; 64]; let mut i = 0usize;
    while i < 16
        invariant i<=16,forall|j:int| 0<=j<i ==> w@[j]==schedule32(block@,j as nat),
        decreases 16-i,
    {
        w[i] = ((block[4*i] as u32) << 24) | ((block[4*i+1] as u32) << 16)
            | ((block[4*i+2] as u32) << 8) | block[4*i+3] as u32; i += 1;
    }
    while i < 64
        invariant 16<=i<=64,forall|j:int| 0<=j<i ==> w@[j]==schedule32(block@,j as nat),
        decreases 64-i,
    {
        let x = w[i-15]; let y = w[i-2];
        let a = rotr32(x,7) ^ rotr32(x,18) ^ (x >> 3);
        let b = rotr32(y,17) ^ rotr32(y,19) ^ (y >> 10);
        w[i] = w[i-16].wrapping_add(a).wrapping_add(w[i-7]).wrapping_add(b); i += 1;
    }
    let mut a=state[0]; let mut b=state[1]; let mut c=state[2]; let mut d=state[3];
    let mut e=state[4]; let mut f=state[5]; let mut g=state[6]; let mut h=state[7];
    i=0;
    while i<64
        invariant i<=64,state@==seed,
            forall|j:int| 0<=j<64 ==> w@[j]==schedule32(block@,j as nat),
            (Round32 {a,b,c,d,e,f,g,h})==rounds32(seed,block@,i as nat),
        decreases 64-i,
    {
        let s1=rotr32(e,6)^rotr32(e,11)^rotr32(e,25);
        let ch=(e&f)^(!e&g);
        let t1=h.wrapping_add(s1).wrapping_add(ch).wrapping_add(K256[i]).wrapping_add(w[i]);
        let s0=rotr32(a,2)^rotr32(a,13)^rotr32(a,22);
        let maj=(a&b)^(a&c)^(b&c); let t2=s0.wrapping_add(maj);
        h=g; g=f; f=e; e=d.wrapping_add(t1); d=c; c=b; b=a; a=t1.wrapping_add(t2); i+=1;
    }
    state[0]=state[0].wrapping_add(a); state[1]=state[1].wrapping_add(b);
    state[2]=state[2].wrapping_add(c); state[3]=state[3].wrapping_add(d);
    state[4]=state[4].wrapping_add(e); state[5]=state[5].wrapping_add(f);
    state[6]=state[6].wrapping_add(g); state[7]=state[7].wrapping_add(h);
}
fn compress512(state: &mut [u64; 8], block: &[u8; 128])
    ensures final(state)@==compressed64(old(state)@,block@),
{
    let ghost seed=state@;
    let mut w=[0u64;80]; let mut i=0usize;
    while i<16
        invariant i<=16,forall|j:int| 0<=j<i ==> w@[j]==schedule64(block@,j as nat),
        decreases 16-i,
    {
        let mut v=0u64; let mut j=0usize;
        while j<8
            invariant i<16,j<=8,v==be_prefix64(block@,i as nat,j as nat),
            decreases 8-j,
        { v=(v<<8)|block[8*i+j] as u64; j+=1; }
        w[i]=v; i+=1;
    }
    while i<80
        invariant 16<=i<=80,forall|j:int| 0<=j<i ==> w@[j]==schedule64(block@,j as nat),
        decreases 80-i,
    {
        let x=w[i-15]; let y=w[i-2];
        let a=rotr64(x,1)^rotr64(x,8)^(x>>7);
        let b=rotr64(y,19)^rotr64(y,61)^(y>>6);
        w[i]=w[i-16].wrapping_add(a).wrapping_add(w[i-7]).wrapping_add(b); i+=1;
    }
    let mut a=state[0]; let mut b=state[1]; let mut c=state[2]; let mut d=state[3];
    let mut e=state[4]; let mut f=state[5]; let mut g=state[6]; let mut h=state[7];
    i=0;
    while i<80
        invariant i<=80,state@==seed,
            forall|j:int| 0<=j<80 ==> w@[j]==schedule64(block@,j as nat),
            (Round64 {a,b,c,d,e,f,g,h})==rounds64(seed,block@,i as nat),
        decreases 80-i,
    {
        let s1=rotr64(e,14)^rotr64(e,18)^rotr64(e,41);
        let ch=(e&f)^(!e&g);
        let t1=h.wrapping_add(s1).wrapping_add(ch).wrapping_add(K512[i]).wrapping_add(w[i]);
        let s0=rotr64(a,28)^rotr64(a,34)^rotr64(a,39);
        let maj=(a&b)^(a&c)^(b&c); let t2=s0.wrapping_add(maj);
        h=g; g=f; f=e; e=d.wrapping_add(t1); d=c; c=b; b=a; a=t1.wrapping_add(t2); i+=1;
    }
    state[0]=state[0].wrapping_add(a); state[1]=state[1].wrapping_add(b);
    state[2]=state[2].wrapping_add(c); state[3]=state[3].wrapping_add(d);
    state[4]=state[4].wrapping_add(e); state[5]=state[5].wrapping_add(f);
    state[6]=state[6].wrapping_add(g); state[7]=state[7].wrapping_add(h);
}

pub struct HashState256 {pub words:Seq<u32>,pub tail:Seq<u8>}
pub struct HashState512 {pub words:Seq<u64>,pub tail:Seq<u8>}
spec fn initial256() -> HashState256 {
    HashState256 {words:seq![0x6a09e667u32,0xbb67ae85u32,0x3c6ef372u32,0xa54ff53au32,
        0x510e527fu32,0x9b05688cu32,0x1f83d9abu32,0x5be0cd19u32],tail:Seq::empty()}
}
spec fn initial512() -> HashState512 {
    HashState512 {words:seq![0x6a09e667f3bcc908u64,0xbb67ae8584caa73bu64,0x3c6ef372fe94f82bu64,0xa54ff53a5f1d36f1u64,
        0x510e527fade682d1u64,0x9b05688c2b3e6c1fu64,0x1f83d9abfb41bd6bu64,0x5be0cd19137e2179u64],tail:Seq::empty()}
}
spec fn absorb256(s:HashState256,byte:u8) -> HashState256 {
    let next=s.tail.push(byte);
    if next.len()==64 {HashState256 {words:compressed32(s.words,next),tail:Seq::empty()}}
    else {HashState256 {words:s.words,tail:next}}
}
spec fn absorb512(s:HashState512,byte:u8) -> HashState512 {
    let next=s.tail.push(byte);
    if next.len()==128 {HashState512 {words:compressed64(s.words,next),tail:Seq::empty()}}
    else {HashState512 {words:s.words,tail:next}}
}
spec fn extend256(s:HashState256,input:Seq<u8>) -> HashState256
    decreases input.len()
{
    if input.len()==0 {s}else{absorb256(extend256(s,input.drop_last()),input.last())}
}
spec fn extend512(s:HashState512,input:Seq<u8>) -> HashState512
    decreases input.len()
{
    if input.len()==0 {s}else{absorb512(extend512(s,input.drop_last()),input.last())}
}
spec fn message256(input:Seq<u8>) -> HashState256 {extend256(initial256(),input)}
spec fn message512(input:Seq<u8>) -> HashState512 {extend512(initial512(),input)}
spec fn padding256(tail:Seq<u8>,length:nat) -> Seq<u8> {
    let n=if tail.len()<56 {64nat}else{128nat};
    let bits=(length*8) as u64;
    Seq::new(n,|i:int| {
        if i<tail.len() {tail[i]}else if i==tail.len() {128u8}
        else if i>=n-8 {(bits>>(((n-1-i)*8) as u32)) as u8}else{0u8}
    })
}
spec fn padding512(tail:Seq<u8>,length:nat) -> Seq<u8> {
    let n=if tail.len()<112 {128nat}else{256nat};
    let high=(length/2305843009213693952) as u64;let low=(length*8) as u64;
    Seq::new(n,|i:int| {
        if i<tail.len() {tail[i]}else if i==tail.len() {128u8}
        else if i>=n-8 {(low>>(((n-1-i)*8) as u32)) as u8}
        else if i>=n-16 {(high>>(((n-9-i)*8) as u32)) as u8}else{0u8}
    })
}
spec fn encoded256(words:Seq<u32>) -> Seq<u8> {
    Seq::new(32,|i:int| (words[i/4]>>(((3-i%4)*8) as u32)) as u8)
}
spec fn encoded512(words:Seq<u64>) -> Seq<u8> {
    Seq::new(64,|i:int| (words[i/8]>>(((7-i%8)*8) as u32)) as u8)
}
spec fn finished256(s:HashState256,length:nat) -> Seq<u8> {
    let padding=padding256(s.tail,length);
    let first=compressed32(s.words,padding.take(64));
    encoded256(if padding.len()==64 {first}else{compressed32(first,padding.subrange(64,128))})
}
spec fn finished512(s:HashState512,length:nat) -> Seq<u8> {
    let padding=padding512(s.tail,length);
    let first=compressed64(s.words,padding.take(128));
    encoded512(if padding.len()==128 {first}else{compressed64(first,padding.subrange(128,256))})
}
pub closed spec fn digest256_reference(input:Seq<u8>) -> Seq<u8> {finished256(message256(input),input.len())}
pub closed spec fn digest512_reference(input:Seq<u8>) -> Seq<u8> {finished512(message512(input),input.len())}
proof fn extend256_concat(seed:HashState256,before:Seq<u8>,after:Seq<u8>)
    ensures extend256(seed,before+after)==extend256(extend256(seed,before),after),
    decreases after.len(),
{
    if after.len()>0 {
        assert((before+after).drop_last()==before+after.drop_last());
        assert((before+after).last()==after.last());
        extend256_concat(seed,before,after.drop_last());
    }
}
proof fn extend512_concat(seed:HashState512,before:Seq<u8>,after:Seq<u8>)
    ensures extend512(seed,before+after)==extend512(extend512(seed,before),after),
    decreases after.len(),
{
    if after.len()>0 {
        assert((before+after).drop_last()==before+after.drop_last());
        assert((before+after).last()==after.last());
        extend512_concat(seed,before,after.drop_last());
    }
}

pub struct Sha256 { state: [u32;8], buffer: [u8;64], used: usize, length: u64, message:Ghost<Seq<u8>> }
impl Sha256 {
    pub closed spec fn valid256(&self) -> bool {
        self.used<64 && self.length<=0x1fff_ffff_ffff_ffff && self.used==self.length%64
            && self.message@.len()==self.length
            && self.state@==message256(self.message@).words
            && self.buffer@.take(self.used as int)==message256(self.message@).tail
    }
    pub closed spec fn input256(&self) -> Seq<u8> {self.message@}
    pub closed spec fn physical256(&self) -> (Seq<u32>,Seq<u8>,usize,u64) {
        (self.state@,self.buffer@,self.used,self.length)
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {self.valid256()}
    pub fn new256() -> (r:Self) ensures r.valid256(),r.input256()==Seq::<u8>::empty() { Self { state:[0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19],buffer:[0;64],used:0,length:0,message:Ghost(Seq::empty()) } }
    pub fn update256(&mut self, input: &[u8]) -> (r:Result<(),Error>)
        ensures final(self).valid256(),r.is_ok() ==> final(self).input256()==old(self).input256()+input@,
            r.is_err() ==> final(self).physical256()==old(self).physical256()
                && final(self).input256()==old(self).input256(),
    {
        proof {use_type_invariant(&*self);}
        let ghost initial_used=self.used;
        let ghost initial_state=message256(self.message@);

        let n=input.len() as u64;
        if n as usize!=input.len() || n>0x1fff_ffff_ffff_ffffu64-self.length { return Err(Error::LengthOverflow); }
        self.length+=n; let mut i=0usize;
        while i<input.len()
            invariant i<=input.len(),self.used<64,
                self.used==(initial_used+i)%64,
                self.length==old(self).length+input.len(),self.length<=0x1fff_ffff_ffff_ffff,
                self.message@==old(self).message@,
                self.state@==extend256(initial_state,input@.take(i as int)).words,
                self.buffer@.take(self.used as int)==extend256(initial_state,input@.take(i as int)).tail,
            decreases input.len()-i,
        {
            proof {
                assert(input@.take(i as int+1).drop_last()==input@.take(i as int));
                assert(input@.take(i as int+1).last()==input@[i as int]);
            }
            self.buffer[self.used]=input[i]; self.used+=1; i+=1;
            if self.used==64 { let b=self.buffer; compress256(&mut self.state,&b); self.used=0; }
        }
        proof {extend256_concat(initial256(),self.message@,input@);}
        self.message=Ghost(self.message@+input@);
        Ok(())
    }
    pub fn finalize256(mut self) -> (r:Vec<u8>)
        ensures r.len()==32,r@==digest256_reference(self.input256()),
    {
        proof {use_type_invariant(&self);}
        let ghost initial_words=self.state@;
        let ghost padded=padding256(self.buffer@.take(self.used as int),self.length as nat);

        let bits=self.length*8;
        self.buffer[self.used]=0x80; self.used+=1;
        if self.used>56 {
            while self.used<64
                invariant self.used<=64,
                    self.buffer@.take(self.used as int)==padded.take(self.used as int),
                decreases 64-self.used,
            { self.buffer[self.used]=0; self.used+=1; }
            let b=self.buffer; compress256(&mut self.state,&b); self.used=0;
        }
        let ghost padding_offset=if padded.len()==64 {0int}else{64int};
        while self.used<56
            invariant self.used<=56,
                self.buffer@.take(self.used as int)==padded.subrange(padding_offset,padding_offset+self.used as int),
                self.state@==if padding_offset==0 {initial_words}
                    else {compressed32(initial_words,padded.take(64))},
            decreases 56-self.used,
        { self.buffer[self.used]=0; self.used+=1; }
        let mut i=0usize;
        while i<8 invariant i<=8, decreases 8-i, { self.buffer[56+i]=(bits>>((7-i)*8)) as u8; i+=1; }
        let b=self.buffer; compress256(&mut self.state,&b);
        let mut out=Vec::new(); i=0;
        while i<8 invariant i<=8,out@==encoded256(self.state@).take((i*4) as int), decreases 8-i, {
            let w=self.state[i]; out.push((w>>24) as u8); out.push((w>>16) as u8);
            out.push((w>>8) as u8); out.push(w as u8); i+=1;
        }
        out
    }
}
pub struct Sha512 { state: [u64;8], buffer: [u8;128], used: usize, length: u64, message:Ghost<Seq<u8>> }
impl Sha512 {
    pub closed spec fn valid512(&self) -> bool {
        self.used<128 && self.length<=u64::MAX && self.used==self.length%128
            && self.message@.len()==self.length
            && self.state@==message512(self.message@).words
            && self.buffer@.take(self.used as int)==message512(self.message@).tail
    }
    pub closed spec fn input512(&self) -> Seq<u8> {self.message@}
    pub closed spec fn physical512(&self) -> (Seq<u64>,Seq<u8>,usize,u64) {
        (self.state@,self.buffer@,self.used,self.length)
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {self.valid512()}
    pub fn new512() -> (r:Self) ensures r.valid512(),r.input512()==Seq::<u8>::empty() { Self { state:[0x6a09e667f3bcc908,0xbb67ae8584caa73b,0x3c6ef372fe94f82b,0xa54ff53a5f1d36f1,0x510e527fade682d1,0x9b05688c2b3e6c1f,0x1f83d9abfb41bd6b,0x5be0cd19137e2179],buffer:[0;128],used:0,length:0,message:Ghost(Seq::empty()) } }
    pub fn update512(&mut self, input: &[u8]) -> (r:Result<(),Error>)
        ensures final(self).valid512(),r.is_ok() ==> final(self).input512()==old(self).input512()+input@,
            r.is_err() ==> final(self).physical512()==old(self).physical512()
                && final(self).input512()==old(self).input512(),
    {
        proof {use_type_invariant(&*self);}
        let ghost initial_used=self.used;
        let ghost initial_state=message512(self.message@);

        let n=input.len() as u64;
        if n as usize!=input.len() || n>u64::MAX-self.length { return Err(Error::LengthOverflow); }
        self.length+=n; let mut i=0usize;
        while i<input.len()
            invariant i<=input.len(),self.used<128,
                self.used==(initial_used+i)%128,
                self.length==old(self).length+input.len(),self.length<=u64::MAX,
                self.message@==old(self).message@,
                self.state@==extend512(initial_state,input@.take(i as int)).words,
                self.buffer@.take(self.used as int)==extend512(initial_state,input@.take(i as int)).tail,
            decreases input.len()-i,
        {
            proof {
                assert(input@.take(i as int+1).drop_last()==input@.take(i as int));
                assert(input@.take(i as int+1).last()==input@[i as int]);
            }
            self.buffer[self.used]=input[i]; self.used+=1; i+=1;
            if self.used==128 { let b=self.buffer; compress512(&mut self.state,&b); self.used=0; }
        }
        proof {extend512_concat(initial512(),self.message@,input@);}
        self.message=Ghost(self.message@+input@);
        Ok(())
    }
    pub fn finalize512(mut self) -> (r:Vec<u8>)
        ensures r.len()==64,r@==digest512_reference(self.input512()),
    {
        proof {use_type_invariant(&self);}
        let ghost initial_words=self.state@;
        let ghost padded=padding512(self.buffer@.take(self.used as int),self.length as nat);

        let low=self.length.wrapping_shl(3); let high=self.length>>61;
        self.buffer[self.used]=0x80; self.used+=1;
        if self.used>112 {
            while self.used<128
                invariant self.used<=128,
                    self.buffer@.take(self.used as int)==padded.take(self.used as int),
                decreases 128-self.used,
            { self.buffer[self.used]=0; self.used+=1; }
            let b=self.buffer; compress512(&mut self.state,&b); self.used=0;
        }
        let ghost padding_offset=if padded.len()==128 {0int}else{128int};
        while self.used<112
            invariant self.used<=112,
                self.buffer@.take(self.used as int)==padded.subrange(padding_offset,padding_offset+self.used as int),
                self.state@==if padding_offset==0 {initial_words}
                    else {compressed64(initial_words,padded.take(128))},
            decreases 112-self.used,
        { self.buffer[self.used]=0; self.used+=1; }
        let mut i=0usize;
        while i<8 invariant i<=8, decreases 8-i, { self.buffer[112+i]=(high>>((7-i)*8)) as u8; self.buffer[120+i]=(low>>((7-i)*8)) as u8; i+=1; }
        let b=self.buffer; compress512(&mut self.state,&b);
        let mut out=Vec::new(); i=0;
        while i<8
            invariant i<=8,out@==encoded512(self.state@).take((i*8) as int),
            decreases 8-i,
        {
            let mut j=0usize;
            while j<8
                invariant i<8,j<=8,out@==encoded512(self.state@).take((i*8+j) as int),
                decreases 8-j,
            {out.push((self.state[i]>>((7-j)*8)) as u8);j+=1;}
            i+=1;
        }
        out
    }
}
pub fn sha256(input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==32 && v@==digest256_reference(input@),Err(_)=>true},
{
    let mut h=Sha256::new256(); h.update256(input)?; Ok(h.finalize256())
}
pub fn sha512(input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==64 && v@==digest512_reference(input@),Err(_)=>true},
{
    let mut h=Sha512::new512(); h.update512(input)?; Ok(h.finalize512())
}

spec fn hmac_material(key:Seq<u8>) -> Seq<u8> {
    if key.len()>128 {digest512_reference(key)}else{key}
}
spec fn hmac_pad(key:Seq<u8>,pad:u8) -> Seq<u8> {
    let material=hmac_material(key);
    Seq::new(128,|i:int| pad^(if i<material.len() {material[i]}else{0u8}))
}
pub closed spec fn hmac512_reference(key:Seq<u8>,input:Seq<u8>) -> Seq<u8> {
    digest512_reference(hmac_pad(key,0x5c)+digest512_reference(hmac_pad(key,0x36)+input))
}
pub closed spec fn hkdf512_block_reference(prk:Seq<u8>,info:Seq<u8>,n:nat) -> Seq<u8>
    decreases n
{
    if n==0 {Seq::empty()}
    else {hmac512_reference(prk,hkdf512_block_reference(prk,info,(n-1) as nat)+info+seq![n as u8])}
}
spec fn hkdf_blocks(prk:Seq<u8>,info:Seq<u8>,n:nat) -> Seq<u8>
    decreases n
{
    if n==0 {Seq::empty()}
    else {hkdf_blocks(prk,info,(n-1) as nat)+hkdf512_block_reference(prk,info,n)}
}
pub closed spec fn hkdf512_expand_reference(prk:Seq<u8>,info:Seq<u8>,length:nat) -> Seq<u8> {
    hkdf_blocks(prk,info,(length+63)/64).take(length as int)
}

pub struct HmacSha512 { inner: Sha512, outer: Sha512, key:Ghost<Seq<u8>>, message:Ghost<Seq<u8>> }
impl HmacSha512 {
    pub closed spec fn hmac_valid(&self) -> bool {
        self.inner.valid512() && self.outer.valid512()
            && self.inner.input512()==hmac_pad(self.key@,0x36)+self.message@
            && self.outer.input512()==hmac_pad(self.key@,0x5c)
    }
    pub closed spec fn hmac_key(&self) -> Seq<u8> {self.key@}
    pub closed spec fn hmac_input(&self) -> Seq<u8> {self.message@}
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {self.hmac_valid()}
    pub fn new_hmac512(key:&[u8]) -> (r:Result<Self,Error>)
        ensures match r {Ok(h)=>h.hmac_valid() && h.hmac_key()==key@ && h.hmac_input()==Seq::<u8>::empty(),Err(_)=>true},
    {
        let mut material=Vec::new();
        if key.len()>128 { material=sha512(key)?; } else { let mut i=0usize; while i<key.len() invariant i<=key.len()<=128,material@==key@.take(i as int), decreases key.len()-i, { material.push(key[i]); i+=1; } }
        let mut ipad=[0x36u8;128]; let mut opad=[0x5cu8;128]; let mut i=0usize;
        while i<material.len()
            invariant i<=material.len()<=128,material@==hmac_material(key@),
                forall|j:int| 0<=j<128 ==> ipad@[j]==0x36u8^(if j<i {material@[j]}else{0u8}),
                forall|j:int| 0<=j<128 ==> opad@[j]==0x5cu8^(if j<i {material@[j]}else{0u8}),
            decreases material.len()-i,
        { ipad[i]^=material[i]; opad[i]^=material[i]; i+=1; }
        let mut inner=Sha512::new512(); let mut outer=Sha512::new512(); inner.update512(&ipad)?; outer.update512(&opad)?;
        Ok(Self { inner,outer,key:Ghost(key@),message:Ghost(Seq::empty()) })
    }
    pub fn update_hmac512(&mut self,input:&[u8]) -> (r:Result<(),Error>)
        ensures final(self).hmac_valid(),final(self).hmac_key()==old(self).hmac_key(),
            final(self).hmac_input()==if r.is_ok() {old(self).hmac_input()+input@}else{old(self).hmac_input()},
    {
        proof {use_type_invariant(&*self);}
        self.inner.update512(input)?;
        self.message=Ghost(self.message@+input@);
        Ok(())
    }
    pub fn finalize_hmac512(mut self) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==64 && v@==hmac512_reference(self.hmac_key(),self.hmac_input()),Err(_)=>true},
{
        proof {use_type_invariant(&self);}
        let digest=self.inner.finalize512(); self.outer.update512(digest.as_slice())?; Ok(self.outer.finalize512())
    }
}
pub fn hmac_sha512(key:&[u8],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==64 && v@==hmac512_reference(key@,input@),Err(_)=>true},
{
    let mut h=HmacSha512::new_hmac512(key)?; h.update_hmac512(input)?; h.finalize_hmac512()
}
pub fn hkdf_sha512_extract(salt:&[u8],input_key:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==64 && v@==hmac512_reference(salt@,input_key@),Err(_)=>true},
{
    hmac_sha512(salt,input_key)
}
pub fn hkdf_sha512_expand(prk:&[u8],info:&[u8],output_len:usize) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==output_len && output_len<=16320
        && v@==hkdf512_expand_reference(prk@,info@,output_len as nat),Err(_)=>true},
{
    if prk.len()!=64 { return Err(Error::InvalidKey); }
    if output_len>255*64 { return Err(Error::OutputTooLong); }
    let mut output=Vec::new(); let mut previous=Vec::new(); let mut counter=1u16;
    while output.len()<output_len
        invariant output.len()<=output_len<=16320,1<=counter<=256,
            output.len()==(counter as usize-1)*64 || output.len()==output_len,
            output@==hkdf_blocks(prk@,info@,(counter-1) as nat).take(output.len() as int),
            previous@==hkdf512_block_reference(prk@,info@,(counter-1) as nat),
        decreases output_len-output.len(),
    {
        let mut h=HmacSha512::new_hmac512(prk)?; h.update_hmac512(previous.as_slice())?; h.update_hmac512(info)?;
        h.update_hmac512(&[counter as u8])?; let next=h.finalize_hmac512()?;
        let left=output_len-output.len(); let take=if left<64 { left } else { 64 };
        let ghost before=output.len();let ghost prior=output@;
        let mut i=0usize;
        while i<take
            invariant i<=take<=64,next.len()==64,output.len()==before+i,
                take<=output_len-before,output@==prior+next@.take(i as int),
            decreases take-i,
        { output.push(next[i]); i+=1; }
        previous=next; counter+=1;
    }
    Ok(output)
}

}
