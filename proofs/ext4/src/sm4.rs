// SPDX-License-Identifier: MPL-2.0

//! GB/T 32907-2016 SM4 block transform and owned expanded-key handle.
//! Byte substitution scans all 256 standard entries at fixed indices; compiler
//! constant-time behavior and physical erasure remain separate obligations.
//! Linux v7.0 crypto/sm4.c supplies the independently pinned format reference.

use vstd::prelude::*;

verus! {

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Error { KeyLength, Retired }

#[verifier::opaque]
const SBOX:[u8;256]=[
    0xd6,0x90,0xe9,0xfe,0xcc,0xe1,0x3d,0xb7,0x16,0xb6,0x14,0xc2,0x28,0xfb,0x2c,0x05,
    0x2b,0x67,0x9a,0x76,0x2a,0xbe,0x04,0xc3,0xaa,0x44,0x13,0x26,0x49,0x86,0x06,0x99,
    0x9c,0x42,0x50,0xf4,0x91,0xef,0x98,0x7a,0x33,0x54,0x0b,0x43,0xed,0xcf,0xac,0x62,
    0xe4,0xb3,0x1c,0xa9,0xc9,0x08,0xe8,0x95,0x80,0xdf,0x94,0xfa,0x75,0x8f,0x3f,0xa6,
    0x47,0x07,0xa7,0xfc,0xf3,0x73,0x17,0xba,0x83,0x59,0x3c,0x19,0xe6,0x85,0x4f,0xa8,
    0x68,0x6b,0x81,0xb2,0x71,0x64,0xda,0x8b,0xf8,0xeb,0x0f,0x4b,0x70,0x56,0x9d,0x35,
    0x1e,0x24,0x0e,0x5e,0x63,0x58,0xd1,0xa2,0x25,0x22,0x7c,0x3b,0x01,0x21,0x78,0x87,
    0xd4,0x00,0x46,0x57,0x9f,0xd3,0x27,0x52,0x4c,0x36,0x02,0xe7,0xa0,0xc4,0xc8,0x9e,
    0xea,0xbf,0x8a,0xd2,0x40,0xc7,0x38,0xb5,0xa3,0xf7,0xf2,0xce,0xf9,0x61,0x15,0xa1,
    0xe0,0xae,0x5d,0xa4,0x9b,0x34,0x1a,0x55,0xad,0x93,0x32,0x30,0xf5,0x8c,0xb1,0xe3,
    0x1d,0xf6,0xe2,0x2e,0x82,0x66,0xca,0x60,0xc0,0x29,0x23,0xab,0x0d,0x53,0x4e,0x6f,
    0xd5,0xdb,0x37,0x45,0xde,0xfd,0x8e,0x2f,0x03,0xff,0x6a,0x72,0x6d,0x6c,0x5b,0x51,
    0x8d,0x1b,0xaf,0x92,0xbb,0xdd,0xbc,0x7f,0x11,0xd9,0x5c,0x41,0x1f,0x10,0x5a,0xd8,
    0x0a,0xc1,0x31,0x88,0xa5,0xcd,0x7b,0xbd,0x2d,0x74,0xd0,0x12,0xb8,0xe5,0xb4,0xb0,
    0x89,0x69,0x97,0x4a,0x0c,0x96,0x77,0x7e,0x65,0xb9,0xf1,0x09,0xc5,0x6e,0xc6,0x84,
    0x18,0xf0,0x7d,0xec,0x3a,0xdc,0x4d,0x20,0x79,0xee,0x5f,0x3e,0xd7,0xcb,0x39,0x48,
];
const FK:[u32;4]=[0xa3b1bac6,0x56aa3350,0x677d9197,0xb27022dc];

spec fn rotate(x:u32,count:u32) -> u32 {let n=count%32;if n==0{x}else{(x<<n)|(x>>(32-n))}}
#[verifier::opaque]
spec fn byte_substituted(a:u8) -> u8 {SBOX@[a as int]}
spec fn substituted(x:u32) -> u32 {
    ((byte_substituted((x>>24) as u8) as u32)<<24)
        |((byte_substituted((x>>16) as u8) as u32)<<16)
        |((byte_substituted((x>>8) as u8) as u32)<<8)|byte_substituted(x as u8) as u32
}
spec fn key_changed(x:u32) -> u32 {let b=substituted(x);b^rotate(b,13)^rotate(b,23)}
spec fn data_changed(x:u32) -> u32 {let b=substituted(x);b^rotate(b,2)^rotate(b,10)^rotate(b,18)^rotate(b,24)}
spec fn round_constant(i:nat) -> u32 {
    (((i*28)%256) as u32)<<24 | ((((i*28+7)%256) as u32)<<16)
        | ((((i*28+14)%256) as u32)<<8) | ((i*28+21)%256) as u32
}
spec fn word(raw:Seq<u8>,at:int) -> u32 {
    ((raw[at] as u32)<<24)|((raw[at+1] as u32)<<16)|((raw[at+2] as u32)<<8)|raw[at+3] as u32
}
struct Registers {a:u32,b:u32,c:u32,d:u32}
spec fn key_registers(raw:Seq<u8>,n:nat) -> Registers
    decreases n
{
    if n==0 {Registers {a:word(raw,0)^FK@[0],b:word(raw,4)^FK@[1],c:word(raw,8)^FK@[2],d:word(raw,12)^FK@[3]}}
    else {
        let old=key_registers(raw,(n-1) as nat);
        Registers {a:old.b,b:old.c,c:old.d,d:old.a^key_changed(old.b^old.c^old.d^round_constant((n-1) as nat))}
    }
}
pub closed spec fn sm4_schedule_reference(raw:Seq<u8>) -> Seq<u32> {
    Seq::new(32,|i:int| key_registers(raw,(i+1) as nat).d)
}
spec fn data_registers(raw:Seq<u8>,keys:Seq<u32>,decrypt:bool,n:nat) -> Registers
    decreases n
{
    if n==0 {Registers {a:word(raw,0),b:word(raw,4),c:word(raw,8),d:word(raw,12)}}
    else {
        let old=data_registers(raw,keys,decrypt,(n-1) as nat);
        let selected=if decrypt {32-n}else{n-1};
        Registers {a:old.b,b:old.c,c:old.d,d:old.a^data_changed(old.b^old.c^old.d^keys[selected as int])}
    }
}
spec fn register_bytes(r:Registers) -> Seq<u8> {
    Seq::new(16,|i:int| {
        let v=if i<4 {r.d}else if i<8 {r.c}else if i<12 {r.b}else{r.a};
        (v>>(((3-i%4)*8) as u32)) as u8
    })
}
pub closed spec fn sm4_block_reference(raw_key:Seq<u8>,input:Seq<u8>,decrypt:bool) -> Seq<u8> {
    register_bytes(data_registers(input,sm4_schedule_reference(raw_key),decrypt,32))
}

fn rotl(x:u32,count:u32) -> (r:u32) ensures r==rotate(x,count) {
    let n=count%32;if n==0 {x}else{(x<<n)|(x>>(32-n))}
}
fn substitute_byte(a:u8) -> (r:u8) ensures r==byte_substituted(a) {
    proof {reveal(byte_substituted);}
    let mut result=0u8;let mut i=0usize;
    while i<256
        invariant i<=256,result==if (a as usize)<i {SBOX@[a as int]}else{0u8},
        decreases 256-i,
    {
        let delta=(a as u16)^(i as u16);
        let mask=(delta.wrapping_sub(1)>>8) as u8;
        result|=SBOX[i]&mask;i+=1;
    }
    result
}
fn tau(x:u32) -> (r:u32) ensures r==substituted(x) {
    ((substitute_byte((x>>24) as u8) as u32)<<24)
        |((substitute_byte((x>>16) as u8) as u32)<<16)
        |((substitute_byte((x>>8) as u8) as u32)<<8)
        |substitute_byte(x as u8) as u32
}
fn key_transform(x:u32) -> (r:u32) ensures r==key_changed(x) {let b=tau(x);b^rotl(b,13)^rotl(b,23)}
fn data_transform(x:u32) -> (r:u32) ensures r==data_changed(x) {let b=tau(x);b^rotl(b,2)^rotl(b,10)^rotl(b,18)^rotl(b,24)}
fn constant(i:usize) -> (r:u32) requires i<32, ensures r==round_constant(i as nat), {
    let a=(i*28)%256;let b=(i*28+7)%256;let c=(i*28+14)%256;let d=(i*28+21)%256;
    ((a as u32)<<24)|((b as u32)<<16)|((c as u32)<<8)|d as u32
}
fn be32(raw:&[u8],at:usize) -> (r:u32) requires at<=raw.len(),4<=raw.len()-at, ensures r==word(raw@,at as int), {
    ((raw[at] as u32)<<24)|((raw[at+1] as u32)<<16)|((raw[at+2] as u32)<<8)|raw[at+3] as u32
}
fn put32(out:&mut [u8;16],at:usize,v:u32)
    requires at<=12,
    ensures forall|i:int| 0<=i<16 ==> final(out)@[i]==
        if at<=i<at+4 {(v>>(((3-(i-at))*8) as u32)) as u8}else{old(out)@[i]},
{
    out[at]=(v>>24) as u8;out[at+1]=(v>>16) as u8;out[at+2]=(v>>8) as u8;out[at+3]=v as u8;
}
struct State {words:[u32;32],retired:bool}
pub struct Sm4Key {state:State}
impl Sm4Key {
    pub closed spec fn sm4_valid(&self) -> bool {
        self.state.retired ==> forall|i:int| 0<=i<32 ==> self.state.words@[i]==0
    }
    pub closed spec fn sm4_retired(&self) -> bool {self.state.retired}
    pub closed spec fn sm4_schedule(&self) -> Seq<u32> {self.state.words@}
    pub closed spec fn sm4_transform_reference(&self,input:Seq<u8>,decrypt:bool) -> Seq<u8> {
        register_bytes(data_registers(input,self.state.words@,decrypt,32))
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {self.sm4_valid()}
    pub fn new_sm4_key(raw:&[u8]) -> (r:Result<Self,Error>)
        ensures match r {Ok(k)=>raw.len()==16 && k.sm4_valid() && !k.sm4_retired()
            && k.sm4_schedule()==sm4_schedule_reference(raw@),Err(_)=>raw.len()!=16},
    {
        if raw.len()!=16 {return Err(Error::KeyLength);}
        let mut a=be32(raw,0)^FK[0];let mut b=be32(raw,4)^FK[1];
        let mut c=be32(raw,8)^FK[2];let mut d=be32(raw,12)^FK[3];
        let mut words=[0u32;32];let mut i=0usize;
        while i<32
            invariant i<=32,raw.len()==16,(Registers {a,b,c,d})==key_registers(raw@,i as nat),
                forall|j:int| 0<=j<i ==> words@[j]==sm4_schedule_reference(raw@)[j],
            decreases 32-i,
        {
            let next=a^key_transform(b^c^d^constant(i));words[i]=next;
            a=b;b=c;c=d;d=next;i+=1;
        }
        Ok(Self {state:State {words,retired:false}})
    }
    fn apply(&self,input:[u8;16],decrypt:bool) -> (r:Result<[u8;16],Error>)
        ensures match r {Ok(v)=>!self.sm4_retired() && v@==self.sm4_transform_reference(input@,decrypt),
            Err(_)=>self.sm4_retired()},
    {
        if self.state.retired {return Err(Error::Retired);}
        let mut a=be32(&input,0);let mut b=be32(&input,4);let mut c=be32(&input,8);let mut d=be32(&input,12);
        let mut i=0usize;
        while i<32
            invariant i<=32,(Registers {a,b,c,d})==data_registers(input@,self.state.words@,decrypt,i as nat),
            decreases 32-i,
        {
            let selected=if decrypt {31-i}else{i};
            let next=a^data_transform(b^c^d^self.state.words[selected]);
            a=b;b=c;c=d;d=next;i+=1;
        }
        let mut out=[0u8;16];put32(&mut out,0,d);put32(&mut out,4,c);put32(&mut out,8,b);put32(&mut out,12,a);Ok(out)
    }
    pub fn encrypt_sm4_block(&self,input:[u8;16]) -> (r:Result<[u8;16],Error>)
        ensures match r {Ok(v)=>!self.sm4_retired() && v@==self.sm4_transform_reference(input@,false),
            Err(_)=>self.sm4_retired()},
    {self.apply(input,false)}
    pub fn decrypt_sm4_block(&self,input:[u8;16]) -> (r:Result<[u8;16],Error>)
        ensures match r {Ok(v)=>!self.sm4_retired() && v@==self.sm4_transform_reference(input@,true),
            Err(_)=>self.sm4_retired()},
    {self.apply(input,true)}
    pub fn retire_sm4(&mut self)
        ensures final(self).sm4_valid(),final(self).sm4_retired(),
            forall|i:int| 0<=i<32 ==> final(self).sm4_schedule()[i]==0,
        opens_invariants none
        no_unwind
    {self.state=State {words:[0u32;32],retired:true};}
}
impl Drop for Sm4Key {
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {self.retire_sm4();}
}

}
