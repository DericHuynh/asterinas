// SPDX-License-Identifier: MPL-2.0

//! Linux fscrypt policy/context codecs and bound key/IV preparation.
//! This implementation-first module does not execute data/name ciphers, install
//! keys in a VFS keyring, generate nonces, or establish key-memory erasure.
//! The v2 HKDF and inode-hash bytes are computed, not supplied by a digest stub.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{bytes, crypto_sha2};

verus! {

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error { Size, Version, Reserved, Modes, Flags, Geometry, StableInodes,
    CasefoldV1, Index, KeyMismatch, KeyRequired, KeySize, HashFailure, OutputTooLong }

#[derive(Clone, Copy)]
pub struct Policy {
    version: u8, contents: u8, filenames: u8, flags: u8, data_unit_bits: u8,
    key: [u8;16],
}
#[derive(Clone, Copy)]
pub struct Context { policy: Policy, nonce: [u8;16] }
#[derive(Clone, Copy)]
pub struct Geometry {
    pub filesystem_block_bits: u8, pub supports_subblock_units: bool,
    pub stable_inodes: bool, pub inode_numbers_are_32bit: bool,
    pub max_data_unit_index: u64, pub casefolded: bool,
}


spec fn allowed_modes(version:u8,c:u8,n:u8) -> bool {
    (c==1 && n==4)||(c==5 && n==6)||(c==9 && n==9)
        ||(version==2 && ((c==1 && n==10)||(c==7 && n==8)))
}
spec fn allowed_fields(version:u8,c:u8,n:u8,flags:u8) -> bool {
    (version==0 || version==2) && allowed_modes(version,c,n)
        && (if version==0 {flags & !7u8==0}
            else {flags & !31u8==0 && (flags & 28==0 || flags & 28==4 || flags & 28==8 || flags & 28==16)})
        && (flags & 4==0 || (c==9 && n==9))
        && (flags & 24==0 || c==1)
}
spec fn key_length(p:Policy) -> nat {if p.version==0 {8}else{16}}
spec fn policy_wire(p:Policy) -> Seq<u8> {
    seq![p.version,p.contents,p.filenames,p.flags]
        +(if p.version==2 {seq![p.data_unit_bits,0u8,0u8,0u8]}else{Seq::empty()})
        +p.key@.take(key_length(p) as int)
}
spec fn context_wire(c:Context) -> Seq<u8> {
    policy_wire(c.policy).update(0,if c.policy.version==0 {1u8}else{2u8})+c.nonce@
}
spec fn geometry_allowed(p:Policy,g:Geometry) -> bool {
    let bits=if p.data_unit_bits==0 {g.filesystem_block_bits}else{p.data_unit_bits};
    9<=g.filesystem_block_bits<=16 && !(p.version==0 && g.casefolded)
        && (p.data_unit_bits==0 || (g.supports_subblock_units && 9<=bits<=g.filesystem_block_bits
            && (bits==g.filesystem_block_bits || p.flags & 16==0)))
        && (p.flags & 24==0 || (g.stable_inodes && g.inode_numbers_are_32bit && g.max_data_unit_index<=0xffff_ffff))
}
fn modes(version:u8,c:u8,n:u8) -> (r:bool) ensures r==allowed_modes(version,c,n) {
    (c==1 && n==4) || (c==5 && n==6) || (c==9 && n==9)
        || (version==2 && ((c==1 && n==10)||(c==7 && n==8)))
}
fn check_fields(version:u8,contents:u8,filenames:u8,flags:u8) -> (r:Result<(),Error>)
    ensures r.is_ok()==allowed_fields(version,contents,filenames,flags),
{
    if version!=0 && version!=2 {return Err(Error::Version);}
    if !modes(version,contents,filenames) { return Err(Error::Modes); }
    if version==0 {
        if flags & !7u8!=0 { return Err(Error::Flags); }
    } else {
        if flags & !31u8!=0 { return Err(Error::Flags); }
        let special=flags & 28u8;
        if special!=0 && special!=4 && special!=8 && special!=16 { return Err(Error::Flags); }
    }
    if flags & 4!=0 && (contents!=9 || filenames!=9) { return Err(Error::Flags); }
    if flags & 24!=0 && contents!=1 { return Err(Error::Flags); }
    Ok(())
}

pub fn parse_policy(raw:&[u8]) -> (r:Result<Policy,Error>)
    ensures match r {Ok(p)=>p.policy_valid() && p.policy_encoding()==raw@,Err(_)=>true},
{
    if raw.len()==0 { return Err(Error::Size); }
    let version=raw[0]; let mut key=[0u8;16]; let du;
    if version==0 {
        if raw.len()!=12 { return Err(Error::Size); }
        let mut i=0usize;
        while i<8
            invariant i<=8,raw.len()==12,
                forall|j:int| 0<=j<16 ==> key@[j]==if j<i {raw@[4+j]}else{0u8},
            decreases 8-i,
        { key[i]=raw[4+i]; i+=1; } du=0;
    } else if version==2 {
        if raw.len()!=24 { return Err(Error::Size); }
        if raw[5]!=0 || raw[6]!=0 || raw[7]!=0 { return Err(Error::Reserved); }
        let mut i=0usize;
        while i<16
            invariant i<=16,raw.len()==24,
                forall|j:int| 0<=j<16 ==> key@[j]==if j<i {raw@[8+j]}else{0u8},
            decreases 16-i,
        { key[i]=raw[8+i]; i+=1; } du=raw[4];
    } else { return Err(Error::Version); }
    check_fields(version,raw[1],raw[2],raw[3])?;
    let policy=Policy { version,contents:raw[1],filenames:raw[2],flags:raw[3],data_unit_bits:du,key };
    Ok(policy)
}
pub fn parse_context(raw:&[u8]) -> (r:Result<Context,Error>)
    ensures match r {Ok(c)=>c.context_encoding()==raw@ && c.context_policy().policy_valid(),Err(_)=>true},
{
    if raw.len()==0 { return Err(Error::Size); }
    let (version,nonce_start,du,key_start,key_len)=if raw[0]==1 {
        if raw.len()!=28 { return Err(Error::Size); } (0u8,12usize,0u8,4usize,8usize)
    } else if raw[0]==2 {
        if raw.len()!=40 { return Err(Error::Size); }
        if raw[5]!=0 || raw[6]!=0 || raw[7]!=0 { return Err(Error::Reserved); }
        (2u8,24usize,raw[4],8usize,16usize)
    } else { return Err(Error::Version); };
    let mut key=[0u8;16]; let mut nonce=[0u8;16]; let mut i=0usize;
    while i<key_len
        invariant i<=key_len<=16,key_start+key_len<=raw.len(),
            key_start==if version==0 {4usize}else{8usize},
            key_len==if version==0 {8usize}else{16usize},
            forall|j:int| 0<=j<16 ==> key@[j]==if j<i {raw@[key_start as int+j]}else{0u8},
        decreases key_len-i,
    { key[i]=raw[key_start+i]; i+=1; }
    i=0;
    while i<16
        invariant i<=16,nonce_start+16<=raw.len(),
            forall|j:int| 0<=j<i ==> nonce@[j]==raw@[nonce_start as int+j],
        decreases 16-i,
    { nonce[i]=raw[nonce_start+i]; i+=1; }
    check_fields(version,raw[1],raw[2],raw[3])?;
    let policy=Policy { version,contents:raw[1],filenames:raw[2],flags:raw[3],data_unit_bits:du,key };
    Ok(Context {policy,nonce})
}
impl Policy {
    pub closed spec fn policy_valid(&self) -> bool {
        allowed_fields(self.version,self.contents,self.filenames,self.flags)
            && (self.version!=0 || (self.data_unit_bits==0
                && forall|i:int| 8<=i<16 ==> self.key@[i]==0))
    }
    pub closed spec fn policy_encoding(&self) -> Seq<u8> {policy_wire(*self)}
    pub closed spec fn policy_fields(&self) -> (u8,u8,u8,u8,u8) {
        (self.version,self.contents,self.filenames,self.flags,self.data_unit_bits)
    }
    pub closed spec fn policy_key(&self) -> Seq<u8> {self.key@.take(key_length(*self) as int)}
    pub closed spec fn accepts_geometry(&self,g:Geometry) -> bool {geometry_allowed(*self,g)}
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {self.policy_valid()}
    pub fn fields(&self) -> (r:(u8,u8,u8,u8,u8)) ensures r==self.policy_fields() { (self.version,self.contents,self.filenames,self.flags,self.data_unit_bits) }
    pub fn key_specifier(&self) -> (r:Vec<u8>)
        ensures r@==self.policy_key(),r.len()==if self.policy_fields().0==0 {8usize}else{16usize},
    {
        let len=if self.version==0 {8usize}else{16usize};
        let mut out=Vec::new(); let mut i=0usize;
        while i<len
            invariant i<=len<=16,out@==self.key@.take(i as int),
            decreases len-i,
        { out.push(self.key[i]); i+=1; } out
    }
    pub fn encode_policy(&self) -> (r:Vec<u8>)
        ensures r@==self.policy_encoding(),r.len()==if self.policy_fields().0==0 {12usize}else{24usize},
    {
        proof {use_type_invariant(self);}
        let mut out=Vec::new(); out.push(self.version); out.push(self.contents); out.push(self.filenames); out.push(self.flags);
        if self.version==2 { out.push(self.data_unit_bits); out.push(0); out.push(0); out.push(0); }
        let len=if self.version==0 {8usize}else{16usize};
        let ghost header=out@;
        let mut i=0usize;
        while i<len
            invariant i<=len<=16,out@==header+self.key@.take(i as int),
            decreases len-i,
        { out.push(self.key[i]); i+=1; } out
    }
    pub fn validate(&self,g:Geometry) -> (r:Result<u8,Error>)
        ensures self.policy_valid(),r.is_ok()==self.accepts_geometry(g),
            match r {Ok(bits)=>9<=bits<=g.filesystem_block_bits<=16
                && bits==if self.policy_fields().4==0 {g.filesystem_block_bits}else{self.policy_fields().4},Err(_)=>true},
    {
        proof {use_type_invariant(self);}
        check_fields(self.version,self.contents,self.filenames,self.flags)?;
        if g.filesystem_block_bits<9 || g.filesystem_block_bits>16 { return Err(Error::Geometry); }
        if self.version==0 && g.casefolded { return Err(Error::CasefoldV1); }
        let bits=if self.data_unit_bits==0 {g.filesystem_block_bits}else{self.data_unit_bits};
        if self.data_unit_bits!=0 {
            if !g.supports_subblock_units || bits<9 || bits>g.filesystem_block_bits { return Err(Error::Geometry); }
            if bits!=g.filesystem_block_bits && self.flags & 16!=0 { return Err(Error::Geometry); }
        }
        if self.flags & 24!=0 {
            if !g.stable_inodes || !g.inode_numbers_are_32bit { return Err(Error::StableInodes); }
            if g.max_data_unit_index>0xffff_ffff { return Err(Error::Index); }
        }
        Ok(bits)
    }
    pub fn with_nonce(&self,nonce:[u8;16]) -> (r:Context)
        ensures r.context_encoding()==self.policy_encoding().update(0,if self.policy_fields().0==0 {1u8}else{2u8})+nonce@,
            r.context_policy().policy_fields()==self.policy_fields(),
    { Context {policy:*self,nonce} }
    pub fn permits_child(&self,child:&Policy) -> (r:bool)
        ensures r==(self.policy_encoding()==child.policy_encoding()),
    {
        self.version==child.version && self.contents==child.contents && self.filenames==child.filenames
            && self.flags==child.flags && self.data_unit_bits==child.data_unit_bits && self.key==child.key
    }
    pub fn padded_filename_len(&self,original:u32,maximum:u32) -> (r:Result<u32,Error>)
        ensures match r {Ok(n)=>original<=n<=maximum,Err(_)=>original>maximum},
    {
        if original>maximum { return Err(Error::Size); }
        let padding=4u64 << (self.flags & 3u8);
        let n=if original<16 {16u64}else{original as u64};
        let rounded=((n+padding-1)/padding)*padding;
        Ok(if rounded>maximum as u64 {maximum}else{rounded as u32})
    }
}

pub closed spec fn mode_iv_bytes(mode:u8) -> nat {if mode==9 || mode==10 {32}else{16}}
spec fn iv_admission(c:Context,g:Geometry,inode:u64,index:u64,filename:bool) -> bool {
    geometry_allowed(c.policy,g) && inode>0 && index<=g.max_data_unit_index
        && (!filename || index==0)
        && (c.policy.flags & 24==0 || (index<=0xffff_ffff && inode<=0xffff_ffff))
}
spec fn iv_word(c:Context,inode:u64,index:u64,hashed_inode:u32) -> u64 {
    if c.policy.flags & 8!=0 {index | (inode<<32)}
    else if c.policy.flags & 16!=0 {((hashed_inode as nat+index as nat)%4294967296) as u64}
    else {index}
}
pub closed spec fn iv_wire(c:Context,inode:u64,index:u64,filename:bool,hashed_inode:u32) -> Seq<u8> {
    let mode=if filename {c.policy.filenames}else{c.policy.contents};
    let word=iv_word(c,inode,index,hashed_inode);
    Seq::new(mode_iv_bytes(mode),|i:int| {
        if i<8 {(word>>((i as u32)*8)) as u8}
        else if c.policy.flags & 4!=0 && i<24 {c.nonce@[i-8]}
        else {0u8}
    })
}
fn iv_size(mode:u8) -> (r:Result<usize,Error>) ensures match r {Ok(n)=>n==mode_iv_bytes(mode) && (n==16 || n==32),Err(_)=>true} {
    if mode==9 || mode==10 {Ok(32)}else if mode==1 || mode==4 || mode==5 || mode==6 || mode==7 || mode==8 {Ok(16)}else{Err(Error::Modes)}
}
fn key_size(mode:u8) -> (r:Result<usize,Error>) ensures match r {Ok(n)=>n==mode_key_bytes(mode) && (n==16 || n==32 || n==64),Err(_)=>true} {
    if mode==1 {Ok(64)}else if mode==4 || mode==7 || mode==9 || mode==10 {Ok(32)}
    else if mode==5 || mode==6 || mode==8 {Ok(16)}else{Err(Error::Modes)}
}
fn append_le64(out:&mut Vec<u8>,v:u64)
    ensures final(out)@==old(out)@+Seq::new(8,|i:int| (v>>((i as u32)*8)) as u8),
{
    let ghost before=out@;let mut i=0usize;
    while i<8
        invariant i<=8,out@==before+Seq::new(i as nat,|j:int| (v>>((j as u32)*8)) as u8),
        decreases 8-i,
    {out.push((v>>(8*i)) as u8);i+=1;}
}
impl Context {
    pub closed spec fn context_encoding(&self) -> Seq<u8> {context_wire(*self)}
    pub closed spec fn context_policy(&self) -> Policy {self.policy}
    pub closed spec fn context_nonce(&self) -> Seq<u8> {self.nonce@}
    pub closed spec fn iv_admissible(&self,g:Geometry,inode:u64,index:u64,filename:bool) -> bool {
        iv_admission(*self,g,inode,index,filename)
    }
    pub fn policy(&self) -> (r:Policy) ensures r==self.context_policy(),r.policy_valid() {proof {use_type_invariant(&self.policy);}self.policy}
    pub fn nonce(&self) -> (r:[u8;16]) ensures r@==self.context_nonce() {self.nonce}
    pub fn encode_context(&self) -> (r:Vec<u8>)
        ensures r@==self.context_encoding(),r.len()==if self.context_policy().policy_fields().0==0 {28usize}else{40usize},
    {
        let mut out=self.policy.encode_policy(); out[0]=if self.policy.version==0 {1}else{2};
        let ghost header=out@;
        let mut i=0usize;
        while i<16
            invariant i<=16,out@==header+self.nonce@.take(i as int),
            decreases 16-i,
        {out.push(self.nonce[i]);i+=1;} out
    }
    pub fn context_iv(&self,g:Geometry,inode:u64,index:u64,filename:bool) -> (r:Result<Vec<u8>,Error>)
        ensures match r {Ok(v)=>self.iv_admissible(g,inode,index,filename)
            && v@==iv_wire(*self,inode,index,filename,0),Err(_)=>true},
    {
        if self.policy.flags & 16!=0 {return Err(Error::KeyRequired);}
        iv_with_hash(self,g,inode,index,filename,0)
    }
}
fn iv_with_hash(c:&Context,g:Geometry,inode:u64,index:u64,filename:bool,hashed_inode:u32) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>c.iv_admissible(g,inode,index,filename)
        && v@==iv_wire(*c,inode,index,filename,hashed_inode),Err(_)=>true},
{
    c.policy.validate(g)?;
    if inode==0 || index>g.max_data_unit_index || (filename && index!=0) {return Err(Error::Index);}
    let mode=if filename {c.policy.filenames}else{c.policy.contents};
    let len=iv_size(mode)?; let mut dun=index;
    if c.policy.flags & 24!=0 {
        if index>0xffff_ffff || inode>0xffff_ffff {return Err(Error::Index);}
        if c.policy.flags & 8!=0 {dun=index | (inode<<32);}
        else {dun=hashed_inode.wrapping_add(index as u32) as u64;}
    }
    let mut out=Vec::new();append_le64(&mut out,dun);
    let mut i=8usize;
    while i<len
        invariant 8<=i<=len<=32,out.len()==i,
            len==mode_iv_bytes(mode),dun==iv_word(*c,inode,index,hashed_inode),
            out@==iv_wire(*c,inode,index,filename,hashed_inode).take(i as int),
        decreases len-i,
    {
        out.push(if c.policy.flags & 4!=0 && i<24 {c.nonce[i-8]}else{0});i+=1;
    }
    Ok(out)
}

pub closed spec fn fscrypt_kdf_reference(prk:Seq<u8>,context:u8,info:Seq<u8>,length:nat) -> Seq<u8> {
    crypto_sha2::hkdf512_expand_reference(prk,seq![102u8,115u8,99u8,114u8,121u8,112u8,116u8,0u8,context]+info,length)
}
spec fn mode_key_bytes(mode:u8) -> nat {
    if mode==1 {64}else if mode==4 || mode==7 || mode==9 || mode==10 {32}else{16}
}
spec fn kdf_context(c:Context) -> u8 {
    if c.policy.flags & 4!=0 {3}
    else if c.policy.flags & 8!=0 {4}
    else if c.policy.flags & 16!=0 {6}
    else {2}
}
spec fn kdf_info(c:Context,uuid:Seq<u8>,filename:bool) -> Seq<u8> {
    let mode=if filename {c.policy.filenames}else{c.policy.contents};
    if c.policy.flags & 4!=0 {seq![mode]}
    else if c.policy.flags & 24!=0 {seq![mode]+uuid}
    else {c.nonce@}
}

fn hkdf(prk:&[u8],context:u8,info:&[u8],length:usize) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==length && length<=16320
        && v@==fscrypt_kdf_reference(prk@,context,info@,length as nat),Err(_)=>true},
{
    if context==0 || context>8 {return Err(Error::Flags);}
    let mut domain=Vec::new(); let prefix=[102u8,115,99,114,121,112,116,0];
    let mut i=0usize;while i<8 invariant i<=8,domain@==prefix@.take(i as int), decreases 8-i, {domain.push(prefix[i]);i+=1;}domain.push(context);
    let ghost header=domain@;
    i=0;
    while i<info.len()
        invariant i<=info.len(),domain@==header+info@.take(i as int),
        decreases info.len()-i,
    {domain.push(info[i]);i+=1;}
    match crypto_sha2::hkdf_sha512_expand(prk,domain.as_slice(),length) {Ok(v)=>Ok(v),Err(_)=>Err(Error::HashFailure)}
}
spec fn little_prefix(raw:Seq<u8>,offset:nat,n:nat) -> u64
    decreases n
{
    if n==0 {0u64}else {
        little_prefix(raw,offset,(n-1) as nat)|((raw[(offset+n-1) as int] as u64)<<(((n-1)*8) as u32))
    }
}
spec fn word_add(a:u64,b:u64) -> u64 {((a as nat+b as nat)%18446744073709551616) as u64}
spec fn word_rotate(x:u64,count:u32) -> u64 {
    let n=count%64;if n==0 {x}else{(x<<n)|(x>>(64-n))}
}
spec fn sip_step(s:Seq<u64>) -> Seq<u64> {
    let a=word_add(s[0],s[1]);let b=word_rotate(s[1],13)^a;let a=word_rotate(a,32);
    let c=word_add(s[2],s[3]);let d=word_rotate(s[3],16)^c;
    let a=word_add(a,d);let d=word_rotate(d,21)^a;
    let c=word_add(c,b);let b=word_rotate(b,17)^c;let c=word_rotate(c,32);
    seq![a,b,c,d]
}
spec fn sip_xor(s:Seq<u64>,i:int,value:u64) -> Seq<u64> {s.update(i,s[i]^value)}
pub closed spec fn inode_hash_reference(inode:u64,key:Seq<u8>) -> u32 {
    let a=little_prefix(key,0,8);let b=little_prefix(key,8,8);
    let s=seq![0x736f6d6570736575u64^a,0x646f72616e646f6du64^b,0x6c7967656e657261u64^a,0x7465646279746573u64^b];
    let s=sip_xor(sip_step(sip_step(sip_xor(s,3,inode))),0,inode);
    let tail=8u64<<56;
    let s=sip_xor(sip_xor(sip_step(sip_step(sip_xor(s,3,tail))),0,tail),2,255);
    let s=sip_step(sip_step(sip_step(sip_step(s))));
    (s[0]^s[1]^s[2]^s[3]) as u32
}

fn read64(raw:&[u8],offset:usize) -> (r:u64)
    requires offset<=raw.len(),8<=raw.len()-offset,
    ensures r==little_prefix(raw@,offset as nat,8),
{
    let mut v=0u64;let mut i=0usize;
    while i<8
        invariant i<=8,offset<=raw.len(),8<=raw.len()-offset,v==little_prefix(raw@,offset as nat,i as nat),
        decreases 8-i,
    {v|=(raw[offset+i] as u64)<<(i*8);i+=1;}v
}
fn rotl64(x:u64,count:u32) -> (r:u64) ensures r==word_rotate(x,count) {
    let n=count%64;
    if n==0 {x}else{(x<<n)|(x>>(64-n))}
}
fn sipround(s:&mut [u64;4]) ensures final(s)@==sip_step(old(s)@), {
    s[0]=s[0].wrapping_add(s[1]);s[1]=rotl64(s[1],13);s[1]^=s[0];s[0]=rotl64(s[0],32);
    s[2]=s[2].wrapping_add(s[3]);s[3]=rotl64(s[3],16);s[3]^=s[2];
    s[0]=s[0].wrapping_add(s[3]);s[3]=rotl64(s[3],21);s[3]^=s[0];
    s[2]=s[2].wrapping_add(s[1]);s[1]=rotl64(s[1],17);s[1]^=s[2];s[2]=rotl64(s[2],32);
}
fn siphash_inode(inode:u64,key:&[u8]) -> (r:u32) requires key.len()==16, ensures r==inode_hash_reference(inode,key@), {
    let a=read64(key,0);let b=read64(key,8);
    let mut s=[0x736f6d6570736575u64^a,0x646f72616e646f6du64^b,0x6c7967656e657261u64^a,0x7465646279746573u64^b];
    s[3]^=inode;sipround(&mut s);sipround(&mut s);s[0]^=inode;
    let tail=8u64<<56;s[3]^=tail;sipround(&mut s);sipround(&mut s);s[0]^=tail;s[2]^=255;
    sipround(&mut s);sipround(&mut s);sipround(&mut s);sipround(&mut s);
    (s[0]^s[1]^s[2]^s[3]) as u32
}

/// Raw-key v2 HKDF material. Holding this value is not a VFS authorization.
/// Key erasure, provisioning, revocation and cipher providers are separate.
pub struct MasterKeyV2 { prk:Vec<u8>,identifier:[u8;16],key_bytes:u8 }
impl MasterKeyV2 {
    pub closed spec fn master_valid(&self) -> bool {
        self.prk.len()==64 && 16<=self.key_bytes<=64
            && self.identifier@==fscrypt_kdf_reference(self.prk@,1,Seq::empty(),16)
    }
    pub closed spec fn master_prk(&self) -> Seq<u8> {self.prk@}
    pub closed spec fn derived_reference(&self,c:Context,uuid:[u8;16],filename:bool) -> Seq<u8> {
        fscrypt_kdf_reference(self.prk@,kdf_context(c),kdf_info(c,uuid@,filename),
            mode_key_bytes(if filename {c.policy.filenames}else{c.policy.contents}))
    }
    pub closed spec fn master_identifier(&self) -> Seq<u8> {self.identifier@}
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {self.master_valid()}
    pub fn from_raw(raw:&[u8]) -> (r:Result<Self,Error>)
        ensures match r {Ok(k)=>k.master_valid() && k.master_prk()==crypto_sha2::hmac512_reference(Seq::new(64,|i:int|0u8),raw@),Err(_)=>true},
    {
        if raw.len()<16 || raw.len()>64 {return Err(Error::KeySize);}
        let salt=[0u8;64];
        let prk=match crypto_sha2::hkdf_sha512_extract(&salt,raw) {Ok(v)=>v,Err(_)=>return Err(Error::HashFailure)};
        let id=hkdf(prk.as_slice(),1,&[],16)?;let mut identifier=[0u8;16];let mut i=0usize;
        while i<16
            invariant i<=16,id.len()==16,forall|j:int| 0<=j<i ==> identifier@[j]==id@[j],
            decreases 16-i,
        {identifier[i]=id[i];i+=1;}
        Ok(Self {prk,identifier,key_bytes:raw.len() as u8})
    }
    pub fn identifier(&self) -> (r:[u8;16]) ensures r@==self.master_identifier() {self.identifier}
    pub fn derive(&self,c:&Context,filesystem_uuid:[u8;16],filename:bool) -> (r:Result<Vec<u8>,Error>)
        ensures match r {Ok(v)=>c.context_policy().policy_fields().0==2 && c.context_policy().policy_key()==self.master_identifier()
            && (v.len()==16 || v.len()==32 || v.len()==64)
            && v@==self.derived_reference(*c,filesystem_uuid,filename),Err(_)=>true},
    {
        if c.policy.version!=2 {return Err(Error::Version);}
        if c.policy.key!=self.identifier {return Err(Error::KeyMismatch);}
        let mode=if filename {c.policy.filenames}else{c.policy.contents};let len=key_size(mode)?;
        let strength=if mode==5 || mode==6 || mode==7 || mode==8 {16u8}else{32u8};
        if self.key_bytes<strength {return Err(Error::KeySize);}
        let mut info=Vec::new();let domain;
        if c.policy.flags & 4!=0 {domain=3u8;info.push(mode);}
        else if c.policy.flags & 24!=0 {
            domain=if c.policy.flags & 8!=0 {4u8}else{6u8};info.push(mode);let mut i=0usize;
            while i<16 invariant i<=16,info@==seq![mode]+filesystem_uuid@.take(i as int), decreases 16-i, {info.push(filesystem_uuid[i]);i+=1;}
        } else {domain=2u8;let mut i=0usize;while i<16 invariant i<=16,info@==c.nonce@.take(i as int), decreases 16-i, {info.push(c.nonce[i]);i+=1;}}
        hkdf(self.prk.as_slice(),domain,info.as_slice(),len)
    }
    pub fn inode_hash(&self,inode:u64) -> (r:Result<u32,Error>)
        ensures match r {Ok(v)=>0<inode<=0xffff_ffff
            && v==inode_hash_reference(inode,fscrypt_kdf_reference(self.master_prk(),7,Seq::empty(),16)),Err(_)=>true},
    {
        if inode==0 || inode>0xffff_ffff {return Err(Error::Index);}
        let key=hkdf(self.prk.as_slice(),7,&[],16)?;Ok(siphash_inode(inode,key.as_slice()))
    }
    pub fn keyed_iv(&self,c:&Context,g:Geometry,inode:u64,index:u64,filename:bool) -> (r:Result<Vec<u8>,Error>)
        ensures match r {Ok(v)=>c.iv_admissible(g,inode,index,filename)
            && c.context_policy().policy_fields().0==2 && c.context_policy().policy_key()==self.master_identifier()
            && v.len()==mode_iv_bytes(if filename {c.context_policy().policy_fields().2}else{c.context_policy().policy_fields().1})
            && v@==iv_wire(*c,inode,index,filename,if c.context_policy().policy_fields().3 & 16!=0 {
                inode_hash_reference(inode,fscrypt_kdf_reference(self.master_prk(),7,Seq::empty(),16))
            }else{0u32}),Err(_)=>true},
    {
        if c.policy.version!=2 {return Err(Error::Version);}
        if c.policy.key!=self.identifier {return Err(Error::KeyMismatch);}
        let mode=if filename {c.policy.filenames}else{c.policy.contents};
        let strength=if mode==5 || mode==6 || mode==7 || mode==8 {16u8}else{32u8};
        if self.key_bytes<strength {return Err(Error::KeySize);}
        let h=if c.policy.flags & 16!=0 {self.inode_hash(inode)?}else{0};
        iv_with_hash(c,g,inode,index,filename,h)
    }
    pub fn directory_hash_key(&self,c:&Context) -> (r:Result<Vec<u8>,Error>)
        ensures match r {Ok(v)=>v.len()==16 && c.context_policy().policy_fields().0==2
            && c.context_policy().policy_key()==self.master_identifier()
            && v@==fscrypt_kdf_reference(self.master_prk(),5,c.context_nonce(),16),Err(_)=>true},
    {
        if c.policy.version!=2 {return Err(Error::Version);}
        if c.policy.key!=self.identifier {return Err(Error::KeyMismatch);}
        hkdf(self.prk.as_slice(),5,&c.nonce,16)
    }
}

}
