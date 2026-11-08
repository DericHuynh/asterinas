// SPDX-License-Identifier: MPL-2.0

//! Actual remaining SM4, AES-ESSIV, Adiantum and HCTR2 fscrypt transforms.
//! These are separate, implementation-first APIs. Existing mode dispatch and
//! filesystem admission remain unchanged. Encryption does not authenticate
//! names or data; constant-time compilation and physical erasure remain open.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{aes::AesKey,sm4::Sm4Key,bytes,crypto_sha2,adiantum,hctr2,
    fscrypt_context::{Context,Geometry,MasterKeyV2},
    fscrypt_cipher::{Role,MasterKeyRef}};

verus! {

pub const MAX_EXTRA_BYTES:usize=16777216;
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Error { KeyLength,WeakKey,Length,Unsupported,Policy,Binding,Index,Retired,Primitive,Hash,Name }

fn aes_key(raw:&[u8]) -> Result<AesKey,Error> {
    match AesKey::new_aes_key(raw) {Ok(v)=>Ok(v),Err(_)=>Err(Error::KeyLength)}
}
fn sm4_key(raw:&[u8]) -> Result<Sm4Key,Error> {
    match Sm4Key::new_sm4_key(raw) {Ok(v)=>Ok(v),Err(_)=>Err(Error::KeyLength)}
}
fn sm4_apply(key:&Sm4Key,b:[u8;16],decrypt:bool) -> Result<[u8;16],Error> {
    let changed=if decrypt {key.decrypt_sm4_block(b)}else{key.encrypt_sm4_block(b)};
    match changed {Ok(v)=>Ok(v),Err(_)=>Err(Error::Primitive)}
}
fn aes_apply(key:&AesKey,b:[u8;16],decrypt:bool) -> Result<[u8;16],Error> {
    let changed=if decrypt {key.decrypt_aes_block(b)}else{key.encrypt_aes_block(b)};
    match changed {Ok(v)=>Ok(v),Err(_)=>Err(Error::Primitive)}
}
fn block(raw:&[u8],at:usize) -> (r:[u8;16])
    requires at<=raw.len(),16<=raw.len()-at,
    ensures r@==raw@.subrange(at as int,at as int+16),
{
    let mut b=[0u8;16];let mut i=0usize;
    while i<16
        invariant i<=16,at<=raw.len(),16<=raw.len()-at,
            forall|j:int| 0<=j<i ==> b@[j]==raw@[at as int+j],
        decreases 16-i,
    {b[i]=raw[at+i];i+=1;}b
}
fn append(out:&mut Vec<u8>,raw:&[u8])
    ensures final(out)@==old(out)@+raw@,
{
    let ghost before=out@;let mut i=0usize;
    while i<raw.len()
        invariant i<=raw.len(),out@==before+raw@.take(i as int),
        decreases raw.len()-i,
    {out.push(raw[i]);i+=1;}
}
fn copy(raw:&[u8]) -> (r:Vec<u8>) ensures r@==raw@ {let mut out=Vec::new();append(&mut out,raw);out}
fn xor(a:[u8;16],b:[u8;16]) -> (r:[u8;16])
    ensures r@==Seq::new(16,|i:int|a@[i]^b@[i]),
{
    let mut out=[0u8;16];let mut i=0usize;
    while i<16
        invariant i<=16,forall|j:int| 0<=j<i ==> out@[j]==a@[j]^b@[j],
        decreases 16-i,
    {out[i]=a[i]^b[i];i+=1;}out
}
fn next_tweak(t:[u8;16]) -> [u8;16] {
    let mut out=[0u8;16];let mut carry=0u8;let mut i=0usize;
    while i<16 {out[i]=(t[i]<<1)|carry;carry=t[i]>>7;i+=1;}
    out[0]^=0x87u8 & 0u8.wrapping_sub(carry);out
}
fn sm4_xex(key:&Sm4Key,b:[u8;16],t:[u8;16],decrypt:bool) -> Result<[u8;16],Error> {
    Ok(xor(sm4_apply(key,xor(b,t),decrypt)?,t))
}
fn sm4_xts(raw_key:&[u8],iv:[u8;16],input:&[u8],decrypt:bool) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==input.len(),Err(_)=>true},
{
    if raw_key.len()!=32 {return Err(Error::KeyLength);}
    if bytes::equal(&raw_key[..16],&raw_key[16..]) {return Err(Error::WeakKey);}
    if input.len()<16 || input.len()>MAX_EXTRA_BYTES {return Err(Error::Length);}
    let key=sm4_key(&raw_key[..16])?;let tweak_key=sm4_key(&raw_key[16..])?;
    let mut tweak=sm4_apply(&tweak_key,iv,false)?;
    let remainder=input.len()%16;let whole=input.len()/16;let normal=if remainder==0 {whole}else{whole-1};
    let mut out=Vec::new();let mut i=0usize;
    while i<normal {
        append(&mut out,&sm4_xex(&key,block(input,i*16),tweak,decrypt)?);
        tweak=next_tweak(tweak);i+=1;
    }
    if remainder!=0 {
        let at=normal*16;let next=next_tweak(tweak);
        if decrypt {
            let pp=sm4_xex(&key,block(input,at),next,true)?;let mut cc=pp;let mut j=0usize;
            while j<remainder {cc[j]=input[at+16+j];j+=1;}
            append(&mut out,&sm4_xex(&key,cc,tweak,true)?);append(&mut out,&pp[..remainder]);
        } else {
            let cc=sm4_xex(&key,block(input,at),tweak,false)?;let mut pp=cc;let mut j=0usize;
            while j<remainder {pp[j]=input[at+16+j];j+=1;}
            append(&mut out,&sm4_xex(&key,pp,next,false)?);append(&mut out,&cc[..remainder]);
        }
    }
    Ok(out)
}
pub fn encrypt_sm4_xts(raw_key:&[u8],iv:[u8;16],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==input.len(),Err(_)=>true},
{sm4_xts(raw_key,iv,input,false)}
pub fn decrypt_sm4_xts(raw_key:&[u8],iv:[u8;16],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==input.len(),Err(_)=>true},
{sm4_xts(raw_key,iv,input,true)}

fn sm4_cts(raw_key:&[u8],iv:[u8;16],input:&[u8],decrypt:bool) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==input.len(),Err(_)=>true},
{
    if input.len()<16 || input.len()>MAX_EXTRA_BYTES {return Err(Error::Length);}
    let key=sm4_key(raw_key)?;let mut out=Vec::new();let mut chain=iv;
    if input.len()==16 {
        let result=if decrypt {xor(sm4_apply(&key,block(input,0),true)?,iv)}
            else {sm4_apply(&key,xor(block(input,0),iv),false)?};
        append(&mut out,&result);return Ok(out);
    }
    let prefix=((input.len()-1)/16-1)*16;let last=input.len()-prefix-16;let mut at=0usize;
    while at<prefix {
        let b=block(input,at);
        if decrypt {append(&mut out,&xor(sm4_apply(&key,b,true)?,chain));chain=b;}
        else {let c=sm4_apply(&key,xor(b,chain),false)?;append(&mut out,&c);chain=c;}
        at+=16;
    }
    if decrypt {
        let d=sm4_apply(&key,block(input,prefix),true)?;let mut stolen=d;let mut tail=[0u8;16];let mut i=0usize;
        while i<last {stolen[i]=input[prefix+16+i];tail[i]=d[i]^stolen[i];i+=1;}
        append(&mut out,&xor(sm4_apply(&key,stolen,true)?,chain));append(&mut out,&tail[..last]);
    } else {
        let stolen=sm4_apply(&key,xor(block(input,prefix),chain),false)?;let mut tail=[0u8;16];let mut i=0usize;
        while i<last {tail[i]=input[prefix+16+i];i+=1;}
        append(&mut out,&sm4_apply(&key,xor(tail,stolen),false)?);append(&mut out,&stolen[..last]);
    }
    Ok(out)
}
pub fn encrypt_sm4_cts(raw_key:&[u8],iv:[u8;16],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==input.len(),Err(_)=>true},
{sm4_cts(raw_key,iv,input,false)}
pub fn decrypt_sm4_cts(raw_key:&[u8],iv:[u8;16],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==input.len(),Err(_)=>true},
{sm4_cts(raw_key,iv,input,true)}

fn aes128_essiv(raw_key:&[u8],initial_iv:[u8;16],input:&[u8],decrypt:bool) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==input.len(),Err(_)=>true},
{
    if raw_key.len()!=16 {return Err(Error::KeyLength);}
    if input.len()<16 || input.len()>MAX_EXTRA_BYTES || input.len()%16!=0 {return Err(Error::Length);}
    let salt=match crypto_sha2::sha256(raw_key) {Ok(v)=>v,Err(_)=>return Err(Error::Hash)};
    let iv_key=aes_key(salt.as_slice())?;let key=aes_key(raw_key)?;
    let mut chain=aes_apply(&iv_key,initial_iv,false)?;let mut out=Vec::new();let mut at=0usize;
    while at<input.len() {
        let b=block(input,at);
        if decrypt {append(&mut out,&xor(aes_apply(&key,b,true)?,chain));chain=b;}
        else {let c=aes_apply(&key,xor(b,chain),false)?;append(&mut out,&c);chain=c;}
        at+=16;
    }
    Ok(out)
}
pub fn encrypt_aes128_essiv(raw_key:&[u8],iv:[u8;16],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==input.len(),Err(_)=>true},
{aes128_essiv(raw_key,iv,input,false)}
pub fn decrypt_aes128_essiv(raw_key:&[u8],iv:[u8;16],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==input.len(),Err(_)=>true},
{aes128_essiv(raw_key,iv,input,true)}

struct Secret {bytes:[u8;32],length:u8,retired:bool}
pub struct ExtraCipherKey {
    context:Context,uuid:[u8;16],inode:u64,geometry:Geometry,role:Role,mode:u8,unit_bits:u8,name_iv:[u8;32],secret:Secret,
}
fn same_role(a:Role,b:Role) -> (r:bool) ensures r==(a==b) {
    matches!((a,b),(Role::Data,Role::Data)|(Role::Name,Role::Name))
}
spec fn mode_for(c:Context,role:Role) -> u8 {
    if role==Role::Data {c.context_policy().policy_fields().1}else{c.context_policy().policy_fields().2}
}
spec fn mode_bytes(mode:u8,role:Role) -> nat {
    if role==Role::Data && mode==5 {16}
    else if role==Role::Data && mode==7 {32}
    else if role==Role::Name && mode==8 {16}
    else if mode==9 || (role==Role::Name && mode==10) {32}
    else {0}
}
fn selected(context:&Context,role:Role) -> (r:u8) ensures r==mode_for(*context,role) {
    let (_,contents,names,_,_)=context.policy().fields();if matches!(role,Role::Data) {contents}else{names}
}
fn extra_size(mode:u8,role:Role) -> (r:Result<usize,Error>)
    ensures match r {Ok(n)=>n==mode_bytes(mode,role) && (n==16 || n==32),Err(_)=>mode_bytes(mode,role)==0},
{
    if matches!(role,Role::Data) && mode==5 {Ok(16)}
    else if matches!(role,Role::Data) && mode==7 {Ok(32)}
    else if matches!(role,Role::Name) && mode==8 {Ok(16)}
    else if mode==9 || (matches!(role,Role::Name) && mode==10) {Ok(32)}
    else {Err(Error::Unsupported)}
}
fn secret(raw:&[u8]) -> (r:Result<Secret,Error>)
    ensures match r {Ok(v)=>!v.retired && v.length==raw.len()
        && v.bytes@.take(raw.len() as int)==raw@,Err(_)=>raw.len()!=16 && raw.len()!=32},
{
    if raw.len()!=16 && raw.len()!=32 {return Err(Error::KeyLength);}
    let mut bytes=[0u8;32];let mut i=0usize;
    while i<raw.len()
        invariant i<=raw.len()<=32,forall|j:int| 0<=j<i ==> bytes@[j]==raw@[j],
        decreases raw.len()-i,
    {bytes[i]=raw[i];i+=1;}
    Ok(Secret {bytes,length:raw.len() as u8,retired:false})
}
pub closed spec fn prepared_master_iv_reference(master:&MasterKeyV2,c:Context,inode:u64,filename:bool) -> Seq<u8> {
    let hash=if c.context_policy().policy_fields().3 & 16!=0 {
        crate::fscrypt_context::inode_hash_reference(inode,
            crate::fscrypt_context::fscrypt_kdf_reference(master.master_prk(),7,Seq::empty(),16))
    }else{0u32};
    let raw=crate::fscrypt_context::iv_wire(c,inode,0,filename,hash);
    raw+Seq::new((32-raw.len()) as nat,|i:int|0u8)
}
pub closed spec fn prepared_legacy_iv_reference(c:Context,inode:u64,filename:bool) -> Seq<u8> {
    let raw=crate::fscrypt_context::iv_wire(c,inode,0,filename,0);
    raw+Seq::new((32-raw.len()) as nat,|i:int|0u8)
}
fn prepared_iv(raw:&[u8]) -> (r:Result<[u8;32],Error>)
    ensures match r {Ok(v)=>(raw.len()==16 || raw.len()==32)
        && v@==raw@+Seq::new((32-raw.len()) as nat,|i:int|0u8),Err(_)=>true},
{
    if raw.len()!=16 && raw.len()!=32 {return Err(Error::Index);}
    let mut out=[0u8;32];let mut i=0usize;
    while i<raw.len()
        invariant i<=raw.len()<=32,forall|j:int| 0<=j<32 ==> out@[j]==if j<i {raw@[j]}else{0u8},
        decreases raw.len()-i,
    {out[i]=raw[i];i+=1;}Ok(out)
}
impl ExtraCipherKey {
    pub closed spec fn extra_valid(&self) -> bool {
        if self.secret.retired {self.secret.length==0 && forall|i:int| 0<=i<32 ==> self.secret.bytes@[i]==0}
        else {
            self.inode>0 && 9<=self.unit_bits<=self.geometry.filesystem_block_bits<=16
                && self.context.context_policy().accepts_geometry(self.geometry)
                && self.mode==mode_for(self.context,self.role)
                && mode_bytes(self.mode,self.role)>0 && self.secret.length==mode_bytes(self.mode,self.role)
        }
    }
    pub closed spec fn extra_bound(&self,uuid:[u8;16],inode:u64,context:&Context,role:Role) -> bool {
        !self.secret.retired && self.uuid==uuid && self.inode==inode && self.role==role
            && self.context.context_encoding()==context.context_encoding()
    }
    pub closed spec fn extra_retired(&self) -> bool {self.secret.retired}
    pub closed spec fn extra_material(&self) -> Seq<u8> {self.secret.bytes@.take(self.secret.length as int)}
    pub closed spec fn extra_binding_view(&self) -> (u64,Role,Seq<u8>,[u8;16]) {
        (self.inode,self.role,self.context.context_encoding(),self.uuid)
    }
    pub closed spec fn extra_prepared_iv(&self) -> Seq<u8> {self.name_iv@}
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {self.extra_valid()}
    pub fn extra_from_v2(master:&MasterKeyV2,context:Context,uuid:[u8;16],inode:u64,geometry:Geometry,role:Role) -> (r:Result<Self,Error>)
        ensures match r {Ok(k)=>k.extra_valid() && k.extra_bound(uuid,inode,&context,role)
            && context.context_policy().policy_fields().0==2
            && k.extra_material()==master.derived_reference(context,uuid,role==Role::Name)
            && k.extra_prepared_iv()==prepared_master_iv_reference(master,context,inode,role==Role::Name),Err(_)=>true},
    {
        let (version,_,_,flags,_)=context.policy().fields();
        if version!=2 {return Err(Error::Binding);}
        let mode=selected(&context,role);let size=extra_size(mode,role)?;
        if (flags & 4!=0 && mode!=9) || (flags & 24!=0 && mode!=10) {return Err(Error::Policy);}
        let unit_bits=match context.policy().validate(geometry){Ok(v)=>v,Err(_)=>return Err(Error::Policy)};
        let key=match master.derive(&context,uuid,matches!(role,Role::Name)){Ok(v)=>v,Err(_)=>return Err(Error::Binding)};
        if key.len()!=size {return Err(Error::KeyLength);}
        if mode==7 && bytes::equal(&key[..16],&key[16..]) {return Err(Error::WeakKey);}
        let raw_iv=match master.keyed_iv(&context,geometry,inode,0,matches!(role,Role::Name)){Ok(v)=>v,Err(_)=>return Err(Error::Binding)};
        let name_iv=prepared_iv(raw_iv.as_slice())?;
        Ok(Self {context,uuid,inode,geometry,role,mode,unit_bits,name_iv,secret:secret(key.as_slice())?})
    }
    pub fn extra_from_v1(raw_master:&[u8],descriptor:&[u8],context:Context,uuid:[u8;16],inode:u64,geometry:Geometry,role:Role) -> (r:Result<Self,Error>)
        ensures match r {Ok(k)=>k.extra_valid() && k.extra_bound(uuid,inode,&context,role)
            && context.context_policy().policy_fields().0==0 && context.context_policy().policy_key()==descriptor@
            && k.extra_prepared_iv()==prepared_legacy_iv_reference(context,inode,role==Role::Name),Err(_)=>true},
    {
        let (version,_,_,flags,_)=context.policy().fields();
        if version!=0 || descriptor.len()!=8 || !bytes::equal(context.policy().key_specifier().as_slice(),descriptor) {return Err(Error::Binding);}
        let mode=selected(&context,role);let size=extra_size(mode,role)?;
        if mode!=5 && mode!=9 {return Err(Error::Unsupported);}
        if flags & 24!=0 || (flags & 4!=0 && mode!=9) {return Err(Error::Policy);}
        if raw_master.len()<size || raw_master.len()>64 {return Err(Error::KeyLength);}
        let unit_bits=match context.policy().validate(geometry){Ok(v)=>v,Err(_)=>return Err(Error::Policy)};
        let raw_iv=match context.context_iv(geometry,inode,0,matches!(role,Role::Name)){Ok(v)=>v,Err(_)=>return Err(Error::Binding)};
        let name_iv=prepared_iv(raw_iv.as_slice())?;
        let mut key=Vec::new();
        if flags & 4!=0 {append(&mut key,&raw_master[..size]);}
        else {
            let nonce=context.nonce();let kdf=aes_key(&nonce)?;let mut at=0usize;
            while at<size
                invariant at<=size<=32,at%16==0,size%16==0,key.len()==at,raw_master.len()>=size,
                decreases size-at,
            {append(&mut key,&aes_apply(&kdf,block(raw_master,at),false)?);at+=16;}
        }
        Ok(Self {context,uuid,inode,geometry,role,mode,unit_bits,name_iv,secret:secret(key.as_slice())?})
    }
    pub fn extra_binding(&self) -> (r:(u64,Role,Vec<u8>,[u8;16]))
        ensures (r.0,r.1,r.2@,r.3)==self.extra_binding_view(),
    {(self.inode,self.role,self.context.encode_context(),self.uuid)}
    fn check(&self,uuid:[u8;16],inode:u64,context:&Context,role:Role) -> (r:Result<(),Error>)
        ensures r.is_ok()==self.extra_bound(uuid,inode,context,role),
    {
        proof {use_type_invariant(self);}
        if self.secret.retired {return Err(Error::Retired);}
        if !bytes::equal(&self.uuid,&uuid) || self.inode!=inode || !same_role(self.role,role)
            || !bytes::equal(self.context.encode_context().as_slice(),context.encode_context().as_slice()) {return Err(Error::Binding);}
        let size=extra_size(self.mode,self.role)?;
        if self.secret.length as usize!=size || self.unit_bits<9 || self.unit_bits>16 || self.inode==0 {return Err(Error::Binding);}
        Ok(())
    }
    fn full_iv(&self,index:u64) -> Result<[u8;32],Error> {
        if matches!(self.role,Role::Name) {
            if index!=0 {return Err(Error::Index);}return Ok(self.name_iv);
        }
        let raw=match self.context.context_iv(self.geometry,self.inode,index,false){Ok(v)=>v,Err(_)=>return Err(Error::Index)};
        prepared_iv(raw.as_slice())
    }
    fn iv(&self,index:u64) -> Result<[u8;16],Error> {
        let iv=self.full_iv(index)?;Ok(block(&iv,0))
    }
    pub fn encrypt_extra_data(&self,uuid:[u8;16],inode:u64,context:&Context,index:u64,input:&[u8]) -> (r:Result<Vec<u8>,Error>)
        ensures self.extra_valid(),match r {Ok(v)=>self.extra_bound(uuid,inode,context,Role::Data)
            && v.len()==input.len(),Err(_)=>true},
    {
        proof {use_type_invariant(self);}
        self.check(uuid,inode,context,Role::Data)?;
        if input.len()!=1usize<<self.unit_bits {return Err(Error::Length);}
        let raw=&self.secret.bytes[..self.secret.length as usize];let iv=self.iv(index)?;
        if self.mode==5 {encrypt_aes128_essiv(raw,iv,input)}else if self.mode==7 {encrypt_sm4_xts(raw,iv,input)}
        else if self.mode==9 {match adiantum::encrypt_adiantum_xchacha12_aes(raw,self.full_iv(index)?,input){Ok(v)=>Ok(v),Err(_)=>Err(Error::Primitive)}}else{Err(Error::Unsupported)}
    }
    pub fn decrypt_extra_data(&self,uuid:[u8;16],inode:u64,context:&Context,index:u64,input:&[u8]) -> (r:Result<Vec<u8>,Error>)
        ensures self.extra_valid(),match r {Ok(v)=>self.extra_bound(uuid,inode,context,Role::Data)
            && v.len()==input.len(),Err(_)=>true},
    {
        proof {use_type_invariant(self);}
        self.check(uuid,inode,context,Role::Data)?;
        if input.len()!=1usize<<self.unit_bits {return Err(Error::Length);}
        let raw=&self.secret.bytes[..self.secret.length as usize];let iv=self.iv(index)?;
        if self.mode==5 {decrypt_aes128_essiv(raw,iv,input)}else if self.mode==7 {decrypt_sm4_xts(raw,iv,input)}
        else if self.mode==9 {match adiantum::decrypt_adiantum_xchacha12_aes(raw,self.full_iv(index)?,input){Ok(v)=>Ok(v),Err(_)=>Err(Error::Primitive)}}else{Err(Error::Unsupported)}
    }
    pub fn encrypt_extra_name(&self,uuid:[u8;16],inode:u64,context:&Context,input:&[u8],maximum:u32) -> (r:Result<Vec<u8>,Error>)
        ensures self.extra_valid(),match r {Ok(v)=>self.extra_bound(uuid,inode,context,Role::Name)
            && v.len()<=255,Err(_)=>true},
    {
        proof {use_type_invariant(self);}
        self.check(uuid,inode,context,Role::Name)?;
        if input.len()==0 || input.len()>255 || maximum<16 || maximum>255 {return Err(Error::Name);}
        let mut i=0usize;while i<input.len(){if input[i]==0 || input[i]==47{return Err(Error::Name);}i+=1;}
        if bytes::equal(input,b".") || bytes::equal(input,b"..") {return Ok(copy(input));}
        let length=match self.context.policy().padded_filename_len(input.len() as u32,maximum){Ok(v)=>v as usize,Err(_)=>return Err(Error::Name)};
        let mut padded=copy(input);while padded.len()<length {padded.push(0);}
        let raw=&self.secret.bytes[..self.secret.length as usize];
        if self.mode==8 {encrypt_sm4_cts(raw,self.iv(0)?,padded.as_slice())}
        else if self.mode==9 {match adiantum::encrypt_adiantum_xchacha12_aes(raw,self.full_iv(0)?,padded.as_slice()){Ok(v)=>Ok(v),Err(_)=>Err(Error::Primitive)}}
        else if self.mode==10 {match hctr2::encrypt_aes256_hctr2(raw,self.full_iv(0)?,padded.as_slice()){Ok(v)=>Ok(v),Err(_)=>Err(Error::Primitive)}}
        else {Err(Error::Unsupported)}
    }
    pub fn decrypt_extra_name(&self,uuid:[u8;16],inode:u64,context:&Context,input:&[u8]) -> (r:Result<Vec<u8>,Error>)
        ensures self.extra_valid(),match r {Ok(v)=>self.extra_bound(uuid,inode,context,Role::Name)
            && v.len()<=255,Err(_)=>true},
    {
        proof {use_type_invariant(self);}
        self.check(uuid,inode,context,Role::Name)?;
        if bytes::equal(input,b".") || bytes::equal(input,b"..") {return Ok(copy(input));}
        if input.len()<16 || input.len()>255 {return Err(Error::Name);}
        let raw=&self.secret.bytes[..self.secret.length as usize];
        let padded=if self.mode==8 {decrypt_sm4_cts(raw,self.iv(0)?,input)?}
        else if self.mode==9 {match adiantum::decrypt_adiantum_xchacha12_aes(raw,self.full_iv(0)?,input){Ok(v)=>v,Err(_)=>return Err(Error::Primitive)}}
        else if self.mode==10 {match hctr2::decrypt_aes256_hctr2(raw,self.full_iv(0)?,input){Ok(v)=>v,Err(_)=>return Err(Error::Primitive)}}
        else {return Err(Error::Unsupported)};
        let mut end=0usize;while end<padded.len() && padded[end]!=0 {if padded[end]==47{return Err(Error::Name);}end+=1;}
        if end==0 {return Err(Error::Name);}Ok(copy(&padded[..end]))
    }
    pub fn retire_extra_cipher(&mut self)
        ensures final(self).extra_valid(),final(self).extra_retired(),final(self).extra_material()==Seq::<u8>::empty(),
            final(self).extra_binding_view()==old(self).extra_binding_view(),
        opens_invariants none
        no_unwind
    {self.secret=Secret {bytes:[0u8;32],length:0,retired:true};}
}
impl Drop for ExtraCipherKey {
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {self.retire_extra_cipher();}
}
pub fn prepare_extra_cipher(master:MasterKeyRef<'_>,context:Context,uuid:[u8;16],inode:u64,geometry:Geometry,role:Role) -> (r:Result<ExtraCipherKey,Error>)
    ensures match r {Ok(k)=>k.extra_valid() && k.extra_bound(uuid,inode,&context,role),Err(_)=>true},
{
    match master {
        MasterKeyRef::V1 {raw,descriptor} => ExtraCipherKey::extra_from_v1(raw,descriptor,context,uuid,inode,geometry,role),
        MasterKeyRef::V2(master) => ExtraCipherKey::extra_from_v2(master,context,uuid,inode,geometry,role),
    }
}

/// One owned key interface for every cipher pair currently accepted by the
/// policy codec. This dispatch API does not grant inode or VFS authority.
pub enum SupportedCipher { Common(crate::fscrypt_cipher::CipherKey), Extra(ExtraCipherKey) }
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum SupportedError {Common(crate::fscrypt_cipher::Error),Extra(Error)}
impl SupportedCipher {
    pub closed spec fn supported_bound(&self,uuid:[u8;16],inode:u64,c:&Context,role:Role) -> bool {
        match self {
            Self::Common(k)=>k.cipher_binding(uuid,inode,c,role),
            Self::Extra(k)=>k.extra_bound(uuid,inode,c,role),
        }
    }
    pub closed spec fn supported_retired(&self) -> bool {
        match self {Self::Common(k)=>k.cipher_retired(),Self::Extra(k)=>k.extra_retired()}
    }
    pub closed spec fn supported_binding_view(&self) -> (u64,Role,Seq<u8>,[u8;16]) {
        match self {Self::Common(k)=>k.binding_view(),Self::Extra(k)=>k.extra_binding_view()}
    }
    pub fn supported_binding(&self) -> (r:(u64,Role,Vec<u8>,[u8;16]))
        ensures (r.0,r.1,r.2@,r.3)==self.supported_binding_view(),
    {match self {Self::Common(k)=>k.binding(),Self::Extra(k)=>k.extra_binding()}}
    pub fn encrypt_supported_data(&self,uuid:[u8;16],inode:u64,c:&Context,index:u64,input:&[u8]) -> (r:Result<Vec<u8>,SupportedError>)
        ensures match r {Ok(v)=>self.supported_bound(uuid,inode,c,Role::Data) && v.len()==input.len(),Err(_)=>true},
    {
        match self {
            Self::Common(k)=>match k.encrypt_data(uuid,inode,c,index,input){Ok(v)=>Ok(v),Err(e)=>Err(SupportedError::Common(e))},
            Self::Extra(k)=>match k.encrypt_extra_data(uuid,inode,c,index,input){Ok(v)=>Ok(v),Err(e)=>Err(SupportedError::Extra(e))},
        }
    }
    pub fn decrypt_supported_data(&self,uuid:[u8;16],inode:u64,c:&Context,index:u64,input:&[u8]) -> (r:Result<Vec<u8>,SupportedError>)
        ensures match r {Ok(v)=>self.supported_bound(uuid,inode,c,Role::Data) && v.len()==input.len(),Err(_)=>true},
    {
        match self {
            Self::Common(k)=>match k.decrypt_data(uuid,inode,c,index,input){Ok(v)=>Ok(v),Err(e)=>Err(SupportedError::Common(e))},
            Self::Extra(k)=>match k.decrypt_extra_data(uuid,inode,c,index,input){Ok(v)=>Ok(v),Err(e)=>Err(SupportedError::Extra(e))},
        }
    }
    pub fn encrypt_supported_name(&self,uuid:[u8;16],inode:u64,c:&Context,input:&[u8],maximum:u32) -> (r:Result<Vec<u8>,SupportedError>)
        ensures match r {Ok(v)=>self.supported_bound(uuid,inode,c,Role::Name) && v.len()<=255,Err(_)=>true},
    {
        match self {
            Self::Common(k)=>match k.encrypt_name(uuid,inode,c,input,maximum){Ok(v)=>Ok(v),Err(e)=>Err(SupportedError::Common(e))},
            Self::Extra(k)=>match k.encrypt_extra_name(uuid,inode,c,input,maximum){Ok(v)=>Ok(v),Err(e)=>Err(SupportedError::Extra(e))},
        }
    }
    pub fn decrypt_supported_name(&self,uuid:[u8;16],inode:u64,c:&Context,input:&[u8]) -> (r:Result<Vec<u8>,SupportedError>)
        ensures match r {Ok(v)=>self.supported_bound(uuid,inode,c,Role::Name) && v.len()<=255,Err(_)=>true},
    {
        match self {
            Self::Common(k)=>match k.decrypt_name(uuid,inode,c,input){Ok(v)=>Ok(v),Err(e)=>Err(SupportedError::Common(e))},
            Self::Extra(k)=>match k.decrypt_extra_name(uuid,inode,c,input){Ok(v)=>Ok(v),Err(e)=>Err(SupportedError::Extra(e))},
        }
    }
    pub fn retire_supported_cipher(&mut self)
        ensures final(self).supported_retired(),
        opens_invariants none
        no_unwind
    {match self {Self::Common(k)=>k.retire_cipher(),Self::Extra(k)=>k.retire_extra_cipher()}}
}
pub fn prepare_supported_cipher(master:MasterKeyRef<'_>,context:Context,uuid:[u8;16],inode:u64,geometry:Geometry,role:Role) -> (r:Result<SupportedCipher,SupportedError>)
    ensures match r {Ok(k)=>k.supported_bound(uuid,inode,&context,role),Err(_)=>true},
{
    let mode=selected(&context,role);
    if mode==1 || mode==4 || mode==6 {
        let result=match master {
            MasterKeyRef::V1 {raw,descriptor}=>crate::fscrypt_cipher::CipherKey::from_v1(raw,descriptor,context,uuid,inode,geometry,role),
            MasterKeyRef::V2(k)=>crate::fscrypt_cipher::CipherKey::from_v2(k,context,uuid,inode,geometry,role),
        };
        match result {Ok(k)=>Ok(SupportedCipher::Common(k)),Err(e)=>Err(SupportedError::Common(e))}
    }else{
        match prepare_extra_cipher(master,context,uuid,inode,geometry,role){Ok(k)=>Ok(SupportedCipher::Extra(k)),Err(e)=>Err(SupportedError::Extra(e))}
    }
}

}
