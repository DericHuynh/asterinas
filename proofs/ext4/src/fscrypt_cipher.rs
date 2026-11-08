// SPDX-License-Identifier: MPL-2.0

//! Executable common fscrypt AES modes and inode/context-bound key handles.
//! AES-XTS and CBC-CS3 execute real transforms. Other Linux modes return an
//! explicit unsupported result. Keys are logically retired and overwritten on
//! drop; physical erasure, side channels, provisioning and VFS authority remain
//! refinement boundaries. These implementation-first paths await proof.

use vstd::prelude::*;
use crate::{aes::AesKey,bytes,fscrypt_context::{Context,Geometry,MasterKeyV2}};

verus! {

pub const MAX_CIPHER_BYTES:usize=16777216;
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Error { KeyLength,WeakKey,Length,Unsupported,Policy,Binding,Index,Retired,Primitive,Name }

fn aes_key(raw:&[u8]) -> Result<AesKey,Error> {
    match AesKey::new_aes_key(raw) {Ok(k)=>Ok(k),Err(_)=>Err(Error::KeyLength)}
}
fn enc(key:&AesKey,b:[u8;16]) -> Result<[u8;16],Error> {
    match key.encrypt_aes_block(b) {Ok(v)=>Ok(v),Err(_)=>Err(Error::Primitive)}
}
fn dec(key:&AesKey,b:[u8;16]) -> Result<[u8;16],Error> {
    match key.decrypt_aes_block(b) {Ok(v)=>Ok(v),Err(_)=>Err(Error::Primitive)}
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
fn append(out:&mut Vec<u8>,b:&[u8])
    ensures final(out)@==old(out)@+b@,
{
    let ghost before=out@;let mut i=0usize;
    while i<b.len()
        invariant i<=b.len(),out@==before+b@.take(i as int),
        decreases b.len()-i,
    {out.push(b[i]);i+=1;}
}
fn copy(raw:&[u8]) -> (r:Vec<u8>) ensures r@==raw@ {let mut v=Vec::new();append(&mut v,raw);v}
fn xor(a:[u8;16],b:[u8;16]) -> (r:[u8;16])
    ensures forall|i:int| 0<=i<16 ==> r@[i]==a@[i]^b@[i],
{
    let mut v=[0u8;16];let mut i=0usize;
    while i<16
        invariant i<=16,forall|j:int| 0<=j<i ==> v@[j]==a@[j]^b@[j],
        decreases 16-i,
    {v[i]=a[i]^b[i];i+=1;}v
}
spec fn tweak_double(t:Seq<u8>) -> Seq<u8> {
    Seq::new(16,|i:int| {
        let shifted=(t[i]<<1)|(if i==0 {0u8}else{t[i-1]>>7});
        if i==0 {shifted^(if t[15]>>7==0 {0u8}else{0x87u8})}else{shifted}
    })
}
fn mul_tweak(t:[u8;16]) -> (r:[u8;16])
    ensures r@==tweak_double(t@),
{
    let mut out=[0u8;16];let mut carry=0u8;let mut i=0usize;
    while i<16
        invariant i<=16,carry==if i==0 {0u8}else{t@[i as int-1]>>7},
            forall|j:int| 0<=j<i ==> out@[j]==(t@[j]<<1)|(if j==0 {0u8}else{t@[j-1]>>7}),
        decreases 16-i,
    {out[i]=(t[i]<<1)|carry;carry=t[i]>>7;i+=1;}
    let mask=0u8.wrapping_sub(carry);
    proof {
        assert(carry==0 || carry==1) by(bit_vector);
        assert(mask==if carry==0 {0u8}else{255u8});
    }
    out[0]^=0x87u8 & mask;out
}
fn xex(key:&AesKey,input:[u8;16],tweak:[u8;16],decrypt:bool) -> Result<[u8;16],Error> {
    let whitened=xor(input,tweak);let changed=if decrypt {dec(key,whitened)?}else{enc(key,whitened)?};Ok(xor(changed,tweak))
}
fn xts(key:&[u8],iv:[u8;16],input:&[u8],decrypt:bool) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==input.len(),Err(_)=>true},
{
    if key.len()!=64 {return Err(Error::KeyLength);}
    if bytes::equal(&key[..32],&key[32..]) {return Err(Error::WeakKey);}
    if input.len()<16 || input.len()>MAX_CIPHER_BYTES {return Err(Error::Length);}
    let data_key=aes_key(&key[..32])?;let tweak_key=aes_key(&key[32..])?;
    let mut tweak=enc(&tweak_key,iv)?;let remainder=input.len()%16;
    let whole=input.len()/16;let normal=if remainder==0 {whole}else{whole-1};
    let mut out=Vec::new();let mut i=0usize;
    while i<normal
        invariant i<=normal,normal<=whole<=1048576,remainder<16,
            input.len()==whole*16+remainder,
            normal==if remainder==0 {whole}else{(whole-1) as usize},
            input.len()>=16,out.len()==i*16,
        decreases normal-i,
    {
        let changed=xex(&data_key,block(input,i*16),tweak,decrypt)?;append(&mut out,&changed);
        tweak=mul_tweak(tweak);i+=1;
    }
    if remainder!=0 {
        let at=normal*16;let next=mul_tweak(tweak);
        if decrypt {
            let pp=xex(&data_key,block(input,at),next,true)?;
            let mut cc=pp;let mut j=0usize;
            while j<remainder
                invariant j<=remainder<16,at+16+remainder==input.len(),
                decreases remainder-j,
            {cc[j]=input[at+16+j];j+=1;}
            let previous=xex(&data_key,cc,tweak,true)?;append(&mut out,&previous);append(&mut out,&pp[..remainder]);
        } else {
            let cc=xex(&data_key,block(input,at),tweak,false)?;
            let mut pp=cc;let mut j=0usize;
            while j<remainder
                invariant j<=remainder<16,at+16+remainder==input.len(),
                decreases remainder-j,
            {pp[j]=input[at+16+j];j+=1;}
            let previous=xex(&data_key,pp,next,false)?;append(&mut out,&previous);append(&mut out,&cc[..remainder]);
        }
    }
    Ok(out)
}
pub fn encrypt_xts_aes256(key:&[u8],iv:[u8;16],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==input.len(),Err(_)=>true},
{xts(key,iv,input,false)}
pub fn decrypt_xts_aes256(key:&[u8],iv:[u8;16],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==input.len(),Err(_)=>true},
{xts(key,iv,input,true)}

fn cbc_cs3(key:&[u8],iv:[u8;16],input:&[u8],decrypt:bool) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==input.len(),Err(_)=>true},
{
    if input.len()<16 || input.len()>MAX_CIPHER_BYTES {return Err(Error::Length);}
    let cipher=aes_key(key)?;let mut out=Vec::new();let mut chain=iv;
    if input.len()==16 {
        let result=if decrypt {xor(dec(&cipher,block(input,0))?,iv)}else{enc(&cipher,xor(block(input,0),iv))?};
        append(&mut out,&result);return Ok(out);
    }
    let prefix=((input.len()-1)/16-1)*16;let last=input.len()-prefix-16;let mut at=0usize;
    while at<prefix
        invariant at<=prefix,at%16==0,prefix%16==0,0<last<=16,
            prefix+16+last==input.len(),input.len()<=MAX_CIPHER_BYTES,
            out.len()==at,
        decreases prefix-at,
    {
        let b=block(input,at);
        if decrypt {let p=xor(dec(&cipher,b)?,chain);append(&mut out,&p);chain=b;}
        else {let c=enc(&cipher,xor(b,chain))?;append(&mut out,&c);chain=c;}
        at+=16;
    }
    if decrypt {
        let d=dec(&cipher,block(input,prefix))?;let mut stolen=d;let mut tail=[0u8;16];let mut i=0usize;
        while i<last
            invariant i<=last<=16,prefix+16+last==input.len(),
            decreases last-i,
        {stolen[i]=input[prefix+16+i];tail[i]=d[i]^stolen[i];i+=1;}
        let previous=xor(dec(&cipher,stolen)?,chain);append(&mut out,&previous);append(&mut out,&tail[..last]);
    } else {
        let stolen=enc(&cipher,xor(block(input,prefix),chain))?;
        let mut tail=[0u8;16];let mut i=0usize;while i<last
            invariant i<=last<=16,prefix+16+last==input.len(),
            decreases last-i,
        {tail[i]=input[prefix+16+i];i+=1;}
        let final_block=enc(&cipher,xor(tail,stolen))?;append(&mut out,&final_block);append(&mut out,&stolen[..last]);
    }
    Ok(out)
}
pub fn encrypt_cbc_cs3_aes(key:&[u8],iv:[u8;16],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==input.len(),Err(_)=>true},
{cbc_cs3(key,iv,input,false)}
pub fn decrypt_cbc_cs3_aes(key:&[u8],iv:[u8;16],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures match r {Ok(v)=>v.len()==input.len(),Err(_)=>true},
{cbc_cs3(key,iv,input,true)}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Role { Data, Name }
pub struct CipherKey {
    context:Context,filesystem_uuid:[u8;16],inode:u64,geometry:Geometry,
    role:Role,mode:u8,unit_bits:u8,hashed_inode:u32,key:Vec<u8>,retired:bool,
}
spec fn selected_mode(c:&Context,role:Role) -> u8 {
    if role==Role::Data {c.context_policy().policy_fields().1}else{c.context_policy().policy_fields().2}
}
spec fn supported_bytes(mode:u8,role:Role) -> nat {
    if role==Role::Data {if mode==1 {64}else{0}}
    else if mode==4 {32}else if mode==6 {16}else{0}
}
fn same_role(a:Role,b:Role) -> (r:bool)
    ensures r==(a==b),
{
    match (a,b) {(Role::Data,Role::Data)|(Role::Name,Role::Name)=>true,_=>false}
}
fn selected(c:&Context,role:Role) -> (r:u8)
    ensures r==selected_mode(c,role),
{
    let (_,contents,names,_,_)=c.policy().fields();if matches!(role,Role::Data) {contents}else{names}
}
fn supported(mode:u8,role:Role) -> (r:Result<usize,Error>)
    ensures match r {Ok(n)=>n==supported_bytes(mode,role) && (n==16 || n==32 || n==64),
        Err(_)=>supported_bytes(mode,role)==0},
{
    if matches!(role,Role::Data) {if mode==1 {Ok(64)}else{Err(Error::Unsupported)}}
    else if mode==4 {Ok(32)}else if mode==6 {Ok(16)}else{Err(Error::Unsupported)}
}
impl CipherKey {
    pub closed spec fn cipher_valid(&self) -> bool {
        9<=self.unit_bits<=self.geometry.filesystem_block_bits<=16
            && self.inode>0 && self.mode==selected_mode(&self.context,self.role)
            && supported_bytes(self.mode,self.role)>0
            && self.key.len()==supported_bytes(self.mode,self.role)
            && (self.retired ==> self.hashed_inode==0
                && forall|i:int| 0<=i<self.key.len() ==> self.key@[i]==0)
    }
    pub closed spec fn cipher_binding(&self,uuid:[u8;16],inode:u64,c:&Context,role:Role) -> bool {
        !self.retired && self.filesystem_uuid==uuid && self.inode==inode && self.role==role
            && self.context.context_encoding()==c.context_encoding()
    }
    pub closed spec fn cipher_retired(&self) -> bool {self.retired}
    pub closed spec fn binding_view(&self) -> (u64,Role,Seq<u8>,[u8;16]) {
        (self.inode,self.role,self.context.context_encoding(),self.filesystem_uuid)
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {self.cipher_valid()}
    pub fn from_v2(master:&MasterKeyV2,context:Context,filesystem_uuid:[u8;16],inode:u64,geometry:Geometry,role:Role) -> (r:Result<Self,Error>)
        ensures match r {Ok(k)=>k.cipher_valid() && k.cipher_binding(filesystem_uuid,inode,&context,role),Err(_)=>true},
    {
        let mode=selected(&context,role);let size=supported(mode,role)?;
        let unit_bits=match context.policy().validate(geometry){Ok(v)=>v,Err(_)=>return Err(Error::Policy)};
        let key=match master.derive(&context,filesystem_uuid,matches!(role,Role::Name)){Ok(v)=>v,Err(_)=>return Err(Error::Binding)};
        if key.len()!=size {return Err(Error::KeyLength);}
        if mode==1 && bytes::equal(&key[..32],&key[32..]) {return Err(Error::WeakKey);}
        if master.keyed_iv(&context,geometry,inode,0,matches!(role,Role::Name)).is_err(){return Err(Error::Binding);}
        let (_,_,_,flags,_)=context.policy().fields();
        let hashed_inode=if flags & 16!=0 {match master.inode_hash(inode){Ok(v)=>v,Err(_)=>return Err(Error::Binding)}}else{0};
        Ok(Self {context,filesystem_uuid,inode,geometry,role,mode,unit_bits,hashed_inode,key,retired:false})
    }
    /// Legacy descriptors are caller-provisioned names, not key verification.
    pub fn from_v1(raw_master:&[u8],provisioned_descriptor:&[u8],context:Context,filesystem_uuid:[u8;16],inode:u64,geometry:Geometry,role:Role) -> (r:Result<Self,Error>)
        ensures match r {Ok(k)=>k.cipher_valid() && k.cipher_binding(filesystem_uuid,inode,&context,role),Err(_)=>true},
    {
        let (version,_,_,_,_)=context.policy().fields();
        if version!=0 || provisioned_descriptor.len()!=8 || !bytes::equal(context.policy().key_specifier().as_slice(),provisioned_descriptor) {return Err(Error::Binding);}
        let mode=selected(&context,role);let size=supported(mode,role)?;
        if raw_master.len()<size || raw_master.len()>64 {return Err(Error::KeyLength);}
        let unit_bits=match context.policy().validate(geometry){Ok(v)=>v,Err(_)=>return Err(Error::Policy)};
        if context.context_iv(geometry,inode,0,matches!(role,Role::Name)).is_err(){return Err(Error::Binding);}
        let nonce=context.nonce();let kdf=aes_key(&nonce)?;let mut key=Vec::new();let mut at=0usize;
        while at<size
            invariant at<=size<=64,size%16==0,at%16==0,key.len()==at,raw_master.len()>=size,
            decreases size-at,
        {append(&mut key,&enc(&kdf,block(raw_master,at))?);at+=16;}
        if mode==1 && bytes::equal(&key[..32],&key[32..]) {return Err(Error::WeakKey);}
        Ok(Self {context,filesystem_uuid,inode,geometry,role,mode,unit_bits,hashed_inode:0,key,retired:false})
    }
    pub fn binding(&self) -> (r:(u64,Role,Vec<u8>,[u8;16]))
        ensures (r.0,r.1,r.2@,r.3)==self.binding_view(),
    {(self.inode,self.role,self.context.encode_context(),self.filesystem_uuid)}
    fn check(&self,filesystem_uuid:[u8;16],inode:u64,context:&Context,role:Role) -> (r:Result<(),Error>)
        ensures r.is_ok()==self.cipher_binding(filesystem_uuid,inode,context,role),
    {
        if self.retired {return Err(Error::Retired);}
        if self.filesystem_uuid!=filesystem_uuid || self.inode!=inode || !same_role(self.role,role) || !bytes::equal(self.context.encode_context().as_slice(),context.encode_context().as_slice()) {return Err(Error::Binding);}
        Ok(())
    }
    fn iv(&self,index:u64) -> Result<[u8;16],Error> {
        if index>self.geometry.max_data_unit_index || (matches!(self.role,Role::Name) && index!=0) {return Err(Error::Index);}
        let (_,_,_,flags,_)=self.context.policy().fields();let mut value=index;
        if flags & 24!=0 {
            if index>0xffff_ffff || self.inode>0xffff_ffff {return Err(Error::Index);}
            value=if flags & 8!=0 {(self.inode<<32)|index}else{self.hashed_inode.wrapping_add(index as u32) as u64};
        }
        let mut iv=[0u8;16];let mut i=0usize;
        while i<8 invariant i<=8, decreases 8-i,
        {iv[i]=(value>>(8*i)) as u8;i+=1;}Ok(iv)
    }
    pub fn encrypt_data(&self,filesystem_uuid:[u8;16],inode:u64,context:&Context,index:u64,plaintext:&[u8]) -> (r:Result<Vec<u8>,Error>)
        ensures self.cipher_valid(),match r {Ok(v)=>self.cipher_binding(filesystem_uuid,inode,context,Role::Data)
            && v.len()==plaintext.len(),Err(_)=>true},
    {
        proof {use_type_invariant(self);}
        self.check(filesystem_uuid,inode,context,Role::Data)?;
        if self.mode!=1 {return Err(Error::Unsupported);}
        if plaintext.len()!=1usize<<self.unit_bits {return Err(Error::Length);}
        encrypt_xts_aes256(self.key.as_slice(),self.iv(index)?,plaintext)
    }
    pub fn decrypt_data(&self,filesystem_uuid:[u8;16],inode:u64,context:&Context,index:u64,ciphertext:&[u8]) -> (r:Result<Vec<u8>,Error>)
        ensures self.cipher_valid(),match r {Ok(v)=>self.cipher_binding(filesystem_uuid,inode,context,Role::Data)
            && v.len()==ciphertext.len(),Err(_)=>true},
    {
        proof {use_type_invariant(self);}
        self.check(filesystem_uuid,inode,context,Role::Data)?;
        if self.mode!=1 {return Err(Error::Unsupported);}
        if ciphertext.len()!=1usize<<self.unit_bits {return Err(Error::Length);}
        decrypt_xts_aes256(self.key.as_slice(),self.iv(index)?,ciphertext)
    }
    pub fn encrypt_name(&self,filesystem_uuid:[u8;16],inode:u64,context:&Context,plaintext:&[u8],maximum:u32) -> (r:Result<Vec<u8>,Error>)
        ensures self.cipher_valid(),match r {Ok(v)=>self.cipher_binding(filesystem_uuid,inode,context,Role::Name)
            && v.len()<=255,Err(_)=>true},
    {
        proof {use_type_invariant(self);}
        self.check(filesystem_uuid,inode,context,Role::Name)?;
        if plaintext.len()==0 || plaintext.len()>255 || maximum<16 || maximum>255 {return Err(Error::Name);}
        let mut i=0usize;
        while i<plaintext.len()
            invariant i<=plaintext.len()<=255,
            decreases plaintext.len()-i,
        {if plaintext[i]==0 || plaintext[i]==47{return Err(Error::Name);}i+=1;}
        if bytes::equal(plaintext,b".") || bytes::equal(plaintext,b"..") {return Ok(copy(plaintext));}
        let len=match self.context.policy().padded_filename_len(plaintext.len() as u32,maximum){Ok(n)=>n as usize,Err(_)=>return Err(Error::Name)};
        let mut padded=copy(plaintext);while padded.len()<len invariant padded.len()<=len<=255, decreases len-padded.len(), {padded.push(0);}
        encrypt_cbc_cs3_aes(self.key.as_slice(),self.iv(0)?,padded.as_slice())
    }
    pub fn decrypt_name(&self,filesystem_uuid:[u8;16],inode:u64,context:&Context,ciphertext:&[u8]) -> (r:Result<Vec<u8>,Error>)
        ensures self.cipher_valid(),match r {Ok(v)=>self.cipher_binding(filesystem_uuid,inode,context,Role::Name)
            && v.len()<=255,Err(_)=>true},
    {
        proof {use_type_invariant(self);}
        self.check(filesystem_uuid,inode,context,Role::Name)?;
        if bytes::equal(ciphertext,b".") || bytes::equal(ciphertext,b"..") {return Ok(copy(ciphertext));}
        if ciphertext.len()<16 || ciphertext.len()>255 {return Err(Error::Name);}
        let padded=decrypt_cbc_cs3_aes(self.key.as_slice(),self.iv(0)?,ciphertext)?;
        let mut end=0usize;
        while end<padded.len() && padded[end]!=0
            invariant end<=padded.len()<=255,
            decreases padded.len()-end,
        {if padded[end]==47{return Err(Error::Name);}end+=1;}
        if end==0 {return Err(Error::Name);}Ok(copy(&padded[..end]))
    }
    pub fn retire_cipher(&mut self)
        ensures final(self).cipher_valid(),final(self).cipher_retired(),
        opens_invariants none
        no_unwind
    {
        proof {use_type_invariant(&*self);}
        let mut i=0usize;
        while i<self.key.len()
            invariant i<=self.key.len(),forall|j:int| 0<=j<i ==> self.key@[j]==0,
                self.key.len()==old(self).key.len(),
                self.unit_bits==old(self).unit_bits,self.geometry==old(self).geometry,
                self.inode==old(self).inode,self.mode==old(self).mode,self.role==old(self).role,
                self.context==old(self).context,
            decreases self.key.len()-i,
        {self.key[i]=0;i+=1;}self.hashed_inode=0;self.retired=true;
    }
}
/// Provisioning selects a legacy named key or a v2 verified identifier.
/// This enum carries key material references, not filesystem permissions.
pub enum MasterKeyRef<'a> { V1 {raw:&'a[u8],descriptor:&'a[u8]}, V2(&'a MasterKeyV2) }
pub fn prepare_cipher(master:MasterKeyRef<'_>,context:Context,filesystem_uuid:[u8;16],inode:u64,geometry:Geometry,role:Role) -> Result<CipherKey,Error> {
    let (version,_,_,_,_)=context.policy().fields();
    match master {
        MasterKeyRef::V1 {raw,descriptor} => {
            if version!=0 {return Err(Error::Binding);}
            CipherKey::from_v1(raw,descriptor,context,filesystem_uuid,inode,geometry,role)
        },
        MasterKeyRef::V2(key) => {
            if version!=2 {return Err(Error::Binding);}
            CipherKey::from_v2(key,context,filesystem_uuid,inode,geometry,role)
        },
    }
}
impl Drop for CipherKey {
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {self.retire_cipher();}
}

}
