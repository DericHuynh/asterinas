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

fn aes_key(raw:&[u8]) -> (r:Result<AesKey,Error>)
    ensures match r {Ok(k)=>(raw.len()==16 || raw.len()==32) && k.valid_aes() && !k.aes_retired()
        && k.aes_round_count()==(if raw.len()==16 {10nat}else{14nat})
        && k.aes_schedule().take(((k.aes_round_count()+1)*16) as int)
            ==crate::aes::expanded_key_reference(raw@,(((k.aes_round_count()+1)*16-raw.len())/4) as nat),
        Err(_)=>raw.len()!=16 && raw.len()!=32},
{
    match AesKey::new_aes_key(raw) {Ok(v)=>Ok(v),Err(_)=>Err(Error::KeyLength)}
}
fn sm4_key(raw:&[u8]) -> (r:Result<Sm4Key,Error>)
    ensures match r {Ok(k)=>raw.len()==16 && k.sm4_valid() && !k.sm4_retired()
        && k.sm4_schedule()==crate::sm4::sm4_schedule_reference(raw@),Err(_)=>raw.len()!=16},
{
    match Sm4Key::new_sm4_key(raw) {Ok(v)=>Ok(v),Err(_)=>Err(Error::KeyLength)}
}
fn sm4_apply(key:&Sm4Key,b:[u8;16],decrypt:bool) -> (r:Result<[u8;16],Error>)
    ensures key.sm4_valid(),match r {Ok(v)=>!key.sm4_retired() && v@==key.sm4_transform_reference(b@,decrypt),
        Err(_)=>key.sm4_retired()},
{
    let changed=if decrypt {key.decrypt_sm4_block(b)}else{key.encrypt_sm4_block(b)};
    match changed {Ok(v)=>Ok(v),Err(_)=>Err(Error::Primitive)}
}
fn aes_apply(key:&AesKey,b:[u8;16],decrypt:bool) -> (r:Result<[u8;16],Error>)
    ensures key.valid_aes(),match r {Ok(v)=>!key.aes_retired()
        && v@==(if decrypt {key.aes_decrypt_reference(b@)}else{key.aes_encrypt_reference(b@)}),
        Err(_)=>key.aes_retired()},
{
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
    ensures r@==xor_bytes(a@,b@),r@==Seq::new(16,|i:int|a@[i]^b@[i]),
{
    let mut out=[0u8;16];let mut i=0usize;
    while i<16
        invariant i<=16,forall|j:int| 0<=j<i ==> out@[j]==a@[j]^b@[j],
        decreases 16-i,
    {out[i]=a[i]^b[i];i+=1;}
    proof {assert(out@ =~= xor_bytes(a@,b@));}
    out
}
spec fn xor_bytes(a:Seq<u8>,b:Seq<u8>) -> Seq<u8> {Seq::new(16,|i:int|a[i]^b[i])}
spec fn tweak_double(t:Seq<u8>) -> Seq<u8> {
    Seq::new(16,|i:int|{
        let shifted=(t[i]<<1)|(if i==0 {0u8}else{t[i-1]>>7});
        if i==0 {shifted^(if t[15]>>7==0 {0u8}else{0x87u8})}else{shifted}
    })
}
fn next_tweak(t:[u8;16]) -> (r:[u8;16])
    ensures r@==tweak_double(t@),
{
    let mut out=[0u8;16];let mut carry=0u8;let mut i=0usize;
    while i<16
        invariant i<=16,carry==(if i==0 {0u8}else{t@[i as int-1]>>7}),
            forall|j:int|0<=j<i ==> out@[j]==(t@[j]<<1)|(if j==0 {0u8}else{t@[j-1]>>7}),
        decreases 16-i,
    {out[i]=(t[i]<<1)|carry;carry=t[i]>>7;i+=1;}
    let mask=0u8.wrapping_sub(carry);let ghost before=out@;let low=out[0];
    proof {
        let last=t@[15];
        assert(carry==last>>7);
        assert(carry==0 || carry==1) by(bit_vector) requires carry==last>>7;
        assert(mask==(if carry==0 {0u8}else{255u8})) by(bit_vector)
            requires carry==0 || carry==1,mask==0u8.wrapping_sub(carry);
        assert((0x87u8 & mask)==(if last>>7==0 {0u8}else{0x87u8})) by(bit_vector)
            requires carry==last>>7,mask==(if carry==0 {0u8}else{255u8});
    }
    out[0]^=0x87u8 & mask;
    proof {
        assert forall|j:int|0<=j<16 implies out@[j]==tweak_double(t@)[j] by {
            if j==0 {
                let first=t@[0];let last=t@[15];let changed=out@[0];let reduction=0x87u8 & mask;
                assert(low==(first<<1)|0u8);
                assert(changed==low^reduction);
                assert(changed==(first<<1)^(if last>>7==0 {0u8}else{0x87u8})) by(bit_vector)
                    requires low==(first<<1)|0u8,changed==low^reduction,
                        reduction==(if last>>7==0 {0u8}else{0x87u8});
            }else{assert(out@[j]==before[j]);}
        }
        assert(out@ =~= tweak_double(t@));
    }
    out
}
spec fn sm4_xex_reference(key:&Sm4Key,input:Seq<u8>,tweak:Seq<u8>,decrypt:bool) -> Seq<u8> {
    xor_bytes(key.sm4_transform_reference(xor_bytes(input,tweak),decrypt),tweak)
}
fn sm4_xex(key:&Sm4Key,b:[u8;16],t:[u8;16],decrypt:bool) -> (r:Result<[u8;16],Error>)
    ensures key.sm4_valid(),match r {Ok(v)=>!key.sm4_retired()
        && v@==sm4_xex_reference(key,b@,t@,decrypt),Err(_)=>key.sm4_retired()},
{
    Ok(xor(sm4_apply(key,xor(b,t),decrypt)?,t))
}
#[verifier::opaque]
spec fn sm4_tweak(key:&Sm4Key,iv:Seq<u8>,count:nat) -> Seq<u8>
    decreases count,
{
    if count==0 {key.sm4_transform_reference(iv,false)}
    else{tweak_double(sm4_tweak(key,iv,(count-1) as nat))}
}
#[verifier::opaque]
spec fn sm4_xts_prefix(key:&Sm4Key,tweak_key:&Sm4Key,iv:Seq<u8>,input:Seq<u8>,decrypt:bool,count:nat) -> Seq<u8>
    decreases count,
{
    if count==0 {Seq::empty()}else{
        sm4_xts_prefix(key,tweak_key,iv,input,decrypt,(count-1) as nat)
            +sm4_xex_reference(key,input.subrange((count as int-1)*16,count as int*16),
                sm4_tweak(tweak_key,iv,(count-1) as nat),decrypt)
    }
}
proof fn sm4_xts_step(key:&Sm4Key,tweak_key:&Sm4Key,iv:Seq<u8>,input:Seq<u8>,decrypt:bool,count:nat)
    requires count*16<=input.len(),
    ensures count==0 ==> sm4_xts_prefix(key,tweak_key,iv,input,decrypt,count)==Seq::<u8>::empty(),
        count>0 ==> sm4_xts_prefix(key,tweak_key,iv,input,decrypt,count)
            ==sm4_xts_prefix(key,tweak_key,iv,input,decrypt,(count-1) as nat)
                +sm4_xex_reference(key,input.subrange((count as int-1)*16,count as int*16),
                    sm4_tweak(tweak_key,iv,(count-1) as nat),decrypt),
        sm4_tweak(tweak_key,iv,0)==tweak_key.sm4_transform_reference(iv,false),
        count>0 ==> sm4_tweak(tweak_key,iv,count)==tweak_double(sm4_tweak(tweak_key,iv,(count-1) as nat)),
        sm4_tweak(tweak_key,iv,count+1)==tweak_double(sm4_tweak(tweak_key,iv,count)),
{
    reveal(sm4_xts_prefix);reveal(sm4_tweak);
}
struct BlockPrefix {output:Seq<u8>,chain:Seq<u8>}
#[verifier::opaque]
spec fn sm4_cbc_prefix(key:&Sm4Key,iv:Seq<u8>,input:Seq<u8>,decrypt:bool,count:nat) -> BlockPrefix
    decreases count,
{
    if count==0 {BlockPrefix {output:Seq::empty(),chain:iv}}else{
        let prior=sm4_cbc_prefix(key,iv,input,decrypt,(count-1) as nat);
        let block=input.subrange((count as int-1)*16,count as int*16);
        if decrypt {BlockPrefix {output:prior.output+xor_bytes(key.sm4_transform_reference(block,true),prior.chain),chain:block}}
        else{let changed=key.sm4_transform_reference(xor_bytes(block,prior.chain),false);
            BlockPrefix {output:prior.output+changed,chain:changed}}
    }
}
#[verifier::opaque]
spec fn aes_cbc_prefix(key:&AesKey,iv:Seq<u8>,input:Seq<u8>,decrypt:bool,count:nat) -> BlockPrefix
    decreases count,
{
    if count==0 {BlockPrefix {output:Seq::empty(),chain:iv}}else{
        let prior=aes_cbc_prefix(key,iv,input,decrypt,(count-1) as nat);
        let block=input.subrange((count as int-1)*16,count as int*16);
        if decrypt {BlockPrefix {output:prior.output+xor_bytes(key.aes_decrypt_reference(block),prior.chain),chain:block}}
        else{let changed=key.aes_encrypt_reference(xor_bytes(block,prior.chain));
            BlockPrefix {output:prior.output+changed,chain:changed}}
    }
}
proof fn sm4_cbc_step(key:&Sm4Key,iv:Seq<u8>,input:Seq<u8>,decrypt:bool,count:nat)
    requires count*16<=input.len(),
    ensures count==0 ==> sm4_cbc_prefix(key,iv,input,decrypt,count)==(BlockPrefix {output:Seq::empty(),chain:iv}),
        count>0 ==> sm4_cbc_prefix(key,iv,input,decrypt,count)=={
            let prior=sm4_cbc_prefix(key,iv,input,decrypt,(count-1) as nat);
            let block=input.subrange((count as int-1)*16,count as int*16);
            if decrypt {BlockPrefix {output:prior.output+xor_bytes(key.sm4_transform_reference(block,true),prior.chain),chain:block}}
            else{let c=key.sm4_transform_reference(xor_bytes(block,prior.chain),false);
                BlockPrefix {output:prior.output+c,chain:c}}
        },
{reveal(sm4_cbc_prefix);}
proof fn aes_cbc_step(key:&AesKey,iv:Seq<u8>,input:Seq<u8>,decrypt:bool,count:nat)
    requires count*16<=input.len(),
    ensures count==0 ==> aes_cbc_prefix(key,iv,input,decrypt,count)==(BlockPrefix {output:Seq::empty(),chain:iv}),
        count>0 ==> aes_cbc_prefix(key,iv,input,decrypt,count)=={
            let prior=aes_cbc_prefix(key,iv,input,decrypt,(count-1) as nat);
            let block=input.subrange((count as int-1)*16,count as int*16);
            if decrypt {BlockPrefix {output:prior.output+xor_bytes(key.aes_decrypt_reference(block),prior.chain),chain:block}}
            else{let c=key.aes_encrypt_reference(xor_bytes(block,prior.chain));
                BlockPrefix {output:prior.output+c,chain:c}}
        },
{reveal(aes_cbc_prefix);}
#[verifier::opaque]
spec fn aes_ecb_prefix(key:&AesKey,input:Seq<u8>,count:nat) -> Seq<u8>
    decreases count,
{
    if count==0 {Seq::empty()}else{
        aes_ecb_prefix(key,input,(count-1) as nat)
            +key.aes_encrypt_reference(input.subrange((count as int-1)*16,count as int*16))
    }
}
proof fn aes_ecb_step(key:&AesKey,input:Seq<u8>,count:nat)
    requires count*16<=input.len(),
    ensures count==0 ==> aes_ecb_prefix(key,input,count)==Seq::<u8>::empty(),
        count>0 ==> aes_ecb_prefix(key,input,count)==aes_ecb_prefix(key,input,(count-1) as nat)
            +key.aes_encrypt_reference(input.subrange((count as int-1)*16,count as int*16)),
{reveal(aes_ecb_prefix);}
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
    proof {sm4_xts_step(&key,&tweak_key,iv@,input@,decrypt,0);}
    while i<normal
        invariant i<=normal<=whole<=1048576,remainder<16,
            input.len()==whole*16+remainder,16<=input.len()<=MAX_EXTRA_BYTES,
            normal==(if remainder==0 {whole}else{(whole-1) as usize}),
            key.sm4_valid() && !key.sm4_retired(),tweak_key.sm4_valid() && !tweak_key.sm4_retired(),
            out.len()==i*16,out@==sm4_xts_prefix(&key,&tweak_key,iv@,input@,decrypt,i as nat),
            tweak@==sm4_tweak(&tweak_key,iv@,i as nat),
        decreases normal-i,
    {
        append(&mut out,&sm4_xex(&key,block(input,i*16),tweak,decrypt)?);
        proof {sm4_xts_step(&key,&tweak_key,iv@,input@,decrypt,(i+1) as nat);}
        tweak=next_tweak(tweak);i+=1;
    }
    if remainder!=0 {
        let at=normal*16;let next=next_tweak(tweak);
        if decrypt {
            let pp=sm4_xex(&key,block(input,at),next,true)?;let mut cc=pp;let mut j=0usize;
            while j<remainder
                invariant j<=remainder<16,at+16+remainder==input.len(),
                    key.sm4_valid() && !key.sm4_retired(),out.len()==at,
                    cc@==Seq::new(16,|z:int|if z<j {input@[at as int+16+z]}else{pp@[z]}),
                decreases remainder-j,
            {cc[j]=input[at+16+j];j+=1;}
            append(&mut out,&sm4_xex(&key,cc,tweak,true)?);append(&mut out,&pp[..remainder]);
        } else {
            let cc=sm4_xex(&key,block(input,at),tweak,false)?;let mut pp=cc;let mut j=0usize;
            while j<remainder
                invariant j<=remainder<16,at+16+remainder==input.len(),
                    key.sm4_valid() && !key.sm4_retired(),out.len()==at,
                    pp@==Seq::new(16,|z:int|if z<j {input@[at as int+16+z]}else{cc@[z]}),
                decreases remainder-j,
            {pp[j]=input[at+16+j];j+=1;}
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
    proof {sm4_cbc_step(&key,iv@,input@,decrypt,0);}
    while at<prefix
        invariant at<=prefix,at%16==0,prefix%16==0,0<last<=16,
            prefix+16+last==input.len(),16<input.len()<=MAX_EXTRA_BYTES,
            key.sm4_valid() && !key.sm4_retired(),out.len()==at,
            out@==sm4_cbc_prefix(&key,iv@,input@,decrypt,(at/16) as nat).output,
            chain@==sm4_cbc_prefix(&key,iv@,input@,decrypt,(at/16) as nat).chain,
        decreases prefix-at,
    {
        let ghost n=(at/16) as nat;let b=block(input,at);
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(at as int,16);
            assert(n as int*16==at);assert((at as int+16)/16==n+1);
            sm4_cbc_step(&key,iv@,input@,decrypt,n+1);
        }
        if decrypt {append(&mut out,&xor(sm4_apply(&key,b,true)?,chain));chain=b;}
        else {let c=sm4_apply(&key,xor(b,chain),false)?;append(&mut out,&c);chain=c;}
        at+=16;
    }
    if decrypt {
        let d=sm4_apply(&key,block(input,prefix),true)?;let mut stolen=d;let mut tail=[0u8;16];let mut i=0usize;
        while i<last
            invariant i<=last<=16,0<last,prefix+16+last==input.len(),out.len()==prefix,
                key.sm4_valid() && !key.sm4_retired(),
                stolen@==Seq::new(16,|z:int|if z<i {input@[prefix as int+16+z]}else{d@[z]}),
                tail@==Seq::new(16,|z:int|if z<i {d@[z]^input@[prefix as int+16+z]}else{0u8}),
            decreases last-i,
        {stolen[i]=input[prefix+16+i];tail[i]=d[i]^stolen[i];i+=1;}
        append(&mut out,&xor(sm4_apply(&key,stolen,true)?,chain));append(&mut out,&tail[..last]);
    } else {
        let stolen=sm4_apply(&key,xor(block(input,prefix),chain),false)?;let mut tail=[0u8;16];let mut i=0usize;
        while i<last
            invariant i<=last<=16,0<last,prefix+16+last==input.len(),out.len()==prefix,
                key.sm4_valid() && !key.sm4_retired(),
                tail@==Seq::new(16,|z:int|if z<i {input@[prefix as int+16+z]}else{0u8}),
            decreases last-i,
        {tail[i]=input[prefix+16+i];i+=1;}
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
    let mut chain=aes_apply(&iv_key,initial_iv,false)?;let ghost seed=chain@;
    let mut out=Vec::new();let mut at=0usize;
    proof {aes_cbc_step(&key,seed,input@,decrypt,0);}
    while at<input.len()
        invariant at<=input.len(),at%16==0,input.len()%16==0,16<=input.len()<=MAX_EXTRA_BYTES,
            key.valid_aes() && !key.aes_retired(),iv_key.valid_aes() && !iv_key.aes_retired(),
            out.len()==at,out@==aes_cbc_prefix(&key,seed,input@,decrypt,(at/16) as nat).output,
            chain@==aes_cbc_prefix(&key,seed,input@,decrypt,(at/16) as nat).chain,
            seed==iv_key.aes_encrypt_reference(initial_iv@),
        decreases input.len()-at,
    {
        let ghost n=(at/16) as nat;let b=block(input,at);
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(at as int,16);
            assert(n as int*16==at);assert((at as int+16)/16==n+1);
            aes_cbc_step(&key,seed,input@,decrypt,n+1);
        }
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
proof fn uuid_array_views(a:[u8;16],b:[u8;16])
    ensures (a==b)==(a@==b@),
{
    if a@==b@ {
        assert forall|i:int| 0<=i<16 implies a[i]==b[i] by {
            vstd::array::lemma_array_index(a,i);
            vstd::array::lemma_array_index(b,i);
            assert(a@[i]==b@[i]);
        }
        assert(a =~= b);
    }
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
            proof {aes_ecb_step(&kdf,raw_master@,0);}
            while at<size
                invariant at<=size<=32,at%16==0,size%16==0,key.len()==at,raw_master.len()>=size,
                    kdf.valid_aes() && !kdf.aes_retired(),key@==aes_ecb_prefix(&kdf,raw_master@,(at/16) as nat),
                    inode>0,context.context_policy().policy_fields().0==0,
                    context.context_policy().policy_key()==descriptor@,
                    context.context_policy().accepts_geometry(geometry),
                    9<=unit_bits<=geometry.filesystem_block_bits<=16,
                    mode==mode_for(context,role),size==mode_bytes(mode,role),size==16 || size==32,
                    name_iv@==prepared_legacy_iv_reference(context,inode,role==Role::Name),
                decreases size-at,
            {
                append(&mut key,&aes_apply(&kdf,block(raw_master,at),false)?);
                proof {aes_ecb_step(&kdf,raw_master@,(at/16+1) as nat);}
                at+=16;
            }
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
        let uuid_equal=bytes::equal(&self.uuid,&uuid);
        proof {
            uuid_array_views(self.uuid,uuid);
            assert(uuid_equal==(self.uuid==uuid));
        }
        if !uuid_equal || self.inode!=inode || !same_role(self.role,role) {return Err(Error::Binding);}
        let actual=self.context.encode_context();let requested=context.encode_context();
        let equal=bytes::equal(actual.as_slice(),requested.as_slice());
        proof {
            assert(actual@==self.context.context_encoding());
            assert(requested@==context.context_encoding());
            assert(equal==(self.context.context_encoding()==context.context_encoding()));
        }
        if !equal {return Err(Error::Binding);}
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
        let mut i=0usize;
        while i<input.len()
            invariant i<=input.len()<=255,input.len()>0,self.extra_valid(),
                self.extra_bound(uuid,inode,context,Role::Name),
                forall|j:int|0<=j<i ==> input@[j]!=0 && input@[j]!=47,
            decreases input.len()-i,
        {if input[i]==0 || input[i]==47{return Err(Error::Name);}i+=1;}
        if bytes::equal(input,b".") || bytes::equal(input,b"..") {return Ok(copy(input));}
        let length=match self.context.policy().padded_filename_len(input.len() as u32,maximum){Ok(v)=>v as usize,Err(_)=>return Err(Error::Name)};
        let mut padded=copy(input);
        while padded.len()<length
            invariant input.len()<=padded.len()<=length<=255,self.extra_valid(),
                self.extra_bound(uuid,inode,context,Role::Name),
                padded@==input@+Seq::new((padded.len()-input.len()) as nat,|j:int|0u8),
                self.context.context_policy().padded_filename_model(input.len() as u32,maximum)==Some(length as u32),
            decreases length-padded.len(),
        {
            padded.push(0);
            assert(padded@ =~= input@+Seq::new((padded.len()-input.len()) as nat,|j:int|0u8));
        }
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
        let mut end=0usize;
        while end<padded.len() && padded[end]!=0
            invariant end<=padded.len()<=255,self.extra_valid(),
                self.extra_bound(uuid,inode,context,Role::Name),
                forall|j:int|0<=j<end ==> padded@[j]!=0 && padded@[j]!=47,
            decreases padded.len()-end,
        {if padded[end]==47{return Err(Error::Name);}end+=1;}
        if end==0 {return Err(Error::Name);}Ok(copy(&padded[..end]))
    }
    pub fn retire_extra_cipher(&mut self)
        ensures final(self).extra_valid(),final(self).extra_retired(),final(self).extra_material()==Seq::<u8>::empty(),
            final(self).extra_binding_view()==old(self).extra_binding_view(),
        opens_invariants none
        no_unwind
    {self.secret=Secret {bytes:[0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8],length:0,retired:true};}
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
