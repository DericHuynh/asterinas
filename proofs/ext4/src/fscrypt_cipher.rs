// SPDX-License-Identifier: MPL-2.0

//! Executable common fscrypt AES modes and inode/context-bound key handles.
//! AES-XTS and CBC-CS3 execute real transforms. Other Linux modes return an
//! explicit unsupported result. Keys are logically retired and overwritten on
//! drop; physical erasure, side channels, provisioning and VFS authority remain
//! refinement boundaries. These implementation-first paths await proof.

use vstd::prelude::*;
use crate::{aes::{self,AesKey},bytes,fscrypt_context::{Context,Geometry,MasterKeyV2}};

verus! {

pub const MAX_CIPHER_BYTES:usize=16777216;
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Error { KeyLength,WeakKey,Length,Unsupported,Policy,Binding,Index,Retired,Primitive,Name }

spec fn aes_material(key:&AesKey,raw:Seq<u8>) -> bool {
    &&& (raw.len()==16 || raw.len()==32)
    &&& key.valid_aes() && !key.aes_retired()
    &&& key.aes_round_count()==if raw.len()==16 {10nat}else{14nat}
    &&& key.aes_schedule().take(((key.aes_round_count()+1)*16) as int)
        ==crate::aes::expanded_key_reference(raw,(((key.aes_round_count()+1)*16-raw.len())/4) as nat)
}
fn aes_key(raw:&[u8]) -> (r:Result<AesKey,Error>)
    ensures match r {Ok(key)=>aes_material(&key,raw@),Err(_)=>raw.len()!=16 && raw.len()!=32},
{
    match AesKey::new_aes_key(raw) {Ok(k)=>Ok(k),Err(_)=>Err(Error::KeyLength)}
}
fn enc(key:&AesKey,b:[u8;16]) -> (r:Result<[u8;16],Error>)
    ensures key.valid_aes(),match r {
        Ok(v)=>!key.aes_retired() && v@==key.aes_encrypt_reference(b@),
        Err(_)=>key.aes_retired(),
    },
{
    match key.encrypt_aes_block(b) {Ok(v)=>Ok(v),Err(_)=>Err(Error::Primitive)}
}
fn dec(key:&AesKey,b:[u8;16]) -> (r:Result<[u8;16],Error>)
    ensures key.valid_aes(),match r {
        Ok(v)=>!key.aes_retired() && v@==key.aes_decrypt_reference(b@),
        Err(_)=>key.aes_retired(),
    },
{
    match key.decrypt_aes_block(b) {Ok(v)=>Ok(v),Err(_)=>Err(Error::Primitive)}
}
fn enc_raw(key:&AesKey,b:[u8;16],Ghost(raw):Ghost<Seq<u8>>) -> (r:Result<[u8;16],Error>)
    requires aes_material(key,raw),
    ensures match r {Ok(v)=>v@==aes::aes_raw_encrypt_reference(raw,b@),Err(_)=>false},
{
    proof {key.aes_raw_key_bridge(raw,b@);}
    enc(key,b)
}
fn dec_raw(key:&AesKey,b:[u8;16],Ghost(raw):Ghost<Seq<u8>>) -> (r:Result<[u8;16],Error>)
    requires aes_material(key,raw),
    ensures match r {Ok(v)=>v@==aes::aes_raw_decrypt_reference(raw,b@),Err(_)=>false},
{
    proof {key.aes_raw_key_bridge(raw,b@);}
    dec(key,b)
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
    ensures r@==xor_bytes(a@,b@),forall|i:int| 0<=i<16 ==> r@[i]==a@[i]^b@[i],
{
    let mut v=[0u8;16];let mut i=0usize;
    while i<16
        invariant i<=16,forall|j:int| 0<=j<i ==> v@[j]==a@[j]^b@[j],
        decreases 16-i,
    {v[i]=a[i]^b[i];i+=1;}
    proof {assert(v@ =~= xor_bytes(a@,b@));}
    v
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
    let ghost before=out@;
    let low=out[0];
    proof {
        let last=t@[15];
        assert(carry==last>>7);
        assert(carry==0 || carry==1) by(bit_vector)
            requires carry==last>>7;
        assert(mask==if carry==0 {0u8}else{255u8}) by(bit_vector)
            requires carry==0 || carry==1,mask==0u8.wrapping_sub(carry);
        assert((0x87u8 & mask)==if last>>7==0 {0u8}else{0x87u8}) by(bit_vector)
            requires carry==last>>7,mask==if carry==0 {0u8}else{255u8};
    }
    out[0]^=0x87u8 & mask;
    proof {
        assert forall|j:int| 0<=j<16 implies out@[j]==tweak_double(t@)[j] by {
            if j==0 {
                let first=t@[0];let last=t@[15];let changed=out@[0];let reduction=0x87u8 & mask;
                assert(low==(first<<1)|0u8);
                assert(changed==low^reduction);
                assert(changed==(first<<1)^(if last>>7==0 {0u8}else{0x87u8})) by(bit_vector)
                    requires low==(first<<1)|0u8,changed==low^reduction,
                        reduction==if last>>7==0 {0u8}else{0x87u8};
            }else{
                assert(out@[j]==before[j]);
            }
        }
        assert(out@ =~= tweak_double(t@));
    }
    out
}
// Functional mode models use the exact raw-key AES references. They do not
// assert cryptographic confidentiality, authenticity, or compiler timing.
spec fn suffix(raw:Seq<u8>,start:int) -> Seq<u8> {
    raw.subrange(start,raw.len() as int)
}
spec fn xor_bytes(a:Seq<u8>,b:Seq<u8>) -> Seq<u8> {
    Seq::new(16,|i:int| a[i]^b[i])
}
spec fn xex_bytes(raw:Seq<u8>,input:Seq<u8>,tweak:Seq<u8>,decrypt:bool) -> Seq<u8> {
    let white=xor_bytes(input,tweak);
    xor_bytes(if decrypt {aes::aes_raw_decrypt_reference(raw,white)}
        else{aes::aes_raw_encrypt_reference(raw,white)},tweak)
}
#[verifier::opaque]
spec fn xts_tweak(raw:Seq<u8>,iv:Seq<u8>,count:nat) -> Seq<u8>
    decreases count,
{
    if count==0 {aes::aes_raw_encrypt_reference(raw,iv)}
    else{tweak_double(xts_tweak(raw,iv,(count-1) as nat))}
}
#[verifier::opaque]
spec fn xts_prefix(key:Seq<u8>,iv:Seq<u8>,input:Seq<u8>,decrypt:bool,count:nat) -> Seq<u8>
    decreases count,
{
    if count==0 {Seq::empty()}else{
        let at=(count-1)*16;
        xts_prefix(key,iv,input,decrypt,(count-1) as nat)
            +xex_bytes(key.take(32),input.subrange(at as int,at as int+16),
                xts_tweak(key.subrange(32,64),iv,(count-1) as nat),decrypt)
    }
}
pub closed spec fn xts_aes256_admitted(key:Seq<u8>,input:Seq<u8>) -> bool {
    key.len()==64 && key.take(32)!=key.subrange(32,64)
        && 16<=input.len()<=MAX_CIPHER_BYTES
}
pub closed spec fn xts_aes256_reference(key:Seq<u8>,iv:Seq<u8>,input:Seq<u8>,decrypt:bool) -> Seq<u8> {
    if !xts_aes256_admitted(key,input) || iv.len()!=16 {Seq::empty()}else{
        let whole=input.len()/16;let rem=input.len()%16;
        let normal=if rem==0 {whole}else{(whole-1) as nat};
        let prefix=xts_prefix(key,iv,input,decrypt,normal);
        if rem==0 {prefix}else{
            let at=normal*16;
            let tweak=xts_tweak(key.subrange(32,64),iv,normal);
            let next=tweak_double(tweak);
            let a=input.subrange(at as int,at as int+16);let tail=input.subrange(at as int+16,input.len() as int);
            if decrypt {
                let p=xex_bytes(key.take(32),a,next,true);
                let c=tail+suffix(p,rem as int);
                prefix+xex_bytes(key.take(32),c,tweak,true)+p.take(rem as int)
            }else{
                let c=xex_bytes(key.take(32),a,tweak,false);
                let p=tail+suffix(c,rem as int);
                prefix+xex_bytes(key.take(32),p,next,false)+c.take(rem as int)
            }
        }
    }
}
proof fn xts_tweak_step(raw:Seq<u8>,iv:Seq<u8>,count:nat)
    requires raw.len()==32,iv.len()==16,
    ensures xts_tweak(raw,iv,count).len()==16,
        count==0 ==> xts_tweak(raw,iv,count)==aes::aes_raw_encrypt_reference(raw,iv),
        count>0 ==> xts_tweak(raw,iv,count)==tweak_double(xts_tweak(raw,iv,(count-1) as nat)),
    decreases count,
{
    reveal(xts_tweak);
    if count==0 {aes::aes_raw_reference_roundtrips(raw,iv);}
    else{xts_tweak_step(raw,iv,(count-1) as nat);}
}
proof fn xts_prefix_step(key:Seq<u8>,iv:Seq<u8>,input:Seq<u8>,decrypt:bool,count:nat)
    requires key.len()==64,iv.len()==16,count*16<=input.len(),
    ensures xts_prefix(key,iv,input,decrypt,count).len()==count*16,
        count==0 ==> xts_prefix(key,iv,input,decrypt,count)==Seq::<u8>::empty(),
        count>0 ==> xts_prefix(key,iv,input,decrypt,count)
            ==xts_prefix(key,iv,input,decrypt,(count-1) as nat)
                +xex_bytes(key.take(32),input.subrange((count as int-1)*16,count as int*16),
                    xts_tweak(key.subrange(32,64),iv,(count-1) as nat),decrypt),
    decreases count,
{
    reveal(xts_prefix);
    if count>0 {xts_prefix_step(key,iv,input,decrypt,(count-1) as nat);}
}
proof fn overwrite_is_concat(original:Seq<u8>,replacement:Seq<u8>)
    requires original.len()==16,replacement.len()<=16,
    ensures Seq::new(16,|i:int| if i<replacement.len(){replacement[i]}else{original[i]})
        ==replacement+suffix(original,replacement.len() as int),
{
    assert(Seq::new(16,|i:int| if i<replacement.len(){replacement[i]}else{original[i]})
        =~=replacement+suffix(original,replacement.len() as int));
}
fn xex(key:&AesKey,input:[u8;16],tweak:[u8;16],decrypt:bool,Ghost(raw):Ghost<Seq<u8>>)
    -> (r:Result<[u8;16],Error>)
    requires aes_material(key,raw),
    ensures match r {Ok(v)=>v@==xex_bytes(raw,input@,tweak@,decrypt),Err(_)=>false},
{
    let whitened=xor(input,tweak);
    proof {assert(whitened@ =~= xor_bytes(input@,tweak@));}
    let changed=if decrypt {dec_raw(key,whitened,Ghost(raw))?}else{enc_raw(key,whitened,Ghost(raw))?};
    let result=xor(changed,tweak);
    proof {assert(result@ =~= xex_bytes(raw,input@,tweak@,decrypt));}
    Ok(result)
}
fn xts(key:&[u8],iv:[u8;16],input:&[u8],decrypt:bool) -> (r:Result<Vec<u8>,Error>)
    ensures r.is_ok()==xts_aes256_admitted(key@,input@),
        match r {Ok(v)=>v.len()==input.len()
            && v@==xts_aes256_reference(key@,iv@,input@,decrypt),Err(_)=>true},
{
    if key.len()!=64 {return Err(Error::KeyLength);}
    if bytes::equal(&key[..32],&key[32..]) {return Err(Error::WeakKey);}
    if input.len()<16 || input.len()>MAX_CIPHER_BYTES {return Err(Error::Length);}
    let data_key=aes_key(&key[..32])?;let tweak_key=aes_key(&key[32..])?;
    let mut tweak=enc_raw(&tweak_key,iv,Ghost(key@.subrange(32,64)))?;let remainder=input.len()%16;
    let whole=input.len()/16;let normal=if remainder==0 {whole}else{whole-1};
    proof {xts_tweak_step(key@.subrange(32,64),iv@,0);xts_prefix_step(key@,iv@,input@,decrypt,0);}
    let mut out=Vec::new();let mut i=0usize;
    while i<normal
        invariant i<=normal,normal<=whole<=1048576,remainder<16,
            input.len()==whole*16+remainder,
            normal==if remainder==0 {whole}else{(whole-1) as usize},
            xts_aes256_admitted(key@,input@),key.len()==64,input.len()>=16,
            aes_material(&data_key,key@.take(32)),aes_material(&tweak_key,key@.subrange(32,64)),
            out.len()==i*16,out@==xts_prefix(key@,iv@,input@,decrypt,i as nat),
            tweak@==xts_tweak(key@.subrange(32,64),iv@,i as nat),
        decreases normal-i,
    {
        let changed=xex(&data_key,block(input,i*16),tweak,decrypt,Ghost(key@.take(32)))?;
        append(&mut out,&changed);
        proof {
            xts_prefix_step(key@,iv@,input@,decrypt,(i+1) as nat);
            xts_tweak_step(key@.subrange(32,64),iv@,(i+1) as nat);
        }
        tweak=mul_tweak(tweak);i+=1;
    }
    if remainder!=0 {
        let at=normal*16;let next=mul_tweak(tweak);
        if decrypt {
            let pp=xex(&data_key,block(input,at),next,true,Ghost(key@.take(32)))?;
            let mut cc=pp;let mut j=0usize;
            while j<remainder
                invariant j<=remainder<16,at+16+remainder==input.len(),
                    cc@==Seq::new(16,|z:int| if z<j {input@[at as int+16+z]}else{pp@[z]}),
                decreases remainder-j,
            {cc[j]=input[at+16+j];j+=1;}
            proof {
                overwrite_is_concat(pp@,input@.subrange(at as int+16,input.len() as int));
                assert(cc@==input@.subrange(at as int+16,input.len() as int)+suffix(pp@,remainder as int));
            }
            let previous=xex(&data_key,cc,tweak,true,Ghost(key@.take(32)))?;
            append(&mut out,&previous);append(&mut out,&pp[..remainder]);
        }else{
            let cc=xex(&data_key,block(input,at),tweak,false,Ghost(key@.take(32)))?;
            let mut pp=cc;let mut j=0usize;
            while j<remainder
                invariant j<=remainder<16,at+16+remainder==input.len(),
                    pp@==Seq::new(16,|z:int| if z<j {input@[at as int+16+z]}else{cc@[z]}),
                decreases remainder-j,
            {pp[j]=input[at+16+j];j+=1;}
            proof {
                overwrite_is_concat(cc@,input@.subrange(at as int+16,input.len() as int));
                assert(pp@==input@.subrange(at as int+16,input.len() as int)+suffix(cc@,remainder as int));
            }
            let previous=xex(&data_key,pp,next,false,Ghost(key@.take(32)))?;
            append(&mut out,&previous);append(&mut out,&cc[..remainder]);
        }
    }
    proof {assert(out@==xts_aes256_reference(key@,iv@,input@,decrypt));}
    Ok(out)
}
pub fn encrypt_xts_aes256(key:&[u8],iv:[u8;16],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures r.is_ok()==xts_aes256_admitted(key@,input@),
        match r {Ok(v)=>v.len()==input.len() && v@==xts_aes256_reference(key@,iv@,input@,false),Err(_)=>true},
{xts(key,iv,input,false)}
pub fn decrypt_xts_aes256(key:&[u8],iv:[u8;16],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures r.is_ok()==xts_aes256_admitted(key@,input@),
        match r {Ok(v)=>v.len()==input.len() && v@==xts_aes256_reference(key@,iv@,input@,true),Err(_)=>true},
{xts(key,iv,input,true)}

struct CbcPrefix {output:Seq<u8>,chain:Seq<u8>}
#[verifier::opaque]
spec fn cbc_prefix(key:Seq<u8>,iv:Seq<u8>,input:Seq<u8>,decrypt:bool,count:nat) -> CbcPrefix
    decreases count,
{
    if count==0 {CbcPrefix {output:Seq::empty(),chain:iv}}else{
        let prior=cbc_prefix(key,iv,input,decrypt,(count-1) as nat);
        let block=input.subrange((count as int-1)*16,count as int*16);
        if decrypt {CbcPrefix {
            output:prior.output+xor_bytes(aes::aes_raw_decrypt_reference(key,block),prior.chain),chain:block,
        }}else{
            let changed=aes::aes_raw_encrypt_reference(key,xor_bytes(block,prior.chain));
            CbcPrefix {output:prior.output+changed,chain:changed}
        }
    }
}
pub closed spec fn cbc_cs3_aes_admitted(key:Seq<u8>,input:Seq<u8>) -> bool {
    (key.len()==16 || key.len()==32) && 16<=input.len()<=MAX_CIPHER_BYTES
}
pub closed spec fn cbc_cs3_aes_reference(key:Seq<u8>,iv:Seq<u8>,input:Seq<u8>,decrypt:bool) -> Seq<u8> {
    if !cbc_cs3_aes_admitted(key,input) || iv.len()!=16 {Seq::empty()}else if input.len()==16 {
        if decrypt {xor_bytes(aes::aes_raw_decrypt_reference(key,input),iv)}
        else{aes::aes_raw_encrypt_reference(key,xor_bytes(input,iv))}
    }else{
        let prefix=(((input.len()-1)/16-1)*16) as nat;
        let last=(input.len()-prefix-16) as nat;
        let prior=cbc_prefix(key,iv,input,decrypt,prefix/16);
        if decrypt {
            let d=aes::aes_raw_decrypt_reference(key,input.subrange(prefix as int,prefix as int+16));
            let stolen=input.subrange(prefix as int+16,input.len() as int)+suffix(d,last as int);
            prior.output+xor_bytes(aes::aes_raw_decrypt_reference(key,stolen),prior.chain)
                +xor_bytes(d,stolen).take(last as int)
        }else{
            let stolen=aes::aes_raw_encrypt_reference(key,xor_bytes(input.subrange(prefix as int,prefix as int+16),prior.chain));
            let tail=input.subrange(prefix as int+16,input.len() as int)+Seq::new((16-last) as nat,|i:int|0u8);
            prior.output+aes::aes_raw_encrypt_reference(key,xor_bytes(tail,stolen))+stolen.take(last as int)
        }
    }
}
proof fn cbc_prefix_step(key:Seq<u8>,iv:Seq<u8>,input:Seq<u8>,decrypt:bool,count:nat)
    requires key.len()==16 || key.len()==32,iv.len()==16,count*16<=input.len(),
    ensures cbc_prefix(key,iv,input,decrypt,count).output.len()==count*16,
        cbc_prefix(key,iv,input,decrypt,count).chain.len()==16,
        count==0 ==> cbc_prefix(key,iv,input,decrypt,count)==(CbcPrefix {output:Seq::empty(),chain:iv}),
        count>0 ==> cbc_prefix(key,iv,input,decrypt,count)=={
            let prior=cbc_prefix(key,iv,input,decrypt,(count-1) as nat);
            let block=input.subrange((count as int-1)*16,count as int*16);
            if decrypt {CbcPrefix {output:prior.output+xor_bytes(aes::aes_raw_decrypt_reference(key,block),prior.chain),chain:block}}
            else{let c=aes::aes_raw_encrypt_reference(key,xor_bytes(block,prior.chain));CbcPrefix {output:prior.output+c,chain:c}}
        },
    decreases count,
{
    reveal(cbc_prefix);
    if count>0 {
        cbc_prefix_step(key,iv,input,decrypt,(count-1) as nat);
        let prior=cbc_prefix(key,iv,input,decrypt,(count-1) as nat);
        let block=input.subrange((count as int-1)*16,count as int*16);
        aes::aes_raw_reference_roundtrips(key,block);
        aes::aes_raw_reference_roundtrips(key,xor_bytes(block,prior.chain));
    }
}
fn cbc_cs3(key:&[u8],iv:[u8;16],input:&[u8],decrypt:bool) -> (r:Result<Vec<u8>,Error>)
    ensures r.is_ok()==cbc_cs3_aes_admitted(key@,input@),
        match r {Ok(v)=>v.len()==input.len() && v@==cbc_cs3_aes_reference(key@,iv@,input@,decrypt),Err(_)=>true},
{
    if input.len()<16 || input.len()>MAX_CIPHER_BYTES {return Err(Error::Length);}
    let cipher=aes_key(key)?;let mut out=Vec::new();let mut chain=iv;
    if input.len()==16 {
        let result=if decrypt {xor(dec_raw(&cipher,block(input,0),Ghost(key@))?,iv)}
            else{enc_raw(&cipher,xor(block(input,0),iv),Ghost(key@))?};
        append(&mut out,&result);
        proof {
            assert(input@.subrange(0,16) =~= input@);
            assert(out@ =~= result@);
            assert(out@==cbc_cs3_aes_reference(key@,iv@,input@,decrypt));
        }
        return Ok(out);
    }
    let prefix=((input.len()-1)/16-1)*16;let last=input.len()-prefix-16;let mut at=0usize;
    proof {cbc_prefix_step(key@,iv@,input@,decrypt,0);}
    while at<prefix
        invariant at<=prefix,at%16==0,prefix%16==0,0<last<=16,
            prefix+16+last==input.len(),input.len()<=MAX_CIPHER_BYTES,
            input.len()>16,cbc_cs3_aes_admitted(key@,input@),aes_material(&cipher,key@),
            prefix==((input.len()-1)/16-1)*16,
            out@==cbc_prefix(key@,iv@,input@,decrypt,(at/16) as nat).output,
            chain@==cbc_prefix(key@,iv@,input@,decrypt,(at/16) as nat).chain,
            out.len()==at,
        decreases prefix-at,
    {
        let ghost n=(at/16) as nat;
        let ghost prior_out=out@;let ghost prior_chain=chain@;
        let b=block(input,at);
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(at as int,16);
            assert(n as int*16==at);
            assert((at as int+16)/16==n+1);
            assert(b@==input@.subrange(n as int*16,(n as int+1)*16));
            cbc_prefix_step(key@,iv@,input@,decrypt,n+1);
        }
        if decrypt {
            let plain=xor(dec_raw(&cipher,b,Ghost(key@))?,chain);
            append(&mut out,&plain);chain=b;
            proof {
                assert(out@==prior_out+xor_bytes(aes::aes_raw_decrypt_reference(key@,b@),prior_chain));
                assert(chain@==b@);
            }
        }else{
            let c=enc_raw(&cipher,xor(b,chain),Ghost(key@))?;
            append(&mut out,&c);chain=c;
            proof {
                assert(chain@==aes::aes_raw_encrypt_reference(key@,xor_bytes(b@,prior_chain)));
                assert(out@==prior_out+chain@);
            }
        }
        proof {
            assert(out@==cbc_prefix(key@,iv@,input@,decrypt,n+1).output);
            assert(chain@==cbc_prefix(key@,iv@,input@,decrypt,n+1).chain);
        }
        at+=16;
    }
    if decrypt {
        let d=dec_raw(&cipher,block(input,prefix),Ghost(key@))?;
        let mut stolen=d;let mut tail=[0u8;16];let mut i=0usize;
        while i<last
            invariant i<=last<=16,0<last,prefix+16+last==input.len(),
                input.len()>16,cbc_cs3_aes_admitted(key@,input@),aes_material(&cipher,key@),
                prefix==((input.len()-1)/16-1)*16,
                out@==cbc_prefix(key@,iv@,input@,decrypt,(prefix/16) as nat).output,
                chain@==cbc_prefix(key@,iv@,input@,decrypt,(prefix/16) as nat).chain,
                d@==aes::aes_raw_decrypt_reference(key@,input@.subrange(prefix as int,prefix as int+16)),
                stolen@==Seq::new(16,|j:int| if j<i {input@[prefix as int+16+j]}else{d@[j]}),
                tail@==Seq::new(16,|j:int| if j<i {d@[j]^input@[prefix as int+16+j]}else{0u8}),
            decreases last-i,
        {stolen[i]=input[prefix+16+i];tail[i]=d[i]^stolen[i];i+=1;}
        proof {
            overwrite_is_concat(d@,input@.subrange(prefix as int+16,input.len() as int));
            assert(stolen@==input@.subrange(prefix as int+16,input.len() as int)+suffix(d@,last as int));
            assert(tail@.take(last as int) =~= xor_bytes(d@,stolen@).take(last as int));
        }
        let previous=xor(dec_raw(&cipher,stolen,Ghost(key@))?,chain);
        append(&mut out,&previous);append(&mut out,&tail[..last]);
    }else{
        let stolen=enc_raw(&cipher,xor(block(input,prefix),chain),Ghost(key@))?;
        let mut tail=[0u8;16];let mut i=0usize;
        while i<last
            invariant i<=last<=16,0<last,prefix+16+last==input.len(),
                input.len()>16,cbc_cs3_aes_admitted(key@,input@),aes_material(&cipher,key@),
                prefix==((input.len()-1)/16-1)*16,
                out@==cbc_prefix(key@,iv@,input@,decrypt,(prefix/16) as nat).output,
                chain@==cbc_prefix(key@,iv@,input@,decrypt,(prefix/16) as nat).chain,
                stolen@==aes::aes_raw_encrypt_reference(key@,
                    xor_bytes(input@.subrange(prefix as int,prefix as int+16),chain@)),
                tail@==Seq::new(16,|j:int| if j<i {input@[prefix as int+16+j]}else{0u8}),
            decreases last-i,
        {tail[i]=input[prefix+16+i];i+=1;}
        proof {
            assert(tail@ =~= input@.subrange(prefix as int+16,input.len() as int)
                +Seq::new((16-last) as nat,|i:int|0u8));
        }
        let final_block=enc_raw(&cipher,xor(tail,stolen),Ghost(key@))?;
        append(&mut out,&final_block);append(&mut out,&stolen[..last]);
    }
    proof {assert(out@==cbc_cs3_aes_reference(key@,iv@,input@,decrypt));}
    Ok(out)
}
pub fn encrypt_cbc_cs3_aes(key:&[u8],iv:[u8;16],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures r.is_ok()==cbc_cs3_aes_admitted(key@,input@),
        match r {Ok(v)=>v.len()==input.len() && v@==cbc_cs3_aes_reference(key@,iv@,input@,false),Err(_)=>true},
{cbc_cs3(key,iv,input,false)}
pub fn decrypt_cbc_cs3_aes(key:&[u8],iv:[u8;16],input:&[u8]) -> (r:Result<Vec<u8>,Error>)
    ensures r.is_ok()==cbc_cs3_aes_admitted(key@,input@),
        match r {Ok(v)=>v.len()==input.len() && v@==cbc_cs3_aes_reference(key@,iv@,input@,true),Err(_)=>true},
{cbc_cs3(key,iv,input,true)}

#[verifier::opaque]
spec fn legacy_key_prefix(nonce:Seq<u8>,raw:Seq<u8>,count:nat) -> Seq<u8>
    decreases count,
{
    if count==0 {Seq::empty()}else{
        legacy_key_prefix(nonce,raw,(count-1) as nat)
            +aes::aes_raw_encrypt_reference(nonce,raw.subrange((count as int-1)*16,count as int*16))
    }
}
proof fn legacy_key_prefix_step(nonce:Seq<u8>,raw:Seq<u8>,count:nat)
    requires nonce.len()==16,count*16<=raw.len(),
    ensures legacy_key_prefix(nonce,raw,count).len()==count*16,
        count==0 ==> legacy_key_prefix(nonce,raw,count)==Seq::<u8>::empty(),
        count>0 ==> legacy_key_prefix(nonce,raw,count)==legacy_key_prefix(nonce,raw,(count-1) as nat)
            +aes::aes_raw_encrypt_reference(nonce,raw.subrange((count as int-1)*16,count as int*16)),
    decreases count,
{
    reveal(legacy_key_prefix);
    if count>0 {
        legacy_key_prefix_step(nonce,raw,(count-1) as nat);
        aes::aes_raw_reference_roundtrips(nonce,raw.subrange((count as int-1)*16,count as int*16));
    }
}
spec fn dot_name(raw:Seq<u8>) -> bool {raw==seq![46u8] || raw==seq![46u8,46u8]}
fn checked_dot_name(raw:&[u8]) -> (r:bool)
    ensures r==dot_name(raw@),
{
    let dot=[46u8];let dotdot=[46u8,46u8];
    proof {
        assert(dot@ =~= seq![46u8]);
        assert(dotdot@ =~= seq![46u8,46u8]);
    }
    let one=bytes::equal(raw,dot.as_slice());
    one || bytes::equal(raw,dotdot.as_slice())
}
pub open spec fn plain_name(raw:Seq<u8>) -> bool {
    0<raw.len()<=255 && forall|i:int| 0<=i<raw.len() ==> raw[i]!=0 && raw[i]!=47
}
#[verifier::opaque]
spec fn first_zero(raw:Seq<u8>,start:nat) -> nat
    decreases raw.len()-start,
{
    if start>=raw.len() {raw.len()}else if raw[start as int]==0 {start}else{first_zero(raw,start+1)}
}
proof fn first_zero_characterization(raw:Seq<u8>,start:nat,end:nat)
    requires start<=end<=raw.len(),
        forall|i:int| start<=i<end ==> raw[i]!=0,
        end==raw.len() || raw[end as int]==0,
    ensures first_zero(raw,start)==end,
    decreases end-start,
{
    reveal(first_zero);
    if start<end {first_zero_characterization(raw,start+1,end);}
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Role { Data, Name }
// Secret storage has no destructor. Retirement publishes one bounded replacement;
// no allocation or potentially unwinding Vec mutation occurs during Drop.
struct CipherSecret {bytes:[u8;64],length:usize,hashed_inode:u32,retired:bool}
pub struct CipherKey {
    context:Context,filesystem_uuid:[u8;16],inode:u64,geometry:Geometry,
    role:Role,mode:u8,unit_bits:u8,secret:CipherSecret,
}
fn secret_from_slice(raw:&[u8],hashed_inode:u32) -> (r:Result<CipherSecret,Error>)
    ensures match r {
        Ok(s)=>!s.retired && s.length==raw.len() && s.hashed_inode==hashed_inode
            && (s.length==16 || s.length==32 || s.length==64)
            && s.bytes@.take(s.length as int)==raw@
            && forall|i:int| s.length<=i<64 ==> s.bytes@[i]==0,
        Err(_)=>raw.len()!=16 && raw.len()!=32 && raw.len()!=64,
    },
{
    if raw.len()!=16 && raw.len()!=32 && raw.len()!=64 {return Err(Error::KeyLength);}
    let mut bytes=[0u8;64];let mut i=0usize;
    while i<raw.len()
        invariant i<=raw.len()<=64,
            forall|j:int| 0<=j<64 ==> bytes@[j]==if j<i {raw@[j]}else{0u8},
        decreases raw.len()-i,
    {bytes[i]=raw[i];i+=1;}
    proof {assert(bytes@.take(raw.len() as int) =~= raw@);}
    Ok(CipherSecret {bytes,length:raw.len(),hashed_inode,retired:false})
}
spec fn selected_mode(c:&Context,role:Role) -> u8 {
    if role==Role::Data {c.context_policy().policy_fields().1}else{c.context_policy().policy_fields().2}
}
spec fn supported_bytes(mode:u8,role:Role) -> nat {
    if role==Role::Data {if mode==1 {64}else{0}}
    else if mode==4 {32}else if mode==6 {16}else{0}
}
proof fn iv_flag_partition(flags:u8)
    ensures (flags & 24==0)==(flags & 8==0 && flags & 16==0),
        flags & 24!=0 && flags & 8==0 ==> flags & 16!=0,
{
    assert((flags & 24==0)==(flags & 8==0 && flags & 16==0)) by(bit_vector);
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
            && self.context.context_policy().policy_valid()
            && self.context.context_policy().accepts_geometry(self.geometry)
            && self.unit_bits==(if self.context.context_policy().policy_fields().4==0 {
                self.geometry.filesystem_block_bits
            }else{self.context.context_policy().policy_fields().4})
            && self.secret.length==supported_bytes(self.mode,self.role) && self.secret.length<=64
            && (self.secret.retired ==> self.secret.hashed_inode==0
                && forall|i:int| 0<=i<64 ==> self.secret.bytes@[i]==0)
    }
    pub closed spec fn cipher_binding(&self,uuid:[u8;16],inode:u64,c:&Context,role:Role) -> bool {
        !self.secret.retired && self.filesystem_uuid==uuid && self.inode==inode && self.role==role
            && self.context.context_encoding()==c.context_encoding()
    }
    pub closed spec fn cipher_retired(&self) -> bool {self.secret.retired}
    pub closed spec fn cipher_material(&self) -> Seq<u8> {self.secret.bytes@.take(self.secret.length as int)}
    pub closed spec fn cipher_index_admitted(&self,index:u64) -> bool {
        index<=self.geometry.max_data_unit_index && (self.role!=Role::Name || index==0)
            && (self.context.context_policy().policy_fields().3 & 24==0
                || (index<=0xffff_ffff && self.inode<=0xffff_ffff))
    }
    pub closed spec fn cipher_iv_reference(&self,index:u64) -> Seq<u8> {
        crate::fscrypt_context::iv_wire(self.context,self.inode,index,self.role==Role::Name,self.secret.hashed_inode)
    }
    pub closed spec fn cipher_data_reference(&self,index:u64,input:Seq<u8>,decrypt:bool) -> Seq<u8> {
        xts_aes256_reference(self.cipher_material(),self.cipher_iv_reference(index),input,decrypt)
    }
    pub closed spec fn cipher_legacy_reference(&self,raw:Seq<u8>) -> Seq<u8> {
        legacy_key_prefix(self.context.context_nonce(),raw,supported_bytes(self.mode,self.role)/16)
    }
    pub closed spec fn name_padded_reference(&self,input:Seq<u8>,maximum:u32) -> Seq<u8> {
        match self.context.context_policy().padded_filename_model(input.len() as u32,maximum) {
            Some(length)=>input+Seq::new((length as nat-input.len()) as nat,|i:int|0u8),
            None=>Seq::empty(),
        }
    }
    pub closed spec fn cipher_name_encrypt_reference(&self,input:Seq<u8>,maximum:u32) -> Seq<u8> {
        if dot_name(input) {input}else{
            cbc_cs3_aes_reference(self.cipher_material(),self.cipher_iv_reference(0),
                self.name_padded_reference(input,maximum),false)
        }
    }
    pub closed spec fn cipher_name_decrypt_reference(&self,input:Seq<u8>) -> Seq<u8> {
        if dot_name(input) {input}else{
            let padded=cbc_cs3_aes_reference(self.cipher_material(),self.cipher_iv_reference(0),input,true);
            padded.take(first_zero(padded,0) as int)
        }
    }
    pub closed spec fn binding_view(&self) -> (u64,Role,Seq<u8>,[u8;16]) {
        (self.inode,self.role,self.context.context_encoding(),self.filesystem_uuid)
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {self.cipher_valid()}
    pub fn from_v2(master:&MasterKeyV2,context:Context,filesystem_uuid:[u8;16],inode:u64,geometry:Geometry,role:Role) -> (r:Result<Self,Error>)
        ensures match r {Ok(k)=>k.cipher_valid() && k.cipher_binding(filesystem_uuid,inode,&context,role)
            && k.cipher_material()==master.derived_reference(context,filesystem_uuid,role==Role::Name),Err(_)=>true},
    {
        let mode=selected(&context,role);let size=supported(mode,role)?;
        let unit_bits=match context.policy().validate(geometry){Ok(v)=>v,Err(_)=>return Err(Error::Policy)};
        let key=match master.derive(&context,filesystem_uuid,matches!(role,Role::Name)){Ok(v)=>v,Err(_)=>return Err(Error::Binding)};
        if key.len()!=size {return Err(Error::KeyLength);}
        if mode==1 && bytes::equal(&key[..32],&key[32..]) {return Err(Error::WeakKey);}
        let admitted_iv=match master.keyed_iv(&context,geometry,inode,0,matches!(role,Role::Name)) {
            Ok(v)=>v,Err(_)=>return Err(Error::Binding),
        };
        proof {assert(inode>0);}
        let (_,_,_,flags,_)=context.policy().fields();
        let hashed_inode=if flags & 16!=0 {match master.inode_hash(inode){Ok(v)=>v,Err(_)=>return Err(Error::Binding)}}else{0};
        let secret=secret_from_slice(key.as_slice(),hashed_inode)?;
        Ok(Self {context,filesystem_uuid,inode,geometry,role,mode,unit_bits,secret})
    }
    /// Legacy descriptors are caller-provisioned names, not key verification.
    pub fn from_v1(raw_master:&[u8],provisioned_descriptor:&[u8],context:Context,filesystem_uuid:[u8;16],inode:u64,geometry:Geometry,role:Role) -> (r:Result<Self,Error>)
        ensures match r {Ok(k)=>k.cipher_valid() && k.cipher_binding(filesystem_uuid,inode,&context,role)
            && k.cipher_material()==k.cipher_legacy_reference(raw_master@),Err(_)=>true},
    {
        let (version,_,_,_,_)=context.policy().fields();
        if version!=0 || provisioned_descriptor.len()!=8 || !bytes::equal(context.policy().key_specifier().as_slice(),provisioned_descriptor) {return Err(Error::Binding);}
        let mode=selected(&context,role);let size=supported(mode,role)?;
        if raw_master.len()<size || raw_master.len()>64 {return Err(Error::KeyLength);}
        let unit_bits=match context.policy().validate(geometry){Ok(v)=>v,Err(_)=>return Err(Error::Policy)};
        let admitted_iv=match context.context_iv(geometry,inode,0,matches!(role,Role::Name)) {
            Ok(v)=>v,Err(_)=>return Err(Error::Binding),
        };
        proof {assert(inode>0);}
        let nonce=context.nonce();let kdf=aes_key(&nonce)?;let mut key=Vec::new();let mut at=0usize;
        proof {legacy_key_prefix_step(nonce@,raw_master@,0);}
        while at<size
            invariant at<=size<=64,size%16==0,at%16==0,key.len()==at,raw_master.len()>=size,
                inode>0,aes_material(&kdf,nonce@),nonce@==context.context_nonce(),
                key@==legacy_key_prefix(nonce@,raw_master@,(at/16) as nat),
                size==supported_bytes(mode,role),mode==selected_mode(&context,role),
                9<=unit_bits<=geometry.filesystem_block_bits<=16,
                context.context_policy().policy_valid() && context.context_policy().accepts_geometry(geometry),
                unit_bits==(if context.context_policy().policy_fields().4==0 {geometry.filesystem_block_bits}
                    else{context.context_policy().policy_fields().4}),
            decreases size-at,
        {
            append(&mut key,&enc_raw(&kdf,block(raw_master,at),Ghost(nonce@))?);
            proof {legacy_key_prefix_step(nonce@,raw_master@,(at/16+1) as nat);}
            at+=16;
        }
        if mode==1 && bytes::equal(&key[..32],&key[32..]) {return Err(Error::WeakKey);}
        let secret=secret_from_slice(key.as_slice(),0)?;
        Ok(Self {context,filesystem_uuid,inode,geometry,role,mode,unit_bits,secret})
    }
    pub fn binding(&self) -> (r:(u64,Role,Vec<u8>,[u8;16]))
        ensures (r.0,r.1,r.2@,r.3)==self.binding_view(),
    {(self.inode,self.role,self.context.encode_context(),self.filesystem_uuid)}
    fn key_material(&self) -> (r:&[u8])
        ensures self.cipher_valid(),r@==self.cipher_material(),
    {
        proof {use_type_invariant(self);}
        &self.secret.bytes[..self.secret.length]
    }
    fn check(&self,filesystem_uuid:[u8;16],inode:u64,context:&Context,role:Role) -> (r:Result<(),Error>)
        ensures r.is_ok()==self.cipher_binding(filesystem_uuid,inode,context,role),
    {
        if self.secret.retired {return Err(Error::Retired);}
        let uuid_equal=bytes::equal(&self.filesystem_uuid,&filesystem_uuid);
        proof {
            uuid_array_views(self.filesystem_uuid,filesystem_uuid);
            assert(uuid_equal==(self.filesystem_uuid==filesystem_uuid));
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
        Ok(())
    }
    fn iv(&self,index:u64) -> (r:Result<[u8;16],Error>)
        ensures self.cipher_valid(),r.is_ok()==self.cipher_index_admitted(index),
            match r {Ok(v)=>v@==self.cipher_iv_reference(index),Err(_)=>true},
    {
        proof {use_type_invariant(self);}
        if index>self.geometry.max_data_unit_index || (matches!(self.role,Role::Name) && index!=0) {return Err(Error::Index);}
        let (_,contents,names,flags,_)=self.context.policy().fields();let mut value=index;
        proof {
            if flags & 4!=0 {
                assert(contents==9 && names==9);
                assert(supported_bytes(self.mode,self.role)==0);
                assert(false);
            }
            assert(flags & 4==0);
        }
        proof {iv_flag_partition(flags);}
        if flags & 24!=0 {
            if index>0xffff_ffff || self.inode>0xffff_ffff {return Err(Error::Index);}
            if flags & 8!=0 {
                value=(self.inode<<32)|index;
                proof {
                    let number=self.inode;
                    assert((number<<32)|index==index|(number<<32)) by(bit_vector);
                }
            }
            else{
                let index32=index as u32;
                let hash=self.secret.hashed_inode;
                let word=hash.wrapping_add(index32);
                proof {
                    assert(flags & 16!=0);
                    assert(index32 as nat==index as nat);
                    assert(word as nat==(hash as nat+index32 as nat)%4294967296);
                }
                value=word as u64;
            }
        }
        proof {
            self.context.common_iv_layout(self.inode,index,self.role==Role::Name,self.secret.hashed_inode);
            assert(value==if flags & 8!=0 {index | (self.inode<<32)}
                else if flags & 16!=0 {((self.secret.hashed_inode as nat+index as nat)%4294967296) as u64}
                else{index});
        }
        let mut iv=[0u8;16];let mut i=0usize;
        while i<8
            invariant i<=8,self.cipher_valid(),
                iv@==Seq::new(16,|j:int| if j<i {(value>>((j as u32)*8)) as u8}else{0u8}),
            decreases 8-i,
        {iv[i]=(value>>(8*i)) as u8;i+=1;}
        proof {assert(iv@==self.cipher_iv_reference(index));}
        Ok(iv)
    }
    pub fn encrypt_data(&self,filesystem_uuid:[u8;16],inode:u64,context:&Context,index:u64,plaintext:&[u8]) -> (r:Result<Vec<u8>,Error>)
        ensures self.cipher_valid(),match r {Ok(v)=>self.cipher_binding(filesystem_uuid,inode,context,Role::Data)
            && self.cipher_index_admitted(index) && v.len()==plaintext.len()
            && v@==self.cipher_data_reference(index,plaintext@,false),Err(_)=>true},
    {
        proof {use_type_invariant(self);}
        self.check(filesystem_uuid,inode,context,Role::Data)?;
        if self.mode!=1 {return Err(Error::Unsupported);}
        if plaintext.len()!=1usize<<self.unit_bits {return Err(Error::Length);}
        encrypt_xts_aes256(self.key_material(),self.iv(index)?,plaintext)
    }
    pub fn decrypt_data(&self,filesystem_uuid:[u8;16],inode:u64,context:&Context,index:u64,ciphertext:&[u8]) -> (r:Result<Vec<u8>,Error>)
        ensures self.cipher_valid(),match r {Ok(v)=>self.cipher_binding(filesystem_uuid,inode,context,Role::Data)
            && self.cipher_index_admitted(index) && v.len()==ciphertext.len()
            && v@==self.cipher_data_reference(index,ciphertext@,true),Err(_)=>true},
    {
        proof {use_type_invariant(self);}
        self.check(filesystem_uuid,inode,context,Role::Data)?;
        if self.mode!=1 {return Err(Error::Unsupported);}
        if ciphertext.len()!=1usize<<self.unit_bits {return Err(Error::Length);}
        decrypt_xts_aes256(self.key_material(),self.iv(index)?,ciphertext)
    }
    pub fn encrypt_name(&self,filesystem_uuid:[u8;16],inode:u64,context:&Context,plaintext:&[u8],maximum:u32) -> (r:Result<Vec<u8>,Error>)
        ensures self.cipher_valid(),match r {Ok(v)=>self.cipher_binding(filesystem_uuid,inode,context,Role::Name)
            && plain_name(plaintext@) && v.len()<=255
            && v@==self.cipher_name_encrypt_reference(plaintext@,maximum),Err(_)=>true},
    {
        proof {use_type_invariant(self);}
        self.check(filesystem_uuid,inode,context,Role::Name)?;
        if plaintext.len()==0 || plaintext.len()>255 || maximum<16 || maximum>255 {return Err(Error::Name);}
        let mut i=0usize;
        while i<plaintext.len()
            invariant i<=plaintext.len()<=255,self.cipher_valid(),
                self.cipher_binding(filesystem_uuid,inode,context,Role::Name),
                plaintext.len()>0,
                forall|j:int| 0<=j<i ==> plaintext@[j]!=0 && plaintext@[j]!=47,
            decreases plaintext.len()-i,
        {if plaintext[i]==0 || plaintext[i]==47{return Err(Error::Name);}i+=1;}
        proof {assert(plain_name(plaintext@));}
        if checked_dot_name(plaintext) {
            proof {assert(dot_name(plaintext@));}
            return Ok(copy(plaintext));
        }
        proof {assert(!dot_name(plaintext@));}
        let len=match self.context.policy().padded_filename_len(plaintext.len() as u32,maximum){Ok(n)=>n as usize,Err(_)=>return Err(Error::Name)};
        let mut padded=copy(plaintext);
        while padded.len()<len
            invariant plaintext.len()<=padded.len()<=len<=255,self.cipher_valid(),
                self.cipher_binding(filesystem_uuid,inode,context,Role::Name),
                plain_name(plaintext@),!dot_name(plaintext@),
                self.context.context_policy().padded_filename_model(plaintext.len() as u32,maximum)==Some(len as u32),
                padded@==plaintext@+Seq::new((padded.len()-plaintext.len()) as nat,|j:int|0u8),
            decreases len-padded.len(),
        {
            padded.push(0);
            assert(padded@ =~= plaintext@+Seq::new((padded.len()-plaintext.len()) as nat,|j:int|0u8));
        }
        proof {assert(padded@==self.name_padded_reference(plaintext@,maximum));}
        encrypt_cbc_cs3_aes(self.key_material(),self.iv(0)?,padded.as_slice())
    }
    pub fn decrypt_name(&self,filesystem_uuid:[u8;16],inode:u64,context:&Context,ciphertext:&[u8]) -> (r:Result<Vec<u8>,Error>)
        ensures self.cipher_valid(),match r {Ok(v)=>self.cipher_binding(filesystem_uuid,inode,context,Role::Name)
            && plain_name(v@) && v.len()<=255
            && v@==self.cipher_name_decrypt_reference(ciphertext@),Err(_)=>true},
    {
        proof {use_type_invariant(self);}
        self.check(filesystem_uuid,inode,context,Role::Name)?;
        if checked_dot_name(ciphertext) {
            proof {assert(dot_name(ciphertext@));assert(plain_name(ciphertext@));}
            return Ok(copy(ciphertext));
        }
        if ciphertext.len()<16 || ciphertext.len()>255 {return Err(Error::Name);}
        let padded=decrypt_cbc_cs3_aes(self.key_material(),self.iv(0)?,ciphertext)?;
        let mut end=0usize;
        while end<padded.len() && padded[end]!=0
            invariant end<=padded.len()<=255,self.cipher_valid(),
                self.cipher_binding(filesystem_uuid,inode,context,Role::Name),
                !dot_name(ciphertext@),
                padded@==cbc_cs3_aes_reference(self.cipher_material(),self.cipher_iv_reference(0),ciphertext@,true),
                forall|j:int| 0<=j<end ==> padded@[j]!=0 && padded@[j]!=47,
            decreases padded.len()-end,
        {if padded[end]==47{return Err(Error::Name);}end+=1;}
        if end==0 {return Err(Error::Name);}
        proof {first_zero_characterization(padded@,0,end as nat);}
        Ok(copy(&padded[..end]))
    }
    pub fn retire_cipher(&mut self)
        ensures final(self).cipher_valid(),final(self).cipher_retired(),
            final(self).cipher_material().len()==old(self).cipher_material().len(),
            forall|i:int| 0<=i<final(self).cipher_material().len() ==> final(self).cipher_material()[i]==0,
        opens_invariants none
        no_unwind
    {
        proof {use_type_invariant(&*self);}
        self.secret=CipherSecret {bytes:[0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8],
            length:self.secret.length,hashed_inode:0,retired:true};
    }
}
/// Provisioning selects a legacy named key or a v2 verified identifier.
/// This enum carries key material references, not filesystem permissions.
pub enum MasterKeyRef<'a> { V1 {raw:&'a[u8],descriptor:&'a[u8]}, V2(&'a MasterKeyV2) }
pub fn prepare_cipher(master:MasterKeyRef<'_>,context:Context,filesystem_uuid:[u8;16],inode:u64,geometry:Geometry,role:Role)
    -> (r:Result<CipherKey,Error>)
    ensures match r {
        Ok(k)=>k.cipher_valid() && k.cipher_binding(filesystem_uuid,inode,&context,role)
            && match master {
                MasterKeyRef::V1 {raw,descriptor:_}=>context.context_policy().policy_fields().0==0
                    && k.cipher_material()==k.cipher_legacy_reference(raw@),
                MasterKeyRef::V2(key)=>context.context_policy().policy_fields().0==2
                    && k.cipher_material()==key.derived_reference(context,filesystem_uuid,role==Role::Name),
            },
        Err(_)=>true,
    },
{
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
