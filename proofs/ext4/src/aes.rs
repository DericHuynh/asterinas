// SPDX-License-Identifier: MPL-2.0

//! Executable AES-128/AES-256 block transform (FIPS 197).
//! S-box computation uses fixed-step field arithmetic, with no secret-indexed
//! table. Constant-time compilation and physical key erasure are separate work.
//! The implementation and destructor are awaiting Verus refinement.

use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error { KeyLength, Retired }


struct FieldProduct { a:u8, b:u8, product:u8 }
spec fn field_double(a:u8) -> u8 {
    (a<<1) ^ (if a>>7==0 {0u8}else{0x1bu8})
}
spec fn field_step(s:FieldProduct) -> FieldProduct {
    FieldProduct {a:field_double(s.a),b:s.b>>1,
        product:s.product^(if s.b&1==0 {0u8}else{s.a})}
}
#[verifier::opaque]
spec fn field_steps(a:u8,b:u8,n:nat) -> FieldProduct
    decreases n
{
    if n==0 {FieldProduct {a,b,product:0}}
    else {field_step(field_steps(a,b,(n-1) as nat))}
}
#[verifier::opaque]
spec fn field_mul(a:u8,b:u8) -> u8 {field_steps(a,b,8).product}
#[verifier::opaque]
spec fn field_inverse(a:u8) -> u8 {
    let a2=field_mul(a,a);let a4=field_mul(a2,a2);let a8=field_mul(a4,a4);
    let a16=field_mul(a8,a8);let a32=field_mul(a16,a16);
    let a64=field_mul(a32,a32);let a128=field_mul(a64,a64);
    field_mul(field_mul(field_mul(field_mul(field_mul(field_mul(a2,a4),a8),a16),a32),a64),a128)
}
spec fn rotate_byte(x:u8,count:u32) -> u8 {
    let n=count%8;if n==0 {x}else{(x<<n)|(x>>(8-n))}
}
#[verifier::opaque]
spec fn substitute(a:u8,backward:bool) -> u8 {
    if backward {field_inverse(rotate_byte(a,1)^rotate_byte(a,3)^rotate_byte(a,6)^0x05)}
    else {let x=field_inverse(a);x^rotate_byte(x,1)^rotate_byte(x,2)^rotate_byte(x,3)^rotate_byte(x,4)^0x63}
}
spec fn keyed(s:Seq<u8>,key:Seq<u8>,round:nat) -> Seq<u8> {
    Seq::new(16,|i:int| s[i]^key[(round*16) as int+i])
}
spec fn substituted(s:Seq<u8>,backward:bool) -> Seq<u8> {
    Seq::new(16,|i:int| substitute(s[i],backward))
}
spec fn shifted(s:Seq<u8>,backward:bool) -> Seq<u8> {
    Seq::new(16,|i:int| {
        let row=i%4;let col=i/4;
        let selected=if backward {(col+4-row)%4}else{(col+row)%4};
        s[selected*4+row]
    })
}
spec fn mixed_byte(s:Seq<u8>,i:int,backward:bool) -> u8 {
    let base=(i/4)*4;let row=i%4;
    let a=s[base];let b=s[base+1];let c=s[base+2];let d=s[base+3];
    if backward {
        if row==0 {field_mul(a,14)^field_mul(b,11)^field_mul(c,13)^field_mul(d,9)}
        else if row==1 {field_mul(a,9)^field_mul(b,14)^field_mul(c,11)^field_mul(d,13)}
        else if row==2 {field_mul(a,13)^field_mul(b,9)^field_mul(c,14)^field_mul(d,11)}
        else {field_mul(a,11)^field_mul(b,13)^field_mul(c,9)^field_mul(d,14)}
    } else {
        if row==0 {field_mul(a,2)^field_mul(b,3)^c^d}
        else if row==1 {a^field_mul(b,2)^field_mul(c,3)^d}
        else if row==2 {a^b^field_mul(c,2)^field_mul(d,3)}
        else {field_mul(a,3)^b^c^field_mul(d,2)}
    }
}
spec fn mixed(s:Seq<u8>,backward:bool) -> Seq<u8> {
    Seq::new(16,|i:int| mixed_byte(s,i,backward))
}
spec fn encrypt_round(s:Seq<u8>,key:Seq<u8>,round:nat,rounds:nat) -> Seq<u8> {
    let t=shifted(substituted(s,false),false);
    keyed(if round<rounds {mixed(t,false)}else{t},key,round)
}
spec fn encrypted(input:Seq<u8>,key:Seq<u8>,rounds:nat,n:nat) -> Seq<u8>
    decreases n
{
    if n==0 {keyed(input,key,0)}
    else {encrypt_round(encrypted(input,key,rounds,(n-1) as nat),key,n,rounds)}
}
spec fn decrypt_round(s:Seq<u8>,key:Seq<u8>,round:nat) -> Seq<u8> {
    let t=keyed(substituted(shifted(s,true),true),key,round);
    if round>0 {mixed(t,true)}else{t}
}
spec fn decrypted(input:Seq<u8>,key:Seq<u8>,rounds:nat,n:nat) -> Seq<u8>
    decreases n
{
    if n==0 {keyed(input,key,rounds)}
    else {decrypt_round(decrypted(input,key,rounds,(n-1) as nat),key,(rounds-n) as nat)}
}
struct ExpandedSchedule {bytes:Seq<u8>,rcon:u8}
pub closed spec fn expanded_key_reference(key:Seq<u8>,n:nat) -> Seq<u8> {key_schedule(key,n).bytes}
spec fn schedule_word(s:ExpandedSchedule,key_len:nat) -> Seq<u8> {
    let n=s.bytes.len();let t=s.bytes.subrange((n-4) as int,n as int);
    if n%key_len==0 {
        seq![substitute(t[1],false)^s.rcon,substitute(t[2],false),substitute(t[3],false),substitute(t[0],false)]
    } else if key_len==32 && n%32==16 {
        Seq::new(4,|i:int| substitute(t[i],false))
    } else {t}
}
spec fn schedule_step(s:ExpandedSchedule,key_len:nat) -> ExpandedSchedule {
    let n=s.bytes.len();let word=schedule_word(s,key_len);
    ExpandedSchedule {
        bytes:s.bytes+Seq::new(4,|i:int| s.bytes[(n-key_len) as int+i]^word[i]),
        rcon:if n%key_len==0 {field_mul(s.rcon,2)}else{s.rcon},
    }
}
spec fn key_schedule(key:Seq<u8>,n:nat) -> ExpandedSchedule
    decreases n
{
    if n==0 {ExpandedSchedule {bytes:key,rcon:1}}
    else {schedule_step(key_schedule(key,(n-1) as nat),key.len())}
}
proof fn schedule_length(key:Seq<u8>,n:nat)
    ensures key_schedule(key,n).bytes.len()==key.len()+n*4,
    decreases n,
{
    if n>0 {schedule_length(key,(n-1) as nat);}
}

spec fn inverse_byte_property(i:nat) -> bool {
    let a=i as u8;
    substitute(substitute(a,false),true)==a && substitute(substitute(a,true),false)==a
}
spec fn inverse_bytes_checked(first:nat,end:nat) -> bool
    decreases end-first
{
    if first>=end {true}else{inverse_byte_property(first) && inverse_bytes_checked(first+1,end)}
}
proof fn checked_byte_range_contains(first:nat,end:nat,i:nat)
    requires first<=i<end<=256,inverse_bytes_checked(first,end),
    ensures inverse_byte_property(i),
    decreases i-first,
{
    if first<i {checked_byte_range_contains(first+1,end,i);}
}
proof fn byte_substitution_inverse(a:u8)
    ensures substitute(substitute(a,false),true)==a,
        substitute(substitute(a,true),false)==a,
{
    reveal(substitute);
    reveal(field_inverse);
    reveal(field_mul);
    reveal(field_steps);
    if a<64 {
        assert(inverse_bytes_checked(0,64)) by(compute);
        checked_byte_range_contains(0,64,a as nat);
    } else if a<128 {
        assert(inverse_bytes_checked(64,128)) by(compute);
        checked_byte_range_contains(64,128,a as nat);
    } else if a<192 {
        assert(inverse_bytes_checked(128,192)) by(compute);
        checked_byte_range_contains(128,192,a as nat);
    } else {
        assert(inverse_bytes_checked(192,256)) by(compute);
        checked_byte_range_contains(192,256,a as nat);
    }
}

proof fn state_substitution_inverse(state:Seq<u8>)
    requires state.len()==16,
    ensures substituted(substituted(state,false),true)==state,
        substituted(substituted(state,true),false)==state,
{
    assert forall|i:int| 0<=i<16 implies
        substituted(substituted(state,false),true)[i]==state[i]
        && substituted(substituted(state,true),false)[i]==state[i] by {
        byte_substitution_inverse(state[i]);
    }
    assert(substituted(substituted(state,false),true) =~= state);
    assert(substituted(substituted(state,true),false) =~= state);
}
proof fn state_shift_inverse(state:Seq<u8>)
    requires state.len()==16,
    ensures shifted(shifted(state,false),true)==state,
        shifted(shifted(state,true),false)==state,
{
    assert forall|i:int| 0<=i<16 implies
        shifted(shifted(state,false),true)[i]==state[i]
        && shifted(shifted(state,true),false)[i]==state[i] by {
        assert(i%4>=0 && i/4>=0);
    }
    assert(shifted(shifted(state,false),true) =~= state);
    assert(shifted(shifted(state,true),false) =~= state);
}

proof fn state_key_inverse(state:Seq<u8>,key:Seq<u8>,round:nat)
    requires state.len()==16,(round+1)*16<=key.len(),
    ensures keyed(keyed(state,key,round),key,round)==state,
{
    assert forall|i:int| 0<=i<16 implies
        keyed(keyed(state,key,round),key,round)[i]==state[i] by {
        let a=state[i];let k=key[(round*16) as int+i];
        assert((a^k)^k==a) by(bit_vector);
    }
    assert(keyed(keyed(state,key,round),key,round) =~= state);
}
proof fn state_substitution_commutes_with_shift(state:Seq<u8>,backward_substitute:bool,backward_shift:bool)
    requires state.len()==16,
    ensures shifted(substituted(state,backward_substitute),backward_shift)
        ==substituted(shifted(state,backward_shift),backward_substitute),
{
    assert(shifted(substituted(state,backward_substitute),backward_shift)
        =~= substituted(shifted(state,backward_shift),backward_substitute));
}
spec fn pre_round(state:Seq<u8>) -> Seq<u8> {shifted(substituted(state,false),false)}
spec fn inverse_pre_round(state:Seq<u8>) -> Seq<u8> {substituted(shifted(state,true),true)}
proof fn pre_round_inverse(state:Seq<u8>)
    requires state.len()==16,
    ensures inverse_pre_round(pre_round(state))==state,
        pre_round(inverse_pre_round(state))==state,
{
    state_shift_inverse(substituted(state,false));
    state_substitution_inverse(state);
    state_substitution_inverse(shifted(state,true));
    state_shift_inverse(state);
}

// A six-coefficient linear polynomial form of the FIPS 197 column matrices.
// The connection to the actual eight-step field multiply is checked over
// every byte, rather than introduced as an algebraic premise.
spec fn coefficient_product(a:u8,c:u8) -> u8 {
    let a2=field_double(a);let a4=field_double(a2);let a8=field_double(a4);
    if c==2 {a2}else if c==3 {a2^a}else if c==9 {a8^a}
    else if c==11 {a8^a2^a}else if c==13 {a8^a4^a}else if c==14 {a8^a4^a2}else{0u8}
}
spec fn coefficient_row(i:nat) -> bool {
    let a=i as u8;
    field_mul(a,2)==coefficient_product(a,2) && field_mul(a,3)==coefficient_product(a,3)
        && field_mul(a,9)==coefficient_product(a,9) && field_mul(a,11)==coefficient_product(a,11)
        && field_mul(a,13)==coefficient_product(a,13) && field_mul(a,14)==coefficient_product(a,14)
}
spec fn coefficients_checked(first:nat,end:nat) -> bool
    decreases end-first
{
    if first>=end {true}else{coefficient_row(first) && coefficients_checked(first+1,end)}
}
proof fn checked_coefficients_contain(first:nat,end:nat,i:nat)
    requires first<=i<end<=256,coefficients_checked(first,end),
    ensures coefficient_row(i),
    decreases i-first,
{
    if first<i {checked_coefficients_contain(first+1,end,i);}
}
proof fn byte_mix_coefficients(a:u8)
    ensures field_mul(a,2)==coefficient_product(a,2),field_mul(a,3)==coefficient_product(a,3),
        field_mul(a,9)==coefficient_product(a,9),field_mul(a,11)==coefficient_product(a,11),
        field_mul(a,13)==coefficient_product(a,13),field_mul(a,14)==coefficient_product(a,14),
{
    reveal(field_mul);reveal(field_steps);
    if a<64 {
        assert(coefficients_checked(0,64)) by(compute);
        checked_coefficients_contain(0,64,a as nat);
    }else if a<128 {
        assert(coefficients_checked(64,128)) by(compute);
        checked_coefficients_contain(64,128,a as nat);
    }else if a<192 {
        assert(coefficients_checked(128,192)) by(compute);
        checked_coefficients_contain(128,192,a as nat);
    }else {
        assert(coefficients_checked(192,256)) by(compute);
        checked_coefficients_contain(192,256,a as nat);
    }
}
spec fn polynomial_column(a:u8,b:u8,c:u8,d:u8,row:u8,backward:bool) -> u8 {
    if backward {
        if row==0 {coefficient_product(a,14)^coefficient_product(b,11)^coefficient_product(c,13)^coefficient_product(d,9)}
        else if row==1 {coefficient_product(a,9)^coefficient_product(b,14)^coefficient_product(c,11)^coefficient_product(d,13)}
        else if row==2 {coefficient_product(a,13)^coefficient_product(b,9)^coefficient_product(c,14)^coefficient_product(d,11)}
        else {coefficient_product(a,11)^coefficient_product(b,13)^coefficient_product(c,9)^coefficient_product(d,14)}
    }else {
        if row==0 {coefficient_product(a,2)^coefficient_product(b,3)^c^d}
        else if row==1 {a^coefficient_product(b,2)^coefficient_product(c,3)^d}
        else if row==2 {a^b^coefficient_product(c,2)^coefficient_product(d,3)}
        else {coefficient_product(a,3)^b^c^coefficient_product(d,2)}
    }
}
proof fn polynomial_columns_inverse(a:u8,b:u8,c:u8,d:u8,row:u8)
    ensures polynomial_column(
        polynomial_column(a,b,c,d,0,false),polynomial_column(a,b,c,d,1,false),
        polynomial_column(a,b,c,d,2,false),polynomial_column(a,b,c,d,3,false),row,true)
            ==if row==0 {a}else if row==1 {b}else if row==2 {c}else{d},
        polynomial_column(
        polynomial_column(a,b,c,d,0,true),polynomial_column(a,b,c,d,1,true),
        polynomial_column(a,b,c,d,2,true),polynomial_column(a,b,c,d,3,true),row,false)
            ==if row==0 {a}else if row==1 {b}else if row==2 {c}else{d},
{
    assert(polynomial_column(
        polynomial_column(a,b,c,d,0,false),polynomial_column(a,b,c,d,1,false),
        polynomial_column(a,b,c,d,2,false),polynomial_column(a,b,c,d,3,false),row,true)
            ==if row==0 {a}else if row==1 {b}else if row==2 {c}else{d}) by(bit_vector);
    assert(polynomial_column(
        polynomial_column(a,b,c,d,0,true),polynomial_column(a,b,c,d,1,true),
        polynomial_column(a,b,c,d,2,true),polynomial_column(a,b,c,d,3,true),row,false)
            ==if row==0 {a}else if row==1 {b}else if row==2 {c}else{d}) by(bit_vector);
}
proof fn mixed_byte_is_polynomial(state:Seq<u8>,i:int,backward:bool)
    requires state.len()==16,0<=i<16,
    ensures mixed_byte(state,i,backward)==polynomial_column(
        state[(i/4)*4],state[(i/4)*4+1],state[(i/4)*4+2],state[(i/4)*4+3],(i%4) as u8,backward),
{
    let base=(i/4)*4;
    byte_mix_coefficients(state[base]);byte_mix_coefficients(state[base+1]);
    byte_mix_coefficients(state[base+2]);byte_mix_coefficients(state[base+3]);
}
proof fn state_mix_inverse(state:Seq<u8>)
    requires state.len()==16,
    ensures mixed(mixed(state,false),true)==state,mixed(mixed(state,true),false)==state,
{
    assert forall|i:int| 0<=i<16 implies
        mixed(mixed(state,false),true)[i]==state[i]
        && mixed(mixed(state,true),false)[i]==state[i] by {
        let base=(i/4)*4;let row=(i%4) as u8;
        assert(0<=base<=12 && base%4==0 && 0<=i%4<4 && i==base+i%4);
        mixed_byte_is_polynomial(state,base,false);mixed_byte_is_polynomial(state,base+1,false);
        mixed_byte_is_polynomial(state,base+2,false);mixed_byte_is_polynomial(state,base+3,false);
        mixed_byte_is_polynomial(state,base,true);mixed_byte_is_polynomial(state,base+1,true);
        mixed_byte_is_polynomial(state,base+2,true);mixed_byte_is_polynomial(state,base+3,true);
        mixed_byte_is_polynomial(mixed(state,false),i,true);
        mixed_byte_is_polynomial(mixed(state,true),i,false);
        polynomial_columns_inverse(state[base],state[base+1],state[base+2],state[base+3],row);
    }
    assert(mixed(mixed(state,false),true) =~= state);
    assert(mixed(mixed(state,true),false) =~= state);
}

proof fn round_reference_lengths(input:Seq<u8>,key:Seq<u8>,rounds:nat,n:nat)
    ensures encrypted(input,key,rounds,n).len()==16,decrypted(input,key,rounds,n).len()==16,
{}

// State cancellation is proved in the coordinates just before SubBytes.
// This matches the executable decryption order, including its final no-mix
// round and the special final encryption round.
proof fn undo_regular_encrypt_round(state:Seq<u8>,key:Seq<u8>,round:nat,rounds:nat)
    requires state.len()==16,0<round<rounds,(round+1)*16<=key.len(),
    ensures decrypt_round(pre_round(encrypt_round(state,key,round,rounds)),key,round)==pre_round(state),
{
    pre_round_inverse(encrypt_round(state,key,round,rounds));
    state_key_inverse(mixed(pre_round(state),false),key,round);
    state_mix_inverse(pre_round(state));
}
proof fn undo_initial_key_round(state:Seq<u8>,key:Seq<u8>)
    requires state.len()==16,16<=key.len(),
    ensures decrypt_round(pre_round(keyed(state,key,0)),key,0)==state,
{
    pre_round_inverse(keyed(state,key,0));
    state_key_inverse(state,key,0);
}
proof fn redo_regular_decrypt_round(state:Seq<u8>,key:Seq<u8>,round:nat,rounds:nat)
    requires state.len()==16,0<round<rounds,(round+1)*16<=key.len(),
    ensures encrypt_round(inverse_pre_round(decrypt_round(state,key,round)),key,round,rounds)
        ==inverse_pre_round(state),
{
    pre_round_inverse(decrypt_round(state,key,round));
    state_mix_inverse(keyed(inverse_pre_round(state),key,round));
    state_key_inverse(inverse_pre_round(state),key,round);
}
proof fn decrypt_encrypted_prefix(input:Seq<u8>,key:Seq<u8>,rounds:nat,n:nat)
    requires input.len()==16,0<rounds,n<rounds,(rounds+1)*16<=key.len(),
    ensures decrypted(encrypted(input,key,rounds,rounds),key,rounds,n)
        ==pre_round(encrypted(input,key,rounds,(rounds-1-n) as nat)),
    decreases n,
{
    if n==0 {
        round_reference_lengths(input,key,rounds,(rounds-1) as nat);
        state_key_inverse(pre_round(encrypted(input,key,rounds,(rounds-1) as nat)),key,rounds);
    }else{
        decrypt_encrypted_prefix(input,key,rounds,(n-1) as nat);
        let round=(rounds-n) as nat;
        assert(0<round<rounds && (round-1) as nat==(rounds-1-n) as nat);
        round_reference_lengths(input,key,rounds,(round-1) as nat);
        undo_regular_encrypt_round(encrypted(input,key,rounds,(round-1) as nat),key,round,rounds);
    }
}
proof fn encrypt_decrypted_prefix(input:Seq<u8>,key:Seq<u8>,rounds:nat,n:nat)
    requires input.len()==16,0<rounds,n<rounds,(rounds+1)*16<=key.len(),
    ensures encrypted(decrypted(input,key,rounds,rounds),key,rounds,n)
        ==inverse_pre_round(decrypted(input,key,rounds,(rounds-1-n) as nat)),
    decreases n,
{
    if n==0 {
        round_reference_lengths(input,key,rounds,(rounds-1) as nat);
        state_key_inverse(inverse_pre_round(decrypted(input,key,rounds,(rounds-1) as nat)),key,0);
    }else{
        encrypt_decrypted_prefix(input,key,rounds,(n-1) as nat);
        let prior=(rounds-n-1) as nat;
        round_reference_lengths(input,key,rounds,prior);
        redo_regular_decrypt_round(decrypted(input,key,rounds,prior),key,n,rounds);
    }
}
proof fn decrypt_encrypt_reference(input:Seq<u8>,key:Seq<u8>,rounds:nat)
    requires input.len()==16,0<rounds,(rounds+1)*16<=key.len(),
    ensures decrypted(encrypted(input,key,rounds,rounds),key,rounds,rounds)==input,
{
    decrypt_encrypted_prefix(input,key,rounds,(rounds-1) as nat);
    undo_initial_key_round(input,key);
}
proof fn encrypt_decrypt_reference(input:Seq<u8>,key:Seq<u8>,rounds:nat)
    requires input.len()==16,0<rounds,(rounds+1)*16<=key.len(),
    ensures encrypted(decrypted(input,key,rounds,rounds),key,rounds,rounds)==input,
{
    encrypt_decrypted_prefix(input,key,rounds,(rounds-1) as nat);
    pre_round_inverse(decrypted(input,key,rounds,0));
    state_key_inverse(input,key,rounds);
}

fn mul(mut a:u8,mut b:u8) -> (r:u8)
    ensures r==field_mul(a,b),
{
    proof {reveal(field_mul);}
    let ghost aa=a;let ghost bb=b;
    proof {reveal(field_steps);}
    let mut product=0u8;let mut i=0usize;
    while i<8
        invariant i<=8,a==field_steps(aa,bb,i as nat).a,
            b==field_steps(aa,bb,i as nat).b,
            product==field_steps(aa,bb,i as nat).product,
        decreases 8-i,
    {
        let ghost next=field_step(FieldProduct {a,b,product});
        proof {
            reveal(field_steps);
            assert(field_steps(aa,bb,(i+1) as nat)==field_step(field_steps(aa,bb,i as nat)));
        }
        let low=b&1;let high=a>>7;
        let low_mask=0u8.wrapping_sub(low);let high_mask=0u8.wrapping_sub(high);
        proof {
            assert((b&1)==0 || (b&1)==1) by(bit_vector);
            assert((a>>7)==0 || (a>>7)==1) by(bit_vector);
            assert(low_mask==if low==0 {0u8}else{255u8});
            assert(high_mask==if high==0 {0u8}else{255u8});
            assert(a & (if b&1==0 {0u8}else{255u8}) == if b&1==0 {0u8}else{a}) by(bit_vector);
            assert(0x1bu8 & (if a>>7==0 {0u8}else{255u8}) == if a>>7==0 {0u8}else{0x1bu8}) by(bit_vector);
        }
        product^=a & low_mask;
        a=(a<<1) ^ (0x1bu8 & high_mask);b>>=1;i+=1;
        proof {
            assert(a==next.a && b==next.b && product==next.product);
        }
    }
    product
}
fn inverse(a:u8) -> (r:u8) ensures r==field_inverse(a) {
    proof {reveal(field_inverse);}
    let a2=mul(a,a);let a4=mul(a2,a2);let a8=mul(a4,a4);let a16=mul(a8,a8);
    let a32=mul(a16,a16);let a64=mul(a32,a32);let a128=mul(a64,a64);
    mul(mul(mul(mul(mul(mul(a2,a4),a8),a16),a32),a64),a128)
}
fn rotl8(x:u8,count:u32) -> (r:u8) ensures r==rotate_byte(x,count) {
    let n=count%8;
    if n==0 {x}else{(x<<n)|(x>>(8-n))}
}
fn sbox(a:u8) -> (r:u8) ensures r==substitute(a,false) {
    proof {reveal(substitute);}
    let x=inverse(a);x^rotl8(x,1)^rotl8(x,2)^rotl8(x,3)^rotl8(x,4)^0x63
}
fn inv_sbox(a:u8) -> (r:u8) ensures r==substitute(a,true) {
    proof {reveal(substitute);}
    inverse(rotl8(a,1)^rotl8(a,3)^rotl8(a,6)^0x05)
}
fn add_key(state:&mut [u8;16],round_keys:&[u8;240],round:usize)
    requires round<=14,
    ensures final(state)@==keyed(old(state)@,round_keys@,round as nat),
{
    let mut i=0usize;
    while i<16
        invariant i<=16,round<=14,
            forall|j:int| 0<=j<16 ==> state@[j]==
                if j<i {keyed(old(state)@,round_keys@,round as nat)[j]}else{old(state)@[j]},
        decreases 16-i,
    {state[i]^=round_keys[round*16+i];i+=1;}
}
fn shift(state:&mut [u8;16],backward:bool)
    ensures final(state)@==shifted(old(state)@,backward),
{
    let old=*state;let mut row=0usize;
    while row<4
        invariant row<=4,forall|j:int| 0<=j<16 ==> state@[j]==
            if j%4<row {shifted(old@,backward)[j]}else{old@[j]},
        decreases 4-row,
    {
        let mut col=0usize;
        while col<4
            invariant row<4,col<=4,forall|j:int| 0<=j<16 ==> state@[j]==
                if j%4<row || (j%4==row && j/4<col) {shifted(old@,backward)[j]}else{old@[j]},
            decreases 4-col,
        {
            let selected=if backward {(col+4-row)%4}else{(col+row)%4};
            state[col*4+row]=old[selected*4+row];col+=1;
        }
        row+=1;
    }
}
fn mix(state:&mut [u8;16],backward:bool)
    ensures final(state)@==mixed(old(state)@,backward),
{
    let ghost original=state@;
    let mut col=0usize;
    while col<4
        invariant col<=4,forall|j:int| 0<=j<16 ==> state@[j]==
            if j<col*4 {mixed(original,backward)[j]}else{original[j]},
        decreases 4-col,
    {
        let i=col*4;let a=state[i];let b=state[i+1];let c=state[i+2];let d=state[i+3];
        if backward {
            state[i]=mul(a,14)^mul(b,11)^mul(c,13)^mul(d,9);
            state[i+1]=mul(a,9)^mul(b,14)^mul(c,11)^mul(d,13);
            state[i+2]=mul(a,13)^mul(b,9)^mul(c,14)^mul(d,11);
            state[i+3]=mul(a,11)^mul(b,13)^mul(c,9)^mul(d,14);
        } else {
            state[i]=mul(a,2)^mul(b,3)^c^d;
            state[i+1]=a^mul(b,2)^mul(c,3)^d;
            state[i+2]=a^b^mul(c,2)^mul(d,3);
            state[i+3]=mul(a,3)^b^c^mul(d,2);
        }
        col+=1;
    }
}

struct AesState {expanded:[u8;240],rounds:u8,retired:bool}
pub struct AesKey {state:AesState}
impl AesKey {
    pub closed spec fn valid_aes(&self) -> bool {
        if self.state.retired {self.state.rounds==0 && forall|i:int| 0<=i<240 ==> self.state.expanded@[i]==0}
        else {self.state.rounds==10 || self.state.rounds==14}
    }
    pub closed spec fn aes_schedule(&self) -> Seq<u8> {self.state.expanded@}
    pub closed spec fn aes_round_count(&self) -> nat {self.state.rounds as nat}
    pub closed spec fn aes_retired(&self) -> bool {self.state.retired}
    pub closed spec fn aes_encrypt_reference(&self,input:Seq<u8>) -> Seq<u8> {
        encrypted(input,self.state.expanded@,self.state.rounds as nat,self.state.rounds as nat)
    }
    pub closed spec fn aes_decrypt_reference(&self,input:Seq<u8>) -> Seq<u8> {
        decrypted(input,self.state.expanded@,self.state.rounds as nat,self.state.rounds as nat)
    }
    pub proof fn aes_reference_roundtrips(&self,input:Seq<u8>)
        requires self.valid_aes(),!self.aes_retired(),input.len()==16,
        ensures self.aes_decrypt_reference(self.aes_encrypt_reference(input))==input,
            self.aes_encrypt_reference(self.aes_decrypt_reference(input))==input,
    {
        decrypt_encrypt_reference(input,self.state.expanded@,self.state.rounds as nat);
        encrypt_decrypt_reference(input,self.state.expanded@,self.state.rounds as nat);
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {self.valid_aes()}
    pub fn new_aes_key(key:&[u8]) -> (r:Result<Self,Error>)
        ensures match r {
            Ok(k) => (key.len()==16 || key.len()==32) && k.valid_aes() && !k.aes_retired()
                && k.aes_round_count()==if key.len()==16 {10nat}else{14nat}
                && k.aes_schedule().take(((k.aes_round_count()+1)*16) as int)
                    ==expanded_key_reference(key@,(((k.aes_round_count()+1)*16-key.len())/4) as nat),
            Err(_) => key.len()!=16 && key.len()!=32,
        },
    {
        if key.len()!=16 && key.len()!=32 {return Err(Error::KeyLength);}
        let rounds=if key.len()==16 {10u8}else{14u8};let total=(rounds as usize+1)*16;
        let mut expanded=[0u8;240];let mut i=0usize;
        while i<key.len()
            invariant i<=key.len(),key.len()==16 || key.len()==32,
                forall|j:int| 0<=j<i ==> expanded@[j]==key@[j],
            decreases key.len()-i,
        {expanded[i]=key[i];i+=1;}
        proof {assert(expanded@.take(i as int)==key@);}
        let mut rcon=1u8;
        while i<total
            invariant key.len()==16 || key.len()==32,rounds==10 || rounds==14,
                total==(rounds as usize+1)*16,key.len()<=i<=total<=240,i%4==0,
                rounds==if key.len()==16 {10u8}else{14u8},
                expanded@.take(i as int)==key_schedule(key@,((i-key.len())/4) as nat).bytes,
                rcon==key_schedule(key@,((i-key.len())/4) as nat).rcon,
            decreases total-i,
        {
            let ghost before_i=i;let ghost before=expanded@;let ghost before_rcon=rcon;
            proof {schedule_length(key@,((i-key.len())/4) as nat);}
            let mut t=[expanded[i-4],expanded[i-3],expanded[i-2],expanded[i-1]];
            if i%key.len()==0 {
                t=[sbox(t[1])^rcon,sbox(t[2]),sbox(t[3]),sbox(t[0])];rcon=mul(rcon,2);
            } else if key.len()==32 && i%32==16 {
                let ghost prior=t@;let mut j=0usize;
                while j<4
                    invariant j<=4,forall|z:int| 0<=z<4 ==> t@[z]==
                        if z<j {substitute(prior[z],false)}else{prior[z]},
                    decreases 4-j,
                {t[j]=sbox(t[j]);j+=1;}
            }
            proof {
                assert(t@==schedule_word(ExpandedSchedule {bytes:before.take(before_i as int),rcon:before_rcon},key.len() as nat));
            }
            let mut j=0usize;
            while j<4
                invariant j<=4,i==before_i+j,before_i>=key.len(),
                    before_i%4==0,before_i+4<=total<=240,
                    key.len()==16 || key.len()==32,
                    forall|z:int| 0<=z<before_i ==> expanded@[z]==before[z],
                    forall|z:int| 0<=z<j ==> expanded@[before_i as int+z]
                        ==before[(before_i-key.len()) as int+z]^t@[z],
                decreases 4-j,
            {expanded[i]=expanded[i-key.len()]^t[j];i+=1;j+=1;}
            proof {
                assert(expanded@.take(i as int)==schedule_step(
                    ExpandedSchedule {bytes:before.take(before_i as int),rcon:before_rcon},key.len() as nat).bytes);
            }
        }
        Ok(Self {state:AesState {expanded,rounds,retired:false}})
    }
    pub fn encrypt_aes_block(&self,input:[u8;16]) -> (r:Result<[u8;16],Error>)
        ensures self.valid_aes(),match r {
            Ok(output) => !self.aes_retired() && output@==self.aes_encrypt_reference(input@),
            Err(_) => self.aes_retired(),
        },
    {
        proof {use_type_invariant(self);}
        if self.state.retired {return Err(Error::Retired);}
        let mut state=input;add_key(&mut state,&self.state.expanded,0);let mut round=1usize;
        while round<=self.state.rounds as usize
            invariant 1<=round<=self.state.rounds as usize+1,self.valid_aes(),!self.state.retired,
                state@==encrypted(input@,self.state.expanded@,self.state.rounds as nat,(round-1) as nat),
            decreases self.state.rounds as usize+1-round,
        {
            let ghost before=state@;
            let mut i=0usize;
            while i<16
                invariant i<=16,forall|j:int| 0<=j<16 ==> state@[j]==
                    if j<i {substitute(before[j],false)}else{before[j]},
                decreases 16-i,
            {state[i]=sbox(state[i]);i+=1;}
            shift(&mut state,false);if round<self.state.rounds as usize {mix(&mut state,false);}
            add_key(&mut state,&self.state.expanded,round);round+=1;
        }
        Ok(state)
    }
    pub fn decrypt_aes_block(&self,input:[u8;16]) -> (r:Result<[u8;16],Error>)
        ensures self.valid_aes(),match r {
            Ok(output) => !self.aes_retired() && output@==self.aes_decrypt_reference(input@),
            Err(_) => self.aes_retired(),
        },
    {
        proof {use_type_invariant(self);}
        if self.state.retired {return Err(Error::Retired);}
        let mut state=input;add_key(&mut state,&self.state.expanded,self.state.rounds as usize);
        let mut round=self.state.rounds as usize;
        while round>0
            invariant round<=self.state.rounds as usize,self.valid_aes(),!self.state.retired,
                state@==decrypted(input@,self.state.expanded@,self.state.rounds as nat,(self.state.rounds as usize-round) as nat),
            decreases round,
        {
            round-=1;shift(&mut state,true);let ghost before=state@;let mut i=0usize;
            while i<16
                invariant i<=16,forall|j:int| 0<=j<16 ==> state@[j]==
                    if j<i {substitute(before[j],true)}else{before[j]},
                decreases 16-i,
            {state[i]=inv_sbox(state[i]);i+=1;}
            add_key(&mut state,&self.state.expanded,round);if round>0 {mix(&mut state,true);}
        }
        Ok(state)
    }
    pub fn retire_aes(&mut self)
        ensures final(self).valid_aes(),final(self).aes_retired(),final(self).aes_round_count()==0,
            forall|i:int| 0<=i<240 ==> final(self).aes_schedule()[i]==0,
        opens_invariants none
        no_unwind
    {
        self.state=AesState {expanded:[
            0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,
            0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,
            0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,
            0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,
            0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,
            0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,
            0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,
            0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,
            0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,
            0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,
            0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,
            0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,
            0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,
            0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,
            0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,
        ],rounds:0,retired:true};
    }
}
impl Drop for AesKey {
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {self.retire_aes();}
}

}
