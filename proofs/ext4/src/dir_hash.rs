// SPDX-License-Identifier: MPL-2.0

//! Linux ext4's six unkeyed filename hash variants. The mathematical word
//! model is independent of native overflow. Hashes select candidate buckets;
//! equality of full names remains mandatory and no collision resistance is
//! assumed. Keyed/encrypted and normalized casefold hashing are separate.

use vstd::prelude::*;

verus! {

#[derive(Clone, Copy)]
pub struct State { pub a: u32, pub b: u32, pub c: u32, pub d: u32 }
#[derive(Clone, Copy)]
pub struct Words { pub a: u32, pub b: u32, pub c: u32, pub d: u32, pub e: u32, pub f: u32, pub g: u32, pub h: u32 }
#[derive(Clone, Copy)]
pub struct Hash { pub major: u32, pub minor: u32 }

pub open spec fn add(a: u32, b: u32) -> u32 { ((a as nat + b as nat) % 4294967296) as u32 }
pub open spec fn byte_word(b: u8, signed: bool) -> u32 { if signed && b >= 128 { (b as nat + 4294967040) as u32 } else { b as u32 } }
pub open spec fn pad(length: nat) -> u32 { let n = length as u32; let p = n | (n << 8); p | (p << 16) }
pub open spec fn packed(raw: Seq<u8>, start: nat, signed: bool, n: nat) -> u32 decreases n {
    if n == 0 { pad(raw.len()) } else {
        let old = packed(raw, start, signed, (n - 1) as nat);
        if start + n - 1 < raw.len() { add(old << 8, byte_word(raw[(start + n - 1) as int], signed)) } else { old }
    }
}
pub open spec fn word(w: Words, i: nat) -> u32 {
    if i == 0 { w.a } else if i == 1 { w.b } else if i == 2 { w.c } else if i == 3 { w.d }
    else if i == 4 { w.e } else if i == 5 { w.f } else if i == 6 { w.g } else { w.h }
}
pub open spec fn block(raw: Seq<u8>, signed: bool) -> Words {
    Words { a: packed(raw, 0, signed, 4), b: packed(raw, 4, signed, 4), c: packed(raw, 8, signed, 4), d: packed(raw, 12, signed, 4),
        e: packed(raw, 16, signed, 4), f: packed(raw, 20, signed, 4), g: packed(raw, 24, signed, 4), h: packed(raw, 28, signed, 4) }
}
fn add_word(a: u32, b: u32) -> (r: u32) ensures r == add(a, b) { ((a as u64 + b as u64) % 4294967296) as u32 }
fn lifted(b: u8, signed: bool) -> (r: u32) ensures r == byte_word(b, signed) {
    if signed && b >= 128 { b as u32 + 4294967040u32 } else { b as u32 }
}
fn pack(raw: &[u8], start: usize, signed: bool) -> (r: u32)
    requires raw.len() <= 255, start <= 28,
    ensures r == packed(raw@, start as nat, signed, 4),
{
    let len = raw.len() as u32;
    let p = len | (len << 8);
    let mut value = p | (p << 16);
    let mut i = 0usize;
    while i < 4
        invariant i <= 4, raw.len() <= 255, start <= 28, value == packed(raw@, start as nat, signed, i as nat),
        decreases 4 - i,
    {
        if start + i < raw.len() { value = add_word(value << 8, lifted(raw[start + i], signed)); }
        i += 1;
    }
    value
}
fn words(raw: &[u8], signed: bool) -> (r: Words)
    requires raw.len() <= 255,
    ensures r == block(raw@, signed),
{
    Words { a: pack(raw, 0, signed), b: pack(raw, 4, signed), c: pack(raw, 8, signed), d: pack(raw, 12, signed),
        e: pack(raw, 16, signed), f: pack(raw, 20, signed), g: pack(raw, 24, signed), h: pack(raw, 28, signed) }
}
fn get(w: Words, i: usize) -> (r: u32) ensures r == word(w, i as nat) {
    if i == 0 { w.a } else if i == 1 { w.b } else if i == 2 { w.c } else if i == 3 { w.d }
    else if i == 4 { w.e } else if i == 5 { w.f } else if i == 6 { w.g } else { w.h }
}

pub open spec fn initial(seed: State) -> State {
    if seed.a == 0 && seed.b == 0 && seed.c == 0 && seed.d == 0 {
        State { a: 0x67452301, b: 0xefcdab89, c: 0x98badcfe, d: 0x10325476 }
    } else { seed }
}
pub open spec fn rotate(v: u32, n: u32) -> u32 { (v << n) | (v >> (32 - n)) }
fn rotate_word(v: u32, n: u32) -> (r: u32)
    requires 0 < n < 32, ensures r == rotate(v, n),
{ (v << n) | (v >> (32 - n)) }

pub open spec fn md_index(i: nat) -> nat {
    let j = i % 8;
    if i < 8 { j } else if i < 16 {
        if j < 4 { 1 + 2 * j } else { (2 * (j - 4)) as nat }
    } else {
        if j == 0 { 3 } else if j == 1 { 7 } else if j == 2 { 2 } else if j == 3 { 6 }
        else if j == 4 { 1 } else if j == 5 { 5 } else if j == 6 { 0 } else { 4 }
    }
}
pub open spec fn md_rotation(i: nat) -> u32 {
    let j = i % 4;
    if j == 0 { 3u32 } else if i < 8 {
        if j == 1 { 7u32 } else if j == 2 { 11u32 } else { 19u32 }
    } else if i < 16 {
        if j == 1 { 5u32 } else if j == 2 { 9u32 } else { 13u32 }
    } else { if j == 1 { 9u32 } else if j == 2 { 11u32 } else { 15u32 } }
}
pub open spec fn md_boolean(s: State, i: nat) -> u32 {
    if i < 8 { s.d ^ (s.b & (s.c ^ s.d)) }
    else if i < 16 { (s.b & s.c) | ((s.b ^ s.c) & s.d) }
    else { s.b ^ s.c ^ s.d }
}
pub open spec fn md_constant(i: nat) -> u32 { if i < 8 { 0u32 } else if i < 16 { 0x5a827999u32 } else { 0x6ed9eba1u32 } }
pub open spec fn md_step(s: State, w: Words, i: nat) -> State {
    let v = rotate(add(add(s.a, md_boolean(s, i)), add(word(w, md_index(i)), md_constant(i))), md_rotation(i));
    State { a: s.d, b: v, c: s.b, d: s.c }
}
pub open spec fn md_rounds(seed: State, w: Words, n: nat) -> State decreases n {
    if n == 0 { seed } else { md_step(md_rounds(seed, w, (n - 1) as nat), w, (n - 1) as nat) }
}
pub open spec fn md_transform(seed: State, w: Words) -> State {
    let out = md_rounds(seed, w, 24);
    State { a: add(seed.a, out.a), b: add(seed.b, out.b), c: add(seed.c, out.c), d: add(seed.d, out.d) }
}
fn half_md4(seed: State, w: Words) -> (r: State) ensures r == md_transform(seed, w) {
    let mut state = seed;
    let mut i = 0usize;
    while i < 24
        invariant i <= 24, state == md_rounds(seed, w, i as nat),
        decreases 24 - i,
    {
        let j = i % 8;
        let slot = if i < 8 { j } else if i < 16 { if j < 4 { 1 + 2 * j } else { 2 * (j - 4) } }
            else { if j == 0 { 3usize } else if j == 1 { 7 } else if j == 2 { 2 } else if j == 3 { 6 }
                else if j == 4 { 1 } else if j == 5 { 5 } else if j == 6 { 0 } else { 4 } };
        let j = i % 4;
        let shift = if j == 0 { 3u32 } else if i < 8 { if j == 1 { 7u32 } else if j == 2 { 11u32 } else { 19u32 } }
            else if i < 16 { if j == 1 { 5u32 } else if j == 2 { 9u32 } else { 13u32 } }
            else { if j == 1 { 9u32 } else if j == 2 { 11u32 } else { 15u32 } };
        let boolean = if i < 8 { state.d ^ (state.b & (state.c ^ state.d)) }
            else if i < 16 { (state.b & state.c) | ((state.b ^ state.c) & state.d) } else { state.b ^ state.c ^ state.d };
        let constant = if i < 8 { 0u32 } else if i < 16 { 0x5a827999u32 } else { 0x6ed9eba1u32 };
        let value = rotate_word(add_word(add_word(state.a, boolean), add_word(get(w, slot), constant)), shift);
        state = State { a: state.d, b: value, c: state.b, d: state.c };
        i += 1;
    }
    State { a: add_word(seed.a, state.a), b: add_word(seed.b, state.b), c: add_word(seed.c, state.c), d: add_word(seed.d, state.d) }
}

pub open spec fn tea_step(s: State, w: Words) -> State {
    let sum = add(s.c, 0x9e3779b9);
    let left = add(s.a, add(s.b << 4, w.a) ^ add(s.b, sum) ^ add(s.b >> 5, w.b));
    let right = add(s.b, add(left << 4, w.c) ^ add(left, sum) ^ add(left >> 5, w.d));
    State { a: left, b: right, c: sum, d: 0 }
}
pub open spec fn tea_rounds(seed: State, w: Words, n: nat) -> State decreases n {
    if n == 0 { State { a: seed.a, b: seed.b, c: 0, d: 0 } } else { tea_step(tea_rounds(seed, w, (n - 1) as nat), w) }
}
pub open spec fn tea_transform(seed: State, w: Words) -> State {
    let out = tea_rounds(seed, w, 16);
    State { a: add(seed.a, out.a), b: add(seed.b, out.b), c: seed.c, d: seed.d }
}
fn tea(seed: State, w: Words) -> (r: State) ensures r == tea_transform(seed, w) {
    let mut state = State { a: seed.a, b: seed.b, c: 0, d: 0 };
    let mut i = 0usize;
    while i < 16
        invariant i <= 16, state == tea_rounds(seed, w, i as nat),
        decreases 16 - i,
    {
        let sum = add_word(state.c, 0x9e3779b9);
        let left = add_word(state.a, add_word(state.b << 4, w.a) ^ add_word(state.b, sum) ^ add_word(state.b >> 5, w.b));
        let right = add_word(state.b, add_word(left << 4, w.c) ^ add_word(left, sum) ^ add_word(left >> 5, w.d));
        state = State { a: left, b: right, c: sum, d: 0 };
        i += 1;
    }
    State { a: add_word(seed.a, state.a), b: add_word(seed.b, state.b), c: seed.c, d: seed.d }
}

pub open spec fn legacy_step(s: State, b: u8, signed: bool) -> State {
    let product = ((byte_word(b, signed) as nat * 7152373) % 4294967296) as u32;
    let mix = add(s.b, s.a ^ product);
    let value = if mix & 0x80000000u32 != 0 { ((mix as nat + 4294967296 - 0x7fffffff) % 4294967296) as u32 } else { mix };
    State { a: value, b: s.a, c: 0, d: 0 }
}
pub open spec fn legacy(raw: Seq<u8>, signed: bool) -> State decreases raw.len() {
    if raw.len() == 0 { State { a: 0x12a3fe2d, b: 0x37abe8f9, c: 0, d: 0 } }
    else { legacy_step(legacy(raw.drop_last(), signed), raw.last(), signed) }
}
fn legacy_hash(raw: &[u8], signed: bool) -> (r: u32) ensures r == legacy(raw@, signed).a << 1 {
    let mut state = State { a: 0x12a3fe2d, b: 0x37abe8f9, c: 0, d: 0 };
    let mut i = 0usize;
    assert(raw@.take(0) =~= Seq::<u8>::empty());
    while i < raw.len()
        invariant i <= raw.len(), state == legacy(raw@.take(i as int), signed),
        decreases raw.len() - i,
    {
        let b = lifted(raw[i], signed);
        let product = ((b as u64 * 7152373u64) % 4294967296) as u32;
        let mix = add_word(state.b, state.a ^ product);
        let value = if mix & 0x80000000u32 != 0 { ((mix as u64 + 4294967296 - 0x7fffffff) % 4294967296) as u32 } else { mix };
        assert(raw@.take(i as int + 1).drop_last() =~= raw@.take(i as int));
        assert(raw@.take(i as int + 1).last() == raw@[i as int]);
        state = State { a: value, b: state.a, c: 0, d: 0 };
        i += 1;
    }
    assert(raw@.take(i as int) =~= raw@);
    state.a << 1
}

pub open spec fn stride(version: u8) -> nat { if version == 1 || version == 4 { 32nat } else { 16nat } }
pub open spec fn rounds(raw: Seq<u8>, seed: State, version: u8, n: nat) -> State decreases n {
    if n == 0 { initial(seed) } else {
        let start = (n - 1) * stride(version);
        let input = block(raw.subrange(start as int, raw.len() as int), version < 3);
        let old = rounds(raw, seed, version, (n - 1) as nat);
        if version == 1 || version == 4 { md_transform(old, input) } else { tea_transform(old, input) }
    }
}
pub open spec fn normalized(hash: u32) -> u32 { let value = hash & !1u32; if value == 0xfffffffeu32 { 0xfffffffcu32 } else { value } }
pub open spec fn value(raw: Seq<u8>, seed: State, version: u8) -> Hash {
    if version == 0 || version == 3 { Hash { major: normalized(legacy(raw, version == 0).a << 1), minor: 0 } }
    else {
        let n = (raw.len() + stride(version) - 1) / (stride(version) as int);
        let result = rounds(raw, seed, version, n as nat);
        Hash { major: normalized(if version == 1 || version == 4 { result.b } else { result.a }),
            minor: if version == 1 || version == 4 { result.c } else { result.b } }
    }
}

pub fn calculate(raw: &[u8], seed: State, version: u8) -> (r: Option<Hash>)
    ensures match r { Some(hash) => raw.len() <= 255 && version <= 5 && hash == value(raw@, seed, version)
        && hash.major & 1u32 == 0 && hash.major < 0xfffffffeu32, None => raw.len() > 255 || version > 5 },
{
    if raw.len() > 255 || version > 5 { return None; }
    let hash;
    let minor;
    if version == 0 || version == 3 { hash = legacy_hash(raw, version == 0); minor = 0u32; }
    else {
        let mut state = if seed.a == 0 && seed.b == 0 && seed.c == 0 && seed.d == 0 {
            State { a: 0x67452301, b: 0xefcdab89, c: 0x98badcfe, d: 0x10325476 }
        } else { seed };
        let size = if version == 1 || version == 4 { 32usize } else { 16usize };
        let count = (raw.len() + size - 1) / size;
        let mut i = 0usize;
        while i < count
            invariant raw.len() <= 255, 1 <= version <= 5, version != 3,
                size == stride(version), size == 16 || size == 32,
                count as int == (raw.len() as int + size as int - 1) / (size as int), i <= count <= 16,
                state == rounds(raw@, seed, version, i as nat),
            decreases count - i,
        {
            assert(i * size < raw.len()) by (nonlinear_arith)
                requires i < count, count as int == (raw.len() as int + size as int - 1) / (size as int), size == 16 || size == 32, raw.len() <= 255;
            let input = words(&raw[i * size..], version < 3);
            state = if version == 1 || version == 4 { half_md4(state, input) } else { tea(state, input) };
            i += 1;
        }
        hash = if version == 1 || version == 4 { state.b } else { state.a };
        minor = if version == 1 || version == 4 { state.c } else { state.b };
    }
    let even = hash & !1u32;
    let major = if even == 0xfffffffeu32 { 0xfffffffcu32 } else { even };
    assert(major & 1u32 == 0 && major < 0xfffffffeu32) by (bit_vector)
        requires even == hash & !1u32, major == if even == 0xfffffffeu32 { 0xfffffffcu32 } else { even };
    Some(Hash { major, minor })
}

pub proof fn every_unkeyed_hash_reserves_the_collision_bit_and_eof_value(raw: Seq<u8>, seed: State, version: u8)
    requires raw.len() <= 255, version <= 5,
    ensures value(raw, seed, version).major & 1u32 == 0, value(raw, seed, version).major != 0xfffffffeu32,
{
    let h = if version == 0 || version == 3 { legacy(raw, version == 0).a << 1 } else {
        let s = rounds(raw, seed, version, ((raw.len() + stride(version) - 1) / (stride(version) as int)) as nat);
        if version == 1 || version == 4 { s.b } else { s.a }
    };
    assert(normalized(h) & 1u32 == 0 && normalized(h) != 0xfffffffeu32) by (bit_vector);
}

}
