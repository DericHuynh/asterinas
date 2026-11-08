// SPDX-License-Identifier: MPL-2.0

//! Fixed Unicode12.1 Linux NFDICF filename keys.
//! Source names retain their on-disk bytes. Keys are private comparison values,
//! not inode, credential, encryption-key or directory-publication authority.
//! Default-ignorable input characters disappear but remain CCC-zero barriers
//! while ordering neighboring combining characters, matching the Linux cursor.

use vstd::prelude::*;
use crate::{bytes, unicode12_data as data};

verus! {

pub const MAX_NAME_BYTES: usize = 255;
pub const MAX_KEY_BYTES: usize = 4096;
pub const MAX_TOKENS: usize = 4096;
pub const BARRIER: u32 = 0x110000;

#[derive(Clone, Copy)]
pub enum Error { InvalidName, InvalidUtf8, Budget, InvalidTables }


/// The mathematical model is tied to the vendored Unicode12.1 constants,
/// not to a host Unicode database. BARRIER is deliberately not a scalar:
/// it models Linux's deleted, class-zero ordering boundary.
pub open spec fn scalar_valid(c: u32) -> bool {
    c <= 0x10ffff && !(0xd800 <= c <= 0xdfff)
}
pub open spec fn token_valid(c: u32) -> bool { scalar_valid(c) || c == BARRIER }
pub open spec fn name_valid(raw: Seq<u8>) -> bool {
    0 < raw.len() <= MAX_NAME_BYTES
        && forall|i: int| 0 <= i < raw.len() ==> raw[i] != 0 && raw[i] != 47
}
#[verifier::opaque]
pub closed spec fn class_search(c: u32, low: int, high: int) -> u8
    decreases high - low,
{
    if 0 <= low < high <= data::proof_ccc_ranges_view().len() {
        let mid = low + (high - low) / 2;
        let range = data::proof_ccc_ranges_view()[mid];
        if c < range.0 { class_search(c, low, mid) }
        else if c > range.1 { class_search(c, mid + 1, high) }
        else { range.2 }
    } else { 0 }
}
#[verifier::opaque]
pub closed spec fn class_model(c: u32) -> u8 {
    class_search(c, 0, data::proof_ccc_ranges_view().len() as int)
}
#[verifier::opaque]
pub closed spec fn ignored_search(c: u32, low: int, high: int) -> bool
    decreases high - low,
{
    if 0 <= low < high <= data::proof_ignorable_ranges_view().len() {
        let mid = low + (high - low) / 2;
        let range = data::proof_ignorable_ranges_view()[mid];
        if c < range.0 { ignored_search(c, low, mid) }
        else if c > range.1 { ignored_search(c, mid + 1, high) }
        else { true }
    } else { false }
}
#[verifier::opaque]
pub closed spec fn ignored_model(c: u32) -> bool {
    ignored_search(c, 0, data::proof_ignorable_ranges_view().len() as int)
}
#[verifier::opaque]
pub closed spec fn map_search(c: u32, low: int, high: int) -> int
    decreases high - low,
{
    if 0 <= low < high <= data::proof_fold_keys_view().len() {
        let mid = low + (high - low) / 2;
        if data::proof_fold_keys_view()[mid] < c { map_search(c, mid + 1, high) }
        else { map_search(c, low, mid) }
    } else { low }
}
#[verifier::opaque]
pub closed spec fn map_index(c: u32) -> Option<int> {
    let i = map_search(c, 0, data::proof_fold_keys_view().len() as int);
    if 0 <= i < data::proof_fold_keys_view().len() && data::proof_fold_keys_view()[i] == c { Some(i) } else { None }
}
#[verifier::opaque]
pub closed spec fn scalar_mapping(c: u32) -> Option<Seq<u32>> {
    if ignored_model(c) { Some(seq![BARRIER]) }
    else if 0xac00 <= c <= 0xd7a3 {
        let x = c as int - 0xac00;
        let head = seq![(0x1100 + x / 588) as u32, (0x1161 + (x % 588) / 28) as u32];
        Some(if x % 28 == 0 { head } else { head.push((0x11a7 + x % 28) as u32) })
    } else if let Some(i) = map_index(c) {
        if i < 0 || i + 1 >= data::proof_fold_offsets_view().len() { None }
        else {
            let first = data::proof_fold_offsets_view()[i] as int;
            let last = data::proof_fold_offsets_view()[i + 1] as int;
            if first > last || last > data::proof_fold_values_view().len() { None }
            else if first == last { Some(seq![BARRIER]) }
            else {
                let values = data::proof_fold_values_view().subrange(first, last);
                if forall|j: int| 0 <= j < values.len() ==> scalar_valid(values[j]) {
                    Some(values)
                } else { None }
            }
        }
    } else { Some(seq![c]) }
}
pub open spec fn swap(s: Seq<u32>, i: int, j: int) -> Seq<u32> {
    s.update(i, s[j]).update(j, s[i])
}
#[verifier::opaque]
pub closed spec fn bubble(s: Seq<u32>, at: int, class: u8) -> Seq<u32>
    decreases at,
{
    if 0 < at < s.len() && class_model(s[at - 1]) != 0 && class_model(s[at - 1]) > class {
        bubble(swap(s, at - 1, at), at - 1, class)
    } else { s }
}
#[verifier::opaque]
pub closed spec fn ordered_append(s: Seq<u32>, c: u32) -> Seq<u32> {
    if class_model(c) == 0 { s.push(c) } else { bubble(s.push(c), s.len() as int, class_model(c)) }
}
#[verifier::opaque]
pub closed spec fn append_all(s: Seq<u32>, values: Seq<u32>) -> Seq<u32>
    decreases values.len(),
{
    if values.len() == 0 { s }
    else { append_all(ordered_append(s, values[0]), values.drop_first()) }
}
#[verifier::opaque]
pub closed spec fn fold_scalars(values: Seq<u32>) -> Option<Seq<u32>>
    decreases values.len(),
{
    if values.len() == 0 { Some(Seq::empty()) }
    else if let Some(prefix) = fold_scalars(values.drop_last()) {
        match scalar_mapping(values.last()) { Some(mapped) => Some(append_all(prefix, mapped)), None => None }
    } else { None }
}
pub open spec fn utf8_width(first: u8) -> nat {
    if first < 0x80 { 1 } else if 0xc2 <= first <= 0xdf { 2 }
    else if 0xe0 <= first <= 0xef { 3 } else if 0xf0 <= first <= 0xf4 { 4 } else { 0 }
}
pub open spec fn decoded_prefix(raw: Seq<u8>, at: int, count: int, width: nat) -> nat
    decreases count,
{
    if count <= 1 {
        (raw[at] & if width == 2 { 0x1fu8 } else if width == 3 { 0x0fu8 } else { 0x07u8 }) as nat
    } else {
        decoded_prefix(raw, at, count - 1, width) * 64 + (raw[at + count - 1] & 63u8) as nat
    }
}
#[verifier::opaque]
pub closed spec fn scalar_step(raw: Seq<u8>, at: int) -> Option<(u32, int)> {
    if at < 0 || at >= raw.len() { None }
    else {
        let width = utf8_width(raw[at]);
        if width == 0 || at + width > raw.len() { None }
        else if width == 1 { Some((raw[at] as u32, at + 1)) }
        else if !(forall|i: int| 1 <= i < width ==> #[trigger] raw[at + i] >= 0x80 && raw[at + i] <= 0xbf) { None }
        else {
            let value = decoded_prefix(raw, at, width as int, width);
            if (width == 2 && value < 0x80) || (width == 3 && value < 0x800)
                || (width == 4 && value < 0x10000) || value > 0x10ffff
                || (0xd800 <= value <= 0xdfff) { None }
            else { Some((value as u32, at + width)) }
        }
    }
}
#[verifier::opaque]
pub closed spec fn decoded_suffix(raw: Seq<u8>, at: int) -> Option<Seq<u32>>
    decreases raw.len() - at,
{
    if at < 0 || at > raw.len() { None }
    else if at == raw.len() { Some(Seq::empty()) }
    else if let Some((c, next)) = scalar_step(raw, at) {
        if at < next <= raw.len() {
            match decoded_suffix(raw, next) { Some(rest) => Some(seq![c] + rest), None => None }
        } else { None }
    } else { None }
}
pub open spec fn utf8_valid(raw: Seq<u8>) -> bool { decoded_suffix(raw, 0).is_some() }
pub open spec fn encoded_scalar(c: u32) -> Seq<u8> {
    if c == BARRIER { Seq::empty() }
    else if c < 0x80 { seq![c as u8] }
    else if c < 0x800 { seq![(0xc0 + c / 64) as u8, (0x80 + c % 64) as u8] }
    else if c < 0x10000 { seq![(0xe0 + c / 4096) as u8, (0x80 + (c / 64) % 64) as u8, (0x80 + c % 64) as u8] }
    else { seq![(0xf0 + c / 262144) as u8, (0x80 + (c / 4096) % 64) as u8,
        (0x80 + (c / 64) % 64) as u8, (0x80 + c % 64) as u8] }
}
#[verifier::opaque]
pub closed spec fn encoded_tokens(tokens: Seq<u32>) -> Seq<u8>
    decreases tokens.len(),
{
    if tokens.len() == 0 { Seq::empty() }
    else { encoded_tokens(tokens.drop_last()) + encoded_scalar(tokens.last()) }
}
#[verifier::opaque]
pub closed spec fn normalized_bytes(raw: Seq<u8>) -> Option<Seq<u8>> {
    match decoded_suffix(raw, 0) {
        Some(values) => match fold_scalars(values) { Some(tokens) => Some(encoded_tokens(tokens)), None => None },
        None => None,
    }
}

proof fn pinned_ccc_view()
    ensures data::proof_ccc_ranges_view() == data::CCC_RANGES@,
{ data::pinned_proof_views_are_exact(); }
proof fn pinned_ignored_view()
    ensures data::proof_ignorable_ranges_view() == data::IGNORABLE_RANGES@,
{ data::pinned_proof_views_are_exact(); }
proof fn pinned_key_view()
    ensures data::proof_fold_keys_view() == data::FOLD_KEYS@,
{ data::pinned_proof_views_are_exact(); }
proof fn pinned_mapping_views()
    ensures data::proof_fold_offsets_view() == data::FOLD_OFFSETS@,
        data::proof_fold_values_view() == data::FOLD_VALUES@,
{ data::pinned_proof_views_are_exact(); }

proof fn class_search_step(c: u32, low: int, high: int)
    requires 0 <= low <= high <= data::proof_ccc_ranges_view().len(),
    ensures class_search(c, low, high) == if low < high {
        let mid = low + (high - low) / 2;
        let range = data::proof_ccc_ranges_view()[mid];
        if c < range.0 { class_search(c, low, mid) }
        else if c > range.1 { class_search(c, mid + 1, high) } else { range.2 }
    } else { 0 },
{ reveal_with_fuel(class_search, 1); }
proof fn ignored_search_step(c: u32, low: int, high: int)
    requires 0 <= low <= high <= data::proof_ignorable_ranges_view().len(),
    ensures ignored_search(c, low, high) == if low < high {
        let mid = low + (high - low) / 2;
        let range = data::proof_ignorable_ranges_view()[mid];
        if c < range.0 { ignored_search(c, low, mid) }
        else if c > range.1 { ignored_search(c, mid + 1, high) } else { true }
    } else { false },
{ reveal_with_fuel(ignored_search, 1); }
proof fn map_search_step(c: u32, low: int, high: int)
    requires 0 <= low <= high <= data::proof_fold_keys_view().len(),
    ensures map_search(c, low, high) == if low < high {
        let mid = low + (high - low) / 2;
        if data::proof_fold_keys_view()[mid] < c { map_search(c, mid + 1, high) }
        else { map_search(c, low, mid) }
    } else { low },
{ reveal_with_fuel(map_search, 1); }
proof fn ordered_append_step(s: Seq<u32>, c: u32)
    ensures ordered_append(s, c) == if class_model(c) == 0 { s.push(c) }
        else { bubble(s.push(c), s.len() as int, class_model(c)) },
{ reveal(ordered_append); }
proof fn bubble_step(s: Seq<u32>, at: int, class: u8)
    ensures bubble(s, at, class) == if 0 < at < s.len()
        && class_model(s[at - 1]) != 0 && class_model(s[at - 1]) > class {
        bubble(swap(s, at - 1, at), at - 1, class)
    } else { s },
{ reveal_with_fuel(bubble, 1); }
proof fn append_all_step(s: Seq<u32>, values: Seq<u32>)
    ensures append_all(s, values) == if values.len() == 0 { s }
        else { append_all(ordered_append(s, values[0]), values.drop_first()) },
{ reveal_with_fuel(append_all, 1); }

pub proof fn appended_values_compose(s: Seq<u32>, left: Seq<u32>, right: Seq<u32>)
    ensures append_all(s, left + right) == append_all(append_all(s, left), right),
    decreases left.len(),
{
    append_all_step(s, left); append_all_step(s, left + right);
    if left.len() > 0 {
        appended_values_compose(ordered_append(s, left[0]), left.drop_first(), right);
        assert((left + right).drop_first() =~= left.drop_first() + right);
    } else { assert(left + right =~= right); }
}
proof fn append_all_push(s: Seq<u32>, values: Seq<u32>, c: u32)
    ensures append_all(s, values.push(c)) == ordered_append(append_all(s, values), c),
{
    appended_values_compose(s, values, seq![c]);
    assert(values.push(c) =~= values + seq![c]);
    assert(seq![c].drop_first() =~= Seq::<u32>::empty());
    append_all_step(append_all(s, values), seq![c]);
    append_all_step(ordered_append(append_all(s, values), c), Seq::empty());
}
proof fn append_all_empty(s: Seq<u32>)
    ensures append_all(s, Seq::<u32>::empty()) == s,
{
    append_all_step(s, Seq::<u32>::empty());
}
proof fn append_all_single(s: Seq<u32>, c: u32)
    ensures append_all(s, seq![c]) == ordered_append(s, c),
{
    assert(seq![c].drop_first() =~= Seq::<u32>::empty());
    append_all_step(s, seq![c]);
    append_all_step(ordered_append(s, c), Seq::empty());
}
proof fn append_all_pair(s: Seq<u32>, a: u32, b: u32)
    ensures append_all(s, seq![a, b]) == ordered_append(ordered_append(s, a), b),
{
    appended_values_compose(s, seq![a], seq![b]);
    append_all_single(s, a); append_all_single(ordered_append(s, a), b);
    assert(seq![a, b] =~= seq![a] + seq![b]);
}
proof fn append_all_three(s: Seq<u32>, a: u32, b: u32, c: u32)
    ensures append_all(s, seq![a, b, c]) == ordered_append(ordered_append(ordered_append(s, a), b), c),
{
    appended_values_compose(s, seq![a, b], seq![c]);
    append_all_pair(s, a, b); append_all_single(ordered_append(ordered_append(s, a), b), c);
    assert(seq![a, b, c] =~= seq![a, b] + seq![c]);
}
proof fn fold_scalars_empty()
    ensures fold_scalars(Seq::empty()) == Some(Seq::empty()),
{ reveal_with_fuel(fold_scalars, 1); }
proof fn fold_scalars_push(values: Seq<u32>, c: u32)
    ensures fold_scalars(values.push(c)) == match fold_scalars(values) {
        Some(prefix) => match scalar_mapping(c) { Some(mapped) => Some(append_all(prefix, mapped)), None => None },
        None => None,
    },
{
    reveal_with_fuel(fold_scalars, 1);
    assert(values.push(c).drop_last() =~= values);
}
proof fn decoded_suffix_step(raw: Seq<u8>, at: int)
    requires 0 <= at <= raw.len(),
    ensures decoded_suffix(raw, at) == if at == raw.len() { Some(Seq::empty()) }
        else if let Some((c, next)) = scalar_step(raw, at) {
            if at < next <= raw.len() {
                match decoded_suffix(raw, next) { Some(rest) => Some(seq![c] + rest), None => None }
            } else { None }
        } else { None },
{ reveal_with_fuel(decoded_suffix, 1); }
pub proof fn decoded_prefix_suffix(raw: Seq<u8>, at: int, prefix: Seq<u32>, c: u32, next: int)
    requires 0 <= at < raw.len(), scalar_step(raw, at) == Some((c, next)), at < next <= raw.len(),
        decoded_suffix(raw, 0) == match decoded_suffix(raw, at) { Some(rest) => Some(prefix + rest), None => None },
    ensures decoded_suffix(raw, 0) == match decoded_suffix(raw, next) {
        Some(rest) => Some(prefix.push(c) + rest), None => None,
    },
{
    decoded_suffix_step(raw, at);
    if let Some(rest) = decoded_suffix(raw, next) {
        assert(prefix + (seq![c] + rest) =~= prefix.push(c) + rest);
    }
}
proof fn encoded_tokens_empty()
    ensures encoded_tokens(Seq::empty()) == Seq::<u8>::empty(),
{ reveal_with_fuel(encoded_tokens, 1); }
proof fn encoded_tokens_push(tokens: Seq<u32>, c: u32)
    ensures encoded_tokens(tokens.push(c)) == encoded_tokens(tokens) + encoded_scalar(c),
{
    reveal_with_fuel(encoded_tokens, 1);
    assert(tokens.push(c).drop_last() =~= tokens);
}

pub struct Key { bytes: Vec<u8>, opaque: bool }

impl Key {
    pub closed spec fn view(&self) -> Seq<u8> { self.bytes@ }
    pub closed spec fn opaque_view(&self) -> bool { self.opaque }
    pub open spec fn wf(&self) -> bool { self.view().len() <= MAX_KEY_BYTES }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn as_bytes(&self) -> (r: &[u8]) ensures self.wf(), r@ == self.view(),
    { proof { use_type_invariant(self); } self.bytes.as_slice() }

    pub fn is_opaque(&self) -> (r: bool) ensures self.wf(), r == self.opaque_view(),
    { proof { use_type_invariant(self); } self.opaque }

    pub fn unicode_version(&self) -> (r: u32) ensures r == 0x000c0100,
    { data::UNICODE_VERSION }

    pub fn equals(&self, other: &Key) -> (r: bool)
        ensures r == (self.opaque_view() == other.opaque_view() && self.view() == other.view()),
    {
        self.opaque == other.opaque && bytes::equal(self.bytes.as_slice(), other.bytes.as_slice())
    }
}

fn copy(raw: &[u8]) -> (r: Vec<u8>) ensures r@ == raw@ {
    let mut result = Vec::<u8>::new(); let mut i = 0usize;
    while i < raw.len() invariant i <= raw.len(), result.len() == i, result@ == raw@.subrange(0, i as int),
        decreases raw.len() - i,
    { result.push(raw[i]); i += 1; }
    result
}

proof fn invalid_continuation(raw: Seq<u8>, at: int, width: nat, bad: int)
    requires 0 <= at < raw.len(), width == utf8_width(raw[at]), width > 1,
        at+width <= raw.len(), 1 <= bad < width,
        raw[at+bad] < 0x80 || raw[at+bad] > 0xbf,
    ensures scalar_step(raw, at).is_none(),
{
    reveal(scalar_step);
    assert(!(raw[at+bad] >= 0x80 && raw[at+bad] <= 0xbf));
    assert(!(forall|i: int| 1 <= i < width ==> #[trigger] raw[at+i] >= 0x80 && raw[at+i] <= 0xbf));
}

fn next_scalar(raw: &[u8], at: usize) -> (r: Option<(u32, usize)>)
    ensures match r {
        Some((c, next)) => scalar_valid(c) && at < next <= raw.len() && next as int <= at as int + 4
            && scalar_step(raw@, at as int) == Some((c, next as int)),
        None => scalar_step(raw@, at as int).is_none(),
    },
{
    proof { reveal(scalar_step); }
    if at >= raw.len() { return None; }
    let first = raw[at];
    let width = if first < 0x80 { 1usize }
        else if first >= 0xc2 && first <= 0xdf { 2usize }
        else if first >= 0xe0 && first <= 0xef { 3usize }
        else if first >= 0xf0 && first <= 0xf4 { 4usize }
        else { return None; };
    if raw.len() - at < width { return None; }
    if width == 1 { return Some((first as u32, at + 1)); }
    let mut value = (first & if width == 2 { 0x1f } else if width == 3 { 0x0f } else { 0x07 }) as u32;
    proof {
        assert(first & 0x1fu8 <= 31u8) by (bit_vector);
        assert(first & 0x0fu8 <= 31u8) by (bit_vector);
        assert(first & 0x07u8 <= 31u8) by (bit_vector);
        assert(value <= 31);
    }
    let mut i = 1usize;
    while i < width
        invariant 1 <= i <= width <= 4, at < raw.len(), width <= raw.len() - at,
            width == utf8_width(raw@[at as int]),
            value as nat == decoded_prefix(raw@, at as int, i as int, width as nat),
            value <= if i == 1 { 31u32 } else if i == 2 { 2047u32 } else if i == 3 { 131071u32 } else { 8388607u32 },
            forall|j: int| 1 <= j < i ==> #[trigger] raw@[at as int + j] >= 0x80 && raw@[at as int + j] <= 0xbf,
        decreases width - i,
    {
        let byte = raw[at + i];
        if byte < 0x80 || byte > 0xbf {
            proof { invalid_continuation(raw@, at as int, width as nat, i as int); }
            return None;
        }
        proof { assert(byte & 63u8 <= 63u8) by (bit_vector); }
        value = value * 64 + (byte & 63) as u32;
        proof {
            if i == 1 { assert(value <= 2047); }
            else if i == 2 { assert(value <= 131071); }
            else { assert(i == 3 && value <= 8388607); }
        }
        i += 1;
    }
    if (width == 2 && value < 0x80) || (width == 3 && value < 0x800)
        || (width == 4 && value < 0x10000) || value > 0x10ffff
        || (value >= 0xd800 && value <= 0xdfff) { return None; }
    Some((value, at + width))
}

/// Unknown/new scalars have CCC zero in the fixed12.1 encoding. They remain
/// valid UTF-8; loading a newer host Unicode database would change semantics.
pub fn combining_class(scalar: u32) -> (r: u8) ensures r == class_model(scalar) {
    let ranges = &data::CCC_RANGES;
    proof { pinned_ccc_view(); reveal(class_model); }
    let mut low = 0usize; let mut high = ranges.len();
    while low < high invariant low <= high <= ranges.len(), ranges@ == data::proof_ccc_ranges_view(),
        class_model(scalar) == class_search(scalar, 0, ranges.len() as int),
        class_search(scalar, low as int, high as int) == class_model(scalar),
        decreases high - low,
    {
        proof { class_search_step(scalar, low as int, high as int); }
        let mid = low + (high - low) / 2;
        let (first, last, class) = ranges[mid];
        if scalar < first { high = mid; }
        else if scalar > last { low = mid + 1; }
        else { return class; }
    }
    proof { class_search_step(scalar, low as int, high as int); }
    0
}

fn ignorable(scalar: u32) -> (r: bool) ensures r == ignored_model(scalar) {
    let ranges = &data::IGNORABLE_RANGES;
    proof { pinned_ignored_view(); reveal(ignored_model); }
    let mut low = 0usize; let mut high = ranges.len();
    while low < high invariant low <= high <= ranges.len(), ranges@ == data::proof_ignorable_ranges_view(),
        ignored_model(scalar) == ignored_search(scalar, 0, ranges.len() as int),
        ignored_search(scalar, low as int, high as int) == ignored_model(scalar),
        decreases high - low,
    {
        proof { ignored_search_step(scalar, low as int, high as int); }
        let mid = low + (high - low) / 2;
        let (first, last) = ranges[mid];
        if scalar < first { high = mid; }
        else if scalar > last { low = mid + 1; }
        else { return true; }
    }
    proof { ignored_search_step(scalar, low as int, high as int); }
    false
}

fn mapping(scalar: u32) -> (r: Option<usize>)
    ensures match r {
        Some(i) => i < data::FOLD_KEYS@.len() && map_index(scalar) == Some(i as int),
        None => map_index(scalar).is_none(),
    },
{
    let keys = &data::FOLD_KEYS;
    proof { pinned_key_view(); }
    let mut low = 0usize; let mut high = keys.len();
    while low < high invariant low <= high <= keys.len(), keys@ == data::proof_fold_keys_view(),
        map_search(scalar, low as int, high as int) == map_search(scalar, 0, keys.len() as int),
        decreases high - low,
    {
        proof { map_search_step(scalar, low as int, high as int); }
        let mid = low + (high - low) / 2;
        if keys[mid] < scalar { low = mid + 1; } else { high = mid; }
    }
    proof { map_search_step(scalar, low as int, high as int); reveal(map_index); }
    if low < keys.len() && keys[low] == scalar { Some(low) } else { None }
}

fn append_token(tokens: &mut Vec<u32>, scalar: u32) -> (r: bool)
    requires old(tokens).len() <= MAX_TOKENS,
    ensures final(tokens).len() <= MAX_TOKENS,
        r ==> final(tokens)@ == ordered_append(old(tokens)@, scalar)
            && final(tokens).len() == old(tokens).len() + 1,
        !r ==> final(tokens)@ == old(tokens)@,
{
    let ghost before = tokens@;
    proof { ordered_append_step(before, scalar); }
    if tokens.len() >= MAX_TOKENS { return false; }
    tokens.push(scalar);
    let class = combining_class(scalar);
    if class == 0 { return true; }
    let mut at = tokens.len() - 1;
    while at > 0 invariant at < tokens.len(), tokens.len() == before.len() + 1,
        tokens.len() <= MAX_TOKENS,
        bubble(tokens@, at as int, class) == ordered_append(before, scalar),
        ensures tokens.len() == before.len()+1, tokens.len() <= MAX_TOKENS, at < tokens.len(),
            at == 0 || tokens@ == ordered_append(before, scalar),
        decreases at,
    {
        proof { bubble_step(tokens@, at as int, class); }
        let previous = combining_class(tokens[at - 1]);
        if previous == 0 || previous <= class {
            proof { assert(bubble(tokens@, at as int, class) == tokens@); }
            break;
        }
        let old = tokens[at - 1]; tokens[at - 1] = tokens[at]; tokens[at] = old;
        at -= 1;
    }
    proof {
        bubble_step(tokens@, at as int, class);
        assert(tokens@ == ordered_append(before, scalar));
    }
    true
}

fn append_mapping(tokens: &mut Vec<u32>, scalar: u32) -> (r: Result<(), Error>)
    requires old(tokens).len() <= MAX_TOKENS, scalar_valid(scalar),
    ensures final(tokens).len() <= MAX_TOKENS,
        r.is_ok() ==> scalar_mapping(scalar).is_some()
            && final(tokens)@ == append_all(old(tokens)@, scalar_mapping(scalar).unwrap()),
        match r { Err(Error::InvalidName) | Err(Error::InvalidUtf8) => false, _ => true },
{
    let ghost before = tokens@;
    proof { reveal(scalar_mapping); pinned_mapping_views(); }
    if ignorable(scalar) {
        if !append_token(tokens, BARRIER) { return Err(Error::Budget); }
        proof {
            append_all_single(before, BARRIER);
            assert(scalar_mapping(scalar) == Some(seq![BARRIER]));
        }
        return Ok(());
    } else if scalar >= 0xac00 && scalar <= 0xd7a3 {
        let x = scalar - 0xac00;
        if !append_token(tokens, 0x1100 + x / 588)
            || !append_token(tokens, 0x1161 + (x % 588) / 28) { return Err(Error::Budget); }
        if x % 28 != 0 && !append_token(tokens, 0x11a7 + x % 28) { return Err(Error::Budget); }
        proof {
            let l = (0x1100 + x as nat / 588) as u32;
            let v = (0x1161 + (x as nat % 588) / 28) as u32;
            let t = (0x11a7 + x as nat % 28) as u32;
            if x % 28 == 0 {
                append_all_pair(before, l, v);
                assert(scalar_mapping(scalar) == Some(seq![l,v]));
            } else {
                append_all_three(before, l, v, t);
                assert(scalar_mapping(scalar) == Some(seq![l,v,t]));
            }
        }
        return Ok(());
    } else if let Some(index) = mapping(scalar) {
        if index >= data::FOLD_OFFSETS.len() || data::FOLD_OFFSETS.len() - index < 2 { return Err(Error::InvalidTables); }
        let first = data::FOLD_OFFSETS[index] as usize;
        let last = data::FOLD_OFFSETS[index + 1] as usize;
        if first > last || last > data::FOLD_VALUES.len() { return Err(Error::InvalidTables); }
        if first == last {
            if !append_token(tokens, BARRIER) { return Err(Error::Budget); }
            proof {
                append_all_single(before, BARRIER);
                assert(scalar_mapping(scalar) == Some(seq![BARRIER]));
            }
            return Ok(());
        }
        proof {
            assert(data::FOLD_VALUES@.subrange(first as int, first as int) =~= Seq::<u32>::empty());
            append_all_empty(before);
        }
        let mut i = first;
        while i < last
            invariant first <= i <= last <= data::FOLD_VALUES.len(), first < last,
                scalar_valid(scalar), !ignored_model(scalar), scalar < 0xac00 || scalar > 0xd7a3,
                map_index(scalar) == Some(index as int), index as nat+1 < data::FOLD_OFFSETS@.len(),
                first == data::FOLD_OFFSETS@[index as int], last == data::FOLD_OFFSETS@[index as int+1],
                data::proof_fold_offsets_view() == data::FOLD_OFFSETS@,
                data::proof_fold_values_view() == data::FOLD_VALUES@,
                tokens.len() <= MAX_TOKENS,
                tokens@ == append_all(before, data::FOLD_VALUES@.subrange(first as int, i as int)),
                forall|j: int| first <= j < i ==> scalar_valid(data::FOLD_VALUES@[j]),
            decreases last - i,
        {
            let value = data::FOLD_VALUES[i];
            if value > 0x10ffff || (value >= 0xd800 && value <= 0xdfff) { return Err(Error::InvalidTables); }
            if !append_token(tokens, value) { return Err(Error::Budget); }
            proof {
                append_all_push(before, data::FOLD_VALUES@.subrange(first as int, i as int), value);
                assert(data::FOLD_VALUES@.subrange(first as int, i as int + 1) =~=
                    data::FOLD_VALUES@.subrange(first as int, i as int).push(value));
            }
            i += 1;
        }
        proof {
            let values = data::FOLD_VALUES@.subrange(first as int, last as int);
            assert forall|j: int| 0 <= j < values.len() implies scalar_valid(#[trigger] values[j]) by {
                assert(values[j] == data::FOLD_VALUES@[first as int+j]);
            }
            assert(scalar_mapping(scalar) == Some(values));
        }
        return Ok(());
    }
    if !append_token(tokens, scalar) { return Err(Error::Budget); }
    proof {
        append_all_single(before, scalar);
        assert(scalar_mapping(scalar) == Some(seq![scalar]));
    }
    Ok(())
}

fn append_utf8(out: &mut Vec<u8>, scalar: u32, budget: usize) -> (r: bool)
    requires old(out).len() <= budget,
    ensures final(out).len() <= budget,
        r ==> token_valid(scalar) && final(out)@ == old(out)@ + encoded_scalar(scalar),
        !r ==> final(out)@ == old(out)@,
{
    if scalar == BARRIER { return true; }
    if scalar > 0x10ffff || (scalar >= 0xd800 && scalar <= 0xdfff) { return false; }
    let width = if scalar < 0x80 { 1usize } else if scalar < 0x800 { 2usize }
        else if scalar < 0x10000 { 3usize } else { 4usize };
    if out.len() > budget || width > budget - out.len() { return false; }
    if width == 1 { out.push(scalar as u8); }
    else if width == 2 {
        out.push((0xc0 + scalar / 64) as u8);
        out.push((0x80 + scalar % 64) as u8);
    } else if width == 3 {
        out.push((0xe0 + scalar / 4096) as u8);
        out.push((0x80 + (scalar / 64) % 64) as u8);
        out.push((0x80 + scalar % 64) as u8);
    } else {
        out.push((0xf0 + scalar / 262144) as u8);
        out.push((0x80 + (scalar / 4096) % 64) as u8);
        out.push((0x80 + (scalar / 64) % 64) as u8);
        out.push((0x80 + scalar % 64) as u8);
    }
    true
}

/// Invalid UTF-8 in non-strict mode falls back to the complete original name.
/// A valid prefix is never partially casefolded when a later byte is invalid.
/// Ignorable-only names may have an empty comparison key; source names remain
/// nonempty. This is not an on-disk filename conversion or an encryption step.
pub fn filename_key(raw: &[u8], strict: bool, byte_budget: usize) -> (r: Result<Key, Error>)
    ensures match r {
        Ok(key) => key.wf() && key.view().len() <= byte_budget && name_valid(raw@)
            && if key.opaque_view() {
                !strict && !utf8_valid(raw@) && key.view() == raw@
            } else { utf8_valid(raw@) && normalized_bytes(raw@) == Some(key.view()) },
        Err(Error::InvalidName) => !name_valid(raw@),
        Err(Error::InvalidUtf8) => name_valid(raw@) && strict && !utf8_valid(raw@),
        Err(_) => true,
    },
{
    if raw.len() == 0 || raw.len() > MAX_NAME_BYTES { return Err(Error::InvalidName); }
    if byte_budget > MAX_KEY_BYTES { return Err(Error::Budget); }
    let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len(), 0 < raw.len() <= MAX_NAME_BYTES, byte_budget <= MAX_KEY_BYTES,
            forall|j: int| 0 <= j < i ==> raw@[j] != 0 && raw@[j] != 47,
        decreases raw.len() - i,
    { if raw[i] == 0 || raw[i] == 47 { return Err(Error::InvalidName); } i += 1; }
    let mut tokens = Vec::<u32>::new(); let mut at = 0usize;
    let ghost mut decoded = Seq::<u32>::empty();
    proof { fold_scalars_empty(); }
    while at < raw.len()
        invariant at <= raw.len(), name_valid(raw@), byte_budget <= MAX_KEY_BYTES,
            tokens.len() <= MAX_TOKENS, fold_scalars(decoded) == Some(tokens@),
            decoded_suffix(raw@, 0) == match decoded_suffix(raw@, at as int) {
                Some(rest) => Some(decoded + rest), None => None,
            },
        decreases raw.len() - at,
    {
        let (scalar, next) = match next_scalar(raw, at) {
            Some(v) => v,
            None => {
                proof { decoded_suffix_step(raw@, at as int); }
                if strict { return Err(Error::InvalidUtf8); }
                if raw.len() > byte_budget { return Err(Error::Budget); }
                return Ok(Key { bytes: copy(raw), opaque: true });
            },
        };
        match append_mapping(&mut tokens, scalar) { Ok(()) => {}, Err(error) => { return Err(error); } }
        proof {
            decoded_prefix_suffix(raw@, at as int, decoded, scalar, next as int);
            fold_scalars_push(decoded, scalar);
            decoded = decoded.push(scalar);
        }
        at = next;
    }
    proof {
        decoded_suffix_step(raw@, at as int);
        assert(decoded_suffix(raw@, 0) == Some(decoded));
    }
    let mut result = Vec::<u8>::new(); i = 0;
    proof {
        encoded_tokens_empty();
        assert(tokens@.subrange(0,0) =~= Seq::<u32>::empty());
    }
    while i < tokens.len()
        invariant i <= tokens.len(), result.len() <= byte_budget <= MAX_KEY_BYTES,
            name_valid(raw@), decoded_suffix(raw@, 0) == Some(decoded), fold_scalars(decoded) == Some(tokens@),
            result@ == encoded_tokens(tokens@.subrange(0, i as int)),
        decreases tokens.len() - i,
    {
        if !append_utf8(&mut result, tokens[i], byte_budget) { return Err(Error::Budget); }
        proof {
            encoded_tokens_push(tokens@.subrange(0, i as int), tokens@[i as int]);
            assert(tokens@.subrange(0, i as int + 1) =~= tokens@.subrange(0, i as int).push(tokens@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(tokens@.subrange(0,tokens.len() as int) =~= tokens@);
        assert(result@ == encoded_tokens(tokens@));
        reveal(normalized_bytes);
        assert(normalized_bytes(raw@) == Some(result@));
    }
    Ok(Key { bytes: result, opaque: false })
}

pub fn compare(left: &[u8], right: &[u8], strict: bool) -> (r: Result<bool, Error>)
    ensures match r {
        Ok(equal) => name_valid(left@) && name_valid(right@)
            && equal == if utf8_valid(left@) && utf8_valid(right@) {
                normalized_bytes(left@) == normalized_bytes(right@)
            } else { !strict && !utf8_valid(left@) && !utf8_valid(right@) && left@ == right@ },
        Err(_) => true,
    },
{
    let left = match filename_key(left, strict, MAX_KEY_BYTES) { Ok(v) => v, Err(e) => { return Err(e); } };
    let right = match filename_key(right, strict, MAX_KEY_BYTES) { Ok(v) => v, Err(e) => { return Err(e); } };
    Ok(left.equals(&right))
}

}
