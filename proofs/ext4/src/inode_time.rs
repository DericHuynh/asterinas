// SPDX-License-Identifier: MPL-2.0

//! Linux ext4 signed base seconds and two-bit epoch/nanosecond words.
//! Raw decoding preserves all on-disk nanosecond bits. Canonical encoding
//! validates nanoseconds and the finite 1901 through 2446 representable range.

use vstd::prelude::*;

verus! {

pub const MIN_SECONDS: i64 = -2147483648;
pub const MAX_SECONDS: i64 = 15032385535;

pub struct Timestamp { pub seconds: i64, pub nanoseconds: u32 }
pub struct Words { pub base: u32, pub extra: u32 }

pub open spec fn signed_base(base: u32) -> int {
    if base < 2147483648 { base as int } else { base as int - 4294967296 }
}

pub open spec fn seconds_value(base: u32, extra: u32, extended: bool) -> int {
    signed_base(base) + if extended { (extra as int % 4) * 4294967296 } else { 0 }
}

pub open spec fn nanos_value(extra: u32, extended: bool) -> nat {
    if extended { extra as nat / 4 } else { 0 }
}

pub open spec fn representable(seconds: int, nanoseconds: nat) -> bool {
    MIN_SECONDS <= seconds <= MAX_SECONDS && nanoseconds < 1000000000
}

pub open spec fn base_word(seconds: int) -> int {
    let remainder = (seconds + 2147483648) % 4294967296;
    if remainder >= 2147483648 { remainder - 2147483648 } else { remainder + 2147483648 }
}

pub open spec fn extra_word(seconds: int, nanoseconds: nat) -> int {
    nanoseconds as int * 4 + (seconds + 2147483648) / 4294967296
}

pub open spec fn legacy_value(seconds: int) -> int {
    if seconds < MIN_SECONDS { MIN_SECONDS as int } else if seconds > 2147483647 { 2147483647int } else { seconds }
}

pub open spec fn legacy_word(seconds: int) -> int {
    let clamped = legacy_value(seconds);
    if clamped >= 0 { clamped } else { clamped + 4294967296 }
}

pub fn decode_words(base: u32, extra: u32, extended: bool) -> (r: Timestamp)
    ensures r.seconds as int == seconds_value(base, extra, extended), r.nanoseconds as nat == nanos_value(extra, extended),
        MIN_SECONDS <= r.seconds <= MAX_SECONDS, r.nanoseconds < 1073741824,
        !extended ==> MIN_SECONDS <= r.seconds <= 2147483647 && r.nanoseconds == 0,
{
    let seconds = if base < 2147483648 { base as i64 } else { base as i64 - 4294967296i64 };
    let epoch = if extended { extra % 4 } else { 0 };
    Timestamp { seconds: seconds + epoch as i64 * 4294967296i64, nanoseconds: if extended { extra / 4 } else { 0 } }
}

pub proof fn extended_fields_reconstruct_the_original_seconds_and_nanoseconds(seconds: int, nanoseconds: nat)
    requires representable(seconds, nanoseconds),
    ensures 0 <= base_word(seconds) <= 4294967295, 0 <= extra_word(seconds, nanoseconds) <= 4294967295,
        seconds_value(base_word(seconds) as u32, extra_word(seconds, nanoseconds) as u32, true) == seconds,
        nanos_value(extra_word(seconds, nanoseconds) as u32, true) == nanoseconds,
{
    let shifted = seconds + 2147483648;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(shifted, 4294967296);
    let epoch = shifted / 4294967296;
    let remainder = shifted % 4294967296;
    assert(0 <= epoch <= 3);
    assert(signed_base(base_word(seconds) as u32) == remainder - 2147483648);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(extra_word(seconds, nanoseconds), 4, nanoseconds as int, epoch);
}

pub fn encode_extended(seconds: i64, nanoseconds: u32) -> (r: Option<Words>)
    ensures match r {
        Some(words) => representable(seconds as int, nanoseconds as nat)
            && words.base as int == base_word(seconds as int) && words.extra as int == extra_word(seconds as int, nanoseconds as nat)
            && seconds_value(words.base, words.extra, true) == seconds && nanos_value(words.extra, true) == nanoseconds,
        None => !representable(seconds as int, nanoseconds as nat),
    },
{
    if seconds < MIN_SECONDS || seconds > MAX_SECONDS || nanoseconds >= 1000000000 { return None; }
    let shifted = seconds + 2147483648i64;
    let epoch = (shifted / 4294967296i64) as u32;
    let remainder = (shifted % 4294967296i64) as u32;
    let base = if remainder >= 2147483648 { remainder - 2147483648 } else { remainder + 2147483648 };
    let extra = nanoseconds * 4 + epoch;
    proof { extended_fields_reconstruct_the_original_seconds_and_nanoseconds(seconds as int, nanoseconds as nat); }
    Some(Words { base, extra })
}

pub fn encode_legacy(seconds: i64) -> (r: u32)
    ensures signed_base(r) == legacy_value(seconds as int), r as int == legacy_word(seconds as int),
{
    let clamped = if seconds < MIN_SECONDS { MIN_SECONDS } else if seconds > 2147483647 { 2147483647i64 } else { seconds };
    if clamped >= 0 { clamped as u32 } else { (clamped + 4294967296i64) as u32 }
}

pub proof fn canonical_extended_words_have_a_unique_encoding(base: u32, extra: u32)
    requires nanos_value(extra, true) < 1000000000,
    ensures representable(seconds_value(base, extra, true), nanos_value(extra, true)),
        base_word(seconds_value(base, extra, true)) == base,
        extra_word(seconds_value(base, extra, true), nanos_value(extra, true)) == extra,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(extra as int, 4);
    let signed = signed_base(base);
    let epoch = extra as int % 4;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(seconds_value(base, extra, true) + 2147483648,
        4294967296, epoch, signed + 2147483648);
}

pub proof fn negative_legacy_seconds_are_not_misread_as_a_future_epoch(base: u32)
    requires base >= 2147483648,
    ensures seconds_value(base, 0, true) == base as int - 4294967296,
        seconds_value(base, 3, true) == seconds_value(base, 0, true) + 12884901888,
        seconds_value(base, 0, false) == seconds_value(base, 0, true),
{
}

}
