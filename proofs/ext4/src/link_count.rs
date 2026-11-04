// SPDX-License-Identifier: MPL-2.0

//! Linux DIR_NLINK: directory i_links_count=1 means unknown, never one actual
//! reference. Exact namespace topology remains checked independently.

use vstd::prelude::*;

verus! {

pub open spec fn matches(mode: u16, stored: u16, references: nat, dir_nlink: bool) -> bool {
    if mode & 0xf000u16 == 0x4000u16 && dir_nlink && stored == 1 { references >= 2 }
    else { references == stored as nat }
}

pub fn agrees(mode: u16, stored: u16, references: u32, dir_nlink: bool) -> (r: bool)
    ensures r == matches(mode, stored, references as nat, dir_nlink),
{
    if mode & 0xf000u16 == 0x4000u16 && dir_nlink && stored == 1 { references >= 2 }
    else { references == stored as u32 }
}

pub fn increment_directory(stored: u16, indexed: bool) -> (r: Option<u16>)
    ensures match r { Some(next) => if indexed { next == if stored == 1 || stored >= 65000 { 1u16 } else { (stored + 1) as u16 } }
        else { stored < 65000 && next as nat == stored as nat + 1 },
        None => !indexed && stored >= 65000 },
{
    if indexed && (stored == 1 || stored >= 65000) { Some(1) }
    else if stored >= 65000 { None }
    else { Some(stored + 1) }
}

pub fn decrement_directory(stored: u16) -> (r: u16)
    ensures r == if stored > 2 { (stored - 1) as u16 } else { stored },
{
    if stored > 2 { stored - 1 } else { stored }
}

pub proof fn unknown_directory_counts_cannot_weaken_regular_file_reference_checks(mode: u16, stored: u16, refs: nat, feature: bool)
    requires mode & 0xf000u16 != 0x4000u16,
    ensures matches(mode, stored, refs, feature) == (refs == stored as nat),
{ }

pub proof fn unknown_counts_still_require_a_live_directory_with_multiple_references(mode: u16, refs: nat)
    requires mode & 0xf000u16 == 0x4000u16, matches(mode, 1, refs, true),
    ensures refs >= 2,
{ }

}
