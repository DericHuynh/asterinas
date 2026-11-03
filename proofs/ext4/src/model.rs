// SPDX-License-Identifier: MPL-2.0

//! Draft Verus model entry point. See ../proof-status.json.
//! These models have NOT been run through Verus in this revision.

use vstd::prelude::*;

mod redo;
mod journal;
mod lease;

verus! {
fn main() {}
}
