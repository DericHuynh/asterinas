// SPDX-License-Identifier: MPL-2.0

//! Ext4 block geometry, independent of CortenMM frame size and failure atomicity.

use vstd::prelude::*;

verus! {

pub open spec fn accepted(bytes: nat) -> bool {
    bytes == 1024 || bytes == 2048 || bytes == 4096 || bytes == 8192 || bytes == 16384 || bytes == 32768 || bytes == 65536
}

pub fn valid(bytes: usize) -> (r: bool) ensures r == accepted(bytes as nat) {
    bytes == 1024 || bytes == 2048 || bytes == 4096 || bytes == 8192 || bytes == 16384 || bytes == 32768 || bytes == 65536
}

}
