// SPDX-License-Identifier: MPL-2.0

//! Linux DAC permission core without ACLs or LSM policy. The VFS must bind the
//! supplied filesystem UID, mapped group membership and capabilities to the current credentials.
//! Passing raw numbers here is not itself evidence of caller authentication.

use vstd::prelude::*;

verus! {

pub struct Credentials {
    pub fsuid: u32,
    pub in_inode_group: bool,
    pub dac_override: bool,
    pub dac_read_search: bool,
}

pub open spec fn selected(mode: u16, owner: u32, c: &Credentials) -> u8 {
    if c.fsuid == owner { ((mode >> 6) & 7) as u8 }
    else if c.in_inode_group { ((mode >> 3) & 7) as u8 }
    else { (mode & 7) as u8 }
}

pub open spec fn permitted(mode: u16, owner: u32, c: &Credentials, request: u8, directory: bool) -> bool {
    &&& request <= 7
    &&& ((selected(mode, owner, c) & request) == request
        || (c.dac_override && (directory || request & 1 == 0 || mode & 0o111 != 0))
        || (c.dac_read_search && (if directory { request & 2 == 0 } else { request == 4 })))
}

pub fn allowed(mode: u16, owner: u32, c: &Credentials, request: u8, directory: bool) -> (r: bool)
    ensures r == permitted(mode, owner, c, request, directory),
{
    if request > 7 { return false; }
    let bits = if c.fsuid == owner { ((mode >> 6) & 7) as u8 }
        else if c.in_inode_group { ((mode >> 3) & 7) as u8 }
        else { (mode & 7) as u8 };
    if bits & request == request { return true; }
    if c.dac_override && (directory || request & 1 == 0 || mode & 0o111 != 0) { return true; }
    c.dac_read_search && (if directory { request & 2 == 0 } else { request == 4 })
}

pub proof fn unprivileged_requests_need_every_requested_bit(mode: u16, owner: u32, c: &Credentials, req: u8, dir: bool)
    requires !c.dac_override, !c.dac_read_search, permitted(mode, owner, c, req, dir),
    ensures selected(mode, owner, c) & req == req,
{
}

pub proof fn override_cannot_execute_a_nonexecutable_regular_file(mode: u16, owner: u32, c: &Credentials)
    requires mode & 0o111 == 0,
    ensures !permitted(mode, owner, c, 1, false),
{
    assert((((mode >> 6) & 7) as u8) & 1 == 0
        && (((mode >> 3) & 7) as u8) & 1 == 0 && ((mode & 7) as u8) & 1 == 0)
        by (bit_vector) requires mode & 0o111 == 0;
    assert(selected(mode, owner, c) & 1 == 0);
    assert(1u8 & 1u8 == 1u8) by (bit_vector);
    assert(!permitted(mode, owner, c, 1, false)) by {
        if permitted(mode, owner, c, 1, false) {
            assert(selected(mode, owner, c) & 1 == 1);
        }
    }
}

pub proof fn owner_permissions_take_precedence_over_group_permissions(mode: u16, owner: u32, c: &Credentials)
    requires c.fsuid == owner,
    ensures selected(mode, owner, c) == ((mode >> 6) & 7) as u8,
{
}

}
