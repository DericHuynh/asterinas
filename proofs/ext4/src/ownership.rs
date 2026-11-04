// SPDX-License-Identifier: MPL-2.0

//! Block-role and initialization specification. This is not yet a validator of
//! all inode extent trees, bitmaps, or namespace links on an ext4 volume.

use vstd::prelude::*;

verus! {

#[verifier::ext_equal]
pub struct Owner { pub inode: nat, pub generation: nat }
pub enum Role { Free, Reserved, Journal, Metadata, Data(Owner) }
pub struct State { pub roles: Map<nat, Role>, pub contents: Map<nat, Seq<u8>> }

pub open spec fn owns(s: State, block: nat, owner: Owner) -> bool {
    s.roles.dom().contains(block) && s.roles[block] == Role::Data(owner)
}

pub open spec fn inv(s: State) -> bool {
    &&& (forall|b: nat| #[trigger] s.contents.dom().contains(b) <==>
        s.roles.dom().contains(b) && s.roles[b] is Data)
    &&& (forall|b: nat| s.contents.dom().contains(b) ==> (#[trigger] s.contents[b]).len() == 4096)
}

pub open spec fn zeros() -> Seq<u8> { Seq::new(4096, |i: int| 0u8) }

pub open spec fn allocate(s: State, block: nat, owner: Owner) -> State {
    State { roles: s.roles.insert(block, Role::Data(owner)),
        contents: s.contents.insert(block, zeros()) }
}

pub open spec fn release(s: State, block: nat) -> State {
    State { roles: s.roles.insert(block, Role::Free), contents: s.contents.remove(block) }
}

pub open spec fn write(s: State, block: nat, bytes: Seq<u8>) -> State {
    State { contents: s.contents.insert(block, bytes), ..s }
}

pub open spec fn read_owned(s: State, block: nat, owner: Owner) -> Option<Seq<u8>> {
    if owns(s, block, owner) { Some(s.contents[block]) } else { None }
}

pub proof fn fresh_allocation_is_initialized(s: State, block: nat, owner: Owner)
    requires inv(s), s.roles.dom().contains(block), s.roles[block] == Role::Free,
    ensures inv(allocate(s, block, owner)), owns(allocate(s, block, owner), block, owner),
        read_owned(allocate(s, block, owner), block, owner) == Some(zeros()),
        allocate(s, block, owner).roles.dom() == s.roles.dom(),
{
    let t = allocate(s, block, owner);
    assert forall|b: nat| #[trigger] t.contents.dom().contains(b) <==>
        t.roles.dom().contains(b) && t.roles[b] is Data by {
        if b != block {
            assert(s.contents.dom().contains(b) <==> s.roles.dom().contains(b) && s.roles[b] is Data);
        }
    }
}

pub proof fn release_removes_read_authority(s: State, block: nat, owner: Owner)
    requires inv(s), owns(s, block, owner),
    ensures inv(release(s, block)),
        forall|who: Owner| read_owned(release(s, block), block, who) == None,
        release(s, block).roles.dom() == s.roles.dom(),
{
    let t = release(s, block);
    assert forall|b: nat| #[trigger] t.contents.dom().contains(b) <==>
        t.roles.dom().contains(b) && t.roles[b] is Data by {
        if b != block {
            assert(s.contents.dom().contains(b) <==> s.roles.dom().contains(b) && s.roles[b] is Data);
        }
    }
}

pub proof fn write_preserves_ownership_and_other_contents(s: State, b: nat, owner: Owner, bytes: Seq<u8>)
    requires inv(s), owns(s, b, owner), bytes.len() == 4096,
    ensures inv(write(s, b, bytes)), write(s, b, bytes).roles == s.roles,
        read_owned(write(s, b, bytes), b, owner) == Some(bytes),
        forall|other: nat| other != b && s.contents.dom().contains(other)
            ==> #[trigger] write(s, b, bytes).contents[other] == s.contents[other],
{
    let t = write(s, b, bytes);
    assert(s.contents.dom().contains(b));
    assert(t.contents.dom() =~= s.contents.dom());
}

pub proof fn one_block_cannot_have_two_owners(s: State, b: nat, a: Owner, other: Owner)
    requires owns(s, b, a), owns(s, b, other),
    ensures a == other,
{
}

pub proof fn reserved_and_journal_blocks_are_not_readable_as_file_data(s: State, b: nat, owner: Owner)
    requires s.roles.dom().contains(b), s.roles[b] == Role::Journal || s.roles[b] == Role::Reserved,
    ensures read_owned(s, b, owner) == None,
{
}

pub proof fn stale_inode_generation_does_not_authorize_read(s: State, b: nat, live: Owner, stale: Owner)
    requires owns(s, b, live), stale.inode == live.inode, stale.generation != live.generation,
    ensures read_owned(s, b, stale) == None,
{
}

pub proof fn block_reuse_cannot_disclose_previous_contents(s: State, b: nat, old_owner: Owner, new_owner: Owner)
    requires inv(s), owns(s, b, old_owner), old_owner != new_owner,
    ensures inv(allocate(release(s, b), b, new_owner)),
        read_owned(allocate(release(s, b), b, new_owner), b, new_owner) == Some(zeros()),
        read_owned(allocate(release(s, b), b, new_owner), b, old_owner) == None,
{
    release_removes_read_authority(s, b, old_owner);
    fresh_allocation_is_initialized(release(s, b), b, new_owner);
}

pub proof fn allocation_model_has_a_nonempty_instance() {
    let s = State { roles: Map::empty().insert(0, Role::Reserved).insert(1, Role::Free),
        contents: Map::empty() };
    assert(inv(s));
    fresh_allocation_is_initialized(s, 1, Owner { inode: 12, generation: 1 });
    let t = allocate(s, 1, Owner { inode: 12, generation: 1 });
    block_reuse_cannot_disclose_previous_contents(t, 1,
        Owner { inode: 12, generation: 1 }, Owner { inode: 13, generation: 1 });
}

}
