// SPDX-License-Identifier: MPL-2.0

//! Linux ext4's compact POSIX ACL disk representation and permission order.
//! IDs and group membership must already be mapped/authenticated by the VFS.
//! This codec does not establish an idmapped-mount or LSM credential boundary.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::bytes;

verus! {

pub const VERSION: u32 = 1;
pub const INVALID: u8 = 255;

#[derive(Clone, Copy)]
pub struct Entry { pub offset: usize, pub tag: u16, pub permissions: u8, pub id: u32 }

pub open spec fn width(tag: u16) -> nat { if tag == 2 || tag == 8 { 8nat } else { 4nat } }
pub open spec fn named(entries: Seq<Entry>) -> bool { exists|i: int| 0 <= i < entries.len() && ((#[trigger] entries[i]).tag == 2 || entries[i].tag == 8) }
pub open spec fn step(state: u8, tag: u16, needs_mask: bool) -> u8 {
    if state == 1 && tag == 1 { 2u8 }
    else if state == 2 && tag == 2 { 2u8 }
    else if state == 2 && tag == 4 { 3u8 }
    else if state == 3 && tag == 8 { 3u8 }
    else if state == 3 && tag == 16 { 4u8 }
    else if (state == 4 || state == 3 && !needs_mask) && tag == 32 { 0u8 }
    else { INVALID }
}
pub open spec fn state(entries: Seq<Entry>) -> u8 decreases entries.len() {
    if entries.len() == 0 { 1u8 } else { step(state(entries.drop_last()), entries.last().tag, named(entries.drop_last())) }
}
#[verifier::opaque]
pub open spec fn record(raw: Seq<u8>, e: Entry) -> bool {
    &&& raw.len() <= 16777216 && e.offset as nat + width(e.tag) <= raw.len()
    &&& e.tag == 1 || e.tag == 2 || e.tag == 4 || e.tag == 8 || e.tag == 16 || e.tag == 32
    &&& bytes::le16(raw, e.offset as int) == e.tag && bytes::le16(raw, e.offset as int + 2) == e.permissions && e.permissions <= 7
    &&& if e.tag == 2 || e.tag == 8 { bytes::le32(raw, e.offset as int + 4) == e.id && e.id != 4294967295 } else { e.id == 0 }
}
#[verifier::opaque]
pub open spec fn chain(raw: Seq<u8>, entries: Seq<Entry>, end: nat) -> bool {
    &&& 4 <= end <= raw.len() <= 16777216
    &&& entries.len() == 0 ==> end == 4
    &&& entries.len() > 0 ==> entries[0].offset == 4 && end == entries.last().offset as nat + width(entries.last().tag)
    &&& forall|i: int| 0 <= i < entries.len() ==> #[trigger] record(raw, entries[i]) && entries[i].offset >= 4
        && (i > 0 ==> entries[i].offset as nat == entries[i - 1].offset as nat + width(entries[i - 1].tag))
        && state(entries.take(i + 1)) != INVALID
}

fn decode(raw: &[u8], offset: usize) -> (r: Option<Entry>)
    ensures match r { Some(e) => record(raw@, e) && e.offset == offset && e.offset <= 16777212 && e.offset as nat + width(e.tag) <= raw.len(), None => true },
{
    if raw.len() > 16777216 || offset > raw.len() || raw.len() - offset < 4 { return None; }
    let tag = bytes::read_le16(raw, offset).unwrap();
    if tag != 1 && tag != 2 && tag != 4 && tag != 8 && tag != 16 && tag != 32 { return None; }
    let permissions = bytes::read_le16(raw, offset + 2).unwrap();
    if permissions > 7 { return None; }
    let id = if tag == 2 || tag == 8 {
        if raw.len() - offset < 8 { return None; }
        let id = bytes::read_le32(raw, offset + 4).unwrap();
        if id == 4294967295 { return None; }
        id
    } else { 0u32 };
    let entry = Entry { offset, tag, permissions: permissions as u8, id };
    assert(record(raw@, entry)) by { reveal(record); }
    Some(entry)
}

fn advance(state: u8, tag: u16, needs_mask: bool) -> (r: u8) ensures r == step(state, tag, needs_mask) {
    if state == 1 && tag == 1 { 2u8 }
    else if state == 2 && tag == 2 { 2u8 }
    else if state == 2 && tag == 4 { 3u8 }
    else if state == 3 && tag == 8 { 3u8 }
    else if state == 3 && tag == 16 { 4u8 }
    else if (state == 4 || state == 3 && !needs_mask) && tag == 32 { 0u8 }
    else { INVALID }
}

proof fn append(raw: Seq<u8>, entries: Seq<Entry>, end: nat, e: Entry)
    requires chain(raw, entries, end), record(raw, e), e.offset == end, step(state(entries), e.tag, named(entries)) != INVALID,
    ensures chain(raw, entries.push(e), end + width(e.tag)), state(entries.push(e)) == step(state(entries), e.tag, named(entries)),
        named(entries.push(e)) == (named(entries) || e.tag == 2 || e.tag == 8),
{
    reveal(chain); reveal(record);
    assert(entries.push(e).drop_last() =~= entries);
    assert(state(entries.push(e)) == step(state(entries), e.tag, named(entries)));
    assert forall|i: int| 0 <= i < entries.push(e).len() implies #[trigger] record(raw, entries.push(e)[i]) && entries.push(e)[i].offset >= 4
        && (i > 0 ==> entries.push(e)[i].offset as nat == entries.push(e)[i - 1].offset as nat + width(entries.push(e)[i - 1].tag))
        && state(entries.push(e).take(i + 1)) != INVALID by {
        if i < entries.len() {
            assert(entries.push(e)[i] == entries[i]);
            assert(record(raw, entries[i]));
            assert(state(entries.take(i + 1)) != INVALID);
            assert(entries.push(e).take(i + 1) =~= entries.take(i + 1));
        } else {
            assert(entries.push(e).take(i + 1) =~= entries.push(e));
            if i > 0 { assert(entries[i - 1] == entries.last()); }
        }
    }
    if named(entries) {
        let i = choose|i: int| 0 <= i < entries.len() && ((#[trigger] entries[i]).tag == 2 || entries[i].tag == 8);
        assert(entries.push(e)[i] == entries[i]);
    }
    assert(entries.push(e).last() == e);
    if entries.len() > 0 { assert(entries.push(e)[0] == entries[0]); }
    else { assert(entries.push(e)[0] == e); }
    assert(chain(raw, entries.push(e), end + width(e.tag)));
}

pub struct AclView { pub raw: Seq<u8>, pub entries: Seq<Entry> }
pub open spec fn valid(v: AclView) -> bool {
    v.raw.len() >= 4 && bytes::le32(v.raw, 0) == VERSION && chain(v.raw, v.entries, v.raw.len()) && state(v.entries) == 0
}

pub struct Acl<'a> { raw: &'a [u8], entries: Vec<Entry> }
impl<'a> Acl<'a> {
    pub closed spec fn view(&self) -> AclView { AclView { raw: self.raw@, entries: self.entries@ } }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn as_slice(&self) -> (r: &[u8]) ensures self.wf(), r@ == self.view().raw {
        proof { use_type_invariant(self); } self.raw
    }
    pub fn count(&self) -> (r: usize) ensures self.wf(), r == self.view().entries.len() { proof { use_type_invariant(self); } self.entries.len() }
    pub fn entry(&self, index: usize) -> (r: Option<Entry>)
        ensures self.wf(), match r { Some(e) => index < self.view().entries.len() && e == self.view().entries[index as int], None => index >= self.view().entries.len() },
    { proof { use_type_invariant(self); } if index < self.entries.len() { Some(self.entries[index]) } else { None } }
}

pub fn parse(raw: &[u8]) -> (r: Option<Acl<'_>>)
    ensures match r { Some(acl) => acl.wf() && acl.view().raw == raw@, None => true },
{
    if raw.len() < 4 || raw.len() > 16777216 || bytes::read_le32(raw, 0).unwrap() != VERSION { return None; }
    let mut entries = Vec::<Entry>::new();
    let mut offset = 4usize;
    let mut current = 1u8;
    let mut needs_mask = false;
    assert(chain(raw@, entries@, 4)) by { reveal(chain); }
    while offset < raw.len()
        invariant chain(raw@, entries@, offset as nat), current == state(entries@), needs_mask == named(entries@),
            4 <= offset <= raw.len() <= 16777216, bytes::le32(raw@, 0) == VERSION,
        decreases raw.len() - offset,
    {
        let e = match decode(raw, offset) { Some(e) => e, None => { return None; } };
        let next = advance(current, e.tag, needs_mask);
        if next == INVALID { return None; }
        proof { append(raw@, entries@, offset as nat, e); }
        offset += if e.tag == 2 || e.tag == 8 { 8usize } else { 4usize };
        needs_mask = needs_mask || e.tag == 2 || e.tag == 8;
        current = next;
        entries.push(e);
    }
    if current != 0 { return None; }
    Some(Acl { raw, entries })
}

pub open spec fn mask(entries: Seq<Entry>) -> u8 decreases entries.len() {
    if entries.len() == 0 { 7u8 } else if entries[0].tag == 16 { entries[0].permissions } else { mask(entries.skip(1)) }
}

fn mask_bits(entries: &Vec<Entry>) -> (r: u8) ensures r == mask(entries@) {
    let mut i = 0usize;
    assert(entries@.skip(0) =~= entries@);
    while i < entries.len()
        invariant i <= entries.len(), mask(entries@) == mask(entries@.skip(i as int)),
        decreases entries.len() - i,
    {
        if entries[i].tag == 16 { return entries[i].permissions; }
        assert(entries@.skip(i as int).skip(1) =~= entries@.skip(i as int + 1));
        i += 1;
    }
    7
}

pub open spec fn decision(entries: Seq<Entry>, owner: u32, group: u32, uid: u32, groups: Seq<u32>, request: u8, mask: u8, found: bool) -> bool
    decreases entries.len(),
{
    if entries.len() == 0 { false } else {
        let e = entries[0];
        if e.tag == 1 && uid == owner { e.permissions & request == request }
        else if e.tag == 2 && uid == e.id { (e.permissions & mask) & request == request }
        else if e.tag == 4 && groups.contains(group) || e.tag == 8 && groups.contains(e.id) {
            if e.permissions & request == request { (e.permissions & mask) & request == request }
            else { decision(entries.skip(1), owner, group, uid, groups, request, mask, true) }
        } else if e.tag == 32 { !found && e.permissions & request == request }
        else { decision(entries.skip(1), owner, group, uid, groups, request, mask, found) }
    }
}
pub open spec fn permitted(v: AclView, owner: u32, group: u32, uid: u32, groups: Seq<u32>, request: u8) -> bool {
    request <= 7 && decision(v.entries, owner, group, uid, groups, request, mask(v.entries), false)
}

fn member(groups: &[u32], id: u32) -> (r: bool) ensures r == groups@.contains(id) {
    let mut i = 0usize;
    while i < groups.len()
        invariant i <= groups.len(), forall|j: int| 0 <= j < i ==> #[trigger] groups@[j] != id,
        decreases groups.len() - i,
    { if groups[i] == id { return true; } i += 1; }
    false
}

impl<'a> Acl<'a> {
    pub fn allows(&self, owner: u32, group: u32, uid: u32, groups: &[u32], request: u8) -> (r: bool)
        ensures self.wf(), r == permitted(self.view(), owner, group, uid, groups@, request),
    {
        proof { use_type_invariant(self); }
        if request > 7 { return false; }
        let mask = mask_bits(&self.entries);
        let mut i = 0usize;
        let mut found = false;
        assert(self.entries@.skip(0) =~= self.entries@);
        while i < self.entries.len()
            invariant self.wf(), i <= self.entries.len(), request <= 7, mask == crate::acl::mask(self.entries@),
                decision(self.entries@, owner, group, uid, groups@, request, mask, false)
                    == decision(self.entries@.skip(i as int), owner, group, uid, groups@, request, mask, found),
            decreases self.entries.len() - i,
        {
            let e = self.entries[i];
            assert(self.entries@.skip(i as int)[0] == e);
            assert(self.entries@.skip(i as int).skip(1) =~= self.entries@.skip(i as int + 1));
            if e.tag == 1 && uid == owner { return e.permissions & request == request; }
            if e.tag == 2 && uid == e.id { return (e.permissions & mask) & request == request; }
            if e.tag == 4 && member(groups, group) || e.tag == 8 && member(groups, e.id) {
                if e.permissions & request == request { return (e.permissions & mask) & request == request; }
                found = true;
            } else if e.tag == 32 { return !found && e.permissions & request == request; }
            i += 1;
        }
        false
    }
}

pub proof fn decoded_acl_permissions_never_introduce_non_permission_bits(v: AclView, i: int)
    requires valid(v), 0 <= i < v.entries.len(),
    ensures v.entries[i].permissions <= 7,
{
    reveal(chain);
    assert(record(v.raw, v.entries[i]));
    reveal(record);
}

pub proof fn every_accepted_acl_ends_with_other(entries: Seq<Entry>)
    requires state(entries) == 0, entries.len() > 0,
    ensures entries.last().tag == 32,
{
}

pub proof fn owner_acl_entry_takes_precedence_over_all_group_entries(v: AclView, owner: u32, group: u32, groups: Seq<u32>, request: u8)
    requires valid(v), v.entries.len() > 0, v.entries[0].tag == 1,
    ensures permitted(v, owner, group, owner, groups, request) == (request <= 7 && v.entries[0].permissions & request == request),
{
}

pub proof fn a_matching_named_user_is_masked_before_any_group_or_other(v: AclView, owner: u32, group: u32, uid: u32, groups: Seq<u32>, request: u8, i: nat)
    requires valid(v), i < v.entries.len(), uid != owner, v.entries[i as int].tag == 2, v.entries[i as int].id == uid,
        forall|j: int| 0 <= j < i ==> (#[trigger] v.entries[j]).tag == 1 || v.entries[j].tag == 2 && v.entries[j].id != uid,
    ensures permitted(v, owner, group, uid, groups, request)
        == (request <= 7 && (v.entries[i as int].permissions & mask(v.entries)) & request == request),
{
    skip_unmatched_users(v.entries, owner, group, uid, groups, request, mask(v.entries), i);
}

proof fn skip_unmatched_users(entries: Seq<Entry>, owner: u32, group: u32, uid: u32, groups: Seq<u32>, request: u8, mask: u8, i: nat)
    requires i < entries.len(), uid != owner, entries[i as int].tag == 2, entries[i as int].id == uid,
        forall|j: int| 0 <= j < i ==> (#[trigger] entries[j]).tag == 1 || entries[j].tag == 2 && entries[j].id != uid,
    ensures decision(entries, owner, group, uid, groups, request, mask, false) == ((entries[i as int].permissions & mask) & request == request),
    decreases i,
{
    if i > 0 {
        let tail = entries.skip(1);
        assert forall|j: int| 0 <= j < i - 1 implies (#[trigger] tail[j]).tag == 1 || tail[j].tag == 2 && tail[j].id != uid by {
            assert(tail[j] == entries[j + 1]);
        }
        skip_unmatched_users(tail, owner, group, uid, groups, request, mask, (i - 1) as nat);
    }
}

pub proof fn denied_group_class_never_falls_through_to_other(entries: Seq<Entry>, owner: u32, group: u32, uid: u32, groups: Seq<u32>, request: u8, mask: u8)
    requires uid != owner,
        forall|i: int| 0 <= i < entries.len() ==> (#[trigger] entries[i]).tag != 2
            && ((entries[i].tag == 4 && groups.contains(group) || entries[i].tag == 8 && groups.contains(entries[i].id))
                ==> entries[i].permissions & request != request),
    ensures !decision(entries, owner, group, uid, groups, request, mask, true),
    decreases entries.len(),
{
    if entries.len() > 0 {
        let tail = entries.skip(1);
        assert forall|i: int| 0 <= i < tail.len() implies (#[trigger] tail[i]).tag != 2
            && ((tail[i].tag == 4 && groups.contains(group) || tail[i].tag == 8 && groups.contains(tail[i].id))
                ==> tail[i].permissions & request != request) by { assert(tail[i] == entries[i + 1]); }
        denied_group_class_never_falls_through_to_other(tail, owner, group, uid, groups, request, mask);
    }
}

pub open spec fn updated_mode(before: u16, e: Entry) -> u16 {
    if e.tag == 1 { before | ((e.permissions as u16) << 6) }
    else if e.tag == 4 { before | ((e.permissions as u16) << 3) }
    else if e.tag == 16 { (before & !0o70u16) | ((e.permissions as u16) << 3) }
    else if e.tag == 32 { before | e.permissions as u16 }
    else { before }
}
pub open spec fn permission_mode(entries: Seq<Entry>) -> u16 decreases entries.len() {
    if entries.len() == 0 { 0u16 } else { updated_mode(permission_mode(entries.drop_last()), entries.last()) }
}
impl<'a> Acl<'a> {
    pub fn mode_matches(&self, mode: u16) -> (r: bool)
        ensures self.wf(), r == (mode & 0o777u16 == permission_mode(self.view().entries)),
    {
        proof { use_type_invariant(self); }
        let mut bits = 0u16;
        let mut i = 0usize;
        assert(self.entries@.take(0) =~= Seq::<Entry>::empty());
        while i < self.entries.len()
            invariant self.wf(), i <= self.entries.len(), bits == permission_mode(self.entries@.take(i as int)),
            decreases self.entries.len() - i,
        {
            let e = self.entries[i];
            let ghost before = bits;
            if e.tag == 1 { bits = bits | ((e.permissions as u16) << 6); }
            else if e.tag == 4 { bits = bits | ((e.permissions as u16) << 3); }
            else if e.tag == 16 { bits = (bits & !0o70u16) | ((e.permissions as u16) << 3); }
            else if e.tag == 32 { bits = bits | e.permissions as u16; }
            assert(self.entries@.take(i as int + 1).drop_last() =~= self.entries@.take(i as int));
            assert(self.entries@.take(i as int + 1).last() == e);
            assert(bits == updated_mode(before, e));
            i += 1;
        }
        assert(self.entries@.take(i as int) =~= self.entries@);
        mode & 0o777u16 == bits
    }
}

proof fn same_record(raw: Seq<u8>, a: Entry, b: Entry)
    requires record(raw, a), record(raw, b), a.offset == b.offset,
    ensures a == b,
{ reveal(record); }
proof fn same_prefix(a: AclView, b: AclView, count: nat)
    requires valid(a), valid(b), a.raw == b.raw, count <= a.entries.len(), count <= b.entries.len(),
    ensures a.entries.take(count as int) == b.entries.take(count as int),
        forall|j: int| 0 <= j < count ==> #[trigger] a.entries[j] == #[trigger] b.entries[j],
    decreases count,
{
    reveal(chain);
    if count > 0 {
        same_prefix(a, b, (count - 1) as nat);
        let i = count as int - 1;
        if i > 0 { assert(a.entries[i - 1] == b.entries[i - 1]); }
        assert(record(a.raw, a.entries[i])); assert(record(b.raw, b.entries[i]));
        assert(a.entries[i].offset == b.entries[i].offset);
        same_record(a.raw, a.entries[i], b.entries[i]);
        assert forall|j: int| 0 <= j < count implies #[trigger] a.entries[j] == #[trigger] b.entries[j] by {
            if j < i { assert(a.entries[j] == b.entries[j]); }
        }
        assert(a.entries.take(count as int) =~= b.entries.take(count as int));
    }
}
pub proof fn complete_acls_from_the_same_bytes_have_identical_entries(a: AclView, b: AclView)
    requires valid(a), valid(b), a.raw == b.raw,
    ensures a == b,
{
    reveal(chain);
    let count = if a.entries.len() < b.entries.len() { a.entries.len() } else { b.entries.len() };
    same_prefix(a, b, count);
    if a.entries.len() < b.entries.len() {
        assert(a.entries.len() > 0);
        assert(b.entries[a.entries.len() as int - 1] == a.entries.last());
        let next = b.entries[a.entries.len() as int];
        assert(record(b.raw, next));
        assert(next.offset as nat == b.entries[a.entries.len() as int - 1].offset as nat + width(b.entries[a.entries.len() as int - 1].tag));
        assert(a.raw.len() == a.entries.last().offset as nat + width(a.entries.last().tag));
        assert(next.offset == a.raw.len()); reveal(record);
    } else if b.entries.len() < a.entries.len() {
        assert(b.entries.len() > 0);
        assert(a.entries[b.entries.len() as int - 1] == b.entries.last());
        let next = a.entries[b.entries.len() as int];
        assert(record(a.raw, next));
        assert(next.offset as nat == a.entries[b.entries.len() as int - 1].offset as nat + width(a.entries[b.entries.len() as int - 1].tag));
        assert(b.raw.len() == b.entries.last().offset as nat + width(b.entries.last().tag));
        assert(next.offset == b.raw.len()); reveal(record);
    }
    assert(a.entries =~= b.entries);
}

}
