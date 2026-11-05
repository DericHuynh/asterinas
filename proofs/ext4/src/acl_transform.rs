// SPDX-License-Identifier: MPL-2.0

//! Pure Linux POSIX ACL chmod and creation-mask transformations.
//! This codec does not grant inode mutation or authenticate a parent/child pair.

use vstd::prelude::*;
use crate::{acl::{self, Acl, AclView, Entry}, acl_xattr, bytes};

verus! {

pub open spec fn has_mask(v: AclView) -> bool {
    exists|i: int| 0 <= i < v.entries.len() && (#[trigger] v.entries[i]).tag == 16
}
pub open spec fn requested_permissions(e: Entry, mode: u16) -> u8 {
    if e.tag == 1 { ((mode >> 6) & 7) as u8 }
    else if e.tag == 4 || e.tag == 16 { ((mode >> 3) & 7) as u8 }
    else { (mode & 7) as u8 }
}
pub open spec fn selected(e: Entry, mask: bool) -> bool {
    e.tag == 1 || e.tag == 32 || e.tag == 16 || e.tag == 4 && !mask
}
pub open spec fn permissions(e: Entry, mode: u16, mask: bool, inheritance: bool) -> u8 {
    if selected(e, mask) {
        if inheritance { e.permissions & requested_permissions(e, mode) } else { requested_permissions(e, mode) }
    } else { e.permissions }
}
pub open spec fn corresponding(before: AclView, after: AclView, mode: u16, inheritance: bool, i: int) -> bool {
    let a = before.entries[i]; let b = after.entries[i];
    a.offset == b.offset && a.tag == b.tag && a.id == b.id
        && b.permissions == permissions(a, mode, has_mask(before), inheritance)
}
pub struct TransformView {
    pub before: AclView, pub after: AclView, pub requested: u16, pub mode: u16, pub inheritance: bool, pub extended: bool,
}
pub open spec fn valid(v: TransformView) -> bool {
    &&& acl::valid(v.before) && acl::valid(v.after)
    &&& v.before.raw.len() == v.after.raw.len() && v.before.raw.len() <= 65536
    &&& v.before.entries.len() == v.after.entries.len()
    &&& forall|i: int| 0 <= i < v.before.entries.len() ==> #[trigger] corresponding(v.before, v.after, v.requested, v.inheritance, i)
    &&& v.mode & !0o777u16 == v.requested & !0o777u16
    &&& v.mode & 0o777u16 == acl::permission_mode(v.after.entries)
    &&& v.extended == acl_xattr::non_equivalent(v.after)
    &&& if v.inheritance { v.mode & v.requested == v.mode } else { v.mode == v.requested }
}

pub struct Transformed { disk: Vec<u8>, checked: Ghost<TransformView>, mode: u16, extended: bool }
impl Transformed {
    pub closed spec fn view(&self) -> TransformView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        valid(self.view()) && self.disk@ == self.view().after.raw && self.mode == self.view().mode && self.extended == self.view().extended
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn as_slice(&self) -> (r: &[u8]) ensures self.wf(), r@ == self.view().after.raw {
        proof { use_type_invariant(self); } &self.disk
    }
    pub fn mode(&self) -> (r: u16) ensures self.wf(), r == self.view().mode {
        proof { use_type_invariant(self); } self.mode
    }
    pub fn extended(&self) -> (r: bool) ensures self.wf(), r == self.view().extended {
        proof { use_type_invariant(self); } self.extended
    }
    pub fn parsed(&self) -> (r: Option<Acl<'_>>)
        ensures self.wf(), match r { Some(value) => value.wf() && value.view() == self.view().after, None => true },
    {
        proof { use_type_invariant(self); }
        let value = match acl::parse(&self.disk) { Some(value) => value, None => { return None; } };
        proof { acl::complete_acls_from_the_same_bytes_have_identical_entries(value.view(), self.view().after); }
        Some(value)
    }
}

fn mask_present(value: &Acl<'_>) -> (r: bool)
    ensures value.wf(), r == has_mask(value.view()),
{
    let n = value.count(); let mut i = 0usize;
    while i < n
        invariant value.wf(), n == value.view().entries.len(), i <= n,
            forall|j: int| 0 <= j < i ==> (#[trigger] value.view().entries[j]).tag != 16,
        decreases n - i,
    {
        if value.entry(i).unwrap().tag == 16 { return true; }
        i += 1;
    }
    false
}
fn changed_permissions(e: Entry, mode: u16, mask: bool, inheritance: bool) -> (r: u8)
    ensures r == permissions(e, mode, mask, inheritance),
{
    if e.tag == 1 || e.tag == 32 || e.tag == 16 || e.tag == 4 && !mask {
        let wanted = if e.tag == 1 { ((mode >> 6) & 7) as u8 }
            else if e.tag == 4 || e.tag == 16 { ((mode >> 3) & 7) as u8 }
            else { (mode & 7) as u8 };
        if inheritance { e.permissions & wanted } else { wanted }
    } else { e.permissions }
}
fn same_entries(before: &Acl<'_>, after: &Acl<'_>, requested: u16, inheritance: bool) -> (r: bool)
    ensures before.wf(), after.wf(), r ==> before.view().entries.len() == after.view().entries.len()
        && forall|i: int| 0 <= i < before.view().entries.len() ==> #[trigger] corresponding(before.view(), after.view(), requested, inheritance, i),
{
    let n = before.count(); if after.count() != n { return false; }
    let mask = mask_present(before); let mut i = 0usize;
    while i < n
        invariant before.wf(), after.wf(), n == before.view().entries.len(), n == after.view().entries.len(), i <= n,
            mask == has_mask(before.view()),
            forall|j: int| 0 <= j < i ==> #[trigger] corresponding(before.view(), after.view(), requested, inheritance, j),
        decreases n - i,
    {
        let a = before.entry(i).unwrap(); let b = after.entry(i).unwrap();
        if a.offset != b.offset || a.tag != b.tag || a.id != b.id || b.permissions != changed_permissions(a, requested, mask, inheritance) { return false; }
        assert(corresponding(before.view(), after.view(), requested, inheritance, i as int)); i += 1;
    }
    true
}
fn transform(value: &Acl<'_>, requested: u16, inheritance: bool) -> (r: Option<Transformed>)
    ensures value.wf(), match r { Some(t) => t.wf() && valid(t.view()) && t.view().before == value.view() && t.view().requested == requested && t.view().inheritance == inheritance, None => true },
{
    let before = value.as_slice(); if before.len() > 65536 { return None; }
    let n = value.count(); let mask = mask_present(value); let mut disk = Vec::new(); let mut j = 0usize;
    while j < before.len()
        invariant value.wf(), before@ == value.view().raw, before.len() <= 65536, j <= before.len(), disk@ == before@.take(j as int),
        decreases before.len() - j,
    { disk.push(before[j]); assert(disk@ =~= before@.take(j as int + 1)); j += 1; }
    let mut i = 0usize;
    while i < n
        invariant value.wf(), before@ == value.view().raw, n == value.view().entries.len(), i <= n,
            before.len() <= 65536, disk.len() == before.len(), mask == has_mask(value.view()),
        decreases n - i,
    {
        let e = value.entry(i).unwrap();
        proof { acl::decoded_acl_permissions_never_introduce_non_permission_bits(value.view(), i as int); }
        if e.offset > disk.len() || disk.len() - e.offset < 4 { return None; }
        let word = bytes::encode_le16(changed_permissions(e, requested, mask, inheritance) as u16);
        bytes::write_bytes(disk.as_mut_slice(), e.offset + 2, &word); i += 1;
    }
    let after = match acl::parse(&disk) { Some(value) => value, None => { return None; } };
    if !same_entries(value, &after, requested, inheritance) { return None; }
    let summary = match acl_xattr::summarize(&after) { Some(value) => value, None => { return None; } };
    let bits = summary.bits; let mode = (requested & !0o777u16) | bits;
    if inheritance { if mode & requested != mode { return None; } }
    else { if mode != requested { return None; } }
    assert(mode & !0o777u16 == requested & !0o777u16) by (bit_vector) requires bits <= 0o777u16, mode == (requested & !0o777u16) | bits;
    assert(mode & 0o777u16 == bits) by (bit_vector) requires bits <= 0o777u16, mode == (requested & !0o777u16) | bits;
    let ghost checked = TransformView { before: value.view(), after: after.view(), requested, mode, inheritance, extended: summary.extended };
    Some(Transformed { disk, checked: Ghost(checked), mode, extended: summary.extended })
}

pub fn chmod(value: &Acl<'_>, mode: u16) -> (r: Option<Transformed>)
    ensures value.wf(), match r { Some(t) => t.wf() && valid(t.view()) && t.view().before == value.view() && t.view().requested == mode && !t.view().inheritance && t.view().mode == mode, None => true },
{ transform(value, mode, false) }
pub fn inherit(value: &Acl<'_>, mode: u16) -> (r: Option<Transformed>)
    ensures value.wf(), match r { Some(t) => t.wf() && valid(t.view()) && t.view().before == value.view() && t.view().requested == mode && t.view().inheritance && t.view().mode & mode == t.view().mode, None => true },
{ transform(value, mode, true) }

pub proof fn acl_transforms_preserve_all_entry_tags_offsets_and_identifiers(v: TransformView, i: int)
    requires valid(v), 0 <= i < v.before.entries.len(),
    ensures v.after.entries[i].tag == v.before.entries[i].tag,
        v.after.entries[i].id == v.before.entries[i].id,
        v.after.entries[i].offset == v.before.entries[i].offset,
{ assert(corresponding(v.before, v.after, v.requested, v.inheritance, i)); }
pub proof fn acl_transforms_preserve_every_named_entry_permission(v: TransformView, i: int)
    requires valid(v), 0 <= i < v.before.entries.len(), v.before.entries[i].tag == 2 || v.before.entries[i].tag == 8,
    ensures v.after.entries[i].permissions == v.before.entries[i].permissions,
{ assert(corresponding(v.before, v.after, v.requested, v.inheritance, i)); }
pub proof fn acl_transforms_preserve_group_object_permissions_when_a_mask_exists(v: TransformView, i: int)
    requires valid(v), has_mask(v.before), 0 <= i < v.before.entries.len(), v.before.entries[i].tag == 4,
    ensures v.after.entries[i].permissions == v.before.entries[i].permissions,
{ assert(corresponding(v.before, v.after, v.requested, v.inheritance, i)); }
pub proof fn inherited_acl_permissions_never_exceed_the_parent_default(v: TransformView, i: int)
    requires valid(v), v.inheritance, 0 <= i < v.before.entries.len(),
    ensures v.after.entries[i].permissions & v.before.entries[i].permissions == v.after.entries[i].permissions,
{
    assert(corresponding(v.before, v.after, v.requested, v.inheritance, i));
    let a = v.before.entries[i]; let b = v.after.entries[i];
    let old = a.permissions; let next = b.permissions; let wanted = requested_permissions(a, v.requested);
    if selected(a, has_mask(v.before)) {
        assert(next == old & wanted);
        assert(next & old == next) by (bit_vector) requires next == old & wanted;
    } else {
        assert(next == old);
        assert(next & old == next) by (bit_vector) requires next == old;
    }
}
pub proof fn inherited_modes_never_add_requested_permissions_or_change_special_bits(v: TransformView)
    requires valid(v), v.inheritance,
    ensures v.mode & v.requested == v.mode, v.mode & !0o777u16 == v.requested & !0o777u16,
{}
pub proof fn chmod_transforms_have_the_exact_requested_permission_classes(v: TransformView, i: int)
    requires valid(v), !v.inheritance, 0 <= i < v.before.entries.len(), selected(v.before.entries[i], has_mask(v.before)),
    ensures v.after.entries[i].permissions == requested_permissions(v.before.entries[i], v.requested), v.mode == v.requested,
{ assert(corresponding(v.before, v.after, v.requested, v.inheritance, i)); }

proof fn shrinking_masks(before: Seq<Entry>, after: Seq<Entry>)
    requires before.len() == after.len(),
        forall|i: int| 0 <= i < before.len() ==> (#[trigger] before[i]).tag == (#[trigger] after[i]).tag
            && after[i].permissions & before[i].permissions == after[i].permissions,
    ensures acl::mask(after) & acl::mask(before) == acl::mask(after),
    decreases before.len(),
{
    reveal_with_fuel(acl::mask, 2);
    if before.len() > 0 {
        assert(before[0].tag == after[0].tag);
        if before[0].tag == 16 {
            assert(acl::mask(before) == before[0].permissions);
            assert(acl::mask(after) == after[0].permissions);
            assert(after[0].permissions & before[0].permissions == after[0].permissions);
        } else {
            let a = before.skip(1); let b = after.skip(1);
            assert forall|i: int| 0 <= i < a.len() implies (#[trigger] a[i]).tag == (#[trigger] b[i]).tag
                && b[i].permissions & a[i].permissions == b[i].permissions by {
                assert(a[i] == before[i + 1]); assert(b[i] == after[i + 1]);
            }
            shrinking_masks(a, b);
            assert(acl::mask(before) == acl::mask(a));
            assert(acl::mask(after) == acl::mask(b));
            assert(acl::mask(after) & acl::mask(before) == acl::mask(after));
        }
    } else {
        let old = acl::mask(before); let next = acl::mask(after);
        assert(old == 7u8 && next == 7u8);
        assert(next & old == next) by (bit_vector) requires old == 7u8, next == 7u8;
    }
}
pub proof fn inherited_effective_class_permissions_never_exceed_the_parent_default(v: TransformView, i: int)
    requires valid(v), v.inheritance, 0 <= i < v.before.entries.len(),
    ensures (v.after.entries[i].permissions & acl::mask(v.after.entries))
        & (v.before.entries[i].permissions & acl::mask(v.before.entries))
            == (v.after.entries[i].permissions & acl::mask(v.after.entries)),
{
    assert forall|j: int| 0 <= j < v.before.entries.len() implies (#[trigger] v.before.entries[j]).tag == (#[trigger] v.after.entries[j]).tag
        && v.after.entries[j].permissions & v.before.entries[j].permissions == v.after.entries[j].permissions by {
        acl_transforms_preserve_all_entry_tags_offsets_and_identifiers(v, j);
        inherited_acl_permissions_never_exceed_the_parent_default(v, j);
    }
    shrinking_masks(v.before.entries, v.after.entries);
    inherited_acl_permissions_never_exceed_the_parent_default(v, i);
    let a = v.before.entries[i].permissions; let b = v.after.entries[i].permissions;
    let m = acl::mask(v.before.entries); let n = acl::mask(v.after.entries);
    assert((b & n) & (a & m) == (b & n)) by (bit_vector)
        requires b & a == b, n & m == n;
}

// Append inside acl_transform.rs's verus! block.
// These lemmas concern the same numeric owner/group and authenticated caller.
// They do not compare a new child's owner with the parent's owner.

proof fn subset_permissions_preserve_grants(before: u8, after: u8, request: u8)
    requires after & before == after, after & request == request,
    ensures before & request == request,
{
    assert(before & request == request) by (bit_vector)
        requires after & before == after, after & request == request;
}

proof fn subset_masked_permissions_preserve_grants(before: u8, after: u8, old_mask: u8, new_mask: u8, request: u8)
    requires after & before == after, new_mask & old_mask == new_mask, (after & new_mask) & request == request,
    ensures (before & old_mask) & request == request,
{
    assert((before & old_mask) & request == request) by (bit_vector)
        requires after & before == after, new_mask & old_mask == new_mask, (after & new_mask) & request == request;
}

// Once a matching group has been found, OTHER can never grant access.
// Every remaining successful non-owner branch therefore proves the mask.
proof fn a_successful_found_group_decision_requires_the_mask(entries: Seq<Entry>, owner: u32, group: u32, uid: u32,
    groups: Seq<u32>, request: u8, mask: u8)
    requires uid != owner, acl::decision(entries, owner, group, uid, groups, request, mask, true),
    ensures mask & request == request,
    decreases entries.len(),
{
    if entries.len() > 0 {
        let e = entries[0]; let p = e.permissions;
        if e.tag == 2 && uid == e.id {
            assert((p & mask) & request == request);
            assert(mask & request == request) by (bit_vector)
                requires (p & mask) & request == request;
        } else if e.tag == 4 && groups.contains(group) || e.tag == 8 && groups.contains(e.id) {
            if e.permissions & request == request {
                assert((p & mask) & request == request);
                assert(mask & request == request) by (bit_vector)
                    requires (p & mask) & request == request;
            } else {
                a_successful_found_group_decision_requires_the_mask(entries.skip(1), owner, group, uid, groups, request, mask);
            }
        } else if e.tag == 32 {
            assert(!acl::decision(entries, owner, group, uid, groups, request, mask, true));
        } else {
            a_successful_found_group_decision_requires_the_mask(entries.skip(1), owner, group, uid, groups, request, mask);
        }
    }
}

spec fn subject_entries_shrink(before: Seq<Entry>, after: Seq<Entry>) -> bool {
    before.len() == after.len()
        && forall|i: int| 0 <= i < before.len() ==> (#[trigger] before[i]).tag == (#[trigger] after[i]).tag
            && before[i].id == after[i].id && after[i].permissions & before[i].permissions == after[i].permissions
}

// No canonical ACL ordering is needed here because owner decisions are
// handled separately. Even a group branch skipped after masking cannot
// manufacture a grant: a later successful group proves the new mask, and
// therefore also proves the old mask.
proof fn shrinking_nonowner_decisions_preserve_grants(before: Seq<Entry>, after: Seq<Entry>, owner: u32, group: u32,
    uid: u32, groups: Seq<u32>, request: u8, old_mask: u8, new_mask: u8, found: bool)
    requires uid != owner, subject_entries_shrink(before, after), new_mask & old_mask == new_mask,
        acl::decision(after, owner, group, uid, groups, request, new_mask, found),
    ensures acl::decision(before, owner, group, uid, groups, request, old_mask, found),
    decreases before.len(),
{
    if before.len() > 0 {
        let a = before[0]; let b = after[0];
        assert(a.tag == b.tag && a.id == b.id && b.permissions & a.permissions == b.permissions);
        let old_tail = before.skip(1); let new_tail = after.skip(1);
        assert forall|i: int| 0 <= i < old_tail.len() implies (#[trigger] old_tail[i]).tag == (#[trigger] new_tail[i]).tag
            && old_tail[i].id == new_tail[i].id && new_tail[i].permissions & old_tail[i].permissions == new_tail[i].permissions by {
            assert(old_tail[i] == before[i + 1]); assert(new_tail[i] == after[i + 1]);
        }
        assert(subject_entries_shrink(old_tail, new_tail));
        if b.tag == 2 && uid == b.id {
            assert((b.permissions & new_mask) & request == request);
            subset_masked_permissions_preserve_grants(a.permissions, b.permissions, old_mask, new_mask, request);
        } else if b.tag == 4 && groups.contains(group) || b.tag == 8 && groups.contains(b.id) {
            if b.permissions & request == request {
                assert((b.permissions & new_mask) & request == request);
                subset_permissions_preserve_grants(a.permissions, b.permissions, request);
                subset_masked_permissions_preserve_grants(a.permissions, b.permissions, old_mask, new_mask, request);
            } else {
                assert(acl::decision(new_tail, owner, group, uid, groups, request, new_mask, true));
                if a.permissions & request == request {
                    a_successful_found_group_decision_requires_the_mask(new_tail, owner, group, uid, groups, request, new_mask);
                    subset_permissions_preserve_grants(old_mask, new_mask, request);
                    let p = a.permissions;
                    assert((p & old_mask) & request == request) by (bit_vector)
                        requires p & request == request, old_mask & request == request;
                } else {
                    shrinking_nonowner_decisions_preserve_grants(old_tail, new_tail, owner, group, uid, groups, request, old_mask, new_mask, true);
                }
            }
        } else if b.tag == 32 {
            assert(!found && b.permissions & request == request);
            subset_permissions_preserve_grants(a.permissions, b.permissions, request);
        } else {
            shrinking_nonowner_decisions_preserve_grants(old_tail, new_tail, owner, group, uid, groups, request, old_mask, new_mask, found);
        }
    }
}

proof fn a_complete_acl_starts_with_the_owning_user(v: AclView)
    requires acl::valid(v),
    ensures v.entries.len() > 0, v.entries[0].tag == 1,
{
    reveal(acl::chain);
    reveal_with_fuel(acl::state, 2);
    assert(v.entries.len() > 0);
    assert(acl::record(v.raw, v.entries[0]));
    assert(acl::state(v.entries.take(1)) != acl::INVALID);
    assert(v.entries.take(1).drop_last() =~= Seq::<Entry>::empty());
    assert(v.entries.take(1).last() == v.entries[0]);
    assert(acl::state(Seq::<Entry>::empty()) == 1u8);
    assert(!acl::named(Seq::<Entry>::empty()));
    assert(acl::state(v.entries.take(1)) == acl::step(1, v.entries[0].tag, false));
}

pub proof fn inherited_acls_never_grant_a_subject_access_denied_by_the_parent_default(v: TransformView,
    owner: u32, group: u32, uid: u32, groups: Seq<u32>, request: u8)
    requires valid(v), v.inheritance, acl::permitted(v.after, owner, group, uid, groups, request),
    ensures acl::permitted(v.before, owner, group, uid, groups, request),
{
    if uid == owner {
        a_complete_acl_starts_with_the_owning_user(v.before);
        a_complete_acl_starts_with_the_owning_user(v.after);
        acl::owner_acl_entry_takes_precedence_over_all_group_entries(v.before, owner, group, groups, request);
        acl::owner_acl_entry_takes_precedence_over_all_group_entries(v.after, owner, group, groups, request);
        inherited_acl_permissions_never_exceed_the_parent_default(v, 0);
        subset_permissions_preserve_grants(v.before.entries[0].permissions, v.after.entries[0].permissions, request);
    } else {
        assert forall|i: int| 0 <= i < v.before.entries.len() implies (#[trigger] v.before.entries[i]).tag == (#[trigger] v.after.entries[i]).tag
            && v.before.entries[i].id == v.after.entries[i].id
            && v.after.entries[i].permissions & v.before.entries[i].permissions == v.after.entries[i].permissions by {
            acl_transforms_preserve_all_entry_tags_offsets_and_identifiers(v, i);
            inherited_acl_permissions_never_exceed_the_parent_default(v, i);
        }
        assert(subject_entries_shrink(v.before.entries, v.after.entries));
        assert forall|i: int| 0 <= i < v.before.entries.len() implies (#[trigger] v.before.entries[i]).tag == (#[trigger] v.after.entries[i]).tag
            && v.after.entries[i].permissions & v.before.entries[i].permissions == v.after.entries[i].permissions by {
            assert(subject_entries_shrink(v.before.entries, v.after.entries));
        }
        shrinking_masks(v.before.entries, v.after.entries);
        shrinking_nonowner_decisions_preserve_grants(v.before.entries, v.after.entries, owner, group, uid, groups, request,
            acl::mask(v.before.entries), acl::mask(v.after.entries), false);
    }
}

}
