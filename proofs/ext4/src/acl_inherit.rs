// SPDX-License-Identifier: MPL-2.0

//! Source-bound Linux ACL creation planning, without child mutation authority.
//! Allocating, initializing and publishing a child inode remain separate VFS
//! and journal obligations; a Plan is not an I/O capability or a create handle.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{acl, acl_transform::{self, TransformView}, allocated_inode::{self, AllocatedInode, NodeView},
    xattr_inode::{self, AttributesView}, xattr_table::{ValueRef, ValueView}};

verus! {

pub open spec fn supported(mode: u16) -> bool {
    let kind = mode & 0xf000u16;
    kind == 0x1000 || kind == 0x2000 || kind == 0x4000 || kind == 0x6000
        || kind == 0x8000 || kind == 0xa000 || kind == 0xc000
}
fn supported_mode(mode: u16) -> (r: bool) ensures r == supported(mode) {
    let kind = mode & 0xf000u16;
    kind == 0x1000 || kind == 0x2000 || kind == 0x4000 || kind == 0x6000
        || kind == 0x8000 || kind == 0xa000 || kind == 0xc000
}
pub open spec fn masked(requested: u16, umask: u16) -> u16 { requested & !(umask & 0o777u16) }

pub struct PlanView {
    pub parent: NodeView, pub attributes: AttributesView, pub requested: u16, pub umask: u16,
    pub mode: u16, pub access: Option<Seq<u8>>, pub default: Option<Seq<u8>>, pub inherited: Option<TransformView>,
}

#[verifier::opaque]
pub open spec fn valid(v: PlanView) -> bool {
    &&& allocated_inode::valid(v.parent) && v.parent.mode & 0xf000u16 == 0x4000 && supported(v.requested)
    &&& xattr_inode::valid(v.attributes) && v.attributes.index == v.parent.volume.index && v.attributes.number == v.parent.number
    &&& v.mode & v.requested == v.mode && v.mode & !0o777u16 == v.requested & !0o777u16
    &&& if v.requested & 0xf000u16 == 0xa000 {
        v.mode == v.requested && v.access is None && v.default is None && v.inherited is None
    } else {
        match v.inherited {
            None => xattr_inode::absent(v.attributes, 3, Seq::empty()) && v.mode == masked(v.requested, v.umask)
                && v.access is None && v.default is None,
            Some(t) => acl_transform::valid(t) && t.inheritance && t.requested == v.requested && t.mode == v.mode
                && xattr_inode::contains(v.attributes, 3, Seq::empty(), ValueView::Bytes(t.before.raw))
                && v.access == (if t.extended { Some(t.after.raw) } else { None })
                && v.default == (if v.requested & 0xf000u16 == 0x4000 { Some(t.before.raw) } else { None }),
        }
    }
}

pub struct Plan { mode: u16, access: Option<Vec<u8>>, default: Option<Vec<u8>>, checked: Ghost<PlanView> }
impl Plan {
    pub closed spec fn view(&self) -> PlanView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        valid(self.view()) && self.mode == self.view().mode
            && (match &self.access { Some(value) => self.view().access == Some(value@), None => self.view().access is None })
            && (match &self.default { Some(value) => self.view().default == Some(value@), None => self.view().default is None })
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn mode(&self) -> (r: u16) ensures self.wf(), r == self.view().mode {
        proof { use_type_invariant(self); } self.mode
    }
    pub fn access(&self) -> (r: Option<&[u8]>)
        ensures self.wf(), match r { Some(value) => self.view().access == Some(value@), None => self.view().access is None },
    {
        proof { use_type_invariant(self); }
        match &self.access { Some(value) => Some(value.as_slice()), None => None }
    }
    pub fn default(&self) -> (r: Option<&[u8]>)
        ensures self.wf(), match r { Some(value) => self.view().default == Some(value@), None => self.view().default is None },
    {
        proof { use_type_invariant(self); }
        match &self.default { Some(value) => Some(value.as_slice()), None => None }
    }
}

fn copy(input: &[u8]) -> (r: Vec<u8>) ensures r@ == input@ {
    let mut value = Vec::new(); let mut i = 0usize;
    while i < input.len()
        invariant i <= input.len(), value@ == input@.take(i as int),
        decreases input.len() - i,
    { value.push(input[i]); assert(value@ =~= input@.take(i as int + 1)); i += 1; }
    value
}

pub fn prepare(parent: &AllocatedInode<'_, '_>, requested: u16, umask: u16) -> (r: Option<Plan>)
    ensures parent.wf(), match r { Some(plan) => plan.wf() && valid(plan.view()) && plan.view().parent == parent.view()
        && plan.view().requested == requested && plan.view().umask == umask, None => true },
{
    let info = parent.info();
    if info.mode & 0xf000u16 != 0x4000 || !supported_mode(requested) { return None; }
    let attributes = match xattr_inode::inspect(parent.volume().index(), parent.number()) { Some(value) => value, None => { return None; } };
    assert(requested & requested == requested) by (bit_vector);
    let mut mode = requested; let mut access: Option<Vec<u8>> = None; let mut default: Option<Vec<u8>> = None;
    let ghost mut inherited: Option<TransformView> = None;
    if requested & 0xf000u16 != 0xa000 {
        let name: &[u8] = &[]; assert(name@ =~= Seq::<u8>::empty());
        match attributes.get(3, name) {
            None => {
                mode = requested & !(umask & 0o777u16);
                assert(mode & requested == mode && mode & !0o777u16 == requested & !0o777u16) by (bit_vector) requires mode == requested & !(umask & 0o777u16);
            },
            Some(ValueRef::Bytes(raw)) => {
                let before = match acl::parse(raw) { Some(value) => value, None => { return None; } };
                let transformed = match acl_transform::inherit(&before, requested) { Some(value) => value, None => { return None; } };
                mode = transformed.mode();
                if transformed.extended() { access = Some(copy(transformed.as_slice())); }
                if requested & 0xf000u16 == 0x4000 { default = Some(copy(raw)); }
                proof { inherited = Some(transformed.view()); }
            },
            Some(ValueRef::Inode { .. }) => { return None; },
        }
    }
    let ghost checked = PlanView { parent: parent.view(), attributes: attributes.view(), requested, umask, mode,
        access: match &access { Some(value) => Some(value@), None => None },
        default: match &default { Some(value) => Some(value@), None => None }, inherited };
    assert(mode & requested == mode && mode & !0o777u16 == requested & !0o777u16);
    assert(valid(checked)) by { reveal(valid); }
    Some(Plan { mode, access, default, checked: Ghost(checked) })
}

pub proof fn inheritance_is_bound_to_the_exact_parent_and_default_acl(v: PlanView)
    requires valid(v), v.inherited is Some,
    ensures v.attributes.index.source == v.parent.volume.index.source, v.attributes.number == v.parent.number,
        xattr_inode::contains(v.attributes, 3, Seq::empty(), ValueView::Bytes(v.inherited.unwrap().before.raw)),
{ reveal(valid); }
pub proof fn child_default_acls_are_exact_parent_copies_only_for_directories(v: PlanView)
    requires valid(v), v.inherited is Some,
    ensures v.default == (if v.requested & 0xf000u16 == 0x4000 { Some(v.inherited.unwrap().before.raw) } else { None }),
{ reveal(valid); }
pub proof fn inherited_access_acls_are_retained_exactly_when_extended(v: PlanView)
    requires valid(v), v.inherited is Some,
    ensures v.access == (if v.inherited.unwrap().extended { Some(v.inherited.unwrap().after.raw) } else { None }),
{ reveal(valid); }
pub proof fn creation_plans_do_not_add_requested_permissions_or_change_special_bits(v: PlanView)
    requires valid(v),
    ensures v.mode & v.requested == v.mode, v.mode & !0o777u16 == v.requested & !0o777u16,
{ reveal(valid); }
pub proof fn umask_is_applied_only_without_a_parent_default_acl(v: PlanView)
    requires valid(v), v.requested & 0xf000u16 != 0xa000, v.inherited is None,
    ensures xattr_inode::absent(v.attributes, 3, Seq::empty()), v.mode == masked(v.requested, v.umask), v.access is None, v.default is None,
{ reveal(valid); }
pub proof fn symlink_creation_skips_acl_and_umask(v: PlanView)
    requires valid(v), v.requested & 0xf000u16 == 0xa000,
    ensures v.mode == v.requested, v.access is None, v.default is None, v.inherited is None,
{ reveal(valid); }

}
