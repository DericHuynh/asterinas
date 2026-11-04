// SPDX-License-Identifier: MPL-2.0

//! Source-bound ACL/DAC decisions for allocated inodes. Caller IDs, mapped
//! groups and capability bits are inputs that the VFS must authenticate. No
//! LSM, idmap, device or runtime-lock authority follows from this host object.

use vstd::prelude::*;
use crate::{access::{self, Credentials}, acl::{self, AclView}, allocated_inode::{self, AllocatedInode, NodeView},
    xattr_inode::{self, AttributesView}, xattr_table::{ValueRef, ValueView}};

verus! {

pub open spec fn capability(mode: u16, c: &Credentials, request: u8, directory: bool) -> bool {
    request <= 7 && (c.dac_override && (directory || request & 1 == 0 || mode & 0o111 != 0)
        || c.dac_read_search && (if directory { request & 2 == 0 } else { request == 4 }))
}
fn capability_allows(mode: u16, c: &Credentials, request: u8, directory: bool) -> (r: bool)
    ensures r == capability(mode, c, request, directory),
{
    request <= 7 && (c.dac_override && (directory || request & 1 == 0 || mode & 0o111 != 0)
        || c.dac_read_search && (if directory { request & 2 == 0 } else { request == 4 }))
}
fn member(groups: &[u32], id: u32) -> (r: bool) ensures r == groups@.contains(id) {
    let mut i = 0usize;
    while i < groups.len()
        invariant i <= groups.len(), forall|j: int| 0 <= j < i ==> #[trigger] groups@[j] != id,
        decreases groups.len() - i,
    { if groups[i] == id { return true; } i += 1; }
    false
}
fn copy_credentials(c: &Credentials) -> (r: Credentials) ensures r == *c {
    Credentials { fsuid: c.fsuid, in_inode_group: c.in_inode_group, dac_override: c.dac_override, dac_read_search: c.dac_read_search }
}

pub struct Detail { pub groups: Seq<u32>, pub attributes: AttributesView, pub acl: Option<AclView> }
pub struct AuthorizationView { pub node: NodeView, pub credentials: Credentials, pub request: u8, pub detail: Detail }
#[verifier::opaque]
pub open spec fn valid(v: AuthorizationView) -> bool {
    &&& allocated_inode::valid(v.node) && v.request <= 7
    &&& xattr_inode::valid(v.detail.attributes) && v.detail.attributes.index == v.node.volume.index && v.detail.attributes.number == v.node.number
    &&& v.credentials.in_inode_group == v.detail.groups.contains(v.node.gid)
    &&& match v.detail.acl {
        None => xattr_inode::absent(v.detail.attributes, 2, Seq::empty())
            && access::permitted(v.node.mode, v.node.uid, &v.credentials, v.request, v.node.mode & 0xf000 == 0x4000),
        Some(acl) => acl::valid(acl) && v.node.mode & 0o777u16 == acl::permission_mode(acl.entries) && xattr_inode::contains(v.detail.attributes, 2, Seq::empty(), ValueView::Bytes(acl.raw))
            && (acl::permitted(acl, v.node.uid, v.node.gid, v.credentials.fsuid, v.detail.groups, v.request)
                || capability(v.node.mode, &v.credentials, v.request, v.node.mode & 0xf000 == 0x4000)),
    }
}

pub struct Authorization<'n, 'v, 'a> { node: &'n AllocatedInode<'v, 'a>, credentials: Credentials, request: u8, detail: Ghost<Detail> }
impl<'n, 'v, 'a> Authorization<'n, 'v, 'a> {
    pub closed spec fn view(&self) -> AuthorizationView { AuthorizationView { node: self.node.view(), credentials: self.credentials, request: self.request, detail: self.detail@ } }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn authorized_node(&self) -> (r: &'n AllocatedInode<'v, 'a>) ensures self.wf(), r.wf(), r.view() == self.view().node {
        proof { use_type_invariant(self); reveal(valid); } self.node
    }
    pub fn requested_bits(&self) -> (r: u8) ensures self.wf(), r == self.view().request {
        proof { use_type_invariant(self); } self.request
    }
    pub(crate) fn release(self) -> (r: (&'n AllocatedInode<'v, 'a>, Credentials, u8, Ghost<AuthorizationView>))
        ensures self.wf(), r.0.wf(), r.0.view() == self.view().node, r.1 == self.view().credentials, r.2 == self.view().request, r.3@ == self.view(),
    {
        proof { use_type_invariant(&self); reveal(valid); }
        let ghost view = self.view();
        (self.node, self.credentials, self.request, Ghost(view))
    }
}

pub fn authorize<'n, 'v, 'a>(node: &'n AllocatedInode<'v, 'a>, credentials: &Credentials, groups: &[u32], request: u8)
    -> (r: Option<Authorization<'n, 'v, 'a>>)
    ensures node.wf(), match r { Some(grant) => grant.wf() && grant.view().node == node.view() && grant.view().credentials == *credentials
        && grant.view().request == request && grant.view().detail.groups == groups@, None => true },
{
    let info = node.info();
    if request > 7 || credentials.in_inode_group != member(groups, info.gid) { return None; }
    let attributes = match xattr_inode::inspect(node.volume().index(), node.number()) { Some(attributes) => attributes, None => { return None; } };
    let name: &[u8] = &[];
    assert(name@ =~= Seq::<u8>::empty());
    let ghost mut acl_view: Option<AclView> = None;
    let directory = info.mode & 0xf000 == 0x4000;
    match attributes.get(2, name) {
        None => { if !access::allowed(info.mode, info.uid, credentials, request, directory) { return None; } },
        Some(ValueRef::Bytes(raw)) => {
            let acl = match acl::parse(raw) { Some(acl) => acl, None => { return None; } };
            if !acl.mode_matches(info.mode) { return None; }
            if !acl.allows(info.uid, info.gid, credentials.fsuid, groups, request)
                && !capability_allows(info.mode, credentials, request, directory) { return None; }
            proof { acl_view = Some(acl.view()); }
        },
        Some(ValueRef::Inode { .. }) => { return None; },
    }
    let ghost detail = Detail { groups: groups@, attributes: attributes.view(), acl: acl_view };
    let ghost view = AuthorizationView { node: node.view(), credentials: *credentials, request, detail };
    assert(valid(view)) by { reveal(valid); }
    Some(Authorization { node, credentials: copy_credentials(credentials), request, detail: Ghost(detail) })
}

pub proof fn an_acl_grant_binds_the_exact_source_inode_and_access_value(v: AuthorizationView)
    requires valid(v), v.detail.acl is Some,
    ensures v.detail.attributes.index.source == v.node.volume.index.source,
        v.detail.attributes.number == v.node.number,
        acl::valid(v.detail.acl.unwrap()),
        xattr_inode::contains(v.detail.attributes, 2, Seq::empty(), ValueView::Bytes(v.detail.acl.unwrap().raw)),
{
    reveal(valid);
}

pub proof fn unprivileged_acl_grants_require_the_actual_acl_decision(v: AuthorizationView)
    requires valid(v), v.detail.acl is Some, !v.credentials.dac_override, !v.credentials.dac_read_search,
    ensures acl::permitted(v.detail.acl.unwrap(), v.node.uid, v.node.gid, v.credentials.fsuid, v.detail.groups, v.request),
{
    reveal(valid);
}

}
