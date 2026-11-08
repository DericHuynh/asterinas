// SPDX-License-Identifier: MPL-2.0

//! Ext4 project-ID fields, inheritance and project-bound namespace checks.
//! These field/policy operations confer no credential or inode authority.
//! Changing a live project requires quota transfer and inode checksum/journal
//! composition by the filesystem operation; neither is implicit in this codec.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::bytes;

verus! {

pub const PROJECT_ID_OFFSET: usize = 156;
pub const PROJECT_INHERIT: u32 = 0x20000000;


pub open spec fn field_model(raw: Seq<u8>) -> bool {
    raw.len() >= 160 && bytes::le16(raw, 128) >= 32
        && bytes::le16(raw, 128) <= raw.len() - 128
}
pub open spec fn decoded(raw: Seq<u8>, feature: bool) -> Option<u32> {
    if raw.len() < 128 { None }
    else if !feature || raw.len() == 128 { Some(0) }
    else if raw.len() < 132 { None }
    else if bytes::le16(raw, 128) > raw.len() - 128 || bytes::le16(raw, 128) % 4 != 0 { None }
    else if !field_model(raw) { Some(0) }
    else { Some(bytes::le32(raw, PROJECT_ID_OFFSET as int) as u32) }
}
pub open spec fn inherit_model(raw: Seq<u8>, feature: bool) -> Option<bool> {
    if raw.len() < 128 { None }
    else { Some(feature && (bytes::le32(raw, 32) as u32) & PROJECT_INHERIT != 0) }
}
pub open spec fn image(raw: Seq<u8>, feature: bool, project: u32) -> Option<Seq<u8>> {
    match decoded(raw, feature) {
        None => None,
        Some(old) => if old == project { Some(raw) }
            else if !feature || !field_model(raw) { None }
            else { Some(bytes::splice(raw, PROJECT_ID_OFFSET as int, bytes::encoded_le(project))) },
    }
}

pub fn field_present(raw: &[u8]) -> (r: bool) ensures r == field_model(raw@) {
    if raw.len() < 160 { return false; }
    let extra = match bytes::read_le16(raw, 128) { Some(v) => v, None => { return false; } };
    extra >= 32 && extra as usize <= raw.len() - 128
}

/// Linux defaults an absent project field to project zero, including old
/// 128-byte inodes. An unavailable feature does not interpret trailing bytes.
pub fn decode(raw: &[u8], project_feature: bool) -> (r: Option<u32>)
    ensures r == decoded(raw@, project_feature),
{
    if raw.len() < 128 { return None; }
    if !project_feature || raw.len() == 128 { return Some(0); }
    if raw.len() < 132 { return None; }
    let extra = bytes::read_le16(raw, 128).unwrap() as usize;
    if extra > raw.len() - 128 || extra % 4 != 0 { return None; }
    if !field_present(raw) { return Some(0); }
    bytes::read_le32(raw, PROJECT_ID_OFFSET)
}

pub fn inherits(raw: &[u8], project_feature: bool) -> (r: Option<bool>)
    ensures r == inherit_model(raw@, project_feature),
{
    if raw.len() < 128 { return None; }
    let flags = bytes::read_le32(raw, 32).unwrap();
    Some(project_feature && flags & PROJECT_INHERIT != 0)
}

pub struct Child { pub project: u32, pub inherit: bool }

pub fn child(parent: &[u8], project_feature: bool, directory: bool) -> (r: Option<Child>)
    ensures match r {
        Some(c) => inherit_model(parent@, project_feature).is_some()
            && c.inherit == (inherit_model(parent@, project_feature).unwrap() && directory)
            && if inherit_model(parent@, project_feature).unwrap() {
                decoded(parent@, project_feature) == Some(c.project)
            } else { c.project == 0 },
        None => inherit_model(parent@, project_feature).is_none()
            || (inherit_model(parent@, project_feature) == Some(true) && decoded(parent@, project_feature).is_none()),
    },
{
    let inherited = match inherits(parent, project_feature) { Some(v) => v, None => { return None; } };
    let project = if inherited {
        match decode(parent, project_feature) { Some(v) => v, None => { return None; } }
    } else { 0 };
    Some(Child { project, inherit: inherited && directory })
}

/// LINK/RENAME into a project-inheriting directory require equal project IDs.
/// Parent directory identity and permissions are separate checked inputs.
pub fn namespace_compatible(directory_project: u32, directory_inherit: bool, inode_project: u32) -> (r: bool)
    ensures r == (!directory_inherit || directory_project == inode_project),
{
    !directory_inherit || directory_project == inode_project
}

/// A checksum-neutral field image. Callers must recalculate the actual inode
/// checksum and atomically journal quota ownership transfer before publication.
pub fn encode(raw: &[u8], project_feature: bool, project: u32) -> (r: Option<Vec<u8>>)
    ensures match r {
        Some(result) => image(raw@, project_feature, project) == Some(result@)
            && result.len() == raw.len()
            && decoded(result@, project_feature) == Some(project)
            && forall|i: int| 0 <= i < raw.len()
                && (i < PROJECT_ID_OFFSET || i >= PROJECT_ID_OFFSET + 4)
                ==> result@[i] == raw@[i],
        None => image(raw@, project_feature, project).is_none(),
    },
{
    let old = match decode(raw, project_feature) { Some(v) => v, None => { return None; } };
    if old != project && (!project_feature || !field_present(raw)) { return None; }
    let mut result = Vec::<u8>::new(); let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len(), result.len() == i, result@ == raw@.subrange(0, i as int),
        decreases raw.len() - i,
    { result.push(raw[i]); i += 1; }
    if old != project {
        let field = bytes::encode_le32(project);
        i = 0;
        while i < 4
            invariant i <= 4, result.len() == raw.len(), raw.len() >= 160,
                field@ == bytes::encoded_le(project),
                result@ == bytes::splice(raw@, PROJECT_ID_OFFSET as int,
                    bytes::encoded_le(project).subrange(0, i as int)),
            decreases 4 - i,
        {
            result[PROJECT_ID_OFFSET + i] = field[i];
            proof {
                assert(result@ =~= bytes::splice(raw@, PROJECT_ID_OFFSET as int,
                    bytes::encoded_le(project).subrange(0, i as int + 1)));
            }
            i += 1;
        }
    }
    proof {
        if old != project {
            bytes::splice_word_frame(raw@, PROJECT_ID_OFFSET as int, bytes::encoded_le(project), 128);
            assert(bytes::le16(result@, 128) == bytes::le16(raw@, 128));
            assert forall|j: int| 0 <= j < raw.len()
                && (j < PROJECT_ID_OFFSET || j >= PROJECT_ID_OFFSET + 4)
                implies result@[j] == raw@[j] by {
                bytes::splice_frame(raw@, PROJECT_ID_OFFSET as int, bytes::encoded_le(project), j);
            }
        }
    }
    Some(result)
}

/// The ioctl/VFS adapter must establish owner-or-capable and quota-inode
/// classification from trusted handles. Booleans here describe that policy;
/// they are not forge-resistant mount or credential capabilities.
pub fn change_allowed(current: u32, requested: u32, project_feature: bool,
    field_available: bool, quota_inode: bool, owner_or_capable: bool) -> (r: bool)
    ensures r == (owner_or_capable && (current == requested
        || (!quota_inode && project_feature && field_available))),
{
    if !owner_or_capable { return false; }
    if current == requested { return true; }
    !quota_inode && project_feature && field_available
}

}
