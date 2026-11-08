// SPDX-License-Identifier: MPL-2.0

//! Linux version-2 ACL xattr input to compact ext4 version-1 disk bytes.
//! Numeric IDs are already in the filesystem mapping supplied by the VFS.

use alloc::vec::Vec;

use vstd::prelude::*;
use crate::{acl::{self, Acl, AclView}, bytes};

verus! {

pub open spec fn removing(input: Seq<u8>) -> bool { input.len() == 0 || input.len() == 4 && bytes::le32(input, 0) == 2 }
pub open spec fn entry_matches(input: Seq<u8>, value: AclView, i: int) -> bool {
    let e = value.entries[i]; let offset = 4 + i * 8;
    bytes::le16(input, offset) == e.tag && bytes::le16(input, offset + 2) == e.permissions
        && (e.tag == 2 || e.tag == 8 ==> bytes::le32(input, offset + 4) == e.id)
}
pub open spec fn represents(input: Seq<u8>, value: AclView) -> bool {
    acl::valid(value) && 4 < input.len() <= 65536 && bytes::le32(input, 0) == 2 && input.len() == 4 + 8 * value.entries.len()
        && forall|i: int| 0 <= i < value.entries.len() ==> #[trigger] entry_matches(input, value, i)
}
pub struct Converted { disk: Vec<u8>, input: Ghost<Seq<u8>>, checked: Ghost<AclView> }
impl Converted {
    pub closed spec fn view(&self) -> AclView { self.checked@ }
    pub closed spec fn input(&self) -> Seq<u8> { self.input@ }
    pub closed spec fn wf(&self) -> bool { represents(self.input(), self.view()) && self.disk@ == self.view().raw }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn parsed(&self) -> (r: Option<Acl<'_>>)
        ensures self.wf(), match r { Some(value) => value.wf() && value.view() == self.view(), None => true },
    {
        proof { use_type_invariant(self); }
        let value = match acl::parse(&self.disk) { Some(value) => value, None => { return None; } };
        proof { acl::complete_acls_from_the_same_bytes_have_identical_entries(value.view(), self.view()); }
        Some(value)
    }
    pub fn as_slice(&self) -> (r: &[u8]) ensures self.wf(), r@ == self.view().raw { proof { use_type_invariant(self); } &self.disk }
}
pub fn is_removal(input: &[u8]) -> (r: bool) ensures r == removing(input@) {
    input.len() == 0 || input.len() == 4 && bytes::read_le32(input, 0).unwrap() == 2
}
fn same_entries(input: &[u8], value: &Acl<'_>) -> (r: bool)
    ensures value.wf(), r ==> represents(input@, value.view()),
{
    let n = value.count();
    if input.len() <= 4 || input.len() > 65536 || (input.len() - 4) % 8 != 0 || bytes::read_le32(input, 0).unwrap() != 2 || n != (input.len() - 4) / 8 { return false; }
    let mut i = 0usize;
    while i < n
        invariant value.wf(), n == value.view().entries.len(), i <= n <= 8191,
            input.len() == 4 + n * 8, input.len() <= 65536, bytes::le32(input@, 0) == 2,
            forall|j: int| 0 <= j < i ==> #[trigger] entry_matches(input@, value.view(), j),
        decreases n - i,
    {
        let e = value.entry(i).unwrap(); let offset = 4 + i * 8;
        if bytes::read_le16(input, offset).unwrap() != e.tag || bytes::read_le16(input, offset + 2).unwrap() != e.permissions as u16
            || (e.tag == 2 || e.tag == 8) && bytes::read_le32(input, offset + 4).unwrap() != e.id { return false; }
        assert(entry_matches(input@, value.view(), i as int)); i += 1;
    }
    true
}
pub fn decode(input: &[u8]) -> (r: Option<Converted>)
    ensures match r { Some(value) => value.wf() && value.input() == input@ && represents(input@, value.view()), None => true },
{
    if input.len() <= 4 || input.len() > 65536 || (input.len() - 4) % 8 != 0 || bytes::read_le32(input, 0).unwrap() != 2 { return None; }
    let n = (input.len() - 4) / 8;
    let mut disk = Vec::new(); disk.push(1u8); disk.push(0u8); disk.push(0u8); disk.push(0u8);
    let mut i = 0usize;
    while i < n
        invariant i <= n <= 8191, input.len() == 4 + n * 8, input.len() <= 65536, disk.len() <= 4 + i * 8,
        decreases n - i,
    {
        let offset = 4 + i * 8; let tag = bytes::read_le16(input, offset).unwrap();
        disk.push(input[offset]); disk.push(input[offset + 1]); disk.push(input[offset + 2]); disk.push(input[offset + 3]);
        if tag == 2 || tag == 8 { disk.push(input[offset + 4]); disk.push(input[offset + 5]); disk.push(input[offset + 6]); disk.push(input[offset + 7]); }
        i += 1;
    }
    let value = match acl::parse(&disk) { Some(value) => value, None => { return None; } };
    if !same_entries(input, &value) { return None; }
    let ghost checked = value.view();
    Some(Converted { disk, input: Ghost(input@), checked: Ghost(checked) })
}
pub open spec fn non_equivalent(v: AclView) -> bool {
    exists|i: int| 0 <= i < v.entries.len() && ((#[trigger] v.entries[i]).tag == 2 || v.entries[i].tag == 8 || v.entries[i].tag == 16)
}
pub struct Summary { pub bits: u16, pub extended: bool }
pub fn summarize(value: &Acl<'_>) -> (r: Option<Summary>)
    ensures value.wf(), match r { Some(s) => s.bits <= 0o777 && s.bits == acl::permission_mode(value.view().entries) && s.extended == non_equivalent(value.view()), None => true },
{
    let n = value.count(); let mut i = 0usize; let mut bits = 0u16; let mut extended = false;
    while i < n
        invariant value.wf(), n == value.view().entries.len(), i <= n,
            bits == acl::permission_mode(value.view().entries.take(i as int)),
            extended == (exists|j: int| 0 <= j < i && ((#[trigger] value.view().entries[j]).tag == 2 || value.view().entries[j].tag == 8 || value.view().entries[j].tag == 16)),
        decreases n - i,
    {
        let e = value.entry(i).unwrap();
        if e.tag == 1 { bits = bits | ((e.permissions as u16) << 6); }
        else if e.tag == 4 { bits = bits | ((e.permissions as u16) << 3); }
        else if e.tag == 16 { bits = (bits & !0o70u16) | ((e.permissions as u16) << 3); }
        else if e.tag == 32 { bits = bits | e.permissions as u16; }
        if e.tag == 2 || e.tag == 8 || e.tag == 16 { extended = true; }
        assert(value.view().entries.take(i as int + 1).drop_last() =~= value.view().entries.take(i as int));
        assert(value.view().entries.take(i as int + 1).last() == e);
        i += 1;
    }
    assert(value.view().entries.take(i as int) =~= value.view().entries);
    if bits > 0o777 { return None; }
    Some(Summary { bits, extended })
}
pub proof fn converted_acls_preserve_every_supplied_named_identifier(input: Seq<u8>, value: AclView, i: int)
    requires represents(input, value), 0 <= i < value.entries.len(), value.entries[i].tag == 2 || value.entries[i].tag == 8,
    ensures value.entries[i].id == bytes::le32(input, 8 + i * 8),
{ assert(entry_matches(input, value, i)); }

// Linux's version-2 userspace ABI reports a full eight-byte record for every
// entry. Special tags use INVALID_ID even though their compact disk form has no
// ID word. Numeric named IDs are already in the supplied filesystem mapping;
// mount/user-namespace conversion belongs to the authenticated VFS boundary.
pub open spec fn canonical_report_id(input: Seq<u8>, value: AclView, i: int) -> bool {
    value.entries[i].tag == 2 || value.entries[i].tag == 8 || bytes::le32(input, 8 + i * 8) == 4294967295
}
pub open spec fn reported(input: Seq<u8>, value: AclView) -> bool {
    represents(input, value) && forall|i: int| 0 <= i < value.entries.len() ==> #[trigger] canonical_report_id(input, value, i)
}
fn normalized_report_ids(input: &[u8], value: &Acl<'_>) -> (r: bool)
    ensures value.wf(), r ==> reported(input@, value.view()),
{
    if !same_entries(input, value) { return false; }
    let n = value.count(); let mut i = 0usize;
    while i < n
        invariant value.wf(), represents(input@, value.view()), n == value.view().entries.len(), i <= n <= 8191,
            input.len() == 4 + 8 * n,
            forall|j: int| 0 <= j < i ==> #[trigger] canonical_report_id(input@, value.view(), j),
        decreases n - i,
    {
        let e = value.entry(i).unwrap();
        if e.tag != 2 && e.tag != 8 && bytes::read_le32(input, 8 + i * 8).unwrap() != 4294967295 { return false; }
        assert(canonical_report_id(input@, value.view(), i as int));
        i += 1;
    }
    true
}
pub fn report(value: &Acl<'_>) -> (r: Option<Vec<u8>>)
    ensures value.wf(), match r { Some(input) => reported(input@, value.view()), None => true },
{
    let n = value.count();
    // The admitted xattr value limit is also the ABI output bound. A compact
    // disk ACL may otherwise contain more entries than fit in this profile.
    if n == 0 || n > 8191 { return None; }
    let mut input = Vec::new(); input.push(2u8); input.push(0u8); input.push(0u8); input.push(0u8);
    let mut i = 0usize;
    while i < n
        invariant value.wf(), n == value.view().entries.len(), i <= n <= 8191, input.len() == 4 + 8 * i,
        decreases n - i,
    {
        let e = value.entry(i).unwrap();
        let tag = bytes::encode_le16(e.tag); let permissions = bytes::encode_le16(e.permissions as u16);
        let id = bytes::encode_le32(if e.tag == 2 || e.tag == 8 { e.id } else { 4294967295u32 });
        input.push(tag[0]); input.push(tag[1]); input.push(permissions[0]); input.push(permissions[1]);
        input.push(id[0]); input.push(id[1]); input.push(id[2]); input.push(id[3]);
        i += 1;
    }
    if !normalized_report_ids(&input, value) { return None; }
    Some(input)
}
pub proof fn reported_acls_preserve_named_ids_and_normalize_special_ids(input: Seq<u8>, value: AclView, i: int)
    requires reported(input, value), 0 <= i < value.entries.len(),
    ensures bytes::le16(input, 4 + i * 8) == value.entries[i].tag,
        bytes::le16(input, 6 + i * 8) == value.entries[i].permissions,
        if value.entries[i].tag == 2 || value.entries[i].tag == 8 {
            bytes::le32(input, 8 + i * 8) == value.entries[i].id
        } else { bytes::le32(input, 8 + i * 8) == 4294967295 },
{
    assert(entry_matches(input, value, i));
    assert(canonical_report_id(input, value, i));
}

}
