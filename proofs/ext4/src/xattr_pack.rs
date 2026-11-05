// SPDX-License-Identifier: MPL-2.0

//! Rebuild bounded Linux inode-body/external xattr tables from owned values.
//! A complete decode and full-byte comparison validate every returned image.
//! Packing conveys neither allocation ownership nor credential authority.

use vstd::prelude::*;
use crate::{bytes, xattr::{self, BodyView}, xattr_entry, xattr_hash,
    xattr_store::{self as store, Store, Item, ItemView}, xattr_table::TableView};

verus! {

pub struct PackedView { pub original: Seq<u8>, pub inode: BodyView, pub external: Option<TableView>, pub items: Seq<ItemView>, pub physical: u64, pub seed: u32, pub inodes: u32 }
pub open spec fn items(v: PackedView) -> Seq<ItemView> {
    (match v.inode.table { Some(table) => store::table_items(table), None => Seq::empty() })
        + (match v.external { Some(table) => store::table_items(table), None => Seq::empty() })
}
#[verifier::opaque]
pub open spec fn valid(v: PackedView) -> bool {
    &&& v.original.len() == 256 && v.inode.raw.subrange(0, 160) == v.original.subrange(0, 160)
    &&& xattr::valid_body(v.inode) && v.inode.raw.len() == 256 && bytes::le16(v.inode.raw, 128) == 32
    &&& (match v.inode.table { Some(table) => crate::xattr_canonical::canonical(table, false), None => true })
    &&& !v.inode.ea && v.inode.inodes == v.inodes && store::valid(v.items) && store::valid(items(v)) && store::same_contents(items(v), v.items)
    &&& match v.external { Some(table) => crate::xattr_table::valid(table) && table.raw.len() == 4096 && table.first == 32 && table.base == 0
        && table.sorted && !table.ea && table.inodes == v.inodes && crate::xattr_canonical::canonical(table, true) && v.physical > 0
        && xattr::header(table.raw, v.physical, v.seed, true) && bytes::le32(table.raw, 4) == 1,
        None => v.physical == 0 }
}
pub struct Packed { inode: Vec<u8>, external: Option<Vec<u8>>, checked: Ghost<PackedView> }
impl Packed {
    pub closed spec fn view(&self) -> PackedView { self.checked@ }
    pub closed spec fn wf(&self) -> bool { valid(self.view()) && self.inode@ == self.view().inode.raw
        && match &self.external { Some(raw) => self.view().external is Some && raw@ == self.view().external.unwrap().raw, None => self.view().external is None } }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn into_parts(self) -> (r: (Vec<u8>, Option<Vec<u8>>))
        ensures self.wf(), r.0@ == self.view().inode.raw,
            match r.1 { Some(raw) => self.view().external is Some && raw@ == self.view().external.unwrap().raw, None => self.view().external is None },
    { proof { use_type_invariant(&self); } (self.inode, self.external) }
    pub fn has_external(&self) -> (r: bool) ensures self.wf(), r == self.view().external.is_some() {
        proof { use_type_invariant(self); } self.external.is_some()
    }
}

fn cost(item: &Item) -> (r: Option<usize>) ensures match r { Some(n) => 16 <= n <= 65808, None => true } {
    let (_, name) = item.key(); let value = item.bytes();
    if name.len() > 255 || value.len() > 65536 { return None; }
    Some(16 + (name.len() + 3) / 4 * 4 + (value.len() + 3) / 4 * 4)
}

// Exact bounded subset-sum placement: maximize the 88-byte body payload,
// leaving the remaining records for the 4060-byte external payload.
fn inline_mask(values: &Store) -> (r: Option<Vec<bool>>)
    ensures values.wf(), match r { Some(mask) => mask.len() == values.view().len(), None => true },
{
    let n = values.len();
    let mut rows: Vec<Vec<bool>> = Vec::new();
    let mut initial = Vec::new(); let mut k = 0usize;
    while k < 23 invariant k <= 23, initial.len() == k, decreases 23 - k,
    { initial.push(k == 0); k += 1; }
    rows.push(initial);
    let mut i = 0usize;
    while i < n
        invariant values.wf(), n == values.view().len(), n <= 260, i <= n, rows.len() == i + 1,
            forall|j: int| 0 <= j < rows.len() ==> (#[trigger] rows@[j]).len() == 23,
        decreases n - i,
    {
        let weight = match cost(values.item(i).unwrap()) { Some(weight) => weight / 4, None => { return None; } };
        let mut row = Vec::new(); let mut k = 0usize;
        while k < 23
            invariant k <= 23, row.len() == k, rows.len() == i + 1, rows@[i as int].len() == 23,
            decreases 23 - k,
        { row.push(rows[i][k] || weight <= k && rows[i][k - weight]); k += 1; }
        rows.push(row); i += 1;
    }
    let mut best = 22usize;
    while best > 0 && !rows[n][best]
        invariant best <= 22, rows.len() == n + 1, rows@[n as int].len() == 23,
        decreases best,
    { best -= 1; }
    let mut mask = Vec::new(); let mut i = 0usize;
    while i < n invariant i <= n <= 260, mask.len() == i, decreases n - i,
    { mask.push(false); i += 1; }
    let mut i = n;
    while i > 0
        invariant values.wf(), n == values.view().len(), n <= 260, i <= n, mask.len() == n,
            best <= 22, rows.len() == n + 1, forall|j: int| 0 <= j < rows.len() ==> (#[trigger] rows@[j]).len() == 23,
        decreases i,
    {
        i -= 1;
        let weight = match cost(values.item(i).unwrap()) { Some(weight) => weight / 4, None => { return None; } };
        if weight <= best && rows[i][best - weight] { mask.set(i, true); best -= weight; }
    }
    Some(mask)
}

fn less(a: &Item, b: &Item) -> bool {
    let (an, ak) = a.key(); let (bn, bk) = b.key();
    if an != bn { return an < bn; }
    if ak.len() != bk.len() { return ak.len() < bk.len(); }
    let mut i = 0usize;
    while i < ak.len()
        invariant i <= ak.len() == bk.len(), decreases ak.len() - i,
    { if ak[i] != bk[i] { return ak[i] < bk[i]; } i += 1; }
    false
}
fn order(values: &Store) -> (r: Vec<usize>)
    ensures values.wf(), r.len() == values.view().len(), forall|i: int| 0 <= i < r.len() ==> #[trigger] r@[i] < values.view().len(),
{
    let n = values.len(); let mut result: Vec<usize> = Vec::new(); let mut i = 0usize;
    while i < n
        invariant n == values.view().len(), n <= 260, i <= n, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result@[j] < n,
        decreases n - i,
    { result.push(i); i += 1; }
    let mut i = 0usize;
    while i < n
        invariant values.wf(), n == values.view().len(), n <= 260, i <= n, result.len() == n,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result@[j] < n,
        decreases n - i,
    {
        let mut minimum = i; let mut j = i + 1;
        while j < n
            invariant values.wf(), n == values.view().len(), n <= 260, i <= minimum < n, i < j <= n, result.len() == n,
                forall|k: int| 0 <= k < result.len() ==> #[trigger] result@[k] < n,
            decreases n - j,
        { if less(values.item(result[j]).unwrap(), values.item(result[minimum]).unwrap()) { minimum = j; } j += 1; }
        let a = result[i]; let b = result[minimum]; result.set(i, b); result.set(minimum, a); i += 1;
    }
    result
}
fn copy_inode(raw: &[u8]) -> (r: Option<Vec<u8>>)
    ensures match r { Some(next) => next.len() == 256 && raw.len() == 256 && next@ == raw@, None => raw.len() != 256 },
{
    if raw.len() != 256 { return None; }
    let mut next = Vec::new(); let mut i = 0usize;
    while i < 256 invariant raw.len() == 256, i <= 256, next@ == raw@.take(i as int), decreases 256 - i,
    { next.push(raw[i]); assert(next@ =~= raw@.take(i as int + 1)); i += 1; }
    Some(next)
}

// These builders are deliberately followed by a complete decoder and exact
// content validation. A returned packing never relies on a hash collision.
fn build(values: &Store, mask: &[bool], indices: &[usize], source: &[u8], body: bool) -> (r: Option<Vec<u8>>)
    ensures values.wf(), match r { Some(raw) => raw.len() == (if body { 256usize } else { 4096usize }), None => true },
{
    let n = values.len();
    if mask.len() != n || indices.len() != n { return None; }
    let mut raw = if body { match copy_inode(source) { Some(raw) => raw, None => { return None; } } } else { bytes::zero_block() };
    if body {
        if bytes::read_le16(&raw, 128).unwrap() != 32 { return None; }
        let mut i = 160usize;
        while i < 256 invariant raw.len() == 256, i <= 256, decreases 256 - i,
        { raw.set(i, 0u8); i += 1; }
        bytes::write_le32(raw.as_mut_slice(), 160, xattr::MAGIC);
    } else {
        bytes::write_le32(raw.as_mut_slice(), 0, xattr::MAGIC);
        bytes::write_le32(raw.as_mut_slice(), 4, 1);
        bytes::write_le32(raw.as_mut_slice(), 8, 1);
    }
    let mut cursor = if body { 164usize } else { 32usize };
    let mut end = raw.len(); let base = if body { 164usize } else { 0usize };
    let mut hashes = Vec::new(); let mut i = 0usize; let mut count = 0usize;
    while i < n
        invariant values.wf(), n == values.view().len(), n <= 260, i <= n, count <= i,
            mask.len() == n, indices.len() == n, raw.len() == (if body { 256usize } else { 4096usize }),
            base == (if body { 164usize } else { 0usize }), cursor <= raw.len(), end <= raw.len(), hashes.len() <= i,
        decreases n - i,
    {
        let index = indices[i]; if index >= n { return None; }
        if mask[index] == body {
            let item = values.item(index).unwrap(); let (namespace, name) = item.key(); let value = item.bytes();
            if name.len() > 255 || value.len() > 65536 { return None; }
            let record = 16 + (name.len() + 3) / 4 * 4; let padded = (value.len() + 3) / 4 * 4;
            if record > raw.len() - cursor || padded > end { return None; }
            let next = cursor + record; let value_start = end - padded;
            if next > value_start || value_start - next < 4 || value_start < base { return None; }
            raw.set(cursor, name.len() as u8); raw.set(cursor + 1, namespace);
            let offset = bytes::encode_le16(if value.len() == 0 { 0u16 } else { (value_start - base) as u16 });
            bytes::write_bytes(raw.as_mut_slice(), cursor + 2, &offset);
            bytes::write_le32(raw.as_mut_slice(), cursor + 8, value.len() as u32);
            if !bytes::write_bytes(raw.as_mut_slice(), cursor + 16, name) { return None; }
            if !bytes::write_bytes(raw.as_mut_slice(), value_start, value) { return None; }
            if !body {
                let hash = xattr_hash::entry_hash(name, value).unwrap();
                bytes::write_le32(raw.as_mut_slice(), cursor + 12, hash); hashes.push(hash);
            }
            cursor = next; end = value_start; count += 1;
        }
        i += 1;
    }
    if body && count == 0 { bytes::write_le32(raw.as_mut_slice(), 160, 0); }
    if !body { let hash = xattr_hash::block_hash(&hashes).unwrap(); bytes::write_le32(raw.as_mut_slice(), 12, hash); }
    Some(raw)
}

pub fn encode(values: &Store, inode: &[u8], physical: u64, seed: u32, inodes: u32) -> (r: Option<Packed>)
    ensures values.wf(), match r { Some(packed) => packed.wf() && packed.view().original == inode@ && packed.view().items == values.view() && packed.view().seed == seed
        && packed.view().inodes == inodes && (packed.view().external is Some ==> packed.view().physical == physical), None => true },
{
    hide(crate::crc::fold);
    let mask = match inline_mask(values) { Some(mask) => mask, None => { return None; } };
    let indices = order(values);
    let mut has_external = false; let mut i = 0usize; let n = values.len();
    while i < n invariant i <= n == values.view().len(), n <= 260, mask.len() == n, decreases n - i,
    { if !mask[i] { has_external = true; } i += 1; }
    if has_external && physical == 0 { return None; }
    let raw_inode = match build(values, &mask, &indices, inode, true) { Some(raw) => raw, None => { return None; } };
    if inode.len() != 256 || !bytes::equal(&raw_inode[..160], &inode[..160]) || bytes::read_le16(&raw_inode, 128).unwrap() != 32 { return None; }
    let body = match xattr::parse_body(&raw_inode, false, inodes) { Some(body) => body, None => { return None; } };
    let mut logical = Store::new();
    if let Some(table) = body.entry_table() { if !crate::xattr_canonical::check(table, false) { return None; } logical = match logical.extend_table(table) { Some(next) => next, None => { return None; } }; }
    let mut external = None;
    let ghost mut external_view: Option<TableView> = None;
    if has_external {
        let mut raw = match build(values, &mask, &indices, inode, false) { Some(raw) => raw, None => { return None; } };
        let checksum = xattr::checksum(&raw, physical, seed).unwrap(); bytes::write_le32(raw.as_mut_slice(), 16, checksum);
        let table = match xattr::parse_block(&raw, physical, seed, true, false, inodes) { Some(table) => table, None => { return None; } };
        if table.refcount() != 1 || !crate::xattr_canonical::check(table.entries(), true) { return None; }
        logical = match logical.extend_table(table.entries()) { Some(next) => next, None => { return None; } };
        proof { external_view = Some(table.view()); }
        external = Some(raw);
    }
    if !logical.equivalent(values) { return None; }
    let ghost view = PackedView { original: inode@, inode: body.view(), external: external_view, items: values.view(), physical: if has_external { physical } else { 0u64 }, seed, inodes };
    assert(xattr::valid_body(view.inode));
    assert(view.original.len() == 256 && view.inode.raw.subrange(0, 160) == view.original.subrange(0, 160));
    assert(store::valid(view.items));
    assert(logical.view() == items(view));
    assert(store::valid(items(view)) && store::same_contents(items(view), view.items));
    assert(match view.external { Some(table) => crate::xattr_table::valid(table) && table.raw.len() == 4096 && table.first == 32 && table.base == 0
        && table.sorted && !table.ea && table.inodes == view.inodes && view.physical > 0
        && xattr::header(table.raw, view.physical, view.seed, true) && bytes::le32(table.raw, 4) == 1, None => view.physical == 0 });
    assert(valid(view)) by { reveal(valid); }
    Some(Packed { inode: raw_inode, external, checked: Ghost(view) })
}

pub proof fn repacking_retains_every_complete_key_and_value(v: PackedView, namespace: u8, name: Seq<u8>)
    requires valid(v),
    ensures store::get(items(v), namespace, name) == store::get(v.items, namespace, name),
{
    reveal(valid);
    store::equivalent_stores_have_identical_full_key_lookup(items(v), v.items, namespace, name);
}

}
