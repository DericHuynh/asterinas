// SPDX-License-Identifier: MPL-2.0

//! Linux INLINE_DATA storage: sixty inode bytes plus the in-inode system.data
//! value. Edits retain existing capacity; allocation-backed conversion and
//! operation/journal authority are supplied by higher layers.

use vstd::prelude::*;
use crate::{bytes, inode_payload, xattr, xattr_hash, xattr_entry, xattr_table::{self, TableView, ValueRef}};

verus! {

pub struct InlineView {
    pub raw: Seq<u8>, pub tail: usize, pub tail_bytes: usize, pub entry: usize,
    pub size: usize, pub mode: u16, pub ea: bool, pub inodes: u32, pub block_bytes: u32,
    pub table: TableView, pub key: usize, pub exclusive: bool,
}
pub open spec fn independent_entry(t: TableView, key: int, index: int) -> bool {
    index == key || t.entries[index].value_inode != 0 || t.entries[index].value_size == 0
        || t.entries[key].value_size == 0
        || t.entries[index].value_offset as nat+t.entries[index].value_size <= t.entries[key].value_offset
        || t.entries[key].value_offset as nat+t.entries[key].value_size <= t.entries[index].value_offset
}
pub open spec fn exclusive_tail(t: TableView, key: usize) -> bool {
    forall|i: int| 0 <= i < t.entries.len() ==> #[trigger] independent_entry(t,key as int,i)
}
#[verifier::opaque]
pub open spec fn valid(v: InlineView) -> bool {
    &&& inode_payload::size_accepted(v.raw.len(), v.block_bytes) && v.raw.len() >= 132
    &&& inode_payload::extra_present(v.raw)
    &&& v.mode == 0x8000 || v.mode == 0x4000
    &&& v.mode == bytes::le16(v.raw, 0) as u16 & 0xf000
    &&& bytes::le32(v.raw, 32) as u32 & 0x10000000 != 0
        && bytes::le32(v.raw, 32) as u32 & 0x80000 == 0
    &&& xattr::valid_body(xattr::BodyView { raw: v.raw, table: Some(v.table), ea: v.ea, inodes: v.inodes })
    &&& v.key < v.table.entries.len() && v.table.raw == v.raw
    &&& v.exclusive == exclusive_tail(v.table,v.key)
    &&& v.table.entries[v.key as int].namespace == 7
        && xattr_entry::name(v.raw, v.table.entries[v.key as int]) == seq![100u8, 97u8, 116u8, 97u8]
    &&& v.table.entries[v.key as int].value_inode == 0
        && v.tail == v.table.entries[v.key as int].value_offset
        && v.tail_bytes == v.table.entries[v.key as int].value_size
        && v.entry == v.table.entries[v.key as int].position
    &&& v.tail as nat + v.tail_bytes <= v.raw.len() && 132 <= v.entry && v.entry as nat + 16 <= v.raw.len()
    &&& v.tail_bytes > 0 ==> v.tail >= 132 && v.entry as nat + 16 <= v.tail
    &&& v.size <= 60 + v.tail_bytes && (v.mode == 0x4000 ==> v.size == 60 + v.tail_bytes)
    &&& v.size as nat == bytes::le32(v.raw, 4)
        + if v.mode == 0x8000 { 4294967296 * bytes::le32(v.raw, 108) } else { 0nat }
}
spec fn bounded(v: InlineView) -> bool {
    &&& inode_payload::size_accepted(v.raw.len(), v.block_bytes) && v.raw.len() >= 132
    &&& v.tail as nat + v.tail_bytes <= v.raw.len() && 132 <= v.entry && v.entry as nat + 16 <= v.raw.len()
    &&& v.tail_bytes > 0 ==> v.tail >= 132 && v.entry as nat + 16 <= v.tail
    &&& v.size <= 60 + v.tail_bytes
}
proof fn storage_bounds(v: InlineView)
    requires valid(v),
    ensures bounded(v),
{ reveal(valid); }
proof fn entry_shape(t: TableView, key: int)
    requires xattr_table::valid(t), 0 <= key < t.entries.len(),
    ensures xattr_entry::record(t.raw,t.base,t.ea,t.inodes,t.entries[key]),
        t.entries[key].position == if key == 0 { t.first } else { t.entries[key-1].next },
        t.entries[key].position as nat+16 <= t.entries[key].next,
{
    reveal(xattr_table::valid); reveal(xattr_table::chain);
    assert(xattr_entry::record(t.raw,t.base,t.ea,t.inodes,t.entries[key]));
    assert(t.entries[key].position == if key == 0 { t.first } else { t.entries[key-1].next });
    reveal(xattr_entry::record);
}
proof fn entry_before_end(t: TableView, key: int)
    requires xattr_table::valid(t), 0 <= key < t.entries.len(),
    ensures t.entries[key].position as nat + 16 <= t.end, t.entries[key].next <= t.end,
    decreases t.entries.len()-key,
{
    reveal(xattr_table::valid); reveal(xattr_table::chain);
    entry_shape(t,key);
    if key+1 < t.entries.len() {
        entry_shape(t,key+1);
        entry_before_end(t,key+1);
    } else {
        assert(key == t.entries.len()-1);
        assert(t.entries[key].next == t.end);
    }
}
proof fn entry_after_first(t: TableView, key: int)
    requires xattr_table::valid(t), 0 <= key < t.entries.len(),
    ensures t.first <= t.entries[key].position,
    decreases key,
{
    entry_shape(t,key);
    if key > 0 {
        entry_after_first(t,key-1);
        entry_shape(t,key-1);
    }
}
proof fn entry_order(t: TableView, left: int, right: int)
    requires xattr_table::valid(t), 0 <= left < right < t.entries.len(),
    ensures t.entries[left].next <= t.entries[right].position,
    decreases right-left,
{
    entry_shape(t,right);
    if left+1 < right {
        entry_order(t,left,right-1);
        entry_shape(t,right-1);
    }
}
pub open spec fn other_attributes_preserved(v: InlineView, after: Seq<u8>) -> bool {
    &&& after.len()==v.raw.len()
    &&& forall|i: int| 0 <= i < v.table.entries.len() && i != v.key ==> {
        let e=(#[trigger] v.table.entries[i]);
        &&& after.subrange(e.position as int,e.next as int)==v.raw.subrange(e.position as int,e.next as int)
        &&& e.value_inode==0 ==> after.subrange(e.value_offset as int,e.value_offset as int+e.value_size as int)
            ==v.raw.subrange(e.value_offset as int,e.value_offset as int+e.value_size as int)
    }
}
pub open spec fn position(v: InlineView, index: int) -> int {
    if index < 60 { 40 + index } else { v.tail as int + index - 60 }
}
pub open spec fn payload(v: InlineView) -> Seq<u8> {
    Seq::new(60 + v.tail_bytes as nat, |i: int| v.raw[position(v, i)])
}
pub open spec fn clipped(size: usize, offset: usize, length: usize) -> nat {
    if offset >= size { 0 } else if length < size - offset { length as nat } else { (size-offset) as nat }
}
pub open spec fn edited_payload(v: InlineView, offset: usize, data: Seq<u8>, new_size: usize) -> Seq<u8> {
    Seq::new(60 + v.tail_bytes as nat, |i: int| if offset <= i < offset + data.len() {
        data[i - offset as int]
    } else if i < v.size && i < new_size { payload(v)[i] } else { 0u8 })
}
pub open spec fn write_field(v: InlineView, i: int) -> bool {
    4 <= i < 8 || 108 <= i < 112 || i == 124 || i == 125
        || inode_payload::extra(v.raw) >= 4 && (i == 130 || i == 131)
        || 40 <= i < 100 || v.tail <= i < v.tail as nat + v.tail_bytes
        || v.entry as nat + 12 <= i < v.entry as nat + 16
}

proof fn field_splice(v: InlineView, before: Seq<u8>, at: usize, value: u32)
    requires bounded(v), before.len() == v.raw.len(),
        at == 4 || at == 108 || at as nat == v.entry as nat+12,
    ensures
        forall|j: int| 0 <= j < 60+v.tail_bytes ==> #[trigger] bytes::splice(before, at as int, bytes::encoded_le(value))[position(v,j)] == before[position(v,j)],
        forall|j: int| 0 <= j < before.len() && !write_field(v,j)
            ==> #[trigger] bytes::splice(before, at as int, bytes::encoded_le(value))[j] == before[j],
{
    assert forall|j: int| 0 <= j < 60+v.tail_bytes implies
        #[trigger] bytes::splice(before, at as int, bytes::encoded_le(value))[position(v,j)] == before[position(v,j)] by {
        bytes::splice_frame(before, at as int, bytes::encoded_le(value), position(v,j));
    }
    assert forall|j: int| 0 <= j < before.len() && !write_field(v,j) implies
        #[trigger] bytes::splice(before, at as int, bytes::encoded_le(value))[j] == before[j] by {
        bytes::splice_frame(before, at as int, bytes::encoded_le(value), j);
    }
}

proof fn attribute_bounds(v: InlineView, index: int)
    requires valid(v), 0 <= index < v.table.entries.len(),
    ensures v.table.entries[index].position as nat+16 <= v.table.entries[index].next,
        v.table.entries[index].next <= v.raw.len(),
        v.table.entries[index].value_inode==0 ==>
            v.table.entries[index].value_offset as nat+v.table.entries[index].value_size <= v.raw.len(),
{
    reveal(valid); reveal(xattr_table::valid); reveal(xattr_table::chain);
    entry_shape(v.table,index); entry_before_end(v.table,index);
    if v.table.entries[index].value_inode==0 {
        xattr_entry::decoded_values_cannot_escape_their_container(v.table.raw,v.table.base,v.table.ea,v.table.inodes,v.table.entries[index]);
    }
}
proof fn other_header_avoids_edit(v: InlineView, index: int, at: int)
    requires valid(v), 0 <= index < v.table.entries.len(), index != v.key,
        v.table.entries[index].position <= at < v.table.entries[index].next,
    ensures !write_field(v,at), 0 <= at < v.raw.len(),
{
    reveal(valid); reveal(xattr_table::valid); reveal(xattr_table::chain);
    attribute_bounds(v,index);
    entry_after_first(v.table,index); entry_before_end(v.table,index);
    entry_before_end(v.table,v.key as int); entry_shape(v.table,v.key as int);
    if index < v.key { entry_order(v.table,index,v.key as int); }
    else { entry_order(v.table,v.key as int,index); }
    if v.tail_bytes > 0 {
        xattr_table::every_local_value_is_disjoint_from_all_entry_and_terminator_bytes(v.table,v.key as int);
    }
}
proof fn other_value_avoids_edit(v: InlineView, index: int, at: int)
    requires valid(v), v.exclusive, 0 <= index < v.table.entries.len(), index != v.key,
        v.table.entries[index].value_inode==0, v.table.entries[index].value_size>0,
        v.table.entries[index].value_offset <= at < v.table.entries[index].value_offset as nat+v.table.entries[index].value_size,
    ensures !write_field(v,at), 0 <= at < v.raw.len(),
{
    reveal(valid); reveal(xattr_table::valid); reveal(xattr_table::chain);
    attribute_bounds(v,index);
    xattr_table::every_local_value_is_disjoint_from_all_entry_and_terminator_bytes(v.table,index);
    entry_after_first(v.table,v.key as int); entry_before_end(v.table,v.key as int);
    assert(independent_entry(v.table,v.key as int,index));
}
pub struct Inline<'a> {
    raw: &'a [u8], tail: usize, tail_bytes: usize, entry: usize,
    size: usize, mode: u16, ea: bool, inodes: u32, block_bytes: u32,
    certificate: Ghost<(TableView, usize)>, exclusive: bool,
}

pub fn parse<'a>(raw: &'a [u8], block_bytes: u32, ea: bool, inodes: u32)
    -> (r: Option<Inline<'a>>)
    ensures match r { Some(inline) => inline.wf() && inline.view().raw == raw@
        && inline.view().block_bytes == block_bytes && inline.view().ea == ea && inline.view().inodes == inodes,
        None => true },
{
    if !inode_payload::valid_size(raw.len(), block_bytes) || raw.len() < 132
        || inode_payload::extra_size(raw).is_none() { return None; }
    let mode = bytes::read_le16(raw, 0).unwrap() & 0xf000;
    if mode != 0x8000 && mode != 0x4000 { return None; }
    let flags = bytes::read_le32(raw, 32).unwrap();
    if flags & 0x10000000 == 0 || flags & 0x80000 != 0 { return None; }
    let body = xattr::parse_body(raw, ea, inodes)?;
    let table = body.entry_table()?;
    let key_name = [100u8, 97u8, 116u8, 97u8];
    let key = table.find(7, &key_name)?;
    let e = table.metadata(key)?;
    if e.value_inode != 0 { return None; }
    match table.value(key)? {
        ValueRef::Inode { .. } => { return None; },
        ValueRef::Bytes(_) => {},
    }
    let tail = e.value_offset;
    let tail_bytes = e.value_size as usize;
    if tail > raw.len() || tail_bytes > raw.len() - tail { return None; }
    let capacity = 60usize + tail_bytes;
    let low = bytes::read_le32(raw, 4).unwrap() as u64;
    let high = if mode == 0x8000 { bytes::read_le32(raw, 108).unwrap() as u64 } else { 0 };
    let size = low + high * 4294967296;
    if size > capacity as u64 || mode == 0x4000 && size != capacity as u64 { return None; }
    proof { assert(table.view().raw==raw@); }
    let mut exclusive=true;
    let mut index=0usize;
    let count=table.len();
    while index<count
        invariant table.wf(), count==table.view().entries.len(), index<=count,
            key<count, table.view().raw==raw@, tail==table.view().entries[key as int].value_offset,
            tail_bytes==table.view().entries[key as int].value_size,
            tail as nat+tail_bytes<=raw.len(),
            exclusive == (forall|j: int| 0 <= j < index ==> #[trigger] independent_entry(table.view(),key as int,j)),
        decreases count-index,
    {
        let other=table.metadata(index)?;
        let mut independent=true;
        if index!=key && other.value_inode==0 && other.value_size>0 && tail_bytes>0 {
            proof {
                entry_shape(table.view(),index as int);
                xattr_entry::decoded_values_cannot_escape_their_container(table.view().raw,table.view().base,table.view().ea,table.view().inodes,other);
            }
            let end=other.value_offset+other.value_size as usize;
            independent=end<=tail || tail+tail_bytes<=other.value_offset;
        }
        proof {
            assert(independent == independent_entry(table.view(),key as int,index as int));
            assert((forall|j: int| 0 <= j < index+1 ==> #[trigger] independent_entry(table.view(),key as int,j))
                == ((forall|j: int| 0 <= j < index ==> #[trigger] independent_entry(table.view(),key as int,j))
                    && independent_entry(table.view(),key as int,index as int))) by {
                if forall|j: int| 0 <= j < index ==> #[trigger] independent_entry(table.view(),key as int,j) {
                    if independent_entry(table.view(),key as int,index as int) {
                        assert forall|j: int| 0 <= j < index+1 implies #[trigger] independent_entry(table.view(),key as int,j) by {
                            if j < index { assert(independent_entry(table.view(),key as int,j)); }
                        }
                    }
                }
            }
        }
        exclusive=exclusive && independent;
        index+=1;
    }
    proof {
        reveal(xattr_table::valid); reveal(xattr_table::chain); reveal(xattr_entry::record);
        xattr_entry::decoded_values_cannot_escape_their_container(raw@, table.view().base, ea, inodes, e);
        xattr_entry::decoded_entry_has_a_bounded_name(raw@, table.view().base, ea, inodes, e);
        entry_before_end(table.view(), key as int);
        entry_after_first(table.view(), key as int);
        assert(e.position >= 132);
        assert(table.view().raw == raw@);
        assert(xattr::valid_body(xattr::BodyView { raw: raw@, table: Some(table.view()), ea, inodes }));
        assert(e.position as nat+16 <= table.view().end);
        if tail_bytes > 0 {
            xattr_table::every_local_value_is_disjoint_from_all_entry_and_terminator_bytes(table.view(), key as int);
            assert(tail >= 132 && e.position as nat+16 <= tail);
        }
        reveal(valid);
        let v = InlineView { raw: raw@, tail, tail_bytes, entry: e.position, size: size as usize,
            mode, ea, inodes, block_bytes, table: table.view(), key, exclusive };
        assert(inode_payload::size_accepted(v.raw.len(),v.block_bytes) && v.raw.len()>=132);
        assert(inode_payload::extra_present(v.raw));
        assert(v.mode==0x8000 || v.mode==0x4000);
        assert(v.mode == bytes::le16(v.raw,0) as u16 & 0xf000);
        assert(bytes::le32(v.raw,32) as u32 & 0x10000000 != 0 && bytes::le32(v.raw,32) as u32 & 0x80000 == 0);
        assert(xattr::valid_body(xattr::BodyView {raw:v.raw,table:Some(v.table),ea:v.ea,inodes:v.inodes}));
        assert(v.key<v.table.entries.len() && v.table.raw==v.raw);
        assert(v.table.entries[v.key as int].namespace==7);
        assert(xattr_entry::name(v.raw,v.table.entries[v.key as int]) == seq![100u8,97u8,116u8,97u8]);
        assert(v.table.entries[v.key as int].value_inode==0);
        assert(v.tail==v.table.entries[v.key as int].value_offset && v.tail_bytes==v.table.entries[v.key as int].value_size && v.entry==v.table.entries[v.key as int].position);
        assert(v.tail as nat+v.tail_bytes<=v.raw.len() && 132<=v.entry && v.entry as nat+16<=v.raw.len());
        assert(v.tail_bytes>0 ==> v.tail>=132 && v.entry as nat+16<=v.tail);
        assert(v.size<=60+v.tail_bytes && (v.mode==0x4000 ==> v.size==60+v.tail_bytes));
        assert(v.size as nat == bytes::le32(v.raw,4) + if v.mode==0x8000 {4294967296*bytes::le32(v.raw,108)}else{0nat});
        assert(valid(v));
    }
    Some(Inline { raw, tail, tail_bytes, entry: e.position, size: size as usize,
        mode, ea, inodes, block_bytes, certificate: Ghost((table.view(), key)), exclusive })
}

impl<'a> Inline<'a> {
    pub closed spec fn view(&self) -> InlineView {
        InlineView { raw: self.raw@, tail: self.tail, tail_bytes: self.tail_bytes, entry: self.entry,
            size: self.size, mode: self.mode, ea: self.ea, inodes: self.inodes, block_bytes: self.block_bytes,
            table: self.certificate@.0, key: self.certificate@.1, exclusive: self.exclusive }
    }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn capacity(&self) -> (r: usize) ensures r == 60 + self.view().tail_bytes { proof { use_type_invariant(self); storage_bounds(self.view()); } 60 + self.tail_bytes }
    pub fn length(&self) -> (r: usize) ensures r == self.view().size { self.size }
    pub fn inline_mode(&self) -> (r: u16) ensures r == self.view().mode { self.mode }
    pub fn source_inode(&self) -> (r: &'a [u8]) ensures r@ == self.view().raw { self.raw }

    pub fn read(&self, offset: usize, length: usize) -> (r: Option<Vec<u8>>)
        ensures match r { Some(data) => self.view().mode == 0x8000 && length <= 65536
            && data.len() == clipped(self.view().size, offset, length)
            && data@ == if offset >= self.view().size { Seq::<u8>::empty() }
                else { payload(self.view()).subrange(offset as int, offset as int + data.len()) },
            None => self.view().mode != 0x8000 || length > 65536 },
    {
        proof { use_type_invariant(self); storage_bounds(self.view()); }
        if self.mode != 0x8000 || length > 65536 { return None; }
        let count = if offset >= self.size { 0 } else {
            if length < self.size - offset { length } else { self.size - offset }
        };
        let mut result = Vec::<u8>::new();
        let mut i = 0usize;
        while i < count
            invariant bounded(self.view()), i <= count, count == clipped(self.size, offset, length),
                result.len() == i, count > 0 ==> offset < self.size && offset as nat + count <= self.size,
                forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == payload(self.view())[offset as int+j],
            decreases count - i,
        {
            let at = offset + i;
            result.push(if at < 60 { self.raw[40 + at] } else { self.raw[self.tail + at - 60] });
            i += 1;
        }
        proof {
            if offset >= self.size { assert(result@ =~= Seq::<u8>::empty()); }
            else { assert(result@ =~= payload(self.view()).subrange(offset as int, offset as int + result.len())); }
        }
        Some(result)
    }

    /// Encode an existing-capacity file write/truncate, zeroing gaps and bytes
    /// outside new EOF. Other xattr entries and inode metadata are preserved.
    pub fn write_regular(&self, offset: usize, data: &[u8], new_size: usize,
        number: u32, metadata_seed: u32) -> (r: Option<Vec<u8>>)
        ensures match r { Some(raw) => raw.len() == self.view().raw.len()
            && inode_payload::checksum_matches(raw@, number, metadata_seed)
            && other_attributes_preserved(self.view(),raw@)
            && (forall|i: int| 0 <= i < 60 + self.view().tail_bytes
                ==> #[trigger] raw@[position(self.view(), i)] == edited_payload(self.view(), offset, data@, new_size)[i])
            && (forall|i: int| 0 <= i < raw.len() && !write_field(self.view(), i)
                ==> #[trigger] raw@[i] == self.view().raw[i]),
            None => true },
    {
        proof { use_type_invariant(self); storage_bounds(self.view()); }
        let capacity = self.capacity();
        if self.mode != 0x8000 || !self.exclusive || new_size > capacity || offset > new_size
            || data.len() > new_size - offset { return None; }
        let mut result = Vec::<u8>::new();
        let mut i = 0usize;
        while i < self.raw.len()
            invariant i <= self.raw.len(), result@ == self.raw@.subrange(0, i as int),
            decreases self.raw.len() - i,
        { result.push(self.raw[i]); i += 1; }
        proof { assert(result@ =~= self.raw@); }
        let retained = if self.size < new_size { self.size } else { new_size };
        i = 0;
        while i < capacity
            invariant bounded(self.view()), i <= capacity == 60 + self.tail_bytes, result.len() == self.raw.len(),
                new_size <= capacity, offset <= new_size, data.len() <= new_size-offset,
                retained == if self.size < new_size { self.size } else { new_size },
                (forall|j: int| 0 <= j < i ==> #[trigger] result@[position(self.view(), j)]
                    == edited_payload(self.view(), offset, data@, new_size)[j]),
                (forall|j: int| 0 <= j < self.raw.len()
                    && !(40 <= j < 40 + i && j < 100)
                    && !(i > 60 && self.tail <= j < self.tail as int + i as int - 60)
                    ==> #[trigger] result@[j] == self.raw@[j]),
            decreases capacity - i,
        {
            let at = if i < 60 { 40 + i } else { self.tail + i - 60 };
            let value = if i >= offset && i - offset < data.len() {
                data[i - offset]
            } else if i < retained {
                if i < 60 { self.raw[40 + i] } else { self.raw[self.tail + i - 60] }
            } else { 0 };
            result.set(at, value);
            i += 1;
        }
        let ghost payload_bytes = result@;
        if !put32(&mut result, 4, new_size as u32) { return None; }
        proof { field_splice(self.view(), payload_bytes, 4, new_size as u32); }
        let ghost low_size_bytes = result@;
        if !put32(&mut result, 108, 0) { return None; }
        proof { field_splice(self.view(), low_size_bytes, 108, 0); }
        if bytes::read_le32(self.raw, self.entry + 12)? != 0 {
            let value = &result[self.tail..self.tail + self.tail_bytes];
            let hash = xattr_hash::entry_hash(b"data", value)?;
            let ghost before_hash = result@;
            if !put32(&mut result, self.entry + 12, hash) { return None; }
            proof { field_splice(self.view(), before_hash, (self.entry+12) as usize, hash); }
        }
        let sealed = inode_payload::seal(result.as_slice(), number, metadata_seed)?;
        proof {
            assert forall|j: int| 0 <= j < 60+self.tail_bytes implies
                #[trigger] sealed@[position(self.view(), j)] == edited_payload(self.view(), offset, data@, new_size)[j] by {
                let at = position(self.view(), j);
                assert(at != 124 && at != 125 && at != 130 && at != 131);
                assert(sealed@[at] == result@[at]);
            }
            assert forall|j: int| 0 <= j < sealed.len() && !write_field(self.view(), j)
                implies #[trigger] sealed@[j] == self.raw@[j] by {
                assert(result@[128] == self.raw@[128] && result@[129] == self.raw@[129]);
                assert(inode_payload::extra(result@) == inode_payload::extra(self.raw@));
                assert(j != 124 && j != 125 && !(inode_payload::extra(result@) >= 4 && (j == 130 || j == 131)));
                assert(sealed@[j] == result@[j]);
            }
        }
        proof {
            assert forall|entry_index: int| 0 <= entry_index < self.view().table.entries.len() && entry_index != self.view().key implies {
                let e=(#[trigger] self.view().table.entries[entry_index]);
                &&& sealed@.subrange(e.position as int,e.next as int)==self.raw@.subrange(e.position as int,e.next as int)
                &&& e.value_inode==0 ==> sealed@.subrange(e.value_offset as int,e.value_offset as int+e.value_size as int)
                    ==self.raw@.subrange(e.value_offset as int,e.value_offset as int+e.value_size as int)
            } by {
                let e=self.view().table.entries[entry_index];
                attribute_bounds(self.view(),entry_index);
                assert forall|at: int| e.position <= at < e.next implies #[trigger] sealed@[at]==self.raw@[at] by {
                    other_header_avoids_edit(self.view(),entry_index,at);
                }
                assert(sealed@.subrange(e.position as int,e.next as int) =~= self.raw@.subrange(e.position as int,e.next as int));
                if e.value_inode==0 && e.value_size>0 {
                    assert forall|at: int| e.value_offset <= at < e.value_offset as nat+e.value_size implies #[trigger] sealed@[at]==self.raw@[at] by {
                        other_value_avoids_edit(self.view(),entry_index,at);
                    }
                }
                if e.value_inode==0 {
                    assert(sealed@.subrange(e.value_offset as int,e.value_offset as int+e.value_size as int)
                        =~= self.raw@.subrange(e.value_offset as int,e.value_offset as int+e.value_size as int));
                }
            }
        }
        let checked = parse(sealed.as_slice(), self.block_bytes, self.ea, self.inodes)?;
        if checked.length() != new_size { return None; }
        Some(sealed)
    }

    /// Linux stores only a parent inode number for dotdot. Dot and dotdot are
    /// synthesized; real dirents occupy two independently bounded regions.
    pub fn directory_entries(&self, number: u32, inodes: u32) -> (r: Option<Vec<Entry>>)
        ensures match r { Some(entries) => 2 <= entries.len() <= 8192
            && entries@[0].target == number && entries@[0].name@ == seq![46u8]
            && entries@[1].name@ == seq![46u8, 46u8],
            None => true },
    {
        proof { use_type_invariant(self); storage_bounds(self.view()); }
        if self.mode != 0x4000 || number == 0 || number > inodes { return None; }
        let parent = bytes::read_le32(self.raw, 40)?;
        if parent == 0 || parent > inodes { return None; }
        let mut entries = Vec::<Entry>::new();
        let mut dot = Vec::<u8>::new(); dot.push(46);
        let mut dotdot = Vec::<u8>::new(); dotdot.push(46); dotdot.push(46);
        entries.push(Entry { target: number, file_type: 2, name: dot });
        entries.push(Entry { target: parent, file_type: 2, name: dotdot });
        if !collect_region(&self.raw[44..100], inodes, &mut entries) { return None; }
        if self.tail_bytes > 0
            && !collect_region(&self.raw[self.tail..self.tail + self.tail_bytes], inodes, &mut entries) {
            return None;
        }
        Some(entries)
    }
}

pub struct Entry { pub target: u32, pub file_type: u8, pub name: Vec<u8> }

fn collect_region(raw: &[u8], inodes: u32, entries: &mut Vec<Entry>) -> (r: bool)
    requires old(entries).len() <= 8192,
    ensures final(entries).len() <= 8192, final(entries).len() >= old(entries).len(),
        forall|i: int| 0 <= i < old(entries).len() ==> #[trigger] final(entries)@[i] == old(entries)@[i],
{
    let mut at = 0usize;
    while at < raw.len()
        invariant at <= raw.len(), old(entries).len() <= entries.len() <= 8192,
            forall|i: int| 0 <= i < old(entries).len() ==> #[trigger] entries@[i] == old(entries)@[i],
        decreases raw.len() - at,
    {
        if raw.len() - at < 8 { return false; }
        let number = bytes::read_le32(raw, at).unwrap();
        let length = bytes::read_le16(raw, at + 4).unwrap() as usize;
        let names = raw[at + 6] as usize;
        let file_type = raw[at + 7];
        if length < 8 || length % 4 != 0 || length > raw.len() - at
            || names > length - 8 || file_type > 7 || number > inodes { return false; }
        if number != 0 {
            if names == 0 || entries.len() >= 8192 { return false; }
            let name = &raw[at + 8..at + 8 + names];
            let mut i = 0usize;
            while i < names
                invariant i <= names == name.len(), old(entries).len() <= entries.len() <= 8192,
                    forall|k: int| 0 <= k < old(entries).len() ==> #[trigger] entries@[k] == old(entries)@[k],
                decreases names-i,
            {
                if name[i] == 0 || name[i] == 47 { return false; }
                i += 1;
            }
            i = 0;
            while i < entries.len()
                invariant i <= entries.len(), old(entries).len() <= entries.len() <= 8192,
                    forall|k: int| 0 <= k < old(entries).len() ==> #[trigger] entries@[k] == old(entries)@[k],
                decreases entries.len()-i,
            {
                if bytes::equal(entries[i].name.as_slice(), name) { return false; }
                i += 1;
            }
            let mut owned = Vec::<u8>::new();
            i = 0;
            while i < names
                invariant i <= names == name.len(), owned@ == name@.subrange(0, i as int),
                decreases names-i,
            { owned.push(name[i]); i += 1; }
            entries.push(Entry { target: number, file_type, name: owned });
        }
        at += length;
    }
    true
}

fn put32(raw: &mut Vec<u8>, at: usize, value: u32) -> (r: bool)
    ensures final(raw).len() == old(raw).len(),
        r == (at as int + 4 <= old(raw).len()),
        final(raw)@ == if r { bytes::splice(old(raw)@, at as int, bytes::encoded_le(value)) } else { old(raw)@ },
{
    bytes::write_le32(raw.as_mut_slice(), at, value)
}

}
