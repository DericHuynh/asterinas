// SPDX-License-Identifier: MPL-2.0

//! Complete canonical record coverage for a linear checksummed directory block.
//! Deleted records remain in the certificate, so no byte span or live record
//! can be silently omitted. Namespace/target validation is a separate layer.

use vstd::prelude::*;
use crate::{bytes, crc, directory::{self, Entry}};

verus! {

pub open spec fn tail(raw: Seq<u8>, seed: u32) -> bool {
    raw.len() == 4096 && bytes::le32(raw, 4084) == 0 && bytes::le16(raw, 4088) == 12
        && raw[4090] == 0 && raw[4091] == 0xde && bytes::le32(raw, 4092) == crc::fold(seed, raw.subrange(0, 4084)) as nat
}

pub open spec fn record(raw: Seq<u8>, inodes: u32, e: Entry) -> bool {
    &&& 8 <= e.name_offset <= 4084
    &&& directory::accepted(raw, e.name_offset as int - 8, inodes)
    &&& e.inode as nat == bytes::le32(raw, e.name_offset as int - 8)
    &&& e.next as nat == e.name_offset as nat - 8 + bytes::le16(raw, e.name_offset as int - 4)
    &&& e.name_length == raw[e.name_offset as int - 2] && e.file_type == raw[e.name_offset as int - 1]
}

#[verifier::opaque]
pub open spec fn chain(raw: Seq<u8>, inodes: u32, records: Seq<Entry>, end: nat) -> bool {
    &&& raw.len() == 4096 && end <= 4084
    &&& end == if records.len() == 0 { 0nat } else { records.last().next as nat }
    &&& forall|i: int| 0 <= i < records.len() ==> #[trigger] record(raw, inodes, records[i])
        && records[i].name_offset as nat == 8 + if i == 0 { 0nat } else { records[i - 1].next as nat }
}

proof fn append_record(raw: Seq<u8>, inodes: u32, records: Seq<Entry>, end: nat, next: Entry)
    requires chain(raw, inodes, records, end), record(raw, inodes, next), next.name_offset as nat == end + 8,
    ensures chain(raw, inodes, records.push(next), next.next as nat),
{
    reveal(chain);
    assert forall|i: int| 0 <= i < records.len() + 1 implies #[trigger] record(raw, inodes, records.push(next)[i])
        && records.push(next)[i].name_offset as nat == 8 + if i == 0 { 0nat } else { records.push(next)[i - 1].next as nat } by {
        if i < records.len() {
            assert(record(raw, inodes, records[i]));
            assert(records.push(next)[i] == records[i]);
            if i > 0 { assert(records.push(next)[i - 1] == records[i - 1]); }
        } else {
            assert(i == records.len() && records.push(next)[i] == next);
            if i > 0 { assert(records.push(next)[i - 1] == records.last()); }
        }
    }
}

proof fn common_records_agree(raw: Seq<u8>, inodes: u32, a: Seq<Entry>, b: Seq<Entry>, a_end: nat, b_end: nat, count: nat)
    requires chain(raw, inodes, a, a_end), chain(raw, inodes, b, b_end), count <= a.len(), count <= b.len(),
    ensures forall|i: int| 0 <= i < count ==> #[trigger] a[i] == b[i],
    decreases count,
{
    reveal(chain);
    if count > 0 {
        common_records_agree(raw, inodes, a, b, a_end, b_end, (count - 1) as nat);
        let i = count as int - 1;
        assert(record(raw, inodes, a[i]) && record(raw, inodes, b[i]));
        if i > 0 { assert(a[i - 1] == b[i - 1]); }
        assert(a[i].name_offset == b[i].name_offset);
        assert(a[i] == b[i]);
        assert forall|j: int| 0 <= j < count implies #[trigger] a[j] == b[j] by { }
    }
}

pub proof fn complete_record_coverage_is_unique(raw: Seq<u8>, inodes: u32, a: Seq<Entry>, b: Seq<Entry>)
    requires chain(raw, inodes, a, 4084), chain(raw, inodes, b, 4084),
    ensures a == b,
{
    reveal(chain);
    let count = if a.len() < b.len() { a.len() } else { b.len() };
    common_records_agree(raw, inodes, a, b, 4084, 4084, count);
    if a.len() < b.len() {
        assert(a.len() > 0);
        assert(a.last() == b[a.len() as int - 1]);
        assert(record(raw, inodes, b[a.len() as int]));
    }
    if b.len() < a.len() {
        assert(b.len() > 0);
        assert(b.last() == a[b.len() as int - 1]);
        assert(record(raw, inodes, a[b.len() as int]));
    }
    assert(a =~= b);
}

pub open spec fn canonical_records(raw: Seq<u8>, inodes: u32) -> Seq<Entry> {
    if exists|records: Seq<Entry>| #[trigger] chain(raw, inodes, records, 4084) {
        choose|records: Seq<Entry>| #[trigger] chain(raw, inodes, records, 4084)
    } else { Seq::empty() }
}

pub struct BlockView { pub raw: Seq<u8>, pub records: Seq<Entry>, pub inodes: u32, pub seed: u32 }

#[verifier::opaque]
pub open spec fn valid(v: BlockView) -> bool {
    &&& tail(v.raw, v.seed) && chain(v.raw, v.inodes, v.records, 4084)
    &&& 0 < v.records.len() <= 510
}

pub proof fn checked_block_has_canonical_records(v: BlockView)
    requires valid(v),
    ensures v.records == canonical_records(v.raw, v.inodes),
{
    reveal(valid);
    assert(exists|records: Seq<Entry>| #[trigger] chain(v.raw, v.inodes, records, 4084));
    complete_record_coverage_is_unique(v.raw, v.inodes, v.records, canonical_records(v.raw, v.inodes));
}

pub struct DirectoryBlock<'a> { raw: &'a [u8], records: Vec<Entry>, inodes: u32, seed: u32 }

impl<'a> DirectoryBlock<'a> {
    pub closed spec fn view(&self) -> BlockView {
        BlockView { raw: self.raw@, records: self.records@, inodes: self.inodes, seed: self.seed }
    }
    pub open spec fn wf(&self) -> bool { valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn len(&self) -> (r: usize) ensures self.wf(), r == self.view().records.len(), 0 < r <= 510 {
        proof { use_type_invariant(self); reveal(valid); }
        self.records.len()
    }

    pub fn get(&self, index: usize) -> (r: Option<&Entry>)
        ensures self.wf(), match r {
            Some(e) => index < self.view().records.len() && *e == self.view().records[index as int] && record(self.view().raw, self.view().inodes, *e),
            None => index >= self.view().records.len(),
        },
    {
        proof { use_type_invariant(self); reveal(valid); reveal(chain); }
        if index >= self.records.len() { None } else { Some(&self.records[index]) }
    }

    pub fn name(&self, index: usize) -> (r: Option<&'a [u8]>)
        ensures self.wf(), match r {
            Some(name) => index < self.view().records.len() && name@ == self.view().raw.subrange(
                self.view().records[index as int].name_offset as int,
                self.view().records[index as int].name_offset as int + self.view().records[index as int].name_length as int),
            None => index >= self.view().records.len(),
        },
    {
        let entry = match self.get(index) { Some(entry) => entry, None => { return None; } };
        Some(&self.raw[entry.name_offset..entry.name_offset + entry.name_length as usize])
    }
}

pub fn parse(raw: &[u8], inodes: u32, seed: u32) -> (r: Option<DirectoryBlock<'_>>)
    ensures match r { Some(block) => block.wf() && block.view().raw == raw@ && block.view().inodes == inodes && block.view().seed == seed, None => true },
{
    if !directory::valid_tail(raw, seed) { return None; }
    let mut records = Vec::<Entry>::new();
    let mut offset = 0usize;
    assert(chain(raw@, inodes, records@, 0)) by { reveal(chain); }
    while offset < 4084
        invariant raw.len() == 4096, tail(raw@, seed), offset <= 4084,
            chain(raw@, inodes, records@, offset as nat), records.len() * 8 <= offset,
        decreases 4084 - offset,
    {
        let entry = match directory::parse(raw, offset, inodes) { Some(entry) => entry, None => { return None; } };
        let next = entry.next;
        assert(record(raw@, inodes, entry));
        proof { append_record(raw@, inodes, records@, offset as nat, entry); }
        records.push(entry);
        offset = next;
    }
    let ghost assembled = BlockView { raw: raw@, records: records@, inodes, seed };
    assert(valid(assembled)) by { reveal(valid); reveal(chain); }
    Some(DirectoryBlock { raw, records, inodes, seed })
}

}
