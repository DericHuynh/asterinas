// SPDX-License-Identifier: MPL-2.0

//! Bounded directory/name uniqueness without a hash-identity assumption.
//! Full byte equality decides duplicates. Bucket/total limits bound hostile
//! collision work; owned names cannot change after insertion. This is an
//! admission helper, not a namespace or access capability.

use vstd::prelude::*;
use crate::{bytes, crc, directory};

verus! {

pub const BUCKETS: usize = 4096;
pub const MAX_BUCKET: usize = 64;
pub const MAX_KEYS: u32 = 65536;

pub type KeyView = (u32, Seq<u8>);
struct Key { directory: u32, name: Vec<u8>, ordinal: u32 }

impl Key {
    closed spec fn view(&self) -> KeyView { (self.directory, self.name@) }
}

spec fn keys_view(keys: Seq<Key>) -> Seq<KeyView> { Seq::new(keys.len(), |i: int| keys[i].view()) }
spec fn buckets_view(buckets: Seq<Vec<Key>>) -> Seq<Seq<KeyView>> {
    Seq::new(buckets.len(), |i: int| keys_view(buckets[i]@))
}

#[verifier::opaque]
spec fn indexed_buckets(buckets: Seq<Vec<Key>>, keys: Seq<KeyView>) -> bool {
    forall|b: int, i: int| 0 <= b < buckets.len() && 0 <= i < buckets[b]@.len() ==>
        (#[trigger] buckets[b]@[i]).ordinal < keys.len() && keys[buckets[b]@[i].ordinal as int] == buckets[b]@[i].view()
}

#[verifier::opaque]
pub open spec fn valid_key(key: KeyView) -> bool {
    key.0 > 0 && 0 < key.1.len() <= 255 && directory::name_ok(key.1, 0, key.1.len())
}

#[verifier::opaque]
pub open spec fn bucket(key: KeyView) -> nat { (crc::fold(key.0, key.1) % 4096) as nat }

proof fn bucket_is_in_range(key: KeyView) ensures bucket(key) < BUCKETS { reveal(bucket); }

#[verifier::opaque]
pub open spec fn bucket_ok(keys: Seq<KeyView>, index: int) -> bool {
    &&& keys.len() <= MAX_BUCKET && keys.no_duplicates()
    &&& forall|i: int| 0 <= i < keys.len() ==> #[trigger] valid_key(keys[i])
    &&& forall|i: int| 0 <= i < keys.len() ==> #[trigger] bucket(keys[i]) == index
}

pub struct SetView { pub buckets: Seq<Seq<KeyView>>, pub keys: Seq<KeyView>, pub total: u32 }

#[verifier::opaque]
pub open spec fn valid(v: SetView) -> bool {
    &&& v.buckets.len() == BUCKETS && v.total as nat == v.keys.len() && v.total <= MAX_KEYS
    &&& v.keys.no_duplicates()
    &&& forall|b: int| 0 <= b < BUCKETS ==> #[trigger] bucket_ok(v.buckets[b], b)
    &&& forall|key: KeyView| #[trigger] v.keys.contains(key) <==> (bucket(key) < v.buckets.len() && v.buckets[bucket(key) as int].contains(key))
}

proof fn recorded_keys_are_valid(v: SetView, key: KeyView)
    requires valid(v), v.keys.contains(key),
    ensures valid_key(key),
{
    reveal(valid);
    bucket_is_in_range(key);
    assert(bucket_ok(v.buckets[bucket(key) as int], bucket(key) as int));
    reveal(bucket_ok);
    let i = choose|i: int| 0 <= i < v.buckets[bucket(key) as int].len() && v.buckets[bucket(key) as int][i] == key;
    assert(valid_key(v.buckets[bucket(key) as int][i]));
}

proof fn a_valid_name_byte(raw: Seq<u8>, count: nat, index: int)
    requires directory::name_ok(raw, 0, count), 0 <= index < count <= raw.len(),
    ensures raw[index] != 0, raw[index] != 47,
{
    reveal(directory::name_ok);
    assert(raw[0 + index] != 0 && raw[0 + index] != 47);
}

proof fn a_checked_bucket_entry(keys: Seq<KeyView>, bucket_index: int, index: int)
    requires bucket_ok(keys, bucket_index), 0 <= index < keys.len(),
    ensures valid_key(keys[index]), bucket(keys[index]) == bucket_index,
{
    reveal(bucket_ok);
}

fn check_key(directory: u32, name: &[u8]) -> (r: bool) ensures r == valid_key((directory, name@)) {
    reveal(valid_key);
    reveal(directory::name_ok);
    if directory == 0 || name.len() == 0 || name.len() > 255 { return false; }
    let mut i = 0usize;
    while i < name.len()
        invariant name.len() <= 255, i <= name.len(), directory::name_ok(name@, 0, i as nat),
        decreases name.len() - i,
    {
        if name[i] == 0 || name[i] == 47 {
            assert(!valid_key((directory, name@))) by {
                reveal(valid_key);
                if valid_key((directory, name@)) { a_valid_name_byte(name@, name.len() as nat, i as int); }
            }
            return false;
        }
        assert(directory::name_ok(name@, 0, i as nat + 1)) by {
            assert forall|j: int| 0 <= j < i + 1 implies name@[j] != 0 && #[trigger] name@[j] != 47 by {
                if j < i { a_valid_name_byte(name@, i as nat, j); }
            }
        }
        i += 1;
    }
    true
}

fn capture(directory: u32, name: &[u8], ordinal: u32) -> (r: Key)
    requires valid_key((directory, name@)),
    ensures r.view() == (directory, name@), r.ordinal == ordinal,
{
    reveal(valid_key);
    let mut copy = Vec::new();
    let mut i = 0usize;
    while i < name.len()
        invariant i <= name.len() <= 255, copy@ == name@.subrange(0, i as int),
        decreases name.len() - i,
    {
        copy.push(name[i]);
        assert(copy@ =~= name@.subrange(0, i as int + 1));
        i += 1;
    }
    assert(copy@ =~= name@);
    Key { directory, name: copy, ordinal }
}

proof fn inserting_a_new_bucket_key(v: SetView, key: KeyView)
    requires valid(v), v.buckets.len() == BUCKETS, bucket(key) < BUCKETS, valid_key(key), !v.keys.contains(key), v.total < MAX_KEYS,
        v.buckets[bucket(key) as int].len() < MAX_BUCKET,
    ensures valid(SetView { buckets: v.buckets.update(bucket(key) as int, v.buckets[bucket(key) as int].push(key)),
        keys: v.keys.push(key), total: (v.total + 1) as u32 }),
{
    hide(crc::fold);
    reveal(valid);
    reveal(bucket_ok);
    bucket_is_in_range(key);
    let b = bucket(key) as int;
    let updated = v.buckets.update(b, v.buckets[b].push(key));
    assert forall|i: int| 0 <= i < BUCKETS implies #[trigger] bucket_ok(updated[i], i) by {
        assert(bucket_ok(v.buckets[i], i));
        if i == b {
            assert(bucket_ok(v.buckets[b], b));
            assert forall|j: int| 0 <= j < v.buckets[b].len() + 1 implies
                #[trigger] valid_key(updated[b][j]) && bucket(updated[b][j]) == b by {
                if j < v.buckets[b].len() {
                    a_checked_bucket_entry(v.buckets[b], b, j);
                    assert(updated[b][j] == v.buckets[b][j]);
                } else { assert(j == v.buckets[b].len() && updated[b][j] == key); }
            }
        }
    }
    assert forall|k: KeyView| #[trigger] v.keys.push(key).contains(k) <==>
        (bucket(k) < updated.len() && updated[bucket(k) as int].contains(k)) by {
        bucket_is_in_range(k);
        vstd::seq_lib::lemma_seq_contains_after_push(v.keys, key, k);
        assert(v.keys.contains(k) == v.buckets[bucket(k) as int].contains(k));
        if bucket(k) == b {
            assert(updated[bucket(k) as int] == v.buckets[b].push(key));
            vstd::seq_lib::lemma_seq_contains_after_push(v.buckets[b], key, k);
            assert(updated[bucket(k) as int].contains(k) == (v.buckets[b].contains(k) || k == key));
        } else { assert(k != key && updated[bucket(k) as int] == v.buckets[bucket(k) as int]); }
    }
}

pub struct NameSet { buckets: Vec<Vec<Key>>, keys: Ghost<Seq<KeyView>>, total: u32 }

impl NameSet {
    pub closed spec fn view(&self) -> SetView { SetView { buckets: buckets_view(self.buckets@), keys: self.keys@, total: self.total } }
    pub closed spec fn indexed(&self) -> bool { indexed_buckets(self.buckets@, self.keys@) }
    pub open spec fn wf(&self) -> bool { valid(self.view()) && self.indexed() }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn new() -> (r: Self) ensures r.wf(), r.view().keys.len() == 0 {
        hide(crc::fold);
        let mut buckets = Vec::<Vec<Key>>::new();
        let mut i = 0usize;
        while i < BUCKETS
            invariant i <= BUCKETS, buckets.len() == i,
                forall|b: int| 0 <= b < i ==> #[trigger] buckets_view(buckets@)[b].len() == 0,
            decreases BUCKETS - i,
        {
            let ghost previous = buckets@;
            buckets.push(Vec::new());
            assert forall|b: int| 0 <= b < i + 1 implies #[trigger] buckets_view(buckets@)[b].len() == 0 by {
                if b < i {
                    assert(buckets_view(previous)[b].len() == 0);
                    assert(buckets@[b] == previous[b]);
                } else { assert(b == i && buckets@[b]@.len() == 0); }
            }
            i += 1;
        }
        let ghost assembled = SetView { buckets: buckets_view(buckets@), keys: Seq::empty(), total: 0 };
        assert(valid(assembled)) by {
            reveal(valid); reveal(bucket_ok);
            assert forall|k: KeyView| #[trigger] assembled.keys.contains(k) <==> assembled.buckets[bucket(k) as int].contains(k) by { bucket_is_in_range(k); }
        }
        assert(indexed_buckets(buckets@, Seq::empty())) by {
            reveal(indexed_buckets);
            assert forall|b: int, i: int| 0 <= b < buckets.len() && 0 <= i < buckets@[b]@.len() implies
                (#[trigger] buckets@[b]@[i]).ordinal < 0 && Seq::<KeyView>::empty()[buckets@[b]@[i].ordinal as int] == buckets@[b]@[i].view() by {
                assert(buckets_view(buckets@)[b].len() == 0);
                assert(buckets@[b]@.len() == 0);
            }
        }
        NameSet { buckets, keys: Ghost(Seq::empty()), total: 0 }
    }

    pub fn len(&self) -> (r: u32) ensures self.wf(), r == self.view().keys.len(), r <= MAX_KEYS {
        proof { use_type_invariant(self); reveal(valid); }
        self.total
    }

    pub fn find(&self, directory: u32, name: &[u8]) -> (r: Option<u32>)
        ensures self.wf(), match r {
            Some(index) => index < self.view().keys.len() && self.view().keys[index as int] == (directory, name@)
                && self.view().keys.contains((directory, name@)),
            None => !self.view().keys.contains((directory, name@)),
        },
    {
        hide(crc::fold);
        proof { use_type_invariant(self); reveal(valid); }
        if directory == 0 || name.len() == 0 || name.len() > 255 {
            proof { if self.view().keys.contains((directory, name@)) { recorded_keys_are_valid(self.view(), (directory, name@)); reveal(valid_key); } }
            return None;
        }
        let index = (crc::crc32c(directory, name) % 4096) as usize;
        assert(index as nat == bucket((directory, name@))) by { reveal(bucket); }
        let entries = &self.buckets[index];
        let ghost keys = keys_view(entries@);
        assert(keys == self.view().buckets[index as int]);
        assert(bucket_ok(keys, index as int));
        assert(keys.len() <= MAX_BUCKET) by { reveal(bucket_ok); }
        let mut i = 0usize;
        while i < entries.len()
            invariant self.wf(), self.buckets.len() == BUCKETS, index < BUCKETS, entries@ == self.buckets@[index as int]@,
                keys == keys_view(entries@), keys.len() <= MAX_BUCKET,
                index as nat == bucket((directory, name@)), i <= entries.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] keys[j] != (directory, name@),
            decreases entries.len() - i,
        {
            let entry = &entries[i];
            assert(entry.view() == keys[i as int]);
            assert(entry.directory == keys[i as int].0 && entry.name@ == keys[i as int].1);
            let stored = entry.name.as_slice();
            assert(stored@ == entry.name@);
            let equal = bytes::equal(stored, name);
            assert(equal == (entry.name@ == name@));
            if entry.directory == directory && equal {
                assert(keys.contains((directory, name@))) by { assert(keys[i as int] == (directory, name@)); }
                proof { reveal(valid); reveal(indexed_buckets); }
                return Some(entry.ordinal);
            }
            assert(keys[i as int] != (directory, name@));
            assert forall|j: int| 0 <= j < i + 1 implies #[trigger] keys[j] != (directory, name@) by {
                if j < i { assert(keys[j] != (directory, name@)); }
            }
            i += 1;
        }
        assert(!keys.contains((directory, name@)));
        proof { reveal(valid); }
        None
    }

    pub fn contains(&self, directory: u32, name: &[u8]) -> (r: bool)
        ensures self.wf(), r == self.view().keys.contains((directory, name@)),
    {
        self.find(directory, name).is_some()
    }

    pub fn insert(self, directory: u32, name: &[u8]) -> (r: Result<Self, Self>)
        ensures match r {
            Ok(next) => next.wf() && next.view().keys == self.view().keys.push((directory, name@)),
            Err(original) => original.view() == self.view() && (!valid_key((directory, name@)) || self.view().keys.contains((directory, name@))
                || self.view().total == MAX_KEYS || self.view().buckets[bucket((directory, name@)) as int].len() == MAX_BUCKET),
        },
    {
        hide(crc::fold);
        proof { use_type_invariant(&self); reveal(valid); }
        if !check_key(directory, name) || self.contains(directory, name) { return Err(self); }
        let index = (crc::crc32c(directory, name) % 4096) as usize;
        assert(index as nat == bucket((directory, name@))) by { reveal(bucket); }
        assert(bucket_ok(self.view().buckets[index as int], index as int));
        assert(self.view().total <= MAX_KEYS && self.view().buckets[index as int].len() <= MAX_BUCKET) by { reveal(valid); reveal(bucket_ok); }
        if self.total == MAX_KEYS || self.buckets[index].len() == MAX_BUCKET { return Err(self); }
        let key = capture(directory, name, self.total);
        let ghost before = self.view();
        let ghost previous_buckets = self.buckets@;
        assert(indexed_buckets(previous_buckets, before.keys));
        proof { inserting_a_new_bucket_key(before, key.view()); }
        let NameSet { mut buckets, keys, total } = self;
        let mut entries = buckets.remove(index);
        let ghost old_entries = entries@;
        entries.push(key);
        assert(keys_view(entries@) =~= keys_view(old_entries).push((directory, name@)));
        buckets.insert(index, entries);
        assert(buckets_view(buckets@) =~= before.buckets.update(index as int, before.buckets[index as int].push((directory, name@))));
        let ghost next_keys = keys@.push((directory, name@));
        let ghost assembled = SetView { buckets: buckets_view(buckets@), keys: next_keys, total: (total + 1) as u32 };
        assert(valid(assembled));
        assert(indexed_buckets(buckets@, next_keys)) by {
            reveal(indexed_buckets);
            assert forall|b: int, i: int| 0 <= b < buckets.len() && 0 <= i < buckets@[b]@.len() implies
                (#[trigger] buckets@[b]@[i]).ordinal < next_keys.len()
                    && next_keys[buckets@[b]@[i].ordinal as int] == buckets@[b]@[i].view() by {
                if b == index as int && i == old_entries.len() {
                    assert(buckets@[b]@[i].ordinal == total && buckets@[b]@[i].view() == (directory, name@));
                } else {
                    assert(buckets@[b]@[i] == previous_buckets[b]@[i]);
                    assert(previous_buckets[b]@[i].ordinal < before.keys.len());
                    assert(before.keys[previous_buckets[b]@[i].ordinal as int] == previous_buckets[b]@[i].view());
                }
            }
        }
        Ok(NameSet { buckets, keys: Ghost(next_keys), total: total + 1 })
    }
}

}
