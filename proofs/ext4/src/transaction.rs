// SPDX-License-Identifier: MPL-2.0

//! Canonical single-descriptor transaction construction from owned after-images.
//! This encodes a candidate patch; global filesystem authority and the durable
//! write protocol are separate obligations. No writable aliases are exported.

use vstd::prelude::*;
use crate::{bytes, crc, descriptor, frozen::{self, FrozenBlock}, jbd2, layout::{JournalLayout, LayoutView}, replay, super_state};

verus! {

pub struct AfterImage { block: u32, image: FrozenBlock }
#[verifier::ext_equal]
pub struct ImageView { pub block: u32, pub image: Seq<u8> }

impl AfterImage {
    pub closed spec fn view(&self) -> ImageView { ImageView { block: self.block, image: self.image.view() } }

    pub fn capture(block: u32, image: &[u8]) -> (r: Option<Self>)
        ensures match r {
            Some(a) => image.len() == 4096 && a.view() == (ImageView { block, image: image@ }),
            None => image.len() != 4096,
        },
    {
        match FrozenBlock::capture(image) { Some(image) => Some(AfterImage { block, image }), None => None }
    }
}

pub open spec fn images(input: Seq<AfterImage>) -> Seq<ImageView> {
    Seq::new(input.len(), |i: int| input[i].view())
}

pub open spec fn distinct(input: Seq<ImageView>) -> bool {
    forall|i: int, j: int| 0 <= i < j < input.len() ==> (#[trigger] input[i]).block != (#[trigger] input[j]).block
}

pub open spec fn input_ok(input: Seq<ImageView>, uuid: Seq<u8>, sequence: u32, layout: &JournalLayout,
    primary: Seq<u8>, partition_bytes: u64) -> bool {
    &&& layout.wf() && uuid.len() == 16 && 0 < sequence < 4294967295 && 0 < input.len() <= 250
    &&& distinct(input)
    &&& (forall|i: int| 0 <= i < input.len() ==> layout.allowed((#[trigger] input[i]).block)
        && input[i].image.len() == 4096
        && (input[i].block == 0 ==> super_state::replay_ok(primary, input[i].image, partition_bytes)))
}

fn valid_input(input: &[AfterImage], uuid: &[u8], sequence: u32, layout: &JournalLayout,
    primary: &[u8], partition_bytes: u64) -> (r: bool)
    ensures r == input_ok(images(input@), uuid@, sequence, layout, primary@, partition_bytes),
{
    if !layout.valid() || uuid.len() != 16 || sequence == 0 || sequence == 4294967295
        || input.len() == 0 || input.len() > 250 { return false; }
    let mut i = 0usize;
    while i < input.len()
        invariant i <= input.len() <= 250,
            forall|j: int| 0 <= j < i ==> layout.allowed((#[trigger] input@[j].view()).block)
                && input@[j].view().image.len() == 4096
                && (input@[j].view().block == 0 ==> super_state::replay_ok(primary@, input@[j].view().image, partition_bytes)),
            forall|p: int, q: int| 0 <= p < q < i ==> (#[trigger] input@[p].view()).block != (#[trigger] input@[q].view()).block,
        decreases input.len() - i,
    {
        let a = &input[i];
        if !layout.allows_target(a.block) || a.image.as_slice().len() != 4096
            || (a.block == 0 && !super_state::valid_replay(primary, a.image.as_slice(), partition_bytes)) {
            proof {
                if input_ok(images(input@), uuid@, sequence, layout, primary@, partition_bytes) {
                    assert(layout.allowed(images(input@)[i as int].block)
                        && images(input@)[i as int].image.len() == 4096
                        && (images(input@)[i as int].block == 0 ==>
                            super_state::replay_ok(primary@, images(input@)[i as int].image, partition_bytes)));
                }
            }
            return false;
        }
        let mut j = 0usize;
        while j < i
            invariant j <= i < input.len(),
                a.view() == input@[i as int].view(),
                forall|k: int| 0 <= k < j ==> (#[trigger] input@[k].view()).block != input@[i as int].view().block,
            decreases i - j,
        {
            if input[j].block == a.block {
                proof {
                    if distinct(images(input@)) {
                        assert(images(input@)[j as int].block != images(input@)[i as int].block);
                    }
                }
                return false;
            }
            proof {
                assert forall|k: int| 0 <= k < j + 1 implies (#[trigger] input@[k].view()).block != input@[i as int].view().block by {
                    if k < j { assert(input@[k].view().block != input@[i as int].view().block); }
                }
            }
            j += 1;
        }
        proof {
            assert forall|p: int, q: int| 0 <= p < q < i + 1 implies
                (#[trigger] input@[p].view()).block != (#[trigger] input@[q].view()).block by {
                if q == i { assert(input@[p].view().block != input@[i as int].view().block); }
            }
        }
        i += 1;
    }
    true
}

pub struct TransactionView {
    pub original: Seq<ImageView>, pub payloads: Seq<Seq<u8>>, pub tags: Seq<jbd2::Tag>,
    pub descriptor: Seq<u8>, pub commit: Seq<u8>, pub sequence: u32, pub layout: LayoutView,
    pub uuid: Seq<u8>, pub seed: u32, pub primary: Seq<u8>, pub partition_bytes: u64,
}

pub open spec fn wf(tx: TransactionView) -> bool {
    &&& tx.layout.start > 1 && 1024 <= tx.layout.journal_blocks <= 32768
        && tx.layout.start as int + tx.layout.journal_blocks <= tx.layout.fs_blocks
    &&& 0 < tx.sequence < 4294967295 && tx.uuid.len() == 16 && tx.seed == crc::fold(0xffffffff, tx.uuid)
    &&& 0 < tx.original.len() <= 250 && tx.original.len() == tx.payloads.len() == tx.tags.len()
    &&& distinct(tx.original)
    &&& descriptor::base(tx.descriptor, tx.uuid, tx.sequence, tx.seed)
    &&& descriptor::candidate(tx.descriptor, tx.tags.len(), tx.layout.fs_blocks)
    &&& descriptor::represents(tx.descriptor, tx.tags)
    &&& jbd2::commit_ok(tx.commit, tx.sequence, tx.seed)
    &&& (forall|i: int| 0 <= i < tx.tags.len() ==> (#[trigger] tx.tags[i]).block == tx.original[i].block
        && replay::payload_for_layout(tx.tags[i], tx.payloads[i], tx.sequence, tx.seed, tx.layout)
        && replay::restored(tx.payloads[i], tx.tags[i].flags % 2 == 1) == tx.original[i].image
        && (tx.original[i].block == 0 ==> super_state::replay_ok(tx.primary, tx.original[i].image, tx.partition_bytes)))
}

pub struct Encoded {
    original: Vec<AfterImage>, payloads: Vec<FrozenBlock>, tags: Vec<jbd2::Tag>,
    descriptor: FrozenBlock, commit: FrozenBlock, sequence: u32, layout: Ghost<LayoutView>,
    uuid: Ghost<Seq<u8>>, seed: u32, primary: Ghost<Seq<u8>>, partition_bytes: u64,
}

impl Encoded {
    pub closed spec fn view(&self) -> TransactionView {
        TransactionView { original: images(self.original@),
            payloads: Seq::new(self.payloads@.len(), |i: int| self.payloads@[i].view()), tags: self.tags@,
            descriptor: self.descriptor.view(), commit: self.commit.view(), sequence: self.sequence,
            layout: self.layout@, uuid: self.uuid@, seed: self.seed, primary: self.primary@, partition_bytes: self.partition_bytes }
    }

    #[verifier::type_invariant]
    spec fn valid(self) -> bool { wf(self.view()) }

    pub fn payload_count(&self) -> (r: usize) ensures r == self.view().payloads.len() { self.payloads.len() }
    pub fn transaction_id(&self) -> (r: u32) ensures r == self.view().sequence { self.sequence }
    pub fn descriptor_bytes(&self) -> (r: &[u8]) ensures r@ == self.view().descriptor { self.descriptor.as_slice() }
    pub fn commit_bytes(&self) -> (r: &[u8]) ensures r@ == self.view().commit { self.commit.as_slice() }

    pub fn payload_at(&self, index: usize) -> (r: Option<&[u8]>)
        ensures match r { Some(b) => index < self.view().payloads.len() && b@ == self.view().payloads[index as int],
            None => index >= self.view().payloads.len() },
    { if index >= self.payloads.len() { None } else { Some(self.payloads[index].as_slice()) } }

    pub fn original_at(&self, index: usize) -> (r: Option<(u32, &[u8])>)
        ensures match r { Some((block, b)) => index < self.view().original.len()
                && block == self.view().original[index as int].block && b@ == self.view().original[index as int].image,
            None => index >= self.view().original.len() },
    {
        if index >= self.original.len() { None }
        else { Some((self.original[index].block, self.original[index].image.as_slice())) }
    }
}

pub fn encode(input: Vec<AfterImage>, uuid: &[u8], sequence: u32, layout: &JournalLayout,
    primary: &[u8], partition_bytes: u64) -> (r: Option<Encoded>)
    ensures match r {
        Some(tx) => input_ok(images(input@), uuid@, sequence, layout, primary@, partition_bytes)
            && wf(tx.view()) && tx.view().original == images(input@) && tx.view().uuid == uuid@
            && tx.view().sequence == sequence && tx.view().layout == layout.view()
            && tx.view().primary == primary@ && tx.view().partition_bytes == partition_bytes,
        None => !input_ok(images(input@), uuid@, sequence, layout, primary@, partition_bytes),
    },
{
    if !valid_input(input.as_slice(), uuid, sequence, layout, primary, partition_bytes) { return None; }
    let seed = crc::crc32c(0xffffffff, uuid);
    let mut payloads: Vec<FrozenBlock> = Vec::new();
    let mut tags: Vec<jbd2::Tag> = Vec::new();
    let mut i = 0usize;
    while i < input.len()
        invariant i <= input.len(), payloads.len() == i, tags.len() == i,
            input_ok(images(input@), uuid@, sequence, layout, primary@, partition_bytes), seed == crc::fold(0xffffffff, uuid@),
            forall|j: int| 0 <= j < i ==> (#[trigger] tags@[j]).block == input@[j].view().block
                && descriptor::input_tag(tags@[j], j, input.len() as nat, layout.view().fs_blocks)
                && replay::payload_for_layout(tags@[j], payloads@[j].view(), sequence, seed, layout.view())
                && replay::restored(payloads@[j].view(), tags@[j].flags % 2 == 1) == input@[j].view().image,
        decreases input.len() - i,
    {
        let a = &input[i];
        assert(layout.allowed(images(input@)[i as int].block));
        assert(images(input@)[i as int].image.len() == 4096);
        let (payload, escaped) = a.image.escape().unwrap();
        let flags = (if escaped { 1u32 } else { 0u32 })
            + (if i == 0 { 0u32 } else { 2u32 }) + (if i + 1 == input.len() { 8u32 } else { 0u32 });
        let checksum = jbd2::payload_checksum(seed, sequence, payload.as_slice()).unwrap();
        let tag = jbd2::Tag { block: a.block, flags, checksum };
        proof {
            if escaped { frozen::escape_restore_roundtrip(a.view().image); }
            assert(replay::restored(payload.view(), flags % 2 == 1) == a.view().image);
            assert(replay::payload_for_layout(tag, payload.view(), sequence, seed, layout.view()));
            assert(descriptor::input_tag(tag, i as int, input.len() as nat, layout.view().fs_blocks));
        }
        payloads.push(payload);
        tags.push(tag);
        i += 1;
    }
    assert(descriptor::admissible(tags@, uuid@, sequence, layout.view().fs_blocks));
    let descriptor = descriptor::encode(tags.as_slice(), uuid, sequence, layout.filesystem_blocks(), seed).unwrap();
    let commit = jbd2::encode_commit(sequence, seed).unwrap();
    Some(Encoded { original: input, payloads, tags, descriptor, commit, sequence, layout: Ghost(layout.view()),
        uuid: Ghost(uuid@), seed, primary: Ghost(primary@), partition_bytes })
}

}
