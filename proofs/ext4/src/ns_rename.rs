// SPDX-License-Identifier: MPL-2.0

//! Bounded same-directory RENAME_NOREPLACE candidate construction. The actual
//! source and complete EA namespace are inspected before editing; concrete
//! after-images are coalesced and re-admitted, with an exact entry and byte
//! frame check. Publication, credentials and durable I/O are separate.

use vstd::prelude::*;
use crate::{bytes, ea_directory, ea_directory_index::{DirectoryIndex},
    ea_namespace::{self, NamespaceView}, feature_policy, inode, namespace_model::EntryView,
    ns_inode_touch, ns_rename_block, patch_set::{self, PatchSet}, snapshot::Snapshot,
    transaction::ImageView};

verus! {

pub const MAX_IMAGE_BYTES: usize = 268435456;

pub enum Error { Invalid, ReadOnly, NotFound, Exists, NoSpace, Rejected }

pub open spec fn certified(c: NamespaceView, source: Seq<u8>) -> bool {
    ea_namespace::valid(c) && c.allocation.integrity.references.index.header.source == source
}
pub open spec fn renamed(before: Seq<EntryView>, after: Seq<EntryView>, entry: usize,
    directory: u32, old_name: Seq<u8>, new_name: Seq<u8>, target: u32, generation: u32) -> bool {
    &&& entry < before.len() == after.len()
    &&& before[entry as int].directory == directory && before[entry as int].name == old_name
    &&& before[entry as int].target == target && before[entry as int].generation == generation
    &&& after[entry as int] == (EntryView { name: new_name, ..before[entry as int] })
    &&& (forall|i: int| 0 <= i < before.len() && i != entry ==> (#[trigger] after[i]) == before[i])
}
pub open spec fn editable(i: int, directory_block: u32, parent_position: u64, target_position: u64) -> bool {
    directory_block as int * 4096 <= i < (directory_block as int + 1) * 4096
        || parent_position <= i < parent_position as int + 256
        || target_position <= i < target_position as int + 256
}
pub open spec fn frame(source: Seq<u8>, result: Seq<u8>, directory_block: u32, parent_position: u64, target_position: u64) -> bool {
    source.len() == result.len()
        && forall|i: int| 0 <= i < source.len() && !editable(i, directory_block, parent_position, target_position)
            ==> #[trigger] result[i] == source[i]
}

pub struct UpdateView {
    pub source: Seq<u8>, pub result: Seq<u8>, pub before: NamespaceView, pub after: NamespaceView,
    pub directory: u32, pub old_name: Seq<u8>, pub new_name: Seq<u8>, pub target: u32, pub generation: u32,
    pub entry: usize, pub selected: EntryView, pub seconds: int, pub nanos: nat, pub patches: Seq<ImageView>, pub directory_block: u32,
    pub parent_position: u64, pub target_position: u64,
    pub parent_node: crate::ea_source::NodeView, pub target_node: crate::ea_source::NodeView, pub directory_view: ea_directory::DirectoryView,
    pub directory_change: ns_rename_block::Change,
    pub parent_change: ns_inode_touch::Change, pub target_change: ns_inode_touch::Change,
}
#[verifier::opaque]
pub open spec fn discovered(v: UpdateView) -> bool {
    &&& certified(v.before, v.source) && 8192 <= v.source.len() <= MAX_IMAGE_BYTES
    &&& !feature_policy::readonly(v.source.subrange(1024, 2048))
    &&& ns_rename_block::proper_name(v.old_name) && ns_rename_block::proper_name(v.new_name)
    &&& !crate::namespace_model::has_name(v.before.index.entries, v.directory, v.new_name)
    &&& v.before.index.entries.contains(v.selected) && v.selected.directory == v.directory
    &&& v.selected.name == v.old_name && v.selected.target == v.target && v.selected.generation == v.generation
    &&& crate::ea_namespace_nodes::active(v.before.index.nodes, v.directory)
    &&& crate::ea_namespace_nodes::active(v.before.index.nodes, v.target)
    &&& v.parent_node == v.before.allocation.ordinary[v.before.index.nodes.slots[v.directory as int].ordinal as int].parent.node
    &&& v.target_node == v.before.allocation.ordinary[v.before.index.nodes.slots[v.target as int].ordinal as int].parent.node
    &&& v.parent_position == v.parent_node.position && v.target_position == v.target_node.position
    &&& v.parent_node.number == v.directory && v.target_node.number == v.target
    &&& v.parent_node.header == v.before.allocation.integrity.references.index.header
    &&& v.target_node.header == v.parent_node.header
    &&& v.generation as nat == bytes::le32(v.target_node.raw, 100)
    &&& ea_directory::valid(v.directory_view) && v.directory_view.volume == v.before.allocation
    &&& v.directory_view.ordinal == v.before.index.nodes.slots[v.directory as int].ordinal
    &&& ea_directory::owner(v.directory_view) == v.directory
    &&& v.selected.logical < v.directory_view.pieces.len()
    &&& v.directory_block == v.directory_view.physical[v.selected.logical as int]
    &&& v.directory_change.before == v.directory_view.pieces[v.selected.logical as int]
    &&& v.directory_change.record == v.selected.record
    &&& ns_rename_block::name(v.directory_change.before, v.directory_change.record as int) == v.old_name
    &&& v.directory_change.before.block.records[v.directory_change.record as int].inode == v.target
    &&& v.directory_change.before.block.records[v.directory_change.record as int].file_type == v.selected.file_type
    &&& v.directory_change.new_name == v.new_name
    &&& v.parent_change.before == v.parent_node.raw && v.target_change.before == v.target_node.raw
    &&& v.parent_change.number == v.directory && v.target_change.number == v.target
    &&& v.parent_change.inodes == v.parent_node.header.inodes && v.target_change.inodes == v.parent_node.header.inodes
    &&& v.parent_change.seed == v.parent_node.header.seed && v.target_change.seed == v.parent_node.header.seed
    &&& v.parent_change.huge == crate::ea_parent::huge(v.parent_node.header) && v.target_change.huge == v.parent_change.huge
    &&& v.parent_change.touch_mtime && !v.target_change.touch_mtime
    &&& v.parent_change.seconds == v.seconds && v.target_change.seconds == v.seconds
    &&& v.parent_change.nanos == v.nanos && v.target_change.nanos == v.nanos
}
#[verifier::opaque]
pub open spec fn planned(v: UpdateView) -> bool {
    &&& discovered(v)
    &&& ns_rename_block::valid(v.directory_change)
    &&& ns_inode_touch::valid(v.parent_change) && ns_inode_touch::valid(v.target_change)
    &&& patch_set::valid(v.patches) && 0 < v.patches.len() <= 3
    &&& (forall|i: int| 0 <= i < v.patches.len() ==> (#[trigger] v.patches[i]).block == v.directory_block
        || v.patches[i].block as nat == v.parent_position / 4096 || v.patches[i].block as nat == v.target_position / 4096)
}

proof fn assemble_discovery(v: UpdateView)
    requires
        (certified(v.before, v.source) && 8192 <= v.source.len() <= MAX_IMAGE_BYTES),
        (!feature_policy::readonly(v.source.subrange(1024, 2048))),
        (ns_rename_block::proper_name(v.old_name) && ns_rename_block::proper_name(v.new_name)),
        (!crate::namespace_model::has_name(v.before.index.entries, v.directory, v.new_name)),
        (v.before.index.entries.contains(v.selected) && v.selected.directory == v.directory),
        (v.selected.name == v.old_name && v.selected.target == v.target && v.selected.generation == v.generation),
        (crate::ea_namespace_nodes::active(v.before.index.nodes, v.directory)),
        (crate::ea_namespace_nodes::active(v.before.index.nodes, v.target)),
        (v.parent_node == v.before.allocation.ordinary[v.before.index.nodes.slots[v.directory as int].ordinal as int].parent.node),
        (v.target_node == v.before.allocation.ordinary[v.before.index.nodes.slots[v.target as int].ordinal as int].parent.node),
        (v.parent_position == v.parent_node.position && v.target_position == v.target_node.position),
        (v.parent_node.number == v.directory && v.target_node.number == v.target),
        (v.parent_node.header == v.before.allocation.integrity.references.index.header),
        (v.target_node.header == v.parent_node.header),
        (v.generation as nat == bytes::le32(v.target_node.raw, 100)),
        (ea_directory::valid(v.directory_view) && v.directory_view.volume == v.before.allocation),
        (v.directory_view.ordinal == v.before.index.nodes.slots[v.directory as int].ordinal),
        (ea_directory::owner(v.directory_view) == v.directory),
        (v.selected.logical < v.directory_view.pieces.len()),
        (v.directory_block == v.directory_view.physical[v.selected.logical as int]),
        (v.directory_change.before == v.directory_view.pieces[v.selected.logical as int]),
        (v.directory_change.record == v.selected.record),
        (ns_rename_block::name(v.directory_change.before, v.directory_change.record as int) == v.old_name),
        (v.directory_change.before.block.records[v.directory_change.record as int].inode == v.target),
        (v.directory_change.before.block.records[v.directory_change.record as int].file_type == v.selected.file_type),
        (v.directory_change.new_name == v.new_name),
        (v.parent_change.before == v.parent_node.raw && v.target_change.before == v.target_node.raw),
        (v.parent_change.number == v.directory && v.target_change.number == v.target),
        (v.parent_change.inodes == v.parent_node.header.inodes && v.target_change.inodes == v.parent_node.header.inodes),
        (v.parent_change.seed == v.parent_node.header.seed && v.target_change.seed == v.parent_node.header.seed),
        (v.parent_change.huge == crate::ea_parent::huge(v.parent_node.header) && v.target_change.huge == v.parent_change.huge),
        (v.parent_change.touch_mtime && !v.target_change.touch_mtime),
        (v.parent_change.seconds == v.seconds && v.target_change.seconds == v.seconds),
        (v.parent_change.nanos == v.nanos && v.target_change.nanos == v.nanos),
    ensures discovered(v),
{ reveal(discovered); }

proof fn assemble_plan(v: UpdateView)
    requires
        (discovered(v)),
        (ns_rename_block::valid(v.directory_change)),
        (ns_inode_touch::valid(v.parent_change) && ns_inode_touch::valid(v.target_change)),
        (patch_set::valid(v.patches) && 0 < v.patches.len() <= 3),
        ((forall|i: int| 0 <= i < v.patches.len() ==> (#[trigger] v.patches[i]).block == v.directory_block
        || v.patches[i].block as nat == v.parent_position / 4096 || v.patches[i].block as nat == v.target_position / 4096)),
    ensures planned(v),
{ reveal(planned); }

#[verifier::opaque]
pub open spec fn image_bytes_match_plan(result: Seq<u8>, v: UpdateView) -> bool {
    &&& result.len() == v.source.len() && result == patch_set::apply(v.source, v.patches)
    &&& v.directory_block >= 2 && (v.directory_block as nat + 1) * 4096 <= v.source.len()
    &&& 8192 <= v.parent_position && v.parent_position as nat + 256 <= v.source.len()
    &&& 8192 <= v.target_position && v.target_position as nat + 256 <= v.source.len()
    &&& (v.parent_position as int + 256 <= v.target_position || v.target_position as int + 256 <= v.parent_position)
    &&& frame(v.source, result, v.directory_block, v.parent_position, v.target_position)
    &&& v.directory_change.before.block.raw == v.source.subrange(v.directory_block as int * 4096, (v.directory_block as int + 1) * 4096)
    &&& v.directory_change.after.block.raw == result.subrange(v.directory_block as int * 4096, (v.directory_block as int + 1) * 4096)
    &&& v.parent_change.before == v.source.subrange(v.parent_position as int, v.parent_position as int + 256)
    &&& v.parent_change.after == result.subrange(v.parent_position as int, v.parent_position as int + 256)
    &&& v.target_change.before == v.source.subrange(v.target_position as int, v.target_position as int + 256)
    &&& v.target_change.after == result.subrange(v.target_position as int, v.target_position as int + 256)
}
#[verifier::opaque]
pub open spec fn valid(v: UpdateView) -> bool {
    &&& planned(v) && certified(v.after, v.result)
    &&& renamed(v.before.index.entries, v.after.index.entries, v.entry, v.directory, v.old_name, v.new_name, v.target, v.generation)
    &&& v.before.index.entries[v.entry as int] == v.selected
    &&& image_bytes_match_plan(v.result, v)
}

proof fn assemble_result(v: UpdateView)
    requires
        (planned(v) && certified(v.after, v.result)),
        (renamed(v.before.index.entries, v.after.index.entries, v.entry, v.directory, v.old_name, v.new_name, v.target, v.generation)),
        (v.before.index.entries[v.entry as int] == v.selected),
        (image_bytes_match_plan(v.result, v)),
    ensures valid(v),
{ reveal(valid); }

pub struct Update { after: Vec<u8>, patches: PatchSet, checked: Ghost<UpdateView> }
impl Update {
    pub closed spec fn view(&self) -> UpdateView { self.checked@ }
    pub closed spec fn wf(&self) -> bool {
        valid(self.view()) && self.after@ == self.view().result && self.patches.view() == self.view().patches
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn bytes(&self) -> (r: &[u8])
        ensures self.wf(), valid(self.view()), r@ == self.view().result,
    { proof { use_type_invariant(self); } &self.after }
    pub fn patches(&self) -> (r: &PatchSet)
        ensures self.wf(), valid(self.view()), r.wf(), r.view() == self.view().patches,
    { proof { use_type_invariant(self); } let _ = self.patches.len(); &self.patches }
    pub(crate) fn into_result(self) -> (r: (Vec<u8>, Ghost<NamespaceView>))
        ensures r.0@ == self.view().result, r.1@ == self.view().after, certified(r.1@, r.0@),
    { proof { use_type_invariant(&self); reveal(valid); } (self.after, Ghost(self.checked@.after)) }
}

fn append(mut output: Vec<u8>, raw: &[u8]) -> (r: Vec<u8>)
    requires output.len() + raw.len() <= MAX_IMAGE_BYTES,
    ensures r@ == output@ + raw@,
{
    let ghost original = output@; let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len(), original.len() + raw.len() <= MAX_IMAGE_BYTES,
            output@ == original + raw@.take(i as int),
        decreases raw.len() - i,
    { output.push(raw[i]); assert(output@ =~= original + raw@.take(i as int + 1)); i += 1; }
    assert(raw@.take(i as int) =~= raw@); output
}
fn copy(raw: &[u8]) -> (r: Vec<u8>)
    requires raw.len() <= MAX_IMAGE_BYTES,
    ensures r@ == raw@,
{
    let output = Vec::new(); let result = append(output, raw); assert(result@ =~= raw@); result
}
fn materialize(source: &Snapshot<'_>) -> (r: Option<Vec<u8>>)
    ensures match r { Some(raw) => raw@ == source.view() && raw.len() <= MAX_IMAGE_BYTES, None => true },
{
    let length = source.partition_bytes(); if length > MAX_IMAGE_BYTES as u64 { return None; }
    let mut output = Vec::new(); let mut offset = 0usize;
    while offset < length as usize
        invariant length == source.view().len(), length <= MAX_IMAGE_BYTES, offset <= length,
            output@ == source.view().take(offset as int),
        decreases length - offset,
    {
        let remaining = length as usize - offset; let amount = if remaining < 65536 { remaining } else { 65536usize };
        let raw = match source.capture_bytes(offset as u64, amount) { Some(raw) => raw, None => { return None; } };
        output = append(output, &raw);
        assert(output@ =~= source.view().take(offset as int + amount));
        offset += amount;
    }
    assert(source.view().take(offset as int) =~= source.view()); Some(output)
}

fn touch_patch(source: &Snapshot<'_>, patches: PatchSet, position: u64, raw: &[u8]) -> (r: Option<PatchSet>)
    ensures match r { Some(next) => next.wf(), None => true },
{
    if raw.len() != 256 || position > source.partition_bytes() || 256 > source.partition_bytes() - position
        || position % 4096 > 3840 || position / 4096 > u32::MAX as u64 { return None; }
    let block = (position / 4096) as u32; let within = (position % 4096) as usize;
    let mut bytes = match patches.get(block) {
        Some(image) => copy(image.as_slice()),
        None => match source.capture(block, 1) { Some(raw) => raw, None => { return None; } },
    };
    if !crate::bytes::write_bytes(bytes.as_mut_slice(), within, raw) { return None; }
    match patches.upsert(block, &bytes) { Ok(next) => Some(next), Err(_) => None }
}

fn names_equal(a: &crate::ea_directory_index::Entry, b: &crate::ea_directory_index::Entry) -> (r: bool)
    ensures r == (a.view().name == b.view().name),
{ bytes::equal(a.name(), b.name()) }
fn identity_equal(a: &crate::ea_directory_index::Entry, b: &crate::ea_directory_index::Entry) -> (r: bool)
    ensures r == (a.view().directory == b.view().directory && a.view().logical == b.view().logical
        && a.view().record == b.view().record && a.view().target == b.view().target
        && a.view().generation == b.view().generation && a.view().file_type == b.view().file_type),
{ a.identity() == b.identity() && a.location() == b.location() }
fn check_entries(before: &DirectoryIndex<'_>, after: &DirectoryIndex<'_>, directory: u32,
    old_name: &[u8], new_name: &[u8], target: u32, generation: u32, logical: u32, record: usize, file_type: u8) -> (r: Option<usize>)
    ensures before.wf(), after.wf(), match r {
        Some(entry) => renamed(before.view().entries, after.view().entries, entry, directory, old_name@, new_name@, target, generation)
            && before.view().entries[entry as int].logical == logical && before.view().entries[entry as int].record == record
            && before.view().entries[entry as int].file_type == file_type,
        None => true },
{
    let count = before.len(); if after.len() != count { return None; }
    let mut chosen: Option<usize> = None; let mut i = 0usize;
    while i < count
        invariant before.wf(), after.wf(), count == before.view().entries.len(), count == after.view().entries.len(), i <= count,
            match chosen { Some(p) => p < i && before.view().entries[p as int].directory == directory
                && before.view().entries[p as int].name == old_name@ && before.view().entries[p as int].target == target
                && before.view().entries[p as int].generation == generation
                && before.view().entries[p as int].logical == logical && before.view().entries[p as int].record == record
                && before.view().entries[p as int].file_type == file_type
                && after.view().entries[p as int] == (EntryView { name: new_name@, ..before.view().entries[p as int] }), None => true },
            forall|j: int| 0 <= j < i && chosen != Some(j as usize) ==> (#[trigger] after.view().entries[j]) == before.view().entries[j],
        decreases count - i,
    {
        let a = before.get(i).unwrap(); let b = after.get(i).unwrap();
        if !identity_equal(a, b) { return None; }
        let (container, actual_target, actual_generation, _) = a.identity();
        if container == directory && bytes::equal(a.name(), old_name) {
            if chosen.is_some() || actual_target != target || actual_generation != generation || a.location() != (logical, record)
                || a.identity().3 != file_type || !bytes::equal(b.name(), new_name) { return None; }
            chosen = Some(i);
            assert(b.view() == (EntryView { name: new_name@, ..a.view() }));
        } else {
            if !names_equal(a, b) { return None; }
            assert(b.view() == a.view());
        }
        i += 1;
    }
    match chosen { Some(entry) => Some(entry), None => None }
}

fn frame_check(source: &Snapshot<'_>, result: &[u8], directory_block: u32, parent_position: u64, target_position: u64) -> (r: bool)
    ensures r ==> frame(source.view(), result@, directory_block, parent_position, target_position),
{
    let length = source.partition_bytes(); if length != result.len() as u64 || length > MAX_IMAGE_BYTES as u64 { return false; }
    let mut offset = 0usize;
    while offset < result.len()
        invariant length == source.view().len(), length == result.len(), length <= MAX_IMAGE_BYTES, offset <= result.len(),
            forall|i: int| 0 <= i < offset && !editable(i, directory_block, parent_position, target_position) ==> #[trigger] result@[i] == source.view()[i],
        decreases result.len() - offset,
    {
        let remaining = result.len() - offset; let amount = if remaining < 65536 { remaining } else { 65536usize };
        let raw = match source.capture_bytes(offset as u64, amount) { Some(raw) => raw, None => { return false; } };
        let mut i = 0usize;
        while i < amount
            invariant offset + amount <= result.len() <= MAX_IMAGE_BYTES, raw.len() == amount <= 65536, i <= amount,
                raw@ == source.view().subrange(offset as int, offset as int + amount),
                source.view().len() == result.len(), offset + amount <= source.view().len(),
                forall|j: int| 0 <= j < offset + i && !editable(j, directory_block, parent_position, target_position) ==> #[trigger] result@[j] == source.view()[j],
            decreases amount - i,
        {
            let at = offset + i;
            let allowed = directory_block as u64 * 4096 <= at as u64 && (at as u64) < (directory_block as u64 + 1) * 4096
                || parent_position <= at as u64 && (at as u128) < parent_position as u128 + 256
                || target_position <= at as u64 && (at as u128) < target_position as u128 + 256;
            assert(allowed == editable(at as int, directory_block, parent_position, target_position));
            if !allowed && result[at] != raw[i] { return false; }
            assert forall|j: int| 0 <= j < at + 1 && !editable(j, directory_block, parent_position, target_position)
                implies (#[trigger] result@[j]) == source.view()[j] by {
                if j < at { assert(result@[j] == source.view()[j]); }
                else { assert(j == at); assert(raw@[i as int] == source.view()[j]); }
            }
            i += 1;
        }
        offset += amount;
    }
    true
}

// Establish source positions and the inner codec frames by checking the actual
// bytes; this also protects shared inode-table blocks after coalescing.
fn check_bytes(source: &Snapshot<'_>, result: &[u8], directory_block: u32, parent_position: u64, target_position: u64,
    directory_before: &[u8], directory_after: &[u8], parent_before: &[u8], parent_after: &[u8], target_before: &[u8], target_after: &[u8]) -> (r: bool)
    ensures r ==> source.view().len() == result.len() && 8192 <= source.view().len() <= MAX_IMAGE_BYTES
        && directory_block >= 2 && (directory_block as nat + 1) * 4096 <= source.view().len()
        && 8192 <= parent_position && parent_position as nat + 256 <= source.view().len()
        && 8192 <= target_position && target_position as nat + 256 <= source.view().len()
        && (parent_position as int + 256 <= target_position || target_position as int + 256 <= parent_position)
        && directory_before@ == source.view().subrange(directory_block as int * 4096, (directory_block as int + 1) * 4096)
        && directory_after@ == result@.subrange(directory_block as int * 4096, (directory_block as int + 1) * 4096)
        && parent_before@ == source.view().subrange(parent_position as int, parent_position as int + 256)
        && parent_after@ == result@.subrange(parent_position as int, parent_position as int + 256)
        && target_before@ == source.view().subrange(target_position as int, target_position as int + 256)
        && target_after@ == result@.subrange(target_position as int, target_position as int + 256)
        && frame(source.view(), result@, directory_block, parent_position, target_position),
{
    let length = source.partition_bytes();
    if length != result.len() as u64 || length < 8192 || length > MAX_IMAGE_BYTES as u64
        || directory_block < 2 || (directory_block as u64 + 1) * 4096 > length
        || parent_position < 8192 || parent_position > length || 256 > length - parent_position
        || target_position < 8192 || target_position > length || 256 > length - target_position { return false; }
    if !(parent_position + 256 <= target_position || target_position + 256 <= parent_position) { return false; }
    let db = directory_block as usize * 4096; let pp = parent_position as usize; let tp = target_position as usize;
    let dbefore = match source.capture_bytes(db as u64, 4096) { Some(raw) => raw, None => { return false; } };
    let pbefore = match source.capture_bytes(parent_position, 256) { Some(raw) => raw, None => { return false; } };
    let tbefore = match source.capture_bytes(target_position, 256) { Some(raw) => raw, None => { return false; } };
    if !bytes::equal(&dbefore, directory_before) || !bytes::equal(&result[db..db + 4096], directory_after)
        || !bytes::equal(&pbefore, parent_before) || !bytes::equal(&result[pp..pp + 256], parent_after)
        || !bytes::equal(&tbefore, target_before) || !bytes::equal(&result[tp..tp + 256], target_after) { return false; }
    frame_check(source, result, directory_block, parent_position, target_position)
}


// A narrow source-ordinal barrier instantiates the allocation quantifier at
// its actual trigger before exposing just the checked inode and source index.
proof fn allocation_ordinary_at(v: crate::ea_allocation::AllocationView, ordinal: int)
    requires crate::ea_allocation::valid(v), 0 <= ordinal < v.ordinary.len(),
    ensures crate::ea_ordinary::valid(v.ordinary[ordinal]),
        v.ordinary[ordinal].index == v.integrity.references.index,
{
    reveal(crate::ea_allocation::valid);
    assert(crate::ea_ordinary::valid(v.ordinary[ordinal]));
    assert(v.ordinary[ordinal].index == v.integrity.references.index);
}

// Include in ns_rename's verus! block. This is a private source-binding lemma;
// it establishes identity from the exact source slot, never checksum equality.
proof fn namespace_inode_node_is_exact(namespace: crate::ea_namespace::NamespaceView,
    number: u32, node: crate::ea_source::NodeView)
    requires crate::ea_namespace::valid(namespace),
        crate::ea_namespace_nodes::active(namespace.index.nodes, number),
        crate::ea_source::node_valid(node), node.number == number,
        node.header == namespace.allocation.integrity.references.index.header,
    ensures namespace.index.nodes.slots[number as int].ordinal < namespace.allocation.ordinary.len(),
        crate::ea_ordinary::valid(namespace.allocation.ordinary[
            namespace.index.nodes.slots[number as int].ordinal as int]),
        namespace.allocation.ordinary[namespace.index.nodes.slots[number as int].ordinal as int].index
            == namespace.allocation.integrity.references.index,
        node == namespace.allocation.ordinary[
            namespace.index.nodes.slots[number as int].ordinal as int].parent.node,
{
    let table = namespace.index.nodes;
    assert(crate::ea_namespace_nodes::valid(table)
        && table.volume == namespace.allocation) by {
        reveal(crate::ea_namespace::valid);
        reveal(crate::ea_directory_index::valid);
    }
    crate::ea_namespace_nodes::every_active_namespace_node_matches_one_exact_source_ordinary_inode(table, number);
    let ordinal = table.slots[number as int].ordinal;
    let ordinary = namespace.allocation.ordinary[ordinal as int];
    assert(crate::ea_namespace_nodes::matches(table.slots[number as int], ordinary));
    assert(crate::ea_allocation::valid(namespace.allocation)) by { reveal(crate::ea_namespace::valid); }
    allocation_ordinary_at(namespace.allocation, ordinal as int);
    assert(crate::ea_ordinary::valid(namespace.allocation.ordinary[ordinal as int]));
    assert(namespace.allocation.ordinary[ordinal as int].index == namespace.allocation.integrity.references.index);
    assert(crate::ea_source::node_valid(ordinary.parent.node)
        && ordinary.parent.node.header == namespace.allocation.integrity.references.index.header
        && ordinary.parent.node.number == number) by {
        reveal(crate::ea_ordinary::valid);
        reveal(crate::ea_parent::valid);
    }
    crate::ea_integrity::same_source_ea_inode_number_identifies_one_exact_node(node, ordinary.parent.node);
}

// The binding is to the actual retained source tree and final ownership
// certificate, not to checksum equality or an independently supplied block.
proof fn captured_piece_is_encoder_view(v: ea_directory::DirectoryView, logical: u32, raw: Seq<u8>,
    inodes: u32, metadata_seed: u32, indexed: bool, large: bool)
    requires ea_directory::valid(v), logical < v.pieces.len(), logical < v.physical.len(),
        (v.physical[logical as int] as nat + 1) * 4096 <= v.volume.integrity.references.index.header.source.len(),
        raw == v.volume.integrity.references.index.header.source.subrange(v.physical[logical as int] as int * 4096,
            (v.physical[logical as int] as int + 1) * 4096),
        inodes == ea_directory::ordinary(v).index.header.inodes,
        metadata_seed == ea_directory::seed(ea_directory::ordinary(v)),
        indexed == ea_directory::indexed(ea_directory::ordinary(v)), large == ea_directory::large(v.volume),
    ensures ns_rename_block::view(raw, inodes, metadata_seed, indexed, logical, v.pieces.len() as u32, large) == v.pieces[logical as int],
        v.pieces[logical as int].block.raw == raw,
        v.pieces[logical as int].block.inodes == inodes, v.pieces[logical as int].block.seed == metadata_seed,
        v.pieces[logical as int].indexed == indexed, v.pieces[logical as int].logical == logical,
        v.pieces[logical as int].blocks == v.pieces.len() as u32, v.pieces[logical as int].large == large,
{
    hide(crate::crc::fold);
    ea_directory::every_directory_piece_comes_from_its_initialized_owned_source_mapping(v, logical);
    assert(ea_directory::ordinary(v).index == v.volume.integrity.references.index) by { reveal(ea_directory::valid); }
    let piece = v.pieces[logical as int];
    assert(ea_directory::checked_piece(v.volume, ea_directory::ordinary(v), piece,
        v.physical[logical as int], logical, v.pieces.len() as u32));
    assert(piece.block.raw == raw && piece.block.inodes == inodes && piece.block.seed == metadata_seed
        && piece.indexed == indexed && piece.logical == logical && piece.blocks == v.pieces.len() as u32 && piece.large == large
        && crate::directory_piece::valid(piece)) by { reveal(ea_directory::checked_piece); }
    assert(piece.block.records == crate::directory_piece::canonical_records(raw, inodes, indexed, logical)) by {
        reveal(crate::directory_piece::valid);
    }
    assert(piece == ns_rename_block::view(raw, inodes, metadata_seed, indexed, logical, v.pieces.len() as u32, large));
}

proof fn assembled_result_keeps_the_plan(before: UpdateView, after: UpdateView)
    requires planned(before), after == (UpdateView { result: after.result, after: after.after, entry: after.entry, ..before }),
    ensures planned(after),
{ reveal(planned); reveal(discovered); }

fn check_targets(patches: &PatchSet, directory_block: u32, parent_position: u64, target_position: u64) -> (r: bool)
    ensures patches.wf(), r ==> 0 < patches.view().len() <= 3
        && (forall|i: int| 0 <= i < patches.view().len() ==> (#[trigger] patches.view()[i]).block == directory_block
            || patches.view()[i].block as nat == parent_position / 4096 || patches.view()[i].block as nat == target_position / 4096),
{
    let count = patches.len(); if count == 0 || count > 3 { return false; }
    let mut i = 0usize;
    while i < count
        invariant patches.wf(), count == patches.view().len(), 0 < count <= 3, i <= count,
            forall|j: int| 0 <= j < i ==> (#[trigger] patches.view()[j]).block == directory_block
                || patches.view()[j].block as nat == parent_position / 4096 || patches.view()[j].block as nat == target_position / 4096,
        decreases count - i,
    {
        let block = patches.at(i).unwrap().block();
        if block != directory_block && block as u64 != parent_position / 4096 && block as u64 != target_position / 4096 { return false; }
        i += 1;
    }
    true
}

struct Plan<'a> {
    directory_block: u32, parent_position: u64, target_position: u64, target: u32, generation: u32, logical: u32, record: usize, file_type: u8,
    directory_before: &'a [u8], parent_before: &'a [u8], target_before: &'a [u8],
    directory_after: Vec<u8>, parent_after: Vec<u8>, target_after: Vec<u8>, patches: PatchSet, checked: Ghost<UpdateView>,
}
impl<'a> Plan<'a> {
    closed spec fn view(&self) -> UpdateView { self.checked@ }
    closed spec fn wf(&self) -> bool {
        planned(self.view()) && self.patches.view() == self.view().patches
            && self.directory_block == self.view().directory_block && self.parent_position == self.view().parent_position
            && self.target_position == self.view().target_position && self.target == self.view().target && self.generation == self.view().generation
            && self.logical == self.view().selected.logical && self.record == self.view().selected.record && self.file_type == self.view().selected.file_type
            && self.directory_before@ == self.view().directory_change.before.block.raw
            && self.parent_before@ == self.view().parent_change.before && self.target_before@ == self.view().target_change.before
            && self.directory_after@ == self.view().directory_change.after.block.raw
            && self.parent_after@ == self.view().parent_change.after && self.target_after@ == self.view().target_change.after
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
}


struct Discovery<'a> {
    directory: u32, directory_block: u32, parent_position: u64, target_position: u64,
    target: u32, generation: u32, logical: u32, record: usize, file_type: u8,
    inodes: u32, checksum_seed: u32, huge: bool, indexed: bool, large: bool, block_seed: u32, count: u32,
    directory_before: &'a [u8], parent_before: &'a [u8], target_before: &'a [u8], checked: Ghost<UpdateView>,
}
impl<'a> Discovery<'a> {
    closed spec fn view(&self) -> UpdateView { self.checked@ }
    closed spec fn wf(&self) -> bool {
        discovered(self.view()) && self.directory == self.view().directory
            && self.directory_block == self.view().directory_block && self.parent_position == self.view().parent_position
            && self.target_position == self.view().target_position && self.target == self.view().target && self.generation == self.view().generation
            && self.logical == self.view().selected.logical && self.record == self.view().selected.record && self.file_type == self.view().selected.file_type
            && self.directory_before@ == self.view().directory_change.before.block.raw
            && self.parent_before@ == self.view().parent_change.before && self.target_before@ == self.view().target_change.before
            && self.directory == self.view().parent_change.number && self.target == self.view().target_change.number
            && self.record == self.view().directory_change.record && self.view().directory_change.new_name == self.view().new_name
            && self.view().parent_change.touch_mtime && !self.view().target_change.touch_mtime
            && self.view().parent_change.seconds == self.view().seconds && self.view().target_change.seconds == self.view().seconds
            && self.view().parent_change.nanos == self.view().nanos && self.view().target_change.nanos == self.view().nanos
            && self.inodes == self.view().parent_change.inodes && self.inodes == self.view().target_change.inodes
            && self.checksum_seed == self.view().parent_change.seed && self.checksum_seed == self.view().target_change.seed
            && self.huge == self.view().parent_change.huge && self.huge == self.view().target_change.huge
            && self.indexed == self.view().directory_change.before.indexed && self.large == self.view().directory_change.before.large
            && self.block_seed == self.view().directory_change.before.block.seed && self.count == self.view().directory_change.before.blocks
            && self.view().directory_change.before == ns_rename_block::view(self.directory_before@, self.inodes, self.block_seed,
                self.indexed, self.logical, self.count, self.large)
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
}

proof fn source_discovery_survives_encoding(before: UpdateView, after: UpdateView)
    requires discovered(before), after == (UpdateView {
        directory_change: ns_rename_block::Change { after: after.directory_change.after, ..before.directory_change },
        parent_change: ns_inode_touch::Change { after: after.parent_change.after, ..before.parent_change },
        target_change: ns_inode_touch::Change { after: after.target_change.after, ..before.target_change },
        patches: after.patches, ..before }),
    ensures discovered(after),
{ reveal(discovered); }

proof fn image_effect_survives_certificate_attachment(before: UpdateView, after: UpdateView)
    requires image_bytes_match_plan(after.result, before),
        after == (UpdateView { result: after.result, after: after.after, entry: after.entry, ..before }),
    ensures image_bytes_match_plan(after.result, after),
{ reveal(image_bytes_match_plan); }

#[verifier::rlimit(20)]
#[verifier::spinoff_prover]
fn discover_source<'a>(source: &Snapshot<'a>, before: &ea_namespace::Namespace<'_, 'a>, directory: u32,
    old_name: &[u8], new_name: &[u8], seconds: i64, nanos: u32) -> (r: Result<Discovery<'a>, Error>)
    requires before.wf(), ea_namespace::valid(before.view()), certified(before.view(), source.view()),
        8192 <= source.view().len() <= MAX_IMAGE_BYTES,
    ensures match r { Ok(d) => d.wf() && discovered(d.view()) && d.view().source == source.view()
        && d.view().before == before.view() && d.view().directory == directory
        && d.view().old_name == old_name@ && d.view().new_name == new_name@
        && d.view().seconds == seconds && d.view().nanos == nanos, Err(_) => true },
{
    hide(vstd::slice::axiom_spec_len);
    hide(crate::crc::fold);
    hide(crate::ea_directory_index::source_has_name);
    hide(crate::namespace_model::has_name);
    hide(ns_rename_block::view);
    let primary = source.block(0).unwrap();
    let primary_raw = primary.as_slice();
    proof { vstd::slice::axiom_spec_len(primary_raw); }
    let superblock = primary.range(1024, 1024).unwrap();
    if feature_policy::is_readonly(superblock).unwrap() { return Err(Error::ReadOnly); }
    if !proper_name(old_name) || !proper_name(new_name) { return Err(Error::Invalid); }
    let entry = match before.lookup(directory, old_name) { Some(entry) => entry, None => { return Err(Error::NotFound); } };
    if before.lookup(directory, new_name).is_some() { return Err(Error::Exists); }
    let (_, target, generation, file_type) = entry.identity(); let (logical, record) = entry.location();
    if target == directory { return Err(Error::Rejected); }
    let nodes = before.index().nodes(); let _target_slot = match nodes.get(target) { Some(slot) => slot, None => { return Err(Error::Rejected); } };
    let parent = match nodes.get(directory) { Some(parent) => parent, None => { return Err(Error::Rejected); } };
    let directory_source = match ea_directory::inspect(before.allocation(), parent.ordinal) { Some(d) => d, None => { return Err(Error::Rejected); } };
    let physical = match directory_source.physical_block(logical) { Some(p) => p, None => { return Err(Error::Rejected); } };
    let directory_bytes = match source.block(physical) { Some(b) => b.as_slice(), None => { return Err(Error::Rejected); } };
    let inode_index = before.allocation().integrity().reference_census().index();
    let parent_inode = match inode_index.node(directory) { Some(n) => n, None => { return Err(Error::Rejected); } };
    let target_inode = match inode_index.node(target) { Some(n) => n, None => { return Err(Error::Rejected); } };
    let parent_raw = parent_inode.raw(); let target_raw = target_inode.raw();
    proof {
        namespace_inode_node_is_exact(before.view(), directory, parent_inode.view());
        namespace_inode_node_is_exact(before.view(), target, target_inode.view());
    }
    if bytes::read_le32(target_raw, 100).unwrap() != generation { return Err(Error::Rejected); }
    let parent_position = parent_inode.position(); let target_position = target_inode.position();
    let (_, inodes, _, checksum_seed) = inode_index.parameters(); let huge = inode_index.header().huge_files();
    let indexed = bytes::read_le32(parent_raw, 32).unwrap() & 0x1000 != 0;
    let large = bytes::read_le32(primary_raw, 1120).unwrap() & 0x4000 != 0;
    let block_seed = inode::inode_seed(checksum_seed, directory, bytes::read_le32(parent_raw, 100).unwrap());
    let count = directory_source.block_count();
    let source_piece = match directory_source.piece(logical) { Some(piece) => piece, None => { return Err(Error::Rejected); } };
    let source_record = match source_piece.get(record) { Some(r) => r, None => { return Err(Error::Rejected); } };
    let source_name = match source_piece.name(record) { Some(name) => name, None => { return Err(Error::Rejected); } };
    if source_record.inode != target || source_record.file_type != file_type || !bytes::equal(source_name, old_name) { return Err(Error::Rejected); }
    proof {
        captured_piece_is_encoder_view(directory_source.view(), logical, directory_bytes@, inodes, block_seed, indexed, large);
    }

    let ghost directory_change = ns_rename_block::Change { before: source_piece.view(), after: source_piece.view(), record, new_name: new_name@ };
    let ghost parent_change = ns_inode_touch::Change { before: parent_raw@, after: parent_raw@, number: directory,
        inodes, seed: checksum_seed, huge, touch_mtime: true, seconds: seconds as int, nanos: nanos as nat };
    let ghost target_change = ns_inode_touch::Change { before: target_raw@, after: target_raw@, number: target,
        inodes, seed: checksum_seed, huge, touch_mtime: false, seconds: seconds as int, nanos: nanos as nat };
    let ghost view = UpdateView { source: source.view(), result: source.view(), before: before.view(), after: before.view(),
        directory, old_name: old_name@, new_name: new_name@, target, generation, entry: 0, selected: entry.view(),
        seconds: seconds as int, nanos: nanos as nat, patches: Seq::empty(), directory_block: physical,
        parent_position, target_position, parent_node: parent_inode.view(), target_node: target_inode.view(),
        directory_view: directory_source.view(), directory_change, parent_change, target_change };
    proof { assemble_discovery(view); }
    Ok(Discovery { directory, directory_block: physical, parent_position, target_position, target, generation, logical, record, file_type,
        inodes, checksum_seed, huge, indexed, large, block_seed, count,
        directory_before: directory_bytes, parent_before: parent_raw, target_before: target_raw, checked: Ghost(view) })
}

proof fn codec_piece_view_retains_its_raw(raw: Seq<u8>, inodes: u32, seed: u32, indexed: bool,
    logical: u32, blocks: u32, large: bool)
    ensures ns_rename_block::view(raw, inodes, seed, indexed, logical, blocks, large).block.raw == raw,
{ reveal(ns_rename_block::view); }

// Keep concrete block staging separate from codec/source witness assembly.
#[verifier::rlimit(10)]
#[verifier::spinoff_prover]
fn stage_patches(source: &Snapshot<'_>, directory_block: u32, parent_position: u64, target_position: u64,
    directory_after: &[u8], parent_after: &[u8], target_after: &[u8]) -> (r: Result<PatchSet, Error>)
    ensures match r { Ok(patches) => patches.wf() && 0 < patches.view().len() <= 3
        && (forall|i: int| 0 <= i < patches.view().len() ==> (#[trigger] patches.view()[i]).block == directory_block
            || patches.view()[i].block as nat == parent_position / 4096 || patches.view()[i].block as nat == target_position / 4096),
        Err(_) => true },
{
    hide(vstd::slice::axiom_spec_len);
    let patches = match PatchSet::new().insert(directory_block, directory_after) { Ok(p) => p, Err(_) => { return Err(Error::NoSpace); } };
    let patches = match touch_patch(source, patches, parent_position, parent_after) { Some(p) => p, None => { return Err(Error::Rejected); } };
    let patches = match touch_patch(source, patches, target_position, target_after) { Some(p) => p, None => { return Err(Error::Rejected); } };
    if !check_targets(&patches, directory_block, parent_position, target_position) { return Err(Error::Rejected); }
    Ok(patches)
}

// Encode the three records before exposing patch staging. The owned outputs
// carry one exact update witness; source-discovery fields stay unchanged.
#[verifier::rlimit(20)]
#[verifier::spinoff_prover]
fn encode_records(d: &Discovery<'_>, new_name: &[u8], seconds: i64, nanos: u32)
    -> (r: Result<(Vec<u8>, Vec<u8>, Vec<u8>, Ghost<UpdateView>), Error>)
    requires d.wf(), new_name@ == d.view().new_name,
        seconds == d.view().seconds, nanos == d.view().nanos,
    ensures d.wf(), match r {
        Ok((directory, parent, target, checked)) =>
            discovered(checked@)
            && ns_rename_block::valid(checked@.directory_change)
            && ns_inode_touch::valid(checked@.parent_change)
            && ns_inode_touch::valid(checked@.target_change)
            && checked@ == (UpdateView {
                directory_change: ns_rename_block::Change {
                    after: checked@.directory_change.after, ..d.view().directory_change },
                parent_change: ns_inode_touch::Change {
                    after: checked@.parent_change.after, ..d.view().parent_change },
                target_change: ns_inode_touch::Change {
                    after: checked@.target_change.after, ..d.view().target_change },
                ..d.view() })
            && checked@.directory_change.before.block.raw == d.directory_before@
            && checked@.parent_change.before == d.parent_before@
            && checked@.target_change.before == d.target_before@
            && checked@.directory_change.after.block.raw == directory@
            && checked@.parent_change.after == parent@
            && checked@.target_change.after == target@,
        Err(_) => true,
    },
{
    hide(vstd::slice::axiom_spec_len);
    hide(ns_rename_block::view);
    let changed_directory = match ns_rename_block::encode(d.directory_before, d.inodes, d.block_seed, d.indexed,
        d.logical, d.count, d.large, d.record, new_name) { Some(raw) => raw, None => { return Err(Error::NoSpace); } };
    let changed_parent = match ns_inode_touch::encode(d.parent_before, d.directory, d.inodes, d.checksum_seed, d.huge, true, seconds, nanos) {
        Some(raw) => raw, None => { return Err(Error::Rejected); }
    };
    let changed_target = match ns_inode_touch::encode(d.target_before, d.target, d.inodes, d.checksum_seed, d.huge, false, seconds, nanos) {
        Some(raw) => raw, None => { return Err(Error::Rejected); }
    };
    let ghost directory_change = ns_rename_block::Change {
        after: ns_rename_block::view(changed_directory@, d.inodes, d.block_seed,
            d.indexed, d.logical, d.count, d.large), ..d.view().directory_change };
    let ghost parent_change = ns_inode_touch::Change {
        after: changed_parent@, ..d.view().parent_change };
    let ghost target_change = ns_inode_touch::Change {
        after: changed_target@, ..d.view().target_change };
    proof {
        codec_piece_view_retains_its_raw(changed_directory@, d.inodes, d.block_seed, d.indexed, d.logical, d.count, d.large);
    }
    let ghost encoded = UpdateView { directory_change, parent_change, target_change, ..d.view() };
    proof { source_discovery_survives_encoding(d.view(), encoded); }
    Ok((changed_directory, changed_parent, changed_target, Ghost(encoded)))
}

// Attach the checked patch set and establish the owned Plan invariant in a
// context containing only the exact encoded records and their source witness.
#[verifier::rlimit(20)]
#[verifier::spinoff_prover]
fn make_plan<'a>(d: Discovery<'a>, changed_directory: Vec<u8>, changed_parent: Vec<u8>,
    changed_target: Vec<u8>, encoded: Ghost<UpdateView>, patches: PatchSet) -> (r: Plan<'a>)
    requires d.wf(),
        discovered(encoded@),
        ns_rename_block::valid(encoded@.directory_change),
        ns_inode_touch::valid(encoded@.parent_change),
        ns_inode_touch::valid(encoded@.target_change),
        encoded@ == (UpdateView {
            directory_change: ns_rename_block::Change {
                after: encoded@.directory_change.after, ..d.view().directory_change },
            parent_change: ns_inode_touch::Change {
                after: encoded@.parent_change.after, ..d.view().parent_change },
            target_change: ns_inode_touch::Change {
                after: encoded@.target_change.after, ..d.view().target_change },
            ..d.view() }),
        encoded@.directory_change.before.block.raw == d.directory_before@,
        encoded@.parent_change.before == d.parent_before@,
        encoded@.target_change.before == d.target_before@,
        encoded@.directory_change.after.block.raw == changed_directory@,
        encoded@.parent_change.after == changed_parent@,
        encoded@.target_change.after == changed_target@,
        patches.wf(), 0 < patches.view().len() <= 3,
        (forall|i: int| 0 <= i < patches.view().len() ==> (#[trigger] patches.view()[i]).block == d.directory_block
            || patches.view()[i].block as nat == d.parent_position / 4096
            || patches.view()[i].block as nat == d.target_position / 4096),
    ensures r.wf(), planned(r.view()),
        r.view() == (UpdateView { patches: patches.view(), ..encoded@ }),
        r.view().source == d.view().source, r.view().before == d.view().before,
        r.view().directory == d.view().directory,
        r.view().old_name == d.view().old_name, r.view().new_name == d.view().new_name,
        r.view().seconds == d.view().seconds, r.view().nanos == d.view().nanos,
{
    hide(vstd::slice::axiom_spec_len);
    hide(ns_rename_block::view);
    let ghost view = UpdateView { patches: patches.view(), ..encoded@ };
    proof { source_discovery_survives_encoding(encoded@, view); assemble_plan(view); }
    Plan { directory_block: d.directory_block, parent_position: d.parent_position, target_position: d.target_position,
        target: d.target, generation: d.generation, logical: d.logical, record: d.record, file_type: d.file_type,
        directory_before: d.directory_before, parent_before: d.parent_before, target_before: d.target_before,
        directory_after: changed_directory, parent_after: changed_parent, target_after: changed_target, patches, checked: Ghost(view) }
}

#[verifier::rlimit(20)]
#[verifier::spinoff_prover]
fn encode_plan<'a>(source: &Snapshot<'a>, d: Discovery<'a>, new_name: &[u8], seconds: i64, nanos: u32) -> (r: Result<Plan<'a>, Error>)
    requires d.wf(), source.view() == d.view().source, new_name@ == d.view().new_name,
        seconds == d.view().seconds, nanos == d.view().nanos,
    ensures match r { Ok(plan) => plan.wf() && planned(plan.view()) && plan.view().source == d.view().source
        && plan.view().before == d.view().before && plan.view().directory == d.view().directory
        && plan.view().old_name == d.view().old_name && plan.view().new_name == d.view().new_name
        && plan.view().seconds == d.view().seconds && plan.view().nanos == d.view().nanos, Err(_) => true },
{
    hide(vstd::slice::axiom_spec_len);
    hide(ns_rename_block::view);
    let (changed_directory, changed_parent, changed_target, encoded) =
        match encode_records(&d, new_name, seconds, nanos) {
            Ok(records) => records, Err(error) => { return Err(error); }
        };
    let patches = match stage_patches(source, d.directory_block, d.parent_position, d.target_position,
        &changed_directory, &changed_parent, &changed_target) { Ok(p) => p, Err(error) => { return Err(error); } };
    Ok(make_plan(d, changed_directory, changed_parent, changed_target, encoded, patches))
}

#[verifier::rlimit(10)]
fn build_plan<'a>(source: &Snapshot<'a>, before: &ea_namespace::Namespace<'_, 'a>, directory: u32,
    old_name: &[u8], new_name: &[u8], seconds: i64, nanos: u32) -> (r: Result<Plan<'a>, Error>)
    requires before.wf(), ea_namespace::valid(before.view()), certified(before.view(), source.view()),
        8192 <= source.view().len() <= MAX_IMAGE_BYTES,
    ensures match r { Ok(plan) => plan.wf() && planned(plan.view()) && plan.view().source == source.view()
        && plan.view().before == before.view() && plan.view().directory == directory
        && plan.view().old_name == old_name@ && plan.view().new_name == new_name@
        && plan.view().seconds == seconds && plan.view().nanos == nanos, Err(_) => true },
{
    let d = match discover_source(source, before, directory, old_name, new_name, seconds, nanos) { Ok(d) => d, Err(e) => { return Err(e); } };
    encode_plan(source, d, new_name, seconds, nanos)
}

#[verifier::rlimit(10)]
fn materialize_plan(source: &Snapshot<'_>, plan: &Plan<'_>) -> (r: Result<Vec<u8>, Error>)
    requires plan.wf(), source.view() == plan.view().source,
    ensures match r { Ok(result) => image_bytes_match_plan(result@, plan.view()), Err(_) => true },
{
    let shadow = match source.overlay(&plan.patches) { Some(s) => s, None => { return Err(Error::NoSpace); } };
    let result = match materialize(&shadow) { Some(raw) => raw, None => { return Err(Error::Rejected); } };
    if !check_bytes(source, &result, plan.directory_block, plan.parent_position, plan.target_position,
        plan.directory_before, &plan.directory_after, plan.parent_before, &plan.parent_after, plan.target_before, &plan.target_after) { return Err(Error::Rejected); }
    assert(image_bytes_match_plan(result@, plan.view())) by { reveal(image_bytes_match_plan); }
    Ok(result)
}

// Include inside ns_rename's verus! block. Keep the complete source-discovery
// predicate out of the executable final-admission context.
proof fn selected_entry_projection_fields(v: UpdateView)
    requires planned(v),
    ensures v.selected.directory == v.directory, v.selected.name == v.old_name,
        v.selected.target == v.target, v.selected.generation == v.generation,
{ reveal(planned); reveal(discovered); }

#[verifier::rlimit(10)]
fn admit_projection(before: &ea_namespace::Namespace<'_, '_>, plan: &Plan<'_>, result: &[u8],
    directory: u32, old_name: &[u8], new_name: &[u8],
    inode_budget: u32, node_budget: u64, byte_budget: u64)
    -> (r: Option<(Ghost<NamespaceView>, usize)>)
    requires before.wf(), plan.wf(), before.view() == plan.view().before,
        directory == plan.view().directory, old_name@ == plan.view().old_name,
        new_name@ == plan.view().new_name,
    ensures before.wf(), plan.wf(), match r {
        Some((certificate, entry)) => certified(certificate@, result@)
            && renamed(before.view().index.entries, certificate@.index.entries, entry,
                directory, old_name@, new_name@, plan.target, plan.generation)
            && before.view().index.entries[entry as int] == plan.view().selected,
        None => true,
    },
{
    proof {
        use_type_invariant(plan);
        selected_entry_projection_fields(plan.view());
    }
    let result_source = Snapshot::from_bytes(result);
    let after = match ea_namespace::inspect(&result_source, inode_budget, node_budget, byte_budget) {
        Some(after) => after, None => { return None; }
    };
    let entry = match check_entries(before.index(), after.index(), directory, old_name, new_name,
        plan.target, plan.generation, plan.logical, plan.record, plan.file_type) {
        Some(entry) => entry, None => { return None; }
    };
    let ghost selected = before.view().index.entries[entry as int];
    assert(selected.directory == plan.view().selected.directory);
    assert(selected.name == plan.view().selected.name);
    assert(selected.target == plan.view().selected.target);
    assert(selected.generation == plan.view().selected.generation);
    assert(selected.logical == plan.view().selected.logical);
    assert(selected.record == plan.view().selected.record);
    assert(selected.file_type == plan.view().selected.file_type);
    assert(selected == plan.view().selected);
    assert(certified(after.view(), result@));
    Some((Ghost(after.view()), entry))
}

#[verifier::rlimit(10)]
fn finish_candidate(plan: Plan<'_>, result: Vec<u8>, after: Ghost<NamespaceView>, entry: usize) -> (r: Update)
    requires plan.wf(), certified(after@, result@), image_bytes_match_plan(result@, plan.view()),
        renamed(plan.view().before.index.entries, after@.index.entries, entry, plan.view().directory,
            plan.view().old_name, plan.view().new_name, plan.view().target, plan.view().generation),
        plan.view().before.index.entries[entry as int] == plan.view().selected,
    ensures r.wf(), valid(r.view()), r.view().source == plan.view().source,
        r.view().directory == plan.view().directory, r.view().old_name == plan.view().old_name,
        r.view().new_name == plan.view().new_name, r.view().seconds == plan.view().seconds, r.view().nanos == plan.view().nanos,
{
    let ghost start = plan.view();
    let ghost view = UpdateView { result: result@, after: after@, entry, ..start };
    proof {
        assembled_result_keeps_the_plan(start, view);
        image_effect_survives_certificate_attachment(start, view);
        assemble_result(view);
    }
    Update { after: result, patches: plan.patches, checked: Ghost(view) }
}

#[verifier::rlimit(10)]
pub fn prepare(source: &Snapshot<'_>, directory: u32, old_name: &[u8], new_name: &[u8], seconds: i64, nanos: u32,
    inode_budget: u32, node_budget: u64, byte_budget: u64) -> (r: Result<Update, Error>)
    ensures match r { Ok(update) => update.wf() && valid(update.view()) && update.view().source == source.view()
        && update.view().directory == directory && update.view().old_name == old_name@ && update.view().new_name == new_name@
        && update.view().seconds == seconds && update.view().nanos == nanos,
        Err(_) => true },
{
    if source.partition_bytes() < 8192 || source.partition_bytes() > MAX_IMAGE_BYTES as u64 { return Err(Error::Invalid); }
    let before = match ea_namespace::inspect(source, inode_budget, node_budget, byte_budget) { Some(before) => before, None => { return Err(Error::Invalid); } };
    let plan = match build_plan(source, &before, directory, old_name, new_name, seconds, nanos) { Ok(plan) => plan, Err(e) => { return Err(e); } };
    let result = match materialize_plan(source, &plan) { Ok(result) => result, Err(e) => { return Err(e); } };
    let (after, changed_entry) = match admit_projection(&before, &plan, &result, directory, old_name, new_name, inode_budget, node_budget, byte_budget) {
        Some(checked) => checked, None => { return Err(Error::Rejected); }
    };
    Ok(finish_candidate(plan, result, after, changed_entry))
}

fn proper_name(name: &[u8]) -> (r: bool)
    ensures r == ns_rename_block::proper_name(name@),
{
    if name.len() == 0 || name.len() > 255 { return false; }
    if name.len() == 1 && name[0] == 46 || name.len() == 2 && name[0] == 46 && name[1] == 46 { return false; }
    let mut i = 0usize;
    while i < name.len()
        invariant 0 < name.len() <= 255, i <= name.len(), !(name.len() == 1 && name@[0] == 46), !(name.len() == 2 && name@[0] == 46 && name@[1] == 46),
            forall|j: int| 0 <= j < i ==> (#[trigger] name@[j]) != 0 && name@[j] != 47,
        decreases name.len() - i,
    { if name[i] == 0 || name[i] == 47 { return false; } i += 1; }
    true
}

pub proof fn every_prepared_rename_has_complete_EA_namespace_admission(v: UpdateView)
    requires valid(v),
    ensures certified(v.before, v.source), certified(v.after, v.result),
{ reveal(valid); reveal(planned); reveal(discovered); reveal(image_bytes_match_plan); }
pub proof fn a_prepared_rename_changes_one_name_and_keeps_its_source_identity(v: UpdateView)
    requires valid(v),
    ensures renamed(v.before.index.entries, v.after.index.entries, v.entry, v.directory, v.old_name, v.new_name, v.target, v.generation),
{ reveal(valid); reveal(planned); reveal(discovered); reveal(image_bytes_match_plan); }
pub proof fn prepared_renames_preserve_every_unrelated_source_byte(v: UpdateView, i: int)
    requires valid(v), 0 <= i < v.source.len(), !editable(i, v.directory_block, v.parent_position, v.target_position),
    ensures v.result[i] == v.source[i],
{ reveal(valid); reveal(planned); reveal(discovered); reveal(image_bytes_match_plan); }
pub proof fn prepared_renames_never_authorize_READONLY_source_images(v: UpdateView)
    requires valid(v),
    ensures !feature_policy::readonly(v.source.subrange(1024, 2048)),
{ reveal(valid); reveal(planned); reveal(discovered); reveal(image_bytes_match_plan); }

pub proof fn prepared_renames_apply_the_requested_inode_times(v: UpdateView)
    requires valid(v),
    ensures crate::inode_time_fields::seconds(v.parent_change.after, crate::inode_time_fields::Field::Ctime) == v.seconds,
        crate::inode_time_fields::nanoseconds(v.parent_change.after, crate::inode_time_fields::Field::Ctime) == v.nanos,
        crate::inode_time_fields::seconds(v.parent_change.after, crate::inode_time_fields::Field::Mtime) == v.seconds,
        crate::inode_time_fields::nanoseconds(v.parent_change.after, crate::inode_time_fields::Field::Mtime) == v.nanos,
        crate::inode_time_fields::seconds(v.target_change.after, crate::inode_time_fields::Field::Ctime) == v.seconds,
        crate::inode_time_fields::nanoseconds(v.target_change.after, crate::inode_time_fields::Field::Ctime) == v.nanos,
{
    reveal(valid); reveal(planned); reveal(discovered); reveal(ns_inode_touch::valid);
}

pub proof fn prepared_renames_target_only_the_checked_directory_and_source_inode_table_blocks(v: UpdateView, i: int)
    requires valid(v), 0 <= i < v.patches.len(),
    ensures v.patches[i].block == v.directory_block || v.patches[i].block as nat == v.parent_position / 4096
        || v.patches[i].block as nat == v.target_position / 4096,
        v.parent_position == v.before.allocation.ordinary[v.before.index.nodes.slots[v.directory as int].ordinal as int].parent.node.position,
        v.target_position == v.before.allocation.ordinary[v.before.index.nodes.slots[v.target as int].ordinal as int].parent.node.position,
{
    reveal(valid); reveal(planned); reveal(discovered);
}


pub proof fn candidate_images_are_certified_and_have_equal_length(v: UpdateView)
    requires valid(v),
    ensures certified(v.before, v.source), certified(v.after, v.result),
        v.result.len() == v.source.len(), 8192 <= v.source.len() <= MAX_IMAGE_BYTES,
{ reveal(valid); reveal(planned); reveal(discovered); reveal(image_bytes_match_plan); }

// Include inside ns_rename's verus! block. This turns exact sequence mutation
// plus complete full-key uniqueness into visible positive/negative lookup facts.
proof fn one_full_key_has_only_one_source_position(entries: Seq<EntryView>, a: int, b: int)
    requires crate::namespace_model::keys(entries).no_duplicates(),
        0 <= a < entries.len(), 0 <= b < entries.len(),
        entries[a].directory == entries[b].directory, entries[a].name == entries[b].name,
    ensures a == b,
{
    let keys = crate::namespace_model::keys(entries);
    assert(keys[a] == (entries[a].directory, entries[a].name));
    assert(keys[b] == (entries[b].directory, entries[b].name));
    assert(keys[a] == keys[b]);
    if a < b { assert(keys[a] != keys[b]); }
    if b < a { assert(keys[b] != keys[a]); }
}

proof fn exact_rename_removes_the_old_full_key_and_adds_the_new_full_key(
    before: Seq<EntryView>, after: Seq<EntryView>, entry: usize,
    directory: u32, old_name: Seq<u8>, new_name: Seq<u8>, target: u32, generation: u32)
    requires renamed(before, after, entry, directory, old_name, new_name, target, generation),
        crate::namespace_model::keys(before).no_duplicates(),
        !crate::namespace_model::has_name(before, directory, new_name),
    ensures crate::namespace_model::has_name(after, directory, new_name),
        !crate::namespace_model::has_name(after, directory, old_name),
{
    let changed = entry as int;
    assert(before[changed].directory == directory && before[changed].name == old_name);
    assert(after[changed].directory == directory && after[changed].name == new_name);
    assert(exists|i: int| 0 <= i < after.len()
        && (#[trigger] after[i]).directory == directory && after[i].name == new_name);
    assert(crate::namespace_model::has_name(after, directory, new_name));
    if old_name == new_name {
        assert(exists|i: int| 0 <= i < before.len()
            && (#[trigger] before[i]).directory == directory && before[i].name == new_name);
        assert(crate::namespace_model::has_name(before, directory, new_name));
        assert(false);
    }
    if crate::namespace_model::has_name(after, directory, old_name) {
        let i = choose|i: int| 0 <= i < after.len()
            && (#[trigger] after[i]).directory == directory && after[i].name == old_name;
        if i == changed {
            assert(old_name == new_name);
        } else {
            assert(after[i] == before[i]);
            one_full_key_has_only_one_source_position(before, i, changed);
            assert(i == changed);
        }
        assert(false);
    }
}

pub proof fn namespace_lookup_sees_the_exact_renamed_name(v: UpdateView)
    requires valid(v),
    ensures crate::namespace_model::has_name(v.after.index.entries, v.directory, v.new_name),
        !crate::namespace_model::has_name(v.after.index.entries, v.directory, v.old_name),
{
    assert(renamed(v.before.index.entries, v.after.index.entries, v.entry, v.directory,
        v.old_name, v.new_name, v.target, v.generation)
        && !crate::namespace_model::has_name(v.before.index.entries, v.directory, v.new_name)
        && crate::ea_directory_index::valid(v.before.index)) by {
        reveal(valid); reveal(planned); reveal(discovered); reveal(crate::ea_namespace::valid);
    }
    crate::ea_directory_index::full_namespace_keys_are_unique_without_a_hash_identity_assumption(v.before.index);
    exact_rename_removes_the_old_full_key_and_adds_the_new_full_key(v.before.index.entries,
        v.after.index.entries, v.entry, v.directory, v.old_name, v.new_name, v.target, v.generation);
}

}
