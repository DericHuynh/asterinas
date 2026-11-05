// SPDX-License-Identifier: MPL-2.0

//! Owned immutable checkout for independent rename preparation.

use vstd::prelude::*;
use crate::{ea_namespace::NamespaceView, ns_mutation_model as model, ns_prepared::Prepared, ns_rename, snapshot::Snapshot};

verus! {

pub(crate) fn copy_bytes(raw: &[u8]) -> (r: Vec<u8>)
    requires raw.len() <= model::MAX_IMAGE_BYTES,
    ensures r@ == raw@,
{
    let mut copy = Vec::new(); let mut i = 0usize;
    while i < raw.len()
        invariant i <= raw.len() <= model::MAX_IMAGE_BYTES, copy@ == raw@.take(i as int),
        decreases raw.len() - i,
    { copy.push(raw[i]); assert(copy@ =~= raw@.take(i as int + 1)); i += 1; }
    assert(raw@.take(i as int) =~= raw@); copy
}

pub struct Checkout {
    bytes: Vec<u8>, epoch: u64, certificate: Ghost<NamespaceView>,
    inode_budget: u32, node_budget: u64, byte_budget: u64,
}

impl Checkout {

    pub(crate) fn capture(bytes: Vec<u8>, epoch: u64, certificate: Ghost<NamespaceView>, inode_budget: u32, node_budget: u64, byte_budget: u64) -> (r: Self)
        requires 0 < bytes.len() <= model::MAX_IMAGE_BYTES, model::certified(certificate@, bytes@),
        ensures r.wf(), r.source_view() == bytes@, r.epoch_view() == epoch, r.namespace_view() == certificate@,
    { Checkout { bytes, epoch, certificate, inode_budget, node_budget, byte_budget } }

    pub closed spec fn source_view(&self) -> Seq<u8> { self.bytes@ }
    pub closed spec fn epoch_view(&self) -> u64 { self.epoch }
    pub closed spec fn namespace_view(&self) -> NamespaceView { self.certificate@ }
    pub open spec fn wf(&self) -> bool {
        0 < self.source_view().len() <= model::MAX_IMAGE_BYTES && model::certified(self.namespace_view(), self.source_view())
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn bytes(&self) -> (r: &[u8]) ensures self.wf(), r@ == self.source_view() {
        proof { use_type_invariant(self); } &self.bytes
    }
    pub fn epoch(&self) -> (r: u64) ensures self.wf(), r == self.epoch_view() {
        proof { use_type_invariant(self); } self.epoch
    }
    pub fn prepare_rename_noreplace(self, directory: u32, old_name: &[u8], new_name: &[u8], seconds: i64, nanos: u32)
        -> (r: Result<Prepared, ns_rename::Error>)
        ensures match r { Ok(prepared) => prepared.wf() && model::prepared_valid(prepared.view())
            && prepared.view().epoch == self.epoch_view() && prepared.view().before == self.source_view()
            && prepared.operation().directory == directory && prepared.operation().old_name == old_name@
            && prepared.operation().new_name == new_name@ && prepared.operation().seconds == seconds as int
            && prepared.operation().nanos == nanos as nat && ns_rename::valid(prepared.operation()), Err(_) => true },
    {
        proof { use_type_invariant(&self); }
        let source = Snapshot::from_bytes(&self.bytes);
        let update = match ns_rename::prepare(&source, directory, old_name, new_name, seconds, nanos,
            self.inode_budget, self.node_budget, self.byte_budget) {
            Ok(update) => update, Err(error) => { return Err(error); }
        };
        let ghost proposal = model::PreparedView { epoch: self.epoch, before: self.bytes@,
            after: update.view().result, before_certificate: self.certificate@, after_certificate: update.view().after };
        proof { ns_rename::candidate_images_are_certified_and_have_equal_length(update.view()); }
        assert(model::prepared_valid(proposal)) by { reveal(model::prepared_valid); }
        Ok(Prepared::create(self.bytes, self.epoch, self.certificate, update))
    }
}

}
