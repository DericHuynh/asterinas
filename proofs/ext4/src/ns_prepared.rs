// SPDX-License-Identifier: MPL-2.0

//! Affine prepared rename with exact owned before and after images.

use vstd::prelude::*;
use crate::{ea_namespace::NamespaceView, ns_mutation_model as model, ns_rename::{self, Update}};

verus! {

pub struct Prepared { before: Vec<u8>, epoch: u64, certificate: Ghost<NamespaceView>, update: Update }

impl Prepared {

    pub(crate) fn create(before: Vec<u8>, epoch: u64, certificate: Ghost<NamespaceView>, update: Update) -> (r: Self)
        requires 0 < before.len() <= model::MAX_IMAGE_BYTES, model::certified(certificate@, before@),
            update.wf(), ns_rename::valid(update.view()), update.view().source == before@,
            update.view().result.len() == before.len(), model::certified(update.view().after, update.view().result),
        ensures r.wf(), model::prepared_valid(r.view()), r.operation() == update.view(),
            r.view() == (model::PreparedView { epoch, before: before@, after: update.view().result,
                before_certificate: certificate@, after_certificate: update.view().after }),
    {
        assert(model::prepared_valid(model::PreparedView { epoch, before: before@, after: update.view().result,
            before_certificate: certificate@, after_certificate: update.view().after })) by { reveal(model::prepared_valid); }
        Prepared { before, epoch, certificate, update }
    }
    pub fn before_bytes(&self) -> (r: &[u8])
        ensures self.wf(), model::prepared_valid(self.view()), r@ == self.view().before,
    { proof { use_type_invariant(self); } &self.before }
    pub(crate) fn into_update(self) -> (r: Update)
        ensures r.wf(), ns_rename::valid(r.view()), r.view() == self.operation(),
            r.view().source == self.view().before, r.view().result == self.view().after,
            r.view().after == self.view().after_certificate,
    { proof { use_type_invariant(&self); } self.update }

    // Publication needs owned bytes and their certificate, not the complete
    // rename plan. Keep the operation representation inside this module.
    pub(crate) fn into_result(self) -> (r: (Vec<u8>, Ghost<NamespaceView>))
        ensures r.0@ == self.view().after, r.1@ == self.view().after_certificate,
            model::certified(r.1@, r.0@),
    {
        proof { use_type_invariant(&self); }
        self.update.into_result()
    }

    // The durable adapter reads the exact coalesced operation patches without
    // exposing them through the existing host-image publication API.
    pub(crate) fn patches(&self) -> (r: &crate::patch_set::PatchSet)
        ensures self.wf(), model::prepared_valid(self.view()), ns_rename::valid(self.operation()),
            r.wf(), r.view() == self.operation().patches,
            self.operation().source == self.view().before,
            self.operation().result == self.view().after,
            self.operation().after == self.view().after_certificate,
    { proof { use_type_invariant(self); } self.update.patches() }

    pub closed spec fn view(&self) -> model::PreparedView {
        model::PreparedView { epoch: self.epoch, before: self.before@, after: self.update.view().result,
            before_certificate: self.certificate@, after_certificate: self.update.view().after }
    }
    pub closed spec fn operation(&self) -> ns_rename::UpdateView { self.update.view() }
    pub closed spec fn wf(&self) -> bool {
        model::prepared_valid(self.view()) && self.update.wf() && ns_rename::valid(self.operation())
            && self.operation().source == self.view().before
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
    pub fn bytes(&self) -> (r: &[u8]) ensures self.wf(), model::prepared_valid(self.view()), r@ == self.view().after {
        proof { use_type_invariant(self); } self.update.bytes()
    }
    pub fn epoch(&self) -> (r: u64) ensures self.wf(), model::prepared_valid(self.view()), r == self.view().epoch {
        proof { use_type_invariant(self); } self.epoch
    }
}

pub proof fn prepared_operations_retain_their_exact_source_and_result(prepared: &Prepared)
    requires prepared.wf(),
    ensures model::prepared_valid(prepared.view()), ns_rename::valid(prepared.operation()),
        prepared.operation().source == prepared.view().before,
        prepared.operation().result == prepared.view().after,
        prepared.operation().after == prepared.view().after_certificate,
{ }

}
