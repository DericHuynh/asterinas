// SPDX-License-Identifier: MPL-2.0

//! Concurrent preparation and atomic host-image namespace publication.
//! Owned checkouts keep old readers immutable. Publication requires the exact
//! source revision and complete source bytes; every successful replacement
//! carries a checked EA namespace and exact supported edit semantics. This host core
//! grants no credentials, journal acknowledgement or CortenMM/OSTD authority.

use vstd::prelude::*;
pub use crate::{ns_checkout::Checkout, ns_prepared::Prepared, ns_edit_prepared::EditPrepared,
    ns_file_rename_prepared::FileRenamePrepared, ns_exchange_prepared::ExchangePrepared};
use crate::ns_checkout::copy_bytes;
use crate::{bytes, ea_namespace::{self, NamespaceView}, ns_mutation_model as model,
    ns_namespace_edit, ns_file_rename, ns_exchange, ns_rename, snapshot::Snapshot};

verus! {


pub struct Store {
    bytes: Vec<u8>, epoch: u64, limit: u64, certificate: Ghost<NamespaceView>,
    inode_budget: u32, node_budget: u64, byte_budget: u64,
}

#[derive(Debug, PartialEq, Eq)]
pub enum PublishError { Stale, SourceMismatch, Exhausted }

proof fn valid_revision_bounds(v: model::View)
    requires model::valid(v),
    ensures v.epoch <= v.limit,
{ reveal(model::valid); }

proof fn checked_source_and_revision_allow_publication(v: model::View, p: model::PreparedView)
    requires model::valid(v), model::prepared_valid(p), v.epoch == p.epoch, v.source == p.before,
        v.epoch < v.limit, v.epoch < u64::MAX,
    ensures model::enabled(v, p), model::valid(model::publish_step(v, p)),
        model::step(v, model::Event::Publish(p)) == model::publish_step(v, p),
        model::publish_step(v, p) == (model::View { epoch: (v.epoch as nat + 1) as u64,
            limit: v.limit, source: p.after, certificate: p.after_certificate }),
{
    assert(model::enabled(v, p));
    model::invariant_preserved_by_publication(v, p);
}

impl Store {
    pub closed spec fn view(&self) -> model::View {
        model::View { epoch: self.epoch, limit: self.limit, source: self.bytes@, certificate: self.certificate@ }
    }
    pub open spec fn wf(&self) -> bool { model::valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn open(raw: &[u8], limit: u64, inode_budget: u32, node_budget: u64, byte_budget: u64) -> (r: Option<Self>)
        ensures match r { Some(store) => store.wf() && model::valid(store.view())
            && store.view().epoch == 0 && store.view().limit == limit && store.view().source == raw@, None => true },
    {
        if raw.len() == 0 || raw.len() > model::MAX_IMAGE_BYTES as usize { return None; }
        let bytes = copy_bytes(raw);
        let source = Snapshot::from_bytes(&bytes);
        let namespace = match ea_namespace::inspect(&source, inode_budget, node_budget, byte_budget) {
            Some(namespace) => namespace, None => { return None; }
        };
        let ghost certificate = namespace.view();
        let ghost v = model::View { epoch: 0, limit, source: bytes@, certificate };
        assert(model::valid(v)) by { reveal(model::valid); }
        Some(Store { bytes, epoch: 0, limit, certificate: Ghost(certificate), inode_budget, node_budget, byte_budget })
    }
    pub fn epoch(&self) -> (r: u64) ensures self.wf(), model::valid(self.view()), r == self.view().epoch {
        proof { use_type_invariant(self); } self.epoch
    }
    pub fn bytes(&self) -> (r: &[u8]) ensures self.wf(), model::valid(self.view()), r@ == self.view().source {
        proof { use_type_invariant(self); } &self.bytes
    }
    pub fn checkout(&self) -> (r: Checkout)
        ensures self.wf(), model::valid(self.view()), r.wf(), r.epoch_view() == self.view().epoch,
            r.source_view() == self.view().source, r.namespace_view() == self.view().certificate,
    {
        proof { use_type_invariant(self); reveal(model::valid); }
        Checkout::capture(copy_bytes(&self.bytes), self.epoch, self.certificate, self.inode_budget, self.node_budget, self.byte_budget)
    }
    // The admission decision and owned replacement are constructed through a
    // shared borrow. The public mutable method performs only the final swap.
    #[verifier::rlimit(20)]
    fn replacement(&self, prepared: Prepared) -> (r: Result<Store, PublishError>)
        ensures self.wf(), model::valid(self.view()), match r {
            Ok(next) => next.wf() && model::valid(next.view())
                && model::enabled(self.view(), prepared.view())
                && next.view() == model::step(self.view(), model::Event::Publish(prepared.view()))
                && next.view() == model::publish_step(self.view(), prepared.view()),
            Err(error) => model::step(self.view(), model::Event::Publish(prepared.view())) == self.view()
                && match error {
                    PublishError::Stale => self.view().epoch != prepared.view().epoch,
                    PublishError::SourceMismatch => self.view().epoch == prepared.view().epoch
                        && self.view().source != prepared.view().before,
                    PublishError::Exhausted => self.view().epoch == prepared.view().epoch
                        && self.view().source == prepared.view().before
                        && (self.view().epoch == self.view().limit || self.view().epoch == u64::MAX),
                },
        },
    {
        hide(vstd::slice::axiom_spec_len);
        hide(model::enabled); hide(model::step); hide(model::publish_step);
        proof { use_type_invariant(self); }
        let ghost old_view = self.view(); let ghost proposal = prepared.view();
        let expected_epoch = prepared.epoch();
        proof { valid_revision_bounds(old_view); }
        if self.epoch != expected_epoch {
            proof { model::a_conflicting_source_or_epoch_rejects_without_publication(old_view, proposal); }
            return Err(PublishError::Stale);
        }
        if !bytes::equal(&self.bytes, prepared.before_bytes()) {
            proof { model::a_conflicting_source_or_epoch_rejects_without_publication(old_view, proposal); }
            return Err(PublishError::SourceMismatch);
        }
        if self.epoch == self.limit || self.epoch == u64::MAX {
            proof { model::exhausted_publication_counters_never_wrap(old_view, proposal); }
            return Err(PublishError::Exhausted);
        }
        proof { checked_source_and_revision_allow_publication(old_view, proposal); }
        let (bytes, certificate) = prepared.into_result();
        let epoch = self.epoch + 1;
        let ghost replacement = model::View { epoch, limit: self.limit, source: bytes@, certificate: certificate@ };
        assert(replacement == model::publish_step(old_view, proposal));
        assert(model::valid(replacement));
        let next = Store { bytes, epoch, limit: self.limit, certificate,
            inode_budget: self.inode_budget, node_budget: self.node_budget, byte_budget: self.byte_budget };
        Ok(next)
    }
    pub fn publish(&mut self, prepared: Prepared) -> (r: Result<u64, PublishError>)
        ensures final(self).wf(), model::valid(final(self).view()),
            final(self).view() == model::step(old(self).view(), model::Event::Publish(prepared.view())),
            match r {
            Ok(epoch) => model::enabled(old(self).view(), prepared.view())
                && final(self).view() == model::publish_step(old(self).view(), prepared.view()) && epoch == final(self).view().epoch,
            Err(error) => final(self).view() == old(self).view() && match error {
                PublishError::Stale => old(self).view().epoch != prepared.view().epoch,
                PublishError::SourceMismatch => old(self).view().epoch == prepared.view().epoch
                    && old(self).view().source != prepared.view().before,
                PublishError::Exhausted => old(self).view().epoch == prepared.view().epoch
                    && old(self).view().source == prepared.view().before
                    && (old(self).view().epoch == old(self).view().limit || old(self).view().epoch == u64::MAX),
            },
        },
    {
        hide(model::enabled); hide(model::step); hide(model::publish_step);
        proof { use_type_invariant(&*self); }
        let ghost current = self.view(); let ghost proposal = prepared.view();
        match self.replacement(prepared) {
            Ok(next) => {
                let epoch = next.epoch;
                assert(next.view() == model::step(current, model::Event::Publish(proposal)));
                *self = next;
                Ok(epoch)
            },
            Err(error) => Err(error),
        }
    }
    // Namespace edits retain their private operation witness through the same
    // exact revision/source admission boundary as the original rename path.
    #[verifier::rlimit(20)]
    fn edit_replacement(&self, prepared: EditPrepared) -> (r: Result<Store, PublishError>)
        ensures self.wf(), model::valid(self.view()), match r {
            Ok(next) => next.wf() && model::valid(next.view())
                && model::enabled(self.view(), prepared.view())
                && next.view() == model::step(self.view(), model::Event::Publish(prepared.view()))
                && next.view() == model::publish_step(self.view(), prepared.view()),
            Err(error) => model::step(self.view(), model::Event::Publish(prepared.view())) == self.view()
                && match error {
                    PublishError::Stale => self.view().epoch != prepared.view().epoch,
                    PublishError::SourceMismatch => self.view().epoch == prepared.view().epoch
                        && self.view().source != prepared.view().before,
                    PublishError::Exhausted => self.view().epoch == prepared.view().epoch
                        && self.view().source == prepared.view().before
                        && (self.view().epoch == self.view().limit || self.view().epoch == u64::MAX),
                },
        },
    {
        hide(vstd::slice::axiom_spec_len);
        hide(model::enabled); hide(model::step); hide(model::publish_step);
        proof { use_type_invariant(self); }
        let ghost old_view = self.view(); let ghost proposal = prepared.view();
        let expected_epoch = prepared.epoch();
        proof { valid_revision_bounds(old_view); }
        if self.epoch != expected_epoch {
            proof { model::a_conflicting_source_or_epoch_rejects_without_publication(old_view, proposal); }
            return Err(PublishError::Stale);
        }
        if !bytes::equal(&self.bytes, prepared.before_bytes()) {
            proof { model::a_conflicting_source_or_epoch_rejects_without_publication(old_view, proposal); }
            return Err(PublishError::SourceMismatch);
        }
        if self.epoch == self.limit || self.epoch == u64::MAX {
            proof { model::exhausted_publication_counters_never_wrap(old_view, proposal); }
            return Err(PublishError::Exhausted);
        }
        proof { checked_source_and_revision_allow_publication(old_view, proposal); }
        let (bytes, certificate) = prepared.into_result();
        let epoch = self.epoch + 1;
        let ghost replacement = model::View { epoch, limit: self.limit, source: bytes@, certificate: certificate@ };
        assert(replacement == model::publish_step(old_view, proposal));
        assert(model::valid(replacement));
        let next = Store { bytes, epoch, limit: self.limit, certificate,
            inode_budget: self.inode_budget, node_budget: self.node_budget, byte_budget: self.byte_budget };
        Ok(next)
    }
    pub fn publish_edit(&mut self, prepared: EditPrepared) -> (r: Result<u64, PublishError>)
        ensures final(self).wf(), model::valid(final(self).view()),
            final(self).view() == model::step(old(self).view(), model::Event::Publish(prepared.view())),
            match r {
            Ok(epoch) => model::enabled(old(self).view(), prepared.view())
                && final(self).view() == model::publish_step(old(self).view(), prepared.view()) && epoch == final(self).view().epoch,
            Err(error) => final(self).view() == old(self).view() && match error {
                PublishError::Stale => old(self).view().epoch != prepared.view().epoch,
                PublishError::SourceMismatch => old(self).view().epoch == prepared.view().epoch
                    && old(self).view().source != prepared.view().before,
                PublishError::Exhausted => old(self).view().epoch == prepared.view().epoch
                    && old(self).view().source == prepared.view().before
                    && (old(self).view().epoch == old(self).view().limit || old(self).view().epoch == u64::MAX),
            },
        },
    {
        hide(model::enabled); hide(model::step); hide(model::publish_step);
        proof { use_type_invariant(&*self); }
        let ghost current = self.view(); let ghost proposal = prepared.view();
        match self.edit_replacement(prepared) {
            Ok(next) => {
                let epoch = next.epoch;
                assert(next.view() == model::step(current, model::Event::Publish(proposal)));
                *self = next;
                Ok(epoch)
            },
            Err(error) => Err(error),
        }
    }
    // Regular-file replacements and exchanges retain their private operation witness through the same
    // exact revision/source admission boundary as the original rename path.
    #[verifier::rlimit(20)]
    fn file_rename_replacement(&self, prepared: FileRenamePrepared) -> (r: Result<Store, PublishError>)
        ensures self.wf(), model::valid(self.view()), match r {
            Ok(next) => next.wf() && model::valid(next.view())
                && model::enabled(self.view(), prepared.view())
                && next.view() == model::step(self.view(), model::Event::Publish(prepared.view()))
                && next.view() == model::publish_step(self.view(), prepared.view()),
            Err(error) => model::step(self.view(), model::Event::Publish(prepared.view())) == self.view()
                && match error {
                    PublishError::Stale => self.view().epoch != prepared.view().epoch,
                    PublishError::SourceMismatch => self.view().epoch == prepared.view().epoch
                        && self.view().source != prepared.view().before,
                    PublishError::Exhausted => self.view().epoch == prepared.view().epoch
                        && self.view().source == prepared.view().before
                        && (self.view().epoch == self.view().limit || self.view().epoch == u64::MAX),
                },
        },
    {
        hide(vstd::slice::axiom_spec_len);
        hide(model::enabled); hide(model::step); hide(model::publish_step);
        proof { use_type_invariant(self); }
        let ghost old_view = self.view(); let ghost proposal = prepared.view();
        let expected_epoch = prepared.epoch();
        proof { valid_revision_bounds(old_view); }
        if self.epoch != expected_epoch {
            proof { model::a_conflicting_source_or_epoch_rejects_without_publication(old_view, proposal); }
            return Err(PublishError::Stale);
        }
        if !bytes::equal(&self.bytes, prepared.before_bytes()) {
            proof { model::a_conflicting_source_or_epoch_rejects_without_publication(old_view, proposal); }
            return Err(PublishError::SourceMismatch);
        }
        if self.epoch == self.limit || self.epoch == u64::MAX {
            proof { model::exhausted_publication_counters_never_wrap(old_view, proposal); }
            return Err(PublishError::Exhausted);
        }
        proof { checked_source_and_revision_allow_publication(old_view, proposal); }
        let (bytes, certificate) = prepared.into_result();
        let epoch = self.epoch + 1;
        let ghost replacement = model::View { epoch, limit: self.limit, source: bytes@, certificate: certificate@ };
        assert(replacement == model::publish_step(old_view, proposal));
        assert(model::valid(replacement));
        let next = Store { bytes, epoch, limit: self.limit, certificate,
            inode_budget: self.inode_budget, node_budget: self.node_budget, byte_budget: self.byte_budget };
        Ok(next)
    }
    pub fn publish_file_rename(&mut self, prepared: FileRenamePrepared) -> (r: Result<u64, PublishError>)
        ensures final(self).wf(), model::valid(final(self).view()),
            final(self).view() == model::step(old(self).view(), model::Event::Publish(prepared.view())),
            match r {
            Ok(epoch) => model::enabled(old(self).view(), prepared.view())
                && final(self).view() == model::publish_step(old(self).view(), prepared.view()) && epoch == final(self).view().epoch,
            Err(error) => final(self).view() == old(self).view() && match error {
                PublishError::Stale => old(self).view().epoch != prepared.view().epoch,
                PublishError::SourceMismatch => old(self).view().epoch == prepared.view().epoch
                    && old(self).view().source != prepared.view().before,
                PublishError::Exhausted => old(self).view().epoch == prepared.view().epoch
                    && old(self).view().source == prepared.view().before
                    && (old(self).view().epoch == old(self).view().limit || old(self).view().epoch == u64::MAX),
            },
        },
    {
        hide(model::enabled); hide(model::step); hide(model::publish_step);
        proof { use_type_invariant(&*self); }
        let ghost current = self.view(); let ghost proposal = prepared.view();
        match self.file_rename_replacement(prepared) {
            Ok(next) => {
                let epoch = next.epoch;
                assert(next.view() == model::step(current, model::Event::Publish(proposal)));
                *self = next;
                Ok(epoch)
            },
            Err(error) => Err(error),
        }
    }
    // Ordinary namespace exchanges retain their private operation witness through the same
    // exact revision/source admission boundary as the original rename path.
    #[verifier::rlimit(20)]
    fn exchange_replacement(&self, prepared: ExchangePrepared) -> (r: Result<Store, PublishError>)
        ensures self.wf(), model::valid(self.view()), match r {
            Ok(next) => next.wf() && model::valid(next.view())
                && model::enabled(self.view(), prepared.view())
                && next.view() == model::step(self.view(), model::Event::Publish(prepared.view()))
                && next.view() == model::publish_step(self.view(), prepared.view()),
            Err(error) => model::step(self.view(), model::Event::Publish(prepared.view())) == self.view()
                && match error {
                    PublishError::Stale => self.view().epoch != prepared.view().epoch,
                    PublishError::SourceMismatch => self.view().epoch == prepared.view().epoch
                        && self.view().source != prepared.view().before,
                    PublishError::Exhausted => self.view().epoch == prepared.view().epoch
                        && self.view().source == prepared.view().before
                        && (self.view().epoch == self.view().limit || self.view().epoch == u64::MAX),
                },
        },
    {
        hide(vstd::slice::axiom_spec_len);
        hide(model::enabled); hide(model::step); hide(model::publish_step);
        proof { use_type_invariant(self); }
        let ghost old_view = self.view(); let ghost proposal = prepared.view();
        let expected_epoch = prepared.epoch();
        proof { valid_revision_bounds(old_view); }
        if self.epoch != expected_epoch {
            proof { model::a_conflicting_source_or_epoch_rejects_without_publication(old_view, proposal); }
            return Err(PublishError::Stale);
        }
        if !bytes::equal(&self.bytes, prepared.before_bytes()) {
            proof { model::a_conflicting_source_or_epoch_rejects_without_publication(old_view, proposal); }
            return Err(PublishError::SourceMismatch);
        }
        if self.epoch == self.limit || self.epoch == u64::MAX {
            proof { model::exhausted_publication_counters_never_wrap(old_view, proposal); }
            return Err(PublishError::Exhausted);
        }
        proof { checked_source_and_revision_allow_publication(old_view, proposal); }
        let (bytes, certificate) = prepared.into_result();
        let epoch = self.epoch + 1;
        let ghost replacement = model::View { epoch, limit: self.limit, source: bytes@, certificate: certificate@ };
        assert(replacement == model::publish_step(old_view, proposal));
        assert(model::valid(replacement));
        let next = Store { bytes, epoch, limit: self.limit, certificate,
            inode_budget: self.inode_budget, node_budget: self.node_budget, byte_budget: self.byte_budget };
        Ok(next)
    }
    pub fn publish_exchange(&mut self, prepared: ExchangePrepared) -> (r: Result<u64, PublishError>)
        ensures final(self).wf(), model::valid(final(self).view()),
            final(self).view() == model::step(old(self).view(), model::Event::Publish(prepared.view())),
            match r {
            Ok(epoch) => model::enabled(old(self).view(), prepared.view())
                && final(self).view() == model::publish_step(old(self).view(), prepared.view()) && epoch == final(self).view().epoch,
            Err(error) => final(self).view() == old(self).view() && match error {
                PublishError::Stale => old(self).view().epoch != prepared.view().epoch,
                PublishError::SourceMismatch => old(self).view().epoch == prepared.view().epoch
                    && old(self).view().source != prepared.view().before,
                PublishError::Exhausted => old(self).view().epoch == prepared.view().epoch
                    && old(self).view().source == prepared.view().before
                    && (old(self).view().epoch == old(self).view().limit || old(self).view().epoch == u64::MAX),
            },
        },
    {
        hide(model::enabled); hide(model::step); hide(model::publish_step);
        proof { use_type_invariant(&*self); }
        let ghost current = self.view(); let ghost proposal = prepared.view();
        match self.exchange_replacement(prepared) {
            Ok(next) => {
                let epoch = next.epoch;
                assert(next.view() == model::step(current, model::Event::Publish(proposal)));
                *self = next;
                Ok(epoch)
            },
            Err(error) => Err(error),
        }
    }
}


pub proof fn accepted_mutations_preserve_admission_and_the_exact_operation(current: model::View, prepared: &Prepared)
    requires model::valid(current), prepared.wf(), model::enabled(current, prepared.view()),
    ensures model::valid(model::publish_step(current, prepared.view())),
        ns_rename::valid(prepared.operation()),
        model::publish_step(current, prepared.view()).source == prepared.operation().result,
        model::publish_step(current, prepared.view()).certificate == prepared.operation().after,
        model::publish_step(current, prepared.view()).epoch > current.epoch,
{ crate::ns_prepared::prepared_operations_retain_their_exact_source_and_result(prepared); model::invariant_preserved_by_publication(current, prepared.view()); }


pub proof fn accepted_edits_preserve_admission_and_the_exact_operation(current: model::View, prepared: &EditPrepared)
    requires model::valid(current), prepared.wf(), model::enabled(current, prepared.view()),
    ensures model::valid(model::publish_step(current, prepared.view())),
        ns_namespace_edit::valid(prepared.operation()),
        ns_namespace_edit::exact_operation(prepared.operation()),
        model::publish_step(current, prepared.view()).source == prepared.operation().result,
        model::publish_step(current, prepared.view()).certificate == prepared.operation().after,
        model::publish_step(current, prepared.view()).epoch > current.epoch,
{
    crate::ns_edit_prepared::prepared_edits_retain_their_exact_source_and_result(prepared);
    ns_namespace_edit::prepared_edits_have_exact_operation(prepared.operation());
    model::invariant_preserved_by_publication(current, prepared.view());
}


pub proof fn accepted_file_renames_preserve_admission_and_the_exact_operation(current: model::View, prepared: &FileRenamePrepared)
    requires model::valid(current), prepared.wf(), model::enabled(current, prepared.view()),
    ensures model::valid(model::publish_step(current, prepared.view())),
        ns_file_rename::valid(prepared.operation()),
        ns_file_rename::exact_operation(prepared.operation()),
        model::publish_step(current, prepared.view()).source == prepared.operation().result,
        model::publish_step(current, prepared.view()).certificate == prepared.operation().after,
        model::publish_step(current, prepared.view()).epoch > current.epoch,
{
    crate::ns_file_rename_prepared::prepared_file_renames_retain_their_exact_source_and_result(prepared);
    ns_file_rename::prepared_edits_have_exact_operation(prepared.operation());
    model::invariant_preserved_by_publication(current, prepared.view());
}

pub proof fn accepted_exchanges_preserve_admission_and_the_exact_operation(current: model::View, prepared: &ExchangePrepared)
    requires model::valid(current), prepared.wf(), model::enabled(current, prepared.view()),
    ensures model::valid(model::publish_step(current, prepared.view())),
        ns_exchange::valid(prepared.operation()),
        ns_exchange::exact_operation(prepared.operation()),
        model::publish_step(current, prepared.view()).source == prepared.operation().result,
        model::publish_step(current, prepared.view()).certificate == prepared.operation().after,
        model::publish_step(current, prepared.view()).epoch > current.epoch,
{
    crate::ns_exchange_prepared::prepared_exchanges_retain_their_exact_source_and_result(prepared);
    ns_exchange::prepared_edits_have_exact_operation(prepared.operation());
    model::invariant_preserved_by_publication(current, prepared.view());
}

}
