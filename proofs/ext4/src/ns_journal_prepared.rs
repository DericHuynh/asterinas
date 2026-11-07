// SPDX-License-Identifier: MPL-2.0

//! Typed prepared namespace operations at the durable journal boundary.
//! The owned operation retains its exact source, result and coalesced patches.
//! Reading these candidates grants no commit, device or publication authority.

use vstd::prelude::*;
use crate::{ns_edit_prepared::EditPrepared, ns_exchange::{self, UpdateView as ExchangeView},
    ns_exchange_prepared::ExchangePrepared, ns_file_rename::{self, UpdateView as FileRenameView},
    ns_file_rename_prepared::FileRenamePrepared, ns_mutation_model::{self as model, PreparedView},
    ns_namespace_edit::{self, UpdateView as EditView}, ns_prepared,
    ns_rename::{self, UpdateView as RenameView}, patch_set::{self, PatchSet}, transaction::ImageView};

verus! {

// Sequence indirection keeps the wide typed views out of the native datatype
// constructor fields. Every admitted operation has exactly one typed witness.
pub enum Operation {
    Rename(Seq<RenameView>), Edit(Seq<EditView>),
    FileRename(Seq<FileRenameView>), Exchange(Seq<ExchangeView>),
}

pub open spec fn patches(operation: Operation) -> Seq<ImageView> {
    match operation {
        Operation::Rename(v) => v[0].patches, Operation::Edit(v) => v[0].patches,
        Operation::FileRename(v) => v[0].patches, Operation::Exchange(v) => v[0].patches,
    }
}

#[verifier::opaque]
pub open spec fn valid_operation(operation: Operation, prepared: PreparedView) -> bool {
    &&& model::prepared_valid(prepared)
    &&& patch_set::valid(patches(operation))
    &&& prepared.after == patch_set::apply(prepared.before, patches(operation))
    &&& match operation {
        Operation::Rename(v) => v.len() == 1 && ns_rename::valid(v[0])
            && v[0].source == prepared.before && v[0].result == prepared.after
            && v[0].after == prepared.after_certificate,
        Operation::Edit(v) => v.len() == 1 && ns_namespace_edit::valid(v[0]) && ns_namespace_edit::exact_operation(v[0])
            && v[0].source == prepared.before && v[0].result == prepared.after
            && v[0].after == prepared.after_certificate,
        Operation::FileRename(v) => v.len() == 1 && ns_file_rename::valid(v[0]) && ns_file_rename::exact_operation(v[0])
            && v[0].source == prepared.before && v[0].result == prepared.after
            && v[0].after == prepared.after_certificate,
        Operation::Exchange(v) => v.len() == 1 && ns_exchange::valid(v[0]) && ns_exchange::exact_operation(v[0])
            && v[0].source == prepared.before && v[0].result == prepared.after
            && v[0].after == prepared.after_certificate,
    }
}

enum Kind {
    Rename(ns_prepared::Prepared), Edit(EditPrepared),
    FileRename(FileRenamePrepared), Exchange(ExchangePrepared),
}

pub struct Prepared { inner: Kind }

impl Prepared {
    pub fn rename(prepared: ns_prepared::Prepared) -> (r: Self)
        ensures r.wf(), r.view() == prepared.view(),
            r.operation() == Operation::Rename(seq![prepared.operation()]),
            valid_operation(r.operation(), r.view()),
    {
        let _ = prepared.epoch();
        let result = Prepared { inner: Kind::Rename(prepared) };
        proof { a_prepared_operation_retains_its_exact_patches(&result); }
        result
    }

    pub fn edit(prepared: EditPrepared) -> (r: Self)
        ensures r.wf(), r.view() == prepared.view(),
            r.operation() == Operation::Edit(seq![prepared.operation()]),
            valid_operation(r.operation(), r.view()),
    {
        let _ = prepared.epoch();
        let result = Prepared { inner: Kind::Edit(prepared) };
        proof { a_prepared_operation_retains_its_exact_patches(&result); }
        result
    }

    pub fn file_rename(prepared: FileRenamePrepared) -> (r: Self)
        ensures r.wf(), r.view() == prepared.view(),
            r.operation() == Operation::FileRename(seq![prepared.operation()]),
            valid_operation(r.operation(), r.view()),
    {
        let _ = prepared.epoch();
        let result = Prepared { inner: Kind::FileRename(prepared) };
        proof { a_prepared_operation_retains_its_exact_patches(&result); }
        result
    }

    pub fn exchange(prepared: ExchangePrepared) -> (r: Self)
        ensures r.wf(), r.view() == prepared.view(),
            r.operation() == Operation::Exchange(seq![prepared.operation()]),
            valid_operation(r.operation(), r.view()),
    {
        let _ = prepared.epoch();
        let result = Prepared { inner: Kind::Exchange(prepared) };
        proof { a_prepared_operation_retains_its_exact_patches(&result); }
        result
    }

    pub closed spec fn view(&self) -> PreparedView {
        match &self.inner {
            Kind::Rename(p) => p.view(), Kind::Edit(p) => p.view(),
            Kind::FileRename(p) => p.view(), Kind::Exchange(p) => p.view(),
        }
    }
    pub closed spec fn operation(&self) -> Operation {
        match &self.inner {
            Kind::Rename(p) => Operation::Rename(seq![p.operation()]), Kind::Edit(p) => Operation::Edit(seq![p.operation()]),
            Kind::FileRename(p) => Operation::FileRename(seq![p.operation()]), Kind::Exchange(p) => Operation::Exchange(seq![p.operation()]),
        }
    }
    pub closed spec fn wf(&self) -> bool {
        match &self.inner {
            Kind::Rename(p) => p.wf(), Kind::Edit(p) => p.wf(),
            Kind::FileRename(p) => p.wf(), Kind::Exchange(p) => p.wf(),
        }
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }

    pub fn before_bytes(&self) -> (r: &[u8])
        ensures self.wf(), valid_operation(self.operation(), self.view()), r@ == self.view().before,
    {
        proof { use_type_invariant(self); a_prepared_operation_retains_its_exact_patches(self); }
        match &self.inner {
            Kind::Rename(p) => p.before_bytes(), Kind::Edit(p) => p.before_bytes(),
            Kind::FileRename(p) => p.before_bytes(), Kind::Exchange(p) => p.before_bytes(),
        }
    }
    pub fn bytes(&self) -> (r: &[u8])
        ensures self.wf(), valid_operation(self.operation(), self.view()), r@ == self.view().after,
    {
        proof { use_type_invariant(self); a_prepared_operation_retains_its_exact_patches(self); }
        match &self.inner {
            Kind::Rename(p) => p.bytes(), Kind::Edit(p) => p.bytes(),
            Kind::FileRename(p) => p.bytes(), Kind::Exchange(p) => p.bytes(),
        }
    }
    pub fn epoch(&self) -> (r: u64)
        ensures self.wf(), valid_operation(self.operation(), self.view()), r == self.view().epoch,
    {
        proof { use_type_invariant(self); a_prepared_operation_retains_its_exact_patches(self); }
        match &self.inner {
            Kind::Rename(p) => p.epoch(), Kind::Edit(p) => p.epoch(),
            Kind::FileRename(p) => p.epoch(), Kind::Exchange(p) => p.epoch(),
        }
    }
    pub(crate) fn patches(&self) -> (r: &PatchSet)
        ensures self.wf(), valid_operation(self.operation(), self.view()), r.wf(),
            r.view() == patches(self.operation()),
    {
        proof { use_type_invariant(self); a_prepared_operation_retains_its_exact_patches(self); }
        match &self.inner {
            Kind::Rename(p) => p.patches(), Kind::Edit(p) => p.patches(),
            Kind::FileRename(p) => p.patches(), Kind::Exchange(p) => p.patches(),
        }
    }
}

// Keep factory proofs independent of the large typed operation predicates.
pub proof fn operation_facts(operation: Operation, prepared: PreparedView)
    requires valid_operation(operation, prepared),
    ensures model::prepared_valid(prepared), patch_set::valid(patches(operation)),
        prepared.after == patch_set::apply(prepared.before, patches(operation)),
{ reveal(valid_operation); }

// Each typed operation is summarized in its own prover context. Callers keep
// the full source discovery and encoding predicates opaque.
proof fn rename_operation_is_valid(operation: RenameView, prepared: PreparedView)
    requires ns_rename::valid(operation), model::prepared_valid(prepared),
        operation.source == prepared.before, operation.result == prepared.after,
        operation.after == prepared.after_certificate,
    ensures valid_operation(Operation::Rename(seq![operation]), prepared),
{
    reveal(ns_rename::valid);
    reveal(ns_rename::planned);
    reveal(ns_rename::image_bytes_match_plan);
    reveal(valid_operation);
}

proof fn edit_operation_is_valid(operation: EditView, prepared: PreparedView)
    requires ns_namespace_edit::valid(operation), model::prepared_valid(prepared),
        operation.source == prepared.before, operation.result == prepared.after,
        operation.after == prepared.after_certificate,
    ensures valid_operation(Operation::Edit(seq![operation]), prepared),
{
    reveal(ns_namespace_edit::valid);
    reveal(valid_operation);
}

proof fn file_rename_operation_is_valid(operation: FileRenameView, prepared: PreparedView)
    requires ns_file_rename::valid(operation), model::prepared_valid(prepared),
        operation.source == prepared.before, operation.result == prepared.after,
        operation.after == prepared.after_certificate,
    ensures valid_operation(Operation::FileRename(seq![operation]), prepared),
{
    reveal(ns_file_rename::valid);
    reveal(valid_operation);
}

proof fn exchange_operation_is_valid(operation: ExchangeView, prepared: PreparedView)
    requires ns_exchange::valid(operation), model::prepared_valid(prepared),
        operation.source == prepared.before, operation.result == prepared.after,
        operation.after == prepared.after_certificate,
    ensures valid_operation(Operation::Exchange(seq![operation]), prepared),
{
    reveal(ns_exchange::valid);
    reveal(valid_operation);
}

pub proof fn a_prepared_operation_retains_its_exact_patches(prepared: &Prepared)
    requires prepared.wf(),
    ensures valid_operation(prepared.operation(), prepared.view()),
{
    match &prepared.inner {
        Kind::Rename(p) => {
            ns_prepared::prepared_operations_retain_their_exact_source_and_result(p);
            rename_operation_is_valid(p.operation(), p.view());
        },
        Kind::Edit(p) => {
            crate::ns_edit_prepared::prepared_edits_retain_their_exact_source_and_result(p);
            edit_operation_is_valid(p.operation(), p.view());
        },
        Kind::FileRename(p) => {
            crate::ns_file_rename_prepared::prepared_file_renames_retain_their_exact_source_and_result(p);
            file_rename_operation_is_valid(p.operation(), p.view());
        },
        Kind::Exchange(p) => {
            crate::ns_exchange_prepared::prepared_exchanges_retain_their_exact_source_and_result(p);
            exchange_operation_is_valid(p.operation(), p.view());
        },
    }
}

}
