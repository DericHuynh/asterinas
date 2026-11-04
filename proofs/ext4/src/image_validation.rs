// SPDX-License-Identifier: MPL-2.0

//! Retained immutable source with a complete static allocation/namespace
//! certificate. Inspection grants no VFS, recovery-command or device authority.

use vstd::prelude::*;
use crate::{allocation, directory_index, layout::JournalLayout, namespace::{self, NamespaceView}, snapshot::Snapshot};

verus! {

pub struct CheckedImage<'a> { source: Snapshot<'a>, journal: JournalLayout, namespace: Ghost<NamespaceView> }

impl<'a> CheckedImage<'a> {
    pub closed spec fn view(&self) -> NamespaceView { self.namespace@ }
    pub open spec fn wf(&self) -> bool { namespace::valid(self.view()) }

    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {
        self.wf() && self.view().index.volume.index.source == self.source.view()
            && self.journal.wf() && self.journal.view() == self.view().index.volume.journal
    }

    pub fn source(&self) -> (r: &Snapshot<'a>)
        ensures self.wf(), r.view() == self.view().index.volume.index.source,
    {
        proof { use_type_invariant(self); }
        &self.source
    }

    pub fn journal(&self) -> (r: &JournalLayout)
        ensures self.wf(), r.wf(), r.view() == self.view().index.volume.journal,
    {
        proof { use_type_invariant(self); }
        &self.journal
    }
}

pub fn inspect<'a>(source: Snapshot<'a>) -> (r: Option<CheckedImage<'a>>)
    ensures match r {
        Some(checked) => checked.wf() && checked.view().index.volume.index.source == source.view(),
        None => true,
    },
{
    let volume = match allocation::parse(source.duplicate()) { Some(volume) => volume, None => { return None; } };
    let index = match directory_index::build(&volume) { Some(index) => index, None => { return None; } };
    let namespace = match namespace::validate(&index) { Some(namespace) => namespace, None => { return None; } };
    let journal = volume.journal().duplicate();
    proof { reveal(namespace::valid); }
    Some(CheckedImage { source, journal, namespace: Ghost(namespace.view()) })
}

}
