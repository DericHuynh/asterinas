// SPDX-License-Identifier: MPL-2.0

//! Verified-core and model entry point. See ../proof-status.json for scope.
//! This library is not registered with the kernel VFS.

#![deny(unsafe_code)]

use vstd::prelude::*;

mod redo;
mod journal;
mod lease;
mod history;
pub mod bytes;
pub mod crc;
pub mod superblock;
pub mod extent;
pub mod directory;
pub mod jbd2;
pub mod frozen;
mod gate;
pub mod ring;
mod persistence;
pub mod journal_superblock;
mod ownership;
pub mod group;
pub mod access;
pub mod inode;
mod system;
pub mod descriptor;

verus! {
fn main() {}
}

pub mod revoke;

pub mod layout;

pub mod replay;

mod replay_refinement;

pub mod scan;
pub mod epoch;

pub mod journal_state;

pub mod super_state;

pub mod recovery_io;

mod recovery_device;

pub mod scan_trace;

pub mod recovery_request;

pub mod scan_stop;

pub mod transaction;

mod journal_view;

mod transaction_refinement;

pub mod write_protocol;

pub mod write_io;

mod freshness;

mod write_device;

mod write_media;

mod write_recognition;

pub mod scan_budget;

mod write_admission;

pub mod recovery_profile;

mod write_recovery;

mod write_history;

mod recovery_closure;
