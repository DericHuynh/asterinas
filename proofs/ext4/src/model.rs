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
