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

pub mod bitmap;

pub mod block_claims;

pub mod inode_claims;

pub mod group_claims;

pub mod snapshot;

pub mod group_metadata;

pub mod group_index;

pub mod inode_table;

pub mod inode_group;

mod allocation_counts;

pub mod allocation;

pub mod allocated_inode;

pub mod file_read;

pub mod directory_block;

pub mod directory_file;

pub mod name_set;

pub mod directory_source;

pub mod namespace_model;

pub mod directory_index;

mod namespace_counts;

mod parent_table;

mod tree_model;

mod namespace_tree;

pub mod namespace;

pub mod patch_set;
mod shadow_model;
pub mod bootstrap;
pub mod bootstrap_identity;
pub mod image_validation;
pub mod recovery_patch;
pub mod recovery_admission;
pub mod block_range;
pub mod extent_span;
mod block_lifetime;
pub mod block_size;
pub mod extent_node;
pub mod source_block;

pub mod extent_tree;

pub mod extent_tree_model;

pub mod extent_claims;

pub mod extent_ownership;

pub mod inode_size;

pub mod inode_blocks;

pub mod group_fields;

pub mod block_bitmap;
