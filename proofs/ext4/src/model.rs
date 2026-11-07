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

pub mod edit_handles;
pub mod edit_schedule;
pub mod writer_admission;
pub mod content_write;
pub mod inode_time;
pub mod inode_time_fields;
pub mod inode_touch;
pub mod disk_image;
pub mod writer_image;
pub mod recovery_image;
pub mod recovery_crash_image;
pub mod extent_frame;
pub mod write_frame;
pub mod inode_projection;
pub mod write_result;
pub mod bootstrap_frame;
pub mod recovery_bootstrap;
pub mod claim_admission;
pub mod claim_budget;
pub mod allocation_budget;
pub mod journal_queue;
pub mod journal_queue_trace;
pub mod journal_program;
pub mod journal_window;

pub mod journal_window_device;

pub mod journal_window_media;

pub mod journal_window_progress;

pub mod window_provenance;

pub mod window_stream;

pub mod window_snapshot;

pub mod window_scan;

pub mod window_records;

pub mod window_recognition;

pub mod window_recovery_profile;
pub mod window_redo;

pub mod window_recovery;

pub mod window_repeated_recovery;

pub mod window_prefix;

pub mod window_admission;

pub mod window_bootstrap;

pub mod feature_policy;
pub mod backup_layout;
pub mod link_count;

pub mod xattr_entry;

pub mod xattr_table;

pub mod xattr;

pub mod xattr_source;

pub mod xattr_inode;

pub mod acl;

pub mod acl_access;

pub mod htree;

pub mod dir_hash;

pub mod htree_topology;

pub mod htree_range;

pub mod htree_names;

pub mod directory_piece;
pub mod directory_htree;

pub mod xattr_table_edit;

pub mod xattr_replace;

pub mod xattr_update;

pub mod xattr_hash;
pub mod xattr_store;

pub mod xattr_pack;

pub mod xattr_inode_edit;

pub mod xattr_block_update;

pub mod xattr_batch;

pub mod xattr_lifecycle;

pub mod xattr_footprint;

pub mod xattr_durable;

pub mod xattr_canonical;

pub mod inode_mode;
pub mod acl_xattr;

pub mod xattr_transaction;
pub mod xattr_commit;

pub mod acl_update;

pub mod acl_transform;
pub mod acl_chmod;
pub mod acl_inherit;

pub mod ea_inode;
pub mod ea_source;
pub mod ea_reference;
pub mod ea_hash;
pub mod ea_value;
pub mod ea_refs;

pub mod ea_index;
pub mod ea_parent;
pub mod ea_ref_projection;
pub mod ea_billing;
pub mod ea_census;

pub mod ea_storage;

pub mod ea_block_policy;

pub mod ea_integrity;

pub mod ea_reservations;

pub mod ea_journal;

pub mod ea_ordinary;

pub mod ea_allocation_counts;

pub mod ea_allocation;

pub mod ea_namespace_nodes;

pub mod ea_directory;

pub mod ea_directory_index;

pub mod ea_namespace_counts;

pub mod ea_namespace_parent;

pub mod ea_namespace_topology;

pub mod ea_namespace;

pub mod ns_mutation_model;

pub mod ns_inode_touch;

pub mod ns_rename_block;

pub mod ns_rename;

pub mod ns_checkout;

pub mod ns_prepared;

pub mod ns_mutation;

pub mod ns_dir_edit;

pub mod ns_inode_links;

pub mod ns_namespace_relation;

pub mod ns_namespace_edit;

pub mod ns_edit_prepared;

pub mod ns_record_target;

pub mod ns_file_rename_relation;

pub mod ns_file_rename;

pub mod ns_file_rename_prepared;

pub mod ns_exchange_relation;

pub mod ns_exchange;

pub mod ns_exchange_prepared;

pub mod ea_bootstrap;

pub mod ea_super_state;

pub mod ns_journal_prepared;

pub mod ea_write_io;

pub mod ea_writer_admission;

pub mod ea_recovery_admission;

pub mod ea_recovery_image;

pub mod ea_write_bootstrap;
