#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
"""Exercise the emitted core on Linux bytes; this does not discharge proofs."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / "build"


def run(args, **kwargs):
    return subprocess.run(args, cwd=ROOT, check=True, **kwargs)


def main():
    (BUILD / "compat-report.json").unlink(missing_ok=True)
    report = json.loads((BUILD / "proof-report.json").read_text())
    if report["status"] != "core_and_models_checked":
        raise RuntimeError("Run the pinned verifier successfully before compatibility tests.")
    for relative, digest in report["source_sha256"].items():
        if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != digest:
            raise RuntimeError("Sources changed after verification: " + relative)
    for relative, field in [("toolchain.lock.json", "lock_sha256"), ("tools/verify.py", "runner_sha256"),
                            ("build/libverified_ext4.rlib", "artifact_sha256")]:
        if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != report[field]:
            raise RuntimeError("Verification artifact changed: " + relative)
    rustc = os.environ.get("RUSTC_BIN", "rustc")
    version = run([rustc, "--version"], capture_output=True, text=True).stdout
    lock = json.loads((ROOT / "toolchain.lock.json").read_text())
    if not version.startswith("rustc " + lock["verus"]["rust_toolchain"] + " "):
        raise RuntimeError("Host tests must use the pinned Verus Rust toolchain.")
    libraries = os.environ.get("VERUS_LIB_DIR")
    if not libraries:
        raise RuntimeError("Set VERUS_LIB_DIR to the pinned release's library directory.")
    image = BUILD / "linux.img"
    image.unlink(missing_ok=True)
    run([os.environ.get("MKE2FS_BIN", "mke2fs"), "-q", "-F", "-t", "ext4", "-b", "4096",
         "-I", "256", "-O", "none,has_journal,extent,filetype,sparse_super,large_file,extra_isize,metadata_csum",
         "-E", "lazy_itable_init=0,lazy_journal_init=0", "build/linux.img", "16384"])
    (BUILD / "fixture-file.bin").write_bytes(bytes(i % 251 for i in range(8192)))
    run([os.environ.get("DEBUGFS_BIN", "debugfs"), "-w", "-R",
         "write build/fixture-file.bin /payload", "build/linux.img"])
    environment = os.environ.copy()
    environment["EXT4_TEST_IMAGE"] = str(image)
    output = []
    for suite in ["compat", "journal"]:
        run([rustc, "--edition=2024", "--test", "tests/" + suite + ".rs", "--extern",
             "verified_ext4=build/libverified_ext4.rlib", "-L", "dependency=" + libraries,
             "-o", "build/" + suite + "-tests"])
        process = subprocess.run(["build/" + suite + "-tests", "--nocapture"], cwd=ROOT, env=environment,
                                 capture_output=True, text=True)
        print(process.stdout, end="")
        output.append(process.stdout)
        (BUILD / "compat.stdout").write_text("\n".join(output))
        if process.returncode != 0:
            print(process.stderr, file=sys.stderr)
            process.check_returncode()
    rejected = []
    misuse = {
        "reuse_request": ("use verified_ext4::recovery_request::{Pending, Completion};\n"
                          "pub fn misuse(p: Pending) { let _ = p.finish_pending(Completion::Succeeded); "
                          "let _ = p.finish_pending(Completion::Succeeded); }\n", "E0382"),
        "redirect_completion": ("pub fn misuse(e: &mut verified_ext4::recovery_io::Recovery) "
                                "{ let _ = e.complete(1, true); }\n", "E0624"),
        "forge_request": ("pub fn misuse(engine: verified_ext4::recovery_io::Recovery) "
                          "{ let _ = verified_ext4::recovery_request::Pending { engine, id: 1 }; }\n", "E0451"),
        "reuse_write_request": ("use verified_ext4::{write_io::Pending, recovery_request::Completion};\n"
                                "pub fn misuse(p: Pending) { let _ = p.finish_pending(Completion::Succeeded); "
                                "let _ = p.finish_pending(Completion::Succeeded); }\n", "E0382"),
        "forge_write_request": ("pub fn misuse(writer: verified_ext4::write_io::Writer) "
                                "{ let _ = verified_ext4::write_io::Pending { writer }; }\n", "E0451"),
        "replace_write_state": ("pub fn misuse(mut w: verified_ext4::write_io::Writer, s: verified_ext4::write_protocol::State) "
                                "{ w.state = s; }\n", "E0616"),
        "reuse_admitted_request": ("use verified_ext4::{recovery_admission::Pending, recovery_request::Completion};\n"
                                   "pub fn misuse(p: Pending<'_, '_>) { let _ = p.finish_pending(Completion::Succeeded); "
                                   "let _ = p.finish_pending(Completion::Succeeded); }\n", "E0382"),
        "forge_admitted_recovery": ("pub fn misuse(r: verified_ext4::recovery_admission::CheckedRecovery<'_, '_>) "
                                    "{ let _ = verified_ext4::recovery_admission::CheckedRecovery { ..r }; }\n", "E0451"),
        "replace_admitted_engine": ("pub fn misuse(mut r: verified_ext4::recovery_admission::CheckedRecovery<'_, '_>, "
                                    "e: verified_ext4::recovery_io::Recovery) { r.engine = e; }\n", "E0616"),
        "forge_extent_tree": ("pub fn misuse(t: verified_ext4::extent_tree::CheckedTree<'_, '_>) "
                              "{ let _ = verified_ext4::extent_tree::CheckedTree { ..t }; }\n", "E0451"),
        "replace_extent_tree_source": ("pub fn misuse<'s, 'image>(mut t: verified_ext4::extent_tree::CheckedTree<'s, 'image>, "
                                      "s: &'s verified_ext4::snapshot::Snapshot<'image>) { t.source = s; }\n", "E0616"),
        "forge_bound_extent_inode": ("pub fn misuse(t: verified_ext4::extent_claims::BoundInode<'_, '_>) "
                                    "{ let _ = verified_ext4::extent_claims::BoundInode { ..t }; }\n", "E0451"),
        "replace_bound_extent_index": ("pub fn misuse<'v, 'image>(mut t: verified_ext4::extent_claims::BoundInode<'v, 'image>, "
                                      "i: &'v verified_ext4::group_index::GroupIndex<'image>) { t.index = i; }\n", "E0616"),
    }
    misuse.update({
        "forge_group_metadata": ("pub fn misuse(m: verified_ext4::group_metadata::GroupMetadata) "
                                 "{ let _ = verified_ext4::group_metadata::GroupMetadata { ..m }; }\n", "E0451"),
        "replace_group_index_source": ("pub fn misuse<'a>(mut i: verified_ext4::group_index::GroupIndex<'a>, "
                                      "s: verified_ext4::snapshot::Snapshot<'a>) { i.source = s; }\n", "E0616"),
        "forge_edit_handle": ("pub fn misuse(h: verified_ext4::edit_handles::Handle<'_>) "
                              "{ let _ = verified_ext4::edit_handles::Handle { ..h }; }\n", "E0451"),
        "redirect_edit_handle": ("pub fn misuse(mut h: verified_ext4::edit_handles::Handle<'_>) "
                                 "{ h.key = 42; }\n", "E0616"),
        "reuse_closed_edit_handle": ("pub fn misuse(h: verified_ext4::edit_handles::Handle<'_>) "
                                     "{ let _ = h.close(); let _ = h.target(); }\n", "E0382"),
        "freeze_borrowed_edit_batch": ("pub fn misuse(mut r: verified_ext4::edit_handles::Running) { "
                                      "let (mut p, _) = r.borrow_parts(1).unwrap(); "
                                      "let h = p.handle_at(0).unwrap(); let _ = r.freeze(); let _ = h.close(); }\n", "E0505"),
        "alias_edit_handle": ("pub fn misuse(mut p: verified_ext4::edit_handles::Part<'_>) { "
                               "let h = p.handle_at(0).unwrap(); let _ = p.handle_at(0); let _ = h.close(); }\n", "E0499"),
        "forge_frozen_edit_batch": ("pub fn misuse(f: verified_ext4::edit_handles::FrozenBatch) "
                                    "{ let _ = verified_ext4::edit_handles::FrozenBatch { ..f }; }\n", "E0451"),
        "forge_admitted_writer": ("pub fn misuse(w: verified_ext4::writer_admission::CheckedWriter<'_, '_>) "
                                   "{ let _ = verified_ext4::writer_admission::CheckedWriter { ..w }; }\n", "E0451"),
        "replace_admitted_writer": ("pub fn misuse(mut w: verified_ext4::writer_admission::CheckedWriter<'_, '_>, "
                                     "raw: verified_ext4::write_io::Writer) { w.writer = raw; }\n", "E0616"),
        "extract_admitted_writer": ("pub fn misuse(w: verified_ext4::writer_admission::CheckedWriter<'_, '_>) "
                                     "{ let _ = w.writer; }\n", "E0616"),
        "reuse_admitted_write_completion": ("pub fn misuse(p: verified_ext4::writer_admission::Pending<'_, '_>) { "
                                             "let _ = p.finish_pending(verified_ext4::recovery_request::Completion::Succeeded); "
                                             "let _ = p.finish_pending(verified_ext4::recovery_request::Completion::Succeeded); }\n", "E0382"),
        "reuse_dispatched_admitted_writer": ("pub fn misuse(w: verified_ext4::writer_admission::CheckedWriter<'_, '_>) "
                                              "{ let _ = w.dispatch(); let _ = w.dispatch(); }\n", "E0382"),
        "replace_admitted_write_pending": ("pub fn misuse(mut p: verified_ext4::writer_admission::Pending<'_, '_>, "
                                            "raw: verified_ext4::write_io::Pending) { p.pending = raw; }\n", "E0616"),
        "forge_content_candidate": ("pub fn misuse(p: verified_ext4::content_write::Candidate<'_, '_, '_>) "
                                     "{ let _ = verified_ext4::content_write::Candidate { ..p }; }\n", "E0451"),
        "redirect_content_candidate": ("pub fn misuse(mut p: verified_ext4::content_write::Candidate<'_, '_, '_>, "
                                        "image: verified_ext4::transaction::AfterImage) { p.image = image; }\n", "E0616"),
        "reuse_content_candidate": ("pub fn misuse(p: verified_ext4::content_write::Candidate<'_, '_, '_>) "
                                     "{ let _ = p.begin(); let _ = p.begin(); }\n", "E0382"),
        "replace_content_inode": ("pub fn misuse<'n, 'v, 'a>(mut p: verified_ext4::content_write::Candidate<'n, 'v, 'a>, "
                                   "n: &'n verified_ext4::allocated_inode::AllocatedInode<'v, 'a>) { p.node = n; }\n", "E0616"),
        "reuse_released_edit_part": ("pub fn misuse(p: verified_ext4::edit_handles::Part<'_>) "
                                      "{ p.release(); let _ = p.part_count(); }\n", "E0382"),
        "alter_journal_queue_credits": ("pub fn misuse(mut q: verified_ext4::journal_queue::Queue) "
                                         "{ q.used = 0; }\n", "E0616"),
        "forge_frozen_journal_version": ("pub fn misuse(batch: verified_ext4::edit_handles::FrozenBatch) "
                                          "{ let _ = verified_ext4::journal_queue::FrozenVersion "
                                          "{ serial: 1, first: 1, blocks: 3, batch }; }\n", "E0451"),
        "replace_frozen_journal_batch": ("pub fn misuse(mut v: verified_ext4::journal_queue::FrozenVersion, "
                                          "batch: verified_ext4::edit_handles::FrozenBatch) { v.batch = batch; }\n", "E0616"),
        "cancel_borrowed_journal_work": ("pub fn misuse(q: &mut verified_ext4::journal_queue::Queue) "
                                          "{ let (_, part, _) = q.borrow_work(0).unwrap(); "
                                          "q.cancel(); let _ = part.part_count(); }\n", "E0499"),
        "overwrite_frozen_journal_version": ("pub fn misuse(q: &verified_ext4::journal_queue::Queue, "
                                              "v: verified_ext4::journal_queue::FrozenVersion) "
                                              "{ q.frozen_versions()[0] = v; }\n", "E0594"),
        "mutate_frozen_journal_bytes": ("pub fn misuse(v: &verified_ext4::journal_queue::FrozenVersion) "
                                         "{ v.image_at(0).unwrap().1[0] = 1; }\n", "E0594"),
        "forge_window_request": ("pub fn misuse(engine: verified_ext4::journal_window::Engine) "
                                   "{ let _ = verified_ext4::journal_window::Pending { engine, id: 1 }; }\n", "E0451"),
        "reuse_window_request": ("pub fn misuse(p: verified_ext4::journal_window::Pending) { "
                                  "let _ = p.finish_pending(verified_ext4::recovery_request::Completion::Succeeded); "
                                  "let _ = p.finish_pending(verified_ext4::recovery_request::Completion::Succeeded); }\n", "E0382"),
        "replace_window_state": ("pub fn misuse(mut e: verified_ext4::journal_window::Engine, "
                                   "s: verified_ext4::journal_program::State) { e.state = s; }\n", "E0616"),
        "mutate_window_command": ("pub fn misuse(p: verified_ext4::journal_window::Pending) { "
                                    "if let verified_ext4::recovery_io::Command::Write { image, .. } = p.pending_command() "
                                    "{ image[0] = 1; } }\n", "E0594"),
        "finish_borrowed_window_request": ("pub fn misuse(p: verified_ext4::journal_window::Pending) { "
                                            "let command = p.pending_command(); "
                                            "let _ = p.finish_pending(verified_ext4::recovery_request::Completion::Succeeded); "
                                            "if let verified_ext4::recovery_io::Command::Write { image, .. } = command "
                                            "{ let _ = image.len(); } }\n", "E0505"),
        "reuse_dispatched_window": ("pub fn misuse(e: verified_ext4::journal_window::Engine) { "
                                     "let _ = verified_ext4::journal_window::dispatch(e, verified_ext4::journal_program::Lane::Bootstrap); "
                                     "let _ = e.finished(); }\n", "E0382"),
    })
    misuse.update({
        "forge_admitted_window": ("pub fn misuse(w: verified_ext4::window_admission::CheckedWindow<'_, '_>) "
                                  "{ let _ = verified_ext4::window_admission::CheckedWindow { ..w }; }\n", "E0451"),
        "replace_admitted_window_engine": ("pub fn misuse(mut w: verified_ext4::window_admission::CheckedWindow<'_, '_>, "
                                           "engine: verified_ext4::journal_window::Engine) { w.engine = engine; }\n", "E0616"),
        "extract_admitted_window_engine": ("pub fn misuse(w: verified_ext4::window_admission::CheckedWindow<'_, '_>) "
                                           "{ let _ = w.engine; }\n", "E0616"),
        "replace_admitted_window_source": ("pub fn misuse<'s, 'a>(mut w: verified_ext4::window_admission::CheckedWindow<'s, 'a>, "
                                           "source: &'s verified_ext4::snapshot::Snapshot<'a>) { w.source = source; }\n", "E0616"),
        "forge_admitted_window_pending": ("pub fn misuse(p: verified_ext4::window_admission::Pending<'_, '_>) "
                                          "{ let _ = verified_ext4::window_admission::Pending { ..p }; }\n", "E0451"),
        "replace_admitted_window_pending": ("pub fn misuse(mut p: verified_ext4::window_admission::Pending<'_, '_>, "
                                            "raw: verified_ext4::journal_window::Pending) { p.pending = raw; }\n", "E0616"),
        "reuse_admitted_window_completion": ("pub fn misuse(p: verified_ext4::window_admission::Pending<'_, '_>) { "
                                             "let _ = p.finish_pending(verified_ext4::recovery_request::Completion::Succeeded); "
                                             "let _ = p.finish_pending(verified_ext4::recovery_request::Completion::Succeeded); }\n", "E0382"),
        "reuse_dispatched_admitted_window": ("pub fn misuse(w: verified_ext4::window_admission::CheckedWindow<'_, '_>) "
                                             "{ let _ = w.dispatch(verified_ext4::journal_program::Lane::Bootstrap); let _ = w.finished(); }\n", "E0382"),
        "mutate_admitted_window_bytes": ("pub fn misuse(p: verified_ext4::window_admission::Pending<'_, '_>) { "
                                         "if let verified_ext4::recovery_io::Command::Write { image, .. } = p.pending_command() "
                                         "{ image[0] = 1; } }\n", "E0594"),
        "finish_borrowed_admitted_window": ("pub fn misuse(p: verified_ext4::window_admission::Pending<'_, '_>) { "
                                            "let command = p.pending_command(); "
                                            "let _ = p.finish_pending(verified_ext4::recovery_request::Completion::Succeeded); "
                                            "if let verified_ext4::recovery_io::Command::Write { image, .. } = command "
                                            "{ let _ = image.len(); } }\n", "E0505"),
    })
    misuse.update({
        "mutate_admitted_window_source_bytes": ("pub fn misuse(mut bytes: Vec<u8>, versions: &[verified_ext4::journal_queue::FrozenVersion]) { "
                                               "let source = verified_ext4::snapshot::Snapshot::from_bytes(&bytes); "
                                               "let window = verified_ext4::window_admission::prepare(&source, versions).unwrap(); "
                                               "bytes[0] = 1; let _ = window.finished(); }\n", "E0502"),
    })
    misuse.update({
        "forge_xattr_attributes": ("pub fn misuse(a: verified_ext4::xattr_inode::Attributes<'_>) "
                                    "{ let _ = verified_ext4::xattr_inode::Attributes { ..a }; }\n", "E0451"),
        "mutate_xattr_value": ("pub fn misuse(a: verified_ext4::xattr_inode::Attributes<'_>) "
                                 "{ if let Some(verified_ext4::xattr_table::ValueRef::Bytes(value)) = a.get(1, b\"name\") "
                                 "{ value[0] = 1; } }\n", "E0594"),
        "forge_parsed_acl": ("pub fn misuse(a: verified_ext4::acl::Acl<'_>) "
                              "{ let _ = verified_ext4::acl::Acl { ..a }; }\n", "E0451"),
        "forge_acl_authorization": ("pub fn misuse(a: verified_ext4::acl_access::Authorization<'_, '_, '_>) "
                                     "{ let _ = verified_ext4::acl_access::Authorization { ..a }; }\n", "E0451"),
        "redirect_acl_authorization": ("pub fn misuse<'n, 'v, 'a>(mut a: verified_ext4::acl_access::Authorization<'n, 'v, 'a>, "
                                        "n: &'n verified_ext4::allocated_inode::AllocatedInode<'v, 'a>) { a.node = n; }\n", "E0616"),
        "reuse_consumed_acl_authorization": ("pub fn misuse(a: verified_ext4::acl_access::Authorization<'_, '_, '_>) "
                                             "{ let _ = verified_ext4::content_write::prepare_authorized(a, 0, b\"x\"); "
                                             "let _ = a.requested_bits(); }\n", "E0382"),
    })
    misuse.update({
        "forge_htree_graph": ("pub fn misuse(g: verified_ext4::htree_topology::Graph<'_>) "
                              "{ let _ = verified_ext4::htree_topology::Graph { ..g }; }\n", "E0451"),
        "alter_htree_logical_count": ("pub fn misuse(mut g: verified_ext4::htree_topology::Graph<'_>) "
                                      "{ g.blocks = 3; }\n", "E0616"),
        "mutate_htree_leaf_source": ("pub fn misuse(root: Vec<u8>, mut leaf: Vec<u8>) { "
                                     "let blocks: [&[u8]; 2] = [&root, &leaf]; "
                                     "let graph = verified_ext4::htree_topology::parse(&blocks, 4096, 0, false).unwrap(); "
                                     "leaf[0] = 1; let _ = graph.logical_role(1); }\n", "E0502"),
    })
    misuse.update({
        "forge_htree_name_catalog": ("pub fn misuse(d: verified_ext4::htree_names::Directory<'_>) "
                                      "{ let _ = verified_ext4::htree_names::Directory { ..d }; }\n", "E0451"),
        "forge_htree_source_record": ("pub fn misuse(e: verified_ext4::htree_names::Entry<'_>) "
                                      "{ let _ = verified_ext4::htree_names::Entry { ..e }; }\n", "E0451"),
        "mutate_live_htree_name_source": ("pub fn misuse(root: Vec<u8>, mut leaf: Vec<u8>) { "
                                           "let blocks: [&[u8]; 2] = [&root, &leaf]; "
                                           "let seed = verified_ext4::dir_hash::State { a: 0, b: 0, c: 0, d: 0 }; "
                                           "let d = verified_ext4::htree_names::build(&blocks, 4096, 0, seed, false, false).unwrap(); "
                                           "leaf[8] = 1; let _ = d.lookup(b\"a\"); }\n", "E0502"),
        "forge_directory_piece": ("pub fn misuse(p: verified_ext4::directory_piece::Piece<'_>) "
                                    "{ let _ = verified_ext4::directory_piece::Piece { ..p }; }\n", "E0451"),
    })
    misuse.update({
        "forge_xattr_update_candidate": ("pub fn misuse(c: verified_ext4::xattr_update::Candidate<'_, '_, '_>) "
                                           "{ let _ = verified_ext4::xattr_update::Candidate { ..c }; }\n", "E0451"),
        "redirect_xattr_update_source": ("pub fn misuse<'n, 'v, 'a>(mut c: verified_ext4::xattr_update::Candidate<'n, 'v, 'a>, "
                                         "n: &'n verified_ext4::allocated_inode::AllocatedInode<'v, 'a>) { c.node = n; }\n", "E0616"),
        "reuse_xattr_update_authorization": ("pub fn misuse(a: verified_ext4::acl_access::Authorization<'_, '_, '_>) "
                                              "{ let _ = verified_ext4::xattr_update::prepare(a, b\"note\", b\"changed\", 123, 0); "
                                              "let _ = a.requested_bits(); }\n", "E0382"),
        "reuse_started_xattr_update": ("pub fn misuse(c: verified_ext4::xattr_update::Candidate<'_, '_, '_>) "
                                        "{ let _ = c.begin(); let _ = c.begin(); }\n", "E0382"),
        "mutate_xattr_update_image": ("pub fn misuse(c: verified_ext4::xattr_update::Candidate<'_, '_, '_>) "
                                       "{ c.after_image().as_slice()[0] = 1; }\n", "E0594"),
    })
    misuse.update({
        "forge_owned_xattr_store": ("pub fn misuse(s: verified_ext4::xattr_store::Store) { let _ = verified_ext4::xattr_store::Store { ..s }; }\n", "E0451"),
        "mutate_owned_xattr_item": ("pub fn misuse(mut i: verified_ext4::xattr_store::Item) { i.value = Vec::new(); }\n", "E0616"),
        "forge_packed_xattrs": ("pub fn misuse(p: verified_ext4::xattr_pack::Packed) { let _ = verified_ext4::xattr_pack::Packed { ..p }; }\n", "E0451"),
        "forge_xattr_lifecycle_candidate": ("pub fn misuse(c: verified_ext4::xattr_lifecycle::Candidate<'_, '_, '_>) { let _ = verified_ext4::xattr_lifecycle::Candidate { ..c }; }\n", "E0451"),
        "redirect_xattr_lifecycle_source": ("pub fn misuse<'n, 'v, 'a>(mut c: verified_ext4::xattr_lifecycle::Candidate<'n, 'v, 'a>, n: &'n verified_ext4::allocated_inode::AllocatedInode<'v, 'a>) { c.node = n; }\n", "E0616"),
        "replace_xattr_lifecycle_patches": ("pub fn misuse(mut c: verified_ext4::xattr_lifecycle::Candidate<'_, '_, '_>, p: verified_ext4::patch_set::PatchSet) { c.patches = p; }\n", "E0616"),
        "mutate_xattr_lifecycle_image": ("pub fn misuse(c: verified_ext4::xattr_lifecycle::Candidate<'_, '_, '_>) { c.patches().at(0).unwrap().as_slice()[0] = 1; }\n", "E0594"),
        "reuse_xattr_lifecycle_grant": ("pub fn misuse(a: verified_ext4::acl_access::Authorization<'_, '_, '_>) { let _ = verified_ext4::xattr_lifecycle::set_user(a, b\"key\", b\"value\", 0, 123, 0); let _ = a.requested_bits(); }\n", "E0382"),
        "reuse_started_xattr_lifecycle": ("pub fn misuse(c: verified_ext4::xattr_lifecycle::Candidate<'_, '_, '_>) { let _ = c.begin(); let _ = c.begin(); }\n", "E0382"),
    })
    misuse.update({
        "forge_acl_mutation_authority": ("pub fn misuse(a: verified_ext4::acl_update::Authorization<'_, '_, '_>) { let _ = verified_ext4::acl_update::Authorization { ..a }; }\n", "E0451"),
        "redirect_acl_mutation_authority": ("pub fn misuse<'n, 'v, 'a>(mut a: verified_ext4::acl_update::Authorization<'n, 'v, 'a>, n: &'n verified_ext4::allocated_inode::AllocatedInode<'v, 'a>) { a.node = n; }\n", "E0616"),
        "retarget_acl_authority_kind": ("pub fn misuse(mut a: verified_ext4::acl_update::Authorization<'_, '_, '_>) { a.kind = verified_ext4::acl_update::Kind::Access; }\n", "E0616"),
        "reuse_acl_mutation_authority": ("pub fn misuse(a: verified_ext4::acl_update::Authorization<'_, '_, '_>) { let _ = verified_ext4::acl_update::prepare(a, b\"\", 1, 0); let _ = verified_ext4::acl_update::prepare(a, b\"\", 1, 0); }\n", "E0382"),
        "forge_acl_mutation_candidate": ("pub fn misuse(c: verified_ext4::acl_update::Candidate<'_, '_, '_>) { let _ = verified_ext4::acl_update::Candidate { ..c }; }\n", "E0451"),
        "replace_acl_mutation_patches": ("pub fn misuse(mut c: verified_ext4::acl_update::Candidate<'_, '_, '_>, p: verified_ext4::patch_set::PatchSet) { c.patches = p; }\n", "E0616"),
        "reuse_started_acl_mutation": ("pub fn misuse(c: verified_ext4::acl_update::Candidate<'_, '_, '_>) { let _ = c.begin(); let _ = c.begin(); }\n", "E0382"),
        "mutate_acl_mutation_image": ("pub fn misuse(c: verified_ext4::acl_update::Candidate<'_, '_, '_>) { c.patches().at(0).unwrap().as_slice()[0] = 1; }\n", "E0594"),
        "forge_converted_acl": ("pub fn misuse(a: verified_ext4::acl_xattr::Converted) { let _ = verified_ext4::acl_xattr::Converted { ..a }; }\n", "E0451"),
        "mutate_converted_acl_bytes": ("pub fn misuse(a: verified_ext4::acl_xattr::Converted) { a.as_slice()[0] = 9; }\n", "E0594"),
        "bypass_xattr_storage_constructor": ("pub fn misuse(n: &verified_ext4::allocated_inode::AllocatedInode<'_, '_>, v: &verified_ext4::xattr_store::Store) { let _ = verified_ext4::xattr_transaction::build(n, v, 0o100777, 1, 0); }\n", "E0603"),
        "confuse_data_grant_with_acl_authority": ("pub fn misuse(a: verified_ext4::acl_access::Authorization<'_, '_, '_>) { let _ = verified_ext4::acl_update::prepare(a, b\"\", 1, 0); }\n", "E0308"),
    })
    misuse.update({
        "forge_chmod_authority": ("pub fn misuse(a: verified_ext4::acl_chmod::Authorization<'_, '_, '_>) { let _ = verified_ext4::acl_chmod::Authorization { ..a }; }\n", "E0451"),
        "replace_chmod_inner_authority": ("pub fn misuse<'n, 'v, 'a>(mut a: verified_ext4::acl_chmod::Authorization<'n, 'v, 'a>, b: verified_ext4::acl_update::Authorization<'n, 'v, 'a>) { a.grant = b; }\n", "E0616"),
        "reuse_chmod_authority": ("pub fn misuse(a: verified_ext4::acl_chmod::Authorization<'_, '_, '_>) { let _ = verified_ext4::acl_chmod::prepare(a, 0o644, 1, 0); let _ = verified_ext4::acl_chmod::prepare(a, 0o777, 1, 0); }\n", "E0382"),
        "confuse_acl_authority_with_chmod": ("pub fn misuse(a: verified_ext4::acl_update::Authorization<'_, '_, '_>) { let _ = verified_ext4::acl_chmod::prepare(a, 0o777, 1, 0); }\n", "E0308"),
        "forge_chmod_candidate": ("pub fn misuse(c: verified_ext4::acl_chmod::Candidate<'_, '_, '_>) { let _ = verified_ext4::acl_chmod::Candidate { ..c }; }\n", "E0451"),
        "redirect_chmod_candidate": ("pub fn misuse<'n, 'v, 'a>(mut c: verified_ext4::acl_chmod::Candidate<'n, 'v, 'a>, n: &'n verified_ext4::allocated_inode::AllocatedInode<'v, 'a>) { c.node = n; }\n", "E0616"),
        "mutate_chmod_candidate_image": ("pub fn misuse(c: verified_ext4::acl_chmod::Candidate<'_, '_, '_>) { c.patches().at(0).unwrap().as_slice()[0] = 1; }\n", "E0594"),
        "reuse_started_chmod": ("pub fn misuse(c: verified_ext4::acl_chmod::Candidate<'_, '_, '_>) { let _ = c.begin(); let _ = c.begin(); }\n", "E0382"),
        "bypass_chmod_storage_constructor": ("pub fn misuse(n: &verified_ext4::allocated_inode::AllocatedInode<'_, '_>, v: &verified_ext4::xattr_store::Store) { let _ = verified_ext4::xattr_transaction::build_chmod(n, v, 0o107777, 1, 0); }\n", "E0603"),
        "forge_acl_transform": ("pub fn misuse(t: verified_ext4::acl_transform::Transformed) { let _ = verified_ext4::acl_transform::Transformed { ..t }; }\n", "E0451"),
        "mutate_acl_transform_bytes": ("pub fn misuse(t: verified_ext4::acl_transform::Transformed) { t.as_slice()[0] = 7; }\n", "E0594"),
        "forge_inheritance_plan": ("pub fn misuse(p: verified_ext4::acl_inherit::Plan) { let _ = verified_ext4::acl_inherit::Plan { ..p }; }\n", "E0451"),
        "redirect_inheritance_mode": ("pub fn misuse(mut p: verified_ext4::acl_inherit::Plan) { p.mode = 0o107777; }\n", "E0616"),
        "mutate_inheritance_access_bytes": ("pub fn misuse(p: verified_ext4::acl_inherit::Plan) { p.access().unwrap()[0] = 7; }\n", "E0594"),
    })
    for name, (source, code) in misuse.items():
        path = BUILD / (name + ".rs")
        path.write_text(source)
        artifact = BUILD / (name + ".rlib")
        artifact.unlink(missing_ok=True)
        process = subprocess.run([rustc, "--edition=2024", "--crate-type=lib", str(path), "--extern",
                                  "verified_ext4=build/libverified_ext4.rlib", "-L", "dependency=" + libraries,
                                  "-o", str(artifact)], cwd=ROOT, capture_output=True, text=True)
        if process.returncode == 0 or code not in process.stderr or artifact.exists():
            raise RuntimeError("Public request boundary accepted misuse: " + name + "\n" + process.stderr)
        rejected.append(name)
        print(name + ": rejected by Rust ownership/privacy checks")
    result = {"schema": 1, "status": "passed", "scope": "host interoperability tests, not formal proof",
              "rustc": version.strip(), "proof_artifact_sha256": report["artifact_sha256"],
              "image_sha256": hashlib.sha256(image.read_bytes()).hexdigest(),
              "request_boundary_rejections": rejected,
              "compatibility_runner_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "test_source_sha256": {s: hashlib.sha256((ROOT / ("tests/" + s + ".rs")).read_bytes()).hexdigest()
                                     for s in ["compat", "journal"]}}
    (BUILD / "compat-report.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
