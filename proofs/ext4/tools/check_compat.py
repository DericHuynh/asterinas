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
    }
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
