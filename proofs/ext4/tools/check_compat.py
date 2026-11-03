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
    run([rustc, "--edition=2024", "--test", "tests/compat.rs", "--extern",
         "verified_ext4=build/libverified_ext4.rlib", "-L", "dependency=" + libraries,
         "-o", "build/compat-tests"])
    environment = os.environ.copy()
    environment["EXT4_TEST_IMAGE"] = str(image)
    process = subprocess.run(["build/compat-tests", "--nocapture"], cwd=ROOT, env=environment,
                             capture_output=True, text=True)
    print(process.stdout, end="")
    (BUILD / "compat.stdout").write_text(process.stdout)
    if process.returncode != 0:
        print(process.stderr, file=sys.stderr)
        process.check_returncode()
    result = {"schema": 1, "status": "passed", "scope": "host interoperability tests, not formal proof",
              "rustc": version.strip(), "proof_artifact_sha256": report["artifact_sha256"],
              "image_sha256": hashlib.sha256(image.read_bytes()).hexdigest(),
              "test_source_sha256": hashlib.sha256((ROOT / "tests/compat.rs").read_bytes()).hexdigest()}
    (BUILD / "compat-report.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
