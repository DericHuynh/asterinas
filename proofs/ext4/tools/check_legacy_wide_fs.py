#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
"""Run legacy-width regressions against an immutable focused-checked rlib.

This runner does not turn a filtered Verus diagnostic into a whole-crate gate.
It leaves the official proof report and build directory untouched.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
TEST_SOURCE = ROOT / "tests/legacy_wide_fs.rs"
EXPECTED_TESTS = {
    "wide_filesystem_counts_are_preserved",
    "largest_legacy_pointer_stays_a_u32_address",
    "small_snapshot_rejects_wide_volume_before_low_pointer_use",
    "budgets_and_empty_reads_keep_existing_priority",
    "neighboring_words_are_separate_little_endian_pointers",
    "sparse_collection_retains_allocations_beyond_eof",
    "logical_file_block_domain_remains_u32",
    "malformed_geometry_and_unsupported_flags_still_fail",
    "small_geometry_rejects_pointer_at_filesystem_end",
    "collection_still_rejects_physical_aliases",
    "sparse_reads_zero_holes_and_clip_eof",
    "collection_still_rejects_logical_block_overflow",
    "complete_source_geometry_requires_every_declared_byte",
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_artifact(attempt, require_current_source):
    result = json.loads((attempt / "result.json").read_text())
    command = json.loads((attempt / "command.json").read_text())
    verification = json.loads((attempt / "stdout").read_text())["verification-results"]
    argv = command["argv"]
    if not (result["returncode"] == 0 and result["snapshot_unchanged"]
            and result["verified_modules"] == ["legacy_map"]
            and not verification["encountered-error"]
            and not verification["encountered-vir-error"]
            and verification["errors"] == 0 and verification["verified"] > 0):
        raise RuntimeError("Attempt is not a successful legacy_map proof diagnostic")
    if any(flag not in argv for flag in
           ["--compile", "--output-json", "--no-external-by-default", "--verify-module"]):
        raise RuntimeError("Proof command omits a required checking/compilation flag")
    if "--no-verify" in argv or argv[argv.index("--verify-module") + 1] != "legacy_map":
        raise RuntimeError("Incorrect proof filter or verification disabled")
    if verification["is-verifying-entire-crate"]:
        raise RuntimeError("Expected a filtered diagnostic; re-evaluate evidence scope")
    manifest = json.loads((attempt / "source-sha256.json").read_text())["snapshot"]
    for relative, expected in manifest.items():
        if sha(attempt / relative) != expected:
            raise RuntimeError("Proof snapshot changed: " + relative)
    source_hash = manifest["src/legacy_map.rs"]
    if require_current_source and sha(ROOT / "src/legacy_map.rs") != source_hash:
        raise RuntimeError("Current legacy_map source differs from checked snapshot")
    artifact = attempt / "build/libverified_ext4.rlib"
    return artifact, {
        "attempt": attempt.name,
        "source_sha256": source_hash,
        "library_sha256": sha(artifact),
        "command_sha256": sha(attempt / "command.json"),
        "verification_results": verification,
        "filtered": True,
        "whole_expansion_verified": False,
    }


def command_run(argv, output, label):
    (output / (label + "-command.json")).write_text(json.dumps(argv, indent=2) + "\n")
    process = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
    (output / (label + "-stdout")).write_text(process.stdout)
    (output / (label + "-stderr")).write_text(process.stderr)
    return process


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof-attempt", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--baseline-proof-attempt", type=Path)
    parser.add_argument("--rustc", default=os.environ.get("RUSTC_BIN", "rustc"))
    parser.add_argument("--libraries", default=os.environ.get("VERUS_LIB_DIR"))
    args = parser.parse_args()
    args.output = args.output.resolve()
    if not args.libraries:
        parser.error("--libraries or VERUS_LIB_DIR is required")
    # A failed attempt remains reviewable and cannot be silently overwritten.
    args.output.mkdir(parents=True, exist_ok=False)
    result_path = args.output / "report.json"
    report = {"schema": 1, "status": "failed", "formal_verification": False}
    try:
        artifact, evidence = checked_artifact(args.proof_attempt.resolve(), True)
        inputs = {"tests": sha(TEST_SOURCE), "runner": sha(Path(__file__)),
                  "library": sha(artifact), "legacy_map": sha(ROOT / "src/legacy_map.rs")}
        lock = json.loads((ROOT / "toolchain.lock.json").read_text())
        version = command_run([args.rustc, "--version"], args.output, "rustc")
        if version.returncode != 0 or version.stdout.split()[1] != lock["verus"]["rust_toolchain"]:
            raise RuntimeError("Native rustc does not match the pinned Verus compiler")
        binary = args.output / "legacy-wide-tests"
        compile_result = command_run(
            [args.rustc, "--edition=2024", "--test", str(TEST_SOURCE), "--extern",
             "verified_ext4=" + str(artifact), "-L", "dependency=" + args.libraries,
             "-o", str(binary)], args.output, "compile")
        if compile_result.returncode != 0:
            raise RuntimeError("Native test compilation failed; see compile-stderr")
        listed = command_run([str(binary), "--list"], args.output, "list")
        names = {line.removesuffix(": test") for line in listed.stdout.splitlines()
                 if line.endswith(": test")}
        if listed.returncode != 0 or names != EXPECTED_TESTS:
            raise RuntimeError("Native test inventory differs from the expected regressions")
        tested = command_run([str(binary), "--test-threads=1"], args.output, "tests")
        expected = (f"test result: ok. {len(EXPECTED_TESTS)} passed; 0 failed; "
                    "0 ignored; 0 measured; 0 filtered out;")
        if tested.returncode != 0 or expected not in tested.stdout:
            raise RuntimeError("Native regressions failed or did not all run; see tests-stdout")
        baseline = None
        if args.baseline_proof_attempt:
            old_artifact, baseline = checked_artifact(args.baseline_proof_attempt.resolve(), False)
            old_binary = args.output / "baseline-legacy-wide-tests"
            old_compile = command_run(
                [args.rustc, "--edition=2024", "--test", str(TEST_SOURCE), "--extern",
                 "verified_ext4=" + str(old_artifact), "-L", "dependency=" + args.libraries,
                 "-o", str(old_binary)], args.output, "baseline-compile")
            if old_compile.returncode != 0:
                raise RuntimeError("Baseline negative-control compilation failed")
            control = command_run(
                [str(old_binary), "--exact", "wide_filesystem_counts_are_preserved", "--nocapture"],
                args.output, "baseline-negative-control")
            if not (control.returncode == 101 and "0 passed; 1 failed;" in control.stdout
                    and "count 4294967297" in control.stdout + control.stderr
                    and sha(old_artifact) == baseline["library_sha256"]):
                raise RuntimeError("Old checked artifact did not show the expected geometry regression")
            baseline["negative_control"] = "expected failure: geometry rejected at 2^32+1 blocks"
        final = {"tests": sha(TEST_SOURCE), "runner": sha(Path(__file__)),
                 "library": sha(artifact), "legacy_map": sha(ROOT / "src/legacy_map.rs")}
        if final != inputs:
            raise RuntimeError("Source, runner or compiled artifact changed during testing")
        report.update({
            "status": "passed",
            "implementation": "Actual focused-checked compiled rlib; no local reimplementation or erasure",
            "proof": evidence,
            "input_sha256": inputs,
            "rustc": version.stdout.strip(),
            "tests_passed": len(EXPECTED_TESTS), "tests_failed": 0,
            "tests_ignored": 0, "tests_filtered": 0,
            "test_names": sorted(EXPECTED_TESTS),
            "baseline_negative_control": baseline,
            "scope": "Synthetic legacy inodes and real Snapshot APIs: wide structural geometry, LE32 pointers, logical bounds, full-source preflight, budgets, sparse reads/collection and aliases",
            "limitations": [
                "No positive multi-terabyte snapshot read was attempted",
                "Structural parser acceptance does not establish full Linux filesystem admission",
                "Filtered proof diagnostic, not a strict whole-crate verification result",
                "No mount, allocation, device writes or writable VFS path is enabled",
            ],
        })
    except Exception as error:
        report["error"] = str(error)
        raise
    finally:
        result_path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "tests_passed": report["tests_passed"],
                      "report": str(result_path)}))


if __name__ == "__main__":
    main()
