#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
"""Replay the sector RAM-model tests on the recorded focused-proof library.

This consumes an existing compiled provider. It never runs Verus, issues a
certificate, changes an admission gate, or establishes physical durability.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def store(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def relative_file(root, relative):
    path = Path(relative)
    require(not path.is_absolute() and ".." not in path.parts,
            "Nonrelative input path: " + relative)
    target = root / path
    require(target.resolve().is_relative_to(root.resolve()),
            "Input escapes provider directory: " + relative)
    return target


def check_provider(provider, expected):
    files = expected["provider_file_sha256"]
    for relative, digest in files.items():
        require(sha(relative_file(provider, relative)) == digest,
                "Recorded focused provider differs: " + relative)
    result = json.loads((provider / "result.json").read_text())
    require(result["returncode"] == 0 and result["snapshot_unchanged"] is True
            and result["diagnostic_only"] is True
            and result["verified_modules"] == ["sector_crash"],
            "Provider is not the successful focused sector proof.")
    results = json.loads((provider / "stdout").read_text())["verification-results"]
    require(results["verified"] == 37 and results["errors"] == 0
            and results["encountered-error"] is False
            and results["encountered-vir-error"] is False
            and results["is-verifying-entire-crate"] is False,
            "Expected focused 37/0 result, not a whole-crate certificate.")
    command = json.loads((provider / "command.json").read_text())
    require(command["verified_modules"] == ["sector_crash"]
            and command["declared_new_modules"] == ["sector_crash"]
            and command["diagnostic_only"] is True
            and command["no_cheating_omitted_for_diagnostic_only"] is True,
            "Unexpected diagnostic scope.")
    argv = command["argv"]
    require("--compile" in argv and "--no-external-by-default" in argv
            and argv[argv.index("--verify-module") + 1] == "sector_crash",
            "Expected compiled focused-provider command.")
    manifest = json.loads((provider / "source-sha256.json").read_text())["snapshot"]
    require(set(manifest) == {
        str(path.relative_to(provider)) for path in (provider / "src").rglob("*.rs")
    }, "Provider snapshot inventory differs from retained Rust sources.")
    for relative, digest in manifest.items():
        require(sha(relative_file(provider, relative)) == digest,
                "Provider source changed: " + relative)
    root_text = (provider / "src/model.rs").read_text()
    modules = re.findall(r"(?m)^(?:pub )?mod ([a-zA-Z0-9_]+);\s*$", root_text)
    require(len(modules) == len(set(modules)) and "sector_crash" in modules
            and "write_media" in modules, "Unexpected focused dependency declarations.")
    # The focused entrypoint only removes declarations; preserve all other tokens.
    def without_declarations(text):
        return re.sub(r"(?m)^(?:pub )?mod [a-zA-Z0-9_]+;\s*$", "", text).split()
    require(without_declarations(root_text) ==
            without_declarations((ROOT / "src/model.rs").read_text()),
            "Focused entrypoint differs beyond module declarations.")
    declared = {}
    for module in modules:
        relative = "src/" + module + ".rs"
        require(relative in manifest, "Declared dependency absent from snapshot: " + relative)
        require(sha(ROOT / relative) == manifest[relative],
                "Current compiled dependency differs from provider: " + relative)
        declared[relative] = manifest[relative]
    require(manifest["src/sector_crash.rs"] == expected["module_sha256"],
            "Unexpected sector model source.")
    pins = json.loads((provider / "baseline-toolchain.lock.json").read_text())
    lock = json.loads((ROOT / "toolchain.lock.json").read_text())
    for field in ["verus", "linux_reference", "asterinas_reference", "required_flags"]:
        require(pins[field] == lock[field], "Provider pin differs: " + field)
    return results, declared


def bindings(provider, library_dir, rustc):
    lock = json.loads((ROOT / "toolchain.lock.json").read_text())
    require(set(lock["model_files"]) == {
        str(path.relative_to(ROOT)) for path in (ROOT / "src").rglob("*.rs")
    }, "Current source inventory differs from pinned manifest.")
    branch_files = list(lock["model_files"]) + [
        "toolchain.lock.json", "tests/sector_crash.rs", "tests/sector_crash_allowed.rs",
        "tests/sector_crash_api_cases.json", "tools/check_sector_crash.py",
        "SECTOR_CRASH.md", "SECTOR_CRASH_STATUS.json",
    ]
    manifest = json.loads((provider / "source-sha256.json").read_text())["snapshot"]
    provider_files = list(manifest) + [
        "result.json", "command.json", "stdout", "stderr", "source-sha256.json",
        "baseline-toolchain.lock.json", "build/libverified_ext4.rlib",
    ]
    dependencies = sorted(path for path in library_dir.iterdir()
                          if path.is_file() and path.suffix in {".rlib", ".so"})
    require(dependencies, "No Verus dependency libraries found.")
    git = {}
    for label, args in [("head", ["rev-parse", "HEAD"]),
                        ("branch", ["branch", "--show-current"]),
                        ("status", ["status", "--porcelain=v1"])]:
        argv = ["git", "-C", str(ROOT)] + args
        process = subprocess.run(argv, capture_output=True, text=True, check=True, timeout=30)
        git[label] = {"argv": argv, "stdout": process.stdout, "stderr": process.stderr,
                      "returncode": process.returncode}
    return {
        "git": git,
        "current_branch_files": {name: sha(ROOT / name) for name in branch_files},
        "provider_files": {name: sha(provider / name) for name in provider_files},
        "rustc": {"path": str(rustc), "sha256": sha(rustc)},
        "dependency_libraries": {str(path): sha(path) for path in dependencies},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--provider", type=Path, required=True,
                        help="directory of the recorded successful focused proof")
    parser.add_argument("--output", type=Path, required=True, help="new evidence directory")
    args = parser.parse_args()
    provider = args.provider.resolve()
    output = args.output.resolve()
    require(not output.exists(), "Output must be a new directory.")
    output.mkdir(parents=True)
    commands = []
    report = {"schema": 1, "status": "failed", "formal_verification": False,
              "scope": "Native RAM model and Rust API checks on one focused-proof library",
              "whole_branch_certificate": False, "writable_mount_enabled": False}
    try:
        status = json.loads((ROOT / "SECTOR_CRASH_STATUS.json").read_text())
        expected = status["focused_component_proof"]
        results, declared = check_provider(provider, expected)
        rustc_name = os.environ.get("RUSTC_BIN", "rustc")
        rustc_found = shutil.which(rustc_name)
        require(rustc_found is not None, "RUSTC_BIN was not found.")
        rustc = Path(rustc_found).resolve()
        library_env = os.environ.get("VERUS_LIB_DIR")
        require(library_env is not None, "Set VERUS_LIB_DIR to the pinned release libraries.")
        library_dir = Path(library_env).resolve()
        before = bindings(provider, library_dir, rustc)
        store(output / "before-bindings.json", before)
        shutil.copyfile(Path(__file__), output / "checker.py")
        library = provider / "build/libverified_ext4.rlib"
        sources = {
            "tests.rs": (ROOT / "tests/sector_crash.rs").read_bytes(),
            "allowed_model_use.rs": (ROOT / "tests/sector_crash_allowed.rs").read_bytes(),
        }
        cases = json.loads((ROOT / "tests/sector_crash_api_cases.json").read_text())["cases"]
        require(set(cases) == {"forged_private_owner.rs", "physical_receipt_factory.rs",
                              "substituted_piece_bytes.rs"}, "Unexpected API fixture inventory.")
        source_pins = status["native_checks"]["input_source_sha256"]
        for name, content in sources.items():
            require(hashlib.sha256(content).hexdigest() == source_pins[name],
                    "Recorded native fixture changed: " + name)
            (output / name).write_bytes(content)
        for name, case in cases.items():
            require(Path(name).name == name and name.endswith(".rs"), "Invalid fixture name.")
            content = case["source"].encode()
            require(hashlib.sha256(content).hexdigest() == case["source_sha256"] ==
                    source_pins["compile-fail/" + name], "API fixture hash mismatch: " + name)
            sources["compile-fail/" + name] = content
            target = output / "compile-fail" / name
            target.parent.mkdir(exist_ok=True)
            target.write_bytes(content)

        def run(argv, label, success=True, timeout=60):
            started = time.monotonic()
            record = {"argv": list(map(str, argv)), "label": label,
                      "expected_success": success, "timeout_seconds": timeout, "state": "started"}
            commands.append(record)
            store(output / "commands.json", commands)
            try:
                process = subprocess.run(record["argv"], cwd=output,
                                         capture_output=True, text=True, timeout=timeout)
            except Exception as error:
                record.update(state="failed_to_complete", error=repr(error),
                              seconds=time.monotonic() - started)
                store(output / "commands.json", commands)
                for stream in ["stdout", "stderr"]:
                    value = getattr(error, stream, None) or ""
                    if isinstance(value, bytes):
                        value = value.decode(errors="replace")
                    (output / (label + "." + stream)).write_text(value)
                raise
            (output / (label + ".stdout")).write_text(process.stdout)
            (output / (label + ".stderr")).write_text(process.stderr)
            record.update(state="completed", returncode=process.returncode,
                          seconds=time.monotonic() - started)
            store(output / "commands.json", commands)
            require((process.returncode == 0) == success,
                    "Unexpected command outcome: " + label)
            return process

        version = run([rustc, "--version"], "rustc-version", timeout=30).stdout
        lock = json.loads((ROOT / "toolchain.lock.json").read_text())
        require(version.startswith("rustc " + lock["verus"]["rust_toolchain"] + " "),
                "Native tests must use the pinned Verus Rust toolchain.")

        def compiler(source, binary, test=False):
            argv = [rustc, "--edition=2021"]
            if test:
                argv.append("--test")
            return argv + [source, "--extern", "verified_ext4_sector_crash=" + str(library),
                           "-L", "dependency=" + str(library_dir), "-o", binary]

        run(compiler(output / "tests.rs", output / "tests", True), "compile-tests")
        tests = run([output / "tests", "--test-threads=1"], "tests")
        require("7 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out" in tests.stdout,
                "Expected all seven unchanged native test families.")
        run(compiler(output / "allowed_model_use.rs", output / "allowed-model-use"),
            "compile-allowed-control")
        run([output / "allowed-model-use"], "allowed-control")
        negatives = {}
        for name, case in sorted(cases.items()):
            process = run(compiler(output / "compile-fail" / name,
                                   output / ("unexpected-" + name[:-3])),
                          "reject-" + name[:-3], success=False)
            require(case["diagnostic_code"] in process.stderr
                    and case["diagnostic_term"] in process.stderr,
                    "Intended diagnostic missing: " + name)
            require("E0463" not in process.stderr and "can't find crate" not in process.stderr,
                    "API rejection was caused by a dependency error: " + name)
            negatives[name] = {"intended_diagnostic": case["diagnostic_code"],
                               "diagnostic_term": case["diagnostic_term"], "rejected": True}
        after = bindings(provider, library_dir, rustc)
        store(output / "after-bindings.json", after)
        require(before == after, "Provider or branch inputs changed during native checks.")
        for relative, content in sources.items():
            require((output / relative).read_bytes() == content,
                    "Copied fixture changed during native checks: " + relative)
        report.update(
            status="passed", native_test_families=7, allowed_control_passed=True,
            negative_api_cases=3, negative_api_results=negatives,
            before_after_inputs_unchanged=True, compiled_actual_provider=True,
            no_local_model_reimplementation=True, focused_verification=results,
            provider_artifact=str(library), provider_sha256=sha(library),
            declared_dependency_module_sha256=declared,
            compiled_source_files_with_root=len(declared) + 1,
            retained_snapshot_sources=len(before["provider_files"]) - 7,
            retained_snapshot_is_not_verification_coverage=True,
            commands_sha256=sha(output / "commands.json"),
            compiled_tests_sha256=sha(output / "tests"),
            limitations=status["limits"],
        )
    except Exception as error:
        report["error"] = repr(error)
        print(str(error), file=sys.stderr)
    finally:
        store(output / "result.json", report)
        store(output / "sha256.json", {
            str(path.relative_to(output)): sha(path)
            for path in sorted(output.rglob("*"))
            if path.is_file() and path.name != "sha256.json"
        })
    print(json.dumps(report, indent=2))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
