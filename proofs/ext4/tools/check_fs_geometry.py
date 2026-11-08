#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
"""Replay the geometry tests against an actual Verus-compiled component.

With --verus, first create a private source snapshot and focused artifact.
With --proof-dir, reuse an existing successful focused diagnostic snapshot.
Neither mode produces or replaces the official whole-crate certificate.
"""

import argparse
import hashlib
import json
from pathlib import Path
import resource
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
ASSETS = ROOT / "tests" / "fs_geometry"


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (16 * 1024**3, 16 * 1024**3))


def invoke(directory, name, argv, timeout):
    start = time.monotonic()
    with (directory / (name + ".stdout")).open("x") as out, (
        directory / (name + ".stderr")
    ).open("x") as err:
        result = subprocess.run(
            list(map(str, argv)),
            cwd=directory,
            stdout=out,
            stderr=err,
            timeout=timeout,
            preexec_fn=limits,
        )
    save(
        directory / (name + "-command.json"),
        {
            "argv": list(map(str, argv)),
            "returncode": result.returncode,
            "seconds": time.monotonic() - start,
        },
    )
    return result


def build_component(verus, destination):
    destination.mkdir()
    lock = json.loads((ROOT / "toolchain.lock.json").read_text())
    version = invoke(destination, "version", [verus, "--version", "--output-json"], 30)
    assert version.returncode == 0
    version_json = json.loads((destination / "version.stdout").read_text())
    assert version_json["verus"]["commit"] == lock["verus"]["commit"]
    save(destination / "verifier-version.json", version_json)
    snapshot = {}
    for relative in lock["model_files"]:
        source = ROOT / relative
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        snapshot[relative] = sha(target)
    shutil.copyfile(
        ROOT / "toolchain.lock.json", destination / "baseline-toolchain.lock.json"
    )
    save(destination / "source-sha256.json", {"snapshot": snapshot})
    (destination / "build").mkdir()
    argv = [
        str(verus),
        "--no-cheating",
        "--no-external-by-default",
        "--output-json",
        "--num-threads",
        "2",
        "--crate-type=rlib",
        "--crate-name=verified_ext4",
        "--compile",
        "--out-dir",
        str(destination / "build"),
        "--verify-module",
        "fs_geometry",
        "src/model.rs",
    ]
    save(
        destination / "command.json",
        {
            "argv": argv,
            "verified_modules": ["fs_geometry"],
            "scope": "focused component in the complete current entrypoint",
        },
    )
    result = invoke(destination, "verification", argv, 600)
    shutil.copyfile(destination / "verification.stdout", destination / "stdout")
    stable = all(sha(destination / name) == value for name, value in snapshot.items())
    save(
        destination / "result.json",
        {
            "returncode": result.returncode,
            "snapshot_unchanged": stable,
            "verified_modules": ["fs_geometry"],
        },
    )
    assert result.returncode == 0 and stable, "focused verification failed"
    return destination


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    provider = parser.add_mutually_exclusive_group(required=True)
    provider.add_argument("--proof-dir", type=Path)
    provider.add_argument("--verus", type=Path)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--rustc", type=Path, required=True)
    parser.add_argument("--verus-lib-dir", type=Path, required=True)
    args = parser.parse_args()
    out = args.out_dir.resolve()
    out.mkdir()
    proof = (
        args.proof_dir.resolve()
        if args.proof_dir
        else build_component(args.verus.resolve(), out / "proof")
    )
    library = proof / "build" / "libverified_ext4.rlib"
    proof_result = json.loads((proof / "result.json").read_text())
    verification = json.loads((proof / "stdout").read_text())["verification-results"]
    command = json.loads((proof / "command.json").read_text())
    assert proof_result["returncode"] == 0 and proof_result["snapshot_unchanged"]
    assert proof_result["verified_modules"] == ["fs_geometry"]
    assert command["verified_modules"] == ["fs_geometry"]
    assert "--compile" in command["argv"] and "--no-verify" not in command["argv"]
    assert "--no-external-by-default" in command["argv"]
    assert verification["verified"] == 29 and verification["errors"] == 0
    assert not verification["encountered-error"] and not verification["encountered-vir-error"]
    assert not verification["is-verifying-entire-crate"]
    assert library.is_file()
    evidence = json.loads((ASSETS / "evidence.json").read_text())
    version_file = proof / "verifier-version.json"
    if version_file.exists():
        version = json.loads(version_file.read_text())
        current_pin = json.loads((ROOT / "toolchain.lock.json").read_text())["verus"]
        assert version["verus"]["commit"] == current_pin["commit"]
    else:
        # The recorded diagnostic predates this portable wrapper. Admit that
        # exact provider and evidence, rather than inferring a compiler pin
        # merely from the snapshot's lock file.
        for path, key in [
            (library, "library_sha256"),
            (proof / "stdout", "proof_stdout_sha256"),
            (proof / "result.json", "proof_result_sha256"),
            (proof / "command.json", "proof_command_sha256"),
        ]:
            assert sha(path) == evidence[key], path
    assert sha(ROOT / "src/fs_geometry.rs") == evidence["source_sha256"]
    for relative in ["src/fs_geometry.rs", "src/block_size.rs"]:
        assert sha(ROOT / relative) == sha(proof / relative), relative
    lock = json.loads((ROOT / "toolchain.lock.json").read_text())
    provider_lock = json.loads((proof / "baseline-toolchain.lock.json").read_text())
    for key in ["verus", "required_flags"]:
        assert lock[key] == provider_lock[key], key
    source_manifest = json.loads((proof / "source-sha256.json").read_text())["snapshot"]
    for relative, digest in source_manifest.items():
        assert sha(proof / relative) == digest, relative
    for name, item in evidence["copied_assets"].items():
        assert sha(ASSETS / name) == item["sha256"], name
    cases = json.loads((ASSETS / "cases.json").read_text())
    negatives = json.loads((ASSETS / "negative-cases.json").read_text())
    assert len(cases) == 1225 and len(negatives) == 5
    protected = {
        library,
        proof / "stdout",
        proof / "result.json",
        proof / "command.json",
        proof / "source-sha256.json",
        proof / "baseline-toolchain.lock.json",
        ROOT / "toolchain.lock.json",
        ROOT / "src/fs_geometry.rs",
        ROOT / "src/block_size.rs",
        Path(__file__).resolve(),
        args.rustc.resolve(),
    }
    if version_file.exists():
        protected.add(version_file)
    if args.verus:
        protected.add(args.verus.resolve())
    protected.update(proof / relative for relative in source_manifest)
    protected.update(p for p in ASSETS.rglob("*") if p.is_file())
    protected.update(p for p in args.verus_lib_dir.resolve().glob("*.rlib"))
    before = {str(p): sha(p) for p in sorted(protected)}
    save(out / "input-sha256.json", before)
    prefix = [
        str(args.rustc.resolve()),
        "--edition=2024",
        "-O",
        "--extern",
        "verified_ext4=" + str(library),
        "-L",
        "dependency=" + str(args.verus_lib_dir.resolve()),
    ]

    def compile_source(source, target, name):
        result = invoke(out, name + "-compile", prefix + [source, "-o", target], 60)
        return result.returncode

    numeric = out / "numeric"
    assert compile_source(ASSETS / "driver.rs", numeric, "numeric") == 0
    with numeric.open("rb") as source:
        assert source.read(5) == b"\x7fELF\x02", "cases require a 64-bit ELF target"
    records = []
    for index, case in enumerate(cases):
        argv = [str(numeric), case["op"], *case["args"]]
        result = subprocess.run(argv, capture_output=True, text=True, timeout=10)
        records.append(
            {
                "case": index,
                "argv": argv,
                "returncode": result.returncode,
                "stdout": result.stdout,
                "stderr": result.stderr,
            }
        )
        if result.returncode != 0 or result.stdout != case["expected_stdout"]:
            save(out / "numeric-results.json", records)
            raise AssertionError("numeric mismatch: " + str(index))
    save(out / "numeric-results.json", records)
    allowed = out / "allowed"
    assert compile_source(ASSETS / "allowed.rs", allowed, "allowed") == 0
    assert invoke(out, "allowed", [allowed], 10).returncode == 0
    rejections = []
    for case in negatives:
        target = out / case["name"]
        code = compile_source(ASSETS / case["source"], target, case["name"])
        stderr = (out / (case["name"] + "-compile.stderr")).read_text()
        assert code != 0 and case["expected_error"] in stderr and not target.exists()
        rejections.append(
            {"name": case["name"], "returncode": code, "error": case["expected_error"]}
        )
    save(out / "negative-results.json", rejections)
    after = {name: sha(name) for name in before}
    save(out / "input-sha256-after.json", after)
    assert after == before, "protected proof/library/source/test inputs changed"
    result = {
        "status": "passed",
        "formal_verification": False,
        "focused_provider_obligations": verification["verified"],
        "focused_provider_errors": 0,
        "provider_whole_crate_verified": False,
        "library_sha256": sha(library),
        "numeric_cases": len(records),
        "negative_boundary_cases": len(rejections),
        "positive_boundary_controls": 1,
        "inputs_unchanged": True,
        "source_sha256": sha(ROOT / "src/fs_geometry.rs"),
        "scope": "numeric geometry and Rust privacy; no kernel/device/durability authority",
    }
    save(out / "result.json", result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
