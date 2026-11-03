# SPDX-License-Identifier: MPL-2.0
"""Draft fail-closed runner for the abstract models, not an ext4 certificate.

This runner has not been executed or validated in the authoring environment.
Validate the official release archive digest from toolchain.lock.json before
installing it. The selected compiler/verifier and Python runtime are trusted.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / "build"
LOCK = json.loads((ROOT / "toolchain.lock.json").read_text())
REPORT = BUILD / "proof-report.json"

def write_report(data):
    BUILD.mkdir(exist_ok=True)
    temporary = REPORT.with_suffix(".tmp")
    temporary.write_text(json.dumps(data, indent=2) + "\n")
    temporary.replace(REPORT)

def main():
    report = {
        "schema": 1,
        "status": "not_run",
        "scope": "abstract models only; no filesystem/driver/refinement claim",
        "writable_mount_enabled": False,
        "required_proofs": LOCK["required_proofs"],
        "source_sha256": {},
    }
    write_report(report)  # Remove any stale success before checking prerequisites.
    try:
        if len(sys.argv) != 1:
            raise RuntimeError("No extra verifier flags or filters are accepted.")
        forbidden = [
            r"\b(?:assume|admit)\s*\(",
            r"verifier\s*::\s*(?:external|external_body|external_fn_specification)\b",
            r"\b(?:axiom|unsafe|inline_air)\b",
            r"#\s*!?\s*\[\s*cfg(?:_attr)?\b",
            r"#\s*!?\s*\[\s*path\s*=",
            r"\binclude(?:_str|_bytes)?\s*!",
        ]
        actual = []
        for relative in LOCK["model_files"]:
            path = ROOT / relative
            contents = path.read_text()
            report["source_sha256"][relative] = hashlib.sha256(path.read_bytes()).hexdigest()
            # Conservative text check is intentionally allowed to fail on comments.
            if any(re.search(pattern, contents) for pattern in forbidden):
                raise RuntimeError("Disallowed model escape/filter in " + relative)
            module = path.stem
            actual += [module + "::" + name for name in re.findall(r"pub proof fn (\w+)", contents)]
        if sorted(actual) != sorted(LOCK["required_proofs"]):
            raise RuntimeError("Named proof inventory differs from the pinned manifest.")
        root_text = (ROOT / LOCK["model_root"]).read_text()
        for module in ["redo", "journal", "lease"]:
            if not re.search(r"\bmod\s+" + module + r"\s*;", root_text):
                raise RuntimeError("Required model module is missing: " + module)
        binary = os.environ.get("VERUS_BIN")
        if not binary:
            raise RuntimeError("Set VERUS_BIN to the pinned verifier executable.")
        version = subprocess.run(
            [binary, "--version", "--output-json"],
            capture_output=True, text=True, check=True,
        )
        version_text = version.stdout + version.stderr
        if LOCK["verus"]["commit"] not in version_text:
            raise RuntimeError("Verifier version did not report the pinned full commit.")
        report["verifier_version"] = json.loads(version.stdout)
        report["command"] = [
            binary, "--no-cheating", "--output-json", LOCK["model_root"],
        ]
        process = subprocess.run(
            report["command"], cwd=ROOT, capture_output=True, text=True,
        )
        (BUILD / "verus.stdout").write_text(process.stdout)
        (BUILD / "verus.stderr").write_text(process.stderr)
        report["exit_code"] = process.returncode
        if process.returncode != 0:
            raise RuntimeError("Verus returned failure; inspect build/verus.stderr.")
        output = json.loads(process.stdout)
        results = output.get("verification-results", {})
        if not (
            results.get("success") is True
            and results.get("is-verifying-entire-crate") is True
            and results.get("errors") == 0
            and results.get("encountered-error") is False
            and results.get("encountered-vir-error") is False
            and results.get("verified", 0) >= len(LOCK["required_proofs"])
        ):
            raise RuntimeError("Missing successful full-crate verification coverage.")
        details = output.get("func-details", {})
        for name in LOCK["required_proofs"]:
            if not any(key == name or key.endswith("::" + name) for key in details):
                raise RuntimeError("Verifier function coverage missing " + name)
        report["status"] = "abstract_models_checked"
        report["verification_results"] = results
        report["named_proof_coverage"] = sorted(LOCK["required_proofs"])
        report["not_proved"] = [
            "physical device/flush/DMA behavior",
            "JBD2/ext4 byte decoding and recovery recognition",
            "multiple transactions and circular-log reuse",
            "VFS permissions, OSTD concurrency, and executable refinement",
            "a functioning or durable ext4 filesystem",
        ]
        write_report(report)
        print("Abstract models checked. Filesystem and integration gates remain closed.")
    except Exception as error:
        report["status"] = "failed_or_not_run"
        report["error"] = str(error)
        write_report(report)
        print(str(error), file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
