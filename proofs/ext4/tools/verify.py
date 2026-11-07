# SPDX-License-Identifier: MPL-2.0
"""Check and compile the verified core; never issue a filesystem certificate.

Validate the official archive against toolchain.lock.json before installing it.
The selected compiler/verifier, its vstd foundation, and Python are trusted.
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
LOCK_BYTES = (ROOT / "toolchain.lock.json").read_bytes()
LOCK = json.loads(LOCK_BYTES)
RUNNER_BYTES = Path(__file__).read_bytes()
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
        "scope": "declared models and executable core; no kernel filesystem claim",
        "writable_mount_enabled": False,
        "required_proofs": LOCK["required_proofs"],
        "required_executable_functions": LOCK["required_executable_functions"],
        "source_sha256": {},
    }
    write_report(report)  # Remove any stale success before checking prerequisites.
    (BUILD / "libverified_ext4.rlib").unlink(missing_ok=True)
    # A timeout must not leave diagnostics from an earlier source revision.
    for name in ["verus.stdout", "verus.stderr", "compile.stdout", "compile.stderr"]:
        (BUILD / name).unlink(missing_ok=True)
    try:
        if len(sys.argv) != 1:
            raise RuntimeError("No extra verifier flags or filters are accepted.")
        forbidden = [
            r"\b(?:assume|admit)\s*[!(]",
            r"\bassume_specification\b",
            r"verifier\s*::\s*external(?:_[A-Za-z0-9_]+)?\b",
            r"\b(?:axiom|unsafe|inline_air)\b",
            r"#\s*!?\s*\[\s*cfg(?:_attr)?\b",
            r"#\s*!?\s*\[\s*path\s*=",
            r"\binclude(?:_str|_bytes)?\s*!",
            r"\bexec_allows_no_decreases_clause\b",
            r"\btokenized_state_machine\s*!",  # Would add trusted generated APIs.
        ]
        actual = []
        actual_exec = []
        if sorted(LOCK["model_files"]) != sorted(
            str(p.relative_to(ROOT)) for p in (ROOT / "src").rglob("*.rs")
        ):
            raise RuntimeError("Every Rust source must be in the pinned source manifest.")
        for relative in LOCK["model_files"]:
            path = ROOT / relative
            contents = path.read_text()
            report["source_sha256"][relative] = hashlib.sha256(path.read_bytes()).hexdigest()
            # Conservative text check is intentionally allowed to fail on comments.
            if any(re.search(pattern, contents) for pattern in forbidden):
                raise RuntimeError("Disallowed model escape/filter in " + relative)
            module = path.stem
            actual += [module + "::" + name for name in re.findall(r"pub proof fn (\w+)", contents)]
            actual_exec += [module + "::" + name for name in re.findall(r"pub fn (\w+)", contents)]
            macro_start = contents.find("verus! {")
            if macro_start < 0 or any(
                m.start() < macro_start for m in re.finditer(r"\bfn\s+\w+", contents)
            ):
                raise RuntimeError("Function definition outside the verified body: " + relative)
        if sorted(actual) != sorted(LOCK["required_proofs"]):
            raise RuntimeError("Named proof inventory differs from the pinned manifest.")
        if sorted(actual_exec) != sorted(LOCK["required_executable_functions"]):
            raise RuntimeError("Executable function inventory differs from the pinned manifest.")
        root_text = (ROOT / LOCK["model_root"]).read_text()
        for module in [Path(p).stem for p in LOCK["model_files"] if p != LOCK["model_root"]]:
            if not re.search(r"\bmod\s+" + module + r"\s*;", root_text):
                raise RuntimeError("Required model module is missing: " + module)
        binary = os.environ.get("VERUS_BIN")
        if not binary:
            raise RuntimeError("Set VERUS_BIN to the pinned verifier executable.")
        version = subprocess.run(
            [binary, "--version", "--output-json"],
            capture_output=True, text=True, check=True, timeout=30,
        )
        version_text = version.stdout + version.stderr
        if LOCK["verus"]["commit"] not in version_text:
            raise RuntimeError("Verifier version did not report the pinned full commit.")
        report["verifier_version"] = json.loads(version.stdout)
        diagnostic_dir = BUILD / "verus-logs" / str(os.getpid())
        diagnostic_dir.mkdir(parents=True)
        report["diagnostic_log_directory"] = str(diagnostic_dir.relative_to(ROOT))
        report["command"] = [
            binary, "--no-cheating", "--no-external-by-default", "--output-json", "--compile",
            "--crate-type=rlib", "--crate-name=verified_ext4", "--out-dir=build",
            "--log", "smt", "--log-dir", report["diagnostic_log_directory"],
            LOCK["model_root"],
        ]
        process = subprocess.run(
            report["command"], cwd=ROOT, capture_output=True, text=True, timeout=2100,
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
            and results.get("verified", 0) >= len(actual) + len(actual_exec)
        ):
            raise RuntimeError("Missing successful full-crate verification coverage.")
        details = output.get("func-details", {})
        coverage = {}
        for name in actual + actual_exec:
            module, function = name.split("::")
            # Associated methods have an additional type segment in Verus JSON.
            matches = [key for key in details if (key == name or key.endswith("::" + name)
                or ("::" + module + "::" in key and key.endswith("::" + function)))]
            if len(matches) != 1:
                raise RuntimeError("Verifier function coverage missing " + name)
            coverage[name] = matches[0]
        artifact = BUILD / "libverified_ext4.rlib"
        if not artifact.is_file():
            raise RuntimeError("Verified executable library was not emitted.")
        for relative, digest in report["source_sha256"].items():
            if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != digest:
                raise RuntimeError("Source changed during verification: " + relative)
        if (ROOT / "toolchain.lock.json").read_bytes() != LOCK_BYTES or Path(__file__).read_bytes() != RUNNER_BYTES:
            raise RuntimeError("Verifier manifest or runner changed during verification.")
        report["status"] = "core_and_models_checked"
        report["verification_results"] = results
        report["named_proof_coverage"] = sorted(LOCK["required_proofs"])
        report["named_executable_coverage"] = sorted(LOCK["required_executable_functions"])
        report["verifier_symbols"] = coverage
        report["artifact_sha256"] = hashlib.sha256(artifact.read_bytes()).hexdigest()
        report["lock_sha256"] = hashlib.sha256(LOCK_BYTES).hexdigest()
        report["runner_sha256"] = hashlib.sha256(RUNNER_BYTES).hexdigest()
        report["not_proved"] = [
            "physical device/flush/DMA behavior",
            "complete ext4/JBD2 decoding, disk-history recognition, and recovery",
            "physical circular-log reuse, revokes, and quiescence",
            "filesystem operations, VFS permissions, and OSTD adapter refinement",
            "a functioning or durable ext4 filesystem",
        ]
        write_report(report)
        print(f"Verus checked {results['verified']} obligations and compiled the core. "
              "Kernel mount gates remain closed.")
    except Exception as error:
        if isinstance(error, subprocess.TimeoutExpired) and error.cmd == report.get("command"):
            for name, output in [("verus.stdout", error.stdout), ("verus.stderr", error.stderr)]:
                (BUILD / name).write_bytes(output.encode() if isinstance(output, str) else output or b"")
        report["status"] = "failed_or_not_run"
        (BUILD / "libverified_ext4.rlib").unlink(missing_ok=True)
        report["error"] = str(error)
        write_report(report)
        print(str(error), file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
