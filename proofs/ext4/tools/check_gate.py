#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
"""Negative checks of the runner, in disposable copies of the proof package."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    cases = ["missing_verifier", "extra_flags", "local_escape", "unlisted_source",
             "missing_module", "false_assertion"]
    for case in cases:
        with tempfile.TemporaryDirectory(prefix="ext4-verification-gate-") as temporary:
            copy = Path(temporary)
            shutil.copytree(ROOT / "src", copy / "src")
            shutil.copytree(ROOT / "tools", copy / "tools")
            shutil.copyfile(ROOT / "toolchain.lock.json", copy / "toolchain.lock.json")
            (copy / "build").mkdir()
            # A failed check must invalidate a stale successful report/library.
            (copy / "build/proof-report.json").write_text('{"status":"core_and_models_checked"}')
            (copy / "build/libverified_ext4.rlib").write_bytes(b"stale artifact")
            environment = os.environ.copy()
            arguments = [sys.executable, str(copy / "tools/verify.py")]
            root = copy / "src/model.rs"
            if case == "missing_verifier":
                environment.pop("VERUS_BIN", None)
            elif case == "extra_flags":
                arguments.append("--verify-function=main")
            elif case == "local_escape":
                root.write_text(root.read_text().replace("fn main() {}", "fn main() { assume(false); }"))
            elif case == "unlisted_source":
                (copy / "src/hidden.rs").write_text("fn hidden() {}")
            elif case == "missing_module":
                root.write_text(root.read_text().replace("mod system;", ""))
            elif case == "false_assertion":
                root.write_text(root.read_text().replace("fn main() {}", "fn main() { assert(false); }"))
            process = subprocess.run(arguments, cwd=copy, env=environment, capture_output=True, text=True, timeout=2160)
            report = json.loads((copy / "build/proof-report.json").read_text())
            if process.returncode == 0 or report["status"] != "failed_or_not_run":
                raise RuntimeError("Gate accepted negative case: " + case)
            if (copy / "build/libverified_ext4.rlib").exists():
                raise RuntimeError("Gate retained an artifact for: " + case)
            if case == "false_assertion" and "Verus returned failure" not in report["error"]:
                raise RuntimeError("False assertion did not reach the verifier: " + report["error"])
            print(case + ": rejected")


if __name__ == "__main__":
    main()
