#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
"""Check timeout diagnostics in an isolated, fault-injected runner copy.

No verifier subprocess is executed. The version call is mocked only to reach
the injected verification timeout; this check cannot produce proof evidence.
"""

import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]


def main():
    with tempfile.TemporaryDirectory(prefix="ext4-timeout-diagnostics-") as temporary:
        copy = Path(temporary)
        shutil.copytree(ROOT / "src", copy / "src")
        shutil.copytree(ROOT / "tools", copy / "tools")
        shutil.copyfile(ROOT / "toolchain.lock.json", copy / "toolchain.lock.json")
        build = copy / "build"
        build.mkdir()
        for name in [
            "verus.stdout", "verus.stderr", "compile.stdout", "compile.stderr",
            "libverified_ext4.rlib",
        ]:
            (build / name).write_bytes(b"stale earlier run")
        (build / "proof-report.json").write_text('{"status":"core_and_models_checked"}')

        runner_path = copy / "tools" / "verify.py"
        spec = importlib.util.spec_from_file_location("_ext4_timeout_runner", runner_path)
        if spec is None or spec.loader is None:
            raise RuntimeError("Could not import the disposable verification runner.")
        runner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(runner)
        binary = "timeout-diagnostic-only"
        partial_stdout = b"current partial stdout"
        partial_stderr = b"current partial stderr"

        def inject_timeout(command, **kwargs):
            if command == [binary, "--version", "--output-json"]:
                return subprocess.CompletedProcess(
                    command, 0,
                    stdout=json.dumps({"commit": runner.LOCK["verus"]["commit"]}),
                    stderr="",
                )
            assert command[0] == binary and "--compile" in command
            assert "--no-cheating" in command and "--no-external-by-default" in command
            raise subprocess.TimeoutExpired(
                command, kwargs["timeout"], output=partial_stdout, stderr=partial_stderr,
            )

        expected_error = io.StringIO()
        with (
            mock.patch.object(runner.subprocess, "run", side_effect=inject_timeout) as calls,
            mock.patch.dict(runner.os.environ, {"VERUS_BIN": binary}),
            mock.patch.object(runner.sys, "argv", [str(runner_path)]),
            contextlib.redirect_stderr(expected_error),
        ):
            assert runner.main() == 1
            assert calls.call_count == 2, "The injected timeout must reach verification."

        report = json.loads((build / "proof-report.json").read_text())
        assert report["status"] == "failed_or_not_run"
        assert "timed out" in report["error"] and "timed out" in expected_error.getvalue()
        assert report["command"][0] == binary and "--compile" in report["command"]
        assert report["writable_mount_enabled"] is False
        assert "verification_results" not in report and "artifact_sha256" not in report
        assert not (build / "libverified_ext4.rlib").exists()
        assert (build / "verus.stdout").read_bytes() == partial_stdout
        assert (build / "verus.stderr").read_bytes() == partial_stderr
        assert not (build / "compile.stdout").exists()
        assert not (build / "compile.stderr").exists()

    print(
        "timeout diagnostics: passed; current partial logs retained, stale logs/artifact "
        "invalidated, no success report or verifier subprocess"
    )
    print("check_timeout.py sha256: " + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
