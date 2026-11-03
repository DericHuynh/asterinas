#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
"""Install the digest-pinned x86 Linux release; Rust is installed separately."""

import argparse
import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--archive", type=Path, help="Use an already downloaded archive")
    args = parser.parse_args()
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        parser.error("This manifest pins the Linux x86-64 release only.")
    lock = json.loads((ROOT / "toolchain.lock.json").read_text())["verus"]
    with tempfile.TemporaryDirectory(prefix="verus-install-") as temporary:
        archive = args.archive
        if archive is None:
            archive = Path(temporary) / "verus.zip"
            subprocess.run(["curl", "--fail", "--location", "--retry", "3", "--proto", "=https",
                            "--output", str(archive), lock["x86_linux_archive"]], check=True)
        if hashlib.sha256(archive.read_bytes()).hexdigest() != lock["x86_linux_sha256"]:
            raise RuntimeError("Verus archive digest differs from toolchain.lock.json.")
        with zipfile.ZipFile(archive) as bundle:
            for entry in bundle.infolist():
                path = Path(entry.filename)
                if path.is_absolute() or ".." in path.parts:
                    raise RuntimeError("Archive path escapes the installation directory.")
            bundle.extractall(temporary)
        source = Path(temporary) / "verus-x86-linux"
        version = json.loads((source / "version.json").read_text())["verus"]
        if version["commit"] != lock["commit"]:
            raise RuntimeError("Release metadata differs from the pinned full commit.")
        destination = args.directory.resolve()
        if destination.exists():
            raise RuntimeError("Choose a new installation directory; existing files are not overwritten.")
        shutil.copytree(source, destination)
        for name in ["verus", "rust_verify", "z3", "cargo-verus"]:
            (destination / name).chmod(0o755)
        print(destination / "verus")


if __name__ == "__main__":
    main()
