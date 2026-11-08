<!-- SPDX-License-Identifier: MPL-2.0 -->

# no_std source package

This isolated prototype packages the ext4 core as a Cargo library based on
a11d5ecc9217d2fd5d78109796cba776f2bfd6dd. The nested workspace leaves the kernel
workspace unchanged. It has passed host and x86_64-unknown-none Cargo checks
under nightly-2026-07-21, plus a pinned Verus frontend/compile-only check.
These are compilation diagnostics, not a formal certificate or kernel linkage.

Cargo.toml pins official vstd revision
8bf68ee741df833ea5d0fe6a2255126fdea87e47 with default features disabled and alloc
enabled. Cargo.lock is retained. The dependency feature audit confirms alloc
present and std absent. Official ghost-erasing macros compile the original
sources; vstd's alloc-enabled VecAdditionalExecFns implements Vec.set and
set_and_swap. No handwritten erasure or compatibility implementations are used.

The source changes are explicit Vec imports in 109 modules, no_std plus alloc
at the root, ghost-compatible import groups in 21 files, and six spec/proof
references qualified to their original crate::group::encoded_le definition.
Executable statements are unchanged. NOSTD_SOURCE_MAP.json records original
and packaged hashes, every import rewrite, the six qualifications and evidence.
Two aliases of already-public proof lemmas are also exposed by the import
repair; runtime public capabilities are unchanged.

The pinned inventories remain 258 files, 972 proof names and 1249 executable
names. toolchain.lock.json, proof-status.json, verification-evidence.json and
the verifier gates are unchanged. Those inventories and existing baseline
evidence do not certify this packaging change.

## Reproduce the Cargo checks

Run from the repository root with the pinned kernel toolchain. The recorded
runs used these compiler settings, one job and an external target directory:

    export RUSTC=/root/.rustup/toolchains/nightly-2026-07-21-x86_64-unknown-linux-gnu/bin/rustc
    export RUSTDOC=/root/.rustup/toolchains/nightly-2026-07-21-x86_64-unknown-linux-gnu/bin/rustdoc
    export CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 CARGO_PROFILE_DEV_DEBUG=0
    export CARGO_TARGET_DIR=/task/ext4-no-std-packaging/target-nightly

Use normal configured proxy/CA trust when dependencies need fetching. Then:

    /root/.rustup/toolchains/nightly-2026-07-21-x86_64-unknown-linux-gnu/bin/cargo check --manifest-path proofs/ext4/Cargo.toml --lib --locked
    /root/.rustup/toolchains/nightly-2026-07-21-x86_64-unknown-linux-gnu/bin/cargo check --manifest-path proofs/ext4/Cargo.toml --lib --target x86_64-unknown-none --locked
    /root/.rustup/toolchains/nightly-2026-07-21-x86_64-unknown-linux-gnu/bin/cargo tree --manifest-path proofs/ext4/Cargo.toml --target x86_64-unknown-none -e features --locked

The recorded host command omitted --locked; future replays should retain it.
Exact original argv, environments, source hashes and results are retained in
NOSTD_SOURCE_MAP.json and the task-local directories below.

| Check | Result | Task-local evidence |
| --- | --- | --- |
| Host Cargo check | Passed, 11.67s | /task/ext4-no-std-packaging/host-check-03 |
| Bare-metal target check | Passed, 9.93s | /task/ext4-no-std-packaging/target-check-02 |
| Dependency feature audit | alloc present; std absent | /task/ext4-no-std-packaging/feature-audit-01 |
| Pinned Verus frontend and compile | Passed, 73.26s; verification skipped | /task/ext4-expansion/typecheck-no-std-02 |

Cargo checks were capped at 180 seconds and 4 GiB of address space; the
feature audit had a 30-second limit.

## Verus diagnostic scope

The immutable frontend snapshot includes the baseline and all 32 feature
modules, with no exclusions. Its orchestrator only reordered those module
declarations in model.rs; all other 257 source hashes match this package.
It ran the following from that snapshot using Verus 0.2026.11.02.8bf68ee
and its Rust 1.99.1 toolchain:

    /workspace/scratch/verus/run --no-verify --no-external-by-default --output-json --compile --crate-type=rlib --crate-name=verified_ext4 --out-dir=build src/model.rs

The --no-verify diagnostic does not run SMT proof obligations and does not
replace tools/verify.py. A new strict run and binding between proof features,
official erasure, the kernel compiler and target remain required.

Host rlibs and prebuilt host proc-macro binaries must not be linked into the
kernel. Kernel Cargo must compile the package and dependencies under the kernel
toolchain, with OSDK's target/sysroot and code-generation settings. This branch
adds no kernel dependency, FsType registration, CortenMM freeze/refinement,
writable lease factory or durability acknowledgement.
