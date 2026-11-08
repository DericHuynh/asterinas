<!-- SPDX-License-Identifier: MPL-2.0 -->

# Captured RAM snapshot bridge

This integration branch adds the existing no_std proof-core package as a normal
source dependency of aster-core. The package remains excluded from root workspace
membership so its nested workspace and lints remain intact. Kernel dependency
resolution uses the root Cargo.lock; proofs/ext4/Cargo.lock does not constrain it.

CapturedSource::with_snapshot lends its immutable owned bytes to
verified_ext4::snapshot::Snapshot. Both callback lifetimes are higher-ranked and
the result type is outside those binders. Borrowed snapshots, blocks or
namespaces derived from the argument cannot escape through that result; callers
can retain owned results. No frame memory is cast to a Rust slice. Device reads
still pass through privately owned CortenMM USegment buffers and VmIo copying
before the image is lent to the core.

This view describes a RAM sample. It does not establish coherent physical
capture, stable device identity, exclusion from other writers, filesystem
admission, permission to mount or write, or hardware persistence. FsType
registration and the production write-lease factory remain absent.

The new captured_source_lends_bounded_verified_snapshot kernel test uses the
existing CortenMM MemoryDisk fixture. It checks a read crossing a 4 KiB frame
boundary, a 1 KiB filesystem SourceBlock, byte/block bounds and oversized requests,
mutation of backing frames after capture, and an owned Vec surviving capture
and device teardown. The existing three adapter tests remain available.

All files under proofs/ext4 are unchanged from 0ff4067. Its package document and
source map record the earlier standalone packaging checks. The checks below
validate this branch's separate kernel dependency wiring and RAM bridge.

## Validation

| Check | Actual result | Task-local evidence |
| --- | --- | --- |
| Kernel-nightly OSDK source check | Passed in 155.54s; sources unchanged | /task/ext4-cortenmm-bridge/kernel-check-01 |
| Dependency feature audit | vstd alloc present; std absent | /task/ext4-cortenmm-bridge/feature-audit-01 |
| Branch-local OSDK host build | Passed in 63.94s; correct embedded source root | /task/ext4-cortenmm-bridge/hosttool-build-01 |
| Scoped snapshot guest test | 1 passed, 0 failed, 146 filtered; rc0 | /task/ext4-cortenmm-bridge/snapshot-ktest-02-classification-01 |

The named guest test is
aster_core::fs::fs_impls::ext4::device::test::captured_source_lends_bounded_verified_snapshot.
Its sources and private fixture files remained unchanged. Generated manifest
path dependencies all resolve inside this bridge worktree. The guest ran with
TCG, 1 GiB and one CPU. This is actual RAM capture/read execution, without a
physical-device coherence, filesystem admission or durability theorem.

Raw guest logs remain in snapshot-ktest-02. Its original validator falsely
reported failure because ANSI coloring surrounds ok; the separate strict
ANSI-normalized classification above records the exact test and 1/0 result.
The earlier snapshot-ktest-01 setup failure is also retained.

## Reproduce with a branch-local host tool

OSDK_LOCAL_DEV and CARGO_MANIFEST_DIR are embedded when the host tool is
compiled. Setting OSDK_LOCAL_DEV only at guest launch cannot change an existing
binary's roots. Build the tool from this worktree's osdk/Cargo.toml with
OSDK_LOCAL_DEV=1; do not reuse a local-dev binary built from another checkout.
The first failed attempt mixed that checkout's OSTD paths with this branch and
hit a Cargo lockfile package collision.

From this repository root, with the pinned kernel nightly, jobs 1,
CARGO_INCREMENTAL=0 and CARGO_PROFILE_DEV_DEBUG=0:

    OSDK_LOCAL_DEV=1 CARGO_TARGET_DIR=/task/ext4-cortenmm-bridge/osdk-host-local-01 cargo build --manifest-path osdk/Cargo.toml --bin cargo-osdk --target x86_64-unknown-linux-gnu --locked --offline

The resulting tool is
/task/ext4-cortenmm-bridge/osdk-host-local-01/x86_64-unknown-linux-gnu/debug/cargo-osdk.
Record its hash; the validated binary is
aaad03600e6cddf9bcd26275dc98b7c94260f759a066d25fc0ffb38616141732.
Full compiler/environment settings and fresh target paths are recorded in
/task/ext4-cortenmm-bridge/branch-local-hosttool-plan/commands.json.

Use that exact tool for the source check, then audit root dependency features:

    /task/ext4-cortenmm-bridge/osdk-host-local-01/x86_64-unknown-linux-gnu/debug/cargo-osdk osdk check --ktests --offline -p aster-core
    cargo tree -p aster-core --target x86_64-unknown-none -e features --locked

Keep private ext2.img, exfat.img, ltp_dev.img and nvme0n1.img files under
test/initramfs/build for the default QEMU arguments. The new test does not
validate those incidental filesystems. Do not replace root Cargo.lock with
the standalone package lock.

Run from kernel/core using a fresh generated-base target directory
(the validated run used /task/ext4-cortenmm-bridge/guest-target-02), with
MEM=1G, SMP=1, NETDEV=none, CONSOLE=ttyS0, QEMU_DISPLAY=none, VIRTIOFS=off, OVMF=off,
BOOT_METHOD=vmm-direct, BOOT_PROTOCOL=multiboot and OSDK_TARGET_ARCH=x86_64:

    /task/ext4-cortenmm-bridge/osdk-host-local-01/x86_64-unknown-linux-gnu/debug/cargo-osdk osdk test captured_source_lends_bounded_verified_snapshot --target-arch x86_64 --boot-method vmm-direct --grub-boot-protocol multiboot --qemu-args="-accel tcg" --qemu-args="-cpu max" --kcmd-args=earlycon --kcmd-args=console=ttyS0

Require the exact function name, 1 passed, 0 failed and All crates tested after
normalizing ANSI coloring. An ordinary exit 0 or a zero-test result is not
coverage. These checks do not discharge the formal transport refinement.
