<!-- SPDX-License-Identifier: MPL-2.0 -->

# Sector-granular crash model

The isolated sector model has passed **37 focused Verus obligations with zero errors** and compiled successfully. The resulting library passed **seven native test families**, three intended Rust API rejections and a successful allowed-use control. This is a component result. The new 259-source branch has not received a new unfiltered strict certificate, and no mount or filesystem write path is enabled.

The branch `feat/verus-ext4-sector-crash` is based on current core commit `b1cc48460eedb0126f2fc8e2ddb8c1d897c3f19b`. It appends one module declaration, one source file, 13 named public proofs and 10 total executable APIs to the existing inventories. Existing inventory prefixes, dependency pins, flags, strict tools, admission gates and core source bodies are unchanged. The historical source preparation used `a9678467486d04dd512c6fb5fc0891a03ff4e127`; the 226 original-baseline source paths are byte-identical between those two commits. This compares those commits, including their expanded entrypoint; it does not identify that entrypoint with the initial baseline entrypoint.

## Model and checked contracts

`SectorCrash` owns one issued request's old image, full issued image, modeled stable image, stable-piece flags and exact namespace/epoch/serial/target identity. Accepted full-image lengths are 1024, 2048, 4096, 8192, 16384, 32768 and 65536 bytes. It uses owned RAM vectors, with no device or CortenMM authority.

Software completion changes only the completion bit. A stable-piece event takes the exact request identity and a checked index, then copies precisely those 512 issued bytes; it accepts no substitute payload. Completion succeeds exactly for a matching identity that has not completed. Stable-piece recording succeeds exactly for a matching identity and in-range index, including after completion. Repeated piece recording is accepted idempotently. Exhaustive error contracts identify mismatches, duplicate completion and out-of-range pieces; every rejection returns the exact unchanged valid owner. Issued bytes remain owned after completion. No cancellation, request reuse, reset or loan-release transition is supplied.

A modeled crash image retains all already stable pieces and any subset of the other issued pieces. The proof treats each modeled piece as indivisible. A physical interpretation therefore needs an additional audited atomic-piece contract. Linux's 512-byte accounting unit alone does not supply that contract; finer physical tears require a finer model.

`abstract_fence_contract` is a conditional relation between two model states for the exact request and serial cutoff. The theorem concludes issued stable bytes only under that relation. There is no executable fence-success operation, receipt type, physical receipt factory or hardware conclusion derived from a boolean.

The constructive mixed-cut witness selects one sector when two differing bytes lie in distinct sectors. The 1120/2044 example assumes both bytes differ and produces an image unequal to both complete inputs. It calculates no checksum and proves neither CRC noncollision nor universal checksum invalidity, Linux defects or accepted recovery.

The old-media embedding covers **one final event** of unchanged `write_media::apply`, under the extra `whole_image_cut` premise restricting the result to all old or all new. It does not embed arbitrary sector cuts, full schedules, concurrent queues, recovery, checkpoint or bootstrap.

| Design obligation | Checked component evidence | Remaining work |
| --- | --- | --- |
| G12: weak media | Exact issued-piece bytes, checked index, outside preservation, known-stable retention and arbitrary initial piece subsets. | Physical atomic-piece refinement and protocol composition. |
| G13: control/bootstrap tears | Constructive two-sector mixed-byte cut; native 1120/2044 example. | Checksum classification, source-owned repair, accepted recovery and repeated-crash closure. |
| G19: physical fences/reset | Exact report guards, software-completion separation and conditional single-request fence relation. | Real drain/cutoff receipts, multi-request ordering, identity uniqueness/reuse, DMA termination and reset quiescence. |
| G20: old-profile restriction | Conditional exact single-event atomic-4096 embedding. | Whole-schedule, queue and recovery refinement; strict integration. |

## Reproduction and evidence scope

[Structured status](SECTOR_CRASH_STATUS.json) binds the exact source, provider command, result, source manifest, compiled library and native fixtures. Source `src/sector_crash.rs` has SHA-256 `de504df5898b7df291faa133be28342f2c6686c28e0ae39b61b591b1fd8e103b`. The focused provider is `proof-sector-01`; its command deliberately selected only `sector_crash` and omitted `--no-cheating` for that diagnostic run. Its 37/0 result is not an unfiltered strict result.

That provider retained hashes for 259 source files. Its generated entrypoint declared 226 modules, so the compiled source closure comprises those modules plus the root: **227 files**. Every declared dependency module matches this branch exactly. The additional retained, undeclared source hashes describe provenance rather than verification coverage. The central [proof status](proof-status.json) and [verification evidence](verification-evidence.json) mark this 259-source branch pending with no whole-crate certificate or certified artifact. Each nests the complete b1cc JSON under `certified_parent_reference`, with `reference_only: true` and `applies_to_current_259_source_branch: false`; its original-file hash preserves the recorded parent provenance.

The unchanged [native tests](tests/sector_crash.rs) exercise all seven image sizes, exact piece copies, unchanged rejected owners, completion without stability, all 256 cuts of an eight-piece image, mixed bytes, whole-image masks and invalid geometry/masks. Their original preparation comments remain byte-for-byte as executed; they are historical comments, not the current result. The [allowed-use control](tests/sector_crash_allowed.rs) compiled and ran before the three negative programs from [API fixtures](tests/sector_crash_api_cases.json). Intended diagnostics were E0451 for private-owner forgery, E0432 for the nonexistent physical receipt factory and E0061 for supplying replacement piece bytes. Missing-crate errors do not count as API-boundary evidence.

The historical native run used its recorded scratch orchestrator. The new [portable replay checker](tools/check_sector_crash.py) is prepared and Python-syntax checked; it has not been run. It consumes the exact recorded compiled provider and checks hashes, declared dependency sources, pinned Rust version, all tests and the positive control before intended negative diagnostics. It writes fresh evidence without running Verus or changing any gate:

```sh
RUSTC_BIN=/path/to/pinned/rustc VERUS_LIB_DIR=/path/to/pinned/verus-libraries \
  python3 tools/check_sector_crash.py \
  --provider /path/to/proof-sector-01 --output /path/to/new-evidence-directory
```

The provider directory must contain the exact recorded artifact and proof metadata, not only an arbitrary library. Updating a provider requires an explicit new evidence review. Native RAM/API tests establish no hardware atomicity, DMA completion, physical fence or durability property.

CortenMM frames, DMA loans, allocator ownership, credentials and sealed source/device capabilities are outside this module. A future runtime refinement must retain actual owned frames and loans through errors until matching completion or proved quiescence. Vectors and numeric identities do not create those capabilities.
