<!-- SPDX-License-Identifier: MPL-2.0 -->

# Checked extent edits and rebuilt forests

Extent17 discharges 219 focused obligations and compiles the exact owned extent implementation.
The source preserves the existing 21 runtime APIs and six public proof interfaces.
The check covers the full successful-result mapping, physical nonalias, canonical layout,
ordered child/subtree interval and incoming-reference contracts.
It does not establish success iff admission or an entire-filesystem proof.

| Design component | Checked contract | Remaining integration |
| --- | --- | --- |
| Sorted extent admission | Valid ordered intervals, canonical written/unwritten splitting and merging, exact mapping and physical nonalias | Source-owned bitmap and allocator admission |
| Insert, replace, punch and truncate | Exact resulting logical map; holes remain holes outside the specified edit; aliases are rejected | Inode sizes, zeroing, quotas, revokes and journal after-images |
| Initialized/unwritten conversion | Exact physical mapping and requested state, with rejection of holes and invalid fragment coordinates | Real data initialization and completion authority |
| Leaf and index encoding | Linux capacities, length sentinels, exact byte fields, reserved-byte framing and inode-context CRC | Coherent captured source and allocated metadata ownership |
| Rebuilt forest | Depth 0–5; emitted leaves reproduce the complete run list; children refer to earlier nodes with matching keys/depths and ordered subtree ranges | Source catalogue ownership and transactional publication |
| Metadata references | Supplied pool prefix is used exactly, unused suffix is returned, addresses exclude final data, and every emitted node has exactly one incoming tree reference | Allocator lifetime, crash/replay integration and retirement |
| Framekernel boundary | Owned Rust byte images and supplied block-number descriptions only | Refinement through safe CortenMM/USegment and VmReader/VmWriter adapters |

Private proof lemmas carry source run-index intervals, earlier-child witnesses and a mixed frontier of
new parents followed by unconsumed children.
A conservation equation accounts for every incoming reference.
Pointwise child and record predicates retain their complete definitions and are explicitly proved before assembly;
they add no trusted assumptions or executable capabilities.
No solver limit is increased.

## Exact focused evidence

| Item | Value |
| --- | --- |
| Snapshot | proof-extent-edit-17 |
| Result | 219 obligations, 0 errors, compiled; module-filtered diagnostic |
| Source | e9818efaeb25f98dd99e0a812b0f7c40d8f1fefd006d46aa6e81e656f1e09c20 |
| Compiled rlib | 64209b72ed56c9e38ea703850a6db0d9d15ba7f1a39ae3b5454f23d4340927d1 |
| Verus | release/0.2026.11.02.8bf68ee, pinned commit 8bf68ee741df833ea5d0fe6a2255126fdea87e47 |
| Linux reference | extents.c at 028ef9c96e96197026887c0f092424679298aae8 |

The immutable command, output and source manifest remain under
/task/ext4-expansion/proof-extent-edit-17.
The command selects only extent_edit and is a focused diagnostic,
not the official unfiltered strict --no-cheating whole-crate gate.
The previous 3,142-obligation baseline evidence and pinned inventories remain unchanged.

This branch records 2,166 focused obligations across 31 modules in 27 current diagnostic entries.
The registry remains 258 source files, 985 named proofs and 1,249 public executable functions.
Private lemmas increase discharged obligations without adding public executable APIs or changing that registry.

## Native validation of the checked artifact

Extent-checked-native-17 links the actual focused artifact with the pinned Rust compiler.
It supplies no replacement extent implementation and no mechanically erased source copy.
The old extent test bodies are extracted byte-for-byte from the previous driver;
the original selected golden inputs remain unchanged.

| Validation | Result |
| --- | ---: |
| Explicit assertions | 219,125 |
| Original block-size/requested-minimum-depth/checksum matrix | 84 combinations, plus empty tree |
| Positive whole-tree audits | 88 |
| Whole-tree lookup probes | 950 |
| Capacity and returned-pool reuse cases across all seven block sizes | 28 |
| Leaf records decoded through actual node readers in the capacity cases | 108,298 |
| Additional explicit rejection checks | 33 |
| Independently generated e2fsprogs extent roots rebuilt byte-for-byte | 3 |
| Independent debugfs mappings, including holes and unwritten allocation | 15 |
| Images accepted by read-only e2fsck | 2 |

The runtime was 3.60 seconds.
Each child had a 2 GiB address-space and 60 CPU-second limit;
the largest full snapshot in the driver was 125 MiB.
Large capacity cases inspected actual emitted node blocks without allocating filesystem-sized snapshots.

The detailed result, source/provider/driver/golden bindings and command logs remain under
/task/ext4-expansion/extent-checked-native-17.
The result hash is ce99e0f9e6e56fec6bb8c0390a2dd09d7d30a0b04b87f34cfc15d24c9d3e662a.
The bindings hash is 12ca2102d92488c81fecb981e3144546433930bb27d43f1a02b483b1f62ec402.
The Linux-format oracle is e2fsprogs userspace tooling; no Linux kernel was mounted.

## Composition and authority boundary

TC21 and its six-family native/API results retain the older extent901d33e source.
They are historical after this replacement and their current-source matches are false.
The focused and native results above are the evidence for the exact new extent bytes.
A new combined compile, strict dependency/whole-crate proof and full official compatibility run are not claimed here.

Extent plans describe owned byte images and checked supplied block numbers.
They do not mint allocation ownership, initialized-data authority, a stable physical source,
an inode or namespace capability, device-write permission, a writable mount or durability.
Framekernel integration must retain safe CortenMM/OSTD ownership and lending;
no Linux page, folio or buffer_head ownership is imported.
Feature gates, baseline reports, toolchain trust settings and production activation remain unchanged.
