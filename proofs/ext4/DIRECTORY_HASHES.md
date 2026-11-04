<!-- SPDX-License-Identifier: MPL-2.0 -->

# Unkeyed ext4 filename hashes

`dir_hash.rs` independently implements Linux ext4's six unkeyed hash IDs:
legacy, half-MD4 and TEA, each with signed-byte and unsigned-byte variants. It
accepts byte strings up to 255 bytes and rejects unsupported IDs and oversized
inputs through a total public API. Hashing a byte string does not validate a
directory name or establish allocation, namespace or credential authority.

Reference: Linux v7.0 commit `028ef9c96e96197026887c0f092424679298aae8`,
`fs/ext4/hash.c`. The implementation uses explicit mathematical 32-bit modular
arithmetic, fixed round-state transitions and a separate total executable path.
It does not import Linux pages, buffers or ownership. CortenMM/OSTD source and
runtime integration remain separate.

| Component | Implemented contract | Remaining work |
| --- | --- | --- |
| Word operations | Exact 32-bit modular addition, signed/unsigned byte lifting and rotation | No cryptographic-security assertion |
| Input packing | Length-derived padding, four-byte groups and exact partial-word treatment | Unicode normalization/casefold policy |
| Seed selection | Four source word inputs; all-zero seed selects Linux's default words | Source superblock seed/flag binding in complete directory admission |
| Legacy | Exact byte recurrence and normalization; no minor hash | Full source directory lookup composition |
| Half-MD4 | Three eight-step rounds, word permutation, rotation and feed-forward over 32-byte chunks | Full source directory lookup composition |
| TEA | Sixteen mixing rounds and feed-forward over 16-byte chunks | Full source directory lookup composition |
| Result | Exact major/minor words, low collision bit clear, reserved EOF value excluded | Keyed SipHash/fscrypt and encrypted/casefold combinations |

Executable round and chunk loops refine the mathematical state recurrences.
Hashes are bucket selectors. Full-key comparison remains mandatory, and no
collision-resistance assumption is made. The standalone HTree routing codec and
these hashes do not open DIR_INDEX admission; complete tree/leaf/key equivalence
and source ownership checks remain required, as do split/merge and journalled
mutation proofs.

Native interoperability checks compare all six variants to debugfs/libext2fs
with default and nonzero seeds, UTF-8 bytes that distinguish signed and unsigned
variants, maximum-length inputs and word/16-byte/32-byte round boundaries.
Boundary tests check unsupported versions, oversized input and reserved result
bits. Exact pinned whole-crate Verus evidence is recorded separately.
