<!-- SPDX-License-Identifier: MPL-2.0 -->

# Complete journal discovery for the admitted bootstrap profile

`bootstrap::projection` derives every locator field from the exact retained
source bytes: primary geometry, feature-selected metadata checksum seed,
group-zero inode table, inode 8's initialized journal extent and the journal
header's independent UUID/checksum domain. `bootstrap::admissible` requires
that projection to satisfy the complete declared bootstrap predicate.

The checked `bootstrap::locate` contract now establishes both directions:

| Executable result | Checked relation |
| --- | --- |
| Some | The result is valid, retains exactly the requested source and equals its unique projection. |
| None | The requested source does not satisfy the declared bootstrap predicate. |

Every valid BootstrapView equals that projection, and valid views of identical
bytes have identical fields. No equality of CRC values substitutes for exact
source identity. These results apply to every constructed Snapshot, including
all admitted shadow depths zero through 32. Discovery still does not depend on
consistent home allocation bitmaps, which may require journal repair.

## Inode-table address correction

The locator now rejects inode table block zero before reading inode 8.
Linux v7.0 `__ext4_get_inode_loc`, in
[the pinned inode.c](https://github.com/torvalds/linux/blob/028ef9c96e96197026887c0f092424679298aae8/fs/ext4/inode.c),
rejects table addresses at or below s_first_data_block. That first block is zero
in the current 4 KiB profile. Whole-image allocation already rejects this alias;
the correction enforces it earlier at journal discovery.

The regression places inode 8 inside the primary superblock, moves the bitmap
addresses to keep the descriptor locally valid, and solves the coupled inode
and superblock CRC equations using an unused superblock word. Thus all three
metadata checksum/parser checks pass before the address check is exercised.
The verified pre-fix build accepts this fixture, and the corrected locator
rejects it. The test is host regression evidence; the formal guarantee comes
from the checked locator contract and its positive table bound.

A separate host check overlays exact primary, descriptor, table and journal
blocks through all 32 supported layers while a home bitmap is inconsistent.
Journal discovery retains the same mapping and bytes at every admitted depth;
the source layer limit still rejects an additional overlay.

| Obligation | Result | Remaining scope |
| --- | --- | --- |
| J-LOCATE | Exact source projection, unique fields and complete bounded discovery; zero table rejected before inode read | Discovery after every physical crash source still needs bootstrap preservation |
| F-ADMIT | Locator Some/None matches its admitted predicate | Complete filesystem, recovery and mount admission remain open |
| F-PARSE | Existing total parsers/range checks compose in both locator directions | Other block/inode/journal layouts and full ext4 features |
| S-ENTRY | The existing private retained-source Bootstrap type keeps its exact source binding | Actual CortenMM source capture, locks, DMA and kernel entry |

This is completeness of journal location for the existing bounded profile,
not completeness of filesystem validation, recovery preparation or recovery
admission. Fresh-process crash reconstruction, actual I/O quiescence and driver
contracts, concurrent journal operation and full ext4 coverage remain open.
Kernel mount/write gates remain closed.
