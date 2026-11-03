// SPDX-License-Identifier: MPL-2.0

//! Abstract after-image algebra, independent of ext4 byte encoding.
//! A value names the complete content of one failure-atomic storage unit.
//! It is a mathematical value, not a checksum. Codec refinement is separate.

use vstd::prelude::*;

verus! {

pub type Disk = Map<nat, nat>;

pub open spec fn overlay(home: Disk, patch: Disk) -> Disk {
    Map::new(home.dom(), |unit: nat|
        if patch.dom().contains(unit) { patch[unit] } else { home[unit] })
}

pub open spec fn compatible(before: Disk, partial: Disk, patch: Disk) -> bool {
    &&& partial.dom() == before.dom()
    &&& patch.dom().subset_of(before.dom())
    &&& forall|unit: nat|
        before.dom().contains(unit) && !patch.dom().contains(unit)
        ==> #[trigger] partial[unit] == before[unit]
}

pub proof fn overlay_preserves_domain(home: Disk, patch: Disk)
    ensures overlay(home, patch).dom() == home.dom(),
{
}

pub proof fn overlay_is_idempotent(home: Disk, patch: Disk)
    ensures overlay(overlay(home, patch), patch) == overlay(home, patch),
{
    assert_maps_equal!(
        overlay(overlay(home, patch), patch) == overlay(home, patch),
        unit => { }
    );
}

pub proof fn complete_redo_overrides_partial_checkpoint(
    before: Disk, partial: Disk, patch: Disk,
)
    requires compatible(before, partial, patch),
    ensures overlay(partial, patch) == overlay(before, patch),
{
    assert_maps_equal!(
        overlay(partial, patch) == overlay(before, patch),
        unit => {
            if before.dom().contains(unit) && !patch.dom().contains(unit) {
                assert(partial[unit] == before[unit]);
            }
        }
    );
}

}
