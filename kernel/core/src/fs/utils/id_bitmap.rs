// SPDX-License-Identifier: MPL-2.0

use core::ops::Range;

use aster_block::BLOCK_SIZE;
use bitvec::{
    order::Lsb0,
    slice::BitSlice,
    view::{AsBits, AsMutBits},
};

use crate::prelude::*;

/// A disk I/O-friendly bitmap for ID management (e.g., block or inode IDs).
///
/// An ID bitmap has the same size as a block, i.e., `BLOCK_SIZE`.
/// Each bit in the bitmap represents one ID:
/// bit 0 at the i-th position of the bitmap means the i-th ID is free
/// and bit 1 means the ID is in use.
/// As such, the bitmap can contain contain at most `BLOCK_SIZE` * 8 bits/IDs.
#[derive(Clone)]
pub(crate) struct IdBitmap {
    buf: Box<[u8]>,
    first_available_id: u16,
    len: u16,
}

impl IdBitmap {
    // Bulk filling costs more than individual bit updates for these tiny ranges.
    const SMALL_RANGE_MAX_LEN: usize = 2;

    /// Creates a new ID bitmap out of a given buffer, whose first `len`-bits represent valid IDs.
    ///
    /// # Panics
    ///
    /// This method panics if `len` is greater than [`IdBitmap::capacity()`].
    pub(crate) fn from_buf(buf: Box<[u8]>, len: u16) -> Self {
        assert!(len <= Self::capacity());
        let mut bitmap = Self {
            buf,
            first_available_id: 0,
            len,
        };

        bitmap.update_first_available_id(0);
        bitmap
    }

    /// Returns the length of the ID bitmap, i.e., the maximum number of IDs.
    #[expect(unused)]
    pub(crate) const fn len(&self) -> u16 {
        self.len
    }

    /// Returns the capacity of the ID bitmap.
    ///
    /// The capacity is the size of the underlying buffer in bits.
    pub(crate) const fn capacity() -> u16 {
        BLOCK_SIZE as u16 * 8
    }

    /// Returns a reference to the underlying buffer of `BLOCK_SIZE` bytes.
    pub(crate) fn as_bytes(&self) -> &[u8] {
        &self.buf
    }

    fn bit_slice(&self) -> &BitSlice<u8, Lsb0> {
        &self.buf.as_bits()[..self.len as usize]
    }

    fn bit_slice_mut(&mut self) -> &mut BitSlice<u8, Lsb0> {
        &mut self.buf.as_mut_bits()[..self.len as usize]
    }

    /// Returns true if the `id` is allocated.
    ///
    /// # Panics
    ///
    /// If the `id` is out of bounds, this method will panic.
    pub(crate) fn is_allocated(&self, id: u16) -> bool {
        self.bit_slice()[id as usize]
    }

    /// Allocates and returns a new `id`.
    ///
    /// If allocation is not possible, it returns `None`.
    pub(crate) fn alloc(&mut self) -> Option<u16> {
        if self.first_available_id < self.len {
            let id = self.first_available_id;
            self.bit_slice_mut().set(id as usize, true);
            self.update_first_available_id(id + 1);
            Some(id)
        } else {
            None
        }
    }

    /// Allocates a consecutive range of new `id`s.
    ///
    /// The `count` is the number of consecutive `id`s to allocate. If it is 0, return `None`.
    ///
    /// If allocation is not possible, it returns `None`.
    pub(crate) fn alloc_consecutive(&mut self, count: u16) -> Option<Range<u16>> {
        if count == 0 {
            return None;
        }

        let end = self.first_available_id.checked_add(count)?;
        if end > self.len {
            return None;
        }

        // Scan the bitmap from the position `first_available_id`
        // for the first `count` number of consecutive 0's.
        let allocated_range = {
            // Invariance: all bits within `curr_range` are 0's.
            let bit_slice = self.bit_slice();
            let mut curr_range = self.first_available_id..self.first_available_id + 1;
            while curr_range.len() < count as usize && curr_range.end < self.len {
                if !bit_slice[curr_range.end as usize] {
                    curr_range.end += 1;
                } else {
                    curr_range = curr_range.end + 1..curr_range.end + 1;
                }
            }

            if curr_range.len() < count as usize {
                return None;
            }

            curr_range
        };

        let bits = self.bit_slice_mut();
        if allocated_range.len() <= Self::SMALL_RANGE_MAX_LEN {
            for id in allocated_range.clone() {
                bits.set(id as usize, true);
            }
        } else {
            bits[allocated_range.start as usize..allocated_range.end as usize].fill(true);
        }

        // In case we need to update `first_available_id`.
        let bit_slice = self.bit_slice();
        if bit_slice[self.first_available_id as usize] {
            self.update_first_available_id(allocated_range.end);
        }

        Some(allocated_range)
    }

    /// Releases the allocated `id`.
    ///
    /// # Panics
    ///
    /// If the `id` is out of bounds, this method will panic.
    pub(crate) fn free(&mut self, id: u16) {
        debug_assert!(self.bit_slice()[id as usize]);

        self.bit_slice_mut().set(id as usize, false);
        if id < self.first_available_id {
            self.first_available_id = id;
        }
    }

    /// Releases the consecutive range of allocated `id`s.
    ///
    /// # Panics
    ///
    /// If the `range` is out of bounds, this method will panic.
    pub(crate) fn free_consecutive(&mut self, range: Range<u16>) {
        if range.is_empty() {
            return;
        }

        let range_start = range.start;
        let bits = self.bit_slice_mut();
        if range.len() <= Self::SMALL_RANGE_MAX_LEN {
            for id in range {
                debug_assert!(bits[id as usize]);
                bits.set(id as usize, false);
            }
        } else {
            let bits = &mut bits[range.start as usize..range.end as usize];
            debug_assert!(bits.all());
            bits.fill(false);
        }

        if range_start < self.first_available_id {
            self.first_available_id = range_start
        }
    }

    /// Updates the `first_available_id` field to the first zero index at or after `start`.
    fn update_first_available_id(&mut self, start: u16) {
        let len = self.len;
        let bit_slice = self
            .bit_slice()
            .get(start as usize..len as usize)
            .expect("start is guaranteed to be valid by the caller");
        self.first_available_id = bit_slice
            .first_zero()
            .map(|offset| start + offset as u16)
            .unwrap_or(len);
    }
}

impl Debug for IdBitmap {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IdBitMap")
            .field("len", &self.len)
            .field("first_available_id", &self.first_available_id)
            .finish()
    }
}

#[cfg(ktest)]
mod test {
    use alloc::vec;

    use aster_block::BLOCK_SIZE;
    use ostd::prelude::ktest;

    use super::IdBitmap;

    #[ktest]
    fn bitmap_alloc_out_of_bounds() {
        let buf = vec![0; BLOCK_SIZE].into_boxed_slice();

        let capacity = BLOCK_SIZE as u16 * 8;
        let mut bitmap = IdBitmap::from_buf(buf, capacity);

        for _ in 0..capacity {
            assert!(bitmap.alloc().is_some());
        }

        // Allocating one more ID should fail since the
        // bitmap's `first_available_id` + `count` is out of bounds.
        assert!(bitmap.alloc_consecutive(1).is_none());
    }

    #[ktest]
    fn bitmap_ranges_preserve_neighbors_and_padding() {
        let len = IdBitmap::capacity() - 3;
        for range in [0..1, 1..8, 3..19, 7..10, 8..16, 15..len] {
            let original = vec![0xff; BLOCK_SIZE];
            let mut bitmap = IdBitmap::from_buf(original.clone().into_boxed_slice(), len);
            let mut expected = original.clone();
            for id in range.clone() {
                expected[id as usize / 8] &= !(1 << (id % 8));
            }

            bitmap.free_consecutive(range.clone());
            assert_eq!(bitmap.as_bytes(), expected);
            assert_eq!(
                bitmap.alloc_consecutive(range.end - range.start),
                Some(range)
            );
            assert_eq!(bitmap.as_bytes(), original);
            assert_eq!(bitmap.alloc(), None);
        }
    }

    #[ktest]
    fn bitmap_allocations_match_first_free_run() {
        const LEN: u16 = 8;
        for mask in 0..=u8::MAX {
            for count in 0..=LEN + 1 {
                let mut original = vec![0xff; BLOCK_SIZE];
                original[0] = mask;
                let mut bitmap = IdBitmap::from_buf(original.clone().into_boxed_slice(), LEN);
                let expected_range = (count > 0 && count <= LEN)
                    .then(|| {
                        (0..=LEN - count)
                            .find(|start| (0..count).all(|idx| mask & (1 << (start + idx)) == 0))
                            .map(|start| start..start + count)
                    })
                    .flatten();
                assert_eq!(bitmap.alloc_consecutive(count), expected_range);

                let mut expected = original.clone();
                if let Some(range) = expected_range {
                    for id in range.clone() {
                        expected[0] |= 1 << id;
                    }
                    assert_eq!(bitmap.as_bytes(), expected);
                    bitmap.free_consecutive(range);
                }
                assert_eq!(bitmap.as_bytes(), original);
                let expected_id = (0..LEN).find(|id| mask & (1 << id) == 0);
                assert_eq!(bitmap.alloc(), expected_id);
            }
        }
    }
}
