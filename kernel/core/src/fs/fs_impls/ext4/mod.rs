// SPDX-License-Identifier: MPL-2.0

//! Implementation-only ext4 device boundary.
//!
//! No filesystem type is registered. Kernel source capture, DMA command
//! ownership and completion plumbing await refinement to the verified core;
//! device leases and persistence contracts cannot be inferred from sectors.

pub(super) mod device;
