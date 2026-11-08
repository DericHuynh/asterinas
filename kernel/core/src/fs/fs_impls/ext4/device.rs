// SPDX-License-Identifier: MPL-2.0

//! Owned CortenMM/OSTD bounce buffers for the initial 4 KiB ext4 transport.
//!
//! This is an implementation boundary awaiting the core-to-device refinement
//! proof. A completed write is not a durability acknowledgement. There is no
//! production constructor for `WriteLease`: neither a sector size nor a
//! successful Flush BIO establishes the required exclusive-access, atomic-write,
//! drain and reset contracts.
//!
//! Capture returns immutable owned bytes, not a coherent-device lease. Other
//! device users may change storage during or after capture. Device admission
//! must separately establish exclusion and source identity before using those
//! bytes to authorize I/O.
//!
//! I/O methods allocate DMA mappings and may sleep. They must be called from
//! normal task context with IRQs enabled, without a spinlock or atomic-mode
//! guard held.

use alloc::{boxed::Box, sync::Arc, vec, vec::Vec};
use core::{fmt, ops::Range};

use aster_block::{
    BLOCK_SIZE, BlockDevice, SECTOR_SIZE,
    bio::{Bio, BioDirection, BioEnqueueError, BioSegment, BioStatus, BioType},
    id::Sid,
};
use device_id::DeviceId;
use ostd::mm::{FrameAllocOptions, PAGE_SIZE, USegment, VmIo};

const FS_BLOCK_BYTES: usize = 4096;
const SECTORS_PER_BLOCK: u64 = 8;

type Result<T> = core::result::Result<T, Error>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Error {
    UnsupportedGeometry,
    OutOfBounds,
    InvalidImage,
    CaptureTooLarge,
    NoMemory,
    DeviceChanged,
    WrongLease,
    FaultedLease,
    Memory(ostd::Error),
    Enqueue(BioEnqueueError),
    Io(BioStatus),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DeviceBinding {
    id: DeviceId,
    sectors: u64,
}

/// A read-only sample of the selected partition, with immutable local bytes.
///
/// Its metadata records the observation; it does not prove that the device
/// matched every sampled byte at a single instant or remains unchanged.
pub(super) struct CapturedSource {
    binding: DeviceBinding,
    bytes: Box<[u8]>,
}

impl CapturedSource {
    pub(super) fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub(super) fn device_id(&self) -> DeviceId {
        self.binding.id
    }

    pub(super) fn partition_bytes(&self) -> usize {
        self.bytes.len()
    }
}

impl fmt::Debug for CapturedSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CapturedSource")
            .field("device_id", &self.binding.id)
            .field("bytes", &self.bytes.len())
            .finish_non_exhaustive()
    }
}

/// A future admitted protected-window lease.
///
/// Fields are private and no production factory is supplied. Adding one
/// requires the device/partition exclusion, persistence and reset refinement,
/// including aliases through raw device files and overlapping partitions.
#[must_use]
pub(super) struct WriteLease {
    device: Arc<dyn BlockDevice>,
    binding: DeviceBinding,
    blocks: Range<u64>,
    faulted: bool,
}

impl WriteLease {
    pub(super) fn is_faulted(&self) -> bool {
        self.faulted
    }
}

/// Transport bound to one actual block-device object and partition geometry.
pub(super) struct Device {
    device: Arc<dyn BlockDevice>,
    binding: DeviceBinding,
    bytes: usize,
    blocks: u64,
}

impl Device {
    pub(super) fn open(device: Arc<dyn BlockDevice>) -> Result<Self> {
        let metadata = device.metadata();
        if PAGE_SIZE != FS_BLOCK_BYTES
            || BLOCK_SIZE != FS_BLOCK_BYTES
            || SECTOR_SIZE != 512
            || metadata.max_nr_segments_per_bio == 0
        {
            return Err(Error::UnsupportedGeometry);
        }
        let bytes = metadata
            .nr_sectors
            .checked_mul(SECTOR_SIZE)
            .ok_or(Error::UnsupportedGeometry)?;
        if bytes == 0 || !bytes.is_multiple_of(FS_BLOCK_BYTES) {
            return Err(Error::UnsupportedGeometry);
        }
        let blocks =
            u64::try_from(bytes / FS_BLOCK_BYTES).map_err(|_| Error::UnsupportedGeometry)?;
        let binding = DeviceBinding {
            id: device.id(),
            sectors: u64::try_from(metadata.nr_sectors).map_err(|_| Error::UnsupportedGeometry)?,
        };
        Ok(Self {
            device,
            binding,
            bytes,
            blocks,
        })
    }

    pub(super) fn nr_blocks(&self) -> u64 {
        self.blocks
    }

    /// Capture exactly the selected partition, or return no partial source.
    ///
    /// The budget is checked before allocation or device I/O. All frame access
    /// uses OSTD's VM I/O APIs; frames are never cast into Rust byte references.
    pub(super) fn capture(&self, max_bytes: usize) -> Result<CapturedSource> {
        self.check_binding()?;
        if self.bytes > max_bytes {
            return Err(Error::CaptureTooLarge);
        }
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(self.bytes)
            .map_err(|_| Error::NoMemory)?;
        bytes.resize(self.bytes, 0);
        for (block, output) in bytes.chunks_exact_mut(FS_BLOCK_BYTES).enumerate() {
            self.read_block(
                u64::try_from(block).map_err(|_| Error::OutOfBounds)?,
                output,
            )?;
        }
        self.check_binding()?;
        Ok(CapturedSource {
            binding: self.binding,
            bytes: bytes.into_boxed_slice(),
        })
    }

    /// Copy one completed read into a caller-owned, exactly sized buffer.
    pub(super) fn read_block(&self, block: u64, output: &mut [u8]) -> Result<()> {
        if output.len() != FS_BLOCK_BYTES {
            return Err(Error::InvalidImage);
        }
        self.check_binding()?;
        let sector = self.sector(block)?;
        // This alias is confined to the call. Only the submitted BIO accesses
        // the frame until completion; the CPU copies it afterward.
        let storage = Self::allocate_frame()?;
        let segment = BioSegment::try_new_from_segment(storage.clone(), BioDirection::FromDevice)
            .map_err(Error::Memory)?;
        self.submit(Bio::new(BioType::Read, sector, vec![segment], None))?;
        self.check_binding()?;
        storage.read_bytes(0, output).map_err(Error::Memory)
    }

    /// Complete one private after-image write; this does not acknowledge
    /// durability. The image is fully copied before its DMA buffer is submitted.
    pub(super) fn write_block(
        &self,
        lease: &mut WriteLease,
        block: u64,
        image: &[u8],
    ) -> Result<()> {
        self.check_lease(lease)?;
        if image.len() != FS_BLOCK_BYTES {
            return Err(Error::InvalidImage);
        }
        let sector = self.sector(block)?;
        if !lease.blocks.contains(&block) {
            return Err(Error::OutOfBounds);
        }
        let result = (|| {
            let storage = Self::allocate_frame()?;
            storage.write_bytes(0, image).map_err(Error::Memory)?;
            // No CPU-accessible segment alias is retained or returned.
            let segment = BioSegment::try_new_from_segment(storage, BioDirection::ToDevice)
                .map_err(Error::Memory)?;
            self.submit(Bio::new(BioType::Write, sector, vec![segment], None))?;
            self.check_binding()
        })();
        if result.is_err() {
            lease.faulted = true;
        }
        result
    }

    /// Complete a Flush BIO under an admitted lease.
    ///
    /// The absent lease factory prevents interpreting an arbitrary driver's
    /// success as the model's drain guarantee. A failed attempt faults the
    /// lease; recovery needs a separately established quiescent reset.
    pub(super) fn flush(&self, lease: &mut WriteLease) -> Result<()> {
        self.check_lease(lease)?;
        let result = self
            .submit(Bio::new(BioType::Flush, Sid::new(0), Vec::new(), None))
            .and_then(|()| self.check_binding());
        if result.is_err() {
            lease.faulted = true;
        }
        result
    }

    fn check_binding(&self) -> Result<()> {
        let metadata = self.device.metadata();
        if self.device.id() != self.binding.id
            || u64::try_from(metadata.nr_sectors).ok() != Some(self.binding.sectors)
            || metadata.max_nr_segments_per_bio == 0
        {
            return Err(Error::DeviceChanged);
        }
        Ok(())
    }

    fn check_lease(&self, lease: &mut WriteLease) -> Result<()> {
        if lease.faulted {
            return Err(Error::FaultedLease);
        }
        if !Arc::ptr_eq(&self.device, &lease.device)
            || self.binding != lease.binding
            || lease.blocks.start >= lease.blocks.end
            || lease.blocks.end > self.blocks
        {
            return Err(Error::WrongLease);
        }
        if let Err(error) = self.check_binding() {
            lease.faulted = true;
            return Err(error);
        }
        Ok(())
    }

    fn sector(&self, block: u64) -> Result<Sid> {
        if block >= self.blocks {
            return Err(Error::OutOfBounds);
        }
        let first = block
            .checked_mul(SECTORS_PER_BLOCK)
            .ok_or(Error::OutOfBounds)?;
        let end = first
            .checked_add(SECTORS_PER_BLOCK)
            .ok_or(Error::OutOfBounds)?;
        if end > self.binding.sectors {
            return Err(Error::OutOfBounds);
        }
        // Partition devices apply their own offset when enqueueing the BIO.
        Ok(Sid::new(first))
    }

    fn allocate_frame() -> Result<USegment> {
        FrameAllocOptions::new()
            .alloc_segment(1)
            .map(Into::into)
            .map_err(Error::Memory)
    }

    fn submit(&self, bio: Bio) -> Result<()> {
        match bio.submit_and_wait(&*self.device).map_err(Error::Enqueue)? {
            BioStatus::Complete => Ok(()),
            status => Err(Error::Io(status)),
        }
    }
}

#[cfg(ktest)]
mod test {
    use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

    use aster_block::{BlockDeviceMeta, bio::SubmittedBio};
    use ostd::{mm::io::util::HasVmReaderWriter, prelude::*};

    use super::*;

    struct MemoryDisk {
        storage: USegment,
        submissions: AtomicUsize,
        fail_flush: AtomicBool,
    }

    impl MemoryDisk {
        fn new(blocks: usize) -> Arc<Self> {
            Arc::new(Self {
                storage: FrameAllocOptions::new()
                    .alloc_segment(blocks)
                    .unwrap()
                    .into(),
                submissions: AtomicUsize::new(0),
                fail_flush: AtomicBool::new(false),
            })
        }
    }

    impl fmt::Debug for MemoryDisk {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("Ext4MemoryDisk")
                .field("bytes", &self.storage.size())
                .finish()
        }
    }

    impl BlockDevice for MemoryDisk {
        fn enqueue(&self, bio: SubmittedBio) -> core::result::Result<(), BioEnqueueError> {
            self.submissions.fetch_add(1, Ordering::Relaxed);
            if bio.type_() == BioType::Flush {
                let status = if self.fail_flush.load(Ordering::Relaxed) {
                    BioStatus::NotSupported
                } else {
                    BioStatus::Complete
                };
                bio.complete(status);
                return Ok(());
            }
            let first = bio
                .sid_range()
                .start
                .to_raw()
                .checked_add(bio.sid_offset())
                .and_then(|sector| sector.checked_mul(SECTOR_SIZE as u64))
                .and_then(|offset| usize::try_from(offset).ok())
                .ok_or(BioEnqueueError::Refused)?;
            let bytes: usize = bio.segments().iter().map(|segment| segment.nbytes()).sum();
            if first
                .checked_add(bytes)
                .is_none_or(|end| end > self.storage.size())
            {
                return Err(BioEnqueueError::Refused);
            }
            let mut offset = first;
            for segment in bio.segments() {
                let copied = match bio.type_() {
                    BioType::Read => segment
                        .dma_slice()
                        .writer()
                        .unwrap()
                        .write(self.storage.reader().skip(offset)),
                    BioType::Write => {
                        let slice = segment.dma_slice();
                        slice
                            .mem_obj()
                            .sync_to_device(slice.offset().clone())
                            .unwrap();
                        self.storage
                            .writer()
                            .skip(offset)
                            .write(&mut slice.reader().unwrap())
                    }
                    BioType::Flush => unreachable!(),
                };
                assert_eq!(copied, segment.nbytes());
                if bio.type_() == BioType::Read {
                    let slice = segment.dma_slice();
                    slice
                        .mem_obj()
                        .sync_from_device(slice.offset().clone())
                        .unwrap();
                }
                offset += copied;
            }
            bio.complete(BioStatus::Complete);
            Ok(())
        }

        fn metadata(&self) -> BlockDeviceMeta {
            BlockDeviceMeta {
                max_nr_segments_per_bio: 1,
                nr_sectors: self.storage.size() / SECTOR_SIZE,
            }
        }

        fn name(&self) -> &str {
            "ext4-test-memory"
        }

        fn id(&self) -> DeviceId {
            DeviceId::null()
        }
    }

    // This fixture is confined to a controlled in-memory device. It is not a
    // production hardware-contract or lease factory.
    fn memory_lease(device: &Device, blocks: Range<u64>) -> WriteLease {
        WriteLease {
            device: device.device.clone(),
            binding: device.binding,
            blocks,
            faulted: false,
        }
    }

    #[ktest]
    fn capture_budget_and_source_ownership() {
        let disk = MemoryDisk::new(2);
        disk.storage.write_bytes(0, b"before").unwrap();
        let device = Device::open(disk.clone()).unwrap();
        assert_eq!(device.nr_blocks(), 2);
        assert!(matches!(
            device.capture(FS_BLOCK_BYTES),
            Err(Error::CaptureTooLarge)
        ));
        assert_eq!(disk.submissions.load(Ordering::Relaxed), 0);
        let captured = device.capture(2 * FS_BLOCK_BYTES).unwrap();
        assert_eq!(captured.partition_bytes(), 2 * FS_BLOCK_BYTES);
        assert_eq!(captured.device_id(), DeviceId::null());
        assert_eq!(&captured.bytes()[..6], b"before");
        disk.storage.write_bytes(0, b"after!").unwrap();
        assert_eq!(&captured.bytes()[..6], b"before");

        let submissions = disk.submissions.load(Ordering::Relaxed);
        let mut output = vec![0u8; FS_BLOCK_BYTES];
        assert_eq!(device.read_block(2, &mut output), Err(Error::OutOfBounds));
        assert_eq!(
            device.read_block(u64::MAX, &mut output),
            Err(Error::OutOfBounds)
        );
        assert_eq!(
            device.read_block(0, &mut output[..512]),
            Err(Error::InvalidImage)
        );
        assert_eq!(disk.submissions.load(Ordering::Relaxed), submissions);
    }

    #[ktest]
    fn private_write_buffers_and_failure_fault_the_lease() {
        let disk = MemoryDisk::new(2);
        let device = Device::open(disk.clone()).unwrap();
        let mut lease = memory_lease(&device, 1..2);
        let image = vec![0x5au8; FS_BLOCK_BYTES];
        assert_eq!(
            device.write_block(&mut lease, 0, &image),
            Err(Error::OutOfBounds)
        );
        assert_eq!(disk.submissions.load(Ordering::Relaxed), 0);
        device.write_block(&mut lease, 1, &image).unwrap();
        let mut actual = vec![0u8; FS_BLOCK_BYTES];
        disk.storage
            .read_bytes(FS_BLOCK_BYTES, &mut actual)
            .unwrap();
        assert_eq!(actual, image);
        device.flush(&mut lease).unwrap();

        disk.fail_flush.store(true, Ordering::Relaxed);
        assert_eq!(
            device.flush(&mut lease),
            Err(Error::Io(BioStatus::NotSupported))
        );
        assert!(lease.is_faulted());
        let submissions = disk.submissions.load(Ordering::Relaxed);
        assert_eq!(
            device.write_block(&mut lease, 1, &image),
            Err(Error::FaultedLease)
        );
        assert_eq!(device.flush(&mut lease), Err(Error::FaultedLease));
        assert_eq!(disk.submissions.load(Ordering::Relaxed), submissions);
    }

    #[ktest]
    fn same_device_id_does_not_allow_lease_substitution() {
        let first = Device::open(MemoryDisk::new(1)).unwrap();
        let second = Device::open(MemoryDisk::new(1)).unwrap();
        assert_eq!(first.binding, second.binding);
        let mut lease = memory_lease(&first, 0..1);
        let image = vec![0u8; FS_BLOCK_BYTES];
        assert_eq!(
            second.write_block(&mut lease, 0, &image),
            Err(Error::WrongLease)
        );
        assert!(!lease.is_faulted());
    }
}
