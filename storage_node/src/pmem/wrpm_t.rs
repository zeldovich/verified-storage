use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {
/// A `WriteRestrictedPersistentMemoryRegions` is a wrapper around a
/// collection of persistent memory regions that restricts how it can
/// be written. Specifically, it only permits a write if it's
/// accompanied by a tracked permission authorizing that write. The
/// tracked permission must authorize every possible state that could
/// result from crashing while the write is ongoing.

pub trait CheckPermission<ID, State>
{
    spec fn check_permission(&self, state: State) -> bool;
    spec fn valid(&self, id: ID) -> bool;
}

#[allow(dead_code)]
pub struct WriteRestrictedPersistentMemoryRegions<ID, Perm, PMRegions>
    where
        Perm: CheckPermission<ID, Seq<Seq<u8>>>,
        PMRegions: PersistentMemoryRegions
{
    pm_regions: PMRegions,
    ghost id: Option<ID>,
    ghost perm: Option<Perm>, // Needed to work around Rust limitation that Perm must be referenced
}

impl<ID, Perm, PMRegions> WriteRestrictedPersistentMemoryRegions<ID, Perm, PMRegions>
    where
        Perm: CheckPermission<ID, Seq<Seq<u8>>>,
        PMRegions: PersistentMemoryRegions
{
    pub closed spec fn view(&self) -> PersistentMemoryRegionsView
    {
        self.pm_regions@
    }

    pub closed spec fn inv(&self) -> bool
    {
        self.pm_regions.inv()
    }

    pub closed spec fn constants(&self) -> PersistentMemoryConstants
    {
        self.pm_regions.constants()
    }

    pub exec fn new(pm_regions: PMRegions) -> (wrpm_regions: Self)
        requires
            pm_regions.inv()
        ensures
            wrpm_regions.inv(),
            wrpm_regions@ == pm_regions@,
            wrpm_regions.constants() == pm_regions.constants(),
    {
        Self {
            pm_regions: pm_regions,
            id: None,
            perm: None
        }
    }

    // This executable function returns an immutable reference to the
    // persistent memory regions. This can be used to perform any
    // operation (e.g., read) that can't mutate the memory. After all,
    // this is a write-restricted memory, not a read-restricted one.
    pub exec fn get_pm_regions_ref(&self) -> (pm_regions: &PMRegions)
        requires
            self.inv(),
        ensures
            pm_regions.inv(),
            pm_regions@ == self@,
            pm_regions.constants() == self.constants(),
    {
        &self.pm_regions
    }

    // This executable function is the only way to perform a write, and
    // it requires the caller to supply permission authorizing the
    // write. The caller must prove that for every state this memory
    // can crash and recover into, the permission authorizes that
    // state.
    #[allow(unused_variables)]
    pub exec fn write(&mut self, index: usize, addr: u64, bytes: &[u8], perm: Tracked<&Perm>)
        requires
            old(self).inv(),
            index < old(self)@.len(),
            addr + bytes@.len() <= old(self)@[index as int].len(),
            addr + bytes@.len() <= u64::MAX,
            old(self)@.no_outstanding_writes_in_range(index as int, addr as int, addr + bytes@.len()),
            // The key thing the caller must prove is that all crash states are authorized by `perm`
            forall |s| old(self)@.write(index as int, addr as int, bytes@).can_crash_as(s)
                  ==> #[trigger] perm@.check_permission(s),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self@ == old(self)@.write(index as int, addr as int, bytes@),
    {
        self.pm_regions.write(index, addr, bytes)
    }

    #[allow(unused_variables)]
    pub exec fn serialize_and_write<S>(&mut self, index: usize, addr: u64, to_write: &S, perm: Tracked<&Perm>)
        where
            S: PmCopy + Sized
        requires
            old(self).inv(),
            index < old(self)@.len(),
            addr + S::spec_size_of() <= old(self)@[index as int].len(),
            old(self)@.no_outstanding_writes_in_range(index as int, addr as int, addr + S::spec_size_of()),
            // The key thing the caller must prove is that all crash states are authorized by `perm`
            forall |s| old(self)@.write(index as int, addr as int, to_write.spec_to_bytes()).can_crash_as(s)
                  ==> #[trigger] perm@.check_permission(s),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self@ == old(self)@.write(index as int, addr as int, to_write.spec_to_bytes()),
    {
        self.pm_regions.serialize_and_write(index, addr, to_write);
    }

    // Even though the memory is write-restricted, no restrictions are
    // placed on calling `flush`. After all, `flush` can only narrow
    // the possible states the memory can crash into. So if the memory
    // is already restricted to only crash into good states, `flush`
    // automatically maintains that restriction.
    pub exec fn flush(&mut self)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            self@ == old(self)@.flush(),
            self.constants() == old(self).constants(),
            forall |i: int| #![auto] 0 <= i < self@.len() ==> old(self)@[i].len() == self@[i].len()
    {
        self.pm_regions.flush()
    }
}

pub trait WriteRestrictedPersistentMemoryRegionTrait<Perm, ID> where Perm: CheckPermission<ID, Seq<u8>> {
    spec fn view(&self) -> PersistentMemoryRegionView;
    spec fn inv(&self) -> bool;
    spec fn constants(&self) -> PersistentMemoryConstants;
    spec fn id(&self) -> ID;

    // This executable function is the only way to perform a write, and
    // it requires the caller to supply permission authorizing the
    // write. The caller must prove that for every state this memory
    // can crash and recover into, the permission authorizes that
    // state.
    exec fn write(&mut self, addr: u64, bytes: &[u8], perm: Tracked<&Perm>)
        requires
            old(self).inv(),
            perm@.valid(old(self).id()),
            addr + bytes@.len() <= old(self)@.len(),
            addr + bytes@.len() <= u64::MAX,
            old(self)@.no_outstanding_writes_in_range(addr as int, addr + bytes@.len()),
                // The key thing the caller must prove is that all crash states are authorized by `perm`
            forall |s| old(self)@.write(addr as int, bytes@).can_crash_as(s)
                  ==> #[trigger] perm@.check_permission(s),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self.id() == old(self).id(),
            self@ == old(self)@.write(addr as int, bytes@);

    exec fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S, perm: Tracked<&Perm>)
        where
            S: PmCopy + Sized
        requires
            old(self).inv(),
            addr + S::spec_size_of() <= old(self)@.len(),
            old(self)@.no_outstanding_writes_in_range(addr as int, addr + S::spec_size_of()),
            // The key thing the caller must prove is that all crash states are authorized by `perm`
            forall |s| old(self)@.write(addr as int, to_write.spec_to_bytes()).can_crash_as(s)
                  ==> #[trigger] perm@.check_permission(s),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self.id() == old(self).id(),
            self@ == old(self)@.write(addr as int, to_write.spec_to_bytes());

    // Even though the memory is write-restricted, no restrictions are
    // placed on calling `flush`. After all, `flush` can only narrow
    // the possible states the memory can crash into. So if the memory
    // is already restricted to only crash into good states, `flush`
    // automatically maintains that restriction.
    exec fn flush(&mut self)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self.id() == old(self).id(),
            self@ == old(self)@.flush();

    // Pass through read-only functions from PersistentMemoryRegion.
    exec fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized,
        requires
            self.inv(),
            0 <= addr < addr + S::spec_size_of() <= self@.len(),
            self@.no_outstanding_writes_in_range(addr as int, addr + S::spec_size_of()),
            // We must have previously written a serialized S to this addr
            S::bytes_parseable(self@.committed().subrange(addr as int, addr + S::spec_size_of()))
        ensures
            match bytes {
                Ok(bytes) => {
                    let true_bytes = self@.committed().subrange(addr as int, addr + S::spec_size_of());
                    let addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| i + addr);
                    // If the persistent memory regions are impervious
                    // to corruption, read returns the last bytes
                    // written. Otherwise, it returns a
                    // possibly-corrupted version of those bytes.
                    if self.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    }
                    else {
                        maybe_corrupted(bytes@, true_bytes, addrs)
                    }
                }
                _ => false
            };

    exec fn get_region_size(&self) -> (result: u64)
        requires
            self.inv()
        ensures
            result == self@.len();

    exec fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>)
        requires
            self.inv(),
            addr + num_bytes <= self@.len(),
            self@.no_outstanding_writes_in_range(addr as int, addr + num_bytes),
        ensures
            match bytes {
                Ok(bytes) => {
                    let true_bytes = self@.committed().subrange(addr as int, addr + num_bytes);
                    let addrs = Seq::<int>::new(num_bytes as nat, |i: int| i + addr);
                    &&& // If the persistent memory regions are impervious
                        // to corruption, read returns the last bytes
                        // written. Otherwise, it returns a
                        // possibly-corrupted version of those bytes.
                        if self.constants().impervious_to_corruption {
                            bytes@ == true_bytes
                        }
                        else {
                            maybe_corrupted(bytes@, true_bytes, addrs)
                        }
                    }
                _ => false
            };
}

#[allow(dead_code)]
pub struct WriteRestrictedPersistentMemoryRegion<ID, Perm, PMRegion>
    where
        Perm: CheckPermission<ID, Seq<u8>>,
        PMRegion: PersistentMemoryRegion
{
    pm_region: PMRegion,
    ghost id: Option<ID>,
    ghost perm: Option<Perm>, // Needed to work around Rust limitation that Perm must be referenced
}

impl<ID, Perm, PMRegion> WriteRestrictedPersistentMemoryRegionTrait<Perm, ID> for WriteRestrictedPersistentMemoryRegion<ID, Perm, PMRegion>
    where
        Perm: CheckPermission<ID, Seq<u8>>,
        PMRegion: PersistentMemoryRegion
{
    closed spec fn view(&self) -> PersistentMemoryRegionView
    {
        self.pm_region@
    }

    closed spec fn inv(&self) -> bool
    {
        self.pm_region.inv()
    }

    closed spec fn constants(&self) -> PersistentMemoryConstants
    {
        self.pm_region.constants()
    }

    open spec fn id(&self) -> ID {
        arbitrary()
    }

    // This executable function is the only way to perform a write, and
    // it requires the caller to supply permission authorizing the
    // write. The caller must prove that for every state this memory
    // can crash and recover into, the permission authorizes that
    // state.
    #[allow(unused_variables)]
    exec fn write(&mut self, addr: u64, bytes: &[u8], perm: Tracked<&Perm>)
    {
        let ghost pmr = self.pm_region;
        self.pm_region.write(addr, bytes);
    }

    #[allow(unused_variables)]
    exec fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S, perm: Tracked<&Perm>)
        where
            S: PmCopy + Sized
    {
        self.pm_region.serialize_and_write(addr, to_write);
    }

    // Even though the memory is write-restricted, no restrictions are
    // placed on calling `flush`. After all, `flush` can only narrow
    // the possible states the memory can crash into. So if the memory
    // is already restricted to only crash into good states, `flush`
    // automatically maintains that restriction.
    exec fn flush(&mut self)
    {
        self.pm_region.flush()
    }

    exec fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized
    {
        self.pm_region.read_aligned(addr)
    }

    exec fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>)
    {
        self.pm_region.read_unaligned(addr, num_bytes)
    }

    exec fn get_region_size(&self) -> (result: u64)
    {
        self.pm_region.get_region_size()
    }
}

impl<ID, Perm, PMRegion> WriteRestrictedPersistentMemoryRegion<ID, Perm, PMRegion>
    where
        Perm: CheckPermission<ID, Seq<u8>>,
        PMRegion: PersistentMemoryRegion
{
    pub exec fn new(pm_region: PMRegion) -> (wrpm_region: Self)
        requires
            pm_region.inv(),
        ensures
            wrpm_region.inv(),
            wrpm_region@ == pm_region@,
            wrpm_region.constants() == pm_region.constants(),
    {
        Self {
            pm_region: pm_region,
            id: None,
            perm: None
        }
    }

    // This executable function returns an immutable reference to the
    // persistent memory region. This can be used to perform any
    // operation (e.g., read) that can't mutate the memory. After all,
    // this is a write-restricted memory, not a read-restricted one.
    pub exec fn get_pm_region_ref(&self) -> (pm_region: &PMRegion)
        requires
            self.inv(),
        ensures
            pm_region.inv(),
            pm_region@ == self@,
            pm_region.constants() == self.constants(),
    {
        &self.pm_region
    }
}
}
