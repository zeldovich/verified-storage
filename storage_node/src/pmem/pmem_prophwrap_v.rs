use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmem_prophspec_v::*;
use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {

pub struct PMRegionProph<PMRegion>
    where PMRegion: PersistentMemoryRegionRaw
{
    pm: PMRegion,
    view: Ghost<PersistentMemoryRegionView>,
}

impl<PMRegion> PersistentMemoryRegion for PMRegionProph<PMRegion>
    where PMRegion: PersistentMemoryRegionRaw
{
    closed spec fn view(&self) -> PersistentMemoryRegionView {
        self.view@
    }

    closed spec fn inv(&self) -> bool {
        &&& self.pm.inv()
        &&& self.view@.read_state == self.pm@.flush().committed()
        &&& self.view@.durable_state == self.pm@.committed()
    }

    closed spec fn constants(&self) -> PersistentMemoryConstants {
        self.pm.constants()
    }

    fn get_region_size(&self) -> u64 {
        self.pm.get_region_size()
    }

    fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
        where S: PmCopy + Sized
    {
        self.pm.read_aligned::<S>(addr)
    }

    fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>)
    {
        self.pm.read_unaligned(addr, num_bytes)
    }

    fn write(&mut self, addr: u64, bytes: &[u8])
    {
        self.pm.write(addr, bytes)
    }

    fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S)
        where S: PmCopy + Sized
    {
        self.pm.serialize_and_write(addr, to_write)
    }

    fn flush(&mut self)
    {
        self.pm.flush()
    }
}

impl<PMRegion> PMRegionProph<PMRegion>
    where PMRegion: PersistentMemoryRegionRaw
{
    pub fn new(pm: PMRegion) -> (result: PMRegionProph<PMRegion>)
        requires
            pm.inv()
        ensures
            result.inv(),
            result@.read_state == pm@.flush().committed(),
            result@.durable_state == pm@.committed(),
    {
        PMRegionProph::<PMRegion>{
            pm: pm,
            view: Ghost(PersistentMemoryRegionView{
                read_state: pm@.flush().committed(),
                durable_state: pm@.committed(),
            }),
        }
    }
}
}
