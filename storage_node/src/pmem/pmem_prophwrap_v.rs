use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmem_prophspec_v::*;
use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use vstd::bytes::*;
use vstd::prelude::*;
use vstd::proph::*;

verus! {

pub struct ChunkProph {
    pub i0: Prophecy::<u64>,
    pub i1: Prophecy::<u64>,
    pub i2: Prophecy::<u64>,
    pub i3: Prophecy::<u64>,
    pub i4: Prophecy::<u64>,
    pub i5: Prophecy::<u64>,
    pub i6: Prophecy::<u64>,
    pub i7: Prophecy::<u64>,
}

impl ChunkProph {
    pub fn new() -> (res: ChunkProph)
    {
        ChunkProph{
            i0: Prophecy::<u64>::new(),
            i1: Prophecy::<u64>::new(),
            i2: Prophecy::<u64>::new(),
            i3: Prophecy::<u64>::new(),
            i4: Prophecy::<u64>::new(),
            i5: Prophecy::<u64>::new(),
            i6: Prophecy::<u64>::new(),
            i7: Prophecy::<u64>::new(),
        }
    }

    pub open spec fn keep(self) -> Set<WriteID>
    {
        set![self.i0@ as nat,
             self.i1@ as nat,
             self.i2@ as nat,
             self.i3@ as nat,
             self.i4@ as nat,
             self.i5@ as nat,
             self.i6@ as nat,
             self.i7@ as nat]
    }
}

pub struct RegionProph {
    pub chunks: Vec<ChunkProph>,
}

impl RegionProph {
    pub fn new(nchunks: u64) -> (res: RegionProph)
        ensures
            res.chunks.len() == nchunks,
    {
        let mut vec: Vec<ChunkProph> = Vec::with_capacity(nchunks as usize);
        while vec.len() != nchunks as usize
        {
            vec.push(ChunkProph::new());
        };
        RegionProph{
            chunks: vec,
        }
    }

    pub open spec fn keep(self) -> Seq<Set<WriteID>>
    {
        Seq::new(self.chunks.len() as nat, |i: int| self.chunks[i].keep())
    }
}

pub struct PMRegionProph<PMRegion>
    where PMRegion: PersistentMemoryRegionRaw
{
    pm: PMRegion,
    flush: Prophecy::<bool>,
    proph: RegionProph,
}

impl<PMRegion> PersistentMemoryRegion for PMRegionProph<PMRegion>
    where PMRegion: PersistentMemoryRegionRaw
{
    closed spec fn view(&self) -> PersistentMemoryRegionView {
        PersistentMemoryRegionView{
            read_state: self.pm@.flush().committed(),
            durable_state: if self.flush@ { self.pm@.flush().committed() } else { self.pm@.keep_writes(self.proph.keep()).committed() },
        }
    }

    closed spec fn inv(&self) -> bool {
        self.pm.inv()
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
        self.pm.write(addr, bytes);
        assert(self@.read_state == update_bytes(old(self)@.read_state, addr as int, bytes@));
    }

    fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S)
        where S: PmCopy + Sized
    {
        self.pm.serialize_and_write(addr, to_write);
        assert(self@.read_state == update_bytes(old(self)@.read_state, addr as int, to_write.spec_to_bytes()));
    }

    fn flush(&mut self)
    {
        let mut flushproph = Prophecy::<bool>::new();
        std::mem::swap(&mut self.flush, &mut flushproph);
        flushproph.resolve(&true);
        self.pm.flush();
        assert(self@.read_state == old(self)@.read_state);
        assert(self@.durable_state == old(self)@.durable_state);
    }
}

impl<PMRegion> PMRegionProph<PMRegion>
    where PMRegion: PersistentMemoryRegionRaw
{
    pub fn new(pm: PMRegion) -> (result: PMRegionProph<PMRegion>)
        requires
            pm.inv(),
            pm@.no_outstanding_writes(),
        ensures
            result.inv(),
            result@.read_state == pm@.flush().committed(),
            result@.durable_state == pm@.committed(),
    {
        let nchunks = pm.get_region_size() / 8 + 1;
        let proph = RegionProph::new(nchunks);
        assert(pm@.committed() == pm@.flush().committed());
        assert(pm@.committed() == pm@.keep_writes(proph.keep()).committed());
        PMRegionProph::<PMRegion>{
            pm: pm,
            flush: Prophecy::<bool>::new(),
            proph: proph,
        }
    }

    pub fn crash(self)
    {
        let mut mself = self;
        let mut flushproph = Prophecy::<bool>::new();
        std::mem::swap(&mut mself.flush, &mut flushproph);
        flushproph.resolve(&false);

        // XXX resolving prophecy would be a way to enforce that the prophecy
        // could be resolved with any value at crash-time.

        let ghost crash_state = self.pm@.keep_writes(self.proph.keep()).committed();
        assert(self@.durable_state == crash_state);
    }
}
}
