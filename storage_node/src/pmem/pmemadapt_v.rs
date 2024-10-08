//! This file implements an adapter from a sequential PersistentMemoryRegion
//! specification to a logical-atomicity-style PersistentMemoryRegionV2 spec.
//!
//! This adapter helps ensure that the logically-atomic spec doesn't say
//! anything unsound in terms of PCM resources.  However, the adapter is
//! part of the trusted code for purposes of crash safety reasoning, because
//! it has to be trusted to correctly reflect the PersistentMemoryRegionView
//! in the fractional resource.

use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmem_prophspec_v::*;
use crate::pmem::pmemspec2_t::*;
use crate::pmem::frac_v::*;
use vstd::prelude::*;
use vstd::invariant::*;

verus! {

    pub struct PMRegionV2<PMRegion>
        where
            PMRegion: PersistentMemoryRegion
    {
        // The underlying persistent memory region.
        pm: PMRegion,

        // Fractional ownership of the persistent memory region state.
        frac: Tracked<FractionalResource<PersistentMemoryRegionView, 3>>,
    }

    impl<PMRegion> PersistentMemoryRegionV2 for PMRegionV2<PMRegion>
        where
            PMRegion: PersistentMemoryRegion
    {
        closed spec fn inv(&self) -> bool {
            &&& self.pm.inv()
            &&& self.frac@.inv()
            &&& self.frac@.val() == self.pm@
            &&& self.frac@.frac() == 1
        }

        closed spec fn id(&self) -> int {
            self.frac@.id()
        }

        closed spec fn constants(&self) -> PersistentMemoryConstants {
            self.pm.constants()
        }

        exec fn get_region_size<Op>(&self, Tracked(op): Tracked<Op>) -> (result: (u64, Tracked<Op::Result>))
            where
                Op: PMRegionGetSizeOperation
        {
            let r = self.pm.get_region_size();
            let Tracked(credit) = create_open_invariant_credit();
            let tracked tr = op.apply(self.frac.borrow(), r, credit);
            (r, Tracked(tr))
        }

        exec fn read_unaligned<Op>(&self, addr: u64, num_bytes: u64, Tracked(op): Tracked<Op>) -> (result: (Result<Vec<u8>, PmemError>, Tracked<Op::Result>))
            where
                Op: PMRegionReadOperation
        {
            let Tracked(credit) = create_open_invariant_credit();
            let tracked tr = op.validate(self.frac.borrow(), credit);

            let r = self.pm.read_unaligned(addr, num_bytes);
            let Tracked(credit) = create_open_invariant_credit();
            let tracked tr = op.apply(self.frac.borrow(), r, credit);
            (r, Tracked(tr))
        }

        exec fn write<Op>(&mut self, addr: u64, bytes: &[u8], Tracked(op): Tracked<Op>) -> (result: Tracked<Op::Result>)
            where
                Op: PMRegionWriteOperation
        {
            let Tracked(credit) = create_open_invariant_credit();
            let tracked tr = op.validate(self.frac.borrow(), credit);

            self.pm.write(addr, bytes);
            let Tracked(credit) = create_open_invariant_credit();
            let tracked tr = op.apply(self.frac.borrow_mut(), self.pm@, credit);
            Tracked(tr)
        }

        exec fn flush<Op>(&mut self, Tracked(op): Tracked<Op>) -> (result: Tracked<Op::Result>)
            where
                Op: PMRegionFlushOperation
        {
            self.pm.flush();
            let Tracked(credit) = create_open_invariant_credit();
            let tracked tr = op.apply(self.frac.borrow_mut(), credit);
            Tracked(tr)
        }

        exec fn read_aligned<S, Op>(&self, addr: u64, Tracked(op): Tracked<Op>) -> (result: (Result<MaybeCorruptedBytes<S>, PmemError>, Tracked<Op::Result>))
            where
                S: PmCopy,
                Op: PMRegionReadAlignedOperation<S>,
        {
            let Tracked(credit) = create_open_invariant_credit();
            let tracked tr = op.validate(self.frac.borrow(), credit);

            let r = self.pm.read_aligned(addr);
            let Tracked(credit) = create_open_invariant_credit();
            let tracked tr = op.apply(self.frac.borrow(), r, credit);
            (r, Tracked(tr))
        }

        exec fn serialize_and_write<S, Op>(&mut self, addr: u64, to_write: &S, Tracked(op): Tracked<Op>) -> (result: Tracked<Op::Result>)
            where
                S: PmCopy,
                Op: PMRegionWriteOperation,
        {
            broadcast use axiom_bytes_len;

            let Tracked(credit) = create_open_invariant_credit();
            let tracked tr = op.validate(self.frac.borrow(), credit);

            self.pm.serialize_and_write(addr, to_write);
            let Tracked(credit) = create_open_invariant_credit();
            let tracked tr = op.apply(self.frac.borrow_mut(), self.pm@, credit);
            Tracked(tr)
        }
    }

    impl<PMRegion> PMRegionV2<PMRegion>
        where
            PMRegion: PersistentMemoryRegion
    {
        pub exec fn new(pm: PMRegion) -> (result: (Self, Tracked<FractionalResource<PersistentMemoryRegionView, 3>>))
            requires
                pm.inv(),
            ensures
                result.0.inv(),
                result.1@.valid(result.0.id(), 2),
                result.1@.val() == pm@,
                result.0.constants() == pm.constants(),
        {
            let tracked r = FractionalResource::<PersistentMemoryRegionView, 3>::alloc(pm@);
            let pmv2 = PMRegionV2{
                pm: pm,
                frac: Tracked(r.split_mut(1)),
            };
            (pmv2, Tracked(r))
        }
    }
}
