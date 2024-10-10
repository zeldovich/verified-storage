//! This file contains a logical-atomicity-style specification for how
//! a persistent memory region behaves, called PersistentMemoryRegionV2.

use crate::pmem::pmcopy_t::*;
use crate::pmem::frac_v::*;
use crate::pmem::pmemspec_t::*;
use vstd::prelude::*;
use vstd::invariant::*;

verus! {

    pub const PMEM_INV_NS: u64 = 12345;

    pub trait PMRegionGetSizeOperation where Self: Sized {
        type Result;

        spec fn id(&self) -> int;
        spec fn pre(&self) -> bool;
        spec fn post(&self, r: Self::Result, v: u64) -> bool;
        proof fn apply(tracked self, tracked r: &FractionalResource<PersistentMemoryRegionView, 3>,
                       v: u64, tracked credit: OpenInvariantCredit) -> (tracked result: Self::Result)
            requires
                self.pre(),
                r.valid(self.id(), 1),
                v == r.val().len(),
            ensures
                self.post(result, v),
            opens_invariants
                [ PMEM_INV_NS ];
    }

    pub trait PMRegionReadOperation where Self: Sized {
        type Result;

        spec fn addr(&self) -> u64;
        spec fn num_bytes(&self) -> u64;
        spec fn constants(&self) -> PersistentMemoryConstants;
        spec fn id(&self) -> int;
        spec fn pre(&self) -> bool;
        spec fn post(&self, r: Self::Result, v: Result<Vec<u8>, PmemError>) -> bool;
        proof fn validate(tracked &self, tracked r: &FractionalResource<PersistentMemoryRegionView, 3>,
                          tracked credit: OpenInvariantCredit)
            requires
                self.pre(),
                r.valid(self.id(), 1),
            ensures
                self.addr() + self.num_bytes() <= r.val().len(),
            opens_invariants
                [ PMEM_INV_NS ];
        proof fn apply(tracked self, tracked r: &FractionalResource<PersistentMemoryRegionView, 3>,
                       v: Result<Vec<u8>, PmemError>, tracked credit: OpenInvariantCredit) -> (tracked result: Self::Result)
            requires
                self.pre(),
                r.valid(self.id(), 1),
                match v {
                    Ok(bytes) => {
                        let true_bytes = r.val().read_state.subrange(self.addr() as int, self.addr() + self.num_bytes());
                        let addrs = Seq::<int>::new(self.num_bytes() as nat, |i: int| i + self.addr());
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
                },
            ensures
                self.post(result, v),
            opens_invariants
                [ PMEM_INV_NS ];
    }

    pub trait PMRegionReadAlignedOperation<S> where S: PmCopy, Self: Sized {
        type Result;

        spec fn addr(&self) -> u64;
        spec fn constants(&self) -> PersistentMemoryConstants;
        spec fn id(&self) -> int;
        spec fn pre(&self) -> bool;
        spec fn post(&self, r: Self::Result, v: Result<MaybeCorruptedBytes<S>, PmemError>) -> bool;
        proof fn validate(tracked &self, tracked r: &FractionalResource<PersistentMemoryRegionView, 3>,
                          tracked credit: OpenInvariantCredit)
            requires
                self.pre(),
                r.valid(self.id(), 1),
            ensures
                self.addr() + S::spec_size_of() <= r.val().len(),
                // We must have previously written a serialized S to this addr
                S::bytes_parseable(r.val().read_state.subrange(self.addr() as int, self.addr() + S::spec_size_of())),
            opens_invariants
                [ PMEM_INV_NS ];
        proof fn apply(tracked self, tracked r: &FractionalResource<PersistentMemoryRegionView, 3>,
                       v: Result<MaybeCorruptedBytes<S>, PmemError>,
                       tracked credit: OpenInvariantCredit) -> (tracked result: Self::Result)
            requires
                self.pre(),
                r.valid(self.id(), 1),
                match v {
                    Ok(bytes) => {
                        let true_bytes = r.val().read_state.subrange(self.addr() as int, self.addr() + S::spec_size_of());
                        let addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| i + self.addr());
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
                },
            ensures
                self.post(result, v),
            opens_invariants
                [ PMEM_INV_NS ];
    }

    pub trait PMRegionWriteOperation where Self: Sized {
        type Result;

        spec fn addr(&self) -> u64;
        spec fn bytes(&self) -> Seq<u8>;
        spec fn id(&self) -> int;
        spec fn pre(&self) -> bool;
        spec fn post(&self, r: Self::Result) -> bool;
        proof fn validate(tracked &self, tracked r: &FractionalResource<PersistentMemoryRegionView, 3>,
                          tracked credit: OpenInvariantCredit)
            requires
                self.pre(),
                r.valid(self.id(), 1),
            ensures
                self.addr() + self.bytes().len() <= r.val().len(),
            opens_invariants
                [ PMEM_INV_NS ];
        proof fn apply(tracked self, tracked r: &mut FractionalResource<PersistentMemoryRegionView, 3>,
                       newv: PersistentMemoryRegionView,
                       tracked credit: OpenInvariantCredit) -> (tracked result: Self::Result)
            requires
                self.pre(),
                old(r).valid(self.id(), 1),
                newv.can_result_from_write(old(r).val(), self.addr() as int, self.bytes()),
            ensures
                r.valid(self.id(), 1),
                r.val() == newv,
                self.post(result),
            opens_invariants
                [ PMEM_INV_NS ];
    }

    pub trait PMRegionFlushOperation where Self: Sized {
        type Result;

        spec fn id(&self) -> int;
        spec fn pre(&self) -> bool;
        spec fn post(&self, r: Self::Result) -> bool;
        proof fn apply(tracked self, tracked r: &FractionalResource<PersistentMemoryRegionView, 3>,
                       tracked credit: OpenInvariantCredit) -> (tracked result: Self::Result)
            requires
                self.pre(),
                r.valid(self.id(), 1),
                r.val().flush_predicted(),
            ensures
                self.post(result),
            opens_invariants
                [ PMEM_INV_NS ];
    }

    pub trait PersistentMemoryRegionV2
    {
        spec fn inv(&self) -> bool;

        spec fn id(&self) -> int;

        spec fn constants(&self) -> PersistentMemoryConstants;

        fn get_region_size<Op>(&self, Tracked(op): Tracked<Op>) -> (result: (u64, Tracked<Op::Result>))
            where
                Op: PMRegionGetSizeOperation,
            requires
                self.inv(),
                op.pre(),
                op.id() == self.id(),
            ensures
                op.post(result.1@, result.0),
        ;

        fn read_unaligned<Op>(&self, addr: u64, num_bytes: u64, Tracked(op): Tracked<Op>) -> (result: (Result<Vec<u8>, PmemError>, Tracked<Op::Result>))
            where
                Op: PMRegionReadOperation,
            requires
                self.inv(),
                op.pre(),
                op.addr() == addr,
                op.num_bytes() == num_bytes,
                op.constants() == self.constants(),
                op.id() == self.id(),
            ensures
                op.post(result.1@, result.0),
        ;

        fn write<Op>(&mut self, addr: u64, bytes: &[u8], Tracked(op): Tracked<Op>) -> (result: Tracked<Op::Result>)
            where
                Op: PMRegionWriteOperation,
            requires
                old(self).inv(),
                op.pre(),
                op.addr() == addr,
                op.bytes() == bytes@,
                op.id() == old(self).id(),
            ensures
                self.inv(),
                self.constants() == old(self).constants(),
                self.id() == old(self).id(),
                op.post(result@),
        ;

        fn flush<Op>(&mut self, Tracked(op): Tracked<Op>) -> (result: Tracked<Op::Result>)
            where
                Op: PMRegionFlushOperation,
            requires
                old(self).inv(),
                op.pre(),
                op.id() == old(self).id(),
            ensures
                self.inv(),
                self.constants() == old(self).constants(),
                self.id() == old(self).id(),
                op.post(result@),
        ;

        fn read_aligned<S, Op>(&self, addr: u64, Tracked(op): Tracked<Op>) -> (result: (Result<MaybeCorruptedBytes<S>, PmemError>, Tracked<Op::Result>))
            where
                S: PmCopy,
                Op: PMRegionReadAlignedOperation<S>,
            requires
                self.inv(),
                op.pre(),
                op.addr() == addr,
                op.constants() == self.constants(),
                op.id() == self.id(),
            ensures
                op.post(result.1@, result.0),
        ;

        fn serialize_and_write<S, Op>(&mut self, addr: u64, to_write: &S, Tracked(op): Tracked<Op>) -> (result: Tracked<Op::Result>)
            where
                S: PmCopy,
                Op: PMRegionWriteOperation,
            requires
                old(self).inv(),
                op.pre(),
                op.addr() == addr,
                op.bytes() == to_write.spec_to_bytes(),
                op.id() == old(self).id(),
            ensures
                self.inv(),
                self.constants() == old(self).constants(),
                self.id() == old(self).id(),
                op.post(result@),
        ;
    }
}
