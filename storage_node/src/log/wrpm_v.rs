use std::fmt::Write;
use std::sync::Arc;

use crate::log::logimpl_v::UntrustedLogImpl;
use crate::log::logspec_t::AbstractLogState;
use crate::log::logimpl_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmem_prophspec_v::*;
use crate::pmem::wrpm_v::*;
use crate::pmem::pmemspec2_t::*;
use crate::pmem::pmemadapt_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::frac_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::invariant::*;
use vstd::modes::*;

verus! {

    pub struct PermissionV2<'a> {
        pub ghost log_id: u128,
        pub tracked frac: &'a FractionalResource<AbstractLogCrashState, 2>,
    }

    impl CheckPermission<LogInvParam, Seq<u8>> for PermissionV2<'_> {
        open spec fn check_permission(&self, state: Seq<u8>) -> bool {
            recover_into(state, self.log_id, self.frac.val())
        }

        open spec fn valid(&self, id: LogInvParam) -> bool {
            self.frac.valid(id.crash_frac_id, 1) &&
            self.log_id == id.log_id
        }
    }

    impl PermissionV2<'_> {

        // This constructor conveys permission to do any update as long as
        // a subsequent crash and recovery can only lead to one of two given
        // abstract states, `frac.val().state1` and `frac.val().state2`.
        pub proof fn new<'a>(
            tracked frac: &'a FractionalResource<AbstractLogCrashState, 2>,
            id: LogInvParam,
        ) -> (tracked perm: PermissionV2<'a>)
            requires
                frac.valid(id.crash_frac_id, 1),
            ensures
                perm.valid(id),
                forall |s| #[trigger] perm.check_permission(s) <==> {
                    ||| UntrustedLogImpl::recover(s, id.log_id) == Some(frac.val().state1)
                    ||| UntrustedLogImpl::recover(s, id.log_id) == Some(frac.val().state2)
                }
        {
            Self {
                log_id: id.log_id,
                frac: frac,
            }
        }
    }

    pub struct WriteRestrictedPersistentMemoryRegionV2<PMRegion>
        where
            PMRegion: PersistentMemoryRegionV2
    {
        pub pm_region: PMRegion,
        pub frac: Tracked<FractionalResource<PersistentMemoryRegionView, 3>>,
        pub inv: Tracked<Arc<AtomicInvariant<LogInvParam, LogInvState, LogInvPred>>>,
    }

    pub struct WRPMGetRegionSize<'a> {
        frac: &'a FractionalResource<PersistentMemoryRegionView, 3>,
    }

    impl PMRegionGetSizeOperation for WRPMGetRegionSize<'_> {
        type Result = ();

        closed spec fn namespace(&self) -> int { 0 }
        closed spec fn id(&self) -> int { self.frac.id() }
        closed spec fn pre(&self) -> bool {
            self.frac.inv()
        }
        closed spec fn post(&self, r: (), v: u64) -> bool {
            v == self.frac.val().len()
        }

        proof fn apply(tracked self, tracked r: &FractionalResource<PersistentMemoryRegionView, 3>,
                       v: u64, tracked credit: OpenInvariantCredit) -> (tracked result: ())
        {
            r.agree(self.frac);
        }
    }

    pub struct WRPMFlush<'a> {
        frac: &'a FractionalResource<PersistentMemoryRegionView, 3>,
    }

    impl PMRegionFlushOperation for WRPMFlush<'_> {
        type Result = ();

        closed spec fn namespace(&self) -> int { 0 }
        closed spec fn id(&self) -> int { self.frac.id() }
        closed spec fn pre(&self) -> bool {
            self.frac.inv()
        }
        closed spec fn post(&self, r: ()) -> bool {
            self.frac.val().flush_predicted()
        }

        proof fn apply(tracked self, tracked r: &FractionalResource<PersistentMemoryRegionView, 3>,
                       tracked credit: OpenInvariantCredit) -> (tracked result: ())
        {
            r.agree(self.frac);
        }
    }

    pub struct WRPMReadUnaligned<'a> {
        addr: u64,
        num_bytes: u64,
        ghost constants: PersistentMemoryConstants,
        frac: &'a FractionalResource<PersistentMemoryRegionView, 3>,
    }

    impl PMRegionReadOperation for WRPMReadUnaligned<'_> {
        type Result = ();

        closed spec fn namespace(&self) -> int { 0 }
        closed spec fn addr(&self) -> u64 { self.addr }
        closed spec fn num_bytes(&self) -> u64 { self.num_bytes }
        closed spec fn constants(&self) -> PersistentMemoryConstants { self.constants }
        closed spec fn id(&self) -> int { self.frac.id() }
        closed spec fn pre(&self) -> bool {
            self.frac.inv() &&
            self.addr + self.num_bytes <= self.frac.val().len()
        }
        closed spec fn post(&self, r: (), v: Result<Vec<u8>, PmemError>) -> bool {
            match v {
                Ok(bytes) => {
                    let true_bytes = self.frac.val().read_state.subrange(self.addr as int, self.addr + self.num_bytes);
                    let addrs = Seq::<int>::new(self.num_bytes as nat, |i: int| i + self.addr);
                    &&& // If the persistent memory regions are impervious
                        // to corruption, read returns the last bytes
                        // written. Otherwise, it returns a
                        // possibly-corrupted version of those bytes.
                        if self.constants.impervious_to_corruption {
                                bytes@ == true_bytes
                        }
                        else {
                            maybe_corrupted(bytes@, true_bytes, addrs)
                        }
                    }
                _ => false
            }
        }

        proof fn validate(tracked &self, tracked r: &FractionalResource<PersistentMemoryRegionView, 3>,
                          tracked credit: OpenInvariantCredit)
        {
            r.agree(self.frac)
        }

        proof fn apply(tracked self, tracked r: &FractionalResource<PersistentMemoryRegionView, 3>,
                       v: Result<Vec<u8>, PmemError>, tracked credit: OpenInvariantCredit) -> (tracked result: ())
        {
            r.agree(self.frac);
        }
    }

    pub struct WRPMReadAligned<'a> {
        addr: u64,
        ghost constants: PersistentMemoryConstants,
        frac: &'a FractionalResource<PersistentMemoryRegionView, 3>,
    }

    impl<S> PMRegionReadAlignedOperation<S> for WRPMReadAligned<'_>
        where S: PmCopy
    {
        type Result = ();

        closed spec fn namespace(&self) -> int { 0 }
        closed spec fn addr(&self) -> u64 { self.addr }
        closed spec fn constants(&self) -> PersistentMemoryConstants { self.constants }
        closed spec fn id(&self) -> int { self.frac.id() }
        closed spec fn pre(&self) -> bool {
            self.frac.inv() &&
            self.addr + S::spec_size_of() <= self.frac.val().len() &&
            S::bytes_parseable(self.frac.val().read_state.subrange(self.addr as int, self.addr + S::spec_size_of()))
        }
        closed spec fn post(&self, r: (), v: Result<MaybeCorruptedBytes<S>, PmemError>) -> bool {
            match v {
                Ok(bytes) => {
                    let true_bytes = self.frac.val().read_state.subrange(self.addr as int, self.addr + S::spec_size_of());
                    let addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| i + self.addr);
                    &&& // If the persistent memory regions are impervious
                        // to corruption, read returns the last bytes
                        // written. Otherwise, it returns a
                        // possibly-corrupted version of those bytes.
                        if self.constants.impervious_to_corruption {
                                bytes@ == true_bytes
                        }
                        else {
                            maybe_corrupted(bytes@, true_bytes, addrs)
                        }
                    }
                _ => false
            }
        }

        proof fn validate(tracked &self, tracked r: &FractionalResource<PersistentMemoryRegionView, 3>,
                          tracked credit: OpenInvariantCredit)
        {
            r.agree(self.frac)
        }

        proof fn apply(tracked self, tracked r: &FractionalResource<PersistentMemoryRegionView, 3>,
                       v: Result<MaybeCorruptedBytes<S>, PmemError>, tracked credit: OpenInvariantCredit) -> (tracked result: ())
        {
            r.agree(self.frac);
        }
    }

    pub struct WRPMWrite<'a> {
        ghost addr: u64,
        ghost bytes: Seq<u8>,
        tracked frac: FractionalResource<PersistentMemoryRegionView, 3>,
        tracked loginv: &'a AtomicInvariant<LogInvParam, LogInvState, LogInvPred>,
        tracked perm: &'a PermissionV2<'a>,
    }

    impl PMRegionWriteOperation for WRPMWrite<'_> {
        type Result = FractionalResource<PersistentMemoryRegionView, 3>;

        closed spec fn namespace(&self) -> int { self.loginv.namespace() }
        closed spec fn addr(&self) -> u64 { self.addr }
        closed spec fn bytes(&self) -> Seq<u8> { self.bytes }
        closed spec fn id(&self) -> int { self.frac.id() }
        closed spec fn pre(&self) -> bool {
            self.addr() + self.bytes().len() <= self.frac.val().len() &&
            self.frac.valid(self.loginv.constant().pm_frac_id, 1) &&
            self.perm.valid(self.loginv.constant()) &&
            forall |s| can_result_from_partial_write(s, self.frac.val().durable_state, self.addr() as int, self.bytes())
                  ==> #[trigger] self.perm.check_permission(s)
        }
        closed spec fn post(&self, r: Self::Result) -> bool {
            r.valid(self.frac.id(), 1) &&
            r.val().can_result_from_write(self.frac.val(), self.addr() as int, self.bytes())
        }

        proof fn validate(tracked &self, tracked r: &FractionalResource<PersistentMemoryRegionView, 3>,
                          tracked credit: OpenInvariantCredit)
        {
            r.agree(&self.frac)
        }

        proof fn apply(tracked self, tracked r: &mut FractionalResource<PersistentMemoryRegionView, 3>,
                       newv: PersistentMemoryRegionView,
                       tracked credit: OpenInvariantCredit) -> (tracked result: Self::Result)
        {
            r.combine_mut(self.frac);
            open_atomic_invariant!(credit => &self.loginv => inner => {
                r.combine_mut(inner.pm);
                r.update_mut(newv);
                inner.pm = r.split_mut(1);

                inner.crash.agree(&self.perm.frac);
                assert forall |s| self.perm.check_permission(s) implies
                    #[trigger] recover_into(s, self.loginv.constant().log_id, inner.crash.val()) by {};
            });
            r.split_mut(1)
        }
    }

    impl<PMRegion> WriteRestrictedPersistentMemoryRegionTrait<LogInvParam, PermissionV2<'_>> for WriteRestrictedPersistentMemoryRegionV2<PMRegion>
        where
            PMRegion: PersistentMemoryRegionV2
    {
        open spec fn view(&self) -> PersistentMemoryRegionView
        {
            self.frac@.val()
        }

        open spec fn inv(&self) -> bool
        {
            self.pm_region.inv() &&
            self.frac@.valid(self.pm_region.id(), 1) &&
            self.inv@.constant().pm_frac_id == self.pm_region.id()
        }

        open spec fn constants(&self) -> PersistentMemoryConstants
        {
            self.pm_region.constants()
        }

        open spec fn id(&self) -> LogInvParam
        {
            self.inv@.constant()
        }

        exec fn get_region_size(&self) -> (result: u64)
        {
            let tracked op = WRPMGetRegionSize{ frac: self.frac.borrow() };
            let (result, Tracked(opres)) = self.pm_region.get_region_size::<WRPMGetRegionSize>(Tracked(op));
            result
        }

        exec fn write(&mut self, addr: u64, bytes: &[u8], Tracked(perm): Tracked<&PermissionV2>) {
            let tracked mut frac = FractionalResource::<PersistentMemoryRegionView, 3>::default();
            let tracked _ = tracked_swap(self.frac.borrow_mut(), &mut frac);
            let tracked op = WRPMWrite{
                addr: addr,
                bytes: bytes@,
                frac: frac,
                loginv: self.inv.borrow(),
                perm: perm,
            };
            let Tracked(opres) = self.pm_region.write::<WRPMWrite>(addr, bytes, Tracked(op));
            self.frac = Tracked(opres);
        }

        exec fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S, Tracked(perm): Tracked<&PermissionV2>)
            where S: PmCopy
        {
            broadcast use axiom_bytes_len;

            let tracked mut frac = FractionalResource::<PersistentMemoryRegionView, 3>::default();
            let tracked _ = tracked_swap(self.frac.borrow_mut(), &mut frac);
            let tracked op = WRPMWrite{
                addr: addr,
                bytes: to_write.spec_to_bytes(),
                frac: frac,
                loginv: self.inv.borrow(),
                perm: perm,
            };
            let Tracked(opres) = self.pm_region.serialize_and_write::<S, WRPMWrite>(addr, to_write, Tracked(op));
            self.frac = Tracked(opres);
        }

        exec fn flush(&mut self) {
            let tracked op = WRPMFlush{ frac: self.frac.borrow() };
            let Tracked(opres) = self.pm_region.flush::<WRPMFlush>(Tracked(op));
        }

        exec fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
            where S: PmCopy + Sized
        {
            let tracked op = WRPMReadAligned{ addr: addr, constants: self.pm_region.constants(), frac: self.frac.borrow() };
            let (result, Tracked(opres)) = self.pm_region.read_aligned::<S, WRPMReadAligned>(addr, Tracked(op));
            result
        }

        exec fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>)
        {
            let tracked op = WRPMReadUnaligned{ addr: addr, num_bytes: num_bytes, constants: self.pm_region.constants(), frac: self.frac.borrow() };
            let (result, Tracked(opres)) = self.pm_region.read_unaligned::<WRPMReadUnaligned>(addr, num_bytes, Tracked(op));
            result
        }
    }

    impl<PMRegion> WriteRestrictedPersistentMemoryRegionV2<PMRegion>
        where
            PMRegion: PersistentMemoryRegionV2
    {
        pub exec fn new(pm_region: PMRegion,
                        Tracked(frac): Tracked<FractionalResource<PersistentMemoryRegionView, 3>>,
                        Tracked(inv): Tracked<Arc<AtomicInvariant<LogInvParam, LogInvState, LogInvPred>>>) -> (wrpm_region: Self)
            requires
                pm_region.inv(),
                frac.valid(pm_region.id(), 1),
                inv.constant().pm_frac_id == pm_region.id(),
            ensures
                wrpm_region.inv(),
                wrpm_region@ == frac.val(),
                wrpm_region.constants() == pm_region.constants(),
                wrpm_region.id() == inv.constant(),
        {
            Self {
                pm_region: pm_region,
                frac: Tracked(frac),
                inv: Tracked(inv),
            }
        }
    }
}
