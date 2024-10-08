//! This file contains the trusted implementation of a `LogImpl`.
//! Although the verifier is run on this file, it needs to be
//! carefully read and audited to be confident of the correctness of
//! this log implementation.
//!
//! Fortunately, it delegates most of its work to an untrusted struct
//! `UntrustedLogImpl`, which doesn't need to be read or audited. It
//! forces the `UntrustedLogImpl` to satisfy certain postconditions,
//! and also places restrictions on what `UntrustedLogImpl` can do to
//! persistent memory. These restrictions ensure that even if the
//! system or process crashes in the middle of an operation, the
//! system will still recover to a consistent state.
//!
//! It requires `UntrustedLogImpl` to implement routines that do the
//! various log operations like read and commit.
//!
//! It also requires `UntrustedLogImpl` to provide a function
//! `UntrustedLogImpl::recover`, which specifies what its `start`
//! routine will do to recover after a crash. It requires its `start`
//! routine to satisfy that specification. It also uses it to limit
//! how `UntrustedLogImpl` writes to memory: It can only perform
//! updates that, if incompletely performed before a crash, still
//! leave the system in a valid state. The `recover` function takes a
//! second parameter, the `log_id` which is passed to the start
//! routine.
//!
//! It also requires `UntrustedLogImpl` to provide a function `view`
//! that converts the current state into an abstract log. It requires
//! that performing a certain operation on the `UntrustedLogImpl`
//! causes a corresponding update to its abstract view. For instance,
//! calling the `u.commit()` method should cause the resulting
//! `u.view()` to become `old(u).view().commit()`.
//!
//! It also permits `UntrustedLogImpl` to provide a function `inv`
//! that encodes any invariants `UntrustedLogImpl` wants maintained
//! across invocations of its functions. This implementation will then
//! guarantee that `inv` holds on any call to an `UntrustedLogImpl`
//! method, and demand that the method preserve that invariant.

use std::fmt::Write;
use std::sync::Arc;

use crate::log::logimpl_v::UntrustedLogImpl;
use crate::log::logspec_t::AbstractLogState;
use crate::pmem::pmemspec_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemspec2_t::*;
use crate::pmem::pmemadapt_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::frac_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::invariant::*;
use vstd::modes::*;

use deps_hack::rand::Rng;

verus! {

    // This is the specification that `LogImpl` provides for data
    // bytes it reads. It says that those bytes are correct unless
    // there was corruption on the persistent memory between the last
    // write and this read.
    pub open spec fn read_correct_modulo_corruption(bytes: Seq<u8>, true_bytes: Seq<u8>,
                                                    impervious_to_corruption: bool) -> bool
    {
        if impervious_to_corruption {
            // If the region is impervious to corruption, the bytes read
            // must match the true bytes, i.e., the bytes last written.

            bytes == true_bytes
        }
        else {
            // Otherwise, there must exist a sequence of distinct
            // addresses `addrs` such that the nth byte of `bytes` is
            // a possibly corrupted version of the nth byte of
            // `true_bytes` read from the nth address in `addrs`.  We
            // don't require the sequence of addresses to be
            // contiguous because the data might not be contiguous on
            // disk (e.g., if it wrapped around the log area).

            exists |addrs: Seq<int>| {
                &&& all_elements_unique(addrs)
                &&& #[trigger] maybe_corrupted(bytes, true_bytes, addrs)
            }
        }
    }

    // This specification function indicates whether the given view of
    // memory will crash in a way that, after recovery, leads to a
    // certain abstract state.
    pub open spec fn crashes_as_abstract_state(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        state: AbstractLogState,
    ) -> bool
    {
        UntrustedLogImpl::recover(pm_region_view.durable_state, log_id) == Some(state)
    }

    pub struct AbstractLogCrashState {
        state1: AbstractLogState,
        state2: AbstractLogState,
    }

    closed spec fn recover_into(s: Seq<u8>, log_id: u128, crash: AbstractLogCrashState) -> bool {
        UntrustedLogImpl::recover(s, log_id) == Some(crash.state1) ||
        UntrustedLogImpl::recover(s, log_id) == Some(crash.state2)
    }

    pub struct PermissionV2<'a> {
        ghost log_id: u128,
        tracked frac: &'a FractionalResource<AbstractLogCrashState, 2>,
    }

    impl CheckPermission<LogInvParam, Seq<u8>> for PermissionV2<'_> {
        closed spec fn check_permission(&self, state: Seq<u8>) -> bool {
            recover_into(state, self.log_id, self.frac.val())
        }

        closed spec fn valid(&self, id: LogInvParam) -> bool {
            self.frac.valid(id.crash_frac_id, 1) &&
            self.log_id == id.log_id
        }
    }

    impl PermissionV2<'_> {

        // This constructor conveys permission to do any update as long as
        // a subsequent crash and recovery can only lead to one of two given
        // abstract states, `frac.val().state1` and `frac.val().state2`.
        proof fn new<'a>(
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

    // This enumeration represents the various errors that can be
    // returned from log operations. They're self-explanatory.
    // TODO: make `PmemErr` and `LogErr` handling cleaner
    #[derive(Debug)]
    pub enum LogErr {
        InsufficientSpaceForSetup { required_space: u64 },
        StartFailedDueToLogIDMismatch { log_id_expected: u128, log_id_read: u128 },
        StartFailedDueToRegionSizeMismatch { region_size_expected: u64, region_size_read: u64 },
        StartFailedDueToProgramVersionNumberUnsupported { version_number: u64, max_supported: u64 },
        StartFailedDueToInvalidMemoryContents,
        CRCMismatch,
        InsufficientSpaceForAppend { available_space: u64 },
        CantReadBeforeHead { head: u128 },
        CantReadPastTail { tail: u128 },
        CantAdvanceHeadPositionBeforeHead { head: u128 },
        CantAdvanceHeadPositionBeyondTail { tail: u128 },
        PmemErr { err: PmemError } // janky workaround so that callers can handle PmemErrors as LogErrors
    }

    // This executable method can be called to compute a random GUID.
    // It uses the external `rand` crate.
    #[verifier::external_body]
    pub exec fn generate_fresh_log_id() -> (out: u128)
    {
        deps_hack::rand::thread_rng().gen::<u128>()
    }

    // Invariant and write-restricted storage adapter.

    pub struct LogInvState {
        // State of the persistent memory from PersistentMemoryRegionV2.
        pm: FractionalResource<PersistentMemoryRegionView, 3>,

        // State of the abstract log on crash.
        crash: FractionalResource<AbstractLogCrashState, 2>,
    }

    pub struct LogInvParam {
        pub pm_frac_id: int,
        pub crash_frac_id: int,
        pub log_id: u128,
    }

    pub struct LogInvPred {}

    impl InvariantPredicate<LogInvParam, LogInvState> for LogInvPred {
        closed spec fn inv(k: LogInvParam, v: LogInvState) -> bool {
            v.pm.valid(k.pm_frac_id, 1) &&
            v.crash.valid(k.crash_frac_id, 1) &&
            recover_into(v.pm.val().durable_state, k.log_id, v.crash.val())
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

    impl PMRegionGetSizeOperation<()> for WRPMGetRegionSize<'_> {
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

    impl PMRegionFlushOperation<()> for WRPMFlush<'_> {
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

    impl PMRegionReadOperation<()> for WRPMReadUnaligned<'_> {
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

    impl<S> PMRegionReadAlignedOperation<S, ()> for WRPMReadAligned<'_>
        where S: PmCopy
    {
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

    pub struct WriteResult {
        frac: FractionalResource<PersistentMemoryRegionView, 3>,
    }

    pub struct WRPMWrite<'a> {
        ghost addr: u64,
        ghost bytes: Seq<u8>,
        tracked frac: FractionalResource<PersistentMemoryRegionView, 3>,
        tracked loginv: &'a AtomicInvariant<LogInvParam, LogInvState, LogInvPred>,
        tracked perm: &'a PermissionV2<'a>,
    }

    impl PMRegionWriteOperation<WriteResult> for WRPMWrite<'_> {
        closed spec fn addr(&self) -> u64 { self.addr }
        closed spec fn bytes(&self) -> Seq<u8> { self.bytes }
        closed spec fn id(&self) -> int { self.frac.id() }
        closed spec fn pre(&self) -> bool {
            self.addr() + self.bytes().len() <= self.frac.val().len() &&
            self.loginv.namespace() == PMEM_INV_NS &&
            self.frac.valid(self.loginv.constant().pm_frac_id, 1) &&
            self.perm.valid(self.loginv.constant()) &&
            forall |s| can_result_from_partial_write(s, self.frac.val().durable_state, self.addr() as int, self.bytes())
                  ==> #[trigger] self.perm.check_permission(s)
        }
        closed spec fn post(&self, r: WriteResult) -> bool {
            r.frac.valid(self.frac.id(), 1) &&
            r.frac.val().can_result_from_write(self.frac.val(), self.addr() as int, self.bytes())
        }

        proof fn validate(tracked &self, tracked r: &FractionalResource<PersistentMemoryRegionView, 3>,
                          tracked credit: OpenInvariantCredit)
        {
            r.agree(&self.frac)
        }

        proof fn apply(tracked self, tracked r: &mut FractionalResource<PersistentMemoryRegionView, 3>,
                       newv: PersistentMemoryRegionView,
                       tracked credit: OpenInvariantCredit) -> (tracked result: WriteResult)
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
            WriteResult{
                frac: r.split_mut(1)
            }
        }
    }

    impl<PMRegion> WriteRestrictedPersistentMemoryRegionTrait<LogInvParam, PermissionV2<'_>> for WriteRestrictedPersistentMemoryRegionV2<PMRegion>
        where
            PMRegion: PersistentMemoryRegionV2
    {
        closed spec fn view(&self) -> PersistentMemoryRegionView
        {
            self.frac@.val()
        }

        closed spec fn inv(&self) -> bool
        {
            self.pm_region.inv() &&
            self.frac@.valid(self.pm_region.id(), 1) &&
            self.inv@.namespace() == PMEM_INV_NS &&
            self.inv@.constant().pm_frac_id == self.pm_region.id()
        }

        closed spec fn constants(&self) -> PersistentMemoryConstants
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
            let (result, Tracked(opres)) = self.pm_region.get_region_size::<_, WRPMGetRegionSize>(Tracked(op));
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
            let Tracked(opres) = self.pm_region.write::<_, WRPMWrite>(addr, bytes, Tracked(op));
            self.frac = Tracked(opres.frac);
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
            let Tracked(opres) = self.pm_region.serialize_and_write::<S, _, WRPMWrite>(addr, to_write, Tracked(op));
            self.frac = Tracked(opres.frac);
        }

        exec fn flush(&mut self) {
            let tracked op = WRPMFlush{ frac: self.frac.borrow() };
            let Tracked(opres) = self.pm_region.flush::<_, WRPMFlush>(Tracked(op));
        }

        exec fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
            where S: PmCopy + Sized
        {
            let tracked op = WRPMReadAligned{ addr: addr, constants: self.pm_region.constants(), frac: self.frac.borrow() };
            let (result, Tracked(opres)) = self.pm_region.read_aligned::<S, _, WRPMReadAligned>(addr, Tracked(op));
            result
        }

        exec fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>)
        {
            let tracked op = WRPMReadUnaligned{ addr: addr, num_bytes: num_bytes, constants: self.pm_region.constants(), frac: self.frac.borrow() };
            let (result, Tracked(opres)) = self.pm_region.read_unaligned::<_, WRPMReadUnaligned>(addr, num_bytes, Tracked(op));
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
                inv.namespace() == PMEM_INV_NS,
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

    /// A `LogImpl` wraps one `UntrustedLogImpl` and one persistent
    /// memory region to provide the executable interface that turns
    /// the persistent memory region into a log.
    ///
    /// The `untrusted_log_impl` field is the wrapped
    /// `UntrustedLogImpl`.
    ///
    /// The `log_id` field is the log ID. It's ghost.
    ///
    /// The `wrpm_region` field contains the write-restricted persistent
    /// memory. This memory will only allow updates allowed by a
    /// tracked `Permission`. So we can pass `wrpm_region` to an
    /// untrusted method, along with a restricting
    /// `Permission`, to limit what it's allowed to do.

    pub struct LogImpl<PMRegion: PersistentMemoryRegion> {
        untrusted_log_impl: UntrustedLogImpl,
        log_id: Ghost<u128>,
        wrpm_region: WriteRestrictedPersistentMemoryRegionV2<PMRegionV2<PMRegion>>,
        abs: Tracked<FractionalResource<AbstractLogCrashState, 2>>,
        inv: Tracked<Arc<AtomicInvariant<LogInvParam, LogInvState, LogInvPred>>>,
    }

    impl <PMRegion: PersistentMemoryRegion> LogImpl<PMRegion> {
        // The view of a `LogImpl` is whatever the
        // `UntrustedLogImpl` it wraps says it is.
        pub closed spec fn view(self) -> AbstractLogState
        {
            self.untrusted_log_impl@
        }

        // The constants of a `LogImpl` are whatever the
        // persistent memory it wraps says they are.
        pub closed spec fn constants(&self) -> PersistentMemoryConstants {
            self.wrpm_region.constants()
        }

        // This is the validity condition that is maintained between
        // calls to methods on `self`.
        //
        // That is, each of the trusted wrappers on untrusted methods
        // below (e.g., `commit`, `advance_head`) can count on `valid`
        // holding because it demands that each untrusted method
        // maintains it.
        //
        // One element of `valid` is that the untrusted `inv` function
        // holds.
        //
        // The other element of `valid` is that the persistent memory,
        // if it crashes and recovers, must represent the current
        // abstract state with pending tentative appends dropped.
        pub closed spec fn valid(self) -> bool {
            &&& self.untrusted_log_impl.inv(&self.wrpm_region, self.log_id@)
            &&& crashes_as_abstract_state(self.wrpm_region@, self.log_id@, self@.drop_pending_appends())
            &&& self.abs@.valid(self.inv@.constant().crash_frac_id, 1)
            &&& self.abs@.val() == AbstractLogCrashState{ state1: self@.drop_pending_appends(), state2: self@.drop_pending_appends() }
            &&& self.log_id@ == self.inv@.constant().log_id
            &&& self.wrpm_region.inv()
            &&& self.wrpm_region.id() == self.inv@.constant()
        }

        // The `setup` method sets up persistent memory regions
        // `pm_region` to store an initial empty log. It returns a
        // vector listing the capacity of the log as well as a
        // fresh log ID to uniquely identify it. See `README.md`
        // for more documentation.
        pub exec fn setup(pm_region: &mut PMRegion) -> (result: Result<(u64, u128), LogErr>)
            requires
                old(pm_region).inv(),
                old(pm_region)@.valid(),
            ensures
                pm_region.inv(),
                pm_region@.valid(),
                match result {
                    Ok((log_capacity, log_id)) => {
                        let state = AbstractLogState::initialize(log_capacity as int);
                        &&& log_capacity <= pm_region@.len()
                        &&& pm_region@.len() == old(pm_region)@.len()
                        &&& crashes_as_abstract_state(pm_region@, log_id, state)
                        &&& pm_region@.read_state == pm_region@.durable_state
                        &&& state == state.drop_pending_appends()
                    },
                    Err(LogErr::InsufficientSpaceForSetup { required_space }) => {
                        &&& pm_region@ == old(pm_region)@
                        &&& pm_region@.len() < required_space
                    },
                    _ => false
                }
        {
            let log_id = generate_fresh_log_id();
            let capacities = UntrustedLogImpl::setup(pm_region, log_id)?;
            Ok((capacities, log_id))
        }

        // The `start` method creates an `UntrustedLogImpl` out of a
        // persistent memory region. It's assumed that the region was
        // initialized with `setup` and then only log operations were
        // allowed to mutate them. See `README.md` for more
        // documentation and an example of use.
        pub exec fn start(pm_region: PMRegion, log_id: u128) -> (result: Result<LogImpl<PMRegion>, LogErr>)
            requires
                pm_region.inv(),
                pm_region@.valid(),
                pm_region@.read_state == pm_region@.durable_state,
                UntrustedLogImpl::recover(pm_region@.durable_state, log_id).is_Some(),
            ensures
                match result {
                    Ok(trusted_log_impl) => {
                        &&& trusted_log_impl.valid()
                        &&& trusted_log_impl.constants() == pm_region.constants()
                        &&& crashes_as_abstract_state(pm_region@, log_id, trusted_log_impl@)
                    },
                    Err(LogErr::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                    Err(e) => e == LogErr::PmemErr{ err: PmemError::AccessOutOfRange },
                }
        {
            // We allow the untrusted `start` method to update memory
            // as part of its initialization. But, to avoid bugs
            // stemming from crashes in the middle of this routine, we
            // must restrict how it updates memory. We must only let
            // it write such that, if a crash happens in the middle,
            // it doesn't change the persistent state.

            let (mut pm_region2, Tracked(mut frac)) = PMRegionV2::new(pm_region);

            let ghost state = UntrustedLogImpl::recover(pm_region@.durable_state, log_id).get_Some_0();
            let tracked abs = FractionalResource::<AbstractLogCrashState, 2>::alloc(AbstractLogCrashState{
                state1: state,
                state2: state,
            });

            let ghost iparam = LogInvParam {
                pm_frac_id: pm_region2.id(),
                crash_frac_id: abs.id(),
                log_id: log_id,
            };
            let tracked istate = LogInvState {
                pm: frac.split_mut(1),
                crash: abs.split_mut(1),
            };
            let tracked inv = AtomicInvariant::<_, _, LogInvPred>::new(iparam, istate, PMEM_INV_NS as int);
            let tracked inv = Arc::new(inv);

            let mut wrpm_region = WriteRestrictedPersistentMemoryRegionV2::new(pm_region2, Tracked(frac), Tracked(inv.clone()));
            let tracked perm = PermissionV2::new(&abs, iparam);
            let untrusted_log_impl =
                UntrustedLogImpl::start(&mut wrpm_region, log_id, Tracked(&perm), Ghost(state))?;

            open_atomic_invariant!(&inv => inner => { proof {
                abs.combine_mut(inner.crash);
                abs.update_mut(AbstractLogCrashState{
                    state1: state.drop_pending_appends(),
                    state2: state.drop_pending_appends(),
                });
                inner.crash = abs.split_mut(1);
                inner.pm.agree(wrpm_region.frac.borrow());
            }});

            Ok(
                LogImpl {
                    untrusted_log_impl,
                    log_id: Ghost(log_id),
                    wrpm_region,
                    abs: Tracked(abs),
                    inv: Tracked(inv),
                },
            )
        }

        // The `tentatively_append` method tentatively appends
        // `bytes_to_append` to the end of the log. It's tentative in
        // that crashes will undo the appends, and reads aren't
        // allowed in the tentative part of the log. See `README.md` for
        // more documentation and examples of use.
        pub exec fn tentatively_append(&mut self, bytes_to_append: &[u8]) -> (result: Result<u128, LogErr>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                self.constants() == old(self).constants(),
                match result {
                    Ok(offset) => {
                        let state = old(self)@;
                        &&& offset == state.head + state.log.len() + state.pending.len()
                        &&& self@ == old(self)@.tentatively_append(bytes_to_append@)
                    },
                    Err(LogErr::InsufficientSpaceForAppend { available_space }) => {
                        &&& self@ == old(self)@
                        &&& available_space < bytes_to_append@.len()
                        &&& {
                               ||| available_space == self@.capacity - self@.log.len() - self@.pending.len()
                               ||| available_space == u128::MAX - self@.head - self@.log.len() - self@.pending.len()
                           }
                    },
                    _ => false
                }
        {
            // For crash safety, we must restrict the untrusted code's
            // writes to persistent memory. We must only let it write
            // such that, if a crash happens in the middle of a write,
            // the view of the persistent state is the current
            // state with pending appends dropped.
            let tracked perm = PermissionV2::new(self.abs.borrow(), self.inv@.constant());
            self.untrusted_log_impl.tentatively_append(&mut self.wrpm_region, bytes_to_append,
                                                       self.log_id, Tracked(&perm))
        }

        // The `commit` method atomically commits all tentative
        // appends that have been done to `self` since the last
        // commit. The commit is atomic in that even if there's a
        // crash in the middle, the recovered-to state either reflects
        // all those tentative appends or none of them. See `README.md`
        // for more documentation and examples of use.
        pub exec fn commit(&mut self) -> (result: Result<(), LogErr>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                self.constants() == old(self).constants(),
                match result {
                    Ok(()) => self@ == old(self)@.commit(),
                    _ => false
                }
        {
            // For crash safety, we must restrict the untrusted code's
            // writes to persistent memory. We must only let it write
            // such that, if a crash happens in the middle of a write,
            // the view of the persistent state is either the current
            // state with all pending appends dropped or the current
            // state with all uncommitted appends committed.
            open_atomic_invariant!(self.inv.borrow() => inner => { proof {
                self.abs.borrow_mut().combine_mut(inner.crash);
                self.abs.borrow_mut().update_mut(AbstractLogCrashState{
                    state1: self@.drop_pending_appends(),
                    state2: self@.commit().drop_pending_appends(),
                });
                inner.crash = self.abs.borrow_mut().split_mut(1);

                assert forall |s| recover_into(s, self.log_id@, AbstractLogCrashState{ state1: self@.drop_pending_appends(), state2: self@.drop_pending_appends() }) implies #[trigger] recover_into(s, self.log_id@, self.abs@.val()) by {};
            }});
            let tracked perm = PermissionV2::new(self.abs.borrow(), self.inv@.constant());
            let res = self.untrusted_log_impl.commit(&mut self.wrpm_region, self.log_id, Tracked(&perm));
            open_atomic_invariant!(self.inv.borrow() => inner => { proof {
                self.abs.borrow_mut().combine_mut(inner.crash);
                self.abs.borrow_mut().update_mut(AbstractLogCrashState{
                    state1: self@.drop_pending_appends(),
                    state2: self@.drop_pending_appends(),
                });
                inner.crash = self.abs.borrow_mut().split_mut(1);
                inner.pm.agree(self.wrpm_region.frac.borrow());
            }});
            res
        }

        // The `advance_head` method advances the head of the log to
        // virtual new head position `new_head`. It doesn't do this
        // tentatively; it completes it durably before returning.
        // However, `advance_head` doesn't commit tentative appends;
        // to do that, you need a separate call to `commit`. See
        // `README.md` for more documentation and examples of use.
        pub exec fn advance_head(&mut self, new_head: u128) -> (result: Result<(), LogErr>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                self.constants() == old(self).constants(),
                match result {
                    Ok(()) => {
                        let state = old(self)@;
                        &&& state.head <= new_head <= state.head + state.log.len()
                        &&& self@ == old(self)@.advance_head(new_head as int)
                    },
                    Err(LogErr::CantAdvanceHeadPositionBeforeHead { head }) => {
                        &&& self@ == old(self)@
                        &&& head == self@.head
                        &&& new_head < head
                    },
                    Err(LogErr::CantAdvanceHeadPositionBeyondTail { tail }) => {
                        &&& self@ == old(self)@
                        &&& tail == self@.head + self@.log.len()
                        &&& new_head > tail
                    },
                    _ => false,
                }
        {
            // For crash safety, we must restrict the untrusted code's
            // writes to persistent memory. We must only let it write
            // such that, if a crash happens in the middle of a write,
            // the view of the persistent state is either the current
            // state or the current state with the head advanced.
            open_atomic_invariant!(self.inv.borrow() => inner => { proof {
                self.abs.borrow_mut().combine_mut(inner.crash);
                self.abs.borrow_mut().update_mut(AbstractLogCrashState{
                    state1: self@.drop_pending_appends(),
                    state2: self@.advance_head(new_head as int).drop_pending_appends(),
                });
                inner.crash = self.abs.borrow_mut().split_mut(1);

                assert forall |s| recover_into(s, self.log_id@, AbstractLogCrashState{ state1: self@.drop_pending_appends(), state2: self@.drop_pending_appends() }) implies #[trigger] recover_into(s, self.log_id@, self.abs@.val()) by {};
            }});
            let tracked perm = PermissionV2::new(self.abs.borrow(), self.inv@.constant());
            let res = self.untrusted_log_impl.advance_head(&mut self.wrpm_region, new_head,
                                                           self.log_id, Tracked(&perm));
            open_atomic_invariant!(self.inv.borrow() => inner => { proof {
                self.abs.borrow_mut().combine_mut(inner.crash);
                self.abs.borrow_mut().update_mut(AbstractLogCrashState{
                    state1: self@.drop_pending_appends(),
                    state2: self@.drop_pending_appends(),
                });
                inner.crash = self.abs.borrow_mut().split_mut(1);
                inner.pm.agree(self.wrpm_region.frac.borrow());
            }});
            res
        }

        // The `read` method reads `len` bytes from the log starting
        // at virtual position `pos`. It isn't allowed to read earlier
        // than the head or past the committed tail. See `README.md` for
        // more documentation and examples of use.
        pub exec fn read(&self, pos: u128, len: u64) -> (result: Result<Vec<u8>, LogErr>)
            requires
                self.valid(),
                pos + len <= u128::MAX,
            ensures
                ({
                    let state = self@;
                    let head = state.head;
                    let log = state.log;
                    match result {
                        Ok(bytes) => {
                            let true_bytes = self@.read(pos as int, len as int);
                            &&& pos >= head
                            &&& pos + len <= head + log.len()
                            &&& read_correct_modulo_corruption(bytes@, true_bytes,
                                                             self.constants().impervious_to_corruption)
                        },
                        Err(LogErr::CantReadBeforeHead{ head: head_pos }) => {
                            &&& pos < head
                            &&& head_pos == head
                        },
                        Err(LogErr::CantReadPastTail{ tail }) => {
                            &&& pos + len > tail
                            &&& tail == head + log.len()
                        },
                        Err(e) => e == LogErr::PmemErr{ err: PmemError::AccessOutOfRange },
                    }
                })
        {
            let (bytes, addrs) = self.untrusted_log_impl.read(&self.wrpm_region, pos, len, self.log_id)?;
            Ok(bytes)
        }

        // The `get_head_tail_and_capacity` method returns three
        // pieces of metadata about the log: the virtual head
        // position, the virtual tail position, and the capacity. The
        // capacity is the maximum number of bytes there can be in the
        // log past the head, including bytes in tentative appends
        // that haven't been committed yet. See `README.md` for more
        // documentation and examples of use.
        pub exec fn get_head_tail_and_capacity(&self) -> (result: Result<(u128, u128, u64), LogErr>)
            requires
                self.valid()
            ensures
                match result {
                    Ok((result_head, result_tail, result_capacity)) => {
                        &&& result_head == self@.head
                        &&& result_tail == self@.head + self@.log.len()
                        &&& result_capacity == self@.capacity
                    },
                    _ => false
                }
        {
            self.untrusted_log_impl.get_head_tail_and_capacity(&self.wrpm_region, self.log_id)
        }
    }

}
