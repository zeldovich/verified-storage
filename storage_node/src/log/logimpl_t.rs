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

    // This specification function indicates whether a given view of
    // memory can only crash in a way that, after recovery, leads to a
    // certain abstract state.
    pub open spec fn can_only_crash_as_state(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        state: AbstractLogState,
    ) -> bool
    {
        forall |s| #[trigger] pm_region_view.can_crash_as(s) ==>
            UntrustedLogImpl::recover(s, log_id) == Some(state)
    }

    // A `TrustedPermission` is the type of a tracked object
    // indicating permission to update memory. It restricts updates so
    // that if a crash happens, the resulting memory `mem` satisfies
    // `is_state_allowable(mem)`.
    //
    // The struct is defined in this file, and it has a non-public
    // field, so the only code that can create one is in this file.
    // So untrusted code in other files can't create one, and we can
    // rely on it to restrict access to persistent memory.

    pub struct AbstractLogCrashState {
        state1: AbstractLogState,
        state2: AbstractLogState,
    }

    #[allow(dead_code)]
    pub struct TrustedPermission {
        ghost log_id: u128,
        tracked frac: FractionalResource<AbstractLogCrashState, 2>,
    }

    closed spec fn recover_into(s: Seq<u8>, log_id: u128, crash: AbstractLogCrashState) -> bool {
        UntrustedLogImpl::recover(s, log_id) == Some(crash.state1) ||
        UntrustedLogImpl::recover(s, log_id) == Some(crash.state2)
    }

    impl CheckPermission<Seq<u8>> for TrustedPermission {
        closed spec fn check_permission(&self, state: Seq<u8>) -> bool {
            recover_into(state, self.log_id, self.frac.val())
        }
    }

    impl TrustedPermission {

        // This is one of two constructors for `TrustedPermission`.
        // It conveys permission to do any update as long as a
        // subsequent crash and recovery can only lead to given
        // abstract state `state`.
        proof fn new_one_possibility(tracked frac: FractionalResource<AbstractLogCrashState, 2>,
                                     log_id: u128,
                                     state: AbstractLogState) -> (tracked perm: Self)
            requires
                frac.inv(),
                frac.frac() == 1,
                frac.val().state1 == state,
                frac.val().state2 == state,
            ensures
                perm.frac == frac,
                forall |s| #[trigger] perm.check_permission(s) <==>
                    UntrustedLogImpl::recover(s, log_id) == Some(state)
        {
            Self::new_two_possibilities(frac, log_id, state, state)
        }

        // This is the second of two constructors for
        // `TrustedPermission`.  It conveys permission to do any
        // update as long as a subsequent crash and recovery can only
        // lead to one of two given abstract states `state1` and
        // `state2`.
        proof fn new_two_possibilities(
            tracked frac: FractionalResource<AbstractLogCrashState, 2>,
            log_id: u128,
            state1: AbstractLogState,
            state2: AbstractLogState
        ) -> (tracked perm: Self)
            requires
                frac.inv(),
                frac.frac() == 1,
                frac.val().state1 == state1,
                frac.val().state2 == state2,
            ensures
                perm.frac == frac,
                forall |s| #[trigger] perm.check_permission(s) <==> {
                    ||| UntrustedLogImpl::recover(s, log_id) == Some(state1)
                    ||| UntrustedLogImpl::recover(s, log_id) == Some(state2)
                }
        {
            Self {
                log_id: log_id,
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
        // State of the persistent memory from PersistentMemoryRegion.
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
            forall |s| v.pm.val().can_crash_as(s) ==> #[trigger] recover_into(s, k.log_id, v.crash.val())
        }
    }

    #[allow(dead_code)]
    pub struct WriteRestrictedPersistentMemoryRegionV2<PMRegion>
        where
            PMRegion: PersistentMemoryRegionV2
    {
        pub pm_region: PMRegion,
        pub frac: Tracked<FractionalResource<PersistentMemoryRegionView, 3>>,
        pub inv: Tracked<Arc<AtomicInvariant<LogInvParam, LogInvState, LogInvPred>>>,
    }

    pub struct EmptyResult {}

    pub struct WRPMGetRegionSize<'a> {
        frac: &'a FractionalResource<PersistentMemoryRegionView, 3>,
    }

    impl PMRegionGetSizeOperation<EmptyResult> for WRPMGetRegionSize<'_> {
        closed spec fn id(&self) -> int { self.frac.id() }
        closed spec fn pre(&self) -> bool {
            self.frac.inv()
        }
        closed spec fn post(&self, r: EmptyResult, v: u64) -> bool {
            v == self.frac.val().len()
        }

        proof fn apply(tracked self, tracked r: &mut FractionalResource<PersistentMemoryRegionView, 3>,
                       v: u64, tracked credit: OpenInvariantCredit) -> (tracked result: EmptyResult)
        {
            r.agree(self.frac);
            EmptyResult{}
        }
    }

    pub struct WRPMReadUnaligned<'a> {
        addr: u64,
        num_bytes: u64,
        ghost constants: PersistentMemoryConstants,
        frac: &'a FractionalResource<PersistentMemoryRegionView, 3>,
    }

    impl PMRegionReadOperation<EmptyResult> for WRPMReadUnaligned<'_> {
        closed spec fn addr(&self) -> u64 { self.addr }
        closed spec fn num_bytes(&self) -> u64 { self.num_bytes }
        closed spec fn constants(&self) -> PersistentMemoryConstants { self.constants }
        closed spec fn id(&self) -> int { self.frac.id() }
        closed spec fn pre(&self) -> bool {
            self.frac.inv() &&
            self.addr() + self.num_bytes() <= self.frac.val().len() &&
            self.frac.val().no_outstanding_writes_in_range(self.addr() as int, self.addr() + self.num_bytes())
        }
        closed spec fn post(&self, r: EmptyResult, v: Result<Vec<u8>, PmemError>) -> bool {
            match v {
                Ok(bytes) => {
                    let true_bytes = self.frac.val().committed().subrange(self.addr() as int, self.addr() + self.num_bytes());
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
            }
        }

        proof fn validate(tracked &self, tracked r: &mut FractionalResource<PersistentMemoryRegionView, 3>,
                          tracked credit: OpenInvariantCredit)
        {
            r.agree(self.frac)
        }

        proof fn apply(tracked self, tracked r: &mut FractionalResource<PersistentMemoryRegionView, 3>,
                       v: Result<Vec<u8>, PmemError>, tracked credit: OpenInvariantCredit) -> (tracked result: EmptyResult)
        {
            r.agree(self.frac);
            EmptyResult{}
        }
    }

    pub struct WriteResult {
        frac: FractionalResource<PersistentMemoryRegionView, 3>,
    }

    pub struct WRPMWriteUnaligned<'a> {
        ghost addr: u64,
        ghost bytes: Seq<u8>,
        tracked frac: FractionalResource<PersistentMemoryRegionView, 3>,
        tracked loginv: &'a AtomicInvariant<LogInvParam, LogInvState, LogInvPred>,
        tracked perm: &'a TrustedPermission,
    }

    impl PMRegionWriteOperation<WriteResult> for WRPMWriteUnaligned<'_> {
        closed spec fn addr(&self) -> u64 { self.addr }
        closed spec fn bytes(&self) -> Seq<u8> { self.bytes }
        closed spec fn id(&self) -> int { self.frac.id() }
        closed spec fn pre(&self) -> bool {
            self.frac.inv() &&
            self.frac.frac() == 1 &&
            self.addr() + self.bytes().len() <= self.frac.val().len() &&
            self.addr() + self.bytes().len() <= u64::MAX &&
            self.frac.val().no_outstanding_writes_in_range(self.addr() as int, self.addr() + self.bytes().len()) &&
            self.loginv.namespace() == PMEM_INV_NS &&
            self.loginv.constant().pm_frac_id == self.frac.id() &&
            self.perm.frac.valid(self.loginv.constant().crash_frac_id, 1) &&
            self.perm.log_id == self.loginv.constant().log_id &&
            forall |s| self.frac.val().write(self.addr() as int, self.bytes()).can_crash_as(s)
                  ==> #[trigger] self.perm.check_permission(s)
        }
        closed spec fn post(&self, r: WriteResult) -> bool {
            r.frac.valid(self.frac.id(), 1) &&
            r.frac.val() == self.frac.val().write(self.addr() as int, self.bytes())
        }

        proof fn validate(tracked &self, tracked r: &mut FractionalResource<PersistentMemoryRegionView, 3>,
                          tracked credit: OpenInvariantCredit)
        {
            r.agree(&self.frac)
        }

        proof fn apply(tracked self, tracked r: &mut FractionalResource<PersistentMemoryRegionView, 3>,
                       tracked credit: OpenInvariantCredit) -> (tracked result: WriteResult)
        {
            let tracked mut mself = self;
            r.combine_mut(mself.frac);
            open_atomic_invariant!(credit => &mself.loginv => inner => {
                inner.crash.agree(&mself.perm.frac);
                r.combine_mut(inner.pm);
                r.update_mut(r.val().write(self.addr() as int, self.bytes()));
                inner.pm = r.split_mut(1);

                assert forall |s| self.perm.check_permission(s) implies #[trigger] recover_into(s, mself.loginv.constant().log_id, inner.crash.val()) by {};
            });
            WriteResult{
                frac: r.split_mut(1)
            }
        }
    }

    impl<PMRegion> WriteRestrictedPersistentMemoryRegionTrait<TrustedPermission> for WriteRestrictedPersistentMemoryRegionV2<PMRegion>
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

        open spec fn same_as(&self, other: &Self) -> bool {
            self.constants() == other.constants() &&
            self.pm_region.id() == other.pm_region.id() &&
            self.inv@.constant() == other.inv@.constant()
        }

        closed spec fn validperm(&self, p: &TrustedPermission) -> bool
        {
            p.frac.valid(self.inv@.constant().crash_frac_id, 1) &&
            p.log_id == self.inv@.constant().log_id
        }

        exec fn get_region_size(&self) -> (result: u64)
        {
            let tracked op = WRPMGetRegionSize{ frac: self.frac.borrow() };
            let (result, Tracked(opres)) = self.pm_region.get_region_size::<_, WRPMGetRegionSize>(Tracked(op));
            result
        }

        exec fn write(&mut self, addr: u64, bytes: &[u8], Tracked(perm): Tracked<&TrustedPermission>) {
            let tracked mut frac = FractionalResource::<PersistentMemoryRegionView, 3>::default();
            proof {
                tracked_swap(self.frac.borrow_mut(), &mut frac);
            };
            let tracked op = WRPMWriteUnaligned{
                addr: addr,
                bytes: bytes@,
                frac: frac,
                loginv: self.inv.borrow(),
                perm: perm,
            };
            let Tracked(opres) = self.pm_region.write::<_, WRPMWriteUnaligned>(addr, bytes, Tracked(op));
            self.frac = Tracked(opres.frac);
        }

        #[verifier::external_body]
        exec fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S, perm: Tracked<&TrustedPermission>) {
            unimplemented!()
        }

        #[verifier::external_body]
        exec fn flush(&mut self) {
            unimplemented!()
        }

        #[verifier::external_body]
        exec fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
            where S: PmCopy + Sized
        {
            unimplemented!()
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
    /// tracked `TrustedPermission`. So we can pass `wrpm_region` to an
    /// untrusted method, along with a restricting
    /// `TrustedPermission`, to limit what it's allowed to do.

    pub struct LogImpl<PMRegion: PersistentMemoryRegionV2> {
        untrusted_log_impl: UntrustedLogImpl,
        log_id: Ghost<u128>,
        wrpm_region: WriteRestrictedPersistentMemoryRegionV2<PMRegion>,
        abs: Tracked<FractionalResource<AbstractLogCrashState, 2>>,
        inv: Tracked<Arc<AtomicInvariant<LogInvParam, LogInvState, LogInvPred>>>,
    }

    impl <PMRegion: PersistentMemoryRegionV2> LogImpl<PMRegion> {
        // The view of a `LogImpl` is whatever the
        // `UntrustedLogImpl` it wraps says it is.
        pub closed spec fn view(self) -> AbstractLogState
        {
            // self.abs@.val()
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
            &&& can_only_crash_as_state(self.wrpm_region@, self.log_id@, self@.drop_pending_appends())
            &&& self.abs@.valid(self.inv@.constant().crash_frac_id, 1)
            &&& self.abs@.val() == AbstractLogCrashState{ state1: self@.drop_pending_appends(), state2: self@.drop_pending_appends() }
            &&& self.wrpm_region.inv()
            &&& self.wrpm_region.pm_region.id() == self.inv@.constant().pm_frac_id
            &&& self.log_id@ == self.inv@.constant().log_id
        }

        // The `setup` method sets up persistent memory regions
        // `pm_region` to store an initial empty log. It returns a
        // vector listing the capacity of the log as well as a
        // fresh log ID to uniquely identify it. See `README.md`
        // for more documentation.
        #[verifier::external_body]
        pub exec fn setup(pm_region: &mut PMRegion, Tracked(frac): Tracked<FractionalResource<PersistentMemoryRegionView, 3>>) -> (result: (Result<(u64, u128), LogErr>, Tracked<FractionalResource<PersistentMemoryRegionView, 3>>))
            requires
                old(pm_region).inv(),
                frac.valid(old(pm_region).id(), 2),
            ensures
                pm_region.inv(),
                pm_region.id() == old(pm_region).id(),
                result.1@.valid(pm_region.id(), 2),
                result.1@.val().no_outstanding_writes(),
                match result.0 {
                    Ok((log_capacity, log_id)) => {
                        let state = AbstractLogState::initialize(log_capacity as int);
                        &&& log_capacity <= result.1@.val().len()
                        &&& result.1@.val().len() == frac.val().len()
                        &&& can_only_crash_as_state(result.1@.val(), log_id, state)
                        &&& UntrustedLogImpl::recover(result.1@.val().committed(), log_id) == Some(state)
                        // Required by the `start` function's precondition. Putting this in the
                        // postcond of `setup` ensures that the trusted caller doesn't have to prove it
                        &&& UntrustedLogImpl::recover(result.1@.val().flush().committed(), log_id) == Some(state)
                        &&& state == state.drop_pending_appends()
                    },
                    Err(LogErr::InsufficientSpaceForSetup { required_space }) => {
                        &&& result.1@.val() == frac.val().flush()
                        &&& result.1@.val().len() < required_space
                    },
                    _ => false
                }
        {
            /*
            let log_id = generate_fresh_log_id();
            let capacities = UntrustedLogImpl::setup(pm_region, log_id);
            match capacities {
                Err(e) => { (Err(e), Tracked(frac)) },
                Ok(capacities) => { Ok((capacities, log_id)) },
            }
            */
            unimplemented!()
        }

        // The `start` method creates an `UntrustedLogImpl` out of a
        // persistent memory region. It's assumed that the region was
        // initialized with `setup` and then only log operations were
        // allowed to mutate them. See `README.md` for more
        // documentation and an example of use.
        pub exec fn start(pm_region: PMRegion, log_id: u128, Tracked(frac): Tracked<FractionalResource<PersistentMemoryRegionView, 3>>) -> (result: Result<LogImpl<PMRegion>, LogErr>)
            requires
                pm_region.inv(),
                frac.valid(pm_region.id(), 2),
                UntrustedLogImpl::recover(frac.val().flush().committed(), log_id).is_Some(),
            ensures
                match result {
                    Ok(trusted_log_impl) => {
                        &&& trusted_log_impl.valid()
                        &&& trusted_log_impl.constants() == pm_region.constants()
                        &&& Some(trusted_log_impl@) == UntrustedLogImpl::recover(frac.val().flush().committed(),
                                                                                 log_id)
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

            let ghost state = UntrustedLogImpl::recover(frac.val().flush().committed(), log_id).get_Some_0();

            let tracked abs = FractionalResource::<AbstractLogCrashState, 2>::alloc(AbstractLogCrashState{
                state1: state,
                state2: state,
            });
            let tracked (abs1, abs2) = abs.split(1);
            let tracked (pm1, pm2) = frac.split(1);

            let ghost inv_param = LogInvParam {
                pm_frac_id: pm_region.id(),
                crash_frac_id: abs.id(),
                log_id: log_id,
            };
            let tracked inv_state = LogInvState {
                pm: pm2,
                crash: abs2,
            };
            let tracked inv = AtomicInvariant::<_, _, LogInvPred>::new(inv_param, inv_state, PMEM_INV_NS as int);
            let tracked inv = Arc::new(inv);

            let mut wrpm_region = WriteRestrictedPersistentMemoryRegionV2::new(pm_region, Tracked(pm1), Tracked(inv.clone()));

            let tracked perm = TrustedPermission::new_one_possibility(abs1, log_id, state);
            let untrusted_log_impl =
                UntrustedLogImpl::start(&mut wrpm_region, log_id, Tracked(&perm), Ghost(state))?;
            Ok(
                LogImpl {
                    untrusted_log_impl,
                    log_id:  Ghost(log_id),
                    abs: Tracked(perm.frac),
                    inv: Tracked(inv.clone()),
                    wrpm_region
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
            let tracked mut abs = FractionalResource::<AbstractLogCrashState, 2>::default();
            proof {
                tracked_swap(self.abs.borrow_mut(), &mut abs);
            };
            let tracked perm = TrustedPermission::new_one_possibility(abs, self.log_id@, self@.drop_pending_appends());
            let res = self.untrusted_log_impl.tentatively_append(&mut self.wrpm_region, bytes_to_append,
                                                                 self.log_id, Tracked(&perm));
            // XXX update abs state
            self.abs = Tracked(perm.frac);
            res
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
            let tracked mut abs = FractionalResource::<AbstractLogCrashState, 2>::default();
            let Tracked(credit) = create_open_invariant_credit();
            proof {
                tracked_swap(self.abs.borrow_mut(), &mut abs);

                open_atomic_invariant!(credit => self.inv.borrow() => inner => {
                    abs.combine_mut(inner.crash);
                    abs.update_mut(AbstractLogCrashState{
                        state1: self@.drop_pending_appends(),
                        state2: self@.commit().drop_pending_appends(),
                    });
                    inner.crash = abs.split_mut(1);

                    assert forall |s| recover_into(s, self.inv@.constant().log_id, AbstractLogCrashState{ state1: self@.drop_pending_appends(), state2: self@.drop_pending_appends() }) implies #[trigger] recover_into(s, self.inv@.constant().log_id, AbstractLogCrashState{ state1: self@.drop_pending_appends(), state2: self@.commit().drop_pending_appends() }) by {};
                });
            };
            let tracked perm = TrustedPermission::new_two_possibilities(abs, self.log_id@, self@.drop_pending_appends(),
                                                                        self@.commit().drop_pending_appends());
            let res = self.untrusted_log_impl.commit(&mut self.wrpm_region, self.log_id, Tracked(&perm));
            let tracked mut abs = perm.frac;
            let Tracked(credit) = create_open_invariant_credit();
            proof {
                open_atomic_invariant!(credit => self.inv.borrow() => inner => {
                    abs.combine_mut(inner.crash);
                    abs.update_mut(AbstractLogCrashState{
                        state1: self@.drop_pending_appends(),
                        state2: self@.drop_pending_appends(),
                    });
                    inner.crash = abs.split_mut(1);
                    inner.pm.agree(self.wrpm_region.frac.borrow());
                });
            };
            self.abs = Tracked(abs);
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
            let tracked mut abs = FractionalResource::<AbstractLogCrashState, 2>::default();
            let Tracked(credit) = create_open_invariant_credit();
            proof {
                tracked_swap(self.abs.borrow_mut(), &mut abs);

                open_atomic_invariant!(credit => self.inv.borrow() => inner => {
                    abs.combine_mut(inner.crash);
                    abs.update_mut(AbstractLogCrashState{
                        state1: self@.drop_pending_appends(),
                        state2: self@.advance_head(new_head as int).drop_pending_appends(),
                    });
                    inner.crash = abs.split_mut(1);

                    assert forall |s| recover_into(s, self.inv@.constant().log_id, AbstractLogCrashState{ state1: self@.drop_pending_appends(), state2: self@.drop_pending_appends() }) implies #[trigger] recover_into(s, self.inv@.constant().log_id, AbstractLogCrashState{ state1: self@.drop_pending_appends(), state2: self@.advance_head(new_head as int).drop_pending_appends() }) by {};
                });
            };
            let tracked perm = TrustedPermission::new_two_possibilities(
                abs,
                self.log_id@,
                self@.drop_pending_appends(),
                self@.advance_head(new_head as int).drop_pending_appends()
            );
            let res = self.untrusted_log_impl.advance_head(&mut self.wrpm_region, new_head,
                                                           self.log_id, Tracked(&perm));
            let tracked mut abs = perm.frac;
            let Tracked(credit) = create_open_invariant_credit();
            proof {
                open_atomic_invariant!(credit => self.inv.borrow() => inner => {
                    abs.combine_mut(inner.crash);
                    abs.update_mut(AbstractLogCrashState{
                        state1: self@.drop_pending_appends(),
                        state2: self@.drop_pending_appends(),
                    });
                    inner.crash = abs.split_mut(1);
                });
            };
            self.abs = Tracked(abs);
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
