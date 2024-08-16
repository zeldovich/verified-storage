use std::fmt::Write;

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::kv::durable::metadata::layout_v::ListEntryMetadata;
use crate::log2::{logimpl_v::*, logspec_t::*, layout_v::*, inv_v::*};
use crate::kv::durable::oplog::logentry_v::*;
use crate::kv::durable::oplog::oplogspec_t::*;
use crate::kv::kvimpl_t::*;
use crate::kv::layout_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t;
use crate::pmem::traits_t::PmSafe;
use crate::pmem::crc_t::*;
use vstd::bytes::*;

use super::inv_v::*;

verus! {
    pub struct UntrustedOpLog<K, L>
        where 
            L: PmCopy + std::fmt::Debug + Copy,
    {
        log: UntrustedLogImpl,
        overall_metadata: OverallMetadata,
        state: Ghost<AbstractOpLogState>,
        current_transaction_crc: CrcDigest,
        _phantom: Option<(K, L)>
    }

    impl<K, L> UntrustedOpLog<K, L>
        where 
            L: PmCopy + std::fmt::Debug + Copy,
            K: std::fmt::Debug,
    {

        pub closed spec fn log_start_addr(self) -> u64 {
            self.overall_metadata.log_area_addr
        }

        pub closed spec fn log_size(self) -> u64 {
            self.overall_metadata.log_area_size
        }

        pub closed spec fn overall_metadata(self) -> OverallMetadata {
            self.overall_metadata
        }

        pub closed spec fn base_log_capacity(self) -> int {
            self.log@.capacity
        }

        pub closed spec fn base_log_view(self) -> AbstractLogState {
            self.log@
        }

        pub closed spec fn log_entry_valid(self, pm_region: PersistentMemoryRegionView, op: AbstractPhysicalOpLogEntry) -> bool {
            // all addrs are within the bounds of the device
            &&& 0 <= op.absolute_addr < op.absolute_addr + op.len < pm_region.len() <= u64::MAX
            // no logged ops change bytes belonging to the log itself
            &&& (op.absolute_addr + op.len < self.overall_metadata.log_area_addr || self.overall_metadata.log_area_addr + self.overall_metadata.log_area_size <= op.absolute_addr)
        }

        pub closed spec fn crc_invariant(self) -> bool {
            self.current_transaction_crc.bytes_in_digest().flatten() == self.log@.pending
        }

        // TODO: should this take overall metadata and say that recovery is successful?
        pub closed spec fn inv<Perm, PM>(self, pm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>) -> bool
            where 
                Perm: CheckPermission<Seq<u8>>,
                PM: PersistentMemoryRegion,
        {
            &&& self.log.inv(pm_region, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat)
            &&& ({
                    // either the op log and base log are empty, or they are not and there are 
                    // bytes in the current transaction's CRC digest
                    ||| self@.physical_op_list.len() == 0
                    ||| self.current_transaction_crc.bytes_in_digest().len() > 0
                })
            &&& ({
                    // either the base log is empty or the op log is committed and non-empty
                    ||| self.log@.log.len() == 0
                    ||| (self@.op_list_committed && self@.physical_op_list.len() > 0)
                })
            &&& self.crc_invariant()
            &&& !self@.op_list_committed ==> {
                // if we aren't committed, then parsing the pending bytes (ignoring crc check,
                // since we haven't written the CRC yet) should give us the current abstract log op list
                let pending_bytes = self.log@.pending;
                let log_ops = Self::parse_log_ops(pending_bytes, self.overall_metadata.log_area_addr as nat, 
                    self.overall_metadata.log_area_size as nat, self.overall_metadata.region_size as nat);
                ||| {
                        &&& log_ops is Some 
                        &&& log_ops.unwrap() == self@.physical_op_list
                    }
                // tentatively appending requires two base log appends, so if the op log append fails,
                // we could end up with pending bytes that cannot be parsed. 
                ||| log_ops is None
            }
            &&& forall |i: int| 0 <= i < self@.physical_op_list.len() ==> {
                    let op = #[trigger] self@.physical_op_list[i];
                    self.log_entry_valid(pm_region@, op)
            } 
            &&& self.overall_metadata.log_area_addr < self.overall_metadata.log_area_addr + self.overall_metadata.log_area_size <= pm_region@.len() <= u64::MAX
            &&& self.overall_metadata.log_area_addr as int % const_persistence_chunk_size() == 0
            &&& no_outstanding_writes_to_metadata(pm_region@, self.overall_metadata.log_area_addr as nat)
        }

        pub closed spec fn view(self) -> AbstractOpLogState
        {
            self.state@
        }

        pub closed spec fn log_len(self) -> nat {
            self.log@.log.len()
        }

        pub open spec fn recover(mem: Seq<u8>, overall_metadata: OverallMetadata) -> Option<AbstractOpLogState>
        {
            // use log's recover method to recover the log state, then parse it into operations
            match UntrustedLogImpl::recover(mem, overall_metadata.log_area_addr as nat,
                                            overall_metadata.log_area_size as nat) {
                Some(log) => {
                    if log.log.len() == 0 {
                        Some(AbstractOpLogState::initialize())
                    } else {
                        if let Some(log_contents) = Self::get_log_contents(log) {
                            // parsing the log only obtains physical entries, but we (should) know that there is a corresponding logical op log (even
                            // if we don't know exactly what it is)
                            if let Some(physical_log_entries) =  Self::parse_log_ops(
                                log_contents, 
                                overall_metadata.log_area_addr as nat, 
                                overall_metadata.log_area_size as nat,
                                overall_metadata.region_size as nat
                            ) {
                                // if exists |logical_log: Seq<LogicalOpLogEntry<_>>| logical_and_physical_logs_correspond::<L>(logical_log, physical_log_entries) {
                                //     let logical_log_entries = choose |logical_log| logical_and_physical_logs_correspond(logical_log, physical_log_entries);
                                    Some(AbstractOpLogState {
                                        // logical_op_list: logical_log_entries,
                                        physical_op_list: physical_log_entries,
                                        op_list_committed: true
                                    })
                                // } else {
                                //     None
                                // }
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    }
                }
                None => None
            }
        }

        pub open spec fn get_log_contents(log: AbstractLogState) -> Option<Seq<u8>>
        {
            let log_contents = extract_bytes(log.log, 0, (log.log.len() - u64::spec_size_of()) as nat);
            let crc_bytes = extract_bytes(log.log, (log.log.len() - u64::spec_size_of()) as nat, u64::spec_size_of());
            let crc = u64::spec_from_bytes(crc_bytes);
            // if the crc written at the end of the transaction does not match the crc of the rest of the log contents, the log is invalid
            if !u64::bytes_parseable(crc_bytes) {
                None
            } else if crc != spec_crc_u64(log_contents) {
                None
            } else {
                Some(log_contents)
            }
        }

        // This lemma helps us prove that recursively parsing the physical log (which, due to the 
        // structure of the log, can only be specified in one direction, which happens to 
        // be opposite of the direction we want) is equivalent to iteratively parsing it. We invoke
        // this lemma to maintain the loop invariant of `parse_phys_op_log` which states that 
        // iteratively parsing the log up to the current offset is equivalent to recursively
        // parsing it up to that same offset.
        proof fn lemma_op_log_parse_equal(
            start: nat,
            mid: nat,
            end: nat,
            log_contents: Seq<u8>,
            log_start_addr: nat, 
            log_size: nat,
            region_size: nat,
        )
        requires
            start <= mid <= end <= log_contents.len(),
            Self::parse_log_ops_helper(start, mid, log_contents, log_start_addr, log_size, region_size) is Some,
            Self::parse_log_op(mid, log_contents, log_start_addr, log_size, region_size) is Some,
            ({
                let last_op = Self::parse_log_op(mid, log_contents, log_start_addr, log_size, region_size);
                &&& last_op matches Some(last_op)
                &&& end == last_op.offset + u64::spec_size_of() * 2 + last_op.len
            })
        ensures 
            Self::parse_log_ops_helper(start, end, log_contents, log_start_addr, log_size, region_size) is Some,
            ({
                let old_seq = Self::parse_log_ops_helper(start, mid, log_contents, log_start_addr, log_size, region_size).unwrap();
                let new_seq = Self::parse_log_ops_helper(start, end, log_contents, log_start_addr, log_size, region_size).unwrap();
                let last_op = Self::parse_log_op(mid, log_contents, log_start_addr, log_size, region_size).unwrap();
                new_seq == old_seq + seq![last_op]
            }),
        decreases end - start
        {
            let old_seq = Self::parse_log_ops_helper(start, mid,log_contents, log_start_addr, log_size, region_size).unwrap();
            let last_op = Self::parse_log_op(mid, log_contents, log_start_addr, log_size, region_size).unwrap();

            if mid == start {
                // Base case: old_seq is empty.
                // This case is not trivial; Verus needs some help reasoning about the end point as well
                assert(Some(Seq::<AbstractPhysicalOpLogEntry>::empty()) == Self::parse_log_ops_helper(end, end, log_contents, log_start_addr, log_size, region_size));
                return;
            }
            // first_op + middle_section == parse_log_ops_helper(start, mid, ...) by the definition of parse (which prepends earlier entries
            // onto the sequence of parsed ops)
            let first_op = Self::parse_log_op(start, log_contents, log_start_addr, log_size, region_size).unwrap();
            let next_start = start + u64::spec_size_of() * 2 + first_op.len;
            let middle_section = Self::parse_log_ops_helper(next_start, mid, log_contents, log_start_addr, log_size, region_size).unwrap();

            // associativity 
            assert((seq![first_op] + middle_section) + seq![last_op] == seq![first_op] + (middle_section + seq![last_op]));

            // recursive call to shrink the middle section; by the base case when it is empty, we can easily establish that
            // seq![last_op] == Seq::empty() + seq![last_op]
            Self::lemma_op_log_parse_equal(next_start, mid, end, log_contents, log_start_addr, log_size, region_size);  
        }

        pub open spec fn parse_log_op(
            offset: nat,
            log_contents: Seq<u8>,
            log_start_addr: nat, 
            log_size: nat,
            region_size: nat,
        ) -> Option<AbstractPhysicalOpLogEntry>
        {
            // 1. Read the absolute addr and log entry size
            let absolute_addr = u64::spec_from_bytes(extract_bytes(log_contents, offset, u64::spec_size_of()));
            let len = u64::spec_from_bytes(extract_bytes(log_contents, offset + u64::spec_size_of(), u64::spec_size_of()));
            if {
                ||| absolute_addr + len > region_size
                ||| offset + u64::spec_size_of() * 2 + len > log_contents.len()
                ||| !({
                    ||| absolute_addr < absolute_addr + len <= log_start_addr // region end before log area
                    ||| log_start_addr + log_size <= absolute_addr < absolute_addr + len // region ends after log area
                })
                ||| len == 0
                ||| log_contents.len() - u64::spec_size_of() * 2 < len
            } {
                // if the entry contains invalid values, recovery fails
                None 
            } else {
                // 2. Read the log entry contents
                let log_entry_contents = extract_bytes(log_contents, offset + u64::spec_size_of() * 2, len as nat);

                // 3. Construct the physical log entry
                let new_op = AbstractPhysicalOpLogEntry { offset, absolute_addr: absolute_addr as nat, len: len as nat, bytes: log_entry_contents };
            
                Some(new_op)
            }
        }

        pub open spec fn parse_log_ops(
            log_contents: Seq<u8>,
            log_start_addr: nat, 
            log_size: nat,
            region_size: nat,
        ) -> Option<Seq<AbstractPhysicalOpLogEntry>>
        {
            Self::parse_log_ops_helper(0, log_contents.len(),  log_contents, log_start_addr, log_size, region_size)
        }

        pub open spec fn parse_log_ops_helper(
            current_offset: nat,
            target_offset: nat,
            log_contents: Seq<u8>,
            log_start_addr: nat, 
            log_size: nat,
            region_size: nat,
        ) -> Option<Seq<AbstractPhysicalOpLogEntry>>
            decreases target_offset - current_offset
        {
            if target_offset == current_offset {
                Some(Seq::empty())
            } else {
                // parse the log entry at the current offset
                let op = Self::parse_log_op(current_offset, log_contents, log_start_addr, log_size, region_size);
                if let Some(op) = op {
                    let entry_size = u64::spec_size_of() * 2 + op.len;
                    if target_offset < current_offset + entry_size {
                        None
                    } else {
                        let seq = Self::parse_log_ops_helper(
                            current_offset + entry_size,
                            target_offset, 
                            log_contents, 
                            log_start_addr,
                            log_size,
                            region_size
                        );
                        if let Some(seq) = seq {
                            Some(seq![op] + seq)
                        } else {
                            None
                        }
                    }
                } else {
                    None
                }
            }
        }

        pub proof fn lemma_successful_log_ops_parse_implies_inv(
            current_offset: nat,
            target_offset: nat,
            log_contents: Seq<u8>,
            overall_metadata: OverallMetadata,
        )
            requires 
                Self::parse_log_ops_helper(current_offset, target_offset, log_contents, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat) is Some 
            ensures 
                ({
                    let parsed_log = Self::parse_log_ops_helper(current_offset, target_offset, log_contents, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat).unwrap();
                    AbstractPhysicalOpLogEntry::log_inv(parsed_log, overall_metadata)
                })
            decreases target_offset - current_offset
        {
            if target_offset == current_offset {
                // trivial
            } else {
                let op = Self::parse_log_op(current_offset, log_contents, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat);
                assert(op is Some); // inv holds when op can be parsed
                let entry_size = u64::spec_size_of() * 2 + op.unwrap().len;
                Self::lemma_successful_log_ops_parse_implies_inv(
                    current_offset + entry_size,
                    target_offset,
                    log_contents,
                    overall_metadata
                );
            }
        }

        pub exec fn parse_phys_op_log<Perm, PM>(
            pm_region: &WriteRestrictedPersistentMemoryRegion<Perm, PM>,
            log_bytes: Vec<u8>,
            overall_metadata: OverallMetadata
        ) -> (result: Result<Vec<PhysicalOpLogEntry>, KvError<K>>)
            where 
                Perm: CheckPermission<Seq<u8>>,
                PM: PersistentMemoryRegion,
            requires
                pm_region.inv(),
                pm_region@.no_outstanding_writes(),
                overall_metadata.log_area_addr + overall_metadata.log_area_size <= pm_region@.len() <= u64::MAX,
                overall_metadata.log_area_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
                Self::recover(pm_region@.committed(), overall_metadata) is Some,
                pm_region@.len() == overall_metadata.region_size,
                ({
                    let base_log_state = UntrustedLogImpl::recover(pm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat);
                    &&& base_log_state matches Some(base_log_state)
                    &&& log_bytes@ == extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat)
                }),
                ({
                    let base_log_state = UntrustedLogImpl::recover(pm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
                    let phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
                    let abstract_op_log = Self::parse_log_ops(phys_op_log_buffer, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat);
                    &&& abstract_op_log matches Some(abstract_log)
                    &&& 0 < abstract_log.len() <= u64::MAX
                }),
                ({
                    let recovered_log = UntrustedOpLog::<K, L>::recover(pm_region@.committed(), overall_metadata);
                    let parsed_ops = Self::parse_log_ops(log_bytes@, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat);
                    &&& recovered_log matches Some(recovered_log)
                    &&& parsed_ops matches Some(parsed_ops)
                    &&& recovered_log.physical_op_list == parsed_ops
                }),
                u64::spec_size_of() * 2 <= log_bytes.len() <= u64::MAX,
                overall_metadata.log_area_addr + overall_metadata.log_area_size <= u64::MAX
            ensures 
                match result {
                    Ok(phys_log) => {
                        ||| {
                            let abstract_op_log = UntrustedOpLog::<K, L>::recover(pm_region@.committed(), overall_metadata);
                            &&& abstract_op_log matches Some(abstract_op_log)
                            &&& phys_log.len() == 0
                            &&& abstract_op_log.physical_op_list.len() == 0
                        }
                        ||| {
                            let abstract_op_log = UntrustedOpLog::<K, L>::recover(pm_region@.committed(), overall_metadata);
                            let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                            &&& abstract_op_log matches Some(abstract_op_log)
                            &&& abstract_op_log.physical_op_list == phys_log_view
                            &&& AbstractPhysicalOpLogEntry::log_inv(phys_log_view, overall_metadata)
                        }
                    }
                    Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                    Err(KvError::LogErr { log_err }) => true, // TODO: better handling for this and PmemErr
                    Err(KvError::PmemErr { pmem_err }) => true,
                    Err(KvError::InternalError) => true,
                    Err(_) => false
                }
    {
        let log_start_addr = overall_metadata.log_area_addr;
        let log_size = overall_metadata.log_area_size;
        let region_size = overall_metadata.region_size;

        let ghost base_log_state = UntrustedLogImpl::recover(pm_region@.committed(), log_start_addr as nat, log_size as nat).unwrap();
        let ghost phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
        let ghost abstract_op_log = Self::parse_log_ops(phys_op_log_buffer, log_start_addr as nat, log_size as nat, region_size as nat).unwrap();

        let mut offset = 0;
        let mut ops = Vec::<PhysicalOpLogEntry>::new();

        proof {
            // Before the loop, we haven't parsed anything
            let phys_log_view = Seq::new(ops@.len(), |i: int| ops[i]@);
            assert(phys_log_view == Seq::<AbstractPhysicalOpLogEntry>::empty());
            assert(Some(phys_log_view) == Self::parse_log_ops_helper(0, 0, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat))
        }

        // let ghost old_log_start_addr = log_start_addr;
        // let ghost old_log_size = log_size;
        // let ghost old_region_size = region_size;
        let ghost old_overall_metadata = overall_metadata;

        while offset < log_bytes.len()
            invariant
                u64::spec_size_of() * 2 <= log_bytes.len() <= u64::MAX,
                0 < abstract_op_log.len() <= u64::MAX,
                Self::parse_log_ops(log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat) is Some,
                ({
                    let phys_log_view = Seq::new(ops@.len(), |i: int| ops[i]@);
                    &&& Self::parse_log_ops_helper(0, offset as nat, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat) matches Some(abstract_log_view)
                    &&& phys_log_view == abstract_log_view
                    &&& AbstractPhysicalOpLogEntry::log_inv(phys_log_view, overall_metadata)
                }),
                ({
                    let recovered_log = UntrustedOpLog::<K, L>::recover(pm_region@.committed(), overall_metadata);
                    let parsed_ops = Self::parse_log_ops(log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat);
                    &&& recovered_log matches Some(recovered_log)
                    &&& parsed_ops matches Some(parsed_ops)
                    &&& recovered_log.physical_op_list == parsed_ops
                }),
                log_start_addr + log_size <= u64::MAX,
                offset <= log_bytes.len(),
                old_overall_metadata == overall_metadata,
                log_start_addr == overall_metadata.log_area_addr,
                log_size == overall_metadata.log_area_size,
                region_size == overall_metadata.region_size,
        {
            broadcast use pmcopy_axioms;

            if offset > log_bytes.len() - traits_t::size_of::<u64>() * 2 {
                return Err(KvError::InternalError);
            }

            // parse the log entry
            let addr_bytes = slice_range(&log_bytes, offset, traits_t::size_of::<u64>());
            let len_bytes = slice_range(&log_bytes, offset + traits_t::size_of::<u64>(), traits_t::size_of::<u64>());
            let addr = u64_from_le_bytes(addr_bytes);
            let len = u64_from_le_bytes(len_bytes);

            // Check that the log entry is valid. 
            if {
                ||| len == 0
                ||| traits_t::size_of::<u64>() * 2 >= (u64::MAX - len) as usize
                ||| log_bytes.len() < traits_t::size_of::<u64>() * 2 + len as usize
                ||| offset > log_bytes.len() - (traits_t::size_of::<u64>() * 2 + len as usize)
                ||| addr >= u64::MAX - len
                ||| addr + len > region_size 
                ||| !({
                    ||| addr + len <= log_start_addr // region end before log area
                    ||| log_start_addr + log_size <= addr // region ends after log area
                })
            } {
                return Err(KvError::InternalError);
            }

            let entry_size = traits_t::size_of::<u64>() * 2 + len as usize;

            let bytes = slice_range_to_vec(&log_bytes, offset + traits_t::size_of::<u64>() * 2, len as usize);

            let phys_log_entry = PhysicalOpLogEntry {
                offset: offset as u64,
                absolute_addr: addr,
                len,
                bytes
            };
            ops.push(phys_log_entry);

            let ghost old_offset = offset;
            offset += entry_size;

            proof {
                let phys_log_view = Seq::new(ops@.len(), |i: int| ops[i]@);
                assert(Self::parse_log_op(old_offset as nat, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat) is Some);
                Self::lemma_op_log_parse_equal(0, old_offset as nat, offset as nat, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat);      
                
                let abstract_partial_log = Self::parse_log_ops_helper(0, offset as nat, log_bytes@, log_start_addr as nat, log_size as nat, region_size as nat);
                assert(abstract_partial_log is Some);
                let abstract_partial_log = abstract_partial_log.unwrap();
                assert(abstract_partial_log == phys_log_view);

                Self::lemma_successful_log_ops_parse_implies_inv(0, offset as nat, log_bytes@, overall_metadata);
            }
        }
        Ok(ops)
    }
    
    // Note that the op log is given the entire PM device but only deals with the log region
    pub exec fn start<Perm, PM>(
        pm_region: &WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        overall_metadata: OverallMetadata
    ) -> (result: Result<(Self, Vec<PhysicalOpLogEntry>), KvError<K>>)
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires
            pm_region.inv(),
            pm_region@.no_outstanding_writes(),
            overall_metadata.log_area_addr + overall_metadata.log_area_size <= pm_region@.len() <= u64::MAX,
            overall_metadata.log_area_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
            Self::recover(pm_region@.committed(), overall_metadata) is Some,
            pm_region@.len() == overall_metadata.region_size,
            ({
                let base_log_state = UntrustedLogImpl::recover(pm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
                let phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
                let abstract_op_log = Self::parse_log_ops(phys_op_log_buffer, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, overall_metadata.region_size as nat);
                &&& abstract_op_log matches Some(abstract_log)
                &&& 0 < abstract_log.len() <= u64::MAX
            }),
            overall_metadata.log_area_addr + overall_metadata.log_area_size <= u64::MAX,
            overall_metadata.log_area_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
        ensures
            match result {
                Ok((op_log_impl, phys_log)) => {
                    ||| {
                        let abstract_op_log = UntrustedOpLog::<K, L>::recover(pm_region@.committed(), overall_metadata);
                        &&& abstract_op_log matches Some(abstract_op_log)
                        &&& phys_log.len() == 0
                        &&& abstract_op_log.physical_op_list.len() == 0
                    }
                    ||| {
                        let abstract_op_log = UntrustedOpLog::<K, L>::recover(pm_region@.committed(), overall_metadata);
                        let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                        &&& abstract_op_log matches Some(abstract_op_log)
                        &&& abstract_op_log.physical_op_list == phys_log_view
                        &&& AbstractPhysicalOpLogEntry::log_inv(phys_log_view, overall_metadata)
                    }
                }
                Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                Err(KvError::LogErr { log_err }) => true, // TODO: better handling for this and PmemErr
                Err(KvError::PmemErr { pmem_err }) => true,
                Err(KvError::InternalError) => true,
                Err(_) => false
            }
    {
        let log_start_addr = overall_metadata.log_area_addr;
        let log_size = overall_metadata.log_area_size;

        // Start the base log
        let ghost base_log_state = UntrustedLogImpl::recover(pm_region@.committed(), log_start_addr as nat, log_size as nat).unwrap();
        let log = match UntrustedLogImpl::start(pm_region, log_start_addr, log_size, Ghost(base_log_state)) {
            Ok(log) => log,
            Err(LogErr::CRCMismatch) => return Err(KvError::CRCMismatch),
            Err(e) => return Err(KvError::LogErr { log_err: e })
        };
        let ghost op_log_state = Self::recover(pm_region@.committed(), overall_metadata);

        // Read the entire log and its CRC and check for corruption. we have to do this before we can parse the bytes.
        // Obtain the head and tail of the log so that we know the region to read to get the log contents and the CRC
        let (head, tail, capacity) = match log.get_head_tail_and_capacity(pm_region, log_start_addr, log_size) {
            Ok((head, tail, capacity)) => (head, tail, capacity),
            Err(e) => return Err(KvError::LogErr { log_err: e }),
        };

        if tail == head {
            return Ok((
                Self {
                    log,
                    overall_metadata,
                    state: Ghost(op_log_state.unwrap()),
                    current_transaction_crc: CrcDigest::new(),
                    _phantom: None
                },
                Vec::new(),
            ));
        } else if tail < traits_t::size_of::<u64>() as u128 || tail - head < traits_t::size_of::<u64>() as u128 {
            return Err(KvError::InternalError); 
        }

        let len = (tail - head) as u64 - traits_t::size_of::<u64>() as u64;
        
        let (log_bytes, log_addrs) = match log.read(pm_region, log_start_addr, log_size, head, len) {
            Ok(bytes) => bytes,
            Err(e) => return Err(KvError::LogErr { log_err: e }),
        };
        let (crc_bytes, crc_addrs) = match log.read(pm_region, log_start_addr, log_size, tail - traits_t::size_of::<u64>() as u128, traits_t::size_of::<u64>() as u64) {
            Ok(bytes) => bytes,
            Err(e) => return Err(KvError::LogErr { log_err: e }),
        };

        if !check_crc(log_bytes.as_slice(), crc_bytes.as_slice(), Ghost(pm_region@.committed()),
            Ghost(pm_region.constants().impervious_to_corruption), log_addrs, crc_addrs) 
        {
            return Err(KvError::CRCMismatch);
        }

        let phys_op_log = Self::parse_phys_op_log(pm_region, log_bytes, overall_metadata)?;

        let op_log_impl = Self {
            log,
            overall_metadata,
            state: Ghost(op_log_state.unwrap()),
            current_transaction_crc: CrcDigest::new(),
            _phantom: None
        };

        Ok((
            op_log_impl,
            phys_op_log
        ))
    }

    proof fn lemma_seqs_flatten_equal_prefix(s: Seq<Seq<u8>>)
        requires 
            s.len() >= 1
        ensures 
            ({
                let first = s[0];
                let suffix = s.drop_first();
                s.flatten() == first + suffix.flatten()
            })
        decreases s.len()
    {
        if s.len() == 1 {
            let first = s[0];
            seq![first].lemma_flatten_one_element();
        } else {
            let first = s[0];
            let prefix = s.subrange(0, s.len() - 1);
            let middle = prefix.drop_first(); 
            let suffix = s.drop_first();

            assert(prefix == seq![first] + middle);
            assert(prefix.flatten() == (seq![first] + middle).flatten());

            Self::lemma_seqs_flatten_equal_prefix(prefix);
            assert(s.flatten() == first + suffix.flatten());
        }
    }

    proof fn lemma_seqs_flatten_equal_suffix(s: Seq<Seq<u8>>)
        requires
            s.len() >= 1
        ensures 
            ({
                let last = s[s.len() - 1];
                let prefix = s.subrange(0, s.len() - 1);
                s.flatten() == prefix.flatten() + last
            })
        decreases s.len()
    {
        if s.len() == 1 {
            let last = s[0];
            assert(s == seq![last]);
            seq![last].lemma_flatten_one_element();
            assert(seq![last].flatten() == last);
        }
        else {
            let first = s[0];
            let last = s[s.len() - 1];
            let middle = s.subrange(0, s.len() - 1).drop_first();
            let suffix = s.drop_first();

            assert(middle == suffix.subrange(0, suffix.len() - 1));

            Self::lemma_seqs_flatten_equal_suffix(suffix);
            assert(suffix.flatten() == middle.flatten() + last);
            assert(first + suffix.flatten() == first + middle.flatten() + last);
        }
    }

    pub exec fn tentatively_append_log_entry<Perm, PM>(
        &mut self,
        log_wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        log_entry: PhysicalOpLogEntry,
        overall_metadata: OverallMetadata,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), KvError<K>>)
        where 
            Perm: CheckPermission<Seq<u8>>,
            PM: PersistentMemoryRegion,
        requires 
            old(self).inv(*old(log_wrpm)),
            overall_metadata.log_area_addr == old(self).log_start_addr(),
            overall_metadata.log_area_size == old(self).log_size(),
            old(self).log_entry_valid(old(log_wrpm)@, log_entry@),
            !old(self)@.op_list_committed,
            Self::parse_log_ops(old(self).base_log_view().pending, old(self).log_start_addr() as nat, 
                old(self).log_size() as nat, old(self).overall_metadata().region_size as nat) is Some,
            // TODO: it would be better to only refer to op log state in this precondition,
            // but the op log state is more abstract than the base log state, and we need to be 
            // specific about the legal base log states here. If this becomes an issue, maybe we could
            // keep more info about the base log state in the op log so that we can refer to it more easily here
            forall |s| #[trigger] perm.check_permission(s) <==>
                UntrustedLogImpl::recover(s, old(self).log_start_addr() as nat, old(self).log_size() as nat) == Some(old(self).base_log_view().drop_pending_appends()),
        ensures 
            self.inv(*log_wrpm),
            match result {
                Ok(()) => {
                    self@ == old(self)@.tentatively_append_log_entry(log_entry@)
                }
                Err(KvError::LogErr { log_err: e }) => true, // TODO
                Err(_) => true // TODO
            }
    {
        // this assert is sufficient to hit the triggers we need to prove that the log entries
        // are all valid after appending the new one
        assert(forall |i: int| 0 <= i < self@.physical_op_list.len() ==> {
            let op = #[trigger] self@.physical_op_list[i];
            self.log_entry_valid(log_wrpm@, op)
        });

        let log_entry_header = PhysicalLogEntryHeader {
            absolute_addr: log_entry.absolute_addr,
            len: log_entry.bytes.len() as u64
        };

        let ghost old_digest = self.current_transaction_crc.bytes_in_digest();
        let ghost old_pending = self.log@.pending;

        let result = self.log.tentatively_append(
            log_wrpm,
            self.overall_metadata.log_area_addr, 
            self.overall_metadata.log_area_size, 
            log_entry_header.as_byte_slice(),
            Tracked(perm)
        );
        match result {
            Ok(_) => {}
            Err(e) => {
                assert(old(self)@.physical_op_list == self@.physical_op_list);
                return Err(KvError::LogErr { log_err: e });
            }
        }
        self.current_transaction_crc.write_bytes(log_entry_header.as_byte_slice());

        proof {
            // TODO: Refactor into a proof
            // This proves that the CRC digest bytes and log pending bytes are the same
            let current_digest = self.current_transaction_crc.bytes_in_digest();
            let bytes = log_entry_header.spec_to_bytes();
            assert(current_digest == old_digest.push(bytes));
            assert(self.log@.pending == old_pending + bytes);
            assert(old_digest.flatten() == old_pending);
            Self::lemma_seqs_flatten_equal_suffix(current_digest);
            assert(current_digest[current_digest.len() - 1] == bytes);
            assert(current_digest.subrange(0, current_digest.len() - 1) == old_digest);
            assert(current_digest.flatten() == old_digest.flatten() + bytes);
        }
        
        assert(self.current_transaction_crc.bytes_in_digest().flatten() == self.log@.pending);

        let ghost old_digest = self.current_transaction_crc.bytes_in_digest();
        let ghost old_pending = self.log@.pending;

        let bytes = log_entry.bytes.as_slice();
        let result = self.log.tentatively_append(
            log_wrpm, 
            self.overall_metadata.log_area_addr, 
            self.overall_metadata.log_area_size, 
            bytes,
            Tracked(perm)
        );
        match result {
            Ok(_) => {}
            Err(e) => {
                assert(old(self)@.physical_op_list == self@.physical_op_list);
                assert(self.log@.pending == old(self).log@.pending + log_entry_header.spec_to_bytes());
                assume(false); // TODO TODO TODO
                // WE HAVE TO PROVE THIS -- IT WILL PROBABLY BE TRICKY
                assert(Self::parse_log_ops(self.log@.pending, self.overall_metadata.log_area_addr as nat, 
                    self.overall_metadata.log_area_size as nat, self.overall_metadata.region_size as nat) is None);
                
                return Err(KvError::LogErr { log_err: e });
            }
        }
        // update the op log's CRC digest
        self.current_transaction_crc.write_bytes(bytes);

        proof {
            let current_digest = self.current_transaction_crc.bytes_in_digest();
            let bytes = bytes@;
            assert(current_digest == old_digest.push(bytes));
            assert(self.log@.pending == old_pending + bytes);
            assert(old_digest.flatten() == old_pending);
            Self::lemma_seqs_flatten_equal_suffix(current_digest);
            assert(current_digest[current_digest.len() - 1] == bytes);
            assert(current_digest.subrange(0, current_digest.len() - 1) == old_digest);
            assert(current_digest.flatten() == old_digest.flatten() + bytes);
        }

        // update the ghost state to reflect the new entry
        let ghost new_state = self.state@.tentatively_append_log_entry(log_entry@);
        self.state = Ghost(new_state);

        proof {
            // We need to prove that we maintain the invariatn that parsing the pending log bytes
            // gives us the current abstract op log
            let old_pending_bytes = old(self).log@.pending;
            let new_pending_bytes = self.log@.pending;

            assert(new_pending_bytes == old_pending_bytes + log_entry_header.spec_to_bytes() + bytes@);

            let old_log_ops = Self::parse_log_ops(old_pending_bytes, self.overall_metadata.log_area_addr as nat, 
                self.overall_metadata.log_area_size as nat, self.overall_metadata.region_size as nat);
            let new_log_ops = Self::parse_log_ops(new_pending_bytes, self.overall_metadata.log_area_addr as nat, 
                self.overall_metadata.log_area_size as nat, self.overall_metadata.region_size as nat);

            // TODO: figure out how to use the existing parsing lemma, or write a new one,
            // to prove that appending a new valid op performs the operation we want
        
            assert(old_log_ops is Some);
            assert(new_log_ops is Some);

            assert(new_log_ops.unwrap() == self@.physical_op_list);
        }
        
        Ok(())
    }

        pub exec fn commit_log<Perm, PM>(
            &mut self, 
            log_wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
            Tracked(perm): Tracked<&Perm>,
        ) -> (result: Result<(), KvError<K>>)
            where 
                Perm: CheckPermission<Seq<u8>>,
                PM: PersistentMemoryRegion,
            requires 
                old(self).inv(*old(log_wrpm)),
                old(self)@.physical_op_list.len() > 0,
                !old(self)@.op_list_committed,
                // TODO: like with tentatively_append above, it might be better to find a way to 
                // express this precondition on the level of the op log rather than the base log
                forall |s| #[trigger] perm.check_permission(s) <==> {
                    ||| Self::recover(s, old(self).overall_metadata()) == Some(AbstractOpLogState::initialize())
                    ||| Self::recover(s, old(self).overall_metadata()) == Some(old(self)@.commit_op_log())
                    // ||| UntrustedLogImpl::recover(s, old(self).log_start_addr() as nat, old(self).log_size() as nat) == 
                    //         Some(old(self).base_log_view().drop_pending_appends())
                    // ||| UntrustedLogImpl::recover(s, old(self).log_start_addr() as nat, old(self).log_size() as nat) == 
                    //         Some(old(self).base_log_view().commit().drop_pending_appends())
                }
            ensures 
                self.inv(*log_wrpm),
                match result {
                    Ok(()) => {
                        self@ == old(self)@.commit_op_log()
                    }
                    Err(_) => true // TODO
                }
        {
            let transaction_crc = self.current_transaction_crc.sum64();
            let bytes = transaction_crc.as_byte_slice();

            proof {
                broadcast use pmcopy_axioms;
                // All base log crash states that result in self.base_log_view.drop_pending_appends() will result in 
                // an op log state that is allowed by `perm`. The base log's `tentatively_append` requires that perm
                // allow base log states that recover to self.base_log_view.drop_pending_appends(), so this 
                // assertion tells us that all crash states considered legal in the base log's `tentatively_append` 
                // also recover to a legal op log state
                assert forall |s| UntrustedLogImpl::recover(s, self.log_start_addr() as nat, self.log_size() as nat) == 
                        Some(self.base_log_view().drop_pending_appends())
                    implies #[trigger] Self::recover(s, self.overall_metadata()) == Some(AbstractOpLogState::initialize()) 
                by {
                    let base_log_recovery_state = UntrustedLogImpl::recover(s, self.log_start_addr() as nat, self.log_size() as nat);
                    assert(base_log_recovery_state is Some);
                    assert(base_log_recovery_state.unwrap().log.len() == 0);
                }
                assert(bytes.len() > 0);
            }

            match self.log.tentatively_append(log_wrpm, self.overall_metadata.log_area_addr, self.overall_metadata.log_area_size, bytes, Tracked(perm)) {
                Ok(_) => {}
                Err(e) => {
                    assert(old(self)@.physical_op_list == self@.physical_op_list);
                    return Err(KvError::LogErr { log_err: e });
                }
            }

            proof {
                assert forall |s| UntrustedLogImpl::recover(s, self.log_start_addr() as nat, self.log_size() as nat) == 
                        Some(self.base_log_view().drop_pending_appends())
                    implies #[trigger] Self::recover(s, self.overall_metadata()) == Some(AbstractOpLogState::initialize()) 
                by {
                    let base_log_recovery_state = UntrustedLogImpl::recover(s, self.log_start_addr() as nat, self.log_size() as nat);
                    assert(base_log_recovery_state is Some);
                    assert(base_log_recovery_state.unwrap().log.len() == 0);
                }

                assert forall |s| UntrustedLogImpl::recover(s, self.log_start_addr() as nat, self.log_size() as nat) == 
                        Some(self.base_log_view().commit().drop_pending_appends())
                    implies #[trigger] Self::recover(s, self.overall_metadata()) == Some(self@.commit_op_log()) 
                by {
                    let base_log_recovery_state = UntrustedLogImpl::recover(s, self.log_start_addr() as nat, self.log_size() as nat);
                    assert(base_log_recovery_state == Some(self.base_log_view().commit().drop_pending_appends()));
                    
                    assert(self.base_log_view().pending.len() > 0);
                    assert(base_log_recovery_state.unwrap().log.len() > 0);
                    assert(self.base_log_view().commit().pending.len() == 0); // no pending appends to drop

                    // so we need to establish what base_log_view().commit() is
                    assume(false);
                }
            }

            
            match self.log.commit(log_wrpm, self.overall_metadata.log_area_addr, self.overall_metadata.log_area_size, Tracked(perm)) {
                Ok(_) => {}
                Err(e) => return Err(KvError::LogErr { log_err: e })
            }
            assume(false);
            Ok(())
        }

        // pub exec fn clear_log<PM>(
        //     &mut self, 
        //     log_wrpm: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PM>,
        //     log_id: u128,
        //     Tracked(perm): Tracked<&TrustedPermission>,
        // ) -> (result: Result<(), KvError<K>>)
        //     where 
        //         PM: PersistentMemoryRegion,
        //     requires 
        //         // TODO
        //     ensures 
        //         // TODO
        // {
        //     assume(false);
        //     // look up the tail of the log, then advance the head to that point
        //     let (head, tail, capacity) = match self.log.get_head_tail_and_capacity(log_wrpm, Ghost(log_id)) {
        //         Ok((head, tail, capacity)) => (head, tail, capacity),
        //         Err(e) => return Err(KvError::LogErr { log_err: e })
        //     };
        //     match self.log.advance_head(log_wrpm, tail, Ghost(log_id), Tracked(perm)) {
        //         Ok(()) => Ok(()),
        //         Err(e) => Err(KvError::LogErr { log_err: e })
        //     }
        // }


    }
}
