//! This file contains lemmas and utility executable functions about
//! persistent memory regions.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use crate::pmem::crc_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::crc_t::*;
use crate::pmem::subregion_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {

    broadcast use pmcopy_axioms;

    // This lemma establishes that if there are no outstanding writes
    // to a particular location in memory, then there's only one
    // possibility for how the byte at that address can crash: it will
    // always crash into its committed state.
    pub proof fn lemma_if_no_outstanding_writes_at_addr_then_persistent_memory_view_can_only_crash_as_committed(
        pm_region_view: PersistentMemoryRegionView,
        addr: int,
    )
        requires
            0 <= addr < pm_region_view.len(),
            pm_region_view.state[addr].outstanding_write.is_none(),
        ensures
            forall |s| pm_region_view.can_crash_as(s) ==> #[trigger] s[addr] == pm_region_view.committed()[addr]
    {
        assert forall |s| pm_region_view.can_crash_as(s) implies #[trigger] s[addr] == pm_region_view.committed()[addr] by {
            let chunk = addr / const_persistence_chunk_size();
            // There are two cases to consider. Each is fairly trivial
            // for Z3, once we cue it to consider the two cases
            // separately with the following `if`.
            if pm_region_view.chunk_corresponds_after_flush(chunk, s) {
            }
            else {
            }
        }
    }

    // This lemma establishes that any persistent memory byte that has
    // no outstanding writes has one possible crash state, which is
    // the same as its committed state.
    pub proof fn lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(
        pm_region_view: PersistentMemoryRegionView,
    )
        ensures
            forall |s, addr: int| {
                &&& pm_region_view.can_crash_as(s)
                &&& 0 <= addr < s.len()
                &&& pm_region_view.state[addr].outstanding_write.is_none()
            } ==> #[trigger] s[addr] == pm_region_view.committed()[addr]
    {
        assert forall |s, addr: int| {
                   &&& pm_region_view.can_crash_as(s)
                   &&& 0 <= addr < s.len()
                   &&& pm_region_view.state[addr].outstanding_write.is_none()
               } implies #[trigger] s[addr] == pm_region_view.committed()[addr] by {
            lemma_if_no_outstanding_writes_at_addr_then_persistent_memory_view_can_only_crash_as_committed(
                pm_region_view, addr);
        }
    }

    // This lemma establishes that if there are no outstanding writes
    // anywhere in a persistent memory region's view, then it can only
    // crash in one state, which is the same as its committed state.
    pub proof fn lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(
        pm_region_view: PersistentMemoryRegionView
    )
        requires
            pm_region_view.no_outstanding_writes()
        ensures
            forall |s| pm_region_view.can_crash_as(s) ==> s == pm_region_view.committed()
    {
        lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(pm_region_view);
        assert (forall |s| pm_region_view.can_crash_as(s) ==> s =~= pm_region_view.committed());
    }

    // This lemma establishes that if there are no outstanding writes
    // anywhere in the view of a collection of persistent memory
    // regions, then the collection can only crash in one state, which
    // is the same as its committed state.
    pub proof fn lemma_if_no_outstanding_writes_then_persistent_memory_regions_view_can_only_crash_as_committed(
        pm_regions_view: PersistentMemoryRegionsView
    )
        requires
            pm_regions_view.no_outstanding_writes()
        ensures
            forall |s| pm_regions_view.can_crash_as(s) ==> s == pm_regions_view.committed()
    {
        assert forall |s| pm_regions_view.can_crash_as(s) implies s == pm_regions_view.committed() by {
            assert forall |i| 0 <= i < pm_regions_view.len() implies s[i] == #[trigger] pm_regions_view[i].committed() by {
                lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(
                    pm_regions_view[i]);
            }
            assert (s =~= pm_regions_view.committed());
        }
    }

    // This lemma establishes that if a persistent memory region has
    // no outstanding writes, then a flush of them does nothing.
    pub proof fn lemma_if_no_outstanding_writes_to_region_then_flush_is_idempotent(
        region_view: PersistentMemoryRegionView,
    )
        requires
            region_view.no_outstanding_writes(),
        ensures
            region_view.flush() == region_view,
    {
        assert(region_view.flush() =~= region_view);
    }

    // This lemma establishes that if a collection of persistent
    // memory regions has no outstanding writes anywhere, then a flush
    // of them does nothing.
    pub proof fn lemma_if_no_outstanding_writes_then_flush_is_idempotent(
        regions_view: PersistentMemoryRegionsView,
    )
        requires
            regions_view.no_outstanding_writes(),
        ensures
            regions_view.flush() == regions_view,
    {
        assert(regions_view.flush().len() == regions_view.len());
        assert forall |i| 0 <= i < regions_view.len() implies
               #[trigger] regions_view.flush().regions[i] == regions_view.regions[i] by {
            assert(regions_view[i].no_outstanding_writes());
            lemma_if_no_outstanding_writes_to_region_then_flush_is_idempotent(regions_view.regions[i]);
        }
        assert(regions_view.flush() =~= regions_view);
    }

    // This is an auto lemma for lemma_if_no_outstanding_writes_then_flush_is_idempotent.
    pub proof fn lemma_auto_if_no_outstanding_writes_then_flush_is_idempotent()
        ensures
            forall |r: PersistentMemoryRegionsView| r.no_outstanding_writes() ==> r.flush() == r
    {
        assert forall |r: PersistentMemoryRegionsView| r.no_outstanding_writes() implies r.flush() == r by {
            lemma_if_no_outstanding_writes_then_flush_is_idempotent(r);
        };
    }

    // This lemma establishes that it's possible to crash into the
    // committed state.
    pub proof fn lemma_persistent_memory_view_can_crash_as_committed(pm_region_view: PersistentMemoryRegionView)
        ensures
            pm_region_view.can_crash_as(pm_region_view.committed()),
    {
    }

    // This lemma establishes that it's possible to crash into the
    // fully-flushed state.
    pub proof fn lemma_persistent_memory_view_can_crash_as_flushed(pm_region_view: PersistentMemoryRegionView)
        ensures
            pm_region_view.can_crash_as(pm_region_view.flush().committed()),
    {
    }

    // This executable function returns a vector containing the sizes
    // of the regions in the given collection of persistent memory
    // regions.
    pub fn get_region_sizes<PMRegions: PersistentMemoryRegions>(pm_regions: &PMRegions) -> (result: Vec<u64>)
        requires
            pm_regions.inv()
        ensures
            result@.len() == pm_regions@.len(),
            forall |i: int| 0 <= i < pm_regions@.len() ==> result@[i] == #[trigger] pm_regions@[i].len()
    {
        let mut result: Vec<u64> = Vec::<u64>::new();
        for which_region in iter: 0..pm_regions.get_num_regions()
            invariant
                iter.end == pm_regions@.len(),
                pm_regions.inv(),
                result@.len() == which_region,
                forall |i: int| 0 <= i < which_region ==> result@[i] == #[trigger] pm_regions@[i].len(),
        {
            result.push(pm_regions.get_region_size(which_region));
        }
        result
    }

    // This executable function checks whether the given CRC read from
    // persistent memory is the actual CRC of the given bytes read
    // from persistent memory. It returns a boolean indicating whether
    // the check succeeds.
    //
    // It guarantees that, if the CRC last written to memory really
    // was the CRC of the data last written to memory, then:
    //
    // 1) If the function returns `true`, then the data read from
    // memory (`data_c`) constitute an uncorrupted copy of the correct
    // bytes last written to memory.
    //
    // 2) If the function returns `false`, then the persistent memory
    // region collection the data and CRC were read from are not
    // impervious to corruption.
    //
    // Parameters:
    //
    // `data_c` -- the possibly corrupted data read from memory
    //
    // `crc_c` -- the possibly corrupted CRC read from memory
    //
    // `mem` (ghost) -- the true contents of the memory that was read from
    //
    // `impervious_to_corruption` (ghost) -- whether that memory is
    // impervious to corruption
    //
    // `data_addr` (ghost) -- where the data were read from in memory
    //
    // `data_length` (ghost) -- the length of the data read from memory
    //
    // `crc_addr` (ghost) -- where the CRC was read from in memory
    pub fn check_crc(
        data_c: &[u8],
        crc_c: &[u8],
        Ghost(mem): Ghost<Seq<u8>>,
        Ghost(impervious_to_corruption): Ghost<bool>,
        Ghost(data_addrs): Ghost<Seq<int>>,
        Ghost(crc_addrs): Ghost<Seq<int>>,
    ) -> (b: bool)
        requires
            data_addrs.len() <= mem.len(),
            crc_addrs.len() <= mem.len(),
            crc_c@.len() == u64::spec_size_of(),
            all_elements_unique(data_addrs),
            all_elements_unique(crc_addrs),
            ({
                let true_data_bytes = Seq::new(data_addrs.len(), |i: int| mem[data_addrs[i] as int]);
                let true_crc_bytes = Seq::new(crc_addrs.len(), |i: int| mem[crc_addrs[i]]);
                &&& true_crc_bytes == spec_crc_bytes(true_data_bytes)
                &&& if impervious_to_corruption {
                        &&& data_c@ == true_data_bytes
                        &&& crc_c@ == true_crc_bytes
                    }
                    else {
                        &&& maybe_corrupted(data_c@, true_data_bytes, data_addrs)
                        &&& maybe_corrupted(crc_c@, true_crc_bytes, crc_addrs)
                    }
            })
        ensures
            ({
                let true_data_bytes = Seq::new(data_addrs.len(), |i: int| mem[data_addrs[i] as int]);
                let true_crc_bytes = Seq::new(crc_addrs.len(), |i: int| mem[crc_addrs[i]]);
                if b {
                    &&& data_c@ == true_data_bytes
                    &&& crc_c@ == true_crc_bytes
                }
                else {
                    !impervious_to_corruption
                }
            })
    {
        // Compute a CRC for the bytes we read.
        let computed_crc = calculate_crc_bytes(data_c);

        // Check whether the CRCs match. This is done in an external body function so that we can convert the maybe-corrupted
        // CRC to a u64 for comparison to the computed CRC.
        let crcs_match = compare_crcs(crc_c, computed_crc);

        proof {
            let true_data_bytes = Seq::new(data_addrs.len(), |i: int| mem[data_addrs[i] as int]);
            let true_crc_bytes = Seq::new(crc_addrs.len(), |i: int| mem[crc_addrs[i]]);

            // We may need to invoke `axiom_bytes_uncorrupted` to justify that since the CRCs match,
            // we can conclude that the data matches as well. That axiom only applies in the case
            // when all three of the following conditions hold: (1) the last-written CRC really is
            // the CRC of the last-written data; (2) the persistent memory regions aren't impervious
            // to corruption; and (3) the CRC read from disk matches the computed CRC. If any of
            // these three is false, we can't invoke `axiom_bytes_uncorrupted`, but that's OK
            // because we don't need it. #1 is a requirement to call this lemma. If #2 is false,
            // then no corruption has happened. If #3 is false, then we've detected corruption.
            if {
                &&& !impervious_to_corruption
                &&& crcs_match
            } {
                axiom_bytes_uncorrupted2(data_c@, true_data_bytes, data_addrs, crc_c@, true_crc_bytes, crc_addrs);
            }
        }
        crcs_match
    }

    pub exec fn check_crc_for_two_reads(
        data1_c: &[u8],
        data2_c: &[u8],
        crc_c: &[u8],
        Ghost(mem): Ghost<Seq<u8>>,
        Ghost(impervious_to_corruption): Ghost<bool>,
        Ghost(data1_addrs): Ghost<Seq<int>>,
        Ghost(data2_addrs): Ghost<Seq<int>>,
        Ghost(crc_addrs): Ghost<Seq<int>>,
    ) -> (b: bool)
        requires
            data1_addrs.len() + data2_addrs.len() <= mem.len(),
            crc_addrs.len() <= mem.len(),
            crc_c@.len() == u64::spec_size_of(),
            all_elements_unique(data1_addrs + data2_addrs),
            all_elements_unique(crc_addrs),
            ({
                let true_data1_bytes = Seq::new(data1_addrs.len(), |i: int| mem[data1_addrs[i] as int]);
                let true_data2_bytes = Seq::new(data2_addrs.len(), |i: int| mem[data2_addrs[i] as int]);
                let true_crc_bytes = Seq::new(crc_addrs.len(), |i: int| mem[crc_addrs[i]]);
                &&& true_crc_bytes == spec_crc_bytes(true_data1_bytes + true_data2_bytes)
                &&& if impervious_to_corruption {
                        &&& data1_c@ == true_data1_bytes
                        &&& data2_c@ == true_data2_bytes
                        &&& crc_c@ == true_crc_bytes
                    }
                    else {
                        &&& maybe_corrupted(data1_c@, true_data1_bytes, data1_addrs)
                        &&& maybe_corrupted(data2_c@, true_data2_bytes, data2_addrs)
                        &&& maybe_corrupted(crc_c@, true_crc_bytes, crc_addrs)
                    }
            })
        ensures
            ({
                let true_data1_bytes = Seq::new(data1_addrs.len(), |i: int| mem[data1_addrs[i] as int]);
                let true_data2_bytes = Seq::new(data2_addrs.len(), |i: int| mem[data2_addrs[i] as int]);
                let true_crc_bytes = Seq::new(crc_addrs.len(), |i: int| mem[crc_addrs[i]]);
                if b {
                    &&& data1_c@ == true_data1_bytes
                    &&& data2_c@ == true_data2_bytes
                    &&& crc_c@ == true_crc_bytes
                }
                else {
                    !impervious_to_corruption
                }
            })
    {
        // calculate the CRC using a digest including both data1_c and data2_c
        let mut digest = CrcDigest::new();
        digest.write_bytes(data1_c);
        digest.write_bytes(data2_c);
        proof {
            reveal_with_fuel(Seq::flatten, 3);
            assert(digest.bytes_in_digest().flatten() =~= data1_c@ + data2_c@);
        }
        let computed_crc = digest.sum64();

        assert(computed_crc == spec_crc_u64(data1_c@ + data2_c@));

        // Check whether the CRCs match. This is done in an external body function so that we can convert the maybe-corrupted
        // CRC to a u64 for comparison to the computed CRC.
        let crcs_match = compare_crcs(crc_c, computed_crc);

        proof {
            let true_data1_bytes = Seq::new(data1_addrs.len(), |i: int| mem[data1_addrs[i] as int]);
            let true_data2_bytes = Seq::new(data2_addrs.len(), |i: int| mem[data2_addrs[i] as int]);
            let true_crc_bytes = Seq::new(crc_addrs.len(), |i: int| mem[crc_addrs[i]]);

            // We may need to invoke `axiom_bytes_uncorrupted` to justify that since the CRCs match,
            // we can conclude that the data matches as well. That axiom only applies in the case
            // when all three of the following conditions hold: (1) the last-written CRC really is
            // the CRC of the last-written data; (2) the persistent memory regions aren't impervious
            // to corruption; and (3) the CRC read from disk matches the computed CRC. If any of
            // these three is false, we can't invoke `axiom_bytes_uncorrupted`, but that's OK
            // because we don't need it. #1 is a precondition for calling this lemma. If #2 is false,
            // then no corruption has happened. If #3 is false, then we've detected corruption.
            if {
                &&& true_crc_bytes == spec_crc_bytes(true_data1_bytes + true_data2_bytes)
                &&& !impervious_to_corruption
                &&& crcs_match
            } {
                let data_c = data1_c@ + data2_c@;
                let true_data = true_data1_bytes + true_data2_bytes;
                axiom_bytes_uncorrupted2(data_c, true_data, data1_addrs + data2_addrs, 
                    crc_c@, true_crc_bytes, crc_addrs);
                assert(extract_bytes(data_c, 0, data1_c@.len()) == data1_c@);
                assert(extract_bytes(data_c, data1_c@.len(), data2_c@.len()) == data2_c@);
                assert(data1_c@ == true_data1_bytes);
                assert(data2_c@ == true_data2_bytes);
            }
        }
        crcs_match
    }

    pub exec fn check_crc_for_two_reads_in_subregion<PM>(
        data1_c: &[u8],
        data2_c: &[u8],
        crc_c: &[u8],
        // Ghost(mem): Ghost<Seq<u8>>,
        subregion: &PersistentMemorySubregion,
        pm_region: &PM,
        Ghost(impervious_to_corruption): Ghost<bool>,
        Ghost(relative_data1_addrs): Ghost<Seq<int>>,
        Ghost(relative_data2_addrs): Ghost<Seq<int>>,
        Ghost(relative_crc_addrs): Ghost<Seq<int>>,
    ) -> (b: bool)
        where 
            PM: PersistentMemoryRegion
        requires
            relative_data1_addrs.len() + relative_data2_addrs.len() <= subregion.view(pm_region).len(),
            relative_crc_addrs.len() <= subregion.view(pm_region).len(),
            forall |i: int| 0 <= i < relative_data1_addrs.len() ==> relative_data1_addrs[i] <= subregion.view(pm_region).len(),
            forall |i: int| 0 <= i < relative_data2_addrs.len() ==> relative_data2_addrs[i] <= subregion.view(pm_region).len(),
            forall |i: int| 0 <= i < relative_crc_addrs.len() ==> relative_crc_addrs[i] <= subregion.view(pm_region).len(),
            crc_c@.len() == u64::spec_size_of(),
            all_elements_unique(relative_data1_addrs + relative_data2_addrs),
            all_elements_unique(relative_crc_addrs),
            ({
                let absolute_data1_addrs = Seq::new(relative_data1_addrs.len(), |i: int| subregion.start() + relative_data1_addrs[i]);
                let absolute_data2_addrs = Seq::new(relative_data2_addrs.len(), |i: int| subregion.start() + relative_data2_addrs[i]);
                let absolute_crc_addrs = Seq::new(relative_crc_addrs.len(), |i: int| subregion.start() + relative_crc_addrs[i]);
                &&& all_elements_unique(absolute_data1_addrs + absolute_data2_addrs)
                &&& all_elements_unique(absolute_crc_addrs)
            }),
            ({
                let true_data1_bytes = Seq::new(relative_data1_addrs.len(), |i: int| subregion.view(pm_region).committed()[relative_data1_addrs[i] as int]);
                let true_data2_bytes = Seq::new(relative_data2_addrs.len(), |i: int| subregion.view(pm_region).committed()[relative_data2_addrs[i] as int]);
                let true_crc_bytes = Seq::new(relative_crc_addrs.len(), |i: int| subregion.view(pm_region).committed()[relative_crc_addrs[i]]);
                &&& true_crc_bytes == spec_crc_bytes(true_data1_bytes + true_data2_bytes)
                &&& if impervious_to_corruption {
                        &&& data1_c@ == true_data1_bytes
                        &&& data2_c@ == true_data2_bytes
                        &&& crc_c@ == true_crc_bytes
                    }
                    else {
                        &&& subregion.maybe_corrupted_relative(data1_c@, true_data1_bytes, relative_data1_addrs)
                        &&& subregion.maybe_corrupted_relative(data2_c@, true_data2_bytes, relative_data2_addrs)
                        &&& subregion.maybe_corrupted_relative(crc_c@, true_crc_bytes, relative_crc_addrs)
                    }
            })
        ensures
            ({
                let true_data1_bytes = Seq::new(relative_data1_addrs.len(), |i: int| subregion.view(pm_region).committed()[relative_data1_addrs[i] as int]);
                let true_data2_bytes = Seq::new(relative_data2_addrs.len(), |i: int| subregion.view(pm_region).committed()[relative_data2_addrs[i] as int]);
                let true_crc_bytes = Seq::new(relative_crc_addrs.len(), |i: int| subregion.view(pm_region).committed()[relative_crc_addrs[i]]);
                if b {
                    &&& data1_c@ == true_data1_bytes
                    &&& data2_c@ == true_data2_bytes
                    &&& crc_c@ == true_crc_bytes
                }
                else {
                    !impervious_to_corruption
                }
            })
    {
        // calculate the CRC using a digest including both data1_c and data2_c
        let mut digest = CrcDigest::new();
        digest.write_bytes(data1_c);
        digest.write_bytes(data2_c);
        proof {
            reveal_with_fuel(Seq::flatten, 3);
            assert(digest.bytes_in_digest().flatten() =~= data1_c@ + data2_c@);
        }
        let computed_crc = digest.sum64();

        assert(computed_crc == spec_crc_u64(data1_c@ + data2_c@));

        // Check whether the CRCs match. This is done in an external body function so that we can convert the maybe-corrupted
        // CRC to a u64 for comparison to the computed CRC.
        let crcs_match = compare_crcs(crc_c, computed_crc);

        proof {
            let true_data1_bytes = Seq::new(relative_data1_addrs.len(), |i: int| subregion.view(pm_region).committed()[relative_data1_addrs[i] as int]);
            let true_data2_bytes = Seq::new(relative_data2_addrs.len(), |i: int| subregion.view(pm_region).committed()[relative_data2_addrs[i] as int]);
            let true_crc_bytes = Seq::new(relative_crc_addrs.len(), |i: int| subregion.view(pm_region).committed()[relative_crc_addrs[i]]);

            // We may need to invoke `axiom_bytes_uncorrupted` to justify that since the CRCs match,
            // we can conclude that the data matches as well. That axiom only applies in the case
            // when all three of the following conditions hold: (1) the last-written CRC really is
            // the CRC of the last-written data; (2) the persistent memory regions aren't impervious
            // to corruption; and (3) the CRC read from disk matches the computed CRC. If any of
            // these three is false, we can't invoke `axiom_bytes_uncorrupted`, but that's OK
            // because we don't need it. If #1 is false, then this lemma isn't expected to prove
            // anything. If #2 is false, then no corruption has happened. If #3 is false, then we've
            // detected corruption.
            if {
                &&& true_crc_bytes == spec_crc_bytes(true_data1_bytes + true_data2_bytes)
                &&& !impervious_to_corruption
                &&& crcs_match
            } {
                let data_c = data1_c@ + data2_c@;
                let true_data = true_data1_bytes + true_data2_bytes;
                let absolute_data1_addrs = Seq::new(relative_data1_addrs.len(), |i: int| subregion.start() + relative_data1_addrs[i]);
                let absolute_data2_addrs = Seq::new(relative_data2_addrs.len(), |i: int| subregion.start() + relative_data2_addrs[i]);
                let absolute_crc_addrs = Seq::new(relative_crc_addrs.len(), |i: int| subregion.start() + relative_crc_addrs[i]);
                axiom_bytes_uncorrupted2(data_c, true_data, absolute_data1_addrs + absolute_data2_addrs, 
                    crc_c@, true_crc_bytes, absolute_crc_addrs);
                assert(extract_bytes(data_c, 0, data1_c@.len()) == data1_c@);
                assert(extract_bytes(data_c, data1_c@.len(), data2_c@.len()) == data2_c@);
                assert(data1_c@ == true_data1_bytes);
                assert(data2_c@ == true_data2_bytes);
            }
        }
        crcs_match
    }



    // This function converts the given encoded CDB read from persistent
    // memory into a boolean. It checks for corruption as it does so. It
    // guarantees that if it returns `Some` then there was no corruption,
    // and that if it returns `None` then the memory isn't impervious to
    // corruption.
    //
    // Parameters:
    //
    // `cdb_c` -- the possibly corrupted encoded CDB read from memory
    //
    // `mem` (ghost) -- the true contents of the memory that was read from
    //
    // `impervious_to_corruption` (ghost) -- whether that memory is
    // impervious to corruption
    //
    // `cdb_addr` (ghost) -- where the CDB was read from in memory
    //
    // Return value:
    //
    // `Some(b)` -- the encoded CDB is uncorrupted and encodes the boolean
    // `b`
    //
    // `None` -- corruption was detected, so the persistent memory regions
    // can't be impervious to corruption
    // 
    // We assume here that the CDB is stored contiguously, which will always be true
    // because we don't write CDBs to the log. If we do ever attempt to use this function
    // to check a CDB that was written to the log, verification will fail because the
    // addresses don't work out.
    pub fn check_cdb(
        cdb_c: MaybeCorruptedBytes<u64>,
        Ghost(mem): Ghost<Seq<u8>>,
        Ghost(impervious_to_corruption): Ghost<bool>,
        Ghost(cdb_addrs): Ghost<Seq<int>>,
    ) -> (result: Option<bool>)
        requires
            forall |i: int| 0 <= i < cdb_addrs.len() ==> cdb_addrs[i] <= mem.len(),
            all_elements_unique(cdb_addrs),
            ({
                let true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem[cdb_addrs[i]]);
                let true_cdb = u64::spec_from_bytes(true_cdb_bytes);
                &&& u64::bytes_parseable(true_cdb_bytes)
                &&& true_cdb == CDB_FALSE || true_cdb == CDB_TRUE
                &&& if impervious_to_corruption { cdb_c@ == true_cdb_bytes }
                        else { maybe_corrupted(cdb_c@, true_cdb_bytes, cdb_addrs) }
            })
        ensures
            ({
                let true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem[cdb_addrs[i]]);
                let true_cdb = u64::spec_from_bytes(true_cdb_bytes);
                match result {
                    Some(b) => if b { true_cdb == CDB_TRUE }
                               else { true_cdb == CDB_FALSE },
                    None => !impervious_to_corruption,
                }
            })
    {
        let ghost true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem[cdb_addrs[i]]);
        proof {
            // We may need to invoke the axiom
            // `axiom_corruption_detecting_boolean` to justify concluding
            // that, if we read `CDB_FALSE` or `CDB_TRUE`, it can't have
            // been corrupted.
            if !impervious_to_corruption && (cdb_c@ == CDB_FALSE.spec_to_bytes() || cdb_c@ == CDB_TRUE.spec_to_bytes()) {
                axiom_corruption_detecting_boolean(cdb_c@, true_cdb_bytes, cdb_addrs);
            }  
        }
        
        let cdb_val = cdb_c.extract_cdb(Ghost(true_cdb_bytes), Ghost(cdb_addrs), Ghost(impervious_to_corruption));
        assert(cdb_val.spec_to_bytes() == cdb_c@);

        // If the read encoded CDB is one of the expected ones, translate
        // it into a boolean; otherwise, indicate corruption.

        if *cdb_val == CDB_FALSE {
            Some(false)
        }
        else if *cdb_val == CDB_TRUE {
            Some(true)
        }
        else {
            proof {
                // This part of the proof can be flaky -- invoking this axiom helps stabilize it
                // by helping Z3 prove that the real CDB is neither valid value, which implies we are 
                // not impervious to corruption
               axiom_to_from_bytes::<u64>(*cdb_val);
            }
            None
        }
    }

    // TODO DOCUMENTATION
    pub fn check_cdb_in_subregion<PM>(
        cdb_c: MaybeCorruptedBytes<u64>,
        subregion: &PersistentMemorySubregion,
        pm_region: &PM,
        Ghost(impervious_to_corruption): Ghost<bool>,
        Ghost(relative_cdb_addrs): Ghost<Seq<int>>,
    ) -> (result: Option<bool>)
        where 
            PM: PersistentMemoryRegion,
        requires
            forall |i: int| 0 <= i < relative_cdb_addrs.len() ==> relative_cdb_addrs[i] <= subregion.view(pm_region).len(),
            all_elements_unique(relative_cdb_addrs),
            ({
                let true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| subregion.view(pm_region).committed()[relative_cdb_addrs[i]]);
                let true_cdb = u64::spec_from_bytes(true_cdb_bytes);
                &&& u64::bytes_parseable(true_cdb_bytes)
                &&& true_cdb == CDB_FALSE || true_cdb == CDB_TRUE
                &&& if impervious_to_corruption { cdb_c@ == true_cdb_bytes }
                        else { subregion.maybe_corrupted_relative(cdb_c@, true_cdb_bytes, relative_cdb_addrs) }
            })
        ensures
            ({
                let true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| subregion.view(pm_region).committed()[relative_cdb_addrs[i]]);
                let true_cdb = u64::spec_from_bytes(true_cdb_bytes);
                match result {
                    Some(b) => if b { true_cdb == CDB_TRUE }
                               else { true_cdb == CDB_FALSE },
                    None => !impervious_to_corruption,
                }
            })
    {
        let ghost true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| subregion.view(pm_region).committed()[relative_cdb_addrs[i]]);
        let ghost absolute_cdb_addrs = Seq::new(relative_cdb_addrs.len(), |i: int| subregion.start() + relative_cdb_addrs[i]);
        proof {
            // We may need to invoke the axiom
            // `axiom_corruption_detecting_boolean` to justify concluding
            // that, if we read `CDB_FALSE` or `CDB_TRUE`, it can't have
            // been corrupted.
            if !impervious_to_corruption && (cdb_c@ == CDB_FALSE.spec_to_bytes() || cdb_c@ == CDB_TRUE.spec_to_bytes()) {
                axiom_corruption_detecting_boolean(cdb_c@, true_cdb_bytes, absolute_cdb_addrs);
            }  
        }
        
        let cdb_val = cdb_c.extract_cdb(Ghost(true_cdb_bytes), Ghost(absolute_cdb_addrs), Ghost(impervious_to_corruption));
        assert(cdb_val.spec_to_bytes() == cdb_c@);

        // If the read encoded CDB is one of the expected ones, translate
        // it into a boolean; otherwise, indicate corruption.

        if *cdb_val == CDB_FALSE {
            Some(false)
        }
        else if *cdb_val == CDB_TRUE {
            Some(true)
        }
        else {
            proof {
                // This part of the proof can be flaky -- invoking this axiom helps stabilize it
                // by helping Z3 prove that the real CDB is neither valid value, which implies we are 
                // not impervious to corruption
               axiom_to_from_bytes::<u64>(*cdb_val);
            }
            None
        }
    }

    /// If the only outstanding write is `const_persistence_chunk_size()`-sized and
    /// -aligned, then there are only two possible resulting crash states,
    /// one with the write and one without.

    // This lemma establishes that, if there are no outstanding writes and
    // we write a `const_persistence_chunk_size()`-aligned segment of length
    // `const_persistence_chunk_size()`, then there are only two possible crash
    // states that can happen after the write is initiated. In one of those
    // crash states, nothing has changed; in the other, all the written
    // bytes have been updated according to this write.
    pub proof fn lemma_single_write_crash_effect_on_pm_region_view(
        pm_region_view: PersistentMemoryRegionView,
        write_addr: int,
        bytes_to_write: Seq<u8>,
    )
        requires
            bytes_to_write.len() == const_persistence_chunk_size(),
            write_addr % const_persistence_chunk_size() == 0,
            0 <= write_addr,
            write_addr + const_persistence_chunk_size() <= pm_region_view.len(),
            pm_region_view.no_outstanding_writes()
        ensures
            ({
                let new_pm_region_view = pm_region_view.write(write_addr, bytes_to_write);
                forall |crash_bytes: Seq<u8>| new_pm_region_view.can_crash_as(crash_bytes) ==> {
                    ||| crash_bytes == pm_region_view.committed()
                    ||| crash_bytes == new_pm_region_view.flush().committed()
                }
            })
    {
        assert forall |crash_bytes: Seq<u8>|
                   pm_region_view.write(write_addr, bytes_to_write).can_crash_as(crash_bytes) implies {
                       ||| crash_bytes == pm_region_view.committed()
                       ||| crash_bytes == pm_region_view.write(write_addr, bytes_to_write).flush().committed()
                   } by {
            let chunk = write_addr / const_persistence_chunk_size();
            let new_pm_region_view = pm_region_view.write(write_addr, bytes_to_write);

            // To reason about all the bytes we haven't written, it's useful to invoke
            // the lemma that says that wherever there's no outstanding write, there's
            // only one possible crash state, the committed state.

            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(new_pm_region_view);

            // Then, we just have to reason about this one written chunk. There are two cases:
            // (1) the chunk isn't flushed at all and (2) the chunk is entirely flushed.

            if new_pm_region_view.chunk_corresponds_ignoring_outstanding_writes(chunk, crash_bytes) {
                assert(crash_bytes =~= pm_region_view.committed());
            }
            if new_pm_region_view.chunk_corresponds_after_flush(chunk, crash_bytes) {
                assert(crash_bytes =~= pm_region_view.write(write_addr, bytes_to_write).flush().committed());
            }
        }
    }

    // This lemma establishes that, if there are no outstanding writes and
    // we write a `const_persistence_chunk_size()`-aligned segment of length
    // `const_persistence_chunk_size()` to a single region among a collection of
    // persistent memory regions, then there are only two possible crash
    // states that can happen after the write is initiated. In one of those
    // crash states, nothing has changed; in the other, all the written
    // bytes have been updated according to this write.
    pub proof fn lemma_single_write_crash_effect_on_pm_regions_view(
        pm_regions_view: PersistentMemoryRegionsView,
        index: int,
        write_addr: int,
        bytes_to_write: Seq<u8>,
    )
        requires
            0 <= index < pm_regions_view.len(),
            bytes_to_write.len() == const_persistence_chunk_size(),
            write_addr % const_persistence_chunk_size() == 0,
            0 <= write_addr,
            write_addr + const_persistence_chunk_size() <= pm_regions_view[index as int].len(),
            pm_regions_view.no_outstanding_writes(),

        ensures
            ({
                let new_pm_regions_view = pm_regions_view.write(index, write_addr, bytes_to_write);
                let flushed_pm_regions_view = new_pm_regions_view.flush();
                forall |crash_bytes: Seq<Seq<u8>>| new_pm_regions_view.can_crash_as(crash_bytes) ==> {
                    ||| crash_bytes == pm_regions_view.committed()
                    ||| crash_bytes == flushed_pm_regions_view.committed()
                }
            })
    {
        let new_pm_regions_view = pm_regions_view.write(index, write_addr, bytes_to_write);
        let flushed_pm_regions_view = new_pm_regions_view.flush();
        assert forall |crash_bytes: Seq<Seq<u8>>| new_pm_regions_view.can_crash_as(crash_bytes) implies {
            ||| crash_bytes == pm_regions_view.committed()
            ||| crash_bytes == flushed_pm_regions_view.committed()
        } by {
            // All other regions other than the written-to one can only
            // crash into their `committed` state, since they have no outstanding writes.
            assert forall |other: int| 0 <= other < pm_regions_view.len() && other != index implies
                       #[trigger] crash_bytes[other] == pm_regions_view[other].committed() by {
                // The following `assert` is required to trigger the `forall`
                // in `PersistentMemoryRegionsView::no_outstanding_writes`:
                assert(pm_regions_view[other].no_outstanding_writes());

                // Knowing that there are no outstanding writes, we can now call the following lemma.
                lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(
                    new_pm_regions_view[other]);
            }

            // This lemma says that there are only two possible states for
            // region number `index` after this write is initiated.
            lemma_single_write_crash_effect_on_pm_region_view(pm_regions_view[index], write_addr, bytes_to_write);

            // We now use extensional equality to show the final result.
            // There are two cases to consider: (1) the write doesn't get
            // flushed; (2) the write gets flushed.

            if crash_bytes[index] == pm_regions_view[index].committed() {
                assert(crash_bytes =~= pm_regions_view.committed());
            }
            if crash_bytes[index] == pm_regions_view[index].write(write_addr, bytes_to_write).flush().committed() {
                let new_regions_view = pm_regions_view.write(index, write_addr, bytes_to_write);
                let flushed_regions_view = new_regions_view.flush();
                assert(forall |any| 0 <= any < pm_regions_view.len() ==> #[trigger] crash_bytes[any] =~=
                    flushed_regions_view.committed()[any]);
                assert(crash_bytes =~= flushed_regions_view.committed());
            }
        }
    }

    // This lemma establishes that if one performs a write and then a
    // flush, then the committed contents reflect that write.
    pub proof fn lemma_write_reflected_after_flush_committed(
        pm_region_view: PersistentMemoryRegionView,
        addr: int,
        bytes: Seq<u8>,
    )
        requires
            0 <= addr,
            addr + bytes.len() <= pm_region_view.len(),
        ensures
            pm_region_view.write(addr, bytes).flush().committed().subrange(addr as int, addr + bytes.len()) == bytes
    {
        // All we need is to get Z3 to consider extensional equality.
        assert(pm_region_view.write(addr, bytes).flush().committed().subrange(addr as int, addr + bytes.len()) =~=
               bytes);
    }

    // Calculates the CRC for a single `PmCopy` object.
    pub fn calculate_crc<S>(val: &S) -> (out: u64)
        where
            S: PmCopy + Sized,
        requires
            // this is true in the default implementation of `spec_crc`, but
            // an impl of `PmCopy` can override the default impl, so
            // we have to require it here
            val.spec_crc() == spec_crc_u64(val.spec_to_bytes())
        ensures
            val.spec_crc() == out,
            spec_crc_u64(val.spec_to_bytes()) == out,
    {
        let mut digest = CrcDigest::new();
        digest.write(val);
        proof {
            lemma_auto_spec_u64_to_from_le_bytes();
            digest.bytes_in_digest().lemma_flatten_one_element();
        }
        digest.sum64()
    }

    pub fn calculate_crc_bytes(val: &[u8]) -> (out: u64) 
        ensures 
            out == spec_crc_u64(val@),
            out.spec_to_bytes() == spec_crc_bytes(val@),
    {
        let mut digest = CrcDigest::new();
        digest.write_bytes(val);
        proof {
            lemma_auto_spec_u64_to_from_le_bytes();
            digest.bytes_in_digest().lemma_flatten_one_element();
        }
        digest.sum64()
    }

    // This lemma establishes that for any `i` and `n`, if
    //
    // `forall |k| 0 <= k < n ==> mem1[i+k] == mem2[i+k]`
    //
    // holds, then
    //
    // `extract_bytes(mem1, i, n) == mem2.extract_bytes(mem2, i, n)`
    //
    // also holds.
    //
    // This is an obvious fact, so the body of the lemma is
    // empty. Nevertheless, the lemma is useful because it establishes
    // a trigger. Specifically, it hints Z3 that whenever Z3 is
    // thinking about two terms `extract_bytes(mem1, i, n)` and
    // `extract_bytes(mem2, i, n)` where `mem1` and `mem2` are the
    // specific memory byte sequences passed to this lemma, Z3 should
    // also think about this lemma's conclusion. That is, it should
    // try to prove that
    //
    // `forall |k| 0 <= k < n ==> mem1[i+k] == mem2[i+k]`
    //
    // and, whenever it can prove that, conclude that
    //
    // `extract_bytes(mem1, i, n) == mem2.extract_bytes(mem2, i, n)`
    pub proof fn lemma_establish_extract_bytes_equivalence(
        mem1: Seq<u8>,
        mem2: Seq<u8>,
    )
        ensures
            forall |i: nat, n: nat| extract_bytes(mem1, i, n) =~= extract_bytes(mem2, i, n) ==>
                #[trigger] extract_bytes(mem1, i, n) == #[trigger] extract_bytes(mem2, i, n)
    {
    }

    // This lemma proves that a subrange of a subrange is equal to the result of a single call to subrange.
    pub proof fn lemma_subrange_of_subrange_equal(mem: Seq<u8>, pos1: nat, pos2: nat, pos3: nat, pos4: nat)
        requires
            pos1 <= pos2 <= pos3 <= pos4 <= mem.len(),
        ensures
            mem.subrange(pos2 as int, pos3 as int) ==
            mem.subrange(pos1 as int, pos4 as int).subrange(pos2 - pos1, pos3 - pos1)
    {
        assert(mem.subrange(pos2 as int, pos3 as int) =~=
               mem.subrange(pos1 as int, pos4 as int).subrange(pos2 - pos1, pos3 - pos1));
    }

    // This lemma proves that an extract_bytes of an extract_bytes is equal to the result of a single call to
    // extract_bytes.
    pub proof fn lemma_extract_bytes_of_extract_bytes_equal(mem: Seq<u8>, start1: nat, start2: nat, len1: nat, len2: nat)
        requires 
            start1 <= start2 <= start2 + len2 <= start1 + len1 <= mem.len()
        ensures 
            extract_bytes(mem, start2, len2) ==
            extract_bytes(extract_bytes(mem, start1, len1), (start2 - start1) as nat, len2)
    {
        lemma_subrange_of_subrange_equal(mem, start1, start2, start2 + len2, start1 + len1);
    }

    // This lemma proves that a subrange of a subrange is equal to the result of a single call to
    // subrange.
    pub proof fn lemma_subrange_of_subrange_forall(mem: Seq<u8>)
        ensures
            forall|s1: int, e1: int, s2: int, e2: int|
               0 <= s1 <= e1 <= mem.len() && 0 <= s2 <= e2 <= e1 - s1 ==>
               mem.subrange(s1, e1).subrange(s2, e2) == mem.subrange(s1 + s2, s1 + e2)
    {
        assert forall|s1: int, e1: int, s2: int, e2: int|
               0 <= s1 <= e1 <= mem.len() && 0 <= s2 <= e2 <= e1 - s1 implies
               mem.subrange(s1, e1).subrange(s2, e2) == mem.subrange(s1 + s2, s1 + e2) by {
            mem.lemma_slice_of_slice(s1, e1, s2, e2);
        }
    }

    pub proof fn lemma_get_crash_state_given_one_for_other_view_differing_only_at_certain_addresses(
        v1: PersistentMemoryRegionView,
        v2: PersistentMemoryRegionView,
        crash_state1: Seq<u8>,
        can_views_differ_at_addr: spec_fn(int) -> bool,
    ) -> (crash_state2: Seq<u8>)
        requires
            v1.len() == v2.len(),
            forall|addr: int| #![trigger can_views_differ_at_addr(addr)]
                0 <= addr < v1.len() && !can_views_differ_at_addr(addr) ==> v1.state[addr] == v2.state[addr],
            v1.can_crash_as(crash_state1),
        ensures
            forall|addr: int| #![trigger can_views_differ_at_addr(addr)]
                0 <= addr < v1.len() && !can_views_differ_at_addr(addr) ==> crash_state1[addr] == crash_state2[addr],
            v2.can_crash_as(crash_state2),
    {
        let crash_state2 = Seq::<u8>::new(crash_state1.len(), |addr: int| {
           if !can_views_differ_at_addr(addr) {
               crash_state1[addr]
           }
           else {
               let chunk = addr / const_persistence_chunk_size();
               if v1.chunk_corresponds_ignoring_outstanding_writes(chunk, crash_state1) {
                   v2.state[addr].state_at_last_flush
               }
               else {
                   v2.state[addr].flush_byte()
               }
           }
        });
        assert forall|chunk| {
            ||| v2.chunk_corresponds_ignoring_outstanding_writes(chunk, crash_state2)
            ||| v2.chunk_corresponds_after_flush(chunk, crash_state2)
        } by {
            if v1.chunk_corresponds_ignoring_outstanding_writes(chunk, crash_state1) {
                assert(v2.chunk_corresponds_ignoring_outstanding_writes(chunk, crash_state2));
            }
            else {
                assert(v1.chunk_corresponds_after_flush(chunk, crash_state1));
                assert(v2.chunk_corresponds_after_flush(chunk, crash_state2));
            }
        }
        crash_state2
    }

    pub proof fn lemma_write_doesnt_change_committed(
        pm: PersistentMemoryRegionView,
        addr: int,
        bytes: Seq<u8>
    )
        requires
            0 <= addr,
            addr + bytes.len() <= pm.len(),
        ensures
            pm.committed() == pm.write(addr, bytes).committed(),
    {
        assert(pm.committed() =~= pm.write(addr, bytes).committed());
    }
}
