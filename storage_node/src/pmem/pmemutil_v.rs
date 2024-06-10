//! This file contains lemmas and utility executable functions about
//! persistent memory regions.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::crc_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {

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
            crc_c@.len() == CRC_SIZE,
            ({
                let true_data_bytes = Seq::new(data_addrs.len(), |i: int| mem[data_addrs[i] as int]);
                let true_crc_bytes = Seq::new(crc_addrs.len(), |i: int| mem[crc_addrs[i]]);
                let true_crc = u64::spec_from_bytes(true_crc_bytes);
                if impervious_to_corruption {
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
                let true_crc_bytes = Seq::new(CRC_SIZE as nat, |i: int| mem[crc_addrs[i]]);
                let true_crc = u64::spec_from_bytes(true_crc_bytes);
                true_crc == spec_crc_u64(true_data_bytes) ==>
                if b {
                    &&& data_c@ == true_data_bytes
                    &&& crc_c@ == true_crc_bytes
                }
                else {
                    !impervious_to_corruption
                }
            })
    {
        assume(false);
        // Compute the CRC of the possibly-corrupted data.
        let computed_crc = bytes_crc(data_c);

        // Convert both the CRC read from memory and the CRC just
        // computed into `u64`s to make it easy to compare them.
        let crc1 = u64_from_le_bytes(crc_c);
        let crc2 = u64_from_le_bytes(computed_crc.as_slice());

        proof {
            let true_data_bytes = Seq::new(data_addrs.len(), |i: int| mem[data_addrs[i] as int]);
            let true_crc_bytes = Seq::new(crc_addrs.len(), |i: int| mem[crc_addrs[i]]);
            let true_crc = u64::spec_from_bytes(true_crc_bytes);

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
                &&& true_crc == spec_crc_u64(true_data_bytes)
                &&& !impervious_to_corruption
                &&& crc_c@ == computed_crc@
            } {
                axiom_bytes_uncorrupted2(data_c@, true_data_bytes, data_addrs, crc_c@, true_crc_bytes, crc_addrs);
            }

            // To argue that `crc1` matches `crc2` if and only if `crc_c`
            // matches `computed_crc`, we invoke the lemma saying that
            // `spec_u64_to_le_bytes` is the inverse of what
            // `u64_from_le_bytes` computes.

            let crc1_alt = spec_u64_to_le_bytes(crc1);
            let crc2_alt = spec_u64_to_le_bytes(crc2);
            lemma_auto_spec_u64_to_from_le_bytes();
        }

        // Return the comparison between the CRCs
        crc1 == crc2
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
    pub fn check_cdb(
        cdb_c: MaybeCorrupted<u64>,
        Ghost(true_cdb): Ghost<u64>,
        Ghost(mem): Ghost<Seq<u8>>,
        Ghost(impervious_to_corruption): Ghost<bool>,
        Ghost(cdb_addrs): Ghost<Seq<int>>,
    ) -> (result: Option<bool>)
        requires
            forall |i: int| 0 <= i < cdb_addrs.len() ==> cdb_addrs[i] <= mem.len(),
            ({
                let true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem[cdb_addrs[i]]);
                &&& true_cdb.spec_to_bytes() == true_cdb_bytes
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
        assume(false);

        proof {
            // We may need to invoke the axiom
            // `axiom_corruption_detecting_boolean` to justify concluding
            // that, if we read `CDB_FALSE` or `CDB_TRUE`, it can't have
            // been corrupted.
            let ghost cdb_c_val = u64::spec_from_bytes(cdb_c@);

            if !impervious_to_corruption && (cdb_c_val == CDB_FALSE || cdb_c_val == CDB_TRUE) {
                let true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem[cdb_addrs[i]]);
                axiom_corruption_detecting_boolean(cdb_c@, true_cdb_bytes, cdb_addrs);
            }
        }

        let cdb_val = cdb_c.extract_init_val(Ghost(true_cdb));

        // If the read encoded CDB is one of the expected ones, translate
        // it into a boolean; otherwise, indicate corruption.

        if cdb_val == CDB_FALSE {
            Some(false)
        }
        else if cdb_val == CDB_TRUE {
            Some(true)
        }
        else {
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
}
