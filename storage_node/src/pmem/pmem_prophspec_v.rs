//! This file contains the trusted specification for how a persistent
//! memory region (implementing trait `PersistentMemoryRegion`)
//! behaves.
//!
//! One of the things it models is what can happen to a persistent
//! memory region if the system crashes in the middle of a write.
//! Specifically, it says that on a crash some subset of the
//! outstanding byte writes will be flushed (performed before the
//! crash) and the rest of the outstanding byte writes will be
//! discarded. Furthermore, any 8-byte-aligned 8-byte chunk either has
//! all its outstanding writes flushed or all of them discarded.
//!
//! Following Perennial, this model uses prophecy to describe the
//! current state of the persistent memory. The abstract state of the
//! storage consists of a read state, which doesn't use prophecy, and
//! a durable state, which does use prophecy.
//
//! The read state is straightforward: It reflects all writes done so
//! far, regardless of whether those writes have been made durable and
//! will survive a crash. So it reflects what future reads will see,
//! at least until the next crash terminates the Verus program.
//!
//! The durable state represents what state would result if a crash
//! happened now. It forms this representation by predicting, every
//! time a write occurs, which of the bytes in that write will be made
//! durable before the next crash. Of course, this prediction can't be
//! made in reality, but that doesn't stop us from making the
//! prediction in ghost state.
//!
//! The semantics of a flush is that, if you're calling flush right
//! now, the predictor must have predicted that all outstanding
//! written bytes would be flushed to persistent memory before the
//! next crash. So a *precondition* of a flush operation is that the
//! read state matches the durable state.
//!
//! Modeling with an omniscient predictor is naturally unrealistic.
//! But in Perennial, it's been proved that any program correct under
//! the prophecy model is correct under the traditional model of a
//! storage system. So the model is a reasonable and sound one.
//!
//! Another thing this file models is how bit corruption manifests. It
//! models a persistent memory region as either impervious to
//! corruption or not so. If a memory is impervious to corruption,
//! then bit corruption never occurs and reads always return the
//! last-written bytes. However, if memory isn't impervious to
//! corruption, then all that's guaranteed is that the bytes that are
//! read and the last-written bytes are related by `maybe_corrupted`.
//!
//! This file also provides axioms allowing possibly-corrupted bytes
//! to be freed of suspicion of corruption. Both axioms require the
//! use of CRCs to detect possible corruption, and model a CRC match
//! as showing evidence of an absence of corruption.

use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {

    /// We model the state of a region of persistent memory as a
    /// `PersistentMemoryRegionView`, which is two sequences of `u8`.
    /// The first is the latest bytes written, reflecting what will
    /// be read by a `read` operation. The second is the bytes that
    /// will be on persistent memory in the event of a crash,
    /// reflecting a prophecy of which outstanding writes will be
    /// made durable.

    #[verifier::ext_equal]
    pub struct PersistentMemoryRegionView
    {
        pub read_state: Seq<u8>,
        pub durable_state: Seq<u8>,
    }

    pub open spec fn update_bytes(s: Seq<u8>, addr: int, bytes: Seq<u8>) -> Seq<u8>
    {
        Seq::new(s.len(), |i: int| if addr <= i < addr + bytes.len() { bytes[i - addr] } else { s[i] })
    }

    /// We model writes as prophesizing which bytes will be written,
    /// subject to the constraint that bytes in the same chunk
    /// (aligned on `const_persistence_chunk_size()` boundaries) will
    /// either all be written or have none of them written.

    pub open spec fn chunk_corresponds(s1: Seq<u8>, s2: Seq<u8>, chunk: int) -> bool
    {
        forall |addr: int| {
            &&& 0 <= addr < s1.len()
            &&& addr_in_chunk(chunk, addr)
        } ==> #[trigger] s1[addr] == s2[addr]
    }

    pub open spec fn chunk_trigger(chunk: int) -> bool
    {
        true
    }

    pub open spec fn can_result_from_partial_write(post: Seq<u8>, pre: Seq<u8>, addr: int, bytes: Seq<u8>) -> bool
    {
        &&& post.len() == pre.len()
        &&& forall |chunk| #[trigger] chunk_trigger(chunk) ==> {
              ||| chunk_corresponds(post, pre, chunk)
              ||| chunk_corresponds(post, update_bytes(pre, addr, bytes), chunk)
        }
    }

    impl PersistentMemoryRegionView
    {
        pub open spec fn len(self) -> nat
        {
            self.read_state.len()
        }

        pub open spec fn valid(self) -> bool
        {
            self.read_state.len() == self.durable_state.len()
        }

        pub open spec fn can_result_from_write(self, pre: Self, addr: int, bytes: Seq<u8>) -> bool
        {
            &&& self.read_state == update_bytes(pre.read_state, addr, bytes)
            &&& can_result_from_partial_write(self.durable_state, pre.durable_state, addr, bytes)
        }

        pub open spec fn flush_predicted(self) -> bool
        {
            self.durable_state == self.read_state
        }
    }

    pub trait PersistentMemoryRegion : Sized
    {
        spec fn view(&self) -> PersistentMemoryRegionView;

        spec fn inv(&self) -> bool;

        spec fn constants(&self) -> PersistentMemoryConstants;

        fn get_region_size(&self) -> (result: u64)
            requires
                self.inv()
            ensures
                result == self@.len()
        ;

        fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
            where 
                S: PmCopy + Sized,
            requires
                self.inv(),
                addr + S::spec_size_of() <= self@.len(),
                // We must have previously written a serialized S to this addr
                S::bytes_parseable(self@.read_state.subrange(addr as int, addr + S::spec_size_of()))
            ensures
                match bytes {
                    Ok(bytes) => {
                        let true_bytes = self@.read_state.subrange(addr as int, addr + S::spec_size_of());
                        let addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| i + addr);
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
                }
            ;

        fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>) 
            requires 
                self.inv(),
                addr + num_bytes <= self@.len(),
            ensures 
                match bytes {
                    Ok(bytes) => {
                        let true_bytes = self@.read_state.subrange(addr as int, addr + num_bytes);
                        let addrs = Seq::<int>::new(num_bytes as nat, |i: int| i + addr);
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
                
        ;

        fn write(&mut self, addr: u64, bytes: &[u8])
            requires
                old(self).inv(),
                addr + bytes@.len() <= old(self)@.len(),
            ensures
                self.inv(),
                self.constants() == old(self).constants(),
                self@.can_result_from_write(old(self)@, addr as int, bytes@),
        ;

        fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S)
            where
                S: PmCopy + Sized
            requires
                old(self).inv(),
                addr + S::spec_size_of() <= old(self)@.len(),
            ensures
                self.inv(),
                self.constants() == old(self).constants(),
                self@.can_result_from_write(old(self)@, addr as int, to_write.spec_to_bytes()),
        ;

        fn flush(&mut self)
            requires
                old(self).inv(),
            ensures
                old(self)@.flush_predicted(), // it must have been prophesized that this flush would happen
                self.inv(),
                self.constants() == old(self).constants(),
                self@ == old(self)@,
        ;
    }

}
