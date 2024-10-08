use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {
pub trait CheckPermission<ID, State>
{
    spec fn check_permission(&self, state: State) -> bool;
    spec fn valid(&self, id: ID) -> bool;
}

pub trait WriteRestrictedPersistentMemoryRegionTrait<ID, Perm>
    where
        Perm: CheckPermission<ID, Seq<u8>>
{
    spec fn view(&self) -> PersistentMemoryRegionView;
    spec fn inv(&self) -> bool;
    spec fn constants(&self) -> PersistentMemoryConstants;
    spec fn id(&self) -> ID;

    // This executable function is the only way to perform a write, and
    // it requires the caller to supply permission authorizing the
    // write. The caller must prove that for every state this memory
    // can crash and recover into, the permission authorizes that
    // state.
    exec fn write(&mut self, addr: u64, bytes: &[u8], perm: Tracked<&Perm>)
        requires
            old(self).inv(),
            perm@.valid(old(self).id()),
            addr + bytes@.len() <= old(self)@.len(),
            // The key thing the caller must prove is that all crash states are authorized by `perm`
            forall |s| can_result_from_partial_write(s, old(self)@.durable_state, addr as int, bytes@)
                  ==> #[trigger] perm@.check_permission(s),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self.id() == old(self).id(),
            self@.can_result_from_write(old(self)@, addr as int, bytes@);

    exec fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S, perm: Tracked<&Perm>)
        where
            S: PmCopy + Sized
        requires
            old(self).inv(),
            perm@.valid(old(self).id()),
            addr + S::spec_size_of() <= old(self)@.len(),
            // The key thing the caller must prove is that all crash states are authorized by `perm`
            forall |s| can_result_from_partial_write(s, old(self)@.durable_state, addr as int, to_write.spec_to_bytes())
                  ==> #[trigger] perm@.check_permission(s),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self.id() == old(self).id(),
            self@.can_result_from_write(old(self)@, addr as int, to_write.spec_to_bytes());

    // Even though the memory is write-restricted, no restrictions are
    // placed on calling `flush`. After all, `flush` can only narrow
    // the possible states the memory can crash into. So if the memory
    // is already restricted to only crash into good states, `flush`
    // automatically maintains that restriction.
    exec fn flush(&mut self)
        requires
            old(self).inv(),
        ensures
            old(self)@.flush_predicted(), // it must have been prophesized that this flush would happen
            self.inv(),
            self.constants() == old(self).constants(),
            self.id() == old(self).id(),
            self@ == old(self)@;

    exec fn get_region_size(&self) -> (result: u64)
        requires
            self.inv()
        ensures
            result == self@.len();

    exec fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
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
            };

    exec fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>)
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
            };
}
}
