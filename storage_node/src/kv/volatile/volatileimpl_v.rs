//! This file contains a trait that defines the interface for the high-level
//! volatile component of the KV store.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::kvimpl_t::*;
use crate::kv::volatile::hash_map::*; // replace with std::hash_map when available
use crate::kv::volatile::volatilespec_t::*;
use crate::pmem::pmcopy_t::*;
use std::hash::Hash;

verus! {

pub struct VolatileKvListEntryLocationImpl
{
    pub list_node_addr: u64,
    pub offset_within_list_node: u64,
}

impl View for VolatileKvListEntryLocationImpl
{
    type V = VolatileKvListEntryLocation;
    open spec fn view(&self) -> Self::V
    {
        VolatileKvListEntryLocation {
            list_node_addr: self.list_node_addr as int,
            offset_within_list_node: self.offset_within_list_node as int,
        }
    }
}

pub struct VolatileKvIndexEntryImpl
{
    pub header_addr: u64,
    pub list_len: u64,
    pub entry_locations: Vec<VolatileKvListEntryLocationImpl>,
}

impl VolatileKvIndexEntryImpl
{
    pub open spec fn valid(&self) -> bool
    {
        self.list_len <= self.entry_locations.len()
    }
}

impl View for VolatileKvIndexEntryImpl
{
    type V = VolatileKvIndexEntry;

    open spec fn view(&self) -> Self::V
    {
        VolatileKvIndexEntry {
            header_addr: self.header_addr as int,
            list_len: self.list_len as int,
            entry_locations: Seq::new(self.entry_locations.len() as nat, |i: int| self.entry_locations[i]@),
        }
    }
}

#[verifier::reject_recursive_types(K)]
pub struct VolatileKvIndexImpl<K>
where
    K: Hash + Eq + Clone + Sized + std::fmt::Debug,
{
    pub m: MyHashMap<K, VolatileKvIndexEntryImpl>,
    pub num_list_entries_per_node: u64,
}

impl<K> VolatileKvIndex<K> for VolatileKvIndexImpl<K>
where
    K: Hash + Eq + Clone + Sized + std::fmt::Debug,
{
    open spec fn view(&self) -> VolatileKvIndexView<K>
    {
        VolatileKvIndexView::<K> {
            contents: Map::<K, VolatileKvIndexEntry>::new(|k: K| self.m@.contains_key(k), |k: K| self.m@[k]@),
            num_list_entries_per_node: self.num_list_entries_per_node as int
        }
    }

    open spec fn valid(&self) -> bool
    {
        &&& 0 < self.num_list_entries_per_node
        &&& forall |k| #[trigger] self.m@.contains_key(k) ==> self.m@[k].valid()
    }

    fn new(
        kvstore_id: u128,
        max_keys: usize,
        num_list_entries_per_node: u64,
    ) -> (result: Result<Self, KvError<K>>)
    {
        let ret = Self {
            m: MyHashMap::<K, VolatileKvIndexEntryImpl>::new(),
            num_list_entries_per_node
        };
        assert(ret@.contents =~= Map::<K, VolatileKvIndexEntry>::empty());
        Ok(ret)
    }

    fn insert_key(
        &mut self,
        key: &K,
        header_addr: u64,
    ) -> (result: Result<(), KvError<K>>)
    {
        assume(false);
        Err(KvError::OutOfSpace)
    }

    fn append_to_list(
        &mut self,
        key: &K,
    ) -> (result: Result<(), KvError<K>>)
    {
        assume(false);
        Err(KvError::OutOfSpace)
    }

    fn get(
        &self,
        key: &K
    ) -> (result: Option<u64>)
    {
        assume(false);
        None
    }

    // Returns the address of the node that contains the list entry at the specified index,
    // as well as which entry in that node corresponds to that list entry.
    fn get_entry_location_by_index(
        &self,
        key: &K,
        idx: usize,
    ) -> (result: Result<(u64, u64), KvError<K>>)
    {
        assume(false);
        Err(KvError::OutOfSpace)
    }

    fn remove(
        &mut self,
        key: &K
    ) -> (result: Result<u64, KvError<K>>)
    {
        let result = match self.m.remove(key) {
            Some(entry) => Ok(entry.header_addr),
            None => Err(KvError::<K>::KeyNotFound),
        };
        assert(self@.contents =~= old(self)@.contents.remove(*key));
        result
    }

    // trims the volatile index for the list associated with the key
    fn trim_list(
        &mut self,
        key: &K,
        trim_length: usize
    ) -> (result: Result<(), KvError<K>>)
    {
        assume(false);
        Err(KvError::OutOfSpace)
    }

    fn get_keys(
        &self
    ) -> (result: Vec<K>)
    {
        assume(false);
        Vec::<K>::new()
    }
}

}
