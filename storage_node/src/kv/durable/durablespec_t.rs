//! A `DurableKvStore` represents the durable components of a `KvStore`. It is generic
//! to allow for different PM abstractions, persistent layouts, etc.
//! It should refine an array where each element optionally contains a key, a item,
//! and a list of pages. This structure encompasses all of the durable KV entries,
//! so we aren't distinguishing between separate physical memory regions. I think
//! we want to stay at a higher level of abstraction here to make it easier to jump
//! up to the overall KV store

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::kvimpl_t::*;
use crate::kv::volatile::volatilespec_t::*;
use crate::pmem::pmemspec_t::*;
use std::hash::Hash;

// TODO: is it safe for the fields of the structs in this file to be pub?

verus! {
    pub struct DurableKvStoreViewEntry<K, I, L>
    where
        K: Hash + Eq,
        // P: LogicalRange,
    {
        pub key: K,
        pub item: I,
        pub pages: Seq<(int, L)>, // (physical location, entry at that location)
    }

    // TODO: remove since the fields are public
    impl<K, I, L> DurableKvStoreViewEntry<K, I, L>
    where
        K: Hash + Eq,
    {
        pub open spec fn key(self) -> K
        {
            self.key
        }

        pub open spec fn item(self) -> I
        {
            self.item
        }

        pub open spec fn pages(self) -> Seq<(int, L)>
        {
            self.pages
        }

        // returns a sequence of entries without their physical locations
        pub open spec fn page_entries(self) -> Seq<L>
        {
            Seq::new(self.pages.len(), |i| self.pages[i].1)
        }
    }

    pub struct DurableKvStoreView<K, I, L>
    where
        K: Hash + Eq,
        I: Item<K>,
        // P: LogicalRange,
    {
        pub contents: Seq<Option<DurableKvStoreViewEntry<K, I, L>>>
    }

    impl<K, I, L> DurableKvStoreView<K, I, L>
    where
        K: Hash + Eq,
        I: Item<K>,
        // P: LogicalRange,
    {
        pub open spec fn spec_index(self, idx: int) -> Option<DurableKvStoreViewEntry<K, I, L>>
        {
            self.contents[idx]
        }

        pub closed spec fn empty(self) -> bool
        {
            forall |i| 0 <= i < self.contents.len() ==>
                self.contents[i].is_None()
        }

        pub open spec fn len(self) -> nat
        {
            self.contents.len()
        }

        pub open spec fn create(self, offset: int, item: I) -> Self
        {
            Self {
                contents: self.contents.update(
                    offset,
                    Some(DurableKvStoreViewEntry {
                        key: item.spec_key(),
                        item,
                        pages: Seq::<(int, L)>::empty()
                    })
                )
            }
        }

        // TODO: might be cleaner to define this elsewhere (like in the interface)
        pub open spec fn matches_volatile_index(&self, volatile_index: VolatileKvIndexView<K>) -> bool
        {
            ||| (self.empty() && volatile_index.empty())
            ||| forall |k: K| volatile_index.contains_key(k) <==>
                {
                    let index = volatile_index[k];
                    match index {
                        Some(index) => {
                            let entry = self.contents[index.metadata_offset];
                            match entry {
                                Some(entry) => {
                                    &&& entry.key() == k
                                    &&& forall |i: int| #![auto] 0 <= i < entry.pages().len() ==> {
                                            entry.pages()[i].0 == index.list_entry_offsets[i]
                                    }
                                }
                                None => false
                            }
                        }
                        None => false
                    }

                }
        }
    }
}
