use builtin::*;
use builtin_macros::*;
use std::fs::Metadata;
use std::hash::Hash;
use vstd::prelude::*;
use vstd::bytes::*;
use crate::kv::durable::logentry_v::*;
use crate::kv::kvimpl_t::*;
use crate::kv::durable::metadata::metadataspec_t::*;
use crate::kv::durable::metadata::layout_v::*;
use crate::kv::durable::oplog::oplogspec_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::wrpm_t::WriteRestrictedPersistentMemoryRegions;
use crate::pmem::crc_t::*;

verus! {
    pub struct MetadataTable<K, E> {
        metadata_table_free_list: Vec<u64>,
        state: Ghost<MetadataTableView<K>>,
        _phantom: Option<E>
    }

    impl<K, E> MetadataTable<K, E>
        where 
            K: Serializable + std::fmt::Debug,
            E: std::fmt::Debug,
    {
        pub closed spec fn view(self) -> MetadataTableView<K> 
        {
            self.state@
        }

        pub closed spec fn recover<L>(
            mems: Seq<Seq<u8>>,
            node_size: u64,
            op_log: Seq<OpLogEntryType>,
            list_entry_map: Map<OpLogEntryType, L>,
            kvstore_id: u128,
        ) -> Option<MetadataTableView<K>>
        {
            if mems.len() != 1 {
                None
            } else {
                let metadata_table_mem = mems[0];
                // let list_node_region_mem = mems[1];
                if metadata_table_mem.len() < ABSOLUTE_POS_OF_METADATA_TABLE {
                    // Invalid if the metadata table sequence is not large enough
                    // to store the metadata header. It actually needs to be big
                    // enough to store an entry for every key, but we don't know
                    // the number of keys yet.
                    None
                } else {
                    // the metadata header is immutable, so we can check that is valid before doing 
                    // any log replay
                    let metadata_header_bytes = metadata_table_mem.subrange(
                        ABSOLUTE_POS_OF_METADATA_HEADER as int,
                        ABSOLUTE_POS_OF_METADATA_HEADER + LENGTH_OF_METADATA_HEADER
                    );
                    let crc_bytes = metadata_table_mem.subrange(
                        ABSOLUTE_POS_OF_HEADER_CRC as int,
                        ABSOLUTE_POS_OF_HEADER_CRC + CRC_SIZE
                    );
                    let metadata_header = MetadataTableHeader::spec_deserialize(metadata_header_bytes);
                    let crc = u64::spec_deserialize(crc_bytes);
                    if crc != metadata_header.spec_crc() {
                        // The list is invalid if the stored CRC does not match the contents
                        // of the metadata header
                        None
                    } else {
                        // replay the log on the metadata table and the list region, then parse them into a list view
                        let metadata_table_mem = Self::replay_log_metadata_table(metadata_table_mem, op_log);
                        // let list_nodes_mem = Self::replay_log_list_nodes(list_node_region_mem, node_size, op_log, list_entry_map);

                        // parse the item table into a mapping index->entry so that we can use it to 
                        // construct each list.
                        // TODO: IGNORE INVALID ENTRIES
                        let metadata_table = parse_metadata_table(metadata_header, metadata_table_mem);
                        match metadata_table {
                            Some(metadata_table) => Some(MetadataTableView::new(metadata_header, metadata_table)),
                            None => None
                        }
                    }
                }
            }
        }

        closed spec fn replay_log_metadata_table(mem: Seq<u8>, op_log: Seq<OpLogEntryType>) -> Seq<u8>
            decreases op_log.len()
        {
            if op_log.len() == 0 {
                mem 
            } else {
                let current_op = op_log[0];
                let op_log = op_log.drop_first();
                let mem = Self::apply_log_op_to_metadata_table_mem(mem, current_op);
                Self::replay_log_metadata_table(mem, op_log)
            }
        }

        // metadata table-related log entries store the CRC that the entry *will* have when all updates are written to it.
        // this ensures that we end up with the correct CRC even if updates to this entry were interrupted by a crash or 
        // if corruption has occurred. So, we don't check CRCs here, we just overwrite the current CRC with the new one and 
        // update relevant fields.
        closed spec fn apply_log_op_to_metadata_table_mem(mem: Seq<u8>, op: OpLogEntryType) -> Seq<u8>
        {
            let table_entry_slot_size = LENGTH_OF_ENTRY_METADATA_MINUS_KEY + CRC_SIZE + CDB_SIZE + K::spec_serialized_len();
            match op {
                OpLogEntryType::ItemTableEntryCommit { item_index, metadata_index, metadata_crc } => {
                    // on item table commit, the corresponding entry in the metadata table updates its item pointer
                    // to point to the newly-committed item. We don't handle item invalidate here because when an item is 
                    // invalidated, either its entire record will be deleted (so this metadata entry will also be deleted)
                    // or we are updating it with a newly-committed item.
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + metadata_index * table_entry_slot_size;
                    let item_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_ITEM_INDEX;
                    let item_index_bytes = item_index.spec_serialize();
                    let crc_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
                    let crc_bytes = metadata_crc.spec_serialize();
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if item_addr <= pos < item_addr + 8 {
                            item_index_bytes[pos - item_addr]
                        } else if crc_addr <= pos < crc_addr + 8 {
                            crc_bytes[pos - crc_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                OpLogEntryType::AppendListNode{list_metadata_index, old_tail, new_tail, metadata_crc} => {
                    // updates the tail field and the entry's CRC. We don't use the old tail value here -- that is only used
                    // when updating list nodes
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + list_metadata_index * table_entry_slot_size;
                    let crc_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
                    let tail_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_TAIL;
                    let crc_bytes = spec_u64_to_le_bytes(metadata_crc);
                    let new_tail_bytes = spec_u64_to_le_bytes(new_tail);
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if crc_addr <= pos < crc_addr + 8 {
                            crc_bytes[pos - crc_addr]
                        } else if tail_addr <= pos < tail_addr + 8 {
                            new_tail_bytes[pos - tail_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                OpLogEntryType::UpdateListLen{list_metadata_index, new_length, metadata_crc} => {
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + list_metadata_index * table_entry_slot_size;
                    let crc_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
                    let len_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_LENGTH;
                    let crc_bytes = spec_u64_to_le_bytes(metadata_crc);
                    let len_bytes = spec_u64_to_le_bytes(new_length);
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if crc_addr <= pos < crc_addr + 8 {
                            crc_bytes[pos - crc_addr]
                        } else if len_addr <= pos < len_addr + 8 {
                            len_bytes[pos - len_addr]
                        } else {
                            pre_byte 
                        }
                    });
                    mem
                } 
                OpLogEntryType::TrimList{list_metadata_index, new_head_node, new_list_len, new_list_start_index, metadata_crc} => {
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + list_metadata_index * table_entry_slot_size;
                    let crc_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
                    let head_addr = entry_offset +  RELATIVE_POS_OF_ENTRY_METADATA_HEAD;
                    let len_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_LENGTH;
                    let start_index_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_FIRST_OFFSET;
                    let crc_bytes = spec_u64_to_le_bytes(metadata_crc);
                    let head_bytes = spec_u64_to_le_bytes(new_head_node);
                    let len_bytes = spec_u64_to_le_bytes(new_list_len);
                    let start_bytes = spec_u64_to_le_bytes(new_list_start_index);
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if crc_addr <= pos < crc_addr + 8 {
                            crc_bytes[pos - crc_addr]
                        } else if head_addr <= pos < head_addr + 8 {
                            head_bytes[pos - head_addr]
                        } else if len_addr <= pos < len_addr + 8 {
                            len_bytes[pos - len_addr]
                        } else if start_index_addr <= pos < start_index_addr + 8 {
                            start_bytes[pos - start_index_addr]
                        } else {
                            pre_byte 
                        }
                    });
                    mem
                }
                OpLogEntryType::CommitMetadataEntry{list_metadata_index} => {
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + list_metadata_index * table_entry_slot_size;
                    // // construct a ghost entry with the values that the new entry will have so that we can obtain a CRC 
                    // let entry = ListEntryMetadata::spec_new(head, head, 0, 0, item_index);
                    // let entry_crc = entry.spec_crc();
                    // let crc_bytes = spec_u64_to_le_bytes(entry_crc);
                    // let crc_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
                    // let entry_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA;
                    let cdb_bytes = spec_u64_to_le_bytes(CDB_TRUE);
                    let cdb_addr = entry_offset + RELATIVE_POS_OF_VALID_CDB;
                    // let key_bytes = key.spec_serialize();
                    // let key_addr = entry_offset + RELATIVE_POS_OF_ENTRY_KEY;
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if cdb_addr <= pos < cdb_addr + 8 {
                            cdb_bytes[pos - cdb_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                OpLogEntryType::InvalidateMetadataEntry{list_metadata_index} => {
                    // In this case, we just have to flip the entry's CDB. We don't clear any other fields
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + list_metadata_index * table_entry_slot_size;
                    let cdb_addr = entry_offset + RELATIVE_POS_OF_VALID_CDB;
                    let cdb_bytes = spec_u64_to_le_bytes(CDB_FALSE);
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if cdb_addr <= pos < cdb_addr + 8 {
                            cdb_bytes[pos - cdb_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                _ => mem // all other ops do not modify the metadata table
            }
        }

        pub fn read_table_metadata<PM>(pm_regions: &PM, list_id: u128) -> (result: Result<&MetadataTableHeader, KvError<K, E>>)
            where
                PM: PersistentMemoryRegions,
            requires
                pm_regions.inv(),
                // TODO
            ensures
                match result {
                    Ok(output_metadata) => {
                        let metadata_size = ListEntryMetadata::spec_serialized_len();
                        let key_size = K::spec_serialized_len();
                        let metadata_slot_size = metadata_size + CRC_SIZE + key_size + CDB_SIZE;
                        &&& output_metadata.num_keys * metadata_slot_size <= u64::MAX
                        &&& ABSOLUTE_POS_OF_METADATA_TABLE + metadata_slot_size * output_metadata.num_keys  <= u64::MAX
                    }
                    Err(_) => true // TODO
                }
                // TODO
        {
            assume(false);

            let ghost mem = pm_regions@[0].committed();

            // read in the header and its CRC, check for corruption
            let metadata: &MetadataTableHeader = pm_regions.read_and_deserialize(0, ABSOLUTE_POS_OF_METADATA_HEADER);
            let metadata_crc = pm_regions.read_and_deserialize(0, ABSOLUTE_POS_OF_HEADER_CRC);

            if !check_crc_deserialized(metadata, metadata_crc, Ghost(mem),
                    Ghost(pm_regions.constants().impervious_to_corruption),
                    Ghost(ABSOLUTE_POS_OF_METADATA_HEADER), Ghost(LENGTH_OF_METADATA_HEADER),
                    Ghost(ABSOLUTE_POS_OF_HEADER_CRC)) {
                return Err(KvError::CRCMismatch);
            }

            // Since we've already checked for corruption, this condition will only fail
            // if the caller tries to use an L with a different size than the one
            // the list was originally set up with
            if {
                ||| metadata.version_number != METADATA_TABLE_VERSION_NUMBER
                ||| metadata.program_guid != METADATA_TABLE_PROGRAM_GUID
            } {
                return Err(KvError::InvalidListMetadata);
            }

            Ok(metadata)
        }

        // this uses the old PM approach but we will switch over to the new lens approach at some point
        pub exec fn setup<PM>(
            pm_regions: &mut PM,
            table_id: u128,
            num_keys: u64,
            list_element_size: u32,
            node_size: u32,
        ) -> (result: Result<(), KvError<K, E>>)
            where 
                PM: PersistentMemoryRegions,
            requires
                old(pm_regions).inv(),
                ({
                    let entry_slot_size = LENGTH_OF_ENTRY_METADATA_MINUS_KEY + CRC_SIZE + CDB_SIZE + K::spec_serialized_len();
                    &&& entry_slot_size <= u64::MAX
                    &&& ABSOLUTE_POS_OF_METADATA_TABLE + num_keys * entry_slot_size <= usize::MAX
                }),
                list_element_size + CRC_SIZE <= u32::MAX,
                // TODO 
            ensures 
                pm_regions.inv(),
                // TODO
        {
            // ensure that there are no outstanding writes
            pm_regions.flush();

            let region_sizes = get_region_sizes(pm_regions);
            let num_regions = region_sizes.len();
            if num_regions < 1 {
                return Err(KvError::TooFewRegions{ required: 1, actual: num_regions });
            } else if num_regions > 1 {
                return Err(KvError::TooManyRegions{ required: 1, actual: num_regions });
            }

            // check that the regions the caller passed in are sufficiently large
            let region_size = region_sizes[0];
            let entry_slot_size = LENGTH_OF_ENTRY_METADATA_MINUS_KEY + CRC_SIZE + CDB_SIZE + K::serialized_len();
            let required_region_size = ABSOLUTE_POS_OF_METADATA_TABLE + num_keys * entry_slot_size;
            if required_region_size > region_size {
                return Err(KvError::RegionTooSmall{ required: required_region_size as usize, actual: region_size as usize });
            }

            let full_list_element_size = list_element_size + CRC_SIZE as u32; 

            Self::write_setup_metadata(pm_regions, num_keys, full_list_element_size, node_size);

            // invalidate all of the entries
            for index in 0..num_keys 
                invariant
                    pm_regions.inv(),
            {
                assume(false);
                let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + index * entry_slot_size;
                pm_regions.serialize_and_write(0, entry_offset + RELATIVE_POS_OF_VALID_CDB, &CDB_FALSE);
            }

            pm_regions.flush();

            Ok(())
        }

        pub exec fn start<PM>(
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedMetadataPermission, PM>,
            table_id: u128,
            Tracked(perm): Tracked<&TrustedMetadataPermission>,
            Ghost(state): Ghost<MetadataTableView<K>>,
        ) -> (result: Result<Self, KvError<K, E>>)
            where 
                PM: PersistentMemoryRegions,
            requires 
                old(wrpm_regions).inv(),
                // TODO
            ensures 
                wrpm_regions.inv(),
                // TODO
        {
            assume(false);

            // 1. ensure that there are no outstanding writes
            wrpm_regions.flush();

            let pm_regions = wrpm_regions.get_pm_regions_ref();
            let ghost mem = pm_regions@[0].committed();

            // 2. check that the caller passed in a valid region. we do this in setup, but we check again here in case
            // the caller didn't also call setup
            let region_sizes = get_region_sizes(pm_regions);
            let num_regions = region_sizes.len();
            if num_regions < 1 {
                return Err(KvError::TooFewRegions{ required: 1, actual: num_regions });
            } else if num_regions > 1 {
                return Err(KvError::TooManyRegions{ required: 1, actual: num_regions });
            }

            // 3. read and check the header 
            let header = Self::read_header(pm_regions, table_id)?;

            // finish validity checks -- check that the regions the caller passed in are sufficiently large
            // we can't do this until after reading the header since it depends on the number of keys we expect
            // to be able to store
            let region_size = region_sizes[0];
            let entry_slot_size = LENGTH_OF_ENTRY_METADATA_MINUS_KEY + CRC_SIZE + CDB_SIZE + K::serialized_len();
            let required_region_size = ABSOLUTE_POS_OF_METADATA_TABLE + header.num_keys * entry_slot_size;
            if required_region_size > region_size {
                return Err(KvError::RegionTooSmall{ required: required_region_size as usize, actual: region_size as usize });
            }


            // 4. read valid bytes and construct the allocator 
            let mut metadata_allocator: Vec<u64> = Vec::with_capacity(header.num_keys as usize);
            for index in 0..header.num_keys 
                // TODO: invariant
            {
                assume(false);
                let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + index * entry_slot_size;
                let cdb_addr = entry_offset + RELATIVE_POS_OF_VALID_CDB;
                let cdb = pm_regions.read_and_deserialize(0, cdb_addr);
                match check_cdb(&cdb, Ghost(mem), Ghost(pm_regions.constants().impervious_to_corruption), Ghost(cdb_addr)) {
                    Some(false) => metadata_allocator.push(index),
                    Some(true) => {},
                    None => return Err(KvError::CRCMismatch),
                }
            }

            Ok(Self {
                metadata_table_free_list: metadata_allocator,
                state: Ghost(MetadataTableView::new(*header, parse_metadata_table(*header, mem).unwrap())),
                _phantom: None
            })
        }

        // Since metadata table entries have a valid CDB, we can tentatively write the whole entry and log a commit op for it,
        // then flip the CDB once the log has been committed
        pub exec fn tentative_create<PM>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedMetadataPermission, PM>,
            table_id: u128,
            list_node_index: u64,
            item_table_index: u64,
            key: &K,
            Tracked(perm): Tracked<&TrustedMetadataPermission>
        ) -> (result: Result<u64, KvError<K, E>>)
            where 
                PM: PersistentMemoryRegions,
            requires 
                old(wrpm_regions).inv(),
                // TODO
            ensures 
                wrpm_regions.inv(),
                // TODO
        {
            assume(false);

            // 1. pop an index from the free list
            // since this index is on the free list, its CDB is already false
            let free_index = match self.metadata_table_free_list.pop(){
                Some(index) => index,
                None => return Err(KvError::OutOfSpace),
            };

            // 2. construct the entry with list metadata and item index
            let entry = ListEntryMetadata::new(list_node_index, list_node_index, 0, 0, item_table_index);

            // 3. calculate the CRC of the entry + key 
            let mut digest = CrcDigest::new();
            digest.write(&entry);
            digest.write(key);
            let crc = digest.sum64();

            // 4. write CRC and entry 
            let entry_slot_size = LENGTH_OF_ENTRY_METADATA_MINUS_KEY + CRC_SIZE + CDB_SIZE + K::serialized_len();
            let slot_addr = ABSOLUTE_POS_OF_METADATA_TABLE + free_index * entry_slot_size;
            let crc_addr = slot_addr + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
            let entry_addr = slot_addr + RELATIVE_POS_OF_ENTRY_METADATA;
            let key_addr = slot_addr + RELATIVE_POS_OF_ENTRY_KEY;

            wrpm_regions.serialize_and_write(0, crc_addr, &crc, Tracked(perm));
            wrpm_regions.serialize_and_write(0, entry_addr, &entry, Tracked(perm));
            wrpm_regions.serialize_and_write(0, key_addr, key, Tracked(perm));

            Ok(free_index)
        }

        // Makes a slot valid by setting its valid CDB.
        // Must log the commit operation before calling this function.
        pub exec fn commit_entry<PM>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedMetadataPermission, PM>,
            table_id: u128,
            index: u64,
            Tracked(perm): Tracked<&TrustedMetadataPermission>
        ) -> (result: Result<(), KvError<K, E>>)
            where 
                PM: PersistentMemoryRegions,
            requires 
                old(wrpm_regions).inv(),
                // TODO
            ensures 
                wrpm_regions.inv(),
                // TODO
        {
            assume(false);

            let entry_slot_size = LENGTH_OF_ENTRY_METADATA_MINUS_KEY + CRC_SIZE + CDB_SIZE + K::serialized_len();
            let slot_addr = ABSOLUTE_POS_OF_METADATA_TABLE + index * entry_slot_size;
            let cdb_addr = slot_addr + RELATIVE_POS_OF_VALID_CDB;

            wrpm_regions.serialize_and_write(0, cdb_addr, &CDB_TRUE, Tracked(perm));

            Ok(())
        }

        pub exec fn invalidate_entry<PM>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedMetadataPermission, PM>,
            table_id: u128,
            index: u64,
            Tracked(perm): Tracked<&TrustedMetadataPermission>
        ) -> (result: Result<(), KvError<K, E>>)
            where 
                PM: PersistentMemoryRegions,
            requires 
                old(wrpm_regions).inv(),
                // TODO
            ensures 
                wrpm_regions.inv(),
                // TODO
        {
            assume(false);

            let entry_slot_size = LENGTH_OF_ENTRY_METADATA_MINUS_KEY + CRC_SIZE + CDB_SIZE + K::serialized_len();
            let slot_addr = ABSOLUTE_POS_OF_METADATA_TABLE + index * entry_slot_size;
            let cdb_addr = slot_addr + RELATIVE_POS_OF_VALID_CDB;

            wrpm_regions.serialize_and_write(0, cdb_addr, &CDB_FALSE, Tracked(perm));

            Ok(())
        }

        // Updates the list's length and the CRC of the entire entry. The caller must provide the CRC (either by calculating it
        // themselves or by reading it from a log entry).
        pub exec fn update_list_len<PM>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedMetadataPermission, PM>,
            table_id: u128,
            index: u64,
            new_length: u64,
            metadata_crc: u64,
            Tracked(perm): Tracked<&TrustedMetadataPermission>
        ) -> (result: Result<(), KvError<K, E>>)
            where 
                PM: PersistentMemoryRegions,
            requires 
                old(wrpm_regions).inv(),
                // TODO
            ensures 
                wrpm_regions.inv(),
                // TODO
        {
            assume(false);

            let entry_slot_size = LENGTH_OF_ENTRY_METADATA_MINUS_KEY + CRC_SIZE + CDB_SIZE + K::serialized_len();
            let slot_addr = ABSOLUTE_POS_OF_METADATA_TABLE + index * entry_slot_size;
            let crc_addr = slot_addr + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
            let len_addr = slot_addr + RELATIVE_POS_OF_ENTRY_METADATA_LENGTH;

            wrpm_regions.serialize_and_write(0, crc_addr, &metadata_crc, Tracked(perm));
            wrpm_regions.serialize_and_write(0, len_addr, &new_length, Tracked(perm));

            Ok(())
        }

        pub exec fn trim_list<PM>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedMetadataPermission, PM>,
            table_id: u128,
            index: u64,
            new_head: u64,
            new_len: u64,
            new_list_start_index: u64,
            metadata_crc: u64,
            Tracked(perm): Tracked<&TrustedMetadataPermission>
        ) -> (result: Result<(), KvError<K, E>>) 
            where 
                PM: PersistentMemoryRegions,
            requires 
                old(wrpm_regions).inv(),
                // TODO
            ensures 
                wrpm_regions.inv(),
                // TODO
        {
            assume(false);

            let entry_slot_size = LENGTH_OF_ENTRY_METADATA_MINUS_KEY + CRC_SIZE + CDB_SIZE + K::serialized_len();
            let slot_addr = ABSOLUTE_POS_OF_METADATA_TABLE + index * entry_slot_size;
            let crc_addr = slot_addr + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
            let head_addr = slot_addr + RELATIVE_POS_OF_ENTRY_METADATA_HEAD;
            let len_addr = slot_addr + RELATIVE_POS_OF_ENTRY_METADATA_LENGTH;
            let start_index_addr = slot_addr + RELATIVE_POS_OF_ENTRY_METADATA_FIRST_OFFSET;

            wrpm_regions.serialize_and_write(0, crc_addr, &metadata_crc, Tracked(perm));
            wrpm_regions.serialize_and_write(0, head_addr, &new_head, Tracked(perm));
            wrpm_regions.serialize_and_write(0, len_addr, &new_len, Tracked(perm));
            wrpm_regions.serialize_and_write(0, start_index_addr, &new_list_start_index, Tracked(perm));

            Ok(())
        }

        exec fn write_setup_metadata<PM>(
            pm_regions: &mut PM, 
            num_keys: u64, 
            list_element_size: u32, 
            list_node_size: u32,
        )
            where 
                PM: PersistentMemoryRegions,
            requires 
                old(pm_regions).inv(),
                // TODO
                // region is large enough
            ensures 
                pm_regions.inv(),
                // TODO
        {
            assume(false);

            // initialize header and compute crc
            let header = MetadataTableHeader {
                element_size: list_element_size,
                node_size: list_node_size, 
                num_keys: num_keys,
                version_number: METADATA_TABLE_VERSION_NUMBER,
                _padding: 0,
                program_guid: METADATA_TABLE_PROGRAM_GUID,
            };
            let header_crc = calculate_crc(&header);

            pm_regions.serialize_and_write(0, ABSOLUTE_POS_OF_METADATA_HEADER, &header);
            pm_regions.serialize_and_write(0, ABSOLUTE_POS_OF_HEADER_CRC, &header_crc);
        }

        exec fn read_header<PM>(
            pm_regions: &PM,
            table_id: u128
        ) -> (result: Result<&MetadataTableHeader, KvError<K, E>>)
            where 
                PM: PersistentMemoryRegions,
            requires 
                pm_regions.inv(),
                // TODO
            ensures 
                // TODO
        {
            assume(false);

            let ghost mem = pm_regions@[0].committed();

            let header: &MetadataTableHeader = pm_regions.read_and_deserialize(0, ABSOLUTE_POS_OF_METADATA_HEADER);
            let header_crc: &u64 = pm_regions.read_and_deserialize(0, ABSOLUTE_POS_OF_HEADER_CRC);

            // check the CRC
            if !check_crc_deserialized(header, header_crc, Ghost(mem),
                    Ghost(pm_regions.constants().impervious_to_corruption),
                    Ghost(ABSOLUTE_POS_OF_METADATA_HEADER), Ghost(LENGTH_OF_METADATA_HEADER),
                    Ghost(ABSOLUTE_POS_OF_HEADER_CRC)) {
                return Err(KvError::CRCMismatch);
            }   

            // check that the contents of the header make sense; since we've already checked for corruption,
            // these checks should never fail
            if {
                ||| header.program_guid != METADATA_TABLE_PROGRAM_GUID 
                ||| header.version_number != METADATA_TABLE_VERSION_NUMBER
            } {
                Err(KvError::InvalidListMetadata)
            } else {
                Ok(header)
            }
        }
    }
}