//! This file contains the definitions and `Serializable`
//! implementations for various log entry types for the
//! durable store. These are trusted because their structure,
//! and `Serializable` implementations, need to be manually
//! audited to ensure they accurately reflect their
//! byte-level Rust representations.
//!
//! TODO: the organization of this file and of logentry_v doesn't make much sense;
//! move things so that they are in the correct _t or _v file.

use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;
use vstd::ptr::*;

use crate::kv::durable::logentry_v::*;
use crate::pmem::serialization_t::*;
use crate::pmem::markers_t::PmSafe;
use deps_hack::PmSafe;

verus! {

    // Enum representing different op log entry types.
    // The concrete types we write to the log are not enums so that we have more control 
    // over layout; this enum is used represent log entries in ghost code and in DRAM 
    // during log replay
    pub enum OpLogEntryType<L>
        where
            L: Serializable
    {
        ItemTableEntryCommit { 
            item_index: u64,
            metadata_index: u64,
            metadata_crc: u64,
        },
        ItemTableEntryInvalidate { item_index: u64 },
        AppendListNode {
            metadata_index: u64,
            old_tail: u64,
            new_tail: u64,
            metadata_crc: u64,
        },
        InsertListElement {
            node_offset: u64,
            index_in_node: u64,
            list_element: L
        },
        UpdateListLen {
            metadata_index: u64,
            new_length: u64,
            metadata_crc: u64,
        },
        TrimList {
            metadata_index: u64,
            new_head_node: u64,
            new_list_len: u64,
            new_list_start_index: u64,
            metadata_crc: u64,
        },
        CommitMetadataEntry {
            metadata_index: u64,
            item_index: u64,
        },
        InvalidateMetadataEntry {
            metadata_index: u64,
        }
    }

    // TODO: documentation
    #[repr(C)]
    #[derive(PmSafe, Copy, Clone)]
    pub struct CommitItemEntry {
        pub entry_type: u64,
        pub item_index: u64,
        pub metadata_index: u64,
        pub metadata_crc: u64,
    }

    impl Serializable for CommitItemEntry {}

    #[repr(C)]
    #[derive(PmSafe, Copy, Clone)]
    pub struct InvalidateItemEntry {
        pub entry_type: u64,
        pub item_index: u64,
    }

    impl Serializable for InvalidateItemEntry {}

    // This log entry represents an operation that appends a new list node
    // (i.e., an array of list elements, plus a next pointer and CRC) to
    // the list associated with the index at `metadata_index`.
    //
    // Writing this entry to the log should be preceded by the allocation
    // of the new tail node (i.e., setting its next pointer to null and updating
    // its CRC accordingly).
    //
    // When this log entry is replayed:
    // 1) the old tail node of the specified list has its next pointer set
    //    to the specified node and its CRC updated accordingly
    // 2) the tail field and CRC of the associated list metadata structure
    //    are updated
    //
    // This entry records both the old and new tail values to ensure that replaying
    // this log entry is idempotent in cases where the list metadata struct's tail
    // field was updated before this entry is replayed.
    #[repr(C)]
    #[derive(PmSafe, Copy, Clone)]
    pub struct AppendListNodeEntry {
        pub entry_type: u64,
        pub metadata_index: u64,
        pub old_tail: u64,
        pub new_tail: u64,
        pub metadata_crc: u64,
    }

    impl Serializable for AppendListNodeEntry {}

    // This log entry represents an operation that writes a new list element
    // to the specified index in the specified ULL node. Note that the index
    // refers to the index in the list node's array, NOT the logical list
    // index that this operation updates.
    //
    // This type of log entry must contain the new list element to write, as
    // the insertion may update a live list element, which is a commiting update.
    // To avoid extra in-memory copying of the list element, we do not include
    // it directly in this structure.
    //
    // When this log entry is replayed:
    // 1) the list element immediately following it in the log is copied to
    //    the specified index in the specified list node.
    //
    // Note that this log entry type does not need to be used for appends.
    // Appending a new list element is a tentative update, as it is modifying
    // a list element outside the current bounds of the list, so it doesn't have
    // to be logged. This entry type only needs to be used for in-place updates
    // of in-bounds indices.
    #[repr(C)]
    #[derive(PmSafe, Copy, Clone)]
    pub struct InsertListElementEntry {
        pub entry_type: u64,
        pub node_offset: u64,
        pub index_in_node: u64,
    }

    impl Serializable for InsertListElementEntry {}

    // This log entry represents an update to a list's length field
    // in its metadata structure. The log entry should contain the actual
    // new length (not a number to add or subtract from the existing length)
    // to ensure that log replay is idempotent.
    //
    // When this log entry is replayed:
    // 1) The list metadata structure at the specified index has its length
    //    field updated to `new_length` and its CRC updated accordingly.
    //
    // This log entry acts as the committing write for list append operations.
    // The new list element should be written tentatively to an out-of-bounds
    // slot; it will become visible when the list length update is applied.
    #[repr(C)]
    #[derive(PmSafe, Copy, Clone)]
    pub struct UpdateListLenEntry {
        pub entry_type: u64,
        pub metadata_index: u64,
        pub new_length: u64,
        pub metadata_crc: u64
    }


    impl Serializable for UpdateListLenEntry {}

    // This log entry represents a list trim operation. It includes the
    // values with which to update the corresponding list metadata structure,
    // not the arguments passed in by the user.
    // When this log entry is replayed:
    // 1) The list metadata structure at the specified index has its head,
    //    length, and start index fields updated with those in the log entry,
    //    as well as a corresponding CRC update.
    #[repr(C)]
    #[derive(PmSafe, Copy, Clone)]
    pub struct TrimListEntry {
        pub entry_type: u64,
        pub metadata_index: u64,
        pub new_head_node: u64,
        pub new_list_len: u64,
        pub new_list_start_index: u64,
        pub metadata_crc: u64, 
    }

    impl Serializable for TrimListEntry {}

    #[repr(C)]
    #[derive(PmSafe, Copy, Clone)]
    pub struct CommitMetadataEntry 
    {
        pub entry_type: u64,
        pub metadata_index: u64,
        pub item_index: u64, // committing a metadata entry implies committing its item
    }

    impl CommitMetadataEntry 
    {
        pub exec fn new(metadata_index: u64, item_index: u64) -> Self 
        {
            Self {
                entry_type: COMMIT_METADATA_ENTRY,
                metadata_index,
                item_index,
            }
        }
    }

    impl Serializable for CommitMetadataEntry {}

    #[repr(C)]
    #[derive(PmSafe, Copy, Clone)]
    pub struct InvalidateMetadataEntry
    {
        pub entry_type: u64,
        pub metadata_index: u64,
    }

    impl Serializable for InvalidateMetadataEntry {}
}
