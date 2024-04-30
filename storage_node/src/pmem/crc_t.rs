use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

use deps_hack::crc64fast::Digest;

verus! {

    // Calculates the CRC for a single `Serializable` object.
    #[verifier::external_body]
    pub fn calculate_crc<S>(val: &S) -> (out: u64)
        where
            S: Serializable + Sized
        ensures
            val.spec_crc() == out,
            spec_u64_from_le_bytes(spec_crc_bytes(val.spec_serialize())) == out,
    {
        let num_bytes: usize = S::serialized_len().try_into().unwrap();
        let s_pointer = val as *const S;
        let bytes_pointer = s_pointer as *const u8;
        // SAFETY: `bytes_pointer` always points to `num_bytes` consecutive, initialized
        // bytes because it was obtained by casting a regular Rust object reference
        // to a raw pointer.
        let bytes = unsafe {
            std::slice::from_raw_parts(bytes_pointer, num_bytes)
        };

        let mut digest = Digest::new();
        digest.write(bytes);
        digest.sum64()
    }

    // Helper struct to hide the external crc64fast Digest type
    // from Verus while still keeping ghost state associated with it
    #[verifier::external_body]
    struct ExternalDigest
    {
        digest: Digest
    }

    // A structure for obtaining CRCs of multiple serializable objects
    // and writing proofs about them.
    pub struct CrcDigest
    {
        digest: ExternalDigest,
        bytes_in_digest: Ghost<Seq<Seq<u8>>>,
    }

    impl CrcDigest
    {
        pub closed spec fn bytes_in_digest(self) -> Seq<Seq<u8>>
        {
            self.bytes_in_digest@
        }

        #[verifier::external_body]
        pub fn new() -> (output: Self)
            ensures
                output.bytes_in_digest() == Seq::<Seq<u8>>::empty()
        {
            Self {
                digest: ExternalDigest{ digest: Digest::new() },
                bytes_in_digest: Ghost(Seq::<Seq<u8>>::empty())
            }
        }

        #[verifier::external_body]
        pub fn write<S>(&mut self, val: &S)
            where
                S: Serializable
            requires

            ensures
                self.bytes_in_digest() == old(self).bytes_in_digest().push(val.spec_serialize())
        {
            // Cast `val` to bytes, then add them to the digest.
            // The crc64fast crate that we use computes the CRC iteratively and does
            // not store copies of the bytes we write to the digest, so this
            // will (hopefully) not incur any copying beyond what is directly
            // necessary to compute the CRC.
            let num_bytes: usize = S::serialized_len().try_into().unwrap();
            let s_pointer = val as *const S;
            let bytes_pointer = s_pointer as *const u8;
            // SAFETY: `bytes_pointer` always points to `num_bytes` consecutive, initialized
            // bytes because it was obtained by casting a regular Rust object reference
            // to a raw pointer.
            let bytes = unsafe {
                std::slice::from_raw_parts(bytes_pointer, num_bytes)
            };
            self.digest.digest.write(bytes);
        }

        // Compute and return the CRC for all bytes in the digest.
        #[verifier::external_body]
        pub fn sum64(&self) -> (output: u64)
            ensures
                ({
                    let all_bytes_seq = self.bytes_in_digest().flatten();
                    &&& output == spec_u64_from_le_bytes(spec_crc_bytes(all_bytes_seq))
                    // &&& output == Self::spec_sum64(all_bytes_seq)
                })

        {
            self.digest.digest.sum64()
        }

        // pub closed spec fn spec_sum64(bytes: Seq<u8>) -> u64;
    }
}
