//! Hash function abstraction for the UBT.
//!
//! The hash function is not final per EIP-7864. This module provides a trait
//! abstraction so different hash functions can be used.
//!
//! Per go-ethereum reference implementation, SHA256 is used for tree hashing.

use alloy_primitives::B256;
use sha2::{Digest, Sha256};

/// Trait for hash functions used in the UBT.
///
/// Per EIP-7864, the hash function has a special rule for a 64-byte input:
/// - `hash([0x00] * 64) = [0x00] * 32` (an empty pair produces the zero hash)
/// - For all other inputs, use the underlying hash function
///
/// The rule does not apply to a leaf value. As in go-ethereum `trie/bintrie`, a leaf
/// that holds 32 zero bytes is present, and its hash is the hash of those 32 bytes.
///
/// # Implementing this trait
///
/// The crate does not apply the zero rule for the implementation. The contract is:
///
/// - [`hash_32`](Self::hash_32) has no zero rule. It must return the hash of the 32
///   input bytes for every input, including `B256::ZERO`. An implementation that
///   returns `B256::ZERO` for a zero value makes a present zero leaf equal to an
///   absent leaf, and gives root hashes that do not agree with go-ethereum.
/// - [`hash_64`](Self::hash_64) must return `B256::ZERO` when both inputs are zero.
///   [`StemNode::hash`](crate::StemNode::hash) calls `hash_64` for every pair of nodes
///   in the 256-leaf subtree, including the empty pairs, so an implementation without
///   the rule gives hashes that do not agree with EIP-7864.
/// - [`hash_raw`](Self::hash_raw) returns `B256::ZERO` when every input byte is zero,
///   as [`Sha256Hasher`] and [`Blake3Hasher`] do.
/// - A zero hash means "empty subtree" in the whole crate: in the root hash, in
///   [`StemNode::hash`](crate::StemNode::hash), and in
///   [`Proof::compute_root`](crate::Proof::compute_root). `hash_32` must not return
///   `B256::ZERO`, and `hash_64` must not return `B256::ZERO` unless both inputs are
///   zero. For a cryptographic hash function this holds unless a preimage of zero is
///   found. With an implementation that breaks this rule, a present leaf can hash
///   as an absent leaf, and a proof from
///   [`generate_stem_proof`](crate::generate_stem_proof) for a stem node whose
///   subtree root is zero does not reconstruct `StemNode::hash`.
///
/// # Thread Safety
///
/// This trait is always `Send + Sync` so that hashers can be used safely in
/// parallel contexts (e.g. stem hashing via the `"parallel"` feature with rayon).
/// Custom hasher implementations must be thread-safe.
pub trait Hasher: Clone + Default + Send + Sync {
    /// Hash a 32-byte value (for leaf nodes).
    ///
    /// There is no zero rule: `hash_32(&B256::ZERO)` is the hash of 32 zero bytes.
    fn hash_32(&self, value: &B256) -> B256;

    /// Hash a 64-byte value (for internal nodes: `left_hash` || `right_hash`).
    ///
    /// Returns `B256::ZERO` when both inputs are zero.
    fn hash_64(&self, left: &B256, right: &B256) -> B256;

    /// Hash for stem node: `hash(stem || 0x00 || subtree_root)`
    fn hash_stem_node(&self, stem: &[u8; 31], subtree_root: &B256) -> B256 {
        let mut input = [0u8; 64];
        input[..31].copy_from_slice(stem);
        input[31] = 0x00;
        input[32..].copy_from_slice(subtree_root.as_slice());

        self.hash_raw(&input)
    }

    /// Raw hash of arbitrary input
    fn hash_raw(&self, input: &[u8]) -> B256;
}

/// SHA256-based hasher (go-ethereum compatible).
///
/// This matches the go-ethereum bintrie implementation.
#[derive(Clone, Debug, Default)]
pub struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn hash_32(&self, value: &B256) -> B256 {
        B256::from_slice(&Sha256::digest(value.as_slice()))
    }

    fn hash_64(&self, left: &B256, right: &B256) -> B256 {
        if left.is_zero() && right.is_zero() {
            return B256::ZERO;
        }

        let mut hasher = Sha256::new();
        hasher.update(left.as_slice());
        hasher.update(right.as_slice());
        B256::from_slice(&hasher.finalize())
    }

    fn hash_raw(&self, input: &[u8]) -> B256 {
        if input.iter().all(|&b| b == 0) {
            return B256::ZERO;
        }
        B256::from_slice(&Sha256::digest(input))
    }
}

/// BLAKE3-based hasher (reference implementation).
///
/// **Note**: BLAKE3 is used for development/experimentation. The final hash function
/// for EIP-7864 is TBD (candidates: Keccak, Poseidon2).
#[derive(Clone, Debug, Default)]
pub struct Blake3Hasher;

impl Hasher for Blake3Hasher {
    fn hash_32(&self, value: &B256) -> B256 {
        B256::from_slice(blake3::hash(value.as_slice()).as_bytes())
    }

    fn hash_64(&self, left: &B256, right: &B256) -> B256 {
        if left.is_zero() && right.is_zero() {
            return B256::ZERO;
        }

        let mut input = [0u8; 64];
        input[..32].copy_from_slice(left.as_slice());
        input[32..].copy_from_slice(right.as_slice());

        B256::from_slice(blake3::hash(&input).as_bytes())
    }

    fn hash_raw(&self, input: &[u8]) -> B256 {
        if input.iter().all(|&b| b == 0) {
            return B256::ZERO;
        }
        B256::from_slice(blake3::hash(input).as_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex_literal(s: &str) -> [u8; 32] {
        let mut out = [0u8; 32];
        hex::decode_to_slice(s, &mut out).expect("valid hex");
        out
    }

    /// `hash_64` and `hash_raw` keep the zero rule. `hash_32` has no zero rule:
    /// the expected value is the SHA-256 digest of 32 zero bytes.
    #[test]
    fn test_zero_hash_special_case_sha256() {
        let hasher = Sha256Hasher;
        let sha256_of_zero32: B256 = B256::from(hex_literal(
            "66687aadf862bd776c8fc18b8e9f8e20089714856ee233b3902a591d0d5f2925",
        ));

        assert_eq!(hasher.hash_32(&B256::ZERO), sha256_of_zero32);
        assert_eq!(hasher.hash_64(&B256::ZERO, &B256::ZERO), B256::ZERO);
        assert_eq!(hasher.hash_raw(&[0u8; 64]), B256::ZERO);
    }

    #[test]
    fn test_zero_hash_special_case_blake3() {
        let hasher = Blake3Hasher;
        let blake3_of_zero32: B256 = B256::from(*blake3::hash(&[0u8; 32]).as_bytes());

        assert_ne!(blake3_of_zero32, B256::ZERO);
        assert_eq!(hasher.hash_32(&B256::ZERO), blake3_of_zero32);
        assert_eq!(hasher.hash_64(&B256::ZERO, &B256::ZERO), B256::ZERO);
        assert_eq!(hasher.hash_raw(&[0u8; 64]), B256::ZERO);
    }

    #[test]
    fn test_non_zero_hash_sha256() {
        let hasher = Sha256Hasher;
        let value = B256::repeat_byte(0x42);

        let hash = hasher.hash_32(&value);
        assert_ne!(hash, B256::ZERO);

        let hash2 = hasher.hash_64(&value, &B256::ZERO);
        assert_ne!(hash2, B256::ZERO);
    }

    #[test]
    fn test_non_zero_hash_blake3() {
        let hasher = Blake3Hasher;
        let value = B256::repeat_byte(0x42);

        let hash = hasher.hash_32(&value);
        assert_ne!(hash, B256::ZERO);

        let hash2 = hasher.hash_64(&value, &B256::ZERO);
        assert_ne!(hash2, B256::ZERO);
    }

    #[test]
    fn test_sha256_deterministic() {
        let hasher = Sha256Hasher;
        let value = B256::repeat_byte(0x42);

        let hash1 = hasher.hash_32(&value);
        let hash2 = hasher.hash_32(&value);
        assert_eq!(hash1, hash2);
    }
}
