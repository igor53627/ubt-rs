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
/// Per EIP-7864, the hash function has special rules:
/// - `hash([0x00] * 64) = [0x00] * 32` (empty input produces zero hash)
/// - For all other inputs, use the underlying hash function
///
/// # Thread Safety
///
/// This trait is always `Send + Sync` so that hashers can be used safely in
/// parallel contexts (e.g. stem hashing via the `"parallel"` feature with rayon).
/// Custom hasher implementations must be thread-safe.
pub trait Hasher: Clone + Default + Send + Sync {
    /// Hash a 32-byte value (for leaf nodes)
    fn hash_32(&self, value: &B256) -> B256;

    /// Hash a 64-byte value (for internal nodes: `left_hash` || `right_hash`)
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
#[derive(Clone, Default)]
pub struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn hash_32(&self, value: &B256) -> B256 {
        if value.is_zero() {
            return B256::ZERO;
        }
        let hash = Sha256::digest(value.as_slice());
        B256::from_slice(&hash)
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
#[derive(Clone, Default)]
pub struct Blake3Hasher;

impl Hasher for Blake3Hasher {
    fn hash_32(&self, value: &B256) -> B256 {
        if value.is_zero() {
            return B256::ZERO;
        }
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

    #[test]
    fn test_zero_hash_special_case_sha256() {
        let hasher = Sha256Hasher;

        assert_eq!(hasher.hash_32(&B256::ZERO), B256::ZERO);
        assert_eq!(hasher.hash_64(&B256::ZERO, &B256::ZERO), B256::ZERO);
    }

    #[test]
    fn test_zero_hash_special_case_blake3() {
        let hasher = Blake3Hasher;

        assert_eq!(hasher.hash_32(&B256::ZERO), B256::ZERO);
        assert_eq!(hasher.hash_64(&B256::ZERO, &B256::ZERO), B256::ZERO);
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
