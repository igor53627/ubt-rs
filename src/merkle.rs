//! Merkle hashing shared by [`StemNode`](crate::StemNode),
//! [`UnifiedBinaryTree`](crate::UnifiedBinaryTree), and
//! [`StreamingTreeBuilder`](crate::StreamingTreeBuilder).

use alloy_primitives::B256;
use std::collections::HashMap;

use crate::{error::Result, Hasher, Stem, SubIndex, UbtError, STEM_LEN};

/// Maximum tree depth (248 bits = 31 bytes * 8)
pub(crate) const MAX_DEPTH: usize = STEM_LEN * 8;

/// Minimum number of stems before using parallel processing.
/// Below this threshold, sequential processing is faster due to rayon overhead.
#[cfg(feature = "parallel")]
pub(crate) const PARALLEL_STEM_THRESHOLD: usize = 100;

/// Compute the hash of a stem node per the go-ethereum algorithm:
/// 1. Hash each present value individually. A zero value is present and is hashed;
///    an absent subindex contributes zero.
/// 2. Build 8-level binary tree (256 leaves)
/// 3. `hash(stem || 0x00 || subtree_root)`
///
/// A stem with no values hashes to `B256::ZERO`, so that it contributes nothing to
/// the root, the same as an absent stem. go-ethereum cannot have such a stem node.
pub(crate) fn hash_stem_values<H: Hasher>(
    hasher: &H,
    stem: &Stem,
    values: &HashMap<SubIndex, B256>,
) -> B256 {
    if values.is_empty() {
        return B256::ZERO;
    }

    let mut data: [B256; 256] = [B256::ZERO; 256];
    for (&idx, value) in values {
        data[usize::from(idx)] = hasher.hash_32(value);
    }

    for level in 1..=8 {
        let pairs: usize = 256 >> level;
        for i in 0..pairs {
            let left: B256 = data[i * 2];
            let right: B256 = data[i * 2 + 1];
            data[i] = hasher.hash_64(&left, &right);
        }
    }

    hasher.hash_stem_node(stem.as_bytes(), &data[0])
}

/// Compute the root hash from a slice of `(stem, stem_hash)` pairs sorted by stem.
///
/// The slice must contain only stems that share their first `depth` bits.
/// A subtree with one stem hashes to that stem's hash; a subtree with more stems
/// hashes to `hash_64(left, right)`, where an empty side contributes zero.
///
/// # Errors
///
/// Returns [`UbtError::TreeDepthExceeded`] if two or more stems remain at `MAX_DEPTH`,
/// which indicates duplicate stems.
pub(crate) fn root_from_sorted_stem_hashes<H: Hasher>(
    hasher: &H,
    stem_hashes: &[(Stem, B256)],
    depth: usize,
) -> Result<B256> {
    if stem_hashes.is_empty() {
        return Ok(B256::ZERO);
    }

    if stem_hashes.len() == 1 {
        return Ok(stem_hashes[0].1);
    }

    if depth >= MAX_DEPTH {
        return Err(UbtError::TreeDepthExceeded { depth });
    }

    // Stems are sorted, so all stems with bit 0 at this depth come before all stems with bit 1.
    let split_point: usize = stem_hashes.partition_point(|(s, _)| !s.bit_at(depth));
    let (left, right) = stem_hashes.split_at(split_point);

    let left_hash: B256 = root_from_sorted_stem_hashes(hasher, left, depth + 1)?;
    let right_hash: B256 = root_from_sorted_stem_hashes(hasher, right, depth + 1)?;

    if left_hash.is_zero() && right_hash.is_zero() {
        Ok(B256::ZERO)
    } else {
        Ok(hasher.hash_64(&left_hash, &right_hash))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Blake3Hasher;

    #[test]
    fn test_tree_depth_exceeded_returns_error() {
        let stem1 = Stem::new([0u8; 31]);
        let mut stem2_bytes = [0u8; 31];
        stem2_bytes[0] = 1;
        let stem2 = Stem::new(stem2_bytes);
        let stem_hashes = vec![(stem1, B256::repeat_byte(1)), (stem2, B256::repeat_byte(2))];

        let err = root_from_sorted_stem_hashes(&Blake3Hasher, &stem_hashes, MAX_DEPTH).unwrap_err();
        assert!(matches!(err, UbtError::TreeDepthExceeded { depth } if depth == MAX_DEPTH));
    }
}
