//! Streaming tree builder for memory-efficient root hash computation.
//!
//! This module provides [`StreamingTreeBuilder`], a way to compute the UBT root hash
//! by streaming through sorted entries without keeping the full tree in memory.
//!
//! # When to Use
//!
//! - **Migrations**: When building a tree from scratch (e.g., MPT -> UBT migration)
//! - **Memory-constrained environments**: When RAM is limited relative to state size
//! - **One-shot computation**: When you need only the root hash, not the tree structure
//!
//! For ongoing state maintenance, use [`crate::UnifiedBinaryTree`] instead.
//!
//! # Parallel vs Serial
//!
//! Two methods are available:
//! - [`StreamingTreeBuilder::build_root_hash`]: Serial stem hashing
//! - [`StreamingTreeBuilder::build_root_hash_parallel`]: Parallel stem hashing (requires `parallel` feature)
//!
//! The parallel version groups entries by stem serially (O(n) streaming), then
//! computes stem hashes concurrently via rayon.

use alloy_primitives::B256;
use std::collections::HashMap;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::{error::Result, Blake3Hasher, Hasher, Stem, SubIndex, TreeKey, UbtError, STEM_LEN};

/// A streaming tree builder that computes root hash with minimal memory.
///
/// This builder is designed for one-shot root hash computation from sorted entries,
/// such as during migrations or state verification.
///
/// # Usage
///
/// 1. Sort all `(TreeKey, B256)` entries by key (stem, then subindex) in lexicographic order
/// 2. Call [`build_root_hash`](Self::build_root_hash) or [`build_root_hash_parallel`](Self::build_root_hash_parallel)
/// 3. Receive the root hash without keeping the full tree in memory
///
/// # Memory Usage
///
/// Memory usage is O(num_stems + tree_depth) instead of O(num_entries), since:
/// - We keep one `Vec<(Stem, B256)>` of stem hashes (one per unique stem)
/// - We use slice-based recursion with no additional allocations
///
/// # Sorting Requirement
///
/// Entries **MUST** be sorted by `(stem, subindex)` in lexicographic order for:
/// - Correct stem grouping (entries with same stem must be consecutive)
/// - Deterministic root hash (sorted stem order ensures canonical tree shape)
///
/// In debug builds, strict ascending order is asserted. Duplicate keys are not allowed.
///
/// # Example
///
/// ```rust
/// use ubt::{StreamingTreeBuilder, TreeKey, Blake3Hasher, B256, Stem};
///
/// let mut entries: Vec<(TreeKey, B256)> = vec![
///     (TreeKey::new(Stem::new([0u8; 31]), 0), B256::repeat_byte(0x01)),
///     (TreeKey::new(Stem::new([0u8; 31]), 1), B256::repeat_byte(0x02)),
/// ];
/// entries.sort_by(|a, b| (a.0.stem, a.0.subindex).cmp(&(b.0.stem, b.0.subindex)));
///
/// let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
/// let root = builder.build_root_hash(entries).unwrap();
/// ```
pub struct StreamingTreeBuilder<H: Hasher = Blake3Hasher> {
    hasher: H,
}

impl<H: Hasher> Default for StreamingTreeBuilder<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: Hasher> StreamingTreeBuilder<H> {
    /// Create a new streaming builder with default hasher.
    pub fn new() -> Self {
        Self {
            hasher: H::default(),
        }
    }

    /// Create a new streaming builder with custom hasher.
    pub fn with_hasher(hasher: H) -> Self {
        Self { hasher }
    }

    /// Build the root hash from a sorted iterator of (TreeKey, B256) entries.
    ///
    /// The entries MUST be sorted by (stem, subindex) in lexicographic order.
    /// In debug builds, this is asserted.
    ///
    /// Returns B256::ZERO for empty input.
    pub fn build_root_hash(&self, entries: impl IntoIterator<Item = (TreeKey, B256)>) -> Result<B256> {
        let mut entries_iter = entries.into_iter().peekable();

        if entries_iter.peek().is_none() {
            return Ok(B256::ZERO);
        }

        // Group entries by stem and compute stem hashes
        let stem_hashes = self.collect_stem_hashes(&mut entries_iter);

        if stem_hashes.is_empty() {
            return Ok(B256::ZERO);
        }

        // Build tree from stem hashes (sorted by stem since entries were sorted)
        self.build_tree_hash(&stem_hashes, 0)
    }

    /// Build the root hash using parallel stem hashing.
    ///
    /// This method uses rayon to compute stem hashes in parallel, which can significantly
    /// speed up computation for large state with many unique stems.
    ///
    /// # Algorithm
    ///
    /// 1. **Serial grouping**: Stream through sorted entries, grouping by stem (O(n))
    /// 2. **Parallel hashing**: Compute stem hashes concurrently via rayon (O(n/p) with p threads)
    /// 3. **Serial tree build**: Build tree hash from sorted stem hashes (O(S) for S stems)
    ///
    /// # Requirements
    ///
    /// - Entries MUST be sorted by `(stem, subindex)` in lexicographic order
    /// - In debug builds, strict ascending order is asserted
    ///
    /// Returns `B256::ZERO` for empty input.
    ///
    /// # Feature Flag
    ///
    /// Requires the `parallel` feature (enabled by default).
    #[cfg(feature = "parallel")]
    pub fn build_root_hash_parallel(
        &self,
        entries: impl IntoIterator<Item = (TreeKey, B256)>,
    ) -> Result<B256> {
        let mut entries_iter = entries.into_iter().peekable();

        if entries_iter.peek().is_none() {
            return Ok(B256::ZERO);
        }

        // Group entries by stem (serial - streaming through sorted entries)
        let stem_groups = self.collect_stem_groups(&mut entries_iter);

        if stem_groups.is_empty() {
            return Ok(B256::ZERO);
        }

        // Compute stem hashes in parallel
        let mut stem_hashes: Vec<(Stem, B256)> = stem_groups
            .into_par_iter()
            .map(|(stem, values)| {
                let hash = self.compute_stem_hash(&stem, &values);
                (stem, hash)
            })
            .collect();

        // Sort by stem for deterministic order (parallel collect doesn't preserve order)
        stem_hashes.sort_by(|a, b| a.0.cmp(&b.0));

        // Build tree from stem hashes (serial - O(n) and fast)
        self.build_tree_hash(&stem_hashes, 0)
    }

    /// Collect entries grouped by stem without computing hashes.
    /// Used by parallel version to separate grouping from hashing.
    #[cfg(feature = "parallel")]
    fn collect_stem_groups<I: Iterator<Item = (TreeKey, B256)>>(
        &self,
        entries: &mut std::iter::Peekable<I>,
    ) -> Vec<(Stem, HashMap<SubIndex, B256>)> {
        let mut stem_groups: Vec<(Stem, HashMap<SubIndex, B256>)> = Vec::new();
        let mut current_stem: Option<Stem> = None;
        let mut current_values: HashMap<SubIndex, B256> = HashMap::new();

        #[cfg(debug_assertions)]
        let mut prev_key: Option<TreeKey> = None;

        for (key, value) in entries.by_ref() {
            #[cfg(debug_assertions)]
            {
                if let Some(prev) = prev_key {
                    debug_assert!(
                        (prev.stem, prev.subindex) < (key.stem, key.subindex),
                        "Entries must be sorted: {:?} should come before {:?}",
                        prev,
                        key
                    );
                }
                prev_key = Some(key);
            }

            match current_stem {
                Some(stem) if stem == key.stem => {
                    // Same stem, accumulate value
                    if !value.is_zero() {
                        current_values.insert(key.subindex, value);
                    }
                }
                Some(stem) => {
                    // New stem, finalize previous
                    if !current_values.is_empty() {
                        stem_groups.push((stem, std::mem::take(&mut current_values)));
                    }
                    // Start new stem
                    current_stem = Some(key.stem);
                    if !value.is_zero() {
                        current_values.insert(key.subindex, value);
                    }
                }
                None => {
                    // First stem
                    current_stem = Some(key.stem);
                    if !value.is_zero() {
                        current_values.insert(key.subindex, value);
                    }
                }
            }
        }

        // Finalize last stem
        if let Some(stem) = current_stem {
            if !current_values.is_empty() {
                stem_groups.push((stem, current_values));
            }
        }

        stem_groups
    }

    /// Collect all entries grouped by stem, compute hash for each stem.
    fn collect_stem_hashes<I: Iterator<Item = (TreeKey, B256)>>(
        &self,
        entries: &mut std::iter::Peekable<I>,
    ) -> Vec<(Stem, B256)> {
        let mut stem_hashes: Vec<(Stem, B256)> = Vec::new();
        let mut current_stem: Option<Stem> = None;
        let mut current_values: HashMap<SubIndex, B256> = HashMap::new();

        #[cfg(debug_assertions)]
        let mut prev_key: Option<TreeKey> = None;

        for (key, value) in entries.by_ref() {
            #[cfg(debug_assertions)]
            {
                if let Some(prev) = prev_key {
                    debug_assert!(
                        (prev.stem, prev.subindex) < (key.stem, key.subindex),
                        "Entries must be sorted: {:?} should come before {:?}",
                        prev,
                        key
                    );
                }
                prev_key = Some(key);
            }

            match current_stem {
                Some(stem) if stem == key.stem => {
                    // Same stem, accumulate value
                    if !value.is_zero() {
                        current_values.insert(key.subindex, value);
                    }
                }
                Some(stem) => {
                    // New stem, finalize previous
                    if !current_values.is_empty() {
                        let hash = self.compute_stem_hash(&stem, &current_values);
                        stem_hashes.push((stem, hash));
                    }
                    // Start new stem
                    current_values.clear();
                    current_stem = Some(key.stem);
                    if !value.is_zero() {
                        current_values.insert(key.subindex, value);
                    }
                }
                None => {
                    // First stem
                    current_stem = Some(key.stem);
                    if !value.is_zero() {
                        current_values.insert(key.subindex, value);
                    }
                }
            }
        }

        // Finalize last stem
        if let Some(stem) = current_stem {
            if !current_values.is_empty() {
                let hash = self.compute_stem_hash(&stem, &current_values);
                stem_hashes.push((stem, hash));
            }
        }

        stem_hashes
    }

    /// Compute hash for a stem node with given values.
    fn compute_stem_hash(&self, stem: &Stem, values: &HashMap<SubIndex, B256>) -> B256 {
        // Step 1: Hash all values
        let mut data = [B256::ZERO; 256];
        for (&idx, &value) in values {
            data[idx as usize] = self.hasher.hash_32(&value);
        }

        // Step 2: Build 8-level binary tree from bottom up
        for level in 1..=8 {
            let pairs = 256 >> level;
            for i in 0..pairs {
                let left = data[i * 2];
                let right = data[i * 2 + 1];
                data[i] = self.hasher.hash_64(&left, &right);
            }
        }

        let subtree_root = data[0];

        // Step 3: hash(stem || 0x00 || subtree_root)
        self.hasher.hash_stem_node(stem.as_bytes(), &subtree_root)
    }

    /// Build tree hash from sorted slice of (stem, hash) pairs.
    ///
    /// Uses partition_point + split_at for O(n) splits with no allocation,
    /// matching the optimization in `UnifiedBinaryTree::build_tree_from_sorted_stems`.
    fn build_tree_hash(&self, stem_hashes: &[(Stem, B256)], depth: usize) -> Result<B256> {
        if stem_hashes.is_empty() {
            return Ok(B256::ZERO);
        }

        if stem_hashes.len() == 1 {
            return Ok(stem_hashes[0].1);
        }

        if depth >= STEM_LEN * 8 {
            return Err(UbtError::TreeDepthExceeded { depth });
        }

        // partition_point finds the first index with bit_at(depth) == 1
        // (i.e. where !bit_at becomes false), so stem_hashes[0..split_point]
        // all have bit 0 and stem_hashes[split_point..] all have bit 1 at this depth.
        let split_point = stem_hashes.partition_point(|(s, _)| !s.bit_at(depth));
        let (left, right) = stem_hashes.split_at(split_point);

        let left_hash = self.build_tree_hash(left, depth + 1)?;
        let right_hash = self.build_tree_hash(right, depth + 1)?;

        if left_hash.is_zero() && right_hash.is_zero() {
            Ok(B256::ZERO)
        } else if left_hash.is_zero() {
            Ok(right_hash)
        } else if right_hash.is_zero() {
            Ok(left_hash)
        } else {
            Ok(self.hasher.hash_64(&left_hash, &right_hash))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::UnifiedBinaryTree;

    #[test]
    fn test_streaming_empty() {
        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
        let entries: Vec<(TreeKey, B256)> = vec![];
        assert_eq!(builder.build_root_hash(entries).unwrap(), B256::ZERO);
    }

    #[test]
    fn test_streaming_single_entry() {
        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
        let key = TreeKey::from_bytes(B256::repeat_byte(0x01));
        let value = B256::repeat_byte(0x42);

        let entries = vec![(key, value)];
        let streaming_root = builder.build_root_hash(entries).unwrap();

        // Compare with regular tree
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert(key, value);

        assert_eq!(streaming_root, tree.root_hash().unwrap());
    }

    #[test]
    fn test_streaming_matches_tree() {
        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();

        // Create test data
        let mut entries: Vec<(TreeKey, B256)> = Vec::new();
        for i in 0u8..10 {
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = i * 10;
            let stem = Stem::new(stem_bytes);
            for j in 0u8..5 {
                let key = TreeKey::new(stem, j);
                let value = B256::repeat_byte(i + j);
                entries.push((key, value));
            }
        }

        // Sort entries
        entries.sort_by(|a, b| (a.0.stem, a.0.subindex).cmp(&(b.0.stem, b.0.subindex)));

        let streaming_root = builder.build_root_hash(entries.clone()).unwrap();

        // Compare with regular tree
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert_batch(entries).unwrap();

        assert_eq!(streaming_root, tree.root_hash().unwrap());
    }

    #[test]
    fn test_streaming_many_stems() {
        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();

        // Create many stems with single values (start from 1 to avoid B256::ZERO)
        let mut entries: Vec<(TreeKey, B256)> = Vec::new();
        for i in 1u8..=100 {
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = i;
            stem_bytes[15] = i.wrapping_mul(7);
            let stem = Stem::new(stem_bytes);
            let key = TreeKey::new(stem, 0);
            entries.push((key, B256::repeat_byte(i)));
        }

        // Sort entries
        entries.sort_by(|a, b| (a.0.stem, a.0.subindex).cmp(&(b.0.stem, b.0.subindex)));

        let streaming_root = builder.build_root_hash(entries.clone()).unwrap();

        // Compare with regular tree
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert_batch(entries).unwrap();

        assert_eq!(streaming_root, tree.root_hash().unwrap());
    }

    #[test]
    fn test_tree_depth_exceeded_returns_error() {
        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();

        let stem1 = Stem::new([0u8; 31]);
        let mut stem2_bytes = [0u8; 31];
        stem2_bytes[0] = 1;
        let stem2 = Stem::new(stem2_bytes);
        let stem_hashes = vec![
            (stem1, B256::repeat_byte(1)),
            (stem2, B256::repeat_byte(2)),
        ];

        let err = builder
            .build_tree_hash(&stem_hashes, STEM_LEN * 8)
            .unwrap_err();
        assert!(
            matches!(err, UbtError::TreeDepthExceeded { depth } if depth == STEM_LEN * 8)
        );
    }

    #[cfg(feature = "parallel")]
    #[test]
    fn test_parallel_matches_serial() {
        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();

        // Create test data with many stems
        let mut entries: Vec<(TreeKey, B256)> = Vec::new();
        for i in 0u8..50 {
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = i;
            stem_bytes[10] = i.wrapping_mul(3);
            stem_bytes[20] = i.wrapping_mul(7);
            let stem = Stem::new(stem_bytes);
            for j in 0u8..10 {
                let key = TreeKey::new(stem, j);
                let value = B256::repeat_byte(i.wrapping_add(j).wrapping_mul(2).max(1));
                entries.push((key, value));
            }
        }

        // Sort entries
        entries.sort_by(|a, b| (a.0.stem, a.0.subindex).cmp(&(b.0.stem, b.0.subindex)));

        let serial_root = builder.build_root_hash(entries.clone()).unwrap();
        let parallel_root = builder.build_root_hash_parallel(entries).unwrap();

        assert_eq!(
            parallel_root, serial_root,
            "Parallel and serial should produce identical root hashes"
        );
    }

    #[cfg(feature = "parallel")]
    #[test]
    fn test_parallel_empty() {
        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
        let entries: Vec<(TreeKey, B256)> = vec![];
        assert_eq!(builder.build_root_hash_parallel(entries).unwrap(), B256::ZERO);
    }

    #[cfg(feature = "parallel")]
    #[test]
    fn test_parallel_single_entry() {
        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
        let key = TreeKey::from_bytes(B256::repeat_byte(0x01));
        let value = B256::repeat_byte(0x42);

        let entries = vec![(key, value)];
        let parallel_root = builder.build_root_hash_parallel(entries.clone()).unwrap();
        let serial_root = builder.build_root_hash(entries).unwrap();

        assert_eq!(parallel_root, serial_root);
    }
}
