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

#[cfg(feature = "parallel")]
use crate::merkle::PARALLEL_STEM_THRESHOLD;
use crate::merkle::{hash_stem_values, root_from_sorted_stem_hashes};
use crate::{error::Result, Blake3Hasher, Hasher, Stem, SubIndex, TreeKey};

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
/// Memory usage is `O(num_stems + tree_depth)` instead of `O(num_entries)`, since:
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

    /// Build the root hash from a sorted iterator of (`TreeKey`, `B256`) entries.
    ///
    /// The entries MUST be sorted by (stem, subindex) in lexicographic order.
    /// In debug builds, this is asserted.
    ///
    /// Returns `B256::ZERO` for empty input.
    ///
    /// # Errors
    ///
    /// Returns an error if the internal tree build exceeds maximum depth, which typically
    /// indicates duplicate stems or a bug in the stem grouping logic.
    #[must_use = "callers should handle errors and use the computed root hash"]
    pub fn build_root_hash(
        &self,
        entries: impl IntoIterator<Item = (TreeKey, B256)>,
    ) -> Result<B256> {
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
        root_from_sorted_stem_hashes(&self.hasher, &stem_hashes, 0)
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
    /// # Errors
    ///
    /// Returns an error if the internal tree build exceeds maximum depth, which typically
    /// indicates duplicate stems or a bug in the stem grouping logic.
    ///
    /// # Feature Flag
    ///
    /// Requires the `parallel` feature (enabled by default).
    #[cfg(feature = "parallel")]
    #[must_use = "callers should handle errors and use the computed root hash"]
    pub fn build_root_hash_parallel(
        &self,
        entries: impl IntoIterator<Item = (TreeKey, B256)>,
    ) -> Result<B256> {
        let mut entries_iter = entries.into_iter().peekable();

        if entries_iter.peek().is_none() {
            return Ok(B256::ZERO);
        }

        // Group entries by stem (serial - streaming through sorted entries)
        let stem_groups = Self::collect_stem_groups(&mut entries_iter);

        if stem_groups.is_empty() {
            return Ok(B256::ZERO);
        }

        // Compute stem hashes in parallel (only if enough stems to offset rayon overhead)
        let mut stem_hashes: Vec<(Stem, B256)> = if stem_groups.len() >= PARALLEL_STEM_THRESHOLD {
            stem_groups
                .into_par_iter()
                .map(|(stem, values)| {
                    let hash = hash_stem_values(&self.hasher, &stem, &values);
                    (stem, hash)
                })
                .collect()
        } else {
            stem_groups
                .into_iter()
                .map(|(stem, values)| {
                    let hash = hash_stem_values(&self.hasher, &stem, &values);
                    (stem, hash)
                })
                .collect()
        };

        // Sort by stem for deterministic order (parallel collect doesn't preserve order)
        stem_hashes.sort_by(|a, b| a.0.cmp(&b.0));

        // Build tree from stem hashes (serial - O(n) and fast)
        root_from_sorted_stem_hashes(&self.hasher, &stem_hashes, 0)
    }

    /// Collect entries grouped by stem without computing hashes.
    /// Used by parallel version to separate grouping from hashing.
    #[cfg(feature = "parallel")]
    fn collect_stem_groups<I: Iterator<Item = (TreeKey, B256)>>(
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
                        "Entries must be sorted: {prev:?} should come before {key:?}",
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
                        "Entries must be sorted: {prev:?} should come before {key:?}",
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
                        let hash = hash_stem_values(&self.hasher, &stem, &current_values);
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
                let hash = hash_stem_values(&self.hasher, &stem, &current_values);
                stem_hashes.push((stem, hash));
            }
        }

        stem_hashes
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
        assert_eq!(
            builder.build_root_hash_parallel(entries).unwrap(),
            B256::ZERO
        );
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
