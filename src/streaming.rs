//! Streaming tree builder for memory-efficient root hash computation.
//!
//! This module provides a way to compute the UBT root hash by streaming
//! through sorted entries, without keeping the full tree in memory.

use alloy_primitives::B256;
use std::collections::HashMap;

use crate::{Blake3Hasher, Hasher, Stem, SubIndex, TreeKey, STEM_LEN};

/// A streaming tree builder that computes root hash with minimal memory.
///
/// # Usage
///
/// 1. Sort all `(TreeKey, B256)` entries by key (stem, then subindex) in lexicographic order
/// 2. Call `build_root_hash` with the sorted iterator
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
    pub fn build_root_hash(&self, entries: impl IntoIterator<Item = (TreeKey, B256)>) -> B256 {
        let mut entries_iter = entries.into_iter().peekable();

        if entries_iter.peek().is_none() {
            return B256::ZERO;
        }

        // Group entries by stem and compute stem hashes
        let stem_hashes = self.collect_stem_hashes(&mut entries_iter);

        if stem_hashes.is_empty() {
            return B256::ZERO;
        }

        // Build tree from stem hashes (sorted by stem since entries were sorted)
        self.build_tree_hash(&stem_hashes, 0)
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

        while let Some((key, value)) = entries.next() {
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
    fn build_tree_hash(&self, stem_hashes: &[(Stem, B256)], depth: usize) -> B256 {
        if stem_hashes.is_empty() {
            return B256::ZERO;
        }

        if stem_hashes.len() == 1 {
            return stem_hashes[0].1;
        }

        debug_assert!(
            depth < STEM_LEN * 8,
            "Tree depth exceeded maximum of {} bits",
            STEM_LEN * 8
        );

        // partition_point finds the first index with bit_at(depth) == 1
        // (i.e. where !bit_at becomes false), so stem_hashes[0..split_point]
        // all have bit 0 and stem_hashes[split_point..] all have bit 1 at this depth.
        let split_point = stem_hashes.partition_point(|(s, _)| !s.bit_at(depth));
        let (left, right) = stem_hashes.split_at(split_point);

        let left_hash = self.build_tree_hash(left, depth + 1);
        let right_hash = self.build_tree_hash(right, depth + 1);

        if left_hash.is_zero() && right_hash.is_zero() {
            B256::ZERO
        } else if left_hash.is_zero() {
            right_hash
        } else if right_hash.is_zero() {
            left_hash
        } else {
            self.hasher.hash_64(&left_hash, &right_hash)
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
        assert_eq!(builder.build_root_hash(entries), B256::ZERO);
    }

    #[test]
    fn test_streaming_single_entry() {
        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
        let key = TreeKey::from_bytes(B256::repeat_byte(0x01));
        let value = B256::repeat_byte(0x42);

        let entries = vec![(key, value)];
        let streaming_root = builder.build_root_hash(entries);

        // Compare with regular tree
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert(key, value);

        assert_eq!(streaming_root, tree.root_hash());
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

        let streaming_root = builder.build_root_hash(entries.clone());

        // Compare with regular tree
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert_batch(entries);

        assert_eq!(streaming_root, tree.root_hash());
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

        let streaming_root = builder.build_root_hash(entries.clone());

        // Compare with regular tree
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert_batch(entries);

        assert_eq!(streaming_root, tree.root_hash());
    }
}
