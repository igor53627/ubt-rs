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
use crate::{error::Result, Blake3Hasher, Hasher, Stem, SubIndex, TreeKey, UbtError};

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
/// The builder checks the order in every build. An entry whose key is equal to the key
/// before it, or sorts before it, gives [`UbtError::EntriesNotSorted`]. Duplicate keys are
/// not allowed.
///
/// # Zero Values
///
/// Every entry is a present leaf, including an entry whose value is `B256::ZERO`.
/// The builder does not skip zero values, so it gives the same root hash as
/// [`UnifiedBinaryTree::insert`](crate::UnifiedBinaryTree::insert) for the same
/// entries, and the same root hash as go-ethereum with [`Sha256Hasher`](crate::Sha256Hasher).
/// To get the root of a tree where a key is absent, leave the key out of the input.
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
#[derive(Clone, Debug)]
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
    ///
    /// Returns `B256::ZERO` for empty input.
    ///
    /// # Errors
    ///
    /// Returns [`UbtError::EntriesNotSorted`] if the entries are not in strictly ascending
    /// `(stem, subindex)` order.
    #[must_use = "callers should handle errors and use the computed root hash"]
    pub fn build_root_hash(
        &self,
        entries: impl IntoIterator<Item = (TreeKey, B256)>,
    ) -> Result<B256> {
        let mut stem_hashes: Vec<(Stem, B256)> = Vec::new();
        for_each_stem_group(entries, |stem, values| {
            stem_hashes.push((stem, hash_stem_values(&self.hasher, &stem, values)));
        })?;

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
    ///
    /// Returns `B256::ZERO` for empty input.
    ///
    /// # Errors
    ///
    /// Returns [`UbtError::EntriesNotSorted`] if the entries are not in strictly ascending
    /// `(stem, subindex)` order.
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
        let mut stem_groups: Vec<(Stem, HashMap<SubIndex, B256>)> = Vec::new();
        for_each_stem_group(entries, |stem, values| {
            stem_groups.push((stem, std::mem::take(values)));
        })?;

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
}

/// Stream through sorted entries and call `on_stem` once per stem, in input order.
///
/// Every entry is a present leaf, including an entry with a zero value, so `on_stem`
/// is called for each stem in the input. The map passed to `on_stem` holds the values
/// of that stem only; it is cleared before the next stem starts, so `on_stem` can take it.
///
/// The entries come from the caller, so the order is checked in every build. Because the
/// keys are strictly ascending, `on_stem` gets each stem one time, in ascending order.
///
/// # Errors
///
/// Returns [`UbtError::EntriesNotSorted`] at the first entry whose key is not greater
/// than the key before it. `on_stem` was then called for the stems before that entry.
fn for_each_stem_group(
    entries: impl IntoIterator<Item = (TreeKey, B256)>,
    mut on_stem: impl FnMut(Stem, &mut HashMap<SubIndex, B256>),
) -> Result<()> {
    let mut previous_key: Option<TreeKey> = None;
    let mut current_values: HashMap<SubIndex, B256> = HashMap::new();

    for (key, value) in entries {
        if let Some(previous) = previous_key {
            if (previous.stem, previous.subindex) >= (key.stem, key.subindex) {
                return Err(UbtError::EntriesNotSorted {
                    previous,
                    current: key,
                });
            }
            if previous.stem != key.stem {
                on_stem(previous.stem, &mut current_values);
                current_values.clear();
            }
        }
        previous_key = Some(key);
        current_values.insert(key.subindex, value);
    }

    if let Some(previous) = previous_key {
        on_stem(previous.stem, &mut current_values);
    }
    Ok(())
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

        // Create many stems with single values; the first value is B256::ZERO
        let mut entries: Vec<(TreeKey, B256)> = Vec::new();
        for i in 0u8..=100 {
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

    /// Uses more stems than `PARALLEL_STEM_THRESHOLD`, so the rayon branch of
    /// `build_root_hash_parallel` runs.
    #[cfg(feature = "parallel")]
    #[test]
    fn test_parallel_matches_serial_above_threshold() {
        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
        let stem_count: u16 = 300;
        assert!(usize::from(stem_count) >= PARALLEL_STEM_THRESHOLD);

        let mut entries: Vec<(TreeKey, B256)> = Vec::new();
        for i in 0..stem_count {
            let [hi, lo] = i.to_be_bytes();
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = hi;
            stem_bytes[1] = lo;
            stem_bytes[20] = 0x5a;
            let stem = Stem::new(stem_bytes);
            entries.push((TreeKey::new(stem, 3), B256::repeat_byte(lo | 1)));
            entries.push((TreeKey::new(stem, 200), B256::repeat_byte(hi + 2)));
        }

        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        for (key, value) in &entries {
            tree.insert(*key, *value);
        }
        let tree_root = tree.root_hash().unwrap();

        let serial_root = builder.build_root_hash(entries.clone()).unwrap();
        let parallel_root = builder.build_root_hash_parallel(entries).unwrap();

        assert_ne!(tree_root, B256::ZERO);
        assert_eq!(serial_root, tree_root);
        assert_eq!(parallel_root, tree_root);
    }

    /// Zero values are present leaves, and a stem whose values are all zero
    /// contributes to the root, at the start, in the middle, and at the end of the
    /// input. The builder gives the root of a tree that holds the same entries, and
    /// not the root of a tree that holds only the non-zero entries.
    #[test]
    fn test_zero_values_and_all_zero_stems_are_present() {
        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
        let stems: Vec<Stem> = (1u8..=5).map(|i| Stem::new([i; 31])).collect();
        let value_a = B256::repeat_byte(0xa1);
        let value_b = B256::repeat_byte(0xb2);

        let entries = vec![
            (TreeKey::new(stems[0], 0), B256::ZERO),
            (TreeKey::new(stems[1], 1), value_a),
            (TreeKey::new(stems[1], 2), B256::ZERO),
            (TreeKey::new(stems[2], 0), B256::ZERO),
            (TreeKey::new(stems[2], 9), B256::ZERO),
            (TreeKey::new(stems[3], 0), B256::ZERO),
            (TreeKey::new(stems[3], 5), value_b),
            (TreeKey::new(stems[4], 7), B256::ZERO),
        ];

        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        for (key, value) in &entries {
            tree.insert(*key, *value);
        }
        assert_eq!(tree.len(), 8);
        assert_eq!(tree.stem_count(), 5);
        let expected = tree.root_hash().unwrap();

        let mut non_zero_only: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        non_zero_only.insert(TreeKey::new(stems[1], 1), value_a);
        non_zero_only.insert(TreeKey::new(stems[3], 5), value_b);
        assert_ne!(expected, non_zero_only.root_hash().unwrap());

        assert_eq!(builder.build_root_hash(entries.clone()).unwrap(), expected);
        #[cfg(feature = "parallel")]
        assert_eq!(builder.build_root_hash_parallel(entries).unwrap(), expected);

        let all_zero = vec![
            (TreeKey::new(stems[0], 0), B256::ZERO),
            (TreeKey::new(stems[1], 0), B256::ZERO),
        ];
        let mut all_zero_tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        for (key, value) in &all_zero {
            all_zero_tree.insert(*key, *value);
        }
        let all_zero_root = all_zero_tree.root_hash().unwrap();
        assert_ne!(all_zero_root, B256::ZERO);
        assert_eq!(
            builder.build_root_hash(all_zero.clone()).unwrap(),
            all_zero_root
        );
        #[cfg(feature = "parallel")]
        assert_eq!(
            builder.build_root_hash_parallel(all_zero).unwrap(),
            all_zero_root
        );
    }

    /// The entry order is input from the caller, so a wrong order is an error in every
    /// build, for both build methods. Goal: each kind of wrong order (repeated key,
    /// descending subindex, descending stem, a stem that comes back after another stem)
    /// gives `EntriesNotSorted` with the two keys at the first wrong position, and the
    /// same entries in ascending order give a root.
    #[test]
    fn test_entries_not_in_ascending_order_are_rejected() {
        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
        let stem_1 = Stem::new([1u8; 31]);
        let stem_2 = Stem::new([2u8; 31]);
        let value = B256::repeat_byte(0x77);
        let key = TreeKey::new;

        let ascending: Vec<TreeKey> = vec![key(stem_1, 4), key(stem_1, 5), key(stem_2, 0)];
        let wrong_orders: [(Vec<TreeKey>, usize); 5] = [
            (vec![key(stem_1, 4), key(stem_1, 4), key(stem_2, 0)], 1),
            (vec![key(stem_1, 5), key(stem_1, 4), key(stem_2, 0)], 1),
            (vec![key(stem_2, 0), key(stem_1, 4), key(stem_1, 5)], 1),
            (vec![key(stem_1, 4), key(stem_2, 0), key(stem_1, 5)], 2),
            (
                vec![
                    key(stem_1, 4),
                    key(stem_1, 5),
                    key(stem_2, 0),
                    key(stem_2, 0),
                ],
                3,
            ),
        ];

        let with_values = |keys: &[TreeKey]| -> Vec<(TreeKey, B256)> {
            keys.iter().map(|&entry_key| (entry_key, value)).collect()
        };
        let assert_rejected = |result: Result<B256>, keys: &[TreeKey], position: usize| match result
        {
            Err(UbtError::EntriesNotSorted { previous, current }) => {
                assert_eq!(previous, keys[position - 1], "keys: {keys:?}");
                assert_eq!(current, keys[position], "keys: {keys:?}");
            }
            other => panic!("expected EntriesNotSorted for {keys:?}, got {other:?}"),
        };

        assert!(builder.build_root_hash(with_values(&ascending)).is_ok());
        #[cfg(feature = "parallel")]
        assert!(builder
            .build_root_hash_parallel(with_values(&ascending))
            .is_ok());

        for (keys, position) in &wrong_orders {
            assert_rejected(builder.build_root_hash(with_values(keys)), keys, *position);
            #[cfg(feature = "parallel")]
            assert_rejected(
                builder.build_root_hash_parallel(with_values(keys)),
                keys,
                *position,
            );
        }
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
