//! Root-hash computation and rebuild logic for [`UnifiedBinaryTree`].

use alloy_primitives::B256;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::merkle::root_from_sorted_stem_hashes;
#[cfg(feature = "parallel")]
use crate::merkle::PARALLEL_STEM_THRESHOLD;
use crate::store::NodeStore;
use crate::{error::Result, Hasher, Stem, TreeKey, UbtError};

use super::{UnifiedBinaryTree, MAX_DEPTH};

/// Set bit at the given position in a B256 (MSB-first ordering).
/// Position 0 is the MSB of the first byte.
fn set_bit_at(mut value: B256, pos: usize) -> B256 {
    assert!(pos < 256, "bit position {pos} is not in a 256-bit value");
    let byte_idx = pos / 8;
    let bit_idx = 7 - (pos % 8);
    value.0[byte_idx] |= 1 << bit_idx;
    value
}

/// Returns whether `value` shares the first `depth` bits with `prefix`.
///
/// Bits are interpreted MSB-first within each byte.
///
/// # Panics
///
/// Panics if `depth` is more than 256.
fn b256_matches_prefix(value: &B256, prefix: &B256, depth: usize) -> bool {
    assert!(depth <= 256, "prefix length {depth} is more than 256 bits");
    let full_bytes = depth / 8;
    if value.0[..full_bytes] != prefix.0[..full_bytes] {
        return false;
    }

    let rem_bits = depth % 8;
    if rem_bits == 0 {
        return true;
    }

    let mask = 0xFFu8 << (8 - rem_bits);
    (value.0[full_bytes] & mask) == (prefix.0[full_bytes] & mask)
}

/// Asserts that every stem with bit 0 at `depth` comes before every stem with bit 1.
///
/// # Panics
///
/// Panics if a stem with bit 0 at `depth` follows a stem with bit 1.
fn assert_partitioned_at(stems: &[Stem], depth: usize) {
    let mut seen_one: bool = false;
    for stem in stems {
        if stem.bit_at(depth) {
            seen_one = true;
        } else {
            assert!(!seen_one, "stems are not partitioned at depth {depth}");
        }
    }
}

impl<H: Hasher, S: NodeStore> UnifiedBinaryTree<H, S> {
    /// Get the root hash of the tree.
    ///
    /// This will trigger a recomputation of the root hash if any modifications
    /// have been made since the last call to `root_hash()`.
    ///
    /// # Errors
    ///
    /// Returns an error if the internal rebuild exceeds maximum depth, which typically
    /// indicates duplicate stems or a bug in the rebuild logic.
    #[must_use = "callers should handle errors and use the computed root hash"]
    pub fn root_hash(&mut self) -> Result<B256> {
        if self.root_dirty {
            self.rebuild_root()?;
            self.root_dirty = false;
        }
        Ok(self.root_hash_cached)
    }

    /// Compute the hash for a stem node.
    ///
    /// Returns `B256::ZERO` for a stem that is not in the store and for a stem node
    /// with no values. A stem node with a value, also a zero value, has a non-zero hash.
    fn compute_stem_hash(&self, stem: &Stem) -> B256 {
        if let Some(stem_node) = self.store.get(stem) {
            stem_node.hash(&self.hasher)
        } else {
            B256::ZERO
        }
    }

    /// Compute the hash of each dirty stem.
    ///
    /// Uses rayon when the `parallel` feature is enabled and there are enough stems
    /// to offset the rayon overhead.
    fn compute_stem_updates(&self, dirty_stems: &[Stem]) -> Vec<(Stem, B256)> {
        #[cfg(feature = "parallel")]
        if dirty_stems.len() >= PARALLEL_STEM_THRESHOLD {
            return dirty_stems
                .par_iter()
                .map(|stem| (*stem, self.compute_stem_hash(stem)))
                .collect();
        }

        dirty_stems
            .iter()
            .map(|stem| (*stem, self.compute_stem_hash(stem)))
            .collect()
    }

    /// Rebuild the root from all stem nodes.
    ///
    /// A dirty stem with a zero hash is removed from `stem_hash_cache`. This is the
    /// case only for a stem that [`delete`](Self::delete) removed from the store and
    /// for a stem node with no values. Both contribute nothing to the root, and the
    /// incremental path sees them as dirty stems without a stem hash.
    fn rebuild_root(&mut self) -> Result<()> {
        // Don't clear `dirty_stem_hashes` until we've successfully rebuilt the root.
        // Otherwise, a failure would lose information needed for a retry.
        let mut dirty_stems: Vec<Stem> = self.dirty_stem_hashes.iter().copied().collect();

        for (stem, hash) in self.compute_stem_updates(&dirty_stems) {
            if hash.is_zero() {
                self.stem_hash_cache.remove(&stem);
            } else {
                self.stem_hash_cache.insert(stem, hash);
            }
        }

        if self.stem_hash_cache.is_empty() {
            self.root_hash_cached = B256::ZERO;
            self.node_hash_cache.clear();
            self.dirty_stem_hashes.clear();
            return Ok(());
        }

        let mut stem_hashes: Vec<(Stem, B256)> =
            self.stem_hash_cache.iter().map(|(s, h)| (*s, *h)).collect();
        stem_hashes.sort_by_key(|(s, _)| *s);

        let root_hash: B256 = if !self.incremental_enabled {
            root_from_sorted_stem_hashes(&self.hasher, &stem_hashes, 0)?
        } else if self.node_hash_cache.is_empty() {
            self.build_root_hash_with_cache(&stem_hashes, 0, B256::ZERO)?
        } else {
            // `incremental_hash_update` splits the dirty stems with `partition_point`,
            // so they must be sorted.
            dirty_stems.sort();
            self.incremental_hash_update(&stem_hashes, 0, B256::ZERO, &dirty_stems)?
        };

        self.root_hash_cached = root_hash;
        self.dirty_stem_hashes.clear();
        Ok(())
    }

    /// Build the root hash and populate the `node_hash_cache` for incremental updates.
    /// This version caches all intermediate node hashes.
    fn build_root_hash_with_cache(
        &mut self,
        stem_hashes: &[(Stem, B256)],
        depth: usize,
        path_prefix: B256,
    ) -> Result<B256> {
        if stem_hashes.is_empty() {
            return Ok(B256::ZERO);
        }

        if stem_hashes.len() == 1 {
            let hash = stem_hashes[0].1;
            self.node_hash_cache.insert((depth, path_prefix), hash);
            return Ok(hash);
        }

        if depth >= MAX_DEPTH {
            return Err(UbtError::TreeDepthExceeded { depth });
        }

        let split_point = stem_hashes.partition_point(|(s, _)| !s.bit_at(depth));
        let (left, right) = stem_hashes.split_at(split_point);

        let left_hash = self.build_root_hash_with_cache(left, depth + 1, path_prefix)?;
        let right_prefix = set_bit_at(path_prefix, depth);
        let right_hash = self.build_root_hash_with_cache(right, depth + 1, right_prefix)?;

        let node_hash = if left_hash.is_zero() && right_hash.is_zero() {
            B256::ZERO
        } else {
            self.hasher.hash_64(&left_hash, &right_hash)
        };

        self.node_hash_cache.insert((depth, path_prefix), node_hash);
        Ok(node_hash)
    }

    /// Recursively update the tree hash, only recomputing paths that contain dirty stems.
    fn incremental_hash_update(
        &mut self,
        stem_hashes: &[(Stem, B256)],
        depth: usize,
        path_prefix: B256,
        dirty_stems: &[Stem],
    ) -> Result<B256> {
        if stem_hashes.is_empty() {
            // Avoid scanning the entire cache for subtrees that are and always were empty.
            // If this subtree became empty due to deletions, `dirty_stems` will be non-empty.
            // If we have cached state for this subtree root, prune it even if dirty information
            // was lost, to avoid reusing stale entries.
            //
            // Invariant: cached subtrees always include the subtree-root entry, so this
            // `contains_key` check is sufficient to detect cached descendants.
            if !dirty_stems.is_empty() || self.node_hash_cache.contains_key(&(depth, path_prefix)) {
                self.prune_node_hash_cache_subtree(depth, path_prefix);
            }
            return Ok(B256::ZERO);
        }

        if dirty_stems.is_empty() {
            if let Some(hash) = self.node_hash_cache.get(&(depth, path_prefix)).copied() {
                return Ok(hash);
            }
            return self.build_root_hash_with_cache(stem_hashes, depth, path_prefix);
        }

        if stem_hashes.len() == 1 {
            // When a subtree collapses to a single stem, treat it as a leaf at this depth and
            // clear any cached descendants to prevent stale entries being reused later.
            self.prune_node_hash_cache_descendants(depth, path_prefix);

            let hash = stem_hashes[0].1;
            self.node_hash_cache.insert((depth, path_prefix), hash);
            return Ok(hash);
        }

        if depth >= MAX_DEPTH {
            return Err(UbtError::TreeDepthExceeded { depth });
        }

        let split_point = stem_hashes.partition_point(|(s, _)| !s.bit_at(depth));
        let (left, right) = stem_hashes.split_at(split_point);

        // `dirty_stems` is sorted and already restricted to this subtree's prefix.
        // That makes `bit_at(depth)` monotone on this slice, so `partition_point` is valid.
        assert_partitioned_at(dirty_stems, depth);
        let dirty_split = dirty_stems.partition_point(|s| !s.bit_at(depth));
        let (left_dirty, right_dirty) = dirty_stems.split_at(dirty_split);

        let right_prefix = set_bit_at(path_prefix, depth);

        let left_hash = self.incremental_hash_update(left, depth + 1, path_prefix, left_dirty)?;
        let right_hash =
            self.incremental_hash_update(right, depth + 1, right_prefix, right_dirty)?;

        let node_hash = if left_hash.is_zero() && right_hash.is_zero() {
            B256::ZERO
        } else {
            self.hasher.hash_64(&left_hash, &right_hash)
        };

        self.node_hash_cache.insert((depth, path_prefix), node_hash);
        Ok(node_hash)
    }

    fn prune_node_hash_cache_descendants(&mut self, depth: usize, path_prefix: B256) {
        if depth > MAX_DEPTH {
            // `depth` should be bounded by `MAX_DEPTH`; if it is ever invalid, clear the cache
            // to avoid reusing stale entries.
            self.node_hash_cache.clear();
            return;
        }
        self.node_hash_cache.retain(|(d, prefix), _| {
            !(*d > depth && b256_matches_prefix(prefix, &path_prefix, depth))
        });
    }

    fn prune_node_hash_cache_subtree(&mut self, depth: usize, path_prefix: B256) {
        if depth > MAX_DEPTH {
            // See `prune_node_hash_cache_descendants`.
            self.node_hash_cache.clear();
            return;
        }
        self.node_hash_cache.retain(|(d, prefix), _| {
            !(*d >= depth && b256_matches_prefix(prefix, &path_prefix, depth))
        });
    }

    /// Enable incremental root hash updates.
    ///
    /// When enabled, intermediate node hashes are cached to allow O(D * C) hash
    /// recomputation where D is tree depth (248) and C is the number of changed stems.
    /// Note: the current rebuild path still collects and sorts all stem hashes,
    /// so end-to-end updates may remain O(S log S).
    ///
    /// This is the recommended mode for block-by-block state updates where only
    /// a small fraction of stems change per block.
    ///
    /// # Cache Behavior
    ///
    /// - The cache is populated lazily on the first `root_hash()` call after enabling
    /// - Memory usage is approximately O(S) for S stems (up to 2x stems for internal nodes)
    /// - Use [`with_capacity`](Self::with_capacity) when creating the tree to pre-allocate
    ///
    /// # Example
    ///
    /// ```rust
    /// use ubt::{UnifiedBinaryTree, Blake3Hasher, TreeKey, B256};
    ///
    /// let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
    /// // Initial inserts...
    /// tree.insert(TreeKey::from_bytes(B256::repeat_byte(0x01)), B256::repeat_byte(0x42));
    /// tree.root_hash().unwrap(); // Full rebuild
    ///
    /// tree.enable_incremental_mode();
    /// tree.root_hash().unwrap(); // Populates cache
    ///
    /// // Subsequent updates do O(D * C) hash recomputation (the stem sort is still O(S log S))
    /// tree.insert(TreeKey::from_bytes(B256::repeat_byte(0x02)), B256::repeat_byte(0x43));
    /// tree.root_hash().unwrap(); // Only recomputes affected paths
    /// ```
    pub fn enable_incremental_mode(&mut self) {
        if !self.incremental_enabled {
            self.incremental_enabled = true;
            self.node_hash_cache.clear();
            if !self.stem_hash_cache.is_empty() {
                for stem in self.stem_hash_cache.keys() {
                    self.dirty_stem_hashes.insert(*stem);
                }
                self.root_dirty = true;
            }
        }
    }

    /// Disable incremental root updates and clear the cache.
    pub fn disable_incremental_mode(&mut self) {
        self.incremental_enabled = false;
        self.node_hash_cache.clear();
    }

    /// Returns whether incremental mode is enabled.
    pub fn is_incremental_enabled(&self) -> bool {
        self.incremental_enabled
    }

    /// Returns the number of cached intermediate node hashes.
    pub fn node_cache_size(&self) -> usize {
        self.node_hash_cache.len()
    }

    /// Batch insert multiple key-value pairs.
    ///
    /// Unlike [`insert`](Self::insert), which defers the work to the next
    /// [`root_hash`](Self::root_hash) call, this method recomputes the root hash
    /// before it returns, if `entries` is not empty.
    ///
    /// As with [`insert`](Self::insert), a zero value is stored as a present leaf.
    /// If a key occurs more than once, the last value wins.
    ///
    /// # Errors
    ///
    /// Returns an error if the root rebuild exceeds maximum depth.
    pub fn insert_batch(
        &mut self,
        entries: impl IntoIterator<Item = (TreeKey, B256)>,
    ) -> Result<()> {
        self.insert_batch_with_progress(entries, |_| {})
    }

    /// Batch insert multiple key-value pairs with progress callback.
    ///
    /// `on_progress` is called after each entry with the number of entries inserted
    /// so far. Like [`insert_batch`](Self::insert_batch), this method recomputes the
    /// root hash before it returns, if `entries` is not empty.
    ///
    /// # Errors
    ///
    /// Returns an error if the root rebuild exceeds maximum depth.
    pub fn insert_batch_with_progress(
        &mut self,
        entries: impl IntoIterator<Item = (TreeKey, B256)>,
        mut on_progress: impl FnMut(usize),
    ) -> Result<()> {
        let mut count: usize = 0;
        for (key, value) in entries {
            self.insert(key, value);
            count += 1;
            on_progress(count);
        }
        if count > 0 {
            self.rebuild_root()?;
            self.root_dirty = false;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Blake3Hasher;

    fn b256_from_zero(overrides: &[(usize, u8)]) -> B256 {
        let mut bytes = [0u8; 32];
        for &(idx, value) in overrides {
            assert!(idx < bytes.len(), "byte index out of range: {idx}");
            bytes[idx] = value;
        }
        B256::from(bytes)
    }

    fn b256_from_fill(fill: u8, overrides: &[(usize, u8)]) -> B256 {
        let mut bytes = [fill; 32];
        for &(idx, value) in overrides {
            assert!(idx < bytes.len(), "byte index out of range: {idx}");
            bytes[idx] = value;
        }
        B256::from(bytes)
    }

    fn assert_prefix_match(value: B256, prefix_ok: B256, prefix_bad: B256, depth: usize) {
        assert!(
            b256_matches_prefix(&value, &prefix_ok, depth),
            "expected match at depth={depth} (value={value:?}, prefix={prefix_ok:?})",
        );
        assert!(
            !b256_matches_prefix(&value, &prefix_bad, depth),
            "expected mismatch at depth={depth} (value={value:?}, prefix={prefix_bad:?})",
        );
    }

    #[test]
    fn test_b256_matches_prefix_depth_0_matches_everything() {
        let a = B256::repeat_byte(0xAA);
        let b = B256::repeat_byte(0xBB);
        assert!(b256_matches_prefix(&a, &b, 0));
    }

    #[test]
    fn test_b256_matches_prefix_depth_256_requires_full_match() {
        let a = B256::repeat_byte(0xAA);
        let b = B256::repeat_byte(0xAA);
        let c = B256::repeat_byte(0xBB);

        assert!(b256_matches_prefix(&a, &b, 256));
        assert!(!b256_matches_prefix(&a, &c, 256));
    }

    #[test]
    fn test_b256_matches_prefix_partial_depths() {
        assert_prefix_match(
            b256_from_zero(&[(0, 0x80)]),
            b256_from_zero(&[(0, 0x80)]),
            b256_from_zero(&[]),
            1,
        );

        assert_prefix_match(
            b256_from_zero(&[(0, 0xAA)]),
            b256_from_zero(&[(0, 0xAA)]),
            b256_from_zero(&[(0, 0xAB)]),
            8,
        );

        assert_prefix_match(
            b256_from_zero(&[(0, 0xAA), (1, 0x80)]),
            b256_from_zero(&[(0, 0xAA), (1, 0x80)]),
            b256_from_zero(&[(0, 0xAA), (1, 0x00)]),
            9,
        );

        assert_prefix_match(
            b256_from_zero(&[(0, 0xAA), (1, 0xFE)]),
            b256_from_zero(&[(0, 0xAA), (1, 0xFF)]),
            b256_from_zero(&[(0, 0xAA), (1, 0x7E)]),
            15,
        );

        assert_prefix_match(
            b256_from_fill(0xAA, &[(31, 0xFE)]),
            b256_from_fill(0xAA, &[(31, 0xFF)]),
            b256_from_fill(0xAA, &[(31, 0x7E)]),
            255,
        );
    }

    #[test]
    fn test_prune_node_hash_cache_invalid_depth_clears_cache() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.node_hash_cache
            .insert((0, B256::ZERO), B256::repeat_byte(1));

        tree.prune_node_hash_cache_subtree(MAX_DEPTH + 1, B256::ZERO);
        assert!(tree.node_hash_cache.is_empty());
    }

    #[test]
    fn test_incremental_delete_prunes_empty_subtree_cache() {
        let mut key_right_bytes = [0u8; 32];
        key_right_bytes[0] = 0x80;

        let key_left = TreeKey::from_bytes(B256::ZERO);
        let key_right = TreeKey::from_bytes(B256::from_slice(&key_right_bytes));

        let left_value = B256::repeat_byte(0x11);
        let right_value = B256::repeat_byte(0x22);

        let mut tree_inc: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree_inc.insert(key_left, left_value);
        tree_inc.insert(key_right, right_value);
        tree_inc.enable_incremental_mode();
        tree_inc.root_hash().unwrap(); // Populate cache

        let right_prefix = set_bit_at(B256::ZERO, 0);
        assert!(tree_inc.node_hash_cache.contains_key(&(1, right_prefix)));

        tree_inc.delete(&key_right);
        let root_inc = tree_inc.root_hash().unwrap();

        let mut tree_full: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree_full.insert(key_left, left_value);
        tree_full.insert(key_right, right_value);
        tree_full.delete(&key_right);
        let root_full = tree_full.root_hash().unwrap();

        assert_eq!(root_inc, root_full);

        let has_right_cache_entries =
            tree_inc.node_hash_cache.iter().any(|((depth, prefix), _)| {
                *depth >= 1 && b256_matches_prefix(prefix, &right_prefix, 1)
            });
        assert!(!has_right_cache_entries);
    }

    #[test]
    fn test_incremental_hash_update_prunes_cached_empty_subtree_without_dirty_info() {
        let mut key_right_bytes = [0u8; 32];
        key_right_bytes[0] = 0x80;

        let key_left = TreeKey::from_bytes(B256::ZERO);
        let key_right = TreeKey::from_bytes(B256::from_slice(&key_right_bytes));

        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert(key_left, B256::repeat_byte(0x11));
        tree.insert(key_right, B256::repeat_byte(0x22));
        tree.enable_incremental_mode();
        tree.root_hash().unwrap(); // Populate cache

        let right_prefix = set_bit_at(B256::ZERO, 0);
        assert!(tree.node_hash_cache.contains_key(&(1, right_prefix)));

        // Make the right subtree empty, but simulate "lost dirty info" by not providing any
        // dirty stems to the incremental update logic.
        let () = tree.delete(&key_right);
        assert!(tree.get(&key_right).is_none());
        tree.dirty_stem_hashes.clear();

        let out = tree
            .incremental_hash_update(&[], 1, right_prefix, &[])
            .unwrap();
        assert_eq!(out, B256::ZERO);

        let has_right_cache_entries = tree.node_hash_cache.iter().any(|((depth, prefix), _)| {
            *depth >= 1 && b256_matches_prefix(prefix, &right_prefix, 1)
        });
        assert!(!has_right_cache_entries);
    }
}
