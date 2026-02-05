//! Root-hash computation and rebuild logic for [`UnifiedBinaryTree`].

use alloy_primitives::B256;
use std::collections::HashSet;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::{error::Result, Hasher, Node, Stem, StemNode, TreeKey, UbtError};

use super::{UnifiedBinaryTree, MAX_DEPTH};

/// Set bit at the given position in a B256 (MSB-first ordering).
/// Position 0 is the MSB of the first byte.
fn set_bit_at(mut value: B256, pos: usize) -> B256 {
    debug_assert!(pos < 256);
    let byte_idx = pos / 8;
    let bit_idx = 7 - (pos % 8);
    value.0[byte_idx] |= 1 << bit_idx;
    value
}

impl<H: Hasher> UnifiedBinaryTree<H> {
    /// Get the root hash of the tree.
    ///
    /// This will trigger a rebuild of the tree structure if any modifications
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
    #[cfg(not(feature = "parallel"))]
    fn compute_stem_hash(&self, stem: &Stem) -> B256 {
        if let Some(stem_node) = self.stems.get(stem) {
            stem_node.hash(&self.hasher)
        } else {
            B256::ZERO
        }
    }

    /// Rebuild the root from all stem nodes.
    #[cfg(not(feature = "parallel"))]
    fn rebuild_root(&mut self) -> Result<()> {
        // Don't clear `dirty_stem_hashes` until we've successfully rebuilt the root.
        // Otherwise, a failure would lose information needed for a retry.
        let dirty_stems: Vec<_> = self.dirty_stem_hashes.iter().copied().collect();

        for stem in &dirty_stems {
            let hash = self.compute_stem_hash(stem);
            if hash.is_zero() {
                self.stem_hash_cache.remove(stem);
            } else {
                self.stem_hash_cache.insert(*stem, hash);
            }
        }

        if self.stem_hash_cache.is_empty() {
            self.root = Node::Empty;
            self.root_hash_cached = B256::ZERO;
            self.node_hash_cache.clear();
            self.dirty_stem_hashes.clear();
            return Ok(());
        }

        if self.incremental_enabled && !self.node_hash_cache.is_empty() {
            self.rebuild_root_incremental(&dirty_stems)?;
        } else {
            let mut stem_hashes: Vec<_> =
                self.stem_hash_cache.iter().map(|(s, h)| (*s, *h)).collect();
            stem_hashes.sort_by_key(|(s, _)| *s);

            let root_hash = if self.incremental_enabled {
                self.node_hash_cache.clear();
                self.build_root_hash_with_cache(&stem_hashes, 0, B256::ZERO)?
            } else {
                self.build_root_hash_from_stem_hashes(&stem_hashes, 0)?
            };

            let stems: Vec<_> = stem_hashes.iter().map(|(s, _)| *s).collect();
            let root = self.build_tree_from_sorted_stems(&stems, 0)?;

            self.root_hash_cached = root_hash;
            self.root = root;
        }

        self.dirty_stem_hashes.clear();
        Ok(())
    }

    /// Rebuild the root from all stem nodes (parallel version).
    #[cfg(feature = "parallel")]
    fn rebuild_root(&mut self) -> Result<()> {
        // Don't clear `dirty_stem_hashes` until we've successfully rebuilt the root.
        // Otherwise, a failure would lose information needed for a retry.
        let dirty_stems: Vec<_> = self.dirty_stem_hashes.iter().copied().collect();

        let stem_updates: Vec<_> = dirty_stems
            .par_iter()
            .map(|stem| {
                let hash = if let Some(stem_node) = self.stems.get(stem) {
                    stem_node.hash(&self.hasher)
                } else {
                    B256::ZERO
                };
                (*stem, hash)
            })
            .collect();

        for (stem, hash) in &stem_updates {
            if hash.is_zero() {
                self.stem_hash_cache.remove(stem);
            } else {
                self.stem_hash_cache.insert(*stem, *hash);
            }
        }

        if self.stem_hash_cache.is_empty() {
            self.root = Node::Empty;
            self.root_hash_cached = B256::ZERO;
            self.node_hash_cache.clear();
            self.dirty_stem_hashes.clear();
            return Ok(());
        }

        if self.incremental_enabled && !self.node_hash_cache.is_empty() {
            self.rebuild_root_incremental(&dirty_stems)?;
        } else {
            let mut stem_hashes: Vec<_> =
                self.stem_hash_cache.iter().map(|(s, h)| (*s, *h)).collect();
            stem_hashes.sort_by_key(|(s, _)| *s);

            let root_hash = if self.incremental_enabled {
                self.node_hash_cache.clear();
                self.build_root_hash_with_cache(&stem_hashes, 0, B256::ZERO)?
            } else {
                self.build_root_hash_from_stem_hashes(&stem_hashes, 0)?
            };

            let stems: Vec<_> = stem_hashes.iter().map(|(s, _)| *s).collect();
            let root = self.build_tree_from_sorted_stems(&stems, 0)?;

            self.root_hash_cached = root_hash;
            self.root = root;
        }

        self.dirty_stem_hashes.clear();
        Ok(())
    }

    /// Build the root hash directly from sorted stem hashes.
    /// This avoids recomputing stem hashes via `Node::hash`.
    fn build_root_hash_from_stem_hashes(
        &self,
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

        let split_point = stem_hashes.partition_point(|(s, _)| !s.bit_at(depth));
        let (left, right) = stem_hashes.split_at(split_point);

        let left_hash = self.build_root_hash_from_stem_hashes(left, depth + 1)?;
        let right_hash = self.build_root_hash_from_stem_hashes(right, depth + 1)?;

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
        } else if left_hash.is_zero() {
            right_hash
        } else if right_hash.is_zero() {
            left_hash
        } else {
            self.hasher.hash_64(&left_hash, &right_hash)
        };

        self.node_hash_cache.insert((depth, path_prefix), node_hash);
        Ok(node_hash)
    }

    /// Perform incremental root update for dirty stems.
    /// Only recomputes paths from changed stems to root, using cached sibling hashes.
    fn rebuild_root_incremental(&mut self, dirty_stems: &[Stem]) -> Result<()> {
        let mut stem_hashes: Vec<_> = self.stem_hash_cache.iter().map(|(s, h)| (*s, *h)).collect();
        stem_hashes.sort_by_key(|(s, _)| *s);

        if stem_hashes.is_empty() {
            self.root = Node::Empty;
            self.root_hash_cached = B256::ZERO;
            self.node_hash_cache.clear();
            return Ok(());
        }

        let dirty_set: HashSet<_> = dirty_stems.iter().copied().collect();
        let root_hash = self.incremental_hash_update(&stem_hashes, 0, B256::ZERO, &dirty_set)?;

        let stems: Vec<_> = stem_hashes.iter().map(|(s, _)| *s).collect();
        let root = self.build_tree_from_sorted_stems(&stems, 0)?;

        self.root_hash_cached = root_hash;
        self.root = root;

        Ok(())
    }

    /// Check if a stem's path matches the given prefix up to depth bits.
    fn stem_matches_prefix(stem: &Stem, prefix: B256, depth: usize) -> bool {
        for i in 0..depth {
            let stem_bit = stem.bit_at(i);
            let prefix_bit = {
                let byte_idx = i / 8;
                let bit_idx = 7 - (i % 8);
                (prefix.0[byte_idx] >> bit_idx) & 1 == 1
            };
            if stem_bit != prefix_bit {
                return false;
            }
        }
        true
    }

    /// Recursively update the tree hash, only recomputing paths that contain dirty stems.
    fn incremental_hash_update(
        &mut self,
        stem_hashes: &[(Stem, B256)],
        depth: usize,
        path_prefix: B256,
        dirty_stems: &HashSet<Stem>,
    ) -> Result<B256> {
        if stem_hashes.is_empty() {
            self.node_hash_cache.remove(&(depth, path_prefix));
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

        let right_prefix = set_bit_at(path_prefix, depth);

        let left_has_dirty = left.iter().any(|(s, _)| dirty_stems.contains(s))
            || dirty_stems
                .iter()
                .any(|s| !s.bit_at(depth) && Self::stem_matches_prefix(s, path_prefix, depth));
        let right_has_dirty = right.iter().any(|(s, _)| dirty_stems.contains(s))
            || dirty_stems
                .iter()
                .any(|s| s.bit_at(depth) && Self::stem_matches_prefix(s, path_prefix, depth));

        let left_hash =
            if left_has_dirty || !self.node_hash_cache.contains_key(&(depth + 1, path_prefix)) {
                self.incremental_hash_update(left, depth + 1, path_prefix, dirty_stems)?
            } else if left.is_empty() {
                B256::ZERO
            } else {
                *self
                    .node_hash_cache
                    .get(&(depth + 1, path_prefix))
                    .expect("cache entry guaranteed by contains_key check")
            };

        let right_hash = if right_has_dirty
            || !self
                .node_hash_cache
                .contains_key(&(depth + 1, right_prefix))
        {
            self.incremental_hash_update(right, depth + 1, right_prefix, dirty_stems)?
        } else if right.is_empty() {
            B256::ZERO
        } else {
            *self
                .node_hash_cache
                .get(&(depth + 1, right_prefix))
                .expect("cache entry guaranteed by contains_key check")
        };

        let node_hash = if left_hash.is_zero() && right_hash.is_zero() {
            B256::ZERO
        } else if left_hash.is_zero() {
            right_hash
        } else if right_hash.is_zero() {
            left_hash
        } else {
            self.hasher.hash_64(&left_hash, &right_hash)
        };

        self.node_hash_cache.insert((depth, path_prefix), node_hash);
        Ok(node_hash)
    }

    /// Enable incremental root hash updates.
    ///
    /// When enabled, intermediate node hashes are cached to allow O(D * C) updates
    /// where D is tree depth (248) and C is the number of changed stems, instead of
    /// O(S log S) for full rebuilds.
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
    /// // Subsequent updates are O(D * C) instead of O(S log S)
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
    /// # Errors
    ///
    /// Returns an error if the root rebuild exceeds maximum depth.
    pub fn insert_batch(
        &mut self,
        entries: impl IntoIterator<Item = (TreeKey, B256)>,
    ) -> Result<()> {
        for (key, value) in entries {
            let stem_node = self
                .stems
                .entry(key.stem)
                .or_insert_with(|| StemNode::new(key.stem));
            stem_node.set_value(key.subindex, value);
            self.dirty_stem_hashes.insert(key.stem);
        }
        self.rebuild_root()?;
        self.root_dirty = false;
        Ok(())
    }

    /// Batch insert multiple key-value pairs with progress callback.
    ///
    /// # Errors
    ///
    /// Returns an error if the root rebuild exceeds maximum depth.
    pub fn insert_batch_with_progress(
        &mut self,
        entries: impl IntoIterator<Item = (TreeKey, B256)>,
        mut on_progress: impl FnMut(usize),
    ) -> Result<()> {
        let mut count = 0usize;
        for (key, value) in entries {
            let stem_node = self
                .stems
                .entry(key.stem)
                .or_insert_with(|| StemNode::new(key.stem));
            stem_node.set_value(key.subindex, value);
            self.dirty_stem_hashes.insert(key.stem);
            count += 1;
            on_progress(count);
        }
        self.rebuild_root()?;
        self.root_dirty = false;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Blake3Hasher;

    #[test]
    fn test_tree_depth_exceeded_returns_error() {
        let tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        let stem1 = Stem::new([0u8; 31]);
        let mut stem2_bytes = [0u8; 31];
        stem2_bytes[0] = 1;
        let stem2 = Stem::new(stem2_bytes);
        let stem_hashes = vec![(stem1, B256::repeat_byte(1)), (stem2, B256::repeat_byte(2))];

        let err = tree
            .build_root_hash_from_stem_hashes(&stem_hashes, MAX_DEPTH)
            .unwrap_err();
        assert!(matches!(err, UbtError::TreeDepthExceeded { depth } if depth == MAX_DEPTH));
    }
}
