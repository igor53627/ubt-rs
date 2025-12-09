//! Main tree implementation.

use alloy_primitives::B256;
use std::collections::{HashMap, HashSet};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::{Blake3Hasher, Hasher, InternalNode, Node, Stem, StemNode, TreeKey, STEM_LEN};

/// Maximum tree depth (248 bits = 31 bytes * 8)
const MAX_DEPTH: usize = STEM_LEN * 8;

/// Key for intermediate node cache: (depth, path_prefix as B256)
/// The path_prefix contains the bits from the root to this node.
/// At depth d, only the first d bits are significant.
type NodeCacheKey = (usize, B256);

/// Set bit at the given position in a B256 (MSB-first ordering).
/// Position 0 is the MSB of the first byte.
fn set_bit_at(mut value: B256, pos: usize) -> B256 {
    debug_assert!(pos < 256);
    let byte_idx = pos / 8;
    let bit_idx = 7 - (pos % 8);
    value.0[byte_idx] |= 1 << bit_idx;
    value
}

/// The Unified Binary Tree.
///
/// A binary tree that stores 32-byte values at 32-byte keys.
/// Keys are split into a 31-byte stem (tree path) and 1-byte subindex (within subtree).
#[derive(Clone, Debug)]
pub struct UnifiedBinaryTree<H: Hasher = Blake3Hasher> {
    /// Root node of the tree (kept for potential proof generation)
    root: Node,
    /// Hasher instance
    hasher: H,
    /// Cached stem nodes for efficient access
    stems: HashMap<Stem, StemNode>,
    /// Whether the root hash needs to be recomputed
    root_dirty: bool,
    /// Cache of stem hashes - maps stem to its computed hash
    stem_hash_cache: HashMap<Stem, B256>,
    /// Stems that need their hash recomputed
    dirty_stem_hashes: HashSet<Stem>,
    /// Cached root hash (computed from stem_hash_cache)
    root_hash_cached: B256,
    /// Cache of intermediate node hashes for incremental updates.
    /// Key: (depth, path_prefix), Value: hash at that node.
    /// This enables O(D * C) updates where D=248 depth and C=changed stems,
    /// instead of O(S log S) for full rebuilds.
    node_hash_cache: HashMap<NodeCacheKey, B256>,
    /// Whether incremental mode is active (cache is populated and valid)
    incremental_enabled: bool,
}

impl<H: Hasher> Default for UnifiedBinaryTree<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: Hasher> UnifiedBinaryTree<H> {
    /// Create a new empty tree.
    pub fn new() -> Self {
        Self {
            root: Node::Empty,
            hasher: H::default(),
            stems: HashMap::new(),
            root_dirty: false,
            stem_hash_cache: HashMap::new(),
            dirty_stem_hashes: HashSet::new(),
            root_hash_cached: B256::ZERO,
            node_hash_cache: HashMap::new(),
            incremental_enabled: false,
        }
    }

    /// Create a new tree with a custom hasher.
    pub fn with_hasher(hasher: H) -> Self {
        Self {
            root: Node::Empty,
            hasher,
            stems: HashMap::new(),
            root_dirty: false,
            stem_hash_cache: HashMap::new(),
            dirty_stem_hashes: HashSet::new(),
            root_hash_cached: B256::ZERO,
            node_hash_cache: HashMap::new(),
            incremental_enabled: false,
        }
    }

    /// Create a new empty tree with pre-allocated capacity for stems.
    ///
    /// Use this when you know approximately how many unique stems will be inserted,
    /// such as during bulk migrations. This avoids HashMap resizing overhead.
    ///
    /// # Example
    /// ```
    /// use ubt::{UnifiedBinaryTree, Blake3Hasher};
    /// let tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::with_capacity(1_000_000);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            root: Node::Empty,
            hasher: H::default(),
            stems: HashMap::with_capacity(capacity),
            root_dirty: false,
            stem_hash_cache: HashMap::with_capacity(capacity),
            dirty_stem_hashes: HashSet::new(),
            root_hash_cached: B256::ZERO,
            node_hash_cache: HashMap::new(),
            incremental_enabled: false,
        }
    }

    /// Create a new tree with a custom hasher and pre-allocated capacity.
    pub fn with_hasher_and_capacity(hasher: H, capacity: usize) -> Self {
        Self {
            root: Node::Empty,
            hasher,
            stems: HashMap::with_capacity(capacity),
            root_dirty: false,
            stem_hash_cache: HashMap::with_capacity(capacity),
            dirty_stem_hashes: HashSet::new(),
            root_hash_cached: B256::ZERO,
            node_hash_cache: HashMap::new(),
            incremental_enabled: false,
        }
    }

    /// Reserve additional capacity for stems.
    ///
    /// Useful when you discover more stems will be needed after initial creation.
    pub fn reserve_stems(&mut self, additional: usize) {
        self.stems.reserve(additional);
        self.stem_hash_cache.reserve(additional);
    }

    /// Returns the number of unique stems in the tree.
    pub fn stem_count(&self) -> usize {
        self.stems.len()
    }

    /// Get the root hash of the tree.
    ///
    /// This will trigger a rebuild of the tree structure if any modifications
    /// have been made since the last call to `root_hash()`.
    pub fn root_hash(&mut self) -> B256 {
        if self.root_dirty {
            self.rebuild_root();
            self.root_dirty = false;
        }
        self.root_hash_cached
    }

    /// Check if the tree is empty.
    pub fn is_empty(&self) -> bool {
        self.stems.is_empty()
    }

    /// Get a value by its full 32-byte key.
    pub fn get(&self, key: &TreeKey) -> Option<B256> {
        self.stems
            .get(&key.stem)
            .and_then(|stem_node| stem_node.get_value(key.subindex))
    }

    /// Get a value by B256 key.
    pub fn get_by_b256(&self, key: &B256) -> Option<B256> {
        self.get(&TreeKey::from_bytes(*key))
    }

    /// Insert a value at the given key.
    pub fn insert(&mut self, key: TreeKey, value: B256) {
        let stem_node = self
            .stems
            .entry(key.stem)
            .or_insert_with(|| StemNode::new(key.stem));
        stem_node.set_value(key.subindex, value);
        self.dirty_stem_hashes.insert(key.stem);
        self.root_dirty = true;
    }

    /// Insert a value using a B256 key.
    pub fn insert_b256(&mut self, key: B256, value: B256) {
        self.insert(TreeKey::from_bytes(key), value);
    }

    /// Delete a value at the given key.
    pub fn delete(&mut self, key: &TreeKey) {
        if let Some(stem_node) = self.stems.get_mut(&key.stem) {
            stem_node.set_value(key.subindex, B256::ZERO);

            if stem_node.values.is_empty() {
                self.stems.remove(&key.stem);
            }
        }
        self.dirty_stem_hashes.insert(key.stem);
        self.root_dirty = true;
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
    fn rebuild_root(&mut self) {
        let dirty_stems: Vec<_> = self.dirty_stem_hashes.drain().collect();

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
            return;
        }

        if self.incremental_enabled && !self.node_hash_cache.is_empty() {
            self.rebuild_root_incremental(&dirty_stems);
        } else {
            let mut stem_hashes: Vec<_> = self
                .stem_hash_cache
                .iter()
                .map(|(s, h)| (*s, *h))
                .collect();
            stem_hashes.sort_by_key(|(s, _)| *s);

            if self.incremental_enabled {
                self.node_hash_cache.clear();
                self.root_hash_cached =
                    self.build_root_hash_with_cache(&stem_hashes, 0, B256::ZERO);
            } else {
                self.root_hash_cached = self.build_root_hash_from_stem_hashes(&stem_hashes, 0);
            }

            let stems: Vec<_> = stem_hashes.iter().map(|(s, _)| *s).collect();
            self.root = self.build_tree_from_sorted_stems(&stems, 0);
        }
    }

    /// Rebuild the root from all stem nodes (parallel version).
    #[cfg(feature = "parallel")]
    fn rebuild_root(&mut self) {
        let dirty_stems: Vec<_> = self.dirty_stem_hashes.drain().collect();

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
            return;
        }

        if self.incremental_enabled && !self.node_hash_cache.is_empty() {
            self.rebuild_root_incremental(&dirty_stems);
        } else {
            let mut stem_hashes: Vec<_> = self
                .stem_hash_cache
                .iter()
                .map(|(s, h)| (*s, *h))
                .collect();
            stem_hashes.sort_by_key(|(s, _)| *s);

            if self.incremental_enabled {
                self.node_hash_cache.clear();
                self.root_hash_cached =
                    self.build_root_hash_with_cache(&stem_hashes, 0, B256::ZERO);
            } else {
                self.root_hash_cached = self.build_root_hash_from_stem_hashes(&stem_hashes, 0);
            }

            let stems: Vec<_> = stem_hashes.iter().map(|(s, _)| *s).collect();
            self.root = self.build_tree_from_sorted_stems(&stems, 0);
        }
    }

    /// Build the root hash directly from sorted stem hashes.
    /// This avoids recomputing stem hashes via Node::hash.
    fn build_root_hash_from_stem_hashes(&self, stem_hashes: &[(Stem, B256)], depth: usize) -> B256 {
        if stem_hashes.is_empty() {
            return B256::ZERO;
        }

        if stem_hashes.len() == 1 {
            return stem_hashes[0].1;
        }

        if depth >= 248 {
            panic!("Tree depth exceeded maximum of 248 bits");
        }

        let split_point = stem_hashes.partition_point(|(s, _)| !s.bit_at(depth));
        let (left, right) = stem_hashes.split_at(split_point);

        let left_hash = self.build_root_hash_from_stem_hashes(left, depth + 1);
        let right_hash = self.build_root_hash_from_stem_hashes(right, depth + 1);

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

    /// Build the root hash and populate the node_hash_cache for incremental updates.
    /// This version caches all intermediate node hashes.
    fn build_root_hash_with_cache(
        &mut self,
        stem_hashes: &[(Stem, B256)],
        depth: usize,
        path_prefix: B256,
    ) -> B256 {
        if stem_hashes.is_empty() {
            return B256::ZERO;
        }

        if stem_hashes.len() == 1 {
            let hash = stem_hashes[0].1;
            self.node_hash_cache.insert((depth, path_prefix), hash);
            return hash;
        }

        if depth >= MAX_DEPTH {
            panic!("Tree depth exceeded maximum of {} bits", MAX_DEPTH);
        }

        let split_point = stem_hashes.partition_point(|(s, _)| !s.bit_at(depth));
        let (left, right) = stem_hashes.split_at(split_point);

        let left_hash = self.build_root_hash_with_cache(left, depth + 1, path_prefix);
        let right_prefix = set_bit_at(path_prefix, depth);
        let right_hash = self.build_root_hash_with_cache(right, depth + 1, right_prefix);

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
        node_hash
    }

    /// Perform incremental root update for dirty stems.
    /// Only recomputes paths from changed stems to root, using cached sibling hashes.
    fn rebuild_root_incremental(&mut self, dirty_stems: &[Stem]) {
        let mut stem_hashes: Vec<_> = self
            .stem_hash_cache
            .iter()
            .map(|(s, h)| (*s, *h))
            .collect();
        stem_hashes.sort_by_key(|(s, _)| *s);

        if stem_hashes.is_empty() {
            self.root = Node::Empty;
            self.root_hash_cached = B256::ZERO;
            self.node_hash_cache.clear();
            return;
        }

        let dirty_set: HashSet<_> = dirty_stems.iter().cloned().collect();
        self.root_hash_cached =
            self.incremental_hash_update(&stem_hashes, 0, B256::ZERO, &dirty_set);

        let stems: Vec<_> = stem_hashes.iter().map(|(s, _)| *s).collect();
        self.root = self.build_tree_from_sorted_stems(&stems, 0);
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
    ) -> B256 {
        if stem_hashes.is_empty() {
            self.node_hash_cache.remove(&(depth, path_prefix));
            return B256::ZERO;
        }

        if stem_hashes.len() == 1 {
            let hash = stem_hashes[0].1;
            self.node_hash_cache.insert((depth, path_prefix), hash);
            return hash;
        }

        if depth >= MAX_DEPTH {
            panic!("Tree depth exceeded maximum of {} bits", MAX_DEPTH);
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

        let left_hash = if left_has_dirty
            || !self
                .node_hash_cache
                .contains_key(&(depth + 1, path_prefix))
        {
            self.incremental_hash_update(left, depth + 1, path_prefix, dirty_stems)
        } else if left.is_empty() {
            B256::ZERO
        } else {
            *self.node_hash_cache.get(&(depth + 1, path_prefix)).unwrap()
        };

        let right_hash = if right_has_dirty
            || !self
                .node_hash_cache
                .contains_key(&(depth + 1, right_prefix))
        {
            self.incremental_hash_update(right, depth + 1, right_prefix, dirty_stems)
        } else if right.is_empty() {
            B256::ZERO
        } else {
            *self.node_hash_cache.get(&(depth + 1, right_prefix)).unwrap()
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
        node_hash
    }

    /// Enable incremental root updates.
    ///
    /// After calling this, subsequent root_hash() calls will only recompute
    /// paths from changed stems to root, using cached intermediate hashes.
    /// This is beneficial when a small number of stems change per block.
    ///
    /// The first call after enabling incremental mode will do a full rebuild
    /// to populate the cache.
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

    /// Build the tree structure from a sorted list of stems using slice partitioning.
    /// This is O(n) per level with no allocations, compared to the previous O(n) allocations per level.
    fn build_tree_from_sorted_stems(&self, stems: &[Stem], depth: usize) -> Node {
        if stems.is_empty() {
            return Node::Empty;
        }

        if stems.len() == 1 {
            let stem = &stems[0];
            if let Some(stem_node) = self.stems.get(stem) {
                return Node::Stem(stem_node.clone());
            }
            return Node::Empty;
        }

        if depth >= 248 {
            panic!("Tree depth exceeded maximum of 248 bits");
        }

        // Use partition_point for O(n) split with no allocation
        // partition_point returns the index where bit_at(depth) becomes true
        // This works because stems are sorted lexicographically, so all stems
        // with bit 0 at this depth come before all stems with bit 1
        let split_point = stems.partition_point(|s| !s.bit_at(depth));
        let (left_stems, right_stems) = stems.split_at(split_point);

        let left = self.build_tree_from_sorted_stems(left_stems, depth + 1);
        let right = self.build_tree_from_sorted_stems(right_stems, depth + 1);

        if left.is_empty() && right.is_empty() {
            Node::Empty
        } else if left.is_empty() {
            right
        } else if right.is_empty() {
            left
        } else {
            Node::Internal(InternalNode::new(left, right))
        }
    }

    /// Get mutable access to a stem node, creating it if it doesn't exist.
    ///
    /// Note: This is a low-level mutating API. Any modifications to the returned
    /// `StemNode` will affect the tree's root hash.
    pub fn get_or_create_stem(&mut self, stem: Stem) -> &mut StemNode {
        self.dirty_stem_hashes.insert(stem);
        self.root_dirty = true;
        self.stems
            .entry(stem)
            .or_insert_with(|| StemNode::new(stem))
    }

    /// Iterate over all (key, value) pairs in the tree.
    pub fn iter(&self) -> impl Iterator<Item = (TreeKey, B256)> + '_ {
        self.stems.iter().flat_map(|(stem, stem_node)| {
            stem_node
                .values
                .iter()
                .map(move |(&subindex, &value)| (TreeKey::new(*stem, subindex), value))
        })
    }

    /// Get the number of non-empty values in the tree.
    pub fn len(&self) -> usize {
        self.stems.values().map(|s| s.values.len()).sum()
    }

    /// Verify a value exists at a key.
    pub fn contains_key(&self, key: &TreeKey) -> bool {
        self.get(key).is_some()
    }

    /// Batch insert multiple key-value pairs.
    pub fn insert_batch(&mut self, entries: impl IntoIterator<Item = (TreeKey, B256)>) {
        for (key, value) in entries {
            let stem_node = self
                .stems
                .entry(key.stem)
                .or_insert_with(|| StemNode::new(key.stem));
            stem_node.set_value(key.subindex, value);
            self.dirty_stem_hashes.insert(key.stem);
        }
        self.rebuild_root();
        self.root_dirty = false;
    }

    /// Batch insert multiple key-value pairs with progress callback.
    pub fn insert_batch_with_progress(
        &mut self,
        entries: impl IntoIterator<Item = (TreeKey, B256)>,
        mut on_progress: impl FnMut(usize),
    ) {
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
        self.rebuild_root();
        self.root_dirty = false;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_tree() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        assert!(tree.is_empty());
        assert_eq!(tree.root_hash(), B256::ZERO);
    }

    #[test]
    fn test_single_insert() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let key = TreeKey::from_bytes(B256::repeat_byte(0x01));
        let value = B256::repeat_byte(0x42);

        tree.insert(key, value);

        assert!(!tree.is_empty());
        assert_eq!(tree.get(&key), Some(value));
        assert_ne!(tree.root_hash(), B256::ZERO);
    }

    #[test]
    fn test_multiple_inserts_same_stem() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let stem = Stem::new([0u8; 31]);

        let key1 = TreeKey::new(stem, 0);
        let key2 = TreeKey::new(stem, 1);

        tree.insert(key1, B256::repeat_byte(0x01));
        tree.insert(key2, B256::repeat_byte(0x02));

        assert_eq!(tree.get(&key1), Some(B256::repeat_byte(0x01)));
        assert_eq!(tree.get(&key2), Some(B256::repeat_byte(0x02)));
        assert_eq!(tree.len(), 2);
    }

    #[test]
    fn test_multiple_inserts_different_stems() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        let mut stem1_bytes = [0u8; 31];
        stem1_bytes[0] = 0b00000000;
        let stem1 = Stem::new(stem1_bytes);

        let mut stem2_bytes = [0u8; 31];
        stem2_bytes[0] = 0b10000000;
        let stem2 = Stem::new(stem2_bytes);

        tree.insert(TreeKey::new(stem1, 0), B256::repeat_byte(0x01));
        tree.insert(TreeKey::new(stem2, 0), B256::repeat_byte(0x02));

        assert_eq!(tree.len(), 2);
        let root = tree.root_hash();
        assert_ne!(root, B256::ZERO);
    }

    #[test]
    fn test_delete() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let key = TreeKey::from_bytes(B256::repeat_byte(0x01));

        tree.insert(key, B256::repeat_byte(0x42));
        assert_eq!(tree.get(&key), Some(B256::repeat_byte(0x42)));

        tree.delete(&key);
        assert_eq!(tree.get(&key), None);
    }

    #[test]
    fn test_root_hash_deterministic() {
        let mut tree1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let mut tree2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        let key1 = TreeKey::from_bytes(B256::repeat_byte(0x01));
        let key2 = TreeKey::from_bytes(B256::repeat_byte(0x02));

        tree1.insert(key1, B256::repeat_byte(0x11));
        tree1.insert(key2, B256::repeat_byte(0x22));

        tree2.insert(key2, B256::repeat_byte(0x22));
        tree2.insert(key1, B256::repeat_byte(0x11));

        assert_eq!(tree1.root_hash(), tree2.root_hash());
    }

    #[test]
    fn test_with_capacity() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::with_capacity(1000);
        assert!(tree.is_empty());
        assert_eq!(tree.root_hash(), B256::ZERO);
    }

    #[test]
    fn test_with_hasher_and_capacity() {
        let hasher = Blake3Hasher;
        let tree: UnifiedBinaryTree<Blake3Hasher> =
            UnifiedBinaryTree::with_hasher_and_capacity(hasher, 1000);
        assert!(tree.is_empty());
    }

    #[test]
    fn test_reserve_stems() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.reserve_stems(1000);
        let key = TreeKey::from_bytes(B256::repeat_byte(0x01));
        tree.insert(key, B256::repeat_byte(0x42));
        assert_eq!(tree.get(&key), Some(B256::repeat_byte(0x42)));
    }

    #[test]
    fn test_stem_count() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        assert_eq!(tree.stem_count(), 0);

        let stem = Stem::new([0u8; 31]);
        tree.insert(TreeKey::new(stem, 0), B256::repeat_byte(0x01));
        tree.insert(TreeKey::new(stem, 1), B256::repeat_byte(0x02));
        assert_eq!(tree.stem_count(), 1);

        let mut stem2_bytes = [0u8; 31];
        stem2_bytes[0] = 0xFF;
        let stem2 = Stem::new(stem2_bytes);
        tree.insert(TreeKey::new(stem2, 0), B256::repeat_byte(0x03));
        assert_eq!(tree.stem_count(), 2);
    }

    #[test]
    fn test_sorted_stems_produces_deterministic_root() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        // Insert many keys with different stems
        for i in 0u8..=255 {
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = i;
            stem_bytes[15] = i.wrapping_add(128);
            let stem = Stem::new(stem_bytes);
            let key = TreeKey::new(stem, i);
            tree.insert(key, B256::repeat_byte(i));
        }

        let root1 = tree.root_hash();

        // Create another tree with same data in different order
        let mut tree2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        for i in (0u8..=255).rev() {
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = i;
            stem_bytes[15] = i.wrapping_add(128);
            let stem = Stem::new(stem_bytes);
            let key = TreeKey::new(stem, i);
            tree2.insert(key, B256::repeat_byte(i));
        }

        let root2 = tree2.root_hash();

        assert_eq!(
            root1, root2,
            "Sorted stem tree building should produce deterministic roots"
        );
    }

    #[test]
    fn test_deferred_root_computation() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        let key1 = TreeKey::from_bytes(B256::repeat_byte(0x01));
        let key2 = TreeKey::from_bytes(B256::repeat_byte(0x02));
        let key3 = TreeKey::from_bytes(B256::repeat_byte(0x03));

        tree.insert(key1, B256::repeat_byte(0x11));
        assert!(tree.root_dirty, "root should be dirty after first insert");

        tree.insert(key2, B256::repeat_byte(0x22));
        assert!(
            tree.root_dirty,
            "root should still be dirty after second insert"
        );

        tree.insert(key3, B256::repeat_byte(0x33));
        assert!(
            tree.root_dirty,
            "root should still be dirty after third insert"
        );

        let hash1 = tree.root_hash();
        assert!(!tree.root_dirty, "root should be clean after root_hash()");
        assert_ne!(hash1, B256::ZERO, "root hash should be non-zero");

        let hash2 = tree.root_hash();
        assert_eq!(
            hash1, hash2,
            "calling root_hash() again should return same value"
        );

        let mut tree2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree2.insert(key1, B256::repeat_byte(0x11));
        tree2.insert(key2, B256::repeat_byte(0x22));
        tree2.insert(key3, B256::repeat_byte(0x33));
        let hash3 = tree2.root_hash();
        assert_eq!(
            hash1, hash3,
            "deferred computation should produce same hash as immediate"
        );
    }

    #[test]
    fn test_mixed_single_and_batch_inserts_root() {
        let mut tree1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let mut tree2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        let k1 = TreeKey::from_bytes(B256::repeat_byte(0x01));
        let k2 = TreeKey::from_bytes(B256::repeat_byte(0x02));
        let k3 = TreeKey::from_bytes(B256::repeat_byte(0x03));

        tree1.insert(k1, B256::repeat_byte(0x11));
        tree1.insert(k2, B256::repeat_byte(0x22));
        tree1.insert(k3, B256::repeat_byte(0x33));
        let h1 = tree1.root_hash();

        tree2.insert(k1, B256::repeat_byte(0x11));
        tree2.insert_batch([
            (k2, B256::repeat_byte(0x22)),
            (k3, B256::repeat_byte(0x33)),
        ]);
        let h2 = tree2.root_hash();

        assert_eq!(h1, h2);
    }

    #[test]
    fn test_insert_batch_clears_dirty_flag() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        let k1 = TreeKey::from_bytes(B256::repeat_byte(0x01));
        let k2 = TreeKey::from_bytes(B256::repeat_byte(0x02));

        tree.insert(k1, B256::repeat_byte(0x11));
        assert!(tree.root_dirty);

        tree.insert_batch([(k2, B256::repeat_byte(0x22))]);
        assert!(!tree.root_dirty, "insert_batch should leave root clean");

        let _ = tree.root_hash();
        assert!(
            !tree.root_dirty,
            "root_hash after clean batch should keep root clean"
        );
    }

    #[test]
    fn test_delete_to_empty_resets_root_hash() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let key = TreeKey::from_bytes(B256::repeat_byte(0x01));

        tree.insert(key, B256::repeat_byte(0x42));
        assert_ne!(tree.root_hash(), B256::ZERO);

        tree.delete(&key);
        let root = tree.root_hash();
        assert_eq!(root, B256::ZERO);
    }

    #[test]
    fn test_get_or_create_stem_marks_dirty() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let stem = Stem::new([0u8; 31]);

        let _ = tree.root_hash();
        assert!(!tree.root_dirty);

        let node = tree.get_or_create_stem(stem);
        node.set_value(0, B256::repeat_byte(0x42));
        assert!(tree.root_dirty, "get_or_create_stem should mark root dirty");

        let hash = tree.root_hash();
        assert_ne!(hash, B256::ZERO);
    }

    /// Tests parallel stem hashing with a large number of stems (201).
    ///
    /// This test exercises the parallel hashing code path by creating enough stems
    /// to trigger rayon's parallel iteration (typically > 100 stems).
    ///
    /// # Correctness Validation
    ///
    /// 1. **Non-empty output**: Root hash must be non-zero, confirming hashing ran.
    /// 2. **Determinism**: Modifying stems and recomputing produces a different hash,
    ///    confirming the hash reflects actual data (not a constant).
    /// 3. **Insertion-order independence**: See `test_root_hash_deterministic` which
    ///    validates that different insertion orders produce the same hash.
    /// 4. **Parallel vs serial equivalence**: See `test_parallel_matches_non_parallel`
    ///    which validates that parallel mode produces the same hash as serial mode.
    #[cfg(feature = "parallel")]
    #[test]
    fn test_parallel_rebuild_many_stems() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        // Insert many keys with different stems to exercise parallel hashing
        for i in 0u8..=200 {
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = i;
            stem_bytes[15] = i.wrapping_add(128);
            let stem = Stem::new(stem_bytes);
            let key = TreeKey::new(stem, i % 10);
            tree.insert(key, B256::repeat_byte(i.max(1)));
        }

        let root1 = tree.root_hash();
        assert_ne!(root1, B256::ZERO, "Root hash should be non-zero");

        // Modify some stems and recompute
        for i in 50u8..100 {
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = i;
            stem_bytes[15] = i.wrapping_add(128);
            let stem = Stem::new(stem_bytes);
            let key = TreeKey::new(stem, (i % 10) + 1);
            tree.insert(key, B256::repeat_byte(i.wrapping_mul(2).max(1)));
        }

        let root2 = tree.root_hash();
        assert_ne!(root2, B256::ZERO, "Root hash should be non-zero after update");
        assert_ne!(root1, root2, "Root hash should change after modifications");
    }

    /// Validates that parallel stem hashing produces identical results to serial hashing.
    ///
    /// This test compares `UnifiedBinaryTree` (which uses parallel hashing when enabled)
    /// against `StreamingTreeBuilder` in serial mode. Both must produce the exact same
    /// root hash for identical input data.
    ///
    /// # Correctness Criteria
    ///
    /// Given identical input data, parallel and serial computation must produce the
    /// exact same root hash. This validates that:
    /// - Parallel aggregation order doesn't affect the final hash
    /// - Thread scheduling variations don't cause non-determinism
    /// - The parallel implementation is a drop-in replacement for serial
    #[cfg(feature = "parallel")]
    #[test]
    fn test_parallel_matches_non_parallel() {
        use crate::StreamingTreeBuilder;

        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let mut entries: Vec<(TreeKey, B256)> = Vec::new();

        for i in 0u8..100 {
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = i;
            stem_bytes[10] = i.wrapping_mul(7);
            let stem = Stem::new(stem_bytes);
            let key = TreeKey::new(stem, i % 10);
            let value = B256::repeat_byte(i.max(1));
            tree.insert(key, value);
            entries.push((key, value));
        }

        entries.sort_by(|a, b| (a.0.stem, a.0.subindex).cmp(&(b.0.stem, b.0.subindex)));

        let tree_root = tree.root_hash();

        // StreamingTreeBuilder serial mode
        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
        let streaming_serial_root = builder.build_root_hash(entries);

        assert_eq!(
            tree_root, streaming_serial_root,
            "UnifiedBinaryTree (parallel enabled) must match StreamingTreeBuilder serial mode"
        );
    }

    #[test]
    fn test_incremental_mode_matches_full_rebuild() {
        let mut tree_full: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let mut tree_incr: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        for i in 0u8..100 {
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = i;
            stem_bytes[10] = i.wrapping_mul(7);
            let stem = Stem::new(stem_bytes);
            let key = TreeKey::new(stem, i % 10);
            tree_full.insert(key, B256::repeat_byte(i.max(1)));
            tree_incr.insert(key, B256::repeat_byte(i.max(1)));
        }

        let hash_full_1 = tree_full.root_hash();
        let hash_incr_1 = tree_incr.root_hash();
        assert_eq!(hash_full_1, hash_incr_1, "Initial hashes should match");

        tree_incr.enable_incremental_mode();
        assert!(tree_incr.is_incremental_enabled());
        assert!(tree_incr.node_cache_size() == 0, "Cache should be empty before first rebuild");

        let hash_incr_2 = tree_incr.root_hash();
        assert_eq!(hash_full_1, hash_incr_2, "Hash after enabling incremental should match");
        assert!(tree_incr.node_cache_size() > 0, "Cache should be populated");

        for i in 20u8..30 {
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = i;
            stem_bytes[10] = i.wrapping_mul(7);
            let stem = Stem::new(stem_bytes);
            let key = TreeKey::new(stem, (i % 10) + 1);
            let new_value = B256::repeat_byte(i.wrapping_add(100));
            tree_full.insert(key, new_value);
            tree_incr.insert(key, new_value);
        }

        let hash_full_3 = tree_full.root_hash();
        let hash_incr_3 = tree_incr.root_hash();
        assert_eq!(
            hash_full_3, hash_incr_3,
            "Incremental update should produce same hash as full rebuild"
        );
        assert_ne!(hash_full_1, hash_full_3, "Hash should change after updates");

        for i in 200u8..210 {
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = i;
            stem_bytes[5] = i;
            let stem = Stem::new(stem_bytes);
            let key = TreeKey::new(stem, 0);
            tree_full.insert(key, B256::repeat_byte(i));
            tree_incr.insert(key, B256::repeat_byte(i));
        }

        let hash_full_4 = tree_full.root_hash();
        let hash_incr_4 = tree_incr.root_hash();
        assert_eq!(
            hash_full_4, hash_incr_4,
            "Adding new stems with incremental should match full rebuild"
        );

        tree_incr.disable_incremental_mode();
        assert!(!tree_incr.is_incremental_enabled());
        assert_eq!(tree_incr.node_cache_size(), 0);
    }

    #[test]
    fn test_incremental_delete_matches_full() {
        let mut tree_full: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let mut tree_incr: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        let keys: Vec<_> = (0u8..50)
            .map(|i| {
                let mut stem_bytes = [0u8; 31];
                stem_bytes[0] = i;
                TreeKey::new(Stem::new(stem_bytes), 0)
            })
            .collect();

        for (i, key) in keys.iter().enumerate() {
            tree_full.insert(*key, B256::repeat_byte((i as u8).max(1)));
            tree_incr.insert(*key, B256::repeat_byte((i as u8).max(1)));
        }

        tree_full.root_hash();
        tree_incr.root_hash();
        tree_incr.enable_incremental_mode();
        tree_incr.root_hash();

        for key in &keys[10..20] {
            tree_full.delete(key);
            tree_incr.delete(key);
        }

        let hash_full = tree_full.root_hash();
        let hash_incr = tree_incr.root_hash();
        assert_eq!(
            hash_full, hash_incr,
            "Deletes with incremental mode should match full rebuild"
        );
    }

    #[test]
    fn test_incremental_empty_tree() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.enable_incremental_mode();
        assert_eq!(tree.root_hash(), B256::ZERO);

        let key = TreeKey::from_bytes(B256::repeat_byte(0x01));
        tree.insert(key, B256::repeat_byte(0x42));
        let h1 = tree.root_hash();
        assert_ne!(h1, B256::ZERO);

        tree.delete(&key);
        assert_eq!(tree.root_hash(), B256::ZERO);
    }
}
