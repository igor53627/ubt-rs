//! Main tree implementation.
//!
//! This module provides [`UnifiedBinaryTree`], the primary data structure for
//! maintaining EIP-7864 state. It supports:
//!
//! - O(1) key-value operations (insert, get, delete)
//! - Lazy root hash computation (only on [`UnifiedBinaryTree::root_hash`] call)
//! - Parallel stem hashing via rayon (when `parallel` feature is enabled)
//! - Incremental root updates via intermediate node caching
//!
//! # Performance Characteristics
//!
//! | Operation | Full Rebuild | Incremental Mode |
//! |-----------|--------------|------------------|
//! | Insert    | O(1)         | O(1)             |
//! | `root_hash` | O(S log S)   | O(S log S) + O(D * C) (structure + hash) |
//!
//! Where S = total stems, D = 248 (tree depth), C = changed stems since last rebuild.
//!
//! Note: incremental mode improves hash recomputation to O(D * C), but the current
//! implementation still sorts stems and rebuilds structure (O(S log S)).

mod build;
mod hash;

use alloy_primitives::B256;
use std::collections::{HashMap, HashSet};

use crate::{Blake3Hasher, Hasher, Node, Stem, StemNode, TreeKey, STEM_LEN};

/// Maximum tree depth (248 bits = 31 bytes * 8)
const MAX_DEPTH: usize = STEM_LEN * 8;

/// Key for intermediate node cache: (depth, `path_prefix` as B256)
/// The `path_prefix` contains the bits from the root to this node.
/// At depth d, only the first d bits are significant.
type NodeCacheKey = (usize, B256);

/// The Unified Binary Tree.
///
/// A binary tree that stores 32-byte values at 32-byte keys.
/// Keys are split into a 31-byte stem (tree path) and 1-byte subindex (within subtree).
///
/// # Implementation Notes
///
/// ## `HashMap` vs `BTreeMap` for stems
///
/// The tree uses `HashMap` for `stems` and `stem_hash_cache` rather than `BTreeMap`.
/// While `BTreeMap` would maintain sorted order (avoiding O(S log S) sort on rebuild),
/// `HashMap` provides O(1) insert vs O(log S) for `BTreeMap`.
///
/// For typical block processing with many inserts per rebuild cycle, `HashMap` is
/// often faster overall. If your workload is rebuild-heavy with few inserts,
/// consider a `BTreeMap`-based variant.
///
/// ## Incremental Mode
///
/// When `enable_incremental_mode()` is called, the tree caches intermediate node
/// hashes in `node_hash_cache`. This makes hash recomputation O(D * C) where D=248
/// (tree depth) and C=changed stems per block.
///
/// Note: the current rebuild path still does structural work (sorting/rebuilding),
/// so end-to-end `root_hash()` may remain O(S log S).
///
/// This is the recommended approach for block-by-block state updates.
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
    /// Cached root hash (computed from `stem_hash_cache`)
    root_hash_cached: B256,
    /// Cache of intermediate node hashes for incremental updates.
    /// Key: (depth, `path_prefix`), Value: hash at that node.
    /// This enables O(D * C) hash recomputation where D=248 depth and C=changed stems.
    /// Note: end-to-end rebuilds still include structural work (e.g., sorting/rebuilding).
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
    /// such as during bulk migrations. This avoids `HashMap` resizing overhead.
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
            // For node_hash_cache, we estimate roughly 2x stems worth of internal nodes,
            // which is an upper bound for a dense binary tree with S leaves. A more
            // precise bound would be O(S), but 2x is a simple, conservative heuristic.
            node_hash_cache: HashMap::with_capacity(capacity * 2),
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
            // For node_hash_cache, we estimate roughly 2x stems worth of internal nodes,
            // which is an upper bound for a dense binary tree with S leaves. A more
            // precise bound would be O(S), but 2x is a simple, conservative heuristic.
            node_hash_cache: HashMap::with_capacity(capacity * 2),
            incremental_enabled: false,
        }
    }

    /// Reserve additional capacity for stems.
    ///
    /// Useful when you discover more stems will be needed after initial creation.
    pub fn reserve_stems(&mut self, additional: usize) {
        self.stems.reserve(additional);
        self.stem_hash_cache.reserve(additional);
        self.node_hash_cache.reserve(additional * 2);
    }

    /// Returns the number of unique stems in the tree.
    pub fn stem_count(&self) -> usize {
        self.stems.len()
    }

    /// Check if the tree is empty.
    pub fn is_empty(&self) -> bool {
        self.stems.is_empty()
    }

    /// Get a value by its full 32-byte key.
    #[must_use]
    pub fn get(&self, key: &TreeKey) -> Option<B256> {
        self.stems
            .get(&key.stem)
            .and_then(|stem_node| stem_node.get_value(key.subindex))
    }

    /// Get a value by B256 key.
    #[must_use]
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_tree() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        assert!(tree.is_empty());
        assert_eq!(tree.root_hash().unwrap(), B256::ZERO);
    }

    #[test]
    fn test_single_insert() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let key = TreeKey::from_bytes(B256::repeat_byte(0x01));
        let value = B256::repeat_byte(0x42);

        tree.insert(key, value);

        assert!(!tree.is_empty());
        assert_eq!(tree.get(&key), Some(value));
        assert_ne!(tree.root_hash().unwrap(), B256::ZERO);
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
        let root = tree.root_hash().unwrap();
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

        assert_eq!(tree1.root_hash().unwrap(), tree2.root_hash().unwrap());
    }

    #[test]
    fn test_with_capacity() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::with_capacity(1000);
        assert!(tree.is_empty());
        assert_eq!(tree.root_hash().unwrap(), B256::ZERO);
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

        let root1 = tree.root_hash().unwrap();

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

        let root2 = tree2.root_hash().unwrap();

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

        let hash1 = tree.root_hash().unwrap();
        assert!(!tree.root_dirty, "root should be clean after root_hash()");
        assert_ne!(hash1, B256::ZERO, "root hash should be non-zero");

        let hash2 = tree.root_hash().unwrap();
        assert_eq!(
            hash1, hash2,
            "calling root_hash() again should return same value"
        );

        let mut tree2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree2.insert(key1, B256::repeat_byte(0x11));
        tree2.insert(key2, B256::repeat_byte(0x22));
        tree2.insert(key3, B256::repeat_byte(0x33));
        let hash3 = tree2.root_hash().unwrap();
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
        let h1 = tree1.root_hash().unwrap();

        tree2.insert(k1, B256::repeat_byte(0x11));
        tree2
            .insert_batch([(k2, B256::repeat_byte(0x22)), (k3, B256::repeat_byte(0x33))])
            .unwrap();
        let h2 = tree2.root_hash().unwrap();

        assert_eq!(h1, h2);
    }

    #[test]
    fn test_insert_batch_clears_dirty_flag() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        let k1 = TreeKey::from_bytes(B256::repeat_byte(0x01));
        let k2 = TreeKey::from_bytes(B256::repeat_byte(0x02));

        tree.insert(k1, B256::repeat_byte(0x11));
        assert!(tree.root_dirty);

        tree.insert_batch([(k2, B256::repeat_byte(0x22))]).unwrap();
        assert!(!tree.root_dirty, "insert_batch should leave root clean");

        tree.root_hash().unwrap();
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
        assert_ne!(tree.root_hash().unwrap(), B256::ZERO);

        tree.delete(&key);
        let root = tree.root_hash().unwrap();
        assert_eq!(root, B256::ZERO);
    }

    #[test]
    fn test_get_or_create_stem_marks_dirty() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let stem = Stem::new([0u8; 31]);

        tree.root_hash().unwrap();
        assert!(!tree.root_dirty);

        let node = tree.get_or_create_stem(stem);
        node.set_value(0, B256::repeat_byte(0x42));
        assert!(tree.root_dirty, "get_or_create_stem should mark root dirty");

        let hash = tree.root_hash().unwrap();
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

        let root1 = tree.root_hash().unwrap();
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

        let root2 = tree.root_hash().unwrap();
        assert_ne!(
            root2,
            B256::ZERO,
            "Root hash should be non-zero after update"
        );
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

        let tree_root = tree.root_hash().unwrap();

        // StreamingTreeBuilder serial mode
        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
        let streaming_serial_root = builder.build_root_hash(entries).unwrap();

        assert_eq!(
            tree_root, streaming_serial_root,
            "UnifiedBinaryTree (parallel enabled) must match StreamingTreeBuilder serial mode"
        );
    }

    /// Tests that parallel stem hashing works correctly with incremental mode enabled.
    ///
    /// This validates that the combination of parallel hashing (for stem computation)
    /// and incremental updates (for node cache) produces correct results across
    /// multiple rebuild cycles.
    #[cfg(feature = "parallel")]
    #[test]
    fn test_parallel_with_incremental_mode() {
        let mut tree_parallel_incr: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let mut tree_parallel_full: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        // Initial inserts
        for i in 0u8..100 {
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = i;
            stem_bytes[10] = i.wrapping_mul(7);
            let stem = Stem::new(stem_bytes);
            let key = TreeKey::new(stem, i % 10);
            let value = B256::repeat_byte(i.max(1));
            tree_parallel_incr.insert(key, value);
            tree_parallel_full.insert(key, value);
        }

        // Both compute initial hash
        let hash1_incr = tree_parallel_incr.root_hash().unwrap();
        let hash1_full = tree_parallel_full.root_hash().unwrap();
        assert_eq!(hash1_incr, hash1_full, "Initial hashes should match");

        // Enable incremental mode on one tree
        tree_parallel_incr.enable_incremental_mode();
        let hash2_incr = tree_parallel_incr.root_hash().unwrap(); // Populates cache
        assert_eq!(
            hash1_incr, hash2_incr,
            "Enabling incremental shouldn't change hash"
        );

        // Modify some stems
        for i in 30u8..50 {
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = i;
            stem_bytes[10] = i.wrapping_mul(7);
            let stem = Stem::new(stem_bytes);
            let key = TreeKey::new(stem, (i % 10) + 1);
            let new_value = B256::repeat_byte(i.wrapping_add(100));
            tree_parallel_incr.insert(key, new_value);
            tree_parallel_full.insert(key, new_value);
        }

        let hash3_incr = tree_parallel_incr.root_hash().unwrap();
        let hash3_full = tree_parallel_full.root_hash().unwrap();
        assert_eq!(
            hash3_incr, hash3_full,
            "Parallel + incremental should match parallel + full rebuild"
        );

        // Delete some stems
        for i in 10u8..20 {
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = i;
            stem_bytes[10] = i.wrapping_mul(7);
            let stem = Stem::new(stem_bytes);
            let key = TreeKey::new(stem, i % 10);
            tree_parallel_incr.delete(&key);
            tree_parallel_full.delete(&key);
        }

        let hash4_incr = tree_parallel_incr.root_hash().unwrap();
        let hash4_full = tree_parallel_full.root_hash().unwrap();
        assert_eq!(
            hash4_incr, hash4_full,
            "Deletes with parallel + incremental should match"
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

        let hash_full_1 = tree_full.root_hash().unwrap();
        let hash_incr_1 = tree_incr.root_hash().unwrap();
        assert_eq!(hash_full_1, hash_incr_1, "Initial hashes should match");

        tree_incr.enable_incremental_mode();
        assert!(tree_incr.is_incremental_enabled());
        assert!(
            tree_incr.node_cache_size() == 0,
            "Cache should be empty before first rebuild"
        );

        let hash_incr_2 = tree_incr.root_hash().unwrap();
        assert_eq!(
            hash_full_1, hash_incr_2,
            "Hash after enabling incremental should match"
        );
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

        let hash_full_3 = tree_full.root_hash().unwrap();
        let hash_incr_3 = tree_incr.root_hash().unwrap();
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

        let hash_full_4 = tree_full.root_hash().unwrap();
        let hash_incr_4 = tree_incr.root_hash().unwrap();
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

        tree_full.root_hash().unwrap();
        tree_incr.root_hash().unwrap();
        tree_incr.enable_incremental_mode();
        tree_incr.root_hash().unwrap();

        for key in &keys[10..20] {
            tree_full.delete(key);
            tree_incr.delete(key);
        }

        let hash_full = tree_full.root_hash().unwrap();
        let hash_incr = tree_incr.root_hash().unwrap();
        assert_eq!(
            hash_full, hash_incr,
            "Deletes with incremental mode should match full rebuild"
        );
    }

    #[test]
    fn test_incremental_empty_tree() {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.enable_incremental_mode();
        assert_eq!(tree.root_hash().unwrap(), B256::ZERO);

        let key = TreeKey::from_bytes(B256::repeat_byte(0x01));
        tree.insert(key, B256::repeat_byte(0x42));
        let h1 = tree.root_hash().unwrap();
        assert_ne!(h1, B256::ZERO);

        tree.delete(&key);
        assert_eq!(tree.root_hash().unwrap(), B256::ZERO);
    }
}
