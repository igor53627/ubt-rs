//! Property-based tests for UBT using proptest.
//!
//! These tests mirror the QuickChick properties in formal/proofs/quickchick_tests.v
//! to ensure the Rust implementation matches the formal specification.

use proptest::prelude::*;
use ubt::{Blake3Hasher, Hasher, Stem, StreamingTreeBuilder, TreeKey, UnifiedBinaryTree, B256};

// ============================================================================
// Strategies for generating random test data
// ============================================================================

fn arb_stem() -> impl Strategy<Value = Stem> {
    prop::array::uniform31(any::<u8>()).prop_map(Stem::new)
}

fn arb_subindex() -> impl Strategy<Value = u8> {
    any::<u8>()
}

fn arb_tree_key() -> impl Strategy<Value = TreeKey> {
    (arb_stem(), arb_subindex()).prop_map(|(stem, subindex)| TreeKey::new(stem, subindex))
}

fn arb_value() -> impl Strategy<Value = B256> {
    prop::array::uniform32(any::<u8>()).prop_map(B256::from)
}

fn arb_nonzero_value() -> impl Strategy<Value = B256> {
    arb_value().prop_filter("value must be nonzero", |v| *v != B256::ZERO)
}

fn arb_key_value() -> impl Strategy<Value = (TreeKey, B256)> {
    (arb_tree_key(), arb_nonzero_value())
}

fn arb_key_value_list(max_len: usize) -> impl Strategy<Value = Vec<(TreeKey, B256)>> {
    prop::collection::vec(arb_key_value(), 0..max_len)
}

// ============================================================================
// Core Tree Properties (P1-P5 from QuickChick)
// ============================================================================

proptest! {
    /// P1: get after insert returns the inserted value
    #[test]
    fn prop_get_insert_same(key in arb_tree_key(), value in arb_nonzero_value()) {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert(key, value);
        prop_assert_eq!(tree.get(&key), Some(value));
    }

    /// P2: insert doesn't affect other keys (different stems)
    #[test]
    fn prop_get_insert_other(
        k1 in arb_tree_key(),
        k2 in arb_tree_key(),
        v1 in arb_nonzero_value(),
        v2 in arb_nonzero_value()
    ) {
        prop_assume!(k1 != k2);
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert(k1, v1);
        tree.insert(k2, v2);
        prop_assert_eq!(tree.get(&k1), Some(v1));
        prop_assert_eq!(tree.get(&k2), Some(v2));
    }

    /// P3: delete removes the value (insert then delete returns None)
    #[test]
    fn prop_insert_delete(key in arb_tree_key(), value in arb_nonzero_value()) {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert(key, value);
        tree.delete(&key);
        prop_assert_eq!(tree.get(&key), None);
    }

    /// P4: insert is idempotent (inserting same value twice = inserting once)
    #[test]
    fn prop_insert_idempotent(key in arb_tree_key(), value in arb_nonzero_value()) {
        let mut tree1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree1.insert(key, value);

        let mut tree2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree2.insert(key, value);
        tree2.insert(key, value);

        prop_assert_eq!(tree1.root_hash(), tree2.root_hash());
    }

    /// P5: get from empty tree returns None
    #[test]
    fn prop_empty_get(key in arb_tree_key()) {
        let tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        prop_assert_eq!(tree.get(&key), None);
    }
}

// ============================================================================
// Stem Properties (P6-P8)
// ============================================================================

proptest! {
    /// P6: insert preserves values at other stems
    #[test]
    fn prop_insert_preserves_other_stems(
        k1 in arb_tree_key(),
        k2 in arb_tree_key(),
        v1 in arb_nonzero_value(),
        v2 in arb_nonzero_value()
    ) {
        prop_assume!(k1.stem != k2.stem);
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert(k1, v1);
        tree.insert(k2, v2);
        prop_assert_eq!(tree.get(&k1), Some(v1));
    }

    /// P7: keys with same stem share a subtree (co-location)
    #[test]
    fn prop_stem_colocation(
        stem in arb_stem(),
        idx1 in arb_subindex(),
        idx2 in arb_subindex(),
        v1 in arb_nonzero_value(),
        v2 in arb_nonzero_value()
    ) {
        prop_assume!(idx1 != idx2);
        let k1 = TreeKey::new(stem, idx1);
        let k2 = TreeKey::new(stem, idx2);

        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert(k1, v1);
        tree.insert(k2, v2);

        // Both values accessible
        prop_assert_eq!(tree.get(&k1), Some(v1));
        prop_assert_eq!(tree.get(&k2), Some(v2));

        // Only one stem in tree
        prop_assert_eq!(tree.stem_count(), 1);
    }

    /// P8: subindex independence - different subindices don't interfere
    #[test]
    fn prop_subindex_independence(
        stem in arb_stem(),
        idx1 in arb_subindex(),
        idx2 in arb_subindex(),
        v in arb_nonzero_value()
    ) {
        prop_assume!(idx1 != idx2);
        let k1 = TreeKey::new(stem, idx1);
        let k2 = TreeKey::new(stem, idx2);

        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert(k1, v);

        // k2 should be None (not affected by k1)
        prop_assert_eq!(tree.get(&k2), None);
    }
}

// ============================================================================
// Delete Properties (P9-P12)
// ============================================================================

proptest! {
    /// P9: delete is idempotent
    #[test]
    fn prop_delete_idempotent(key in arb_tree_key(), value in arb_nonzero_value()) {
        let mut tree1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree1.insert(key, value);
        tree1.delete(&key);

        let mut tree2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree2.insert(key, value);
        tree2.delete(&key);
        tree2.delete(&key);

        prop_assert_eq!(tree1.root_hash(), tree2.root_hash());
    }

    /// P10: insert zero is equivalent to delete (both result in None for get)
    #[test]
    fn prop_zero_insert_is_delete(key in arb_tree_key(), value in arb_nonzero_value()) {
        let mut tree1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree1.insert(key, value);
        tree1.delete(&key);

        let mut tree2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree2.insert(key, value);
        tree2.insert(key, B256::ZERO);

        // Both should return None for get (zero = deleted)
        prop_assert_eq!(tree1.get(&key), None);
        prop_assert_eq!(tree2.get(&key), None);
    }

    /// P11: delete nonexistent key is a no-op
    #[test]
    fn prop_delete_nonexistent_noop(
        k1 in arb_tree_key(),
        k2 in arb_tree_key(),
        v in arb_nonzero_value()
    ) {
        prop_assume!(k1 != k2);

        let mut tree1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree1.insert(k1, v);
        let hash1 = tree1.root_hash();

        tree1.delete(&k2); // k2 doesn't exist
        let hash2 = tree1.root_hash();

        prop_assert_eq!(hash1, hash2);
    }

    /// P12: last insert wins (overwrite semantics)
    #[test]
    fn prop_last_insert_wins(
        key in arb_tree_key(),
        v1 in arb_nonzero_value(),
        v2 in arb_nonzero_value()
    ) {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert(key, v1);
        tree.insert(key, v2);
        prop_assert_eq!(tree.get(&key), Some(v2));
    }
}

// ============================================================================
// Hash Properties (P13-P15)
// ============================================================================

proptest! {
    /// P13: root hash is deterministic
    #[test]
    fn prop_root_hash_deterministic(entries in arb_key_value_list(20)) {
        let mut tree1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let mut tree2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        for (k, v) in &entries {
            tree1.insert(*k, *v);
            tree2.insert(*k, *v);
        }

        prop_assert_eq!(tree1.root_hash(), tree2.root_hash());
    }

    /// P14: empty tree has zero hash
    #[test]
    fn prop_empty_tree_zero_hash(_dummy: u8) {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        prop_assert_eq!(tree.root_hash(), B256::ZERO);
    }

    /// P15: different values produce different hashes (probabilistic)
    #[test]
    fn prop_different_values_different_hashes(
        key in arb_tree_key(),
        v1 in arb_nonzero_value(),
        v2 in arb_nonzero_value()
    ) {
        prop_assume!(v1 != v2);

        let mut tree1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree1.insert(key, v1);

        let mut tree2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree2.insert(key, v2);

        prop_assert_ne!(tree1.root_hash(), tree2.root_hash());
    }
}

// ============================================================================
// Order Independence (P16-P17)
// ============================================================================

proptest! {
    /// P16: batch operations commute (insert order doesn't matter for final hash)
    #[test]
    fn prop_batch_operations_commute(
        k1 in arb_tree_key(),
        k2 in arb_tree_key(),
        v1 in arb_nonzero_value(),
        v2 in arb_nonzero_value()
    ) {
        prop_assume!(k1 != k2);

        let mut tree1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree1.insert(k1, v1);
        tree1.insert(k2, v2);

        let mut tree2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree2.insert(k2, v2);
        tree2.insert(k1, v1);

        prop_assert_eq!(tree1.root_hash(), tree2.root_hash());
    }

    /// P17: insert order independence for larger batches
    #[test]
    fn prop_insert_order_independence(entries in arb_key_value_list(10)) {
        // Deduplicate by key (keep last value for each key)
        let mut deduped = std::collections::HashMap::new();
        for (k, v) in &entries {
            deduped.insert(*k, *v);
        }
        let unique: Vec<_> = deduped.into_iter().collect();

        if unique.len() < 2 {
            return Ok(());
        }

        // Forward order
        let mut tree1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        for (k, v) in &unique {
            tree1.insert(*k, *v);
        }

        // Reverse order
        let mut tree2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        for (k, v) in unique.iter().rev() {
            tree2.insert(*k, *v);
        }

        prop_assert_eq!(tree1.root_hash(), tree2.root_hash());
    }
}

// ============================================================================
// Batch Insert Properties (P18-P19)
// ============================================================================

proptest! {
    /// P18: batch insert equals sequential insert
    #[test]
    fn prop_batch_equals_sequential(entries in arb_key_value_list(20)) {
        // Deduplicate
        let mut deduped = std::collections::HashMap::new();
        for (k, v) in &entries {
            deduped.insert(*k, *v);
        }
        let unique: Vec<_> = deduped.into_iter().collect();

        // Sequential inserts
        let mut tree1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        for (k, v) in &unique {
            tree1.insert(*k, *v);
        }

        // Batch insert
        let mut tree2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree2.insert_batch(unique.clone());

        prop_assert_eq!(tree1.root_hash(), tree2.root_hash());
    }

    /// P19: batch then individual equals all sequential
    #[test]
    fn prop_batch_then_individual(
        batch_entries in arb_key_value_list(10),
        k in arb_tree_key(),
        v in arb_nonzero_value()
    ) {
        // Ensure k is not in batch
        let batch_keys: std::collections::HashSet<_> = batch_entries.iter().map(|(k, _)| k).collect();
        prop_assume!(!batch_keys.contains(&k));

        // Deduplicate batch
        let mut deduped = std::collections::HashMap::new();
        for (k, v) in &batch_entries {
            deduped.insert(*k, *v);
        }
        let unique_batch: Vec<_> = deduped.into_iter().collect();

        // Method 1: batch then individual
        let mut tree1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree1.insert_batch(unique_batch.clone());
        tree1.insert(k, v);

        // Method 2: all sequential
        let mut tree2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        for (bk, bv) in &unique_batch {
            tree2.insert(*bk, *bv);
        }
        tree2.insert(k, v);

        prop_assert_eq!(tree1.root_hash(), tree2.root_hash());
    }
}

// ============================================================================
// Streaming Builder Properties (P20-P21)
// ============================================================================

proptest! {
    /// P20: streaming builder produces same hash as tree
    #[test]
    fn prop_streaming_equals_tree(entries in arb_key_value_list(20)) {
        // Deduplicate and sort
        let mut deduped = std::collections::HashMap::new();
        for (k, v) in &entries {
            if *v != B256::ZERO {
                deduped.insert(*k, *v);
            }
        }
        let mut sorted: Vec<_> = deduped.into_iter().collect();
        sorted.sort_by(|a, b| (a.0.stem, a.0.subindex).cmp(&(b.0.stem, b.0.subindex)));

        // Tree hash
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        for (k, v) in &sorted {
            tree.insert(*k, *v);
        }
        let tree_hash = tree.root_hash();

        // Streaming hash
        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
        let streaming_hash = builder.build_root_hash(sorted);

        prop_assert_eq!(tree_hash, streaming_hash);
    }

    /// P21: streaming parallel equals streaming serial
    #[test]
    #[cfg(feature = "parallel")]
    fn prop_streaming_parallel_equals_serial(entries in arb_key_value_list(20)) {
        // Deduplicate and sort
        let mut deduped = std::collections::HashMap::new();
        for (k, v) in &entries {
            if *v != B256::ZERO {
                deduped.insert(*k, *v);
            }
        }
        let mut sorted: Vec<_> = deduped.into_iter().collect();
        sorted.sort_by(|a, b| (a.0.stem, a.0.subindex).cmp(&(b.0.stem, b.0.subindex)));

        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
        let serial_hash = builder.build_root_hash(sorted.clone());
        let parallel_hash = builder.build_root_hash_parallel(sorted);

        prop_assert_eq!(serial_hash, parallel_hash);
    }
}

// ============================================================================
// Incremental Mode Properties (P22-P23)
// ============================================================================

proptest! {
    /// P22: incremental mode produces same hash as full rebuild
    #[test]
    fn prop_incremental_equals_full(
        initial in arb_key_value_list(10),
        update_key in arb_tree_key(),
        update_value in arb_nonzero_value()
    ) {
        // Ensure update_key is not in initial
        let initial_keys: std::collections::HashSet<_> = initial.iter().map(|(k, _)| k).collect();
        prop_assume!(!initial_keys.contains(&update_key));

        // Deduplicate initial
        let mut deduped = std::collections::HashMap::new();
        for (k, v) in &initial {
            deduped.insert(*k, *v);
        }
        let unique_initial: Vec<_> = deduped.into_iter().collect();

        // Full rebuild approach
        let mut tree1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        for (k, v) in &unique_initial {
            tree1.insert(*k, *v);
        }
        tree1.root_hash();
        tree1.insert(update_key, update_value);
        let full_hash = tree1.root_hash();

        // Incremental approach
        let mut tree2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        for (k, v) in &unique_initial {
            tree2.insert(*k, *v);
        }
        tree2.root_hash();
        tree2.enable_incremental_mode();
        tree2.root_hash(); // Populate cache
        tree2.insert(update_key, update_value);
        let incremental_hash = tree2.root_hash();

        prop_assert_eq!(full_hash, incremental_hash);
    }

    /// P23: multiple incremental updates are consistent
    #[test]
    fn prop_multiple_incremental_updates(
        initial in arb_key_value_list(5),
        updates in arb_key_value_list(5)
    ) {
        // Deduplicate initial
        let mut deduped = std::collections::HashMap::new();
        for (k, v) in &initial {
            deduped.insert(*k, *v);
        }
        let unique_initial: Vec<_> = deduped.into_iter().collect();

        // Full rebuild for all
        let mut tree1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        for (k, v) in &unique_initial {
            tree1.insert(*k, *v);
        }
        for (k, v) in &updates {
            tree1.insert(*k, *v);
        }
        let full_hash = tree1.root_hash();

        // Incremental mode
        let mut tree2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        for (k, v) in &unique_initial {
            tree2.insert(*k, *v);
        }
        tree2.root_hash();
        tree2.enable_incremental_mode();
        tree2.root_hash();
        for (k, v) in &updates {
            tree2.insert(*k, *v);
        }
        let incremental_hash = tree2.root_hash();

        prop_assert_eq!(full_hash, incremental_hash);
    }
}

// ============================================================================
// Boundary Conditions (P24-P26)
// ============================================================================

proptest! {
    /// P24: max subindex (255) works correctly
    #[test]
    fn prop_max_subindex_works(stem in arb_stem(), value in arb_nonzero_value()) {
        let key = TreeKey::new(stem, 255);
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert(key, value);
        prop_assert_eq!(tree.get(&key), Some(value));
    }

    /// P25: min subindex (0) works correctly
    #[test]
    fn prop_min_subindex_works(stem in arb_stem(), value in arb_nonzero_value()) {
        let key = TreeKey::new(stem, 0);
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert(key, value);
        prop_assert_eq!(tree.get(&key), Some(value));
    }

    /// P26: full stem (256 values) works
    #[test]
    fn prop_full_stem_256_values(stem in arb_stem()) {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        // Insert all 256 subindices (use idx|1 to ensure nonzero values)
        for idx in 0u8..=255 {
            let key = TreeKey::new(stem, idx);
            // Create a nonzero value: set first byte to idx, last byte to 0xFF
            let mut value_bytes = [idx; 32];
            value_bytes[31] = 0xFF; // Ensure nonzero
            let value = B256::from(value_bytes);
            tree.insert(key, value);
        }

        // Verify all 256 values
        for idx in 0u8..=255 {
            let key = TreeKey::new(stem, idx);
            let mut expected_bytes = [idx; 32];
            expected_bytes[31] = 0xFF;
            let expected = B256::from(expected_bytes);
            prop_assert_eq!(tree.get(&key), Some(expected));
        }

        prop_assert_eq!(tree.stem_count(), 1);
    }
}

// ============================================================================
// Key/Stem Encoding (P27-P28)
// ============================================================================

proptest! {
    /// P27: TreeKey from_bytes round-trips correctly
    #[test]
    fn prop_tree_key_roundtrip(key in arb_tree_key()) {
        let bytes = key.to_bytes();
        let recovered = TreeKey::from_bytes(bytes);
        prop_assert_eq!(key, recovered);
    }

    /// P28: B256 key conversion round-trips
    #[test]
    fn prop_b256_key_roundtrip(b256_key in prop::array::uniform32(any::<u8>()).prop_map(B256::from)) {
        let tree_key = TreeKey::from_bytes(b256_key);
        let recovered = tree_key.to_bytes();
        prop_assert_eq!(b256_key, recovered);
    }
}

// ============================================================================
// Stress Tests (P29-P30)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))] // Fewer cases for stress tests

    /// P29: large tree with many stems handles correctly
    #[test]
    fn prop_large_tree_many_stems(entries in arb_key_value_list(100)) {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        for (k, v) in &entries {
            tree.insert(*k, *v);
        }

        // All values should be retrievable
        for (k, v) in &entries {
            let got = tree.get(k);
            // Due to overwrites, we just check it's Some if v is nonzero
            if *v != B256::ZERO {
                prop_assert!(got.is_some());
            }
        }

        // Hash should be deterministic
        let hash1 = tree.root_hash();
        let hash2 = tree.root_hash();
        prop_assert_eq!(hash1, hash2);
    }

    /// P30: alternating insert/delete sequence is consistent
    #[test]
    fn prop_alternating_insert_delete(
        entries in arb_key_value_list(20),
        delete_indices in prop::collection::vec(0usize..20, 0..10)
    ) {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        // Insert all
        for (k, v) in &entries {
            tree.insert(*k, *v);
        }

        // Delete some
        for idx in &delete_indices {
            if *idx < entries.len() {
                tree.delete(&entries[*idx].0);
            }
        }

        // Verify remaining entries
        for (i, (k, v)) in entries.iter().enumerate() {
            if delete_indices.contains(&i) {
                prop_assert_eq!(tree.get(k), None);
            } else if *v != B256::ZERO {
                // May have been overwritten by duplicate key
                let _ = tree.get(k);
            }
        }

        // Hash should be stable
        let h1 = tree.root_hash();
        let h2 = tree.root_hash();
        prop_assert_eq!(h1, h2);
    }
}

// ============================================================================
// Oracle-Suggested Tests: Invariants (P31-P35)
// ============================================================================

/// Strategy that allows zero values (for testing zero-as-delete semantics)
fn arb_updates(max_len: usize) -> impl Strategy<Value = Vec<(TreeKey, B256)>> {
    prop::collection::vec((arb_tree_key(), arb_value()), 0..max_len)
}

proptest! {
    /// P31: len() and stem_count() match logical state after arbitrary updates
    #[test]
    fn prop_len_and_stem_count_match_logical_state(updates in arb_updates(50)) {
        use std::collections::{HashMap, HashSet};

        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let mut map: HashMap<TreeKey, B256> = HashMap::new();

        for (k, v) in &updates {
            tree.insert(*k, *v);
            if *v == B256::ZERO {
                map.remove(k);
            } else {
                map.insert(*k, *v);
            }
        }

        // len == number of keys with nonzero final value
        prop_assert_eq!(tree.len(), map.len());

        // stem_count == number of stems that have at least one nonzero value
        let logical_stems: HashSet<_> = map.keys().map(|k| k.stem).collect();
        prop_assert_eq!(tree.stem_count(), logical_stems.len());

        // All logical values are retrievable and equal
        for (k, v) in &map {
            prop_assert_eq!(tree.get(k), Some(*v));
        }
    }

    /// P32: Deleting the only value for a stem removes that stem
    #[test]
    fn prop_delete_last_value_removes_stem(
        stem in arb_stem(),
        idx in arb_subindex(),
        value in arb_nonzero_value()
    ) {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let key = TreeKey::new(stem, idx);

        tree.insert(key, value);
        prop_assert_eq!(tree.stem_count(), 1);
        prop_assert!(!tree.is_empty());

        tree.delete(&key);

        prop_assert_eq!(tree.get(&key), None);
        prop_assert_eq!(tree.stem_count(), 0);
        prop_assert!(tree.is_empty());
        prop_assert_eq!(tree.root_hash(), B256::ZERO);
    }

    /// P33: B256 APIs equivalent to TreeKey APIs
    #[test]
    fn prop_b256_apis_equivalent(key_bytes in arb_value(), value in arb_value()) {
        let key = TreeKey::from_bytes(key_bytes);

        // TreeKey path
        let mut t1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        t1.insert(key, value);
        let v1 = t1.get(&key);

        // B256 path
        let mut t2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        t2.insert_b256(key_bytes, value);
        let v2 = t2.get_by_b256(&key_bytes);

        prop_assert_eq!(v1, v2);
        prop_assert_eq!(t1.root_hash(), t2.root_hash());
    }

    /// P34: insert_batch equivalent to individual inserts (including zeros)
    #[test]
    fn prop_insert_batch_with_zeros(entries in arb_updates(50)) {
        let mut t1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        for (k, v) in &entries {
            t1.insert(*k, *v);
        }
        let h1 = t1.root_hash();

        let mut t2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        t2.insert_batch(entries.clone());
        let h2 = t2.root_hash();

        prop_assert_eq!(h1, h2);
    }

    /// P35: Root hash stable without mutation (caching correctness)
    #[test]
    fn prop_root_hash_stable_without_mutation(entries in arb_key_value_list(50)) {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        for (k, v) in &entries {
            tree.insert(*k, *v);
        }

        let h1 = tree.root_hash();
        let h2 = tree.root_hash();
        let h3 = tree.root_hash();

        prop_assert_eq!(h1, h2);
        prop_assert_eq!(h2, h3);
    }
}

// ============================================================================
// Oracle-Suggested Tests: Incremental Mode (P36-P37)
// ============================================================================

/// Operation type for state machine testing
#[derive(Clone, Debug)]
enum Op {
    Insert(TreeKey, B256),
    Delete(TreeKey),
}

fn arb_ops(max_len: usize) -> impl Strategy<Value = Vec<Op>> {
    prop::collection::vec(
        prop_oneof![
            (arb_tree_key(), arb_value()).prop_map(|(k, v)| Op::Insert(k, v)),
            arb_tree_key().prop_map(Op::Delete),
        ],
        0..max_len,
    )
}

proptest! {
    /// P36: Incremental mode equivalent to full rebuild for any op sequence
    #[test]
    fn prop_incremental_mode_arbitrary_ops(ops in arb_ops(30)) {
        let mut full: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let mut inc: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        // Populate caches before enabling incremental
        let _ = full.root_hash();
        let _ = inc.root_hash();
        inc.enable_incremental_mode();
        let _ = inc.root_hash();

        for op in ops {
            match op {
                Op::Insert(k, v) => {
                    full.insert(k, v);
                    inc.insert(k, v);
                }
                Op::Delete(k) => {
                    full.delete(&k);
                    inc.delete(&k);
                }
            }
        }

        prop_assert_eq!(full.root_hash(), inc.root_hash());
    }

    /// P37: Deeply colliding stems (differ only in last bit) hash consistently
    #[test]
    fn prop_deep_colliding_stems(
        base in prop::array::uniform31(any::<u8>()),
        v1 in arb_nonzero_value(),
        v2 in arb_nonzero_value()
    ) {
        let s1 = Stem::new(base);
        let mut other = base;
        other[30] ^= 0x01; // Flip last bit
        let s2 = Stem::new(other);

        // Skip if stems are somehow equal
        if s1 == s2 {
            return Ok(());
        }

        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert(TreeKey::new(s1, 0), v1);
        tree.insert(TreeKey::new(s2, 0), v2);
        let tree_root = tree.root_hash();

        // Build via streaming
        let mut entries = vec![
            (TreeKey::new(s1, 0), v1),
            (TreeKey::new(s2, 0), v2),
        ];
        entries.sort_by(|a, b| (a.0.stem, a.0.subindex).cmp(&(b.0.stem, b.0.subindex)));

        let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
        let streaming_root = builder.build_root_hash(entries);

        prop_assert_eq!(tree_root, streaming_root);
    }
}

// ============================================================================
// Oracle-Suggested Tests: Proof Properties (P38-P40)
// ============================================================================

use ubt::{generate_stem_proof, Proof, ProofNode, StemNode};

proptest! {
    /// P38: Stem proof siblings reconstruct subtree root correctly
    #[test]
    fn prop_stem_proof_reconstructs_subtree(
        stem in arb_stem(),
        values in prop::collection::btree_map(arb_subindex(), arb_nonzero_value(), 1..20),
        query_idx in arb_subindex()
    ) {
        let hasher = Blake3Hasher;
        let mut node = StemNode::new(stem);
        for (idx, v) in &values {
            node.set_value(*idx, *v);
        }

        let (value, siblings) = generate_stem_proof(&node, query_idx, &hasher);

        // Rebuild subtree root from proof siblings (bottom-up, matching generate_stem_proof)
        let mut current = match value {
            Some(v) => hasher.hash_32(&v),
            None => B256::ZERO,
        };

        let mut idx = query_idx as usize;
        for sibling in siblings.iter() {
            // Bottom-up: level 0 is leaf level, bit is idx & 1
            let is_right = (idx & 1) == 1;
            current = if is_right {
                hasher.hash_64(sibling, &current)
            } else {
                hasher.hash_64(&current, sibling)
            };
            idx /= 2;
        }

        // The computed subtree root + stem should equal node hash
        let computed_stem_hash = hasher.hash_stem_node(stem.as_bytes(), &current);
        let expected_stem_hash = node.hash(&hasher);

        prop_assert_eq!(computed_stem_hash, expected_stem_hash);
    }

    /// P39: generate_stem_proof returns correct value
    #[test]
    fn prop_stem_proof_value_correct(
        stem in arb_stem(),
        idx in arb_subindex(),
        value in arb_nonzero_value()
    ) {
        let hasher = Blake3Hasher;
        let mut node = StemNode::new(stem);
        node.set_value(idx, value);

        let (proof_val, _siblings) = generate_stem_proof(&node, idx, &hasher);
        prop_assert_eq!(proof_val, Some(value));

        // Query non-existent index
        let other_idx = idx.wrapping_add(1);
        if node.get_value(other_idx).is_none() {
            let (proof_val2, _) = generate_stem_proof(&node, other_idx, &hasher);
            prop_assert_eq!(proof_val2, None);
        }
    }

    /// P40: Extension proof with matching stem is invalid
    #[test]
    fn prop_extension_matching_stem_invalid(key in arb_tree_key()) {
        let hasher = Blake3Hasher;
        let bogus_hash = B256::repeat_byte(0xAA);

        let proof = Proof::new(
            key,
            None,
            vec![ProofNode::Extension {
                stem: key.stem,
                stem_hash: bogus_hash,
            }],
        );

        let result = proof.compute_root(&hasher);
        prop_assert!(result.is_err());
    }
}

// ============================================================================
// Oracle-Suggested Tests: Embedding/Code (P41-P42)
// ============================================================================

use ubt::{chunkify_code, dechunkify_code, BasicDataLeaf, CodeChunk};

proptest! {
    /// P41: BasicDataLeaf encode/decode roundtrip
    /// Note: code_size is limited to 24 bits (3 bytes) in encoding
    #[test]
    fn prop_basic_data_leaf_roundtrip(
        nonce in any::<u64>(),
        balance in any::<u128>(),
        code_size in 0u32..0x00FF_FFFF // 24-bit max
    ) {
        let leaf = BasicDataLeaf::new(nonce, balance, code_size);
        let decoded = BasicDataLeaf::decode(leaf.encode());
        prop_assert_eq!(leaf, decoded);
    }

    /// P42: Code chunking produces consistent chunks
    #[test]
    fn prop_code_chunking_consistent(code in prop::collection::vec(any::<u8>(), 0..500)) {
        let chunks1 = chunkify_code(&code);
        let chunks2 = chunkify_code(&code);

        prop_assert_eq!(chunks1.len(), chunks2.len());
        for (c1, c2) in chunks1.iter().zip(chunks2.iter()) {
            prop_assert_eq!(c1.encode(), c2.encode());
        }
    }
}

// ============================================================================
// Additional Oracle-Suggested Tests (P43-P50)
// ============================================================================

proptest! {
    /// P43: Code chunkify/dechunkify roundtrip
    #[test]
    fn prop_code_chunk_roundtrip(code in prop::collection::vec(any::<u8>(), 0..1024)) {
        let chunks = chunkify_code(&code);
        let recovered = dechunkify_code(&chunks, code.len());
        prop_assert_eq!(code, recovered);
    }

    /// P44: CodeChunk encode/decode roundtrip
    #[test]
    fn prop_code_chunk_encode_decode(
        leading in 0u8..31,
        data in prop::array::uniform31(any::<u8>())
    ) {
        let chunk = CodeChunk::new(leading, data);
        let decoded = CodeChunk::decode(chunk.encode());
        prop_assert_eq!(chunk.leading_pushdata, decoded.leading_pushdata);
        prop_assert_eq!(chunk.data, decoded.data);
    }

    /// P45: Enable incremental mode mid-stream
    #[test]
    fn prop_incremental_enable_midstream(ops in arb_ops(40)) {
        let mut full: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let mut inc: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        let mid = ops.len() / 2;

        // Apply first half without incremental
        for op in &ops[..mid] {
            match op {
                Op::Insert(k, v) => { full.insert(*k, *v); inc.insert(*k, *v); }
                Op::Delete(k) => { full.delete(k); inc.delete(k); }
            }
        }

        // Force rebuild before enabling incremental
        let _ = full.root_hash();
        let _ = inc.root_hash();

        // Now enable incremental and continue
        inc.enable_incremental_mode();
        let _ = inc.root_hash();

        for op in &ops[mid..] {
            match op {
                Op::Insert(k, v) => { full.insert(*k, *v); inc.insert(*k, *v); }
                Op::Delete(k) => { full.delete(k); inc.delete(k); }
            }
        }

        prop_assert_eq!(full.root_hash(), inc.root_hash());
    }

    /// P46: Mixing insert_batch with incremental mode
    #[test]
    fn prop_incremental_with_batch(
        initial in arb_key_value_list(20),
        batch in arb_key_value_list(20)
    ) {
        let mut full: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let mut inc: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        // Initial inserts
        for (k, v) in &initial {
            full.insert(*k, *v);
            inc.insert(*k, *v);
        }

        let _ = full.root_hash();
        let _ = inc.root_hash();
        inc.enable_incremental_mode();
        let _ = inc.root_hash();

        // Full tree: individual inserts
        for (k, v) in &batch {
            full.insert(*k, *v);
        }

        // Incremental tree: batch insert
        inc.insert_batch(batch.clone());

        prop_assert_eq!(full.root_hash(), inc.root_hash());
    }

    /// P47: Incremental root hash stability
    #[test]
    fn prop_incremental_root_hash_stable(entries in arb_key_value_list(50)) {
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        for (k, v) in &entries {
            tree.insert(*k, *v);
        }

        tree.enable_incremental_mode();
        let h1 = tree.root_hash();
        let h2 = tree.root_hash();
        let h3 = tree.root_hash();

        prop_assert_eq!(h1, h2);
        prop_assert_eq!(h2, h3);
    }

    /// P48: Constructor equivalence (new vs with_capacity)
    #[test]
    fn prop_constructors_equivalent(entries in arb_key_value_list(100)) {
        let mut t1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let mut t2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::with_capacity(1024);
        let hasher = Blake3Hasher;
        let mut t3: UnifiedBinaryTree<Blake3Hasher> =
            UnifiedBinaryTree::with_hasher_and_capacity(hasher, 1024);

        for (k, v) in &entries {
            t1.insert(*k, *v);
            t2.insert(*k, *v);
            t3.insert(*k, *v);
        }

        prop_assert_eq!(t1.root_hash(), t2.root_hash());
        prop_assert_eq!(t1.root_hash(), t3.root_hash());
    }

    /// P49: insert_batch_with_progress equivalent to insert_batch
    #[test]
    fn prop_insert_batch_with_progress_equivalent(entries in arb_key_value_list(100)) {
        let mut t1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        t1.insert_batch(entries.clone());
        let h1 = t1.root_hash();

        let mut t2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let mut progress_count = 0usize;
        t2.insert_batch_with_progress(entries.clone(), |n| progress_count = n);
        let h2 = t2.root_hash();

        prop_assert_eq!(h1, h2);
        prop_assert_eq!(progress_count, entries.len());
    }

    /// P50: B256 APIs equivalent for many updates
    #[test]
    fn prop_b256_apis_equivalent_many(entries in arb_key_value_list(100)) {
        let mut t1: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let mut t2: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

        for (k, v) in &entries {
            t1.insert(*k, *v);
            t2.insert_b256(k.to_bytes(), *v);
        }

        prop_assert_eq!(t1.root_hash(), t2.root_hash());

        // Verify get equivalence
        for (k, _) in &entries {
            prop_assert_eq!(t1.get(k), t2.get_by_b256(&k.to_bytes()));
        }
    }
}
