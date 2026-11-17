//! Go-ethereum compatibility tests using their test vectors.
//!
//! These tests use `Sha256Hasher` and assert that root hashes are equal to the
//! roots that go-ethereum's bintrie produces for the same entries.

#[cfg(test)]
mod tests {
    use crate::{Sha256Hasher, Stem, TreeKey, UnifiedBinaryTree, B256};

    fn hex_to_b256(s: &str) -> B256 {
        let s = s.strip_prefix("0x").unwrap_or(s);
        let bytes = hex::decode(s).expect("valid hex");
        B256::from_slice(&bytes)
    }

    // Test vectors from go-ethereum trie/bintrie/trie_test.go
    const ZERO_KEY: B256 = B256::ZERO;

    fn one_key() -> B256 {
        hex_to_b256("0101010101010101010101010101010101010101010101010101010101010101")
    }

    fn two_key() -> B256 {
        hex_to_b256("0202020202020202020202020202020202020202020202020202020202020202")
    }

    /// `TestSingleEntry` from go-ethereum
    /// Expected root: aab1060e04cb4f5dc6f697ae93156a95714debbf77d54238766adc5709282b6f
    #[test]
    fn test_single_entry_sha256() {
        let mut tree: UnifiedBinaryTree<Sha256Hasher> = UnifiedBinaryTree::new();

        // Insert key=0x00...00, value=0x0101...01
        tree.insert_b256(ZERO_KEY, one_key());

        let root = tree.root_hash().unwrap();
        let expected =
            hex_to_b256("aab1060e04cb4f5dc6f697ae93156a95714debbf77d54238766adc5709282b6f");

        // Verify tree has the value
        assert_eq!(tree.get_by_b256(&ZERO_KEY), Some(one_key()));

        // Root must match go-ethereum exactly
        assert_eq!(root, expected, "single entry root must match go-ethereum");
    }

    /// `TestTwoEntriesDiffFirstBit` from go-ethereum
    /// Expected root: dfc69c94013a8b3c65395625a719a87534a7cfd38719251ad8c8ea7fe79f065e
    #[test]
    fn test_two_entries_diff_first_bit_sha256() {
        let mut tree: UnifiedBinaryTree<Sha256Hasher> = UnifiedBinaryTree::new();

        // Insert two entries differing in first bit
        tree.insert_b256(ZERO_KEY, one_key());

        let key2 = hex_to_b256("8000000000000000000000000000000000000000000000000000000000000000");
        tree.insert_b256(key2, two_key());

        let root = tree.root_hash().unwrap();
        let expected =
            hex_to_b256("dfc69c94013a8b3c65395625a719a87534a7cfd38719251ad8c8ea7fe79f065e");

        assert_eq!(tree.len(), 2);
        assert_eq!(root, expected, "two entries root must match go-ethereum");
        assert_eq!(tree.get_by_b256(&ZERO_KEY), Some(one_key()));
        assert_eq!(tree.get_by_b256(&key2), Some(two_key()));
    }

    /// Test stem node hashing matches go-ethereum
    #[test]
    fn test_stem_node_hash_single_value() {
        use crate::{Sha256Hasher, StemNode};

        let hasher = Sha256Hasher;
        let stem = Stem::new([0u8; 31]);
        let mut node = StemNode::new(stem);

        // Insert value at subindex 0
        node.set_value(0, one_key());

        let hash = node.hash(&hasher);
        println!("Stem node hash (single value at idx 0): {hash}");

        // The hash should be:
        // 1. hash(value) for leaf
        // 2. Build 8-level tree
        // 3. hash(stem || 0x00 || subtree_root)

        // Verify it's non-zero and deterministic
        assert_ne!(hash, B256::ZERO);
        assert_eq!(hash, node.hash(&hasher));
    }

    /// Test colocated values (same stem, different subindex)
    #[test]
    fn test_colocated_values_sha256() {
        let mut tree: UnifiedBinaryTree<Sha256Hasher> = UnifiedBinaryTree::new();

        // Keys with same stem (first 31 bytes) but different subindex
        let key1 = hex_to_b256("0000000000000000000000000000000000000000000000000000000000000003");
        let key2 = hex_to_b256("0000000000000000000000000000000000000000000000000000000000000004");

        tree.insert_b256(key1, one_key());
        tree.insert_b256(key2, two_key());

        // Both should be in same stem
        let tk1 = TreeKey::from_bytes(key1);
        let tk2 = TreeKey::from_bytes(key2);
        assert_eq!(tk1.stem, tk2.stem);

        // Tree should have 2 values but only 1 stem
        assert_eq!(tree.len(), 2);

        let root = tree.root_hash().unwrap();
        println!("Colocated values root: {root}");
        assert_ne!(root, B256::ZERO);
    }

    /// Regression test for #70: one-sided subtrees must `hash_64` against zero,
    /// not short-circuit by returning the non-empty child's hash directly.
    /// Two stems that both start with bit 0 produce a one-sided tree at depth 0.
    /// Expected root from go-ethereum: eb3937998684b2dbf1f87c9b48ff3dd0282ca3073d3f87611e06586b88297c91
    #[test]
    fn test_one_sided_subtree_hashes_against_zero() {
        let mut tree: UnifiedBinaryTree<Sha256Hasher> = UnifiedBinaryTree::new();

        // Both keys start with bit 0 → both go left at depth 0, right subtree is empty
        let key1 = hex_to_b256("0000000000000000000000000000000000000000000000000000000000000001");
        let key2 = hex_to_b256("0100000000000000000000000000000000000000000000000000000000000001");

        tree.insert_b256(
            key1,
            hex_to_b256("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"),
        );
        tree.insert_b256(
            key2,
            hex_to_b256("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"),
        );

        let root = tree.root_hash().unwrap();
        let expected =
            hex_to_b256("eb3937998684b2dbf1f87c9b48ff3dd0282ca3073d3f87611e06586b88297c91");
        assert_eq!(
            root, expected,
            "one-sided subtree root must match go-ethereum (issue #70)"
        );
    }

    /// Same test via `StreamingTreeBuilder` for #70 coverage.
    #[test]
    fn test_one_sided_subtree_streaming() {
        use crate::{StreamingTreeBuilder, TreeKey};

        let builder = StreamingTreeBuilder::<Sha256Hasher>::new();

        let key1 = hex_to_b256("0000000000000000000000000000000000000000000000000000000000000001");
        let key2 = hex_to_b256("0100000000000000000000000000000000000000000000000000000000000001");
        let val1 = hex_to_b256("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
        let val2 = hex_to_b256("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");

        let entries = vec![
            (TreeKey::from_bytes(key1), val1),
            (TreeKey::from_bytes(key2), val2),
        ];
        let root = builder.build_root_hash(entries).unwrap();
        let expected =
            hex_to_b256("eb3937998684b2dbf1f87c9b48ff3dd0282ca3073d3f87611e06586b88297c91");
        assert_eq!(
            root, expected,
            "streaming one-sided subtree root must match go-ethereum (issue #70)"
        );
    }

    fn k80() -> B256 {
        hex_to_b256("8000000000000000000000000000000000000000000000000000000000000000")
    }

    fn k03() -> B256 {
        hex_to_b256("0000000000000000000000000000000000000000000000000000000000000003")
    }

    fn k04() -> B256 {
        hex_to_b256("0000000000000000000000000000000000000000000000000000000000000004")
    }

    /// Entries of go-ethereum `TestMerkleizeMultipleEntries`: the value for key
    /// number `i` is `i` as a little-endian `u64`, so the first value is all zero.
    fn merkleize_entries() -> Vec<(B256, B256)> {
        let keys: [B256; 4] = [
            ZERO_KEY,
            k80(),
            hex_to_b256("0100000000000000000000000000000000000000000000000000000000000000"),
            hex_to_b256("8100000000000000000000000000000000000000000000000000000000000000"),
        ];
        keys.iter()
            .zip(0u64..)
            .map(|(key, i)| {
                let mut value = [0u8; 32];
                value[..8].copy_from_slice(&i.to_le_bytes());
                (*key, B256::from(value))
            })
            .collect()
    }

    fn tree_root(entries: &[(B256, B256)]) -> B256 {
        let mut tree: UnifiedBinaryTree<Sha256Hasher> = UnifiedBinaryTree::new();
        for (key, value) in entries {
            tree.insert_b256(*key, *value);
        }
        tree.root_hash().unwrap()
    }

    /// A single leaf that holds 32 zero bytes is present and is hashed.
    /// Root from the go-ethereum `trie/bintrie` code at commit `b0f9324c`.
    #[test]
    fn test_zero_value_only_sha256() {
        let root: B256 = tree_root(&[(ZERO_KEY, B256::ZERO)]);
        assert_eq!(
            root,
            hex_to_b256("d90841cd9ac38b304a3ba8bf706cb89b26aba153c72b73663fafb5445db8d39c"),
            "zero_value_only root must match go-ethereum"
        );
    }

    /// A zero value beside a non-zero value in the same stem.
    /// Root from the go-ethereum `trie/bintrie` code at commit `b0f9324c`.
    #[test]
    fn test_zero_value_beside_value_sha256() {
        let root: B256 = tree_root(&[(k03(), one_key()), (k04(), B256::ZERO)]);
        assert_eq!(
            root,
            hex_to_b256("921070b0df7aaa65f5fe8a2d4470e60aafce0bc60dbb75fc63a842012ee4e43b"),
            "zero_value_beside_value root must match go-ethereum"
        );
    }

    /// A zero write over a value keeps the leaf and the stem.
    /// Root from the go-ethereum `trie/bintrie` code at commit `b0f9324c`.
    #[test]
    fn test_write_then_zero_sha256() {
        let root: B256 = tree_root(&[
            (ZERO_KEY, one_key()),
            (k80(), two_key()),
            (k80(), B256::ZERO),
        ]);
        assert_eq!(
            root,
            hex_to_b256("99e98bcbc2472cb109aa6b706c25a5bdf1b703c4b1cf2c7c21b4dc35a6ca67d9"),
            "write_then_zero root must match go-ethereum"
        );
    }

    /// `TestMerkleizeMultipleEntries` from go-ethereum, with its inputs and its pinned root.
    #[test]
    fn test_merkleize_multiple_entries_sha256() {
        let root: B256 = tree_root(&merkleize_entries());
        assert_eq!(
            root,
            hex_to_b256("9317155862f7a3867660ddd0966ff799a3d16aa4df1e70a7516eaa4a675191b5"),
            "merkleize root must match go-ethereum"
        );
    }

    /// Assert the root that `StreamingTreeBuilder` gives for `writes`: entries sorted
    /// by key, and only the last write of a repeated key.
    fn assert_streaming_root(name: &str, writes: &[(B256, B256)], expected: &str) {
        use crate::StreamingTreeBuilder;
        use std::collections::BTreeMap;

        let last_writes: BTreeMap<B256, B256> = writes.iter().copied().collect();
        let entries: Vec<(TreeKey, B256)> = last_writes
            .into_iter()
            .map(|(key, value)| (TreeKey::from_bytes(key), value))
            .collect();

        let builder = StreamingTreeBuilder::<Sha256Hasher>::new();
        assert_eq!(
            builder.build_root_hash(entries.clone()).unwrap(),
            hex_to_b256(expected),
            "streaming {name} root must match go-ethereum"
        );
        #[cfg(feature = "parallel")]
        assert_eq!(
            builder.build_root_hash_parallel(entries).unwrap(),
            hex_to_b256(expected),
            "parallel streaming {name} root must match go-ethereum"
        );
    }

    /// The four zero-value scenarios through `StreamingTreeBuilder`. The roots are
    /// the go-ethereum roots of the tree tests above.
    #[test]
    fn test_zero_value_roots_streaming() {
        assert_streaming_root(
            "zero_value_only",
            &[(ZERO_KEY, B256::ZERO)],
            "d90841cd9ac38b304a3ba8bf706cb89b26aba153c72b73663fafb5445db8d39c",
        );
        assert_streaming_root(
            "zero_value_beside_value",
            &[(k03(), one_key()), (k04(), B256::ZERO)],
            "921070b0df7aaa65f5fe8a2d4470e60aafce0bc60dbb75fc63a842012ee4e43b",
        );
        assert_streaming_root(
            "write_then_zero",
            &[
                (ZERO_KEY, one_key()),
                (k80(), two_key()),
                (k80(), B256::ZERO),
            ],
            "99e98bcbc2472cb109aa6b706c25a5bdf1b703c4b1cf2c7c21b4dc35a6ca67d9",
        );
        assert_streaming_root(
            "merkleize",
            &merkleize_entries(),
            "9317155862f7a3867660ddd0966ff799a3d16aa4df1e70a7516eaa4a675191b5",
        );
    }

    /// The zero-value roots do not depend on the incremental mode: a zero write
    /// after the node cache is populated gives the go-ethereum root too.
    #[test]
    fn test_write_then_zero_incremental_sha256() {
        let mut tree: UnifiedBinaryTree<Sha256Hasher> = UnifiedBinaryTree::new();
        tree.insert_b256(ZERO_KEY, one_key());
        tree.insert_b256(k80(), two_key());
        tree.enable_incremental_mode();
        assert_eq!(
            tree.root_hash().unwrap(),
            hex_to_b256("dfc69c94013a8b3c65395625a719a87534a7cfd38719251ad8c8ea7fe79f065e")
        );

        tree.insert_b256(k80(), B256::ZERO);
        assert_eq!(
            tree.root_hash().unwrap(),
            hex_to_b256("99e98bcbc2472cb109aa6b706c25a5bdf1b703c4b1cf2c7c21b4dc35a6ca67d9")
        );
        assert_eq!(tree.get_by_b256(&k80()), Some(B256::ZERO));
        assert_eq!(tree.len(), 2);
        assert_eq!(tree.stem_count(), 2);
    }

    /// `delete` has no go-ethereum counterpart. After the writes of the
    /// `write_then_zero` scenario, `delete` of the zeroed key removes the leaf and its
    /// stem, and the root is the root of a tree that never saw that key.
    #[test]
    fn test_delete_after_zero_write_restores_never_written_root() {
        let mut never_written: UnifiedBinaryTree<Sha256Hasher> = UnifiedBinaryTree::new();
        never_written.insert_b256(ZERO_KEY, one_key());
        let expected: B256 = never_written.root_hash().unwrap();
        assert_eq!(
            expected,
            hex_to_b256("aab1060e04cb4f5dc6f697ae93156a95714debbf77d54238766adc5709282b6f")
        );

        for incremental in [false, true] {
            let mut tree: UnifiedBinaryTree<Sha256Hasher> = UnifiedBinaryTree::new();
            if incremental {
                tree.enable_incremental_mode();
            }
            tree.insert_b256(ZERO_KEY, one_key());
            tree.insert_b256(k80(), two_key());
            tree.insert_b256(k80(), B256::ZERO);
            assert_eq!(
                tree.root_hash().unwrap(),
                hex_to_b256("99e98bcbc2472cb109aa6b706c25a5bdf1b703c4b1cf2c7c21b4dc35a6ca67d9")
            );

            tree.delete(&TreeKey::from_bytes(k80()));

            assert_eq!(tree.get_by_b256(&k80()), None);
            assert_eq!(tree.len(), 1);
            assert_eq!(tree.stem_count(), 1);
            assert_eq!(
                tree.root_hash().unwrap(),
                expected,
                "incremental={incremental}"
            );
        }
    }

    /// A stem node that `get_or_create_stem` created, and that holds no value,
    /// contributes nothing to the root. go-ethereum cannot have such a node.
    #[test]
    fn test_get_or_create_stem_without_write_keeps_root() {
        let mut ghost_stem_bytes = [0u8; 31];
        ghost_stem_bytes[0] = 0x40;
        let ghost_stem = Stem::new(ghost_stem_bytes);

        for incremental in [false, true] {
            let mut only_ghost: UnifiedBinaryTree<Sha256Hasher> = UnifiedBinaryTree::new();
            if incremental {
                only_ghost.enable_incremental_mode();
            }
            let _ = only_ghost.get_or_create_stem(ghost_stem);
            assert_eq!(only_ghost.root_hash().unwrap(), B256::ZERO);

            let mut tree: UnifiedBinaryTree<Sha256Hasher> = UnifiedBinaryTree::new();
            if incremental {
                tree.enable_incremental_mode();
            }
            tree.insert_b256(ZERO_KEY, one_key());
            tree.insert_b256(k80(), two_key());
            let expected =
                hex_to_b256("dfc69c94013a8b3c65395625a719a87534a7cfd38719251ad8c8ea7fe79f065e");
            assert_eq!(tree.root_hash().unwrap(), expected);

            let _ = tree.get_or_create_stem(ghost_stem);
            assert_eq!(
                tree.root_hash().unwrap(),
                expected,
                "incremental={incremental}"
            );

            tree.get_or_create_stem(ghost_stem).set_value(0, B256::ZERO);
            let with_zero_leaf: B256 = tree.root_hash().unwrap();
            assert_ne!(with_zero_leaf, expected);

            tree.get_or_create_stem(ghost_stem).remove_value(0);
            assert_eq!(
                tree.root_hash().unwrap(),
                expected,
                "incremental={incremental}"
            );
        }
    }

    /// Test hash determinism with SHA256
    #[test]
    fn test_hash_determinism_sha256() {
        let mut tree1: UnifiedBinaryTree<Sha256Hasher> = UnifiedBinaryTree::new();
        let mut tree2: UnifiedBinaryTree<Sha256Hasher> = UnifiedBinaryTree::new();

        let key1 = hex_to_b256("0000000000000000000000000000000000000000000000000000000000000001");
        let key2 = hex_to_b256("8000000000000000000000000000000000000000000000000000000000000001");

        // Insert in different order
        tree1.insert_b256(key1, one_key());
        tree1.insert_b256(key2, two_key());

        tree2.insert_b256(key2, two_key());
        tree2.insert_b256(key1, one_key());

        assert_eq!(tree1.root_hash().unwrap(), tree2.root_hash().unwrap());
    }

    /// Test internal node hash
    #[test]
    fn test_internal_node_hash_sha256() {
        use crate::{Hasher, InternalNode, Node, Sha256Hasher, StemNode};

        let hasher = Sha256Hasher;

        // Create two stem nodes
        let mut stem1 = StemNode::new(Stem::new([0u8; 31]));
        stem1.set_value(0, one_key());

        let mut bytes2 = [0u8; 31];
        bytes2[0] = 0x80; // Different first bit
        let mut stem2 = StemNode::new(Stem::new(bytes2));
        stem2.set_value(0, two_key());

        // Create internal node
        let internal = InternalNode::new(Node::Stem(stem1.clone()), Node::Stem(stem2.clone()));

        let left_hash = stem1.hash(&hasher);
        let right_hash = stem2.hash(&hasher);
        let internal_hash = internal.hash(&hasher);

        // Internal hash should be hash(left || right)
        let expected = hasher.hash_64(&left_hash, &right_hash);
        assert_eq!(internal_hash, expected);

        println!("Left stem hash:  {left_hash}");
        println!("Right stem hash: {right_hash}");
        println!("Internal hash:   {internal_hash}");
    }
}
