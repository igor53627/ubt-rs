//! Main tree implementation.

use alloy_primitives::B256;
use std::collections::HashMap;

use crate::{
    Hasher, Blake3Hasher, Node, InternalNode, StemNode, Stem, TreeKey,
};

/// The Unified Binary Tree.
///
/// A binary tree that stores 32-byte values at 32-byte keys.
/// Keys are split into a 31-byte stem (tree path) and 1-byte subindex (within subtree).
#[derive(Clone, Debug)]
pub struct UnifiedBinaryTree<H: Hasher = Blake3Hasher> {
    /// Root node of the tree
    root: Node,
    /// Hasher instance
    hasher: H,
    /// Cached stem nodes for efficient access
    stems: HashMap<Stem, StemNode>,
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
        }
    }

    /// Create a new tree with a custom hasher.
    pub fn with_hasher(hasher: H) -> Self {
        Self {
            root: Node::Empty,
            hasher,
            stems: HashMap::new(),
        }
    }

    /// Get the root hash of the tree.
    pub fn root_hash(&self) -> B256 {
        self.root.hash(&self.hasher)
    }

    /// Check if the tree is empty.
    pub fn is_empty(&self) -> bool {
        self.stems.is_empty()
    }

    /// Get a value by its full 32-byte key.
    pub fn get(&self, key: &TreeKey) -> Option<B256> {
        self.stems.get(&key.stem).and_then(|stem_node| {
            stem_node.get_value(key.subindex)
        })
    }

    /// Get a value by B256 key.
    pub fn get_by_b256(&self, key: &B256) -> Option<B256> {
        self.get(&TreeKey::from_bytes(*key))
    }

    /// Insert a value at the given key.
    pub fn insert(&mut self, key: TreeKey, value: B256) {
        let stem_node = self.stems.entry(key.stem).or_insert_with(|| {
            StemNode::new(key.stem)
        });
        stem_node.set_value(key.subindex, value);
        self.rebuild_root();
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
        self.rebuild_root();
    }

    /// Rebuild the root from all stem nodes.
    fn rebuild_root(&mut self) {
        if self.stems.is_empty() {
            self.root = Node::Empty;
            return;
        }

        let stems: Vec<_> = self.stems.keys().cloned().collect();
        self.root = self.build_tree_from_stems(&stems, 0);
    }

    /// Build the tree structure from a list of stems starting at the given bit depth.
    fn build_tree_from_stems(&self, stems: &[Stem], depth: usize) -> Node {
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
            panic!("Tree depth exceeded maximum");
        }

        let (left_stems, right_stems): (Vec<_>, Vec<_>) = stems
            .iter()
            .partition(|s| !s.bit_at(depth));

        let left = self.build_tree_from_stems(&left_stems, depth + 1);
        let right = self.build_tree_from_stems(&right_stems, depth + 1);

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
    pub fn get_or_create_stem(&mut self, stem: Stem) -> &mut StemNode {
        self.stems.entry(stem).or_insert_with(|| StemNode::new(stem))
    }

    /// Iterate over all (key, value) pairs in the tree.
    pub fn iter(&self) -> impl Iterator<Item = (TreeKey, B256)> + '_ {
        self.stems.iter().flat_map(|(stem, stem_node)| {
            stem_node.values.iter().map(move |(&subindex, &value)| {
                (TreeKey::new(*stem, subindex), value)
            })
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
            let stem_node = self.stems.entry(key.stem).or_insert_with(|| {
                StemNode::new(key.stem)
            });
            stem_node.set_value(key.subindex, value);
        }
        self.rebuild_root();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_tree() {
        let tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
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
}
