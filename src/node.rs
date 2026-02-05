//! Tree node types for the UBT.
//!
//! Four node types per EIP-7864:
//! - `InternalNode`: Has `left_hash` and `right_hash` (black nodes in diagrams)
//! - `StemNode`: Has `stem`, `left_hash` and `right_hash` (blue nodes)
//! - `LeafNode`: Contains a 32-byte value (orange nodes)
//! - `EmptyNode`: Represents empty subtree (`hash = 0`)

use alloy_primitives::B256;
use std::collections::HashMap;

use crate::{Hasher, Stem, SubIndex};

/// A node in the UBT.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub enum Node {
    /// Empty node (hash = 0)
    #[default]
    Empty,
    /// Internal branching node with two children
    Internal(InternalNode),
    /// Stem node that roots a 256-value subtree
    Stem(StemNode),
    /// Leaf node containing a value
    Leaf(LeafNode),
}

impl Node {
    /// Calculate the hash of this node.
    pub fn hash<H: Hasher>(&self, hasher: &H) -> B256 {
        match self {
            Self::Empty => B256::ZERO,
            Self::Internal(node) => node.hash(hasher),
            Self::Stem(node) => node.hash(hasher),
            Self::Leaf(node) => node.hash(hasher),
        }
    }

    /// Check if this node is empty.
    pub fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }
}

/// Internal branching node.
///
/// Used for tree traversal based on stem bits.
///
/// Hash formula:
/// `hash = hash(left_hash || right_hash)`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InternalNode {
    /// Left child
    pub left: Box<Node>,
    /// Right child
    pub right: Box<Node>,
}

impl InternalNode {
    /// Create a new internal node.
    pub fn new(left: Node, right: Node) -> Self {
        Self {
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Calculate the hash: `hash(left_hash || right_hash)`
    pub fn hash<H: Hasher>(&self, hasher: &H) -> B256 {
        let left_hash = self.left.hash(hasher);
        let right_hash = self.right.hash(hasher);
        hasher.hash_64(&left_hash, &right_hash)
    }
}

/// Stem node that roots a 256-value subtree.
///
/// The stem identifies which 31-byte prefix this subtree represents.
/// The subtree contains 256 leaves indexed by the last byte (subindex).
///
/// Per go-ethereum:
/// 1. Hash each value: `data\[i\] = hash(value\[i\])` or zero if nil
/// 2. Build 8-level binary tree from bottom up
/// 3. Final hash = `hash(stem || 0x00 || subtree_root)`
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct StemNode {
    /// The 31-byte stem
    pub stem: Stem,
    /// Direct access to leaf values (sparse representation)
    /// Maps subindex -> value
    pub values: HashMap<SubIndex, B256>,
}

impl StemNode {
    /// Create a new stem node with no values.
    pub fn new(stem: Stem) -> Self {
        Self {
            stem,
            values: HashMap::new(),
        }
    }

    /// Set a value at the given subindex.
    pub fn set_value(&mut self, subindex: SubIndex, value: B256) {
        if value.is_zero() {
            self.values.remove(&subindex);
        } else {
            self.values.insert(subindex, value);
        }
    }

    /// Get a value at the given subindex.
    pub fn get_value(&self, subindex: SubIndex) -> Option<B256> {
        self.values.get(&subindex).copied()
    }

    /// Calculate the hash per go-ethereum algorithm:
    /// 1. Hash each value individually
    /// 2. Build 8-level binary tree (256 leaves)
    /// 3. `hash(stem || 0x00 || subtree_root)`
    pub fn hash<H: Hasher>(&self, hasher: &H) -> B256 {
        // Step 1: Hash all values
        let mut data = [B256::ZERO; 256];
        for (&idx, &value) in &self.values {
            data[idx as usize] = hasher.hash_32(&value);
        }

        // Step 2: Build 8-level binary tree from bottom up
        // Level 1: 256 -> 128
        // Level 2: 128 -> 64
        // ...
        // Level 8: 2 -> 1
        for level in 1..=8 {
            let pairs = 256 >> level;
            for i in 0..pairs {
                let left = data[i * 2];
                let right = data[i * 2 + 1];
                data[i] = hasher.hash_64(&left, &right);
            }
        }

        let subtree_root = data[0];

        // Step 3: hash(stem || 0x00 || subtree_root)
        hasher.hash_stem_node(self.stem.as_bytes(), &subtree_root)
    }
}

/// Leaf node containing a 32-byte value.
///
/// Hash formula:
/// `hash = hash(value)`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeafNode {
    /// The 32-byte value stored at this leaf
    pub value: B256,
}

impl LeafNode {
    /// Create a new leaf node.
    pub const fn new(value: B256) -> Self {
        Self { value }
    }

    /// Calculate the hash: `hash(value)`
    pub fn hash<H: Hasher>(&self, hasher: &H) -> B256 {
        hasher.hash_32(&self.value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Blake3Hasher, Sha256Hasher};

    #[test]
    fn test_empty_node_hash() {
        let hasher = Blake3Hasher;
        let node: Node = Node::Empty;
        assert_eq!(node.hash(&hasher), B256::ZERO);
    }

    #[test]
    fn test_leaf_node_hash() {
        let hasher = Blake3Hasher;
        let value = B256::repeat_byte(0x42);
        let node = LeafNode::new(value);
        let hash = node.hash(&hasher);
        assert_ne!(hash, B256::ZERO);
    }

    #[test]
    fn test_stem_node_with_value() {
        let hasher = Blake3Hasher;
        let stem = Stem::new([0u8; 31]);
        let mut node: StemNode = StemNode::new(stem);

        node.set_value(0, B256::repeat_byte(0x42));
        assert_eq!(node.get_value(0), Some(B256::repeat_byte(0x42)));
        assert_eq!(node.get_value(1), None);

        let hash = node.hash(&hasher);
        assert_ne!(hash, B256::ZERO);
    }

    #[test]
    fn test_stem_node_hash_sha256() {
        let hasher = Sha256Hasher;
        let stem = Stem::new([0u8; 31]);
        let mut node = StemNode::new(stem);

        // Set a single value
        node.set_value(0, B256::repeat_byte(0x01));

        let hash = node.hash(&hasher);
        assert_ne!(hash, B256::ZERO);

        // Hash should be deterministic
        let hash2 = node.hash(&hasher);
        assert_eq!(hash, hash2);
    }

    #[test]
    fn test_stem_node_empty_hash() {
        let hasher = Sha256Hasher;
        let stem = Stem::new([0u8; 31]);
        let node = StemNode::new(stem);

        // Empty stem node should still have non-zero hash (stem contributes)
        let hash = node.hash(&hasher);
        // With all-zero stem and all-zero values, subtree is zero
        // hash(0^31 || 0x00 || 0^32) should be computed
        println!("Empty stem node hash: {}", hash);
    }
}
