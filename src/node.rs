//! Tree node types for the UBT.
//!
//! Four node types per EIP-7864:
//! - [`InternalNode`]: Branching node with `left` and `right` child nodes (black nodes in diagrams)
//! - [`StemNode`]: Contains a `stem` and sparse `values` map for its 256-leaf subtree (blue nodes)
//! - [`LeafNode`]: Contains a 32-byte `value` (orange nodes)
//! - Empty node (`Node::Empty`): Represents an empty subtree (`hash = 0`)

use alloy_primitives::B256;
use std::collections::HashMap;

use crate::merkle::hash_stem_values;
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
/// 1. Hash each present value: `data\[i\] = hash(value\[i\])`, or zero if the subindex
///    is absent. A value of 32 zero bytes is present and is hashed.
/// 2. Build 8-level binary tree from bottom up
/// 3. Final hash = `hash(stem || 0x00 || subtree_root)`
///
/// A stem node with no values does not exist in go-ethereum. In this crate its hash
/// is `B256::ZERO`, the same as an absent stem.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct StemNode {
    /// The 31-byte stem
    pub stem: Stem,
    /// Direct access to leaf values (sparse representation)
    /// Maps subindex -> value. An entry is a present leaf, also when its value is zero.
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
    ///
    /// The value is stored as a present leaf for every `value`, including
    /// `B256::ZERO`. As in go-ethereum, a zero write does not remove the leaf.
    /// Use [`remove_value`](Self::remove_value) to make a subindex absent.
    pub fn set_value(&mut self, subindex: SubIndex, value: B256) {
        self.values.insert(subindex, value);
    }

    /// Remove the value at the given subindex and return it.
    ///
    /// After the call the subindex is absent, as if it was never written.
    /// Returns `None` if the subindex was absent. This operation has no
    /// go-ethereum counterpart: go-ethereum deletes with a zero write.
    ///
    /// # Example
    ///
    /// ```
    /// use ubt::{Stem, StemNode, B256};
    ///
    /// let mut node = StemNode::new(Stem::new([0u8; 31]));
    /// node.set_value(7, B256::ZERO);
    /// assert_eq!(node.get_value(7), Some(B256::ZERO));
    /// assert_eq!(node.remove_value(7), Some(B256::ZERO));
    /// assert_eq!(node.get_value(7), None);
    /// ```
    pub fn remove_value(&mut self, subindex: SubIndex) -> Option<B256> {
        self.values.remove(&subindex)
    }

    /// Get a value at the given subindex.
    ///
    /// Returns `None` for an absent subindex and `Some(B256::ZERO)` for a present
    /// zero value.
    pub fn get_value(&self, subindex: SubIndex) -> Option<B256> {
        self.values.get(&subindex).copied()
    }

    /// Calculate the hash per go-ethereum algorithm:
    /// 1. Hash each present value individually (a zero value is present and is hashed)
    /// 2. Build 8-level binary tree (256 leaves)
    /// 3. `hash(stem || 0x00 || subtree_root)`
    ///
    /// Returns `B256::ZERO` for a stem node with no values.
    pub fn hash<H: Hasher>(&self, hasher: &H) -> B256 {
        hash_stem_values(hasher, &self.stem, &self.values)
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

    /// A stem node with no values hashes to zero for every stem, so that it
    /// contributes nothing to the root, the same as an absent stem.
    #[test]
    fn test_stem_node_empty_hash() {
        let zero_stem = StemNode::new(Stem::new([0u8; 31]));
        let nonzero_stem = StemNode::new(Stem::new([0xabu8; 31]));

        assert_eq!(zero_stem.hash(&Sha256Hasher), B256::ZERO);
        assert_eq!(nonzero_stem.hash(&Sha256Hasher), B256::ZERO);
        assert_eq!(zero_stem.hash(&Blake3Hasher), B256::ZERO);
        assert_eq!(nonzero_stem.hash(&Blake3Hasher), B256::ZERO);
    }

    /// A zero value is a present leaf: `set_value` keeps it, the hash is not the
    /// hash of a node without that leaf, and `remove_value` makes it absent again.
    #[test]
    fn test_stem_node_zero_value_is_present() {
        let hasher = Sha256Hasher;
        let stem = Stem::new([0x11u8; 31]);

        let mut node = StemNode::new(stem);
        node.set_value(3, B256::repeat_byte(0x42));
        let hash_without_zero_leaf: B256 = node.hash(&hasher);

        node.set_value(4, B256::ZERO);
        assert_eq!(node.get_value(4), Some(B256::ZERO));
        assert_eq!(node.values.len(), 2);
        assert_ne!(node.hash(&hasher), hash_without_zero_leaf);

        node.set_value(3, B256::ZERO);
        assert_eq!(node.get_value(3), Some(B256::ZERO));
        assert_eq!(node.values.len(), 2);
        assert_ne!(node.hash(&hasher), B256::ZERO);

        assert_eq!(node.remove_value(3), Some(B256::ZERO));
        assert_eq!(node.remove_value(3), None);
        assert_eq!(node.remove_value(4), Some(B256::ZERO));
        assert!(node.values.is_empty());
        assert_eq!(node.hash(&hasher), B256::ZERO);
    }

    /// The stem hash of a single zero leaf, built by hand from the go-ethereum rules.
    /// For the all-zero stem this value is the root that go-ethereum gives for the
    /// single entry `(0^32, 0^32)`.
    #[test]
    fn test_stem_node_single_zero_leaf_hash_sha256() {
        use sha2::{Digest, Sha256};

        let mut subtree_root: [u8; 32] = Sha256::digest([0u8; 32]).into();
        for _ in 0..8 {
            let mut pair = [0u8; 64];
            pair[..32].copy_from_slice(&subtree_root);
            subtree_root = Sha256::digest(pair).into();
        }
        let mut stem_input = [0u8; 64];
        stem_input[32..].copy_from_slice(&subtree_root);
        let expected: [u8; 32] = Sha256::digest(stem_input).into();

        let mut node = StemNode::new(Stem::new([0u8; 31]));
        node.set_value(0, B256::ZERO);

        assert_eq!(node.hash(&Sha256Hasher), B256::from(expected));
        assert_eq!(
            hex::encode(expected),
            "d90841cd9ac38b304a3ba8bf706cb89b26aba153c72b73663fafb5445db8d39c"
        );
    }
}
