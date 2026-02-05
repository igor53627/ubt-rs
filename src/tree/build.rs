//! Tree structure construction helpers.

use crate::{error::Result, Hasher, InternalNode, Node, Stem, UbtError};

use super::{UnifiedBinaryTree, MAX_DEPTH};

impl<H: Hasher> UnifiedBinaryTree<H> {
    /// Build the tree structure from a sorted list of stems using slice partitioning.
    /// This is O(n) per level with no allocations, compared to the previous O(n) allocations per level.
    pub(super) fn build_tree_from_sorted_stems(&self, stems: &[Stem], depth: usize) -> Result<Node> {
        if stems.is_empty() {
            return Ok(Node::Empty);
        }

        if stems.len() == 1 {
            let stem = &stems[0];
            if let Some(stem_node) = self.stems.get(stem) {
                return Ok(Node::Stem(stem_node.clone()));
            }
            return Ok(Node::Empty);
        }

        if depth >= MAX_DEPTH {
            return Err(UbtError::TreeDepthExceeded { depth });
        }

        // Use partition_point for O(n) split with no allocation
        // partition_point returns the index where bit_at(depth) becomes true
        // This works because stems are sorted lexicographically, so all stems
        // with bit 0 at this depth come before all stems with bit 1
        let split_point = stems.partition_point(|s| !s.bit_at(depth));
        let (left_stems, right_stems) = stems.split_at(split_point);

        let left = self.build_tree_from_sorted_stems(left_stems, depth + 1)?;
        let right = self.build_tree_from_sorted_stems(right_stems, depth + 1)?;

        if left.is_empty() && right.is_empty() {
            Ok(Node::Empty)
        } else if left.is_empty() {
            Ok(right)
        } else if right.is_empty() {
            Ok(left)
        } else {
            Ok(Node::Internal(InternalNode::new(left, right)))
        }
    }
}

