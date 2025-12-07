//! Merkle proof generation and verification for the UBT.
//!
//! Proofs allow verifying that a key-value pair exists in the tree
//! without having the full tree.

use alloy_primitives::B256;

use crate::{Hasher, Stem, TreeKey, UbtError, error::Result, StemNode, Node, STEM_LEN};

/// Direction in the tree (for proof paths)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Direction {
    Left,
    Right,
}

/// A node in a Merkle proof path.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ProofNode {
    /// Sibling hash at an internal node level
    Internal {
        sibling: B256,
        direction: Direction,
    },
    /// Stem node with the stem and subtree sibling hashes
    Stem {
        stem: Stem,
        /// Sibling hashes for the 8-level subtree (from leaf to root)
        subtree_siblings: Vec<B256>,
    },
    /// Extension proof (stem differs from expected)
    Extension {
        stem: Stem,
        stem_hash: B256,
    },
}

/// A Merkle proof for a value in the UBT.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Proof {
    /// The key being proven
    pub key: TreeKey,
    /// The value at the key (None if proving non-existence)
    pub value: Option<B256>,
    /// Proof nodes from leaf to root
    pub path: Vec<ProofNode>,
}

impl Proof {
    /// Create a new proof.
    pub fn new(key: TreeKey, value: Option<B256>, path: Vec<ProofNode>) -> Self {
        Self { key, value, path }
    }

    /// Verify this proof against an expected root hash.
    pub fn verify<H: Hasher>(&self, hasher: &H, expected_root: &B256) -> Result<bool> {
        let computed_root = self.compute_root(hasher)?;
        Ok(&computed_root == expected_root)
    }

    /// Compute the root hash from this proof.
    pub fn compute_root<H: Hasher>(&self, hasher: &H) -> Result<B256> {
        let mut current_hash = match &self.value {
            Some(v) => hasher.hash_32(v),
            None => B256::ZERO,
        };

        for node in &self.path {
            match node {
                ProofNode::Internal { sibling, direction } => {
                    current_hash = match direction {
                        Direction::Left => hasher.hash_64(&current_hash, sibling),
                        Direction::Right => hasher.hash_64(sibling, &current_hash),
                    };
                }
                ProofNode::Stem { stem, subtree_siblings } => {
                    // Rebuild subtree hash from siblings
                    for (level, sibling) in subtree_siblings.iter().enumerate() {
                        let bit = (self.key.subindex >> (7 - level)) & 1;
                        current_hash = if bit == 0 {
                            hasher.hash_64(&current_hash, sibling)
                        } else {
                            hasher.hash_64(sibling, &current_hash)
                        };
                    }
                    // Apply stem node hash
                    current_hash = hasher.hash_stem_node(stem.as_bytes(), &current_hash);
                }
                ProofNode::Extension { stem, stem_hash } => {
                    // Non-existence proof: the stem differs
                    if stem == &self.key.stem {
                        return Err(UbtError::InvalidProof(
                            "Extension proof with matching stem".to_string()
                        ));
                    }
                    current_hash = *stem_hash;
                }
            }
        }

        Ok(current_hash)
    }

    /// Get the size of the proof in bytes.
    pub fn size(&self) -> usize {
        let mut size = 32 + 1; // key stem + subindex
        size += 33; // value (32 bytes + 1 byte for Option tag)
        
        for node in &self.path {
            size += match node {
                ProofNode::Internal { .. } => 32 + 1, // sibling + direction
                ProofNode::Stem { subtree_siblings, .. } => {
                    STEM_LEN + subtree_siblings.len() * 32
                }
                ProofNode::Extension { .. } => STEM_LEN + 32,
            };
        }
        size
    }
}

/// Generate a proof for a key in a stem node.
pub fn generate_stem_proof<H: Hasher>(
    stem_node: &StemNode,
    subindex: u8,
    hasher: &H,
) -> (Option<B256>, Vec<B256>) {
    let value = stem_node.get_value(subindex);
    
    // Hash all values
    let mut data = [B256::ZERO; 256];
    for (&idx, &v) in &stem_node.values {
        data[idx as usize] = hasher.hash_32(&v);
    }
    
    // Collect siblings while building tree
    let mut siblings = Vec::with_capacity(8);
    let mut idx = subindex as usize;
    
    for level in 0..8 {
        // Sibling index
        let sibling_idx = idx ^ 1;
        siblings.push(data[sibling_idx]);
        
        // Build next level
        let pairs = 256 >> (level + 1);
        for i in 0..pairs {
            let left = data[i * 2];
            let right = data[i * 2 + 1];
            data[i] = hasher.hash_64(&left, &right);
        }
        
        idx /= 2;
    }
    
    (value, siblings)
}

/// A multi-proof for multiple keys.
#[derive(Clone, Debug, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MultiProof {
    /// Keys being proven
    pub keys: Vec<TreeKey>,
    /// Values at keys (None for non-existence)
    pub values: Vec<Option<B256>>,
    /// Shared proof nodes (deduplicated)
    pub nodes: Vec<B256>,
    /// Stems included in the proof
    pub stems: Vec<Stem>,
}

impl MultiProof {
    /// Create a new empty multi-proof.
    pub fn new() -> Self {
        Self::default()
    }

    /// Get the number of keys in the proof.
    pub fn len(&self) -> usize {
        self.keys.len()
    }

    /// Check if the proof is empty.
    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    /// Get the size of the proof in bytes.
    pub fn size(&self) -> usize {
        let mut size = 0;
        size += self.keys.len() * 32; // keys
        size += self.values.len() * 33; // values with option tag
        size += self.nodes.len() * 32; // shared nodes
        size += self.stems.len() * STEM_LEN; // stems
        size
    }
}

/// Witness data for stateless execution.
#[derive(Clone, Debug, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Witness {
    /// Pre-state values needed for execution
    pub pre_values: Vec<(TreeKey, B256)>,
    /// Proof for pre-state
    pub proof: MultiProof,
}

impl Witness {
    /// Create a new empty witness.
    pub fn new() -> Self {
        Self::default()
    }

    /// Get the size of the witness in bytes.
    pub fn size(&self) -> usize {
        let mut size = self.proof.size();
        size += self.pre_values.len() * (32 + 32); // key + value
        size
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Blake3Hasher, Sha256Hasher};

    #[test]
    fn test_stem_proof_generation() {
        let hasher = Sha256Hasher;
        let stem = Stem::new([0u8; 31]);
        let mut node = StemNode::new(stem);
        
        node.set_value(0, B256::repeat_byte(0x42));
        node.set_value(5, B256::repeat_byte(0x43));
        
        let (value, siblings) = generate_stem_proof(&node, 0, &hasher);
        
        assert_eq!(value, Some(B256::repeat_byte(0x42)));
        assert_eq!(siblings.len(), 8);
    }

    #[test]
    fn test_proof_size() {
        let key = TreeKey::from_bytes(B256::repeat_byte(0x01));
        let path = vec![
            ProofNode::Internal { 
                sibling: B256::ZERO, 
                direction: Direction::Left 
            },
            ProofNode::Stem {
                stem: key.stem,
                subtree_siblings: vec![B256::ZERO; 8],
            },
        ];
        let proof = Proof::new(key, Some(B256::repeat_byte(0x42)), path);
        
        let size = proof.size();
        println!("Proof size: {} bytes", size);
        assert!(size > 0);
    }

    #[test]
    fn test_proof_verify_simple() {
        let hasher = Sha256Hasher;
        let stem = Stem::new([0u8; 31]);
        let mut node = StemNode::new(stem);
        
        let value = B256::repeat_byte(0x42);
        node.set_value(0, value);
        
        // Generate proof
        let (_, siblings) = generate_stem_proof(&node, 0, &hasher);
        
        let key = TreeKey::new(stem, 0);
        let proof = Proof::new(
            key,
            Some(value),
            vec![ProofNode::Stem {
                stem,
                subtree_siblings: siblings,
            }],
        );
        
        // The computed root should match the node's hash
        let expected_root = node.hash(&hasher);
        let result = proof.verify(&hasher, &expected_root);
        
        assert!(result.is_ok());
        assert!(result.unwrap());
    }
}
