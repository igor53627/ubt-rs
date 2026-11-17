//! Merkle proof generation and verification for the UBT.
//!
//! Proofs allow verifying that a key-value pair exists in the tree
//! without having the full tree.

use alloy_primitives::B256;

use crate::{error::Result, Hasher, Stem, StemNode, TreeKey, UbtError, STEM_LEN};

/// Direction in the tree (for proof paths)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Direction {
    /// The proven node is the left child; the sibling hash is the right input of the hash.
    Left,
    /// The proven node is the right child; the sibling hash is the left input of the hash.
    Right,
}

/// A node in a Merkle proof path.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ProofNode {
    /// Sibling hash at an internal node level
    Internal {
        /// Hash of the sibling subtree.
        sibling: B256,
        /// Side of the internal node on which the proven node is.
        direction: Direction,
    },
    /// Stem node with the stem and subtree sibling hashes
    Stem {
        /// Stem of the stem node.
        stem: Stem,
        /// Sibling hashes for the 8-level subtree (from leaf to root)
        subtree_siblings: Vec<B256>,
    },
    /// Extension proof (stem differs from expected)
    Extension {
        /// Stem of the stem node that is in the tree at this position.
        stem: Stem,
        /// Hash of that stem node.
        stem_hash: B256,
    },
}

/// A Merkle proof for a value in the UBT.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Proof {
    /// The key being proven
    pub key: TreeKey,
    /// The value at the key (None if proving non-existence).
    ///
    /// `Some(B256::ZERO)` claims a present leaf that holds 32 zero bytes. It is not
    /// equal to `None`: a present zero leaf contributes `hash_32(0^32)` and an
    /// absent leaf contributes 32 zero bytes.
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
    ///
    /// Returns `Ok(true)` if the computed root matches `expected_root`.
    ///
    /// # Errors
    ///
    /// Returns an error if the proof is structurally invalid.
    pub fn verify<H: Hasher>(&self, hasher: &H, expected_root: &B256) -> Result<bool> {
        let computed_root = self.compute_root(hasher)?;
        Ok(&computed_root == expected_root)
    }

    /// Compute the root hash from this proof.
    ///
    /// The leaf contributes `hash_32(value)` for `Some(value)`, also for
    /// `Some(B256::ZERO)`, and 32 zero bytes for `None`.
    ///
    /// # Errors
    ///
    /// Returns an error if the proof is structurally invalid.
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
                ProofNode::Stem {
                    stem,
                    subtree_siblings,
                } => {
                    if subtree_siblings.len() != 8 {
                        return Err(UbtError::InvalidProof(format!(
                            "stem subtree siblings length must be 8, got {}",
                            subtree_siblings.len()
                        )));
                    }

                    // Siblings are ordered from leaf to root, so level 0 uses the
                    // lowest bit of the subindex.
                    for (level, sibling) in subtree_siblings.iter().enumerate() {
                        let bit = (self.key.subindex >> level) & 1;
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
                            "Extension proof with matching stem".to_string(),
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
        let mut size = 32 + 1; // key, counted as 33 bytes (stem and subindex occupy 32)
        size += 33; // value (32 bytes + 1 byte for Option tag)

        for node in &self.path {
            size += match node {
                ProofNode::Internal { .. } => 32 + 1, // sibling + direction
                ProofNode::Stem {
                    subtree_siblings, ..
                } => STEM_LEN + subtree_siblings.len() * 32,
                ProofNode::Extension { .. } => STEM_LEN + 32,
            };
        }
        size
    }
}

/// Generate a proof for a key in a stem node.
///
/// Returns the value at `subindex` and the 8 sibling hashes from leaf to root.
/// The value is `None` for an absent subindex and `Some(B256::ZERO)` for a present
/// zero leaf. A present zero leaf of another subindex contributes `hash_32(0^32)`
/// to the siblings; an absent subindex contributes 32 zero bytes.
///
/// For a stem node with no values, [`StemNode::hash`] is `B256::ZERO`, but
/// [`Proof::compute_root`] applies the stem hash to the zero subtree root. A proof
/// from this function for such a node, with a stem that is not all zero, does not
/// verify against `StemNode::hash`. go-ethereum cannot have a stem node with no values.
#[must_use]
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
    use crate::Sha256Hasher;

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
                direction: Direction::Left,
            },
            ProofNode::Stem {
                stem: key.stem,
                subtree_siblings: vec![B256::ZERO; 8],
            },
        ];
        let proof = Proof::new(key, Some(B256::repeat_byte(0x42)), path);

        let size = proof.size();
        println!("Proof size: {size} bytes");
        assert!(size > 0);
    }

    /// Build a stem-only proof using `generate_stem_proof`.
    ///
    /// Callers that care about proof-shape invariants (e.g., sibling count) should assert on
    /// `proof.path`.
    fn build_stem_proof<H: Hasher>(
        hasher: &H,
        stem: Stem,
        subindex: u8,
        value: B256,
    ) -> (Proof, B256) {
        let mut node = StemNode::new(stem);
        node.set_value(subindex, value);

        let (generated_value, siblings) = generate_stem_proof(&node, subindex, hasher);
        assert_eq!(generated_value, Some(value));

        let key = TreeKey::new(stem, subindex);
        let proof = Proof::new(
            key,
            Some(value),
            vec![ProofNode::Stem {
                stem,
                subtree_siblings: siblings,
            }],
        );

        (proof, node.hash(hasher))
    }

    #[test]
    fn test_proof_verify_simple() {
        let hasher = Sha256Hasher;
        let stem = Stem::new([0u8; 31]);
        let value = B256::repeat_byte(0x42);

        let (proof, expected_root) = build_stem_proof(&hasher, stem, 0, value);
        let result = proof.verify(&hasher, &expected_root);

        assert!(result.is_ok());
        assert!(result.unwrap());
    }

    /// A proof from `generate_stem_proof` must verify against `StemNode::hash`
    /// for every subindex of a full stem node.
    #[test]
    fn test_stem_proof_verifies_for_every_subindex() {
        let hasher = Sha256Hasher;
        let stem = Stem::new([7u8; 31]);
        let mut node = StemNode::new(stem);
        for subindex in 0u8..=255 {
            let mut value = [0x11u8; 32];
            value[0] = subindex;
            node.set_value(subindex, B256::from(value));
        }
        let expected_root: B256 = node.hash(&hasher);

        let mut failed: Vec<u8> = Vec::new();
        for subindex in 0u8..=255 {
            let (value, siblings) = generate_stem_proof(&node, subindex, &hasher);
            let proof = Proof::new(
                TreeKey::new(stem, subindex),
                value,
                vec![ProofNode::Stem {
                    stem,
                    subtree_siblings: siblings,
                }],
            );
            if !proof.verify(&hasher, &expected_root).unwrap() {
                failed.push(subindex);
            }
        }

        assert!(
            failed.is_empty(),
            "{} of 256 subindexes do not verify: {failed:?}",
            failed.len()
        );

        let (_, siblings) = generate_stem_proof(&node, 0, &hasher);
        let wrong_value = Proof::new(
            TreeKey::new(stem, 0),
            Some(B256::repeat_byte(0xee)),
            vec![ProofNode::Stem {
                stem,
                subtree_siblings: siblings,
            }],
        );
        assert!(!wrong_value.verify(&hasher, &expected_root).unwrap());
    }

    /// The expected root is built by hand, without `generate_stem_proof` and
    /// without `StemNode::hash`: values at subindexes 0 and 1, proof for subindex 1.
    #[test]
    fn test_compute_root_hand_built_stem_proof() {
        let hasher = Sha256Hasher;
        let stem = Stem::new([9u8; 31]);
        let value0 = B256::repeat_byte(0xa0);
        let value1 = B256::repeat_byte(0xa1);

        let mut subtree_root: B256 =
            hasher.hash_64(&hasher.hash_32(&value0), &hasher.hash_32(&value1));
        for _ in 1..8 {
            subtree_root = hasher.hash_64(&subtree_root, &B256::ZERO);
        }
        let expected_root: B256 = hasher.hash_stem_node(stem.as_bytes(), &subtree_root);

        let mut siblings: Vec<B256> = vec![B256::ZERO; 8];
        siblings[0] = hasher.hash_32(&value0);
        let proof = Proof::new(
            TreeKey::new(stem, 1),
            Some(value1),
            vec![ProofNode::Stem {
                stem,
                subtree_siblings: siblings,
            }],
        );

        assert_eq!(proof.compute_root(&hasher).unwrap(), expected_root);
    }

    /// A present zero leaf contributes `sha256(0^32)`; an absent leaf contributes zero.
    /// The expected root is built by hand with `sha2`, not with the crate hasher.
    /// A proof for the present zero leaf verifies with `Some(B256::ZERO)` and does
    /// not verify with `None`. A proof for an absent leaf verifies with `None` and
    /// does not verify with `Some(B256::ZERO)`.
    #[test]
    fn test_proof_for_present_zero_leaf() {
        use sha2::{Digest, Sha256};

        fn sha256_pair(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
            let mut input = [0u8; 64];
            input[..32].copy_from_slice(left);
            input[32..].copy_from_slice(right);
            Sha256::digest(input).into()
        }

        let hasher = Sha256Hasher;
        let stem = Stem::new([9u8; 31]);
        let value2 = B256::repeat_byte(0xa2);
        let zero_leaf_hash: [u8; 32] = Sha256::digest([0u8; 32]).into();
        let value2_hash: [u8; 32] = Sha256::digest(value2.as_slice()).into();

        let pair_2_3: [u8; 32] = sha256_pair(&value2_hash, &zero_leaf_hash);
        let mut subtree_root: [u8; 32] = sha256_pair(&[0u8; 32], &pair_2_3);
        for _ in 2..8 {
            subtree_root = sha256_pair(&subtree_root, &[0u8; 32]);
        }
        let mut stem_input = [0u8; 64];
        stem_input[..31].copy_from_slice(stem.as_bytes());
        stem_input[32..].copy_from_slice(&subtree_root);
        let expected_bytes: [u8; 32] = Sha256::digest(stem_input).into();
        let expected_root = B256::from(expected_bytes);

        let mut node = StemNode::new(stem);
        node.set_value(2, value2);
        node.set_value(3, B256::ZERO);
        assert_eq!(node.hash(&hasher), expected_root);

        let proof_with = |subindex: u8, value: Option<B256>| -> Proof {
            let (_, siblings) = generate_stem_proof(&node, subindex, &hasher);
            Proof::new(
                TreeKey::new(stem, subindex),
                value,
                vec![ProofNode::Stem {
                    stem,
                    subtree_siblings: siblings,
                }],
            )
        };

        let (zero_leaf_value, zero_leaf_siblings) = generate_stem_proof(&node, 3, &hasher);
        assert_eq!(zero_leaf_value, Some(B256::ZERO));
        assert_eq!(zero_leaf_siblings[0], B256::from(value2_hash));

        assert!(proof_with(3, Some(B256::ZERO))
            .verify(&hasher, &expected_root)
            .unwrap());
        assert!(!proof_with(3, None).verify(&hasher, &expected_root).unwrap());

        let (neighbour_value, neighbour_siblings) = generate_stem_proof(&node, 2, &hasher);
        assert_eq!(neighbour_value, Some(value2));
        assert_eq!(neighbour_siblings[0], B256::from(zero_leaf_hash));
        assert!(proof_with(2, Some(value2))
            .verify(&hasher, &expected_root)
            .unwrap());

        let (absent_value, _) = generate_stem_proof(&node, 1, &hasher);
        assert_eq!(absent_value, None);
        assert!(proof_with(1, None).verify(&hasher, &expected_root).unwrap());
        assert!(!proof_with(1, Some(B256::ZERO))
            .verify(&hasher, &expected_root)
            .unwrap());
    }

    #[test]
    fn test_compute_root_rejects_invalid_stem_sibling_lengths() {
        let hasher = Sha256Hasher;
        let stem = Stem::new([0u8; 31]);
        let key = TreeKey::new(stem, 0);
        let value = B256::repeat_byte(0x42);

        for len in [0usize, 7, 9] {
            let proof = Proof::new(
                key,
                Some(value),
                vec![ProofNode::Stem {
                    stem,
                    subtree_siblings: vec![B256::ZERO; len],
                }],
            );

            let err = proof.compute_root(&hasher).unwrap_err();
            assert!(matches!(err, UbtError::InvalidProof(_)));
        }

        let (proof_ok, expected_root) = build_stem_proof(&hasher, stem, 0, value);
        let ProofNode::Stem {
            subtree_siblings, ..
        } = proof_ok.path.first().unwrap()
        else {
            panic!("expected a stem proof node");
        };
        assert_eq!(subtree_siblings.len(), 8);

        assert_eq!(proof_ok.compute_root(&hasher).unwrap(), expected_root);
    }
}
